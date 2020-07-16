/* Minimal Linux Intel Processor Trace driver. */

/*
 * Copyright (c) 2020
 * Author: Deng
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * Alternatively you can use this file under the GPLv2.
 */


#include <linux/module.h>
#include <linux/miscdevice.h>
#include <linux/fs.h>
#include <linux/cpu.h>
#include <linux/moduleparam.h>
#include <linux/kernel.h>
#include <linux/gfp.h>
#include <linux/io.h>
#include <linux/mm.h>
#include <linux/uaccess.h>
#include <linux/sched.h>
#include <linux/kallsyms.h>
#include <linux/kprobes.h>
#include <linux/dcache.h>
#include <linux/ctype.h>
#include <linux/syscore_ops.h>
#include <trace/events/sched.h>
#include <asm/msr.h>
#include <asm/processor.h>
#include <asm/processor-flags.h>
#define CREATE_TRACE_POINTS
#include "pttp.h"

#include "compat.h"
#include "simple-pt.h"

#define MSR_IA32_RTIT_OUTPUT_BASE	0x00000560
#define MSR_IA32_RTIT_OUTPUT_MASK_PTRS	0x00000561
#define MSR_IA32_RTIT_CTL		0x00000570
#define TRACE_EN	BIT_ULL(0)//进行trace
#define CYC_EN		BIT_ULL(1)
#define CTL_OS		BIT_ULL(2)//设置此变量指明的位为1则对内核进行trace
#define CTL_USER	BIT_ULL(3)
#define PT_ERROR	BIT_ULL(4)
#define CR3_FILTER	BIT_ULL(7)
#define PWR_EVT_EN	BIT_ULL(4)
#define FUP_ON_PTW_EN	BIT_ULL(5)
#define TO_PA		BIT_ULL(8)
#define MTC_EN		BIT_ULL(9)
#define TSC_EN		BIT_ULL(10)
#define DIS_RETC	BIT_ULL(11)
#define PTW_EN		BIT_ULL(12)
#define BRANCH_EN	BIT_ULL(13)
#define MTC_MASK	(0xf << 14)
#define CYC_MASK	(0xf << 19)
#define PSB_MASK	(0xf << 24)
#define ADDR0_SHIFT	32
#define ADDR1_SHIFT	36
#define ADDR0_MASK	(0xfULL << ADDR0_SHIFT)
#define ADDR1_MASK	(0xfULL << ADDR1_SHIFT)
#define MSR_IA32_RTIT_STATUS		0x00000571
#define MSR_IA32_CR3_MATCH		0x00000572
#define TOPA_STOP	BIT_ULL(4)
#define TOPA_INT	BIT_ULL(2)
#define TOPA_END	BIT_ULL(0)
#define TOPA_SIZE_SHIFT 6
#define MSR_IA32_ADDR0_START		0x00000580
#define MSR_IA32_ADDR0_END		0x00000581
#define MSR_IA32_ADDR1_START		0x00000582
#define MSR_IA32_ADDR1_END		0x00000583



static void restart(void);


static int start_set(const char *val, const struct kernel_param *kp)
{
	int ret = param_set_int(val, kp);//进行变量赋值
	restart();
	return ret;
}
static struct kernel_param_ops start_ops = {
	.set = start_set,
	.get = param_get_int,
};



//其实就是进行赋值
static int symbol_set(const char *val, const struct kernel_param *kp)
{
	int ret = -EIO;
	if (!isdigit(val[0])) {
		pr_err("Symbols are not supported anymore. Please resolve through /proc/kallsyms");
	} else {
		ret = param_set_ulong(val, kp);
	}
	return ret;
}

static int start = 0;


//宏DEFINE_PER_CPU为每一个CPU核心都申请了指定的变量
static DEFINE_PER_CPU(unsigned long, pt_buffer_cpu);
static DEFINE_PER_CPU(u64 *, topa_cpu);
static DEFINE_PER_CPU(bool, pt_running);
static DEFINE_PER_CPU(u64, pt_offset);

static bool initialized;
static bool has_cr3_match;
static int pt_buffer_order = 9;//Order of PT buffer size per CPU (2^n pages)
static int pt_num_buffers = 1;//Number of PT buffers per CPU (if supported)

module_param_cb(start, &start_ops, &start, 0644);
MODULE_PARM_DESC(start, "Set to 1 to start trace, or 0 to stop");
static int user = 1;//指明是否对用户空间进行trace
static int kernel = 0;//指明是否对内核进行trace
static int tsc_en = 1;
static char comm_filter[100];
module_param_string(comm_filter, comm_filter, sizeof(comm_filter), 0644);//-c后的参数指向的位置，即要过滤的进程名
MODULE_PARM_DESC(comm_filter, "Process name to set CR3 filter for");
static int cr3_filter = 1;
static bool clear_on_start = true;

static DEFINE_MUTEX(restart_mutex);


//MSR（Model Specific Register）是x86架构中的概念，指的是在x86架构处理器中，
//一系列用于控制CPU运行、功能开关、调试、跟踪程序执行、监测CPU性能等方面的寄存器。
//对于这些寄存器，需要采用专门的指令 RDMSR 和 WRMSR 进行读写。
//详见https://blog.csdn.net/lindahui2008/article/details/82720455
static inline int pt_wrmsrl_safe(unsigned msr, u64 val)
{
	int ret = wrmsrl_safe(msr, val);
	trace_msr(msr, val, ret != 0, 0);
	return ret;
}

static inline int pt_rdmsrl_safe(unsigned msr, u64 *val)
{
	//通过rdmsrl(MSR_LSTAR,ksystem_call)可获得系统调用的入口地址
	//然后对该入口地址进行解析得到系统调用
	int ret = rdmsrl_safe(msr, val);
	trace_msr(msr, *val, ret != 0, 1);
	return ret;
}


//写入msr后，PT硬件会自动根据cr3的值来进行过滤
static inline void set_cr3_filter0(u64 cr3)
{
	if(pt_wrmsrl_safe(MSR_IA32_CR3_MATCH, cr3) < 0)
		pr_err("cpu %d, cannot set CR3 filter\n", smp_processor_id());
}


//最终将控制信息写入PT并启动PT的函数
static int start_pt(void)
{
	u64 val, oldval;

	if (pt_rdmsrl_safe(MSR_IA32_RTIT_CTL, &val) < 0)
		return -1;

	oldval = val;
	/* Disable trace for reconfiguration */
	if (val & TRACE_EN)//如果之前已经开启了trace，那么通过msr停止trace
		pt_wrmsrl_safe(MSR_IA32_RTIT_CTL, val & ~TRACE_EN);

	//pt_buffer_cpu变量表示分配给PT使用的缓冲区的大小，这里对其进行初始化
	//pt_buffer_cpu是每个CPU核心都有的同名变量(详见声明处)，__this_cpu_read获取当前CPU的pt_buffer_cpu变量
	if (clear_on_start && !(val & TRACE_EN)) {//将pt缓冲区置0
		memset((void *)__this_cpu_read(pt_buffer_cpu), 0, PAGE_SIZE << pt_buffer_order);
		//init_mask_ptrs();//直接将此函数的内容放到了下面
		pt_wrmsrl_safe(MSR_IA32_RTIT_OUTPUT_MASK_PTRS, 0ULL);//对mask_ptrs进行初始化
		pt_wrmsrl_safe(MSR_IA32_RTIT_STATUS, 0ULL);
	}

	val &= ~(TSC_EN | CTL_OS | CTL_USER | CR3_FILTER | DIS_RETC | TO_PA |
		 CYC_EN | TRACE_EN | BRANCH_EN | CYC_EN | MTC_EN |
		 MTC_EN | MTC_MASK | CYC_MASK | PSB_MASK | ADDR0_MASK | ADDR1_MASK);
	/* Otherwise wait for start trigger */
	val |= TRACE_EN;
	val |= BRANCH_EN;
	// if (!single_range)
	// 	val |= TO_PA;
	val |= TO_PA;
	if (tsc_en)
		val |= TSC_EN;
	if (kernel)//kernel为1则通知PT对内核进行trace，否则不
		val |= CTL_OS;
	if (user)
		val |= CTL_USER;
	if (cr3_filter && has_cr3_match) {
		//下面这个判断条件很重要，删除后过滤功能失效
		if(!(oldval & CR3_FILTER)) {
			set_cr3_filter0(0ULL);//为什么会是执行这条分支，即不进行过滤？因为第一次时还没有找到进程的cr3的值，所以还不能进行过滤，将msr中用于过滤的位设为0，详见27
		}
		val |= CR3_FILTER;
	}
	//val包含了所有的控制信息，使用pt_wrmsrl_safe将控制信息传递给PT并启动它
	if (pt_wrmsrl_safe(MSR_IA32_RTIT_CTL, val) < 0)
		return -1;
	__this_cpu_write(pt_running, true);//将pt_running改为TRUE，标志PT正在运行
	return 0;
}

//调用start_pt进行trace
static void do_start_pt(void *arg)
{
	//smp_processor_id()用来获取当前cpu的id
	int cpu = smp_processor_id();
	if (start_pt() < 0)
		pr_err("cpu %d, RTIT_CTL enable failed\n", cpu);
}

//停止trace
static void stop_pt(void *arg)
{
	u64 offset;
	u64 ctl, status, extra;

	if (!__this_cpu_read(pt_running))
		return;
	pt_rdmsrl_safe(MSR_IA32_RTIT_CTL, &ctl);
	pt_rdmsrl_safe(MSR_IA32_RTIT_STATUS, &status);
	if (!(ctl & TRACE_EN))
		pr_debug("cpu %d, trace was not enabled on stop, ctl %llx, status %llx\n",
				raw_smp_processor_id(), ctl, status);
	if (status & PT_ERROR) {
		pr_info("cpu %d, error happened: status %llx\n",
				raw_smp_processor_id(), status);
		pt_wrmsrl_safe(MSR_IA32_RTIT_STATUS, 0);
	}
	pt_wrmsrl_safe(MSR_IA32_RTIT_CTL, 0LL);
	pt_rdmsrl_safe(MSR_IA32_RTIT_OUTPUT_MASK_PTRS, &offset);
	extra = 0;
	// if (!single_range)
	// 	extra = ((offset & 0xffffffff) >> 7) <<
	// 		(pt_buffer_order + PAGE_SHIFT);
	extra = ((offset & 0xffffffff) >> 7) <<
 		(pt_buffer_order + PAGE_SHIFT);
	__this_cpu_write(pt_offset, (offset >> 32) + extra);
	__this_cpu_write(pt_running, false);
}


//进行trace
static void restart(void)
{
	if (!initialized)
		return;

	//上锁
	mutex_lock(&restart_mutex);
	//start=1 时在每个CPU核心上运行do_start_pt开始进行trace
	//否则……
	on_each_cpu(start ? do_start_pt : stop_pt, NULL, 1);
	mutex_unlock(&restart_mutex);
}


//为PT申请存储追踪数据的缓冲区
//也就是申请用于存储PT数据的物理页面，然后将物理首地址给topa_cpu
static int simple_pt_buffer_init(int cpu)
{
	unsigned long pt_buffer;
	u64 *topa;

	/* allocate buffer */
	pt_buffer = per_cpu(pt_buffer_cpu, cpu);
	if (!pt_buffer) {
		pt_buffer = __get_free_pages(GFP_KERNEL|__GFP_NOWARN|__GFP_ZERO, pt_buffer_order);
		if (!pt_buffer) {
			pr_err("cpu %d, Cannot allocate %ld KB buffer\n", cpu,
					(PAGE_SIZE << pt_buffer_order) / 1024);
			return -ENOMEM;
		}
		per_cpu(pt_buffer_cpu, cpu) = pt_buffer;
	}

	// if (!single_range) {
		/* allocate topa */
	topa = per_cpu(topa_cpu, cpu);
	if (!topa) {
		int n;

		topa = (u64 *)__get_free_page(GFP_KERNEL|__GFP_ZERO);
		if (!topa) {
			pr_err("cpu %d, Cannot allocate topa page\n", cpu);
			goto out_pt_buffer;
		}
		per_cpu(topa_cpu, cpu) = topa;

		/* create circular topa table */
		n = 0;
		topa[n++] = (u64)__pa(pt_buffer) |
			(pt_buffer_order << TOPA_SIZE_SHIFT);
		for (; n < pt_num_buffers; n++) {
			void *buf = (void *)__get_free_pages(
				GFP_KERNEL|__GFP_NOWARN|__GFP_ZERO,
				pt_buffer_order);
			if (!buf) {
				pr_warn("Cannot allocate %d'th PT buffer\n", n);
				break;
			}
			topa[n] = __pa(buf) |
				(pt_buffer_order << TOPA_SIZE_SHIFT);
		}
		topa[n] = (u64)__pa(topa) | TOPA_END; /* circular buffer */
	}
	// }
	return 0;

out_pt_buffer:
	free_pages(pt_buffer, pt_buffer_order);
	per_cpu(pt_buffer_cpu, cpu) = 0;
	return -ENOMEM;
}


//获取存放PT数据的物理页面的数量
static unsigned topa_entries(int cpu)
{
	//per_cpu应该是一个宏函数，返回对应CPU的该变量
	u64 *topa = per_cpu(topa_cpu, cpu);
	int n;

	// if (single_range)
	// 	return 1;
	if (!topa)
		return 0;
	for (n = 0; !(topa[n] & TOPA_END); n++)
		;
	return n;
}



//返回的就是file指向的设备
//驱动开发中通常将文件的私有数据private_data指向设备结构体，
//在read()、write()、ioctl()等函数通过 private_data 访问数据 设备结构体。
//了在同一个驱动支持多个相同设备时，为各个设备准备的数据结构互相不冲突
static inline int file_get_cpu(struct file *file)
{
	return (long)file->private_data;
}


//此设备的mmap的底层实现。mmap是一种内存映射文件的方法，即将一个文件(struct file)或者其它对象映射到进程的地址空间(struct vm_area_struct)，
//实现文件磁盘地址和进程虚拟地址空间中一段虚拟地址的一一对映关系。实现这样的映射关系后，
//进程就可以采用指针的方式读写操作这一段内存，而系统会自动回写脏页面到对应的文件磁盘上，
//即完成了对文件的操作而不必再调用read,write等系统调用函数。相反，内核空间对这段区域的修改也直接反映用户空间。
//struct file *file实际上指的就是这个设备。
static int simple_pt_mmap(struct file *file, struct vm_area_struct *vma)
{
	unsigned long len = vma->vm_end - vma->vm_start;
	int cpu = file_get_cpu(file);//变量cpu代表一个cpu核心
	unsigned num = topa_entries(cpu);//变量num表示该cpu分配的PT缓冲区的物理页面数
	int i, err;
	u64 *topa;
	unsigned long buffer_size = PAGE_SIZE << pt_buffer_order;//PT缓冲区大小

	vma->vm_flags &= ~VM_MAYWRITE;

	if (len % PAGE_SIZE || len != num * buffer_size || vma->vm_pgoff)
		return -EINVAL;

	if (vma->vm_flags & VM_WRITE)
		return -EPERM;

	if (!cpu_online(cpu))
		return -EIO;

	if (num <= 1) {
		return remap_pfn_range(vma, vma->vm_start,
			       __pa(per_cpu(pt_buffer_cpu, cpu)) >> PAGE_SHIFT,
			       buffer_size,
			       vma->vm_page_prot);
	}
	topa = per_cpu(topa_cpu, cpu);
	err = 0;
	for (i = 0; i < num; i++) {
		err = remap_pfn_range(vma,
				vma->vm_start + i*buffer_size,//要映射到的用户空间的首地址
				topa[i] >> PAGE_SHIFT,//topa_cpu存放的应该就是PT缓冲区的物理首地址
				buffer_size,
				vma->vm_page_prot);
		if (err)
			break;
	}
	return err;
}

//对注册为杂项设备的simple_pt的I/O通道进行管理，是file_operation的一部分
static long simple_pt_ioctl(struct file *file, unsigned int cmd,
			    unsigned long arg)
{
	switch (cmd) {//arg为CPU核心编号
	case SIMPLE_PT_SET_CPU: {
		unsigned long cpu = arg;
		if (cpu >= NR_CPUS || !cpu_online(cpu))
			return -EINVAL;
		file->private_data = (void *)cpu;
		return 0;
	}
	case SIMPLE_PT_GET_SIZE: {
		int num = topa_entries(file_get_cpu(file));
		return put_user(num * (PAGE_SIZE << pt_buffer_order),
				(int *)arg);//put_user用于向用户空间传递一些基本类型的变量
	}
	case SIMPLE_PT_GET_OFFSET: {
		unsigned offset;
		int ret = 0;
		mutex_lock(&restart_mutex);
		if (per_cpu(pt_running, file_get_cpu(file)))//返回的就是file指向的设备，在这里就是CPU核心，因此这里per_cpu返回对应cpu的running变量
			ret = -EIO;
		else
			offset = per_cpu(pt_offset, file_get_cpu(file));
		mutex_unlock(&restart_mutex);
		if (!ret)
			ret = put_user(offset, (int *)arg);
		return ret;
	}
	default:
		return -ENOTTY;
	}
}


//这是对结构体 进行赋值，".owner = THIS_MODULE"相当于"simple_pt_fops.owner = THIS_MODULE"
//file_operation就是把系统调用和驱动程序关联起来的关键数据结构，详见https://www.cnblogs.com/ZJoy/archive/2011/01/09/1931379.html
static const struct file_operations simple_pt_fops = {
	.owner = THIS_MODULE,
	.mmap =	simple_pt_mmap,
	.unlocked_ioctl = simple_pt_ioctl,
	.llseek = noop_llseek,
};

//miscdevice共享一个主设备号MISC_MAJOR(即10)，但次设备号不同。 所有的miscdevice设备形成了一个链表，
//对设备访问时内核根据次设备号查找对应的miscdevice设备，然后调用其file_operations结构中注册的文件操作接口进行操作。
//详见https://blog.csdn.net/u013377887/article/details/72847213，https://www.cnblogs.com/fellow1988/p/6235080.htmlhttps://www.cnblogs.com/fellow1988/p/6235080.html
static struct miscdevice simple_pt_miscdev = {
	MISC_DYNAMIC_MINOR,
	"simple-pt",
	&simple_pt_fops
};


//将指定进程名的cr3的值写入cr3
static void set_cr3_filter(void *arg)
{
	u64 val;

	if (pt_rdmsrl_safe(MSR_IA32_RTIT_CTL, &val) < 0)
		return;
	if ((val & TRACE_EN) && pt_wrmsrl_safe(MSR_IA32_RTIT_CTL, val & ~TRACE_EN) < 0)//暂停trace
		return;

	set_cr3_filter0(*(u64*)arg);//设置CR3_MATCH中cr3的值，下面是原set_cr3_filter0的代码
	// if(pt_wrmsrl_safe(MSR_IA32_CR3_MATCH, cr3) < 0)
	// 	pr_err("cpu %d, cannot set CR3 filter\n", smp_processor_id());

	if ((val & TRACE_EN) && pt_wrmsrl_safe(MSR_IA32_RTIT_CTL, val) < 0)//继续trace
		return;

}


//此函数判断当前进程名是否等于指定的comm_filter，是则返回True
static bool match_comm(void)
{
	char *s;

	s = strchr(comm_filter, '\n');//strchr(str, c) 在参数 str 所指向的字符串中搜索第一次出现字符 c（一个无符号字符）的位置。
	if (s)
		*s = 0;
	if (comm_filter[0] == 0)//match_comm找到指定进程后，start_pt会将comm_filter置0，防止出现问题
		return true;
	//current是类似__LINE__的宏，指向保存进程信息的task_struct结构，current->comm即当前进程的名称
	return !strcmp(current->comm, comm_filter);//strcmp(str1, str2) 把 str1 所指向的字符串和 str2 所指向的字符串进行比较，相等时返回0。
}


//获取cr3寄存器的值
static u64 retrieve_cr3(void)
{
	u64 cr3;

	asm volatile("mov %%cr3,%0" : "=r" (cr3));
	return cr3 & ~0xfff; // mask out the PCID PCID是进程上下文标识符，这里去除它
}

static int probe_exec(struct kprobe *kp, struct pt_regs *regs)
{
	u64 cr3;
	char *pathbuf, *path;

	if (!match_comm())//此函数判断当前进程名是否等于指定的comm_filter，是则返回True
		return 0;

	//之后的代码是用来获取cr3并进行设置的，所以只运行一次

	pathbuf = (char *)__get_free_page(GFP_KERNEL);
	if (!pathbuf)
		return 0;

	/* mmap_sem needed? */
	path = d_path(&current->mm->exe_file->f_path, pathbuf, PAGE_SIZE);
	if (IS_ERR(path))
		goto out;

	cr3 = retrieve_cr3();//获取cr3寄存器的值
	trace_exec_cr3(cr3, path, current->pid);
	if (comm_filter[0] && has_cr3_match) {
		mutex_lock(&restart_mutex);
		on_each_cpu(set_cr3_filter, &cr3, 1);//将cr3的值写入msr中，然后PT硬件会自动进行匹配
		mutex_unlock(&restart_mutex);
	}
out:
	free_page((unsigned long)pathbuf);
	return 0;
}



/* Arbitrary symbol in the exec*() path that is called after the new mm/CR3 is set up */
static struct kprobe finalize_exec_kp = {
	.symbol_name = "finalize_exec",
	.pre_handler = probe_exec,
};



//获取CPU信息，如是否支持PT等
static int simple_pt_cpuid(void)
{
	unsigned a, b, c, d;
	unsigned a1, b1, c1, d1;

	cpuid(0, &a, &b, &c, &d);
	if (a < 0x14) {
		pr_info("Not enough CPUID support for PT\n");
		return -EIO;
	}
	cpuid_count(0x07, 0, &a, &b, &c, &d);
	if ((b & BIT(25)) == 0) {
		pr_info("No PT support\n");
		return -EIO;
	}
	cpuid_count(0x14, 0, &a, &b, &c, &d);
	// if (!single_range && !(c & BIT(0))) {
	// 	pr_info("No ToPA support\n");
	// 	return -EIO;
	// }
	if (!(c & BIT(0))) {
		pr_info("No ToPA support\n");
		return -EIO;
	}
	has_cr3_match = !!(b & BIT(0));
	// has_ptw = !!(b & BIT(4));
	// has_pwr_evt = !!(b & BIT(5));
	if (!(c & BIT(1)))
		pt_num_buffers = 1;
	pt_num_buffers = min_t(unsigned, pt_num_buffers,
			       (PAGE_SIZE / 8) - 1);
	a1 = b1 = c1 = d1 = 0;
	if (a >= 1)
		cpuid_count(0x14, 1, &a1, &b1, &c1, &d1);

	return 0;
}

static int spt_hotplug_state = -1;

static void free_topa(u64 *topa)
{
	int j;

	for (j = 1; j < pt_num_buffers; j++) {
		if (topa[j] & TOPA_END)
			break;
		free_pages((unsigned long)__va(topa[j] & PAGE_MASK),
				pt_buffer_order);
	}
}


//为PT的运行作准备
static int spt_cpu_startup(unsigned int cpu)
{
	int err;
	u64 ctl;
	u64 *topa;

	err = simple_pt_buffer_init(cpu);
	if (err)
		return err;

	//下面是原simple_pt_cpu_init的功能，整合到这里了
	/* check for pt already active */
	if (pt_rdmsrl_safe(MSR_IA32_RTIT_CTL, &ctl) < 0) {//pt_rdmsrl_safe获取调用了PT的系统调用赋给ctl
		pr_err("cpu %d, Cannot access RTIT_CTL\n", cpu);
		return -EIO;
	}
	if (ctl & TRACE_EN) {
		pr_err("cpu %d, PT already active: %llx\n", cpu, ctl);
	}

	//下面是原simple_pt_init_msrs的功能，整合到这里了
	topa = __this_cpu_read(topa_cpu);
	pt_wrmsrl_safe(MSR_IA32_RTIT_OUTPUT_BASE, __pa(topa));//这里设置PT缓冲区的物理首地址，PT数据将会直接输出到这里？
	//init_mask_ptrs();//直接将此函数的内容放到了下面
	pt_wrmsrl_safe(MSR_IA32_RTIT_OUTPUT_MASK_PTRS, 0ULL);//对mask_ptrs进行初始化
	pt_wrmsrl_safe(MSR_IA32_RTIT_STATUS, 0ULL);
	return 0;
}

static int spt_cpu_teardown(unsigned int cpu)
{
	stop_pt(NULL);
	if (per_cpu(topa_cpu, cpu)) {
		u64 *topa = per_cpu(topa_cpu, cpu);
		free_topa(topa);
		free_page((unsigned long)topa);
		per_cpu(topa_cpu, cpu) = NULL;
	}
	if (per_cpu(pt_buffer_cpu, cpu)) {
		free_pages(per_cpu(pt_buffer_cpu, cpu), pt_buffer_order);
		per_cpu(pt_buffer_cpu, cpu) = 0;
	}
	return 0;
}

static int simple_pt_init(void)
{
	int err;

	if (THIS_MODULE->taints)
		fix_tracepoints();

	//获取CPU信息，如是否支持PT等
	err = simple_pt_cpuid();
	if (err < 0)
		return err;

	//misc_register(系统函数)将此模块注册为一个杂项设备
	err = misc_register(&simple_pt_miscdev);
	if (err < 0) {
		pr_err("Cannot register simple-pt device\n");
		return err;
	}

	//声明在compat.h中，用于启动和终止CPU
	//将会在每个cpu上调用spt_cpu_startup
	err = cpuhp_setup_state(CPUHP_AP_ONLINE_DYN, "simple-pt",
				       spt_cpu_startup,
				       spt_cpu_teardown);
	if (err < 0)
		goto out_buffers;
	spt_hotplug_state = err;

	/* Trace exec->cr3 */
	/* This used to use the sched_exec trace point, but Linux doesn't
	 * export trace points anymore.
	 */
	//使用register_kprobe注册kprobe断点，其中kp->addr指向断点函数，断点前会回调设置的函数
	err = register_kprobe(&finalize_exec_kp);
	if (err) {
		pr_info("Cannot register exec kprobe on finalize_exec: %d\n", err);
		/* Ignore error */
	}
	
	initialized = true;
	//start变量标识是否开始trace，由sptcmd向parameters写入进行设置
	if (start)
		//进行trace，这里不会运行
		restart();

	pr_info("%s\n", start ? "running" : "loaded");
	return 0;

out_buffers:
	misc_deregister(&simple_pt_miscdev);
	return err;
}

static void simple_pt_exit(void)
{
	if (spt_hotplug_state >= 0)
		cpuhp_remove_state(spt_hotplug_state);
	misc_deregister(&simple_pt_miscdev);
	unregister_kprobe(&finalize_exec_kp);

	pr_info("exited\n");
}

module_init(simple_pt_init);
module_exit(simple_pt_exit);
MODULE_LICENSE("Dual BSD/GPL");
MODULE_AUTHOR("Andi Kleen");
