// Build-configuration queries and runtime settings used by `Lean.Shell` / `Init.Meta` / `Init.System.Platform`
// (`lean_internal_*`, from runtime/{object,memory,interrupt,thread,debug,platform}.cpp,
// util/options.cpp and library/elab_environment.cpp).
//
// The values mirror a stage1 `Release` build of Lean 4 (multi-threaded, no LLVM backend, no ASan).
// Runtime settings are stored in `LeanRuntimeSettings` so that other areas (heartbeats, memory
// checks, thread creation, debug tags) can read them.

namespace LeanInterpreter.Runtime;

/// <summary>Runtime settings changed through `Lean.Internal.set*` (see `lean_internal_set_*`).</summary>
public static class LeanRuntimeSettings
{
    /// <summary>`LEAN_BUILD_TYPE` of the emulated build.</summary>
    public const string BuildType = "Release";

    /// <summary>`LEAN_BELIEVER_TRUST_LEVEL` (kernel/environment.h).</summary>
    public const uint BelieverTrustLevel = 1024;

    /// <summary>`g_max_memory` (runtime/memory.cpp); 0 = unlimited.</summary>
    public static ulong MaxMemory;

    /// <summary>`g_max_heartbeat` (runtime/interrupt.cpp); thread-local in C.</summary>
    [ThreadStatic] public static ulong MaxHeartbeat;

    /// <summary>`lthread::set_thread_stack_size` (runtime/thread.cpp); 0 = default.</summary>
    public static ulong ThreadStackSize;

    static readonly HashSet<string> s_debugTags = new();

    /// <summary>`enable_debug` (runtime/debug.cpp).</summary>
    public static void EnableDebug(string tag)
    {
        lock (s_debugTags) s_debugTags.Add(tag);
    }

    /// <summary>`is_debug_enabled` (runtime/debug.cpp).</summary>
    public static bool IsDebugEnabled(string tag)
    {
        lock (s_debugTags) return s_debugTags.Contains(tag);
    }
}

public static unsafe partial class LeanRt
{

    /* setExitOnPanic (exit : Bool) : BaseIO Unit */
    public static Obj lean_internal_set_exit_on_panic(byte exit)
    {
        lean_set_exit_on_panic(exit != 0);
        return lean_box(0);
    }

    /* getHardwareConcurrency (_ : Unit) : UInt32 */
    public static uint lean_internal_get_hardware_concurrency(Obj unit) => (uint)System.Environment.ProcessorCount;

    /* getDefaultMaxMemory (_ : Unit) : Nat -- LEAN_DEFAULT_MAX_MEMORY is not defined by default */
    public static Obj lean_internal_get_default_max_memory(Obj unit) => lean_box(0);

    /* setMaxMemory (max : USize) : BaseIO Unit */
    public static Obj lean_internal_set_max_memory(ulong max)
    {
        LeanRuntimeSettings.MaxMemory = max;
        return lean_box(0);
    }

    /* setThreadStackSize (sz : USize) : BaseIO Unit */
    public static Obj lean_internal_set_thread_stack_size(ulong sz)
    {
        LeanRuntimeSettings.ThreadStackSize = sz;
        return lean_box(0);
    }

    /* getDefaultMaxHeartbeat (_ : Unit) : Nat -- LEAN_DEFAULT_MAX_HEARTBEAT is not defined by default */
    public static Obj lean_internal_get_default_max_heartbeat(Obj unit) => lean_box(0);

    /* setMaxHeartbeat (max : USize) : BaseIO Unit */
    public static Obj lean_internal_set_max_heartbeat(ulong max)
    {
        // `g_max_heartbeat`: the limit of the kernel's `check_heartbeat` on this thread
        // (`lean --timeout`); threads started from here inherit it
        LeanRuntimeSettings.MaxHeartbeat = max;
        LeanInterpreter.Kernel.KernelLimits.MaxHeartbeat = max;
        return lean_box(0);
    }

    /* enableDebug (tag : @& String) : BaseIO Unit */
    public static Obj lean_internal_enable_debug(Obj tag)
    {
        LeanRuntimeSettings.EnableDebug(lean_string_to_net(tag));
        return lean_box(0);
    }

    public static byte lean_internal_has_llvm_backend(Obj unit) => 0;
    public static byte lean_internal_has_address_sanitizer(Obj unit) => 0;
    public static byte lean_internal_is_multi_thread(Obj unit) => 1;
    public static byte lean_internal_is_debug(Obj unit) => 0;
    public static byte lean_internal_is_stage0(Obj unit) => 0;

    public static Obj lean_internal_get_build_type(Obj unit) => lean_mk_string(LeanRuntimeSettings.BuildType);

    /* getDefaultVerbose (_ : Unit) : Bool */
    public static byte lean_internal_get_default_verbose(Obj unit) => 1;

    static delegate*<Obj, Obj> s_num_options_get_empty;

    /* getOptionOverrides (_ : Unit) : Options -- no overrides outside of stage 0 (stdlib_flags.h) */
    public static Obj lean_internal_get_option_overrides(Obj unit)
    {
        if (s_num_options_get_empty == null)
            s_num_options_get_empty = (delegate*<Obj, Obj>)LeanExports.Get("lean_options_get_empty");
        return s_num_options_get_empty(lean_box(0));
    }

    /* getBelieverTrustLevel (_ : Unit) : UInt32 */
    public static uint lean_internal_get_believer_trust_level(Obj unit) => LeanRuntimeSettings.BelieverTrustLevel;
}
