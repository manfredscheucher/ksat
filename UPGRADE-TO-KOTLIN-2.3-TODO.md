# TODO for a future agent: upgrade this repo to Kotlin 2.3.21

This repo is still on **Kotlin 2.2.20**. Six sibling apps were already upgraded to
**Kotlin 2.3.21 + Compose Multiplatform 1.12.1 + coroutines 1.11.0** — use them as the
reference for how to do this one. Don't reinvent it; copy what worked.

## Why 2.3 (and when it actually matters)

The driver was iOS: the KSafe library (`eu.anifantakis:ksafe`) ships an iosArm64 klib
built with Kotlin 2.3.x (ABI 2.3.0), which refuses to link against a 2.2.x project. If
THIS repo does not use KSafe and has no iOS target, the upgrade is low-urgency — but
keeping the version matrix aligned across repos is still worth it.

## Reference commits (read these diffs first)

- `~/github/OpenYarnStash` commit `c0f1829` — the canonical app upgrade.
- `~/github/MisterManager` commit `cdfd66a`.
- `~/github/kotlin-common` commit `f4bc8ab` (the version bump) + `c21a807` (drop iosX64)
  + `2caf0fd` (sync-server thin jar).
- Games: kotlidor `31c29f6`, kotlidozo `6003f29`, kotlichess `b440b78`, luckySweep `15410bf`.

## The version matrix (verified against Maven metadata)

```
kotlin               = 2.3.21
composeMultiplatform = 1.12.1
kotlinx-coroutines   = 1.11.0
kotlinBrowser        = 2026.9.3   # only if the repo has a js/wasm target using kotlin-wrappers
# AGP stayed at 8.13.2
```
Bump these in `gradle/libs.versions.toml`.

## Two real bugs 2.3 surfaced (check for them here too)

2.3 has stricter expect/actual resolution and dropped a couple of stdlib symbols. In the
six upgraded repos these broke the iOS build and had to be fixed:

1. **Missing `isDebugBuild` iOS actual** — if the repo declares `expect val isDebugBuild`
   in commonMain, make sure `src/iosMain/.../Platform.ios.kt` has
   `actual val isDebugBuild: Boolean = true`. MisterManager was missing it.
2. **Missing expect/actual for Native** — any `expect fun`/`expect val` without an iosMain
   actual now fails to compile (`Expected ... has no actual declaration ... for Native`).
   kotligame-common's `PlatformBackHandler` was missing its iOS actual (added as a no-op).
3. **`platform.Foundation.exit` was removed** — replace with
   `import kotlin.system.exitProcess; exitProcess(0)`.
4. **`iosX64()`** (Intel simulator) target: dropped in kotlin-common since all devices are
   arm64. Optional, only if it causes metadata resolution trouble.

## Submodule handling (IMPORTANT — follow the global rule)

If this repo has a `kotlin-common` / `kotligame-common` / etc. submodule, DO NOT
`git fetch` or `submodule update --remote`. The owner checkout lives at
`~/github/<submodule>`. Propagate its already-upgraded commit locally:
`git merge-base --is-ancestor <old-pin> <new>` (ancestor check, no rollback) →
`git -C ~/github/<sub> pack-objects --revs --stdout '<new> ^<old-pin>' | git -C <repo>/<sub> unpack-objects`
→ `git -C <repo>/<sub> checkout <new>` → `git -C <repo> add <sub>`. See
`~/.claude/CLAUDE.md` ("Submodul-Pointer propagieren") for the exact commands.

## Verify before committing (do NOT trust exit code — grep for "BUILD SUCCESSFUL")

```
./gradlew :composeApp:jvmTest                      # or the repo's test task
./gradlew :composeApp:compileKotlinIosArm64        # if there is an iOS target
```
A Gradle run can print `BUILD FAILED` yet still exit 0 in some setups — always grep the
log for `BUILD SUCCESSFUL`. Commit message style: short, e.g.
`Upgrade to Kotlin 2.3.21 + Compose MP 1.12.1`. Never push — that's Manfred's job.

Delete this file once the upgrade is done.
