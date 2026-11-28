/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The logarithmic divergence at the origin

`-log x → ∞` as `x → 0⁺` (`tendsto_neg_log_nhdsGT_zero`), the divergence that logarithmic
small-argument estimates compare against, such as those for the modified Bessel function `K₀`
(`EpsilonEridani.Mathematics.SpecialFunctions.BesselK.Basic`).
-/

public section

open Real Filter Topology

namespace EpsilonEridani

/-- `-log x → ∞` as `x → 0⁺`, the divergence that every logarithmic small-argument estimate
compares against. -/
theorem tendsto_neg_log_nhdsGT_zero : Tendsto (fun x : ℝ ↦ -log x) (𝓝[>] 0) atTop :=
  tendsto_neg_atBot_atTop.comp tendsto_log_nhdsGT_zero

end EpsilonEridani
