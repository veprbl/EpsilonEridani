/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import EpsilonEridani.Mathematics.Probability.InverseTransform
public import EpsilonEridani.QFT.Shower.Sudakov

/-!
# The Sudakov emission law and its scale sampler

The measure whose density at the scale `t` is the emission rate `K t` times the Sudakov factor
`sudakov K t T`, and the theorem that one uniform variate sampled through the inverse of the
Sudakov factor draws from it. This is the scale-sampling step of a parton shower, stated as a
law on the scales.

`emissionLaw K T` is that measure, defined as a density against Lebesgue measure on the scales
below the hard scale `T` (it has no mass above `T`). Its distribution function is
`emissionCdf K T`, the Sudakov factor capped at `1`, so that

`emissionLaw K T (Iic x) = ENNReal.ofReal (sudakov K x T)` for `x ≤ T`.

This is an improper fundamental theorem of calculus: the density is the derivative in the lower
limit of the Sudakov factor, whose limit at `-∞` is `0`. Without that limit the same computation
gives `sudakov K x T - L` for the limit `L` (`emissionLaw_Iic_of_le`), and the measure is
defective, with total mass `1 - L`.

That `emissionLaw K T` is the law of the first emission scale of a shower, i.e. that the Sudakov
factor is the probability of no emission under an emission process with intensity `K`, is not
proved here: no emission process is built in this file, and `emissionLaw` is defined directly by
its density.

The hypotheses of the probabilistic statements are `K` continuous and non-negative, and the
integrated kernel diverging as the scale falls. Without the divergence the sampling theorem below
genuinely fails, so the hypothesis is not decoration.

`hasLaw_emissionLaw_of_isQuantileFunction` is the sampling theorem, stated for an arbitrary
inverse of the distribution function through `EpsilonEridani.IsQuantileFunction`: an
implementation inverts the Sudakov factor in whatever closed form its kernel allows, which the
characterisation accepts without being told the formula. Reading the characterisation below the
hard scale makes the content explicit: `q u` is the least scale `x` at which the integrated kernel
`∫_x^T K` has fallen to `-log u`, which for a primitive `Γ` of `K` is the sampler
`Γ⁻¹(Γ T + log u)`. For a constant kernel everything is in closed form and the sampler is
`u ↦ T + log u / r` (`hasLaw_add_log_div_emissionLaw_const`).

The veto algorithm, which samples this same law through an overestimating kernel whose inverse is
available, is the subject of `EpsilonEridani.QFT.Shower.Sudakov`; the identity that makes it
unbiased is proved there, and the law of its output is not treated here.

## Main definitions

* `EpsilonEridani.QFT.Shower.emissionLaw`: the measure with the Sudakov density below the hard
  scale.
* `EpsilonEridani.QFT.Shower.emissionCdf`: its distribution function.

## Main results

* `EpsilonEridani.QFT.Shower.integral_Iic_mul_sudakov`: the Sudakov density integrates to the
  Sudakov factor, less its limit at `-∞`, on the scales below `x`.
* `EpsilonEridani.QFT.Shower.emissionLaw_Iic` and
  `EpsilonEridani.QFT.Shower.isProbabilityMeasure_emissionLaw`: the distribution function of
  `emissionLaw` is `emissionCdf`, and its total mass is one.
* `EpsilonEridani.QFT.Shower.cdf_emissionLaw`: `emissionCdf` is the distribution function of the
  law, in the sense of `ProbabilityTheory.cdf`.
* `EpsilonEridani.QFT.Shower.hasLaw_emissionLaw_of_isQuantileFunction` and
  `EpsilonEridani.QFT.Shower.hasLaw_add_log_div_emissionLaw_const`: the scale sampler draws from
  `emissionLaw`.

## References

* T. Sjöstrand, *A model for initial state parton showers*, Phys. Lett. B 157 (1985) 321, for the
  veto algorithm and the Sudakov density it samples.
* S. Plätzer and M. Sjödahl, *The Sudakov veto algorithm reloaded*, Eur. Phys. J. Plus 127 (2012)
  26.
-/

@[expose] public section

open MeasureTheory Measure Set Filter Topology ProbabilityTheory

open scoped ENNReal

namespace EpsilonEridani

namespace QFT

namespace Shower

variable {K : ℝ → ℝ} {T x : ℝ}

/-- The *Sudakov emission law*: the measure with density `K t * sudakov K t T` -- the rate at `t`
times the Sudakov factor between `t` and `T` -- against Lebesgue measure on the scales below the
hard scale `T`. -/
noncomputable def emissionLaw (K : ℝ → ℝ) (T : ℝ) : Measure ℝ :=
  (volume.restrict (Iic T)).withDensity fun t => ENNReal.ofReal (K t * sudakov K t T)

/-- The distribution function of `emissionLaw`: the Sudakov factor below the hard scale, and `1`
above it. -/
noncomputable def emissionCdf (K : ℝ → ℝ) (T : ℝ) (x : ℝ) : ℝ := min (sudakov K x T) 1

/-- The Sudakov density is non-negative where the kernel is. -/
theorem mul_sudakov_nonneg {t : ℝ} (hKt : 0 ≤ K t) (T : ℝ) : 0 ≤ K t * sudakov K t T :=
  mul_nonneg hKt (sudakov_pos K t T).le

/-- The distribution function of `emissionLaw` is non-negative. -/
theorem emissionCdf_nonneg (K : ℝ → ℝ) (T x : ℝ) : 0 ≤ emissionCdf K T x :=
  le_min (sudakov_pos K x T).le zero_le_one

/-- Where the kernel integrates non-negatively up to the hard scale, the distribution function of
`emissionLaw` is the Sudakov factor. -/
theorem emissionCdf_of_le (h : 0 ≤ ∫ s in x..T, K s) : emissionCdf K T x = sudakov K x T :=
  min_eq_left (sudakov_le_one h)

/-- Where the kernel integrates non-negatively from the hard scale, the distribution function of
`emissionLaw` is `1`. -/
theorem emissionCdf_of_ge (h : 0 ≤ ∫ s in T..x, K s) : emissionCdf K T x = 1 :=
  min_eq_right (one_le_sudakov (by rw [intervalIntegral.integral_symm]; linarith))

/-- The Sudakov density is continuous, for a continuous kernel. -/
@[fun_prop]
theorem continuous_mul_sudakov (hK : Continuous K) (T : ℝ) :
    Continuous fun t => K t * sudakov K t T :=
  hK.mul (continuous_sudakov (fun a b => hK.intervalIntegrable a b) T)

/-- The Sudakov density is integrable on every left-infinite interval of scales, for a continuous
non-negative kernel. -/
theorem integrableOn_Iic_mul_sudakov (hK : Continuous K) (hK0 : ∀ t, 0 ≤ K t) (T x : ℝ) :
    IntegrableOn (fun t => K t * sudakov K t T) (Iic x) := by
  have hcont := continuous_mul_sudakov hK T
  refine integrableOn_Iic_of_intervalIntegral_norm_bounded (sudakov K x T) x
    (a := id) (l := atBot) (fun _ => hcont.integrableOn_Ioc) tendsto_id
    (Eventually.of_forall fun y => ?_)
  simp only [id_eq]
  have hnorm : ∫ s in y..x, ‖K s * sudakov K s T‖ = ∫ s in y..x, K s * sudakov K s T :=
    intervalIntegral.integral_congr fun s _ =>
      Real.norm_of_nonneg (mul_sudakov_nonneg (hK0 s) T)
  rw [hnorm, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_sudakov hK s T) (hcont.intervalIntegrable _ _)]
  linarith [sudakov_pos K y T]

/-- **The Sudakov density integrates to the Sudakov factor.** On the scales below `x`, the
integral of the Sudakov density is `sudakov K x T` less the limit `L` of the Sudakov factor at
`-∞`, by the fundamental theorem of calculus on the left-infinite interval of scales. -/
theorem integral_Iic_mul_sudakov (hK : Continuous K) (hK0 : ∀ t, 0 ≤ K t) {L : ℝ}
    (hL : Tendsto (fun t => sudakov K t T) atBot (𝓝 L)) (x : ℝ) :
    ∫ t in Iic x, K t * sudakov K t T = sudakov K x T - L :=
  integral_Iic_of_hasDerivAt_of_tendsto' (fun t _ => hasDerivAt_sudakov hK t T)
    (integrableOn_Iic_mul_sudakov hK hK0 T x) hL

/-- The mass `emissionLaw` gives to a measurable set, as a `lintegral` of the Sudakov density over
the part of that set below the hard scale. -/
theorem emissionLaw_apply {s : Set ℝ} (hs : MeasurableSet s) :
    emissionLaw K T s = ∫⁻ t in s ∩ Iic T, ENNReal.ofReal (K t * sudakov K t T) := by
  rw [emissionLaw, withDensity_apply _ hs, Measure.restrict_restrict hs]

/-- Below the hard scale, `emissionLaw` gives a left-infinite interval the Sudakov factor at its
end, less the limit `L` of the Sudakov factor at `-∞`. -/
theorem emissionLaw_Iic_of_le (hK : Continuous K) (hK0 : ∀ t, 0 ≤ K t) {L : ℝ}
    (hL : Tendsto (fun t => sudakov K t T) atBot (𝓝 L)) (hx : x ≤ T) :
    emissionLaw K T (Iic x) = ENNReal.ofReal (sudakov K x T - L) := by
  rw [emissionLaw_apply measurableSet_Iic, Iic_inter_Iic, inf_eq_left.2 hx,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_Iic_mul_sudakov hK hK0 T x)
      (Eventually.of_forall fun t => mul_sudakov_nonneg (hK0 t) T),
    integral_Iic_mul_sudakov hK hK0 hL x]

/-- `emissionLaw` gives no mass above the hard scale. -/
theorem emissionLaw_Iic_of_ge (hx : T ≤ x) :
    emissionLaw K T (Iic x) = emissionLaw K T (Iic T) := by
  rw [emissionLaw_apply measurableSet_Iic, emissionLaw_apply measurableSet_Iic, Iic_inter_Iic,
    Iic_inter_Iic, inf_eq_right.2 hx, inf_idem]

/-- **The distribution function of `emissionLaw` is `emissionCdf`**, at every scale: below the
hard scale it is the Sudakov factor, and above it the mass is exhausted. -/
theorem emissionLaw_Iic (hK : Continuous K) (hK0 : ∀ t, 0 ≤ K t)
    (hdiv : Tendsto (fun t => ∫ s in t..T, K s) atBot atTop) (x : ℝ) :
    emissionLaw K T (Iic x) = ENNReal.ofReal (emissionCdf K T x) := by
  have hL := tendsto_sudakov_atBot hdiv
  rcases le_or_gt x T with hx | hx
  · rw [emissionLaw_Iic_of_le hK hK0 hL hx, sub_zero,
      emissionCdf_of_le (intervalIntegral.integral_nonneg hx fun s _ => hK0 s)]
  · rw [emissionLaw_Iic_of_ge hx.le, emissionLaw_Iic_of_le hK hK0 hL le_rfl, sub_zero,
      sudakov_self, emissionCdf_of_ge (intervalIntegral.integral_nonneg hx.le fun s _ => hK0 s)]

/-- `emissionLaw` is a probability measure when the integrated kernel diverges as the scale
falls. -/
theorem isProbabilityMeasure_emissionLaw (hK : Continuous K) (hK0 : ∀ t, 0 ≤ K t)
    (hdiv : Tendsto (fun t => ∫ s in t..T, K s) atBot atTop) :
    IsProbabilityMeasure (emissionLaw K T) := by
  refine ⟨?_⟩
  have huniv : emissionLaw K T univ = emissionLaw K T (Iic T) := by
    rw [emissionLaw_apply MeasurableSet.univ, emissionLaw_apply measurableSet_Iic, univ_inter,
      Iic_inter_Iic, inf_idem]
  rw [huniv, emissionLaw_Iic_of_le hK hK0 (tendsto_sudakov_atBot hdiv) le_rfl, sudakov_self,
    sub_zero, ENNReal.ofReal_one]

/-- The distribution function of `emissionLaw` is `emissionCdf`, in the sense of
`ProbabilityTheory.cdf`. -/
theorem cdf_emissionLaw (hK : Continuous K) (hK0 : ∀ t, 0 ≤ K t)
    (hdiv : Tendsto (fun t => ∫ s in t..T, K s) atBot atTop) :
    cdf (emissionLaw K T) = emissionCdf K T := by
  have := isProbabilityMeasure_emissionLaw hK hK0 hdiv
  funext x
  rw [← ENNReal.toReal_ofReal (cdf_nonneg _ x), ofReal_cdf, emissionLaw_Iic hK hK0 hdiv x,
    ENNReal.toReal_ofReal (emissionCdf_nonneg K T x)]

/-- **The scale sampler draws from the Sudakov emission law.** Any inverse of the Sudakov
distribution function, applied to one uniform variate on `[0, 1]`, has law `emissionLaw K T`.

This is the specification of the scale-sampling step of a parton shower: the characterisation
`IsQuantileFunction` asks only that `q u` be the least scale whose Sudakov factor reaches `u`, so
an implementation may invert its own kernel in whatever closed form it has. -/
theorem hasLaw_emissionLaw_of_isQuantileFunction (hK : Continuous K) (hK0 : ∀ t, 0 ≤ K t)
    (hdiv : Tendsto (fun t => ∫ s in t..T, K s) atBot atTop) {q : ℝ → ℝ}
    (h : IsQuantileFunction (emissionCdf K T) q) :
    HasLaw q (emissionLaw K T) (volume.restrict (Icc (0 : ℝ) 1)) :=
  have := isProbabilityMeasure_emissionLaw hK hK0 hdiv
  h.hasLaw (emissionLaw_Iic hK hK0 hdiv)

/-! ### The constant kernel

The instance where every ingredient is in closed form: a constant emission rate `r`. The
Sudakov factor is `exp (-(T - t) r)` (`EpsilonEridani.QFT.Shower.sudakov_const`), so the sampler
is `u ↦ T + log u / r` and `emissionLaw` is the law of the hard scale less an exponential variate
of rate `r`. -/

variable {r : ℝ}

/-- The integrated constant kernel diverges as the scale falls, so `emissionLaw` has total mass
one. -/
theorem tendsto_integral_const_atBot_atTop (hr : 0 < r) (T : ℝ) :
    Tendsto (fun t => ∫ _s in t..T, r) atBot atTop := by
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  have h : Tendsto (fun t : ℝ => T - t) atBot atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_left atBot T tendsto_neg_atBot_atTop
  exact h.atTop_mul_const hr

/-- Below the hard scale, the distribution function of `emissionLaw` for a constant kernel of
non-negative rate `r` is `exp (-(T - x) r)`. -/
theorem emissionCdf_const (hr : 0 ≤ r) (hx : x ≤ T) :
    emissionCdf (fun _ => r) T x = Real.exp (-((T - x) * r)) := by
  rw [emissionCdf_of_le (intervalIntegral.integral_nonneg hx fun _ _ => hr), sudakov_const]

/-- `u ↦ T + log u / r` inverts the Sudakov distribution function of a constant kernel of rate
`r`, in closed form: the characterisation is a pair of logarithmic inequalities. -/
theorem isQuantileFunction_emissionCdf_const (hr : 0 < r) (T : ℝ) :
    IsQuantileFunction (emissionCdf (fun _ => r) T) (fun u => T + Real.log u / r) := by
  intro u hu x
  rcases le_or_gt x T with hx | hx
  · rw [emissionCdf_const hr.le hx, ← Real.log_le_iff_le_exp hu.1,
      show -((T - x) * r) = (x - T) * r by ring, ← div_le_iff₀ hr]
    constructor <;> intro h <;> linarith
  · have hlog : Real.log u / r < 0 := div_neg_of_neg_of_pos (Real.log_neg hu.1 hu.2) hr
    rw [emissionCdf_of_ge (intervalIntegral.integral_nonneg hx.le fun _ _ => hr.le)]
    exact iff_of_true (by linarith) hu.2.le

/-- **The scale sampler for a constant kernel.** On `[0, 1]` with Lebesgue measure,
`u ↦ T + log u / r` has law `emissionLaw` of the constant kernel of rate `r`. -/
theorem hasLaw_add_log_div_emissionLaw_const (hr : 0 < r) (T : ℝ) :
    HasLaw (fun u => T + Real.log u / r) (emissionLaw (fun _ => r) T)
      (volume.restrict (Icc (0 : ℝ) 1)) :=
  hasLaw_emissionLaw_of_isQuantileFunction continuous_const (fun _ => hr.le)
    (tendsto_integral_const_atBot_atTop hr T) (isQuantileFunction_emissionCdf_const hr T)

end Shower

end QFT

end EpsilonEridani
