/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Particles.Fragmentation.Basic
public import EpsilonEridani.Particles.Meson.Pion

/-!
# Charge conjugation, flavour symmetry, and the favoured and unfavoured combinations

The fragmentation functions of one hadron multiplet are not independent: the discrete symmetries
relate the fragmentation of a parton into a hadron to the fragmentation of another parton into
another hadron of the same multiplet. This file states those relations and uses them to split the
fragmentation functions of a flavour into the two combinations that are quoted in practice.

The favoured and unfavoured combinations are read off a valence assignment
`valence : Hadron → Finset (Species Flavor)`, which is explicit data, so they are not a
convention. Relating them across a hadron and its antiparticle, or across the hadrons and the
flavours exchanged by a flavour symmetry, uses only the compatibility `Parton.ValenceInvariant` of
the valence assignment with the symmetry.

Two relations on a family `D` are named, both instances of `Invariant`. `ChargeConjRelation τ D`
says that the fragmentation of the antiparton of `s` into the antihadron `τ h` is the fragmentation
of `s` into `h`, and `FlavorSymmetryRelation τ ρ D` says the same for a relabelling `ρ` of the
quark flavours together with the permutation `τ` of the multiplet it induces; isospin is the case
where `ρ` exchanges the up and the down flavour. Neither is a consequence of the definition of a
fragmentation function as an interface, so both are hypotheses of the theorems that use them. Where
both hold with the same permutation of the multiplet, `Invariant.apply_eq_apply` relates the
relabelled and the conjugate parton inside a single hadron; this is what reduces the number of
independent light-hadron fragmentation functions.

For a hadron `h` and a quark flavour `i`, the *favoured* combination collects the fragmentation
into `h` of those species of flavour `i` that are valence constituents of `h`, and the
*unfavoured* combination collects the rest. A flavour for which exactly one of the quark and the
antiquark is a valence constituent is a `IsValenceFlavor`; for such a flavour each combination is
a single fragmentation function, conjugating the parton index exchanges the two, and their
difference is the valence combination `D_{q_i} - D_{qbar_i}` when the valence constituent is the
quark and its negative when it is the antiquark. For a flavour whose quark and antiquark both
occur, as in a flavour-neutral hadron, the favoured combination is the total fragmentation of the
flavour and the unfavoured one vanishes, so the two are not separated; `favored_pion_zero`
exhibits that case for the encoding of the neutral pion's valence content as all four light
species.

The pion triplet `Meson.pionMultiplet` is worked out as an instance:
`favored_pion_plus_down_eq_favored_pion_plus_up` is the familiar `D_u^{π⁺} = D_{dbar}^{π⁺}`, derived
from the two relations rather than assumed.

## Main definitions

* `EpsilonEridani.Particles.Fragmentation.ChargeConjRelation` and
  `EpsilonEridani.Particles.Fragmentation.FlavorSymmetryRelation`: the two symmetry relations.
* `EpsilonEridani.Particles.Fragmentation.partonConj`: conjugating the parton index alone.
* `EpsilonEridani.Particles.Fragmentation.favored` and
  `EpsilonEridani.Particles.Fragmentation.unfavored`: the two combinations of a hadron and a
  flavour.
* `EpsilonEridani.Particles.Fragmentation.valenceStepFrag`: an explicit family satisfying the
  relations and separating the two combinations.

## Main statements

* `Fragmentation.favored_add_unfavored`: the two combinations add up to the total fragmentation
  of the flavour.
* `Fragmentation.favored_partonConj_eq_unfavored` and
  `Fragmentation.unfavored_partonConj_eq_favored`: on a valence flavour, conjugating the parton
  index exchanges the two combinations.
* `Fragmentation.favored_eq_of_invariant` and `Fragmentation.unfavored_eq_of_invariant`: a family
  invariant under a symmetry compatible with the valence assignment has the same combinations at a
  flavour in a hadron as at the image flavour in the image hadron.
* `Fragmentation.favored_conj_of_chargeConjRelation`: under the charge-conjugation relation a
  hadron and its antiparticle have the same favoured combination.
* `Fragmentation.favored_map_of_flavorSymmetryRelation`: under a flavour-symmetry relation the
  favoured combination of a flavour in a hadron is that of the relabelled flavour in the image
  hadron.
* `Fragmentation.favored_valenceStepFrag_ne_unfavored`: the two combinations of `valenceStepFrag`
  differ at every valence flavour.
* `Fragmentation.favored_pion_plus_down_eq_favored_pion_plus_up`: `D_u^{π⁺} = D_{dbar}^{π⁺}`.

## References

* J. Collins, *Foundations of Perturbative QCD*, Cambridge University Press (2011), §12.5.
* A. Metz and A. Vossen, *Parton fragmentation functions*, Prog. Part. Nucl. Phys. 91 (2016) 136,
  `arXiv:1607.02521`, §2.3.
* D. de Florian, R. Sassot and M. Stratmann, *Global analysis of fragmentation functions for pions
  and kaons and their uncertainties*, Phys. Rev. D 75 (2007) 114010, §II.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace Particles
namespace Fragmentation

open Parton Meson

variable {Hadron Flavor : Type}

/-! ### The two symmetry relations -/

/-- A family satisfies the *charge-conjugation relation* for the antiparticle map `τ` when the
fragmentation of the antiparton of `s` into the antihadron `τ h` is the fragmentation of `s` into
`h`, `D_{τ h}^{sbar} = D_h^s`. It is the relation that the action of charge conjugation on the
light-cone correlator imposes on the fragmentation functions of a multiplet. -/
abbrev ChargeConjRelation (τ : Hadron → Hadron) (D : Frag Hadron (Species Flavor)) : Prop :=
  Invariant τ Species.conj D

/-- A family satisfies the *flavour-symmetry relation* of the symmetry `(τ, ρ)` — a relabelling `ρ`
of the quark flavours together with the permutation `τ` of the multiplet it induces — when
`D_{τ h}^{ρ s} = D_h^s`. Isospin within a light-hadron multiplet is the case where `ρ` exchanges
the up and the down flavour. -/
abbrev FlavorSymmetryRelation (τ : Hadron → Hadron) (ρ : Flavor → Flavor)
    (D : Frag Hadron (Species Flavor)) : Prop :=
  Invariant τ (Species.map ρ) D

/-- Conjugating the parton index alone: the fragmentation of the antiparton of `s` into the *same*
hadron. This is not a symmetry of a family — it compares two different physical functions — and on
a valence flavour it exchanges the favoured and the unfavoured combination. -/
def partonConj (D : Frag Hadron (Species Flavor)) : Frag Hadron (Species Flavor) :=
  comap id Species.conj D

theorem partonConj_eq_comap (D : Frag Hadron (Species Flavor)) :
    partonConj D = comap id Species.conj D :=
  (rfl)

@[simp]
theorem partonConj_apply (D : Frag Hadron (Species Flavor)) (h : Hadron) (s : Species Flavor)
    (z Q2 : ℝ) : partonConj D h s z Q2 = D h (Species.conj s) z Q2 :=
  (rfl)

@[simp]
theorem partonConj_partonConj (D : Frag Hadron (Species Flavor)) :
    partonConj (partonConj D) = D := by
  rw [partonConj_eq_comap, partonConj_eq_comap, comap_comap, Species.conj_involutive.comp_self]
  exact comap_id D

@[simp]
theorem zMoment_partonConj (D : Frag Hadron (Species Flavor)) (n : ℕ) (h : Hadron)
    (s : Species Flavor) (Q2 : ℝ) :
    zMoment (partonConj D) n h s Q2 = zMoment D n h (Species.conj s) Q2 :=
  zMoment_comap id Species.conj D n h s Q2

/-- Conjugating the parton index preserves the structural assumptions. -/
theorem Assumptions.partonConj {D : Frag Hadron (Species Flavor)} (hD : Assumptions D) :
    Assumptions (Fragmentation.partonConj D) :=
  hD.comap id Species.conj

/-! ### The favoured and the unfavoured combination -/

variable [DecidableEq Flavor]

/-- The *favoured* combination of the hadron `h` and the flavour `i` for the valence assignment
`valence`: the fragmentation into `h` of those species of flavour `i` that are valence constituents
of `h`. -/
def favored (valence : Hadron → Finset (Species Flavor)) (D : Frag Hadron (Species Flavor))
    (h : Hadron) (i : Flavor) (z Q2 : ℝ) : ℝ :=
  ∑ s ∈ Species.flavorPair i ∩ valence h, D h s z Q2

/-- The *unfavoured* combination of the hadron `h` and the flavour `i` for the valence assignment
`valence`: the fragmentation into `h` of those species of flavour `i` that are not valence
constituents of `h`. -/
def unfavored (valence : Hadron → Finset (Species Flavor)) (D : Frag Hadron (Species Flavor))
    (h : Hadron) (i : Flavor) (z Q2 : ℝ) : ℝ :=
  ∑ s ∈ Species.flavorPair i \ valence h, D h s z Q2

variable (valence : Hadron → Finset (Species Flavor)) (D : Frag Hadron (Species Flavor))

theorem favored_def (h : Hadron) (i : Flavor) (z Q2 : ℝ) :
    favored valence D h i z Q2 = ∑ s ∈ Species.flavorPair i ∩ valence h, D h s z Q2 :=
  (rfl)

theorem unfavored_def (h : Hadron) (i : Flavor) (z Q2 : ℝ) :
    unfavored valence D h i z Q2 = ∑ s ∈ Species.flavorPair i \ valence h, D h s z Q2 :=
  (rfl)

/-- The two combinations of a flavour add up to the total fragmentation of that flavour, the sum
over its quark and its antiquark. -/
theorem favored_add_unfavored (h : Hadron) (i : Flavor) (z Q2 : ℝ) :
    favored valence D h i z Q2 + unfavored valence D h i z Q2
      = D h (Species.quark i) z Q2 + D h (Species.antiquark i) z Q2 := by
  rw [favored_def, unfavored_def, Finset.sum_inter_add_sum_sdiff, Species.sum_flavorPair]

/-- Where a family is non-negative on the quark and the antiquark of a flavour, the favoured
combination of that flavour is non-negative. -/
theorem favored_nonneg {h : Hadron} {z Q2 : ℝ} (i : Flavor)
    (hD : ∀ s ∈ Species.flavorPair i, 0 ≤ D h s z Q2) : 0 ≤ favored valence D h i z Q2 :=
  Finset.sum_nonneg fun s hs => hD s (Finset.mem_inter.1 hs).1

/-- Where a family is non-negative on the quark and the antiquark of a flavour, the unfavoured
combination of that flavour is non-negative. -/
theorem unfavored_nonneg {h : Hadron} {z Q2 : ℝ} (i : Flavor)
    (hD : ∀ s ∈ Species.flavorPair i, 0 ≤ D h s z Q2) : 0 ≤ unfavored valence D h i z Q2 :=
  Finset.sum_nonneg fun s hs => hD s (Finset.mem_sdiff.1 hs).1

/-- The favoured combinations of a fragmentation family satisfy the structural assumptions. -/
theorem Assumptions.favored {D : Frag Hadron (Species Flavor)} (hD : Assumptions D)
    (valence : Hadron → Finset (Species Flavor)) :
    Assumptions (Fragmentation.favored valence D) where
  support h _ z Q2 hz := Finset.sum_eq_zero fun s _ => hD.support h s z Q2 hz
  nonneg h i z Q2 hz₀ hz₁ := favored_nonneg valence D i fun s _ => hD.nonneg h s z Q2 hz₀ hz₁

/-- The unfavoured combinations of a fragmentation family satisfy the structural assumptions. -/
theorem Assumptions.unfavored {D : Frag Hadron (Species Flavor)} (hD : Assumptions D)
    (valence : Hadron → Finset (Species Flavor)) :
    Assumptions (Fragmentation.unfavored valence D) where
  support h _ z Q2 hz := Finset.sum_eq_zero fun s _ => hD.support h s z Q2 hz
  nonneg h i z Q2 hz₀ hz₁ := unfavored_nonneg valence D i fun s _ => hD.nonneg h s z Q2 hz₀ hz₁

variable {valence D} {h : Hadron} {i : Flavor}

/-- When the quark of a flavour is its hadron's valence constituent and the antiquark is not,
the favoured combination of that flavour is the quark's fragmentation function. -/
theorem favored_eq_apply_quark (hq : Species.quark i ∈ valence h)
    (hq' : Species.antiquark i ∉ valence h) (z Q2 : ℝ) :
    favored valence D h i z Q2 = D h (Species.quark i) z Q2 := by
  have hv : Species.flavorPair i ∩ valence h = {Species.quark i} := by
    ext s
    simp only [Finset.mem_inter, Species.mem_flavorPair, Finset.mem_singleton]
    grind
  rw [favored_def, hv, Finset.sum_singleton]

/-- When the antiquark of a flavour is its hadron's valence constituent and the quark is not,
the favoured combination of that flavour is the antiquark's fragmentation function. -/
theorem favored_eq_apply_antiquark (hq' : Species.antiquark i ∈ valence h)
    (hq : Species.quark i ∉ valence h) (z Q2 : ℝ) :
    favored valence D h i z Q2 = D h (Species.antiquark i) z Q2 := by
  have hv : Species.flavorPair i ∩ valence h = {Species.antiquark i} := by
    ext s
    simp only [Finset.mem_inter, Species.mem_flavorPair, Finset.mem_singleton]
    grind
  rw [favored_def, hv, Finset.sum_singleton]

/-- When the quark of a flavour is its hadron's valence constituent and the antiquark is not,
the unfavoured combination of that flavour is the antiquark's fragmentation function. -/
theorem unfavored_eq_apply_antiquark (hq : Species.quark i ∈ valence h)
    (hq' : Species.antiquark i ∉ valence h) (z Q2 : ℝ) :
    unfavored valence D h i z Q2 = D h (Species.antiquark i) z Q2 := by
  have := favored_add_unfavored valence D h i z Q2
  rw [favored_eq_apply_quark hq hq'] at this
  linarith

/-- When the antiquark of a flavour is its hadron's valence constituent and the quark is not,
the unfavoured combination of that flavour is the quark's fragmentation function. -/
theorem unfavored_eq_apply_quark (hq' : Species.antiquark i ∈ valence h)
    (hq : Species.quark i ∉ valence h) (z Q2 : ℝ) :
    unfavored valence D h i z Q2 = D h (Species.quark i) z Q2 := by
  have := favored_add_unfavored valence D h i z Q2
  rw [favored_eq_apply_antiquark hq' hq] at this
  linarith

/-- When both the quark and the antiquark of a flavour are valence constituents of a hadron, as
in a flavour-neutral hadron, the favoured combination of that flavour is its total
fragmentation. -/
theorem favored_eq_add_of_quark_mem_of_antiquark_mem (hq : Species.quark i ∈ valence h)
    (hq' : Species.antiquark i ∈ valence h) (z Q2 : ℝ) :
    favored valence D h i z Q2 = D h (Species.quark i) z Q2 + D h (Species.antiquark i) z Q2 := by
  have hv : Species.flavorPair i ∩ valence h = Species.flavorPair i := by
    ext s
    simp only [Finset.mem_inter, Species.mem_flavorPair]
    grind
  rw [favored_def, hv, Species.sum_flavorPair]

/-- When both the quark and the antiquark of a flavour are valence constituents of a hadron, the
unfavoured combination of that flavour vanishes. -/
theorem unfavored_eq_zero_of_quark_mem_of_antiquark_mem (hq : Species.quark i ∈ valence h)
    (hq' : Species.antiquark i ∈ valence h) (z Q2 : ℝ) : unfavored valence D h i z Q2 = 0 := by
  have := favored_add_unfavored valence D h i z Q2
  rw [favored_eq_add_of_quark_mem_of_antiquark_mem hq hq'] at this
  linarith

/-- When neither the quark nor the antiquark of a flavour is a valence constituent of a hadron,
the favoured combination of that flavour vanishes. -/
theorem favored_eq_zero_of_quark_notMem_of_antiquark_notMem (hq : Species.quark i ∉ valence h)
    (hq' : Species.antiquark i ∉ valence h) (z Q2 : ℝ) : favored valence D h i z Q2 = 0 := by
  have hv : Species.flavorPair i ∩ valence h = ∅ := by
    ext s
    simp only [Finset.mem_inter, Species.mem_flavorPair, Finset.notMem_empty, iff_false]
    grind
  rw [favored_def, hv, Finset.sum_empty]

/-- When neither the quark nor the antiquark of a flavour is a valence constituent of a hadron,
the unfavoured combination of that flavour is its total fragmentation. -/
theorem unfavored_eq_add_of_quark_notMem_of_antiquark_notMem (hq : Species.quark i ∉ valence h)
    (hq' : Species.antiquark i ∉ valence h) (z Q2 : ℝ) :
    unfavored valence D h i z Q2
      = D h (Species.quark i) z Q2 + D h (Species.antiquark i) z Q2 := by
  have := favored_add_unfavored valence D h i z Q2
  rw [favored_eq_zero_of_quark_notMem_of_antiquark_notMem hq hq'] at this
  linarith

/-- On a flavour whose valence constituent is the quark, the difference of the two combinations is
the valence combination `D_{q_i} - D_{qbar_i}` of that flavour. -/
theorem favored_sub_unfavored_eq_of_quark_mem (hq : Species.quark i ∈ valence h)
    (hq' : Species.antiquark i ∉ valence h) (z Q2 : ℝ) :
    favored valence D h i z Q2 - unfavored valence D h i z Q2
      = D h (Species.quark i) z Q2 - D h (Species.antiquark i) z Q2 := by
  rw [favored_eq_apply_quark hq hq', unfavored_eq_apply_antiquark hq hq']

/-- On a flavour whose valence constituent is the antiquark, the difference of the two combinations
is the opposite `D_{qbar_i} - D_{q_i}` of the valence combination of that flavour. -/
theorem favored_sub_unfavored_eq_of_antiquark_mem (hq' : Species.antiquark i ∈ valence h)
    (hq : Species.quark i ∉ valence h) (z Q2 : ℝ) :
    favored valence D h i z Q2 - unfavored valence D h i z Q2
      = D h (Species.antiquark i) z Q2 - D h (Species.quark i) z Q2 := by
  rw [favored_eq_apply_antiquark hq' hq, unfavored_eq_apply_quark hq' hq]

/-! ### Reindexing the combinations by conjugation -/

/-- On a valence flavour, conjugating the parton index carries the favoured combination to the
unfavoured one. -/
theorem favored_partonConj_eq_unfavored (hi : IsValenceFlavor valence h i) (z Q2 : ℝ) :
    favored valence (partonConj D) h i z Q2 = unfavored valence D h i z Q2 := by
  rw [favored_def, unfavored_def, ← hi.image_conj_inter_valence_eq_sdiff, partonConj_eq_comap]
  exact (sum_image_comap id Species.conj_involutive.injective.injOn D h z Q2).symm

/-- On a valence flavour, conjugating the parton index carries the unfavoured combination to the
favoured one. -/
theorem unfavored_partonConj_eq_favored (hi : IsValenceFlavor valence h i) (z Q2 : ℝ) :
    unfavored valence (partonConj D) h i z Q2 = favored valence D h i z Q2 := by
  have := favored_partonConj_eq_unfavored (D := partonConj D) hi z Q2
  rwa [partonConj_partonConj, eq_comm] at this

/-- For a family invariant under `(τ, σ)`, a valence assignment compatible with `(τ, σ)`, and a map
`σ` carrying the two species of the flavour `i` injectively onto those of the flavour `j`, the
favoured combination of `j` in the image hadron is the favoured combination of `i` in the hadron. -/
theorem favored_eq_of_invariant {τ : Hadron → Hadron} {σ : Species Flavor → Species Flavor}
    {j : Flavor} (hv : ValenceInvariant valence τ σ)
    (hpair : (Species.flavorPair i).image σ = Species.flavorPair j)
    (hσ : Set.InjOn σ (Species.flavorPair i : Set (Species Flavor))) (hD : Invariant τ σ D)
    (h : Hadron) (z Q2 : ℝ) : favored valence D (τ h) j z Q2 = favored valence D h i z Q2 := by
  rw [favored_def, favored_def, ← hpair, ← hv.image_inter_valence,
    hD.sum_image (hσ.mono (Finset.coe_subset.2 Finset.inter_subset_left))]

/-- For a family invariant under `(τ, σ)`, a valence assignment compatible with `(τ, σ)`, and a map
`σ` carrying the two species of the flavour `i` injectively onto those of the flavour `j`, the
unfavoured combination of `j` in the image hadron is the unfavoured combination of `i` in the
hadron. -/
theorem unfavored_eq_of_invariant {τ : Hadron → Hadron} {σ : Species Flavor → Species Flavor}
    {j : Flavor} (hv : ValenceInvariant valence τ σ)
    (hpair : (Species.flavorPair i).image σ = Species.flavorPair j)
    (hσ : Set.InjOn σ (Species.flavorPair i : Set (Species Flavor))) (hD : Invariant τ σ D)
    (h : Hadron) (z Q2 : ℝ) : unfavored valence D (τ h) j z Q2 = unfavored valence D h i z Q2 := by
  rw [unfavored_def, unfavored_def, ← hpair, ← hv.image_sdiff_valence,
    hD.sum_image (hσ.mono (Finset.coe_subset.2 Finset.sdiff_subset))]

/-- Under the charge-conjugation relation of the antiparticle map `τ`, for a valence assignment
compatible with taking the antiparticle, a hadron and its antiparticle have the same favoured
combination at every flavour. -/
theorem favored_conj_of_chargeConjRelation {τ : Hadron → Hadron}
    (hv : ValenceInvariant valence τ Species.conj) (hCC : ChargeConjRelation τ D) (h : Hadron)
    (i : Flavor) (z Q2 : ℝ) : favored valence D (τ h) i z Q2 = favored valence D h i z Q2 :=
  favored_eq_of_invariant hv (Species.image_conj_flavorPair i)
    Species.conj_involutive.injective.injOn hCC h z Q2

/-- Under the charge-conjugation relation of the antiparticle map `τ`, for a valence assignment
compatible with taking the antiparticle, a hadron and its antiparticle have the same unfavoured
combination at every flavour. -/
theorem unfavored_conj_of_chargeConjRelation {τ : Hadron → Hadron}
    (hv : ValenceInvariant valence τ Species.conj) (hCC : ChargeConjRelation τ D) (h : Hadron)
    (i : Flavor) (z Q2 : ℝ) : unfavored valence D (τ h) i z Q2 = unfavored valence D h i z Q2 :=
  unfavored_eq_of_invariant hv (Species.image_conj_flavorPair i)
    Species.conj_involutive.injective.injOn hCC h z Q2

/-- Under the flavour-symmetry relation of `(τ, ρ)`, for a valence assignment compatible with the
symmetry, the favoured combination of the relabelled flavour in the image hadron is the favoured
combination of the flavour in the hadron. -/
theorem favored_map_of_flavorSymmetryRelation {τ : Hadron → Hadron} {ρ : Flavor → Flavor}
    (hv : ValenceInvariant valence τ (Species.map ρ))
    (hFS : FlavorSymmetryRelation τ ρ D) (h : Hadron) (i : Flavor) (z Q2 : ℝ) :
    favored valence D (τ h) (ρ i) z Q2 = favored valence D h i z Q2 :=
  favored_eq_of_invariant hv (Species.image_map_flavorPair ρ i) (Species.injOn_map_flavorPair ρ i)
    hFS h z Q2

/-- Under the flavour-symmetry relation of `(τ, ρ)`, for a valence assignment compatible with the
symmetry, the unfavoured combination of the relabelled flavour in the image hadron is the
unfavoured combination of the flavour in the hadron. -/
theorem unfavored_map_of_flavorSymmetryRelation {τ : Hadron → Hadron} {ρ : Flavor → Flavor}
    (hv : ValenceInvariant valence τ (Species.map ρ))
    (hFS : FlavorSymmetryRelation τ ρ D) (h : Hadron) (i : Flavor) (z Q2 : ℝ) :
    unfavored valence D (τ h) (ρ i) z Q2 = unfavored valence D h i z Q2 :=
  unfavored_eq_of_invariant hv (Species.image_map_flavorPair ρ i)
    (Species.injOn_map_flavorPair ρ i) hFS h z Q2

/-! ### An explicit family -/

/-- An explicit fragmentation family for a valence assignment: it takes the value `2 z` on the
valence species of a hadron and `1 - z` on every other species, cut off outside the unit interval.
It satisfies `Assumptions`, it is invariant under every symmetry the valence assignment is
compatible with (`invariant_valenceStepFrag`), so in particular it satisfies the charge-conjugation
relation of a valence assignment compatible with taking the antiparticle, and it separates the
favoured from the unfavoured combination of every valence flavour. -/
def valenceStepFrag (valence : Hadron → Finset (Species Flavor)) : Frag Hadron (Species Flavor) :=
  indicatorUnitInterval fun h s z _ => if s ∈ valence h then 2 * z else 1 - z

theorem valenceStepFrag_def (valence : Hadron → Finset (Species Flavor)) :
    valenceStepFrag valence
      = indicatorUnitInterval fun h s z _ => if s ∈ valence h then 2 * z else 1 - z :=
  (rfl)

/-- On the unit interval, `valenceStepFrag` is `2 z` on a valence species. -/
theorem valenceStepFrag_apply_of_mem (valence : Hadron → Finset (Species Flavor)) {h : Hadron}
    {s : Species Flavor} {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ valence h) (Q2 : ℝ) :
    valenceStepFrag valence h s z Q2 = 2 * z := by
  rw [valenceStepFrag_def, indicatorUnitInterval_of_mem _ hz, ite_eq_left hs]

/-- On the unit interval, `valenceStepFrag` is `1 - z` off the valence species. -/
theorem valenceStepFrag_apply_of_notMem (valence : Hadron → Finset (Species Flavor)) {h : Hadron}
    {s : Species Flavor} {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) (hs : s ∉ valence h) (Q2 : ℝ) :
    valenceStepFrag valence h s z Q2 = 1 - z := by
  rw [valenceStepFrag_def, indicatorUnitInterval_of_mem _ hz, ite_eq_right hs]

/-- `valenceStepFrag` is a fragmentation family: it is supported in, and non-negative on, the
unit interval. -/
theorem assumptions_valenceStepFrag (valence : Hadron → Finset (Species Flavor)) :
    Assumptions (valenceStepFrag valence) := by
  refine assumptions_indicatorUnitInterval fun h s z Q2 hz₀ hz₁ => ?_
  split
  · positivity
  · linarith

/-- `valenceStepFrag` is invariant under a map of the hadrons and a map of the species exactly
because the valence assignment is. -/
theorem invariant_valenceStepFrag (valence : Hadron → Finset (Species Flavor))
    {τ : Hadron → Hadron} {σ : Species Flavor → Species Flavor}
    (hv : ValenceInvariant valence τ σ) :
    Invariant τ σ (valenceStepFrag valence) := by
  rw [invariant_def, valenceStepFrag_def, comap_indicatorUnitInterval]
  congr 1
  funext h s z _
  simp only [comap_apply, hv.mem_iff]

/-- On a valence flavour the favoured combination of `valenceStepFrag` is `2 z`. -/
theorem favored_valenceStepFrag (hi : IsValenceFlavor valence h i) {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1) (Q2 : ℝ) :
    favored valence (valenceStepFrag valence) h i z Q2 = 2 * z := by
  rcases isValenceFlavor_iff.1 hi with ⟨hq, hq'⟩ | ⟨hq', hq⟩
  · rw [favored_eq_apply_quark hq hq', valenceStepFrag_apply_of_mem valence hz hq]
  · rw [favored_eq_apply_antiquark hq' hq, valenceStepFrag_apply_of_mem valence hz hq']

/-- On a valence flavour the unfavoured combination of `valenceStepFrag` is `1 - z`. -/
theorem unfavored_valenceStepFrag (hi : IsValenceFlavor valence h i) {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1) (Q2 : ℝ) :
    unfavored valence (valenceStepFrag valence) h i z Q2 = 1 - z := by
  rcases isValenceFlavor_iff.1 hi with ⟨hq, hq'⟩ | ⟨hq', hq⟩
  · rw [unfavored_eq_apply_antiquark hq hq', valenceStepFrag_apply_of_notMem valence hz hq']
  · rw [unfavored_eq_apply_quark hq' hq, valenceStepFrag_apply_of_notMem valence hz hq]

/-- On a valence flavour, the favoured and the unfavoured combination of `valenceStepFrag` are
different functions of the momentum fraction and the scale: at `z = 1/2` the favoured combination
is `1` and the unfavoured one is `1/2`. For a valence assignment compatible with a symmetry,
`valenceStepFrag` satisfies the corresponding relation (`invariant_valenceStepFrag`), so such a
relation does not identify the two combinations; for the pion triplet this is
`exists_chargeConjRelation_and_flavorSymmetryRelation_favored_ne_unfavored`. -/
theorem favored_valenceStepFrag_ne_unfavored (hi : IsValenceFlavor valence h i) :
    favored valence (valenceStepFrag valence) h i
      ≠ unfavored valence (valenceStepFrag valence) h i := by
  intro heq
  have h₁ := congr_fun (congr_fun heq (1 / 2)) 0
  rw [favored_valenceStepFrag hi (by norm_num), unfavored_valenceStepFrag hi (by norm_num)] at h₁
  norm_num at h₁

/-! ### The pion triplet -/

/-- The favoured combination of the positive pion at the up flavour is the fragmentation of the
up quark. -/
@[simp]
theorem favored_pion_plus_up (D : Frag Pion (Species UpDownFlavor)) (z Q2 : ℝ) :
    favored Pion.valence D .plus .up z Q2 = D .plus (.quark .up) z Q2 :=
  favored_eq_apply_quark (by simp) (by simp) z Q2

/-- The favoured combination of the positive pion at the down flavour is the fragmentation of
the down antiquark. -/
@[simp]
theorem favored_pion_plus_down (D : Frag Pion (Species UpDownFlavor)) (z Q2 : ℝ) :
    favored Pion.valence D .plus .down z Q2 = D .plus (.antiquark .down) z Q2 :=
  favored_eq_apply_antiquark (by simp) (by simp) z Q2

/-- The unfavoured combination of the positive pion at the up flavour is the fragmentation of
the up antiquark. -/
@[simp]
theorem unfavored_pion_plus_up (D : Frag Pion (Species UpDownFlavor)) (z Q2 : ℝ) :
    unfavored Pion.valence D .plus .up z Q2 = D .plus (.antiquark .up) z Q2 :=
  unfavored_eq_apply_antiquark (by simp) (by simp) z Q2

/-- The unfavoured combination of the positive pion at the down flavour is the fragmentation of
the down quark. -/
@[simp]
theorem unfavored_pion_plus_down (D : Frag Pion (Species UpDownFlavor)) (z Q2 : ℝ) :
    unfavored Pion.valence D .plus .down z Q2 = D .plus (.quark .down) z Q2 :=
  unfavored_eq_apply_quark (by simp) (by simp) z Q2

/-- The favoured combination of the negative pion at the up flavour is the fragmentation of the
up antiquark. -/
@[simp]
theorem favored_pion_minus_up (D : Frag Pion (Species UpDownFlavor)) (z Q2 : ℝ) :
    favored Pion.valence D .minus .up z Q2 = D .minus (.antiquark .up) z Q2 :=
  favored_eq_apply_antiquark (by simp) (by simp) z Q2

/-- The favoured combination of the negative pion at the down flavour is the fragmentation of
the down quark. -/
@[simp]
theorem favored_pion_minus_down (D : Frag Pion (Species UpDownFlavor)) (z Q2 : ℝ) :
    favored Pion.valence D .minus .down z Q2 = D .minus (.quark .down) z Q2 :=
  favored_eq_apply_quark (by simp) (by simp) z Q2

/-- The unfavoured combination of the negative pion at the up flavour is the fragmentation of
the up quark. -/
@[simp]
theorem unfavored_pion_minus_up (D : Frag Pion (Species UpDownFlavor)) (z Q2 : ℝ) :
    unfavored Pion.valence D .minus .up z Q2 = D .minus (.quark .up) z Q2 :=
  unfavored_eq_apply_quark (by simp) (by simp) z Q2

/-- The unfavoured combination of the negative pion at the down flavour is the fragmentation of
the down antiquark. -/
@[simp]
theorem unfavored_pion_minus_down (D : Frag Pion (Species UpDownFlavor)) (z Q2 : ℝ) :
    unfavored Pion.valence D .minus .down z Q2 = D .minus (.antiquark .down) z Q2 :=
  unfavored_eq_apply_antiquark (by simp) (by simp) z Q2

/-- The valence content of the flavour-neutral pion is encoded as all four light species, so each
flavour has both its quark and its antiquark as valence constituents and the favoured combination
is the total fragmentation of the flavour. This is a consequence of that encoding, not a physical
favoured fragmentation function: the two combinations are not separated for the neutral pion, as
`not_isValenceFlavor_pion_zero` records. -/
@[simp]
theorem favored_pion_zero (D : Frag Pion (Species UpDownFlavor)) (i : UpDownFlavor) (z Q2 : ℝ) :
    favored Pion.valence D .zero i z Q2
      = D .zero (.quark i) z Q2 + D .zero (.antiquark i) z Q2 :=
  favored_eq_add_of_quark_mem_of_antiquark_mem (by cases i <;> simp) (by cases i <;> simp) z Q2

/-- The valence content of the flavour-neutral pion is encoded as all four light species, so its
unfavoured combinations vanish. This is a consequence of that encoding, not a physical statement
that the unfavoured fragmentation into the neutral pion vanishes: the two combinations are not
separated for the neutral pion, as `not_isValenceFlavor_pion_zero` records. -/
@[simp]
theorem unfavored_pion_zero (D : Frag Pion (Species UpDownFlavor)) (i : UpDownFlavor) (z Q2 : ℝ) :
    unfavored Pion.valence D .zero i z Q2 = 0 :=
  unfavored_eq_zero_of_quark_mem_of_antiquark_mem (by cases i <;> simp) (by cases i <;> simp) z Q2

/-- The two favoured combinations of the positive pion agree: `D_u^{π⁺} = D_{dbar}^{π⁺}`. This is
the relation that reduces the independent pion fragmentation functions to one favoured and one
unfavoured function, and it is a consequence of charge conjugation together with isospin, not a
separate assumption. -/
theorem favored_pion_plus_down_eq_favored_pion_plus_up
    {D : Frag Pion (Species UpDownFlavor)} (hCC : ChargeConjRelation Pion.conj D)
    (hI : FlavorSymmetryRelation Pion.conj UpDownFlavor.swap D) (z Q2 : ℝ) :
    favored Pion.valence D .plus .down z Q2 = favored Pion.valence D .plus .up z Q2 := by
  rw [favored_pion_plus_down, favored_pion_plus_up]
  have h1 := Invariant.apply_eq_apply Pion.conj_involutive.surjective hCC hI .plus
    (Species.quark .down) z Q2
  simpa using h1.symm

/-- The two unfavoured combinations of the positive pion agree: `D_d^{π⁺} = D_{ubar}^{π⁺}`. -/
theorem unfavored_pion_plus_down_eq_unfavored_pion_plus_up
    {D : Frag Pion (Species UpDownFlavor)} (hCC : ChargeConjRelation Pion.conj D)
    (hI : FlavorSymmetryRelation Pion.conj UpDownFlavor.swap D) (z Q2 : ℝ) :
    unfavored Pion.valence D .plus .down z Q2 = unfavored Pion.valence D .plus .up z Q2 := by
  rw [unfavored_pion_plus_down, unfavored_pion_plus_up]
  have h1 := Invariant.apply_eq_apply Pion.conj_involutive.surjective hCC hI .plus
    (Species.quark .up) z Q2
  simpa using h1

/-- The two relations of the pion triplet are satisfied together by a family whose favoured and
unfavoured combinations differ, so the two relations do not identify the favoured with the
unfavoured combination. -/
theorem exists_chargeConjRelation_and_flavorSymmetryRelation_favored_ne_unfavored :
    ∃ D : Frag Pion (Species UpDownFlavor), Assumptions D ∧ ChargeConjRelation Pion.conj D ∧
      FlavorSymmetryRelation Pion.conj UpDownFlavor.swap D ∧
      favored Pion.valence D .plus .up ≠ unfavored Pion.valence D .plus .up :=
  ⟨valenceStepFrag Pion.valence, assumptions_valenceStepFrag _,
    invariant_valenceStepFrag _ valenceInvariant_pion_conj,
    invariant_valenceStepFrag _ valenceInvariant_pion_swap,
    favored_valenceStepFrag_ne_unfavored (isValenceFlavor_pion_plus .up)⟩

end Fragmentation
end Particles
end EpsilonEridani
