/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Particles.Parton.Species

/-!
# The valence content of a hadron multiplet

The valence content of a family of hadrons is a map `valence` sending a hadron `h` to the finite
set of parton species that are valence constituents of `h`. The valence assignment is explicit
data, so whatever is read off it is not a convention.

A flavour for which exactly one of the quark and the antiquark is a valence constituent is a
`IsValenceFlavor`. This holds for each flavour that occurs in a flavoured meson and fails for a
flavour-neutral hadron.

A valence assignment is a `ValenceInvariant` of a map `τ` of the hadrons and a map `σ` of the
species when `σ s` is a valence constituent of `τ h` exactly when `s` is one of `h`. This is the
compatibility of the valence content with a symmetry, such as charge conjugation or isospin.

A multiplet of hadrons closed under taking the antiparticle is a `HadronMultiplet`: the
antiparticle involution `conj` on the hadrons, the valence content, and the compatibility of the
two, that the valence constituents of the antiparticle are the antiparticles of the valence
constituents. The pion triplet is worked out as an instance in the module
`EpsilonEridani.Particles.Meson.Pion`.

## Main definitions

* `EpsilonEridani.Particles.Parton.IsValenceFlavor`: exactly one of the quark and the antiquark of a
  flavour is a valence constituent of a hadron.
* `EpsilonEridani.Particles.Parton.ValenceInvariant`: the valence content is compatible with a map
  of the hadrons and a map of the species.
* `EpsilonEridani.Particles.Parton.HadronMultiplet`: a hadron multiplet with its antiparticle map
  and valence content.

## Main statements

* `IsValenceFlavor.image_conj_inter_valence_eq_sdiff`: at a valence flavour, conjugation carries
  the valence species of that flavour in a hadron to its non-valence species.
* `ValenceInvariant.image_inter_valence` and `ValenceInvariant.image_sdiff_valence`: a compatible
  map of the species carries the valence and the non-valence species of a hadron within a set to
  those of its image within the image set.
* `ValenceInvariant.image_valence`: a compatible surjective map of the species carries the valence
  content of a hadron to that of its image.
* `HadronMultiplet.valenceInvariant_conj`: the valence content of a multiplet is compatible with
  taking the antiparticle.
* `HadronMultiplet.image_conj_valence`: conjugation carries the valence content of a hadron to that
  of its antiparticle.
* `HadronMultiplet.image_conj_inter_valence` and `HadronMultiplet.image_conj_sdiff_valence`:
  conjugation carries the valence and the non-valence species of a flavour in a hadron to those in
  its antiparticle.
* `IsValenceFlavor.conj`: for a valence content compatible with conjugation, a valence flavour of a
  hadron is a valence flavour of its antiparticle.
-/

public section

namespace EpsilonEridani
namespace Particles
namespace Parton

variable {Hadron Flavor : Type}

/-- The flavour `i` is a *valence flavour* of the hadron `h` for the valence content `valence` when
exactly one of the quark and the antiquark of flavour `i` is a valence constituent of `h`. This
holds for each flavour that occurs in a flavoured meson; it fails for a flavour whose quark and
antiquark both occur, as in a flavour-neutral hadron, and for a flavour that does not occur at
all. -/
def IsValenceFlavor (valence : Hadron → Finset (Species Flavor)) (h : Hadron) (i : Flavor) :
    Prop :=
  Xor (Species.quark i ∈ valence h) (Species.antiquark i ∈ valence h)

section IsValenceFlavor

variable {valence : Hadron → Finset (Species Flavor)} {h : Hadron} {i : Flavor}

theorem isValenceFlavor_iff : IsValenceFlavor valence h i ↔
    Xor (Species.quark i ∈ valence h) (Species.antiquark i ∈ valence h) :=
  Iff.rfl

/-- A flavour whose quark, and not whose antiquark, is a valence constituent is a valence
flavour. -/
theorem isValenceFlavor_of_quark_mem (hq : Species.quark i ∈ valence h)
    (hq' : Species.antiquark i ∉ valence h) : IsValenceFlavor valence h i :=
  Or.inl ⟨hq, hq'⟩

/-- A flavour whose antiquark, and not whose quark, is a valence constituent is a valence
flavour. -/
theorem isValenceFlavor_of_antiquark_mem (hq' : Species.antiquark i ∈ valence h)
    (hq : Species.quark i ∉ valence h) : IsValenceFlavor valence h i :=
  Or.inr ⟨hq', hq⟩

/-- At a valence flavour, the antiquark is a valence constituent exactly when the quark is
not. -/
theorem IsValenceFlavor.antiquark_mem_iff (hi : IsValenceFlavor valence h i) :
    Species.antiquark i ∈ valence h ↔ Species.quark i ∉ valence h :=
  (xor_iff_not_iff'.1 hi).symm

/-- At a valence flavour, the quark is a valence constituent exactly when the antiquark is
not. -/
theorem IsValenceFlavor.quark_mem_iff (hi : IsValenceFlavor valence h i) :
    Species.quark i ∈ valence h ↔ Species.antiquark i ∉ valence h :=
  xor_iff_iff_not.1 hi

/-- At a valence flavour, conjugation carries the valence species of that flavour in a hadron to
the non-valence species of that flavour in the same hadron. -/
theorem IsValenceFlavor.image_conj_inter_valence_eq_sdiff [DecidableEq Flavor]
    (hi : IsValenceFlavor valence h i) :
    (Species.flavorPair i ∩ valence h).image Species.conj = Species.flavorPair i \ valence h := by
  ext s
  simp only [Finset.mem_image, Finset.mem_inter, Finset.mem_sdiff, Species.mem_flavorPair]
  rcases hi with ⟨hq, hq'⟩ | ⟨hq', hq⟩ <;> grind [Species.conj_quark, Species.conj_antiquark]

end IsValenceFlavor

/-- The valence content `valence` is *invariant* under a map `τ` of the hadrons and a map `σ` of the
species when `σ s` is a valence constituent of `τ h` exactly when `s` is a valence constituent of
`h`. This is the compatibility of the valence content with a symmetry `(τ, σ)` of the hadrons and
the partons, such as charge conjugation or a relabelling of the quark flavours. -/
def ValenceInvariant (valence : Hadron → Finset (Species Flavor)) (τ : Hadron → Hadron)
    (σ : Species Flavor → Species Flavor) : Prop :=
  ∀ h s, σ s ∈ valence (τ h) ↔ s ∈ valence h

section ValenceInvariant

variable {valence : Hadron → Finset (Species Flavor)} {τ : Hadron → Hadron}
  {σ : Species Flavor → Species Flavor}

theorem valenceInvariant_iff : ValenceInvariant valence τ σ ↔
    ∀ h s, σ s ∈ valence (τ h) ↔ s ∈ valence h :=
  Iff.rfl

theorem ValenceInvariant.mem_iff (hv : ValenceInvariant valence τ σ) (h : Hadron)
    (s : Species Flavor) : σ s ∈ valence (τ h) ↔ s ∈ valence h :=
  hv h s

/-- A compatible map of the species carries the valence constituents of a hadron lying in a set `t`
to the valence constituents of the image hadron lying in the image of `t`. -/
theorem ValenceInvariant.image_inter_valence [DecidableEq Flavor]
    (hv : ValenceInvariant valence τ σ) (t : Finset (Species Flavor)) (h : Hadron) :
    (t ∩ valence h).image σ = t.image σ ∩ valence (τ h) := by
  ext s
  simp only [Finset.mem_image, Finset.mem_inter]
  constructor
  · rintro ⟨a, ⟨ha, hah⟩, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, (hv.mem_iff h a).2 hah⟩
  · rintro ⟨⟨a, ha, rfl⟩, hah⟩
    exact ⟨a, ⟨ha, (hv.mem_iff h a).1 hah⟩, rfl⟩

/-- A compatible map of the species carries the non-valence species of a hadron lying in a set `t`
to the non-valence species of the image hadron lying in the image of `t`. -/
theorem ValenceInvariant.image_sdiff_valence [DecidableEq Flavor]
    (hv : ValenceInvariant valence τ σ) (t : Finset (Species Flavor)) (h : Hadron) :
    (t \ valence h).image σ = t.image σ \ valence (τ h) := by
  ext s
  simp only [Finset.mem_image, Finset.mem_sdiff]
  constructor
  · rintro ⟨a, ⟨ha, hah⟩, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, mt (hv.mem_iff h a).1 hah⟩
  · rintro ⟨⟨a, ha, rfl⟩, hah⟩
    exact ⟨a, ⟨ha, mt (hv.mem_iff h a).2 hah⟩, rfl⟩

/-- A compatible surjective map of the species carries the valence content of a hadron to that of
its image. -/
theorem ValenceInvariant.image_valence [DecidableEq Flavor] (hv : ValenceInvariant valence τ σ)
    (hσ : Function.Surjective σ) (h : Hadron) : (valence h).image σ = valence (τ h) := by
  ext s
  obtain ⟨t, rfl⟩ := hσ s
  rw [hv.mem_iff, Finset.mem_image]
  refine ⟨?_, fun ht => ⟨t, ht, rfl⟩⟩
  rintro ⟨a, ha, hat⟩
  rwa [← hv.mem_iff h, ← hat, hv.mem_iff]

end ValenceInvariant

/-- The discrete data of a multiplet of observed hadrons closed under taking the antiparticle: the
antiparticle map `conj` on the hadrons and the valence content `valence h`, the finite set of
parton species that are valence constituents of `h`. The two are tied by `mem_valence_conj`: the
valence constituents of the antiparticle are the antiparticles of the valence constituents. -/
@[ext]
structure HadronMultiplet (Hadron Flavor : Type) where
  /-- The antiparticle of a hadron of the multiplet. -/
  conj : Hadron → Hadron
  /-- Taking the antiparticle twice returns the hadron. -/
  conj_involutive : Function.Involutive conj
  /-- The parton species that are valence constituents of a hadron of the multiplet. -/
  valence : Hadron → Finset (Species Flavor)
  /-- A species is a valence constituent of the antiparticle exactly when its antiparticle is a
  valence constituent of the hadron. -/
  mem_valence_conj (h : Hadron) (s : Species Flavor) :
    s ∈ valence (conj h) ↔ Species.conj s ∈ valence h

namespace HadronMultiplet

variable (C : HadronMultiplet Hadron Flavor)

@[simp]
theorem conj_conj (h : Hadron) : C.conj (C.conj h) = h :=
  C.conj_involutive h

/-- The valence content of a multiplet is compatible with taking the antiparticle of the hadron
and of the parton together. -/
theorem valenceInvariant_conj : ValenceInvariant C.valence C.conj Species.conj := fun h s => by
  rw [C.mem_valence_conj, Species.conj_conj]

/-- Conjugation carries the valence content of a hadron to that of its antiparticle. -/
theorem image_conj_valence [DecidableEq Flavor] (h : Hadron) :
    (C.valence h).image Species.conj = C.valence (C.conj h) :=
  C.valenceInvariant_conj.image_valence Species.conj_involutive.surjective h

/-- Conjugation carries the valence species of a flavour in a hadron to the valence species of
that flavour in its antiparticle. -/
theorem image_conj_inter_valence [DecidableEq Flavor] (h : Hadron) (i : Flavor) :
    (Species.flavorPair i ∩ C.valence h).image Species.conj
      = Species.flavorPair i ∩ C.valence (C.conj h) := by
  rw [C.valenceInvariant_conj.image_inter_valence, Species.image_conj_flavorPair]

/-- Conjugation carries the non-valence species of a flavour in a hadron to the non-valence
species of that flavour in its antiparticle. -/
theorem image_conj_sdiff_valence [DecidableEq Flavor] (h : Hadron) (i : Flavor) :
    (Species.flavorPair i \ C.valence h).image Species.conj
      = Species.flavorPair i \ C.valence (C.conj h) := by
  rw [C.valenceInvariant_conj.image_sdiff_valence, Species.image_conj_flavorPair]

end HadronMultiplet

namespace IsValenceFlavor

variable {valence : Hadron → Finset (Species Flavor)} {τ : Hadron → Hadron} {h : Hadron}
  {i : Flavor}

/-- For a valence content compatible with the antiparticle map `τ`, a valence flavour of a hadron
is a valence flavour of its antiparticle. -/
theorem conj (hv : ValenceInvariant valence τ Species.conj) (hi : IsValenceFlavor valence h i) :
    IsValenceFlavor valence (τ h) i := by
  rw [isValenceFlavor_iff, ← hv.mem_iff h, ← hv.mem_iff h, Species.conj_quark,
    Species.conj_antiquark] at hi
  rwa [isValenceFlavor_iff, xor_comm]

end IsValenceFlavor

end Parton
end Particles
end EpsilonEridani
