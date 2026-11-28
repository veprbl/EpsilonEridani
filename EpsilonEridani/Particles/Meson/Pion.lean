/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Particles.Meson.Basic
public import EpsilonEridani.Particles.Parton.ValenceContent

/-!
# The pion triplet as a hadron multiplet

The pion triplet is worked out as an instance of `Parton.HadronMultiplet`: `pionMultiplet` is
`π⁺ = u dbar`, `π⁻ = d ubar` and the flavour-neutral `π⁰`.

The pion triplet is indexed by its own two-flavour type `UpDownFlavor` rather than by the three
light flavours `LightFlavor`, because the pions form an isospin multiplet of the up and the down
flavour: the isospin reflection `UpDownFlavor.swap` is an involution exchanging the two, and every
flavour of `UpDownFlavor` is a valence flavour of each charged pion, which fails for the strange
flavour of `LightFlavor`. The hadron type `Pion` labels the three pions, including the neutral
pion, which is not a `PseudoscalarMeson` with a single valence quark and antiquark. The two
encodings are connected by `UpDownFlavor.toLightFlavor`, under which the valence content of the
charged pions is that of `piPlus` and `piMinus`.

## Main definitions

* `EpsilonEridani.Particles.Meson.UpDownFlavor`: the up and the down quark flavour.
* `EpsilonEridani.Particles.Meson.Pion` and `EpsilonEridani.Particles.Meson.pionMultiplet`: the
  pion triplet.
* `EpsilonEridani.Particles.Meson.UpDownFlavor.toLightFlavor`: the up and the down flavour as light
  flavours.

## Main statements

* `isValenceFlavor_pion_plus`, `isValenceFlavor_pion_minus` and `not_isValenceFlavor_pion_zero`:
  both flavours are valence flavours of each charged pion and neither is a valence flavour of the
  neutral pion.
* `valenceInvariant_pion_conj` and `valenceInvariant_pion_swap`: the valence content of the pion
  triplet is compatible with charge conjugation and with the isospin reflection.
* `Pion.image_map_valence_plus` and `Pion.image_map_valence_minus`: the valence content of the
  charged pions, read as light flavours, is that of `piPlus` and `piMinus`.
-/

public section

namespace EpsilonEridani.Particles.Meson

open Parton

/-- The up and the down quark flavour, the two flavours of the pion triplet's valence content. -/
inductive UpDownFlavor where
  /-- The up flavour. -/
  | up
  /-- The down flavour. -/
  | down
  deriving DecidableEq

instance : Fintype UpDownFlavor where
  elems := {.up, .down}
  complete i := by cases i <;> simp

/-- The isospin reflection: it exchanges the up and the down flavour. -/
def UpDownFlavor.swap : UpDownFlavor → UpDownFlavor
  | up => down
  | down => up

@[simp]
theorem UpDownFlavor.swap_up : swap .up = .down :=
  (rfl)

@[simp]
theorem UpDownFlavor.swap_down : swap .down = .up :=
  (rfl)

@[simp]
theorem UpDownFlavor.swap_swap (i : UpDownFlavor) : swap (swap i) = i := by
  cases i <;> rfl

/-- The isospin reflection is an involution. -/
theorem UpDownFlavor.swap_involutive : Function.Involutive swap :=
  UpDownFlavor.swap_swap

/-- The up and the down flavour as light flavours, leaving out the strange flavour. -/
def UpDownFlavor.toLightFlavor : UpDownFlavor → LightFlavor
  | up => .u
  | down => .d

@[simp]
theorem UpDownFlavor.toLightFlavor_up : toLightFlavor .up = .u :=
  (rfl)

@[simp]
theorem UpDownFlavor.toLightFlavor_down : toLightFlavor .down = .d :=
  (rfl)

theorem UpDownFlavor.toLightFlavor_injective : Function.Injective toLightFlavor := by
  intro i j h
  cases i <;> cases j <;> first | rfl | cases h

/-- The pion triplet. -/
inductive Pion where
  /-- The positive pion `u dbar`. -/
  | plus
  /-- The neutral pion. -/
  | zero
  /-- The negative pion `d ubar`. -/
  | minus
  deriving DecidableEq

instance : Fintype Pion where
  elems := {.plus, .zero, .minus}
  complete h := by cases h <;> simp

/-- The antiparticle of a pion: the charged pions are exchanged and the neutral pion is its own
antiparticle. -/
def Pion.conj : Pion → Pion
  | plus => minus
  | zero => zero
  | minus => plus

@[simp]
theorem Pion.conj_plus : conj .plus = .minus :=
  (rfl)

@[simp]
theorem Pion.conj_zero : conj .zero = .zero :=
  (rfl)

@[simp]
theorem Pion.conj_minus : conj .minus = .plus :=
  (rfl)

@[simp]
theorem Pion.conj_conj (h : Pion) : conj (conj h) = h := by
  cases h <;> rfl

/-- Taking the antiparticle of a pion twice returns the pion. -/
theorem Pion.conj_involutive : Function.Involutive Pion.conj :=
  Pion.conj_conj

/-- The valence content of the pions: `π⁺ = u dbar` and `π⁻ = d ubar`, while the neutral pion, a
superposition of `u ubar` and `d dbar`, has all four light species as valence constituents. -/
def Pion.valence : Pion → Finset (Species UpDownFlavor)
  | plus => {.quark .up, .antiquark .down}
  | zero => {.quark .up, .antiquark .up, .quark .down, .antiquark .down}
  | minus => {.quark .down, .antiquark .up}

@[simp]
theorem Pion.valence_plus : valence .plus = {.quark .up, .antiquark .down} :=
  (rfl)

@[simp]
theorem Pion.valence_zero :
    valence .zero = {.quark .up, .antiquark .up, .quark .down, .antiquark .down} :=
  (rfl)

@[simp]
theorem Pion.valence_minus : valence .minus = {.quark .down, .antiquark .up} :=
  (rfl)

/-- The valence content of the positive pion, read as light flavours, is the valence quark and the
valence antiquark of `piPlus`. -/
theorem Pion.image_map_valence_plus :
    (valence .plus).image (Species.map UpDownFlavor.toLightFlavor)
      = {.quark piPlus.valenceQuark, .antiquark piPlus.valenceAntiquark} := by
  simp [Finset.image_insert, Species.map_quark, Species.map_antiquark]

/-- The valence content of the negative pion, read as light flavours, is the valence quark and the
valence antiquark of `piMinus`. -/
theorem Pion.image_map_valence_minus :
    (valence .minus).image (Species.map UpDownFlavor.toLightFlavor)
      = {.quark piMinus.valenceQuark, .antiquark piMinus.valenceAntiquark} := by
  simp [Finset.image_insert, Species.map_quark, Species.map_antiquark]

/-- The pion triplet as a hadron multiplet. -/
def pionMultiplet : HadronMultiplet Pion UpDownFlavor where
  conj := Pion.conj
  conj_involutive := Pion.conj_involutive
  valence := Pion.valence
  mem_valence_conj h s := by
    cases h
    all_goals
      simp only [Pion.conj, Pion.valence, Finset.mem_insert, Finset.mem_singleton,
        Species.conj_involutive.eq_iff, Species.conj_quark, Species.conj_antiquark]
      tauto

@[simp]
theorem pionMultiplet_conj : pionMultiplet.conj = Pion.conj :=
  (rfl)

@[simp]
theorem pionMultiplet_valence : pionMultiplet.valence = Pion.valence :=
  (rfl)

/-- Both flavours are valence flavours of the positive pion: the up quark and the down
antiquark are its valence constituents, and the up antiquark and the down quark are not. -/
theorem isValenceFlavor_pion_plus (i : UpDownFlavor) : IsValenceFlavor Pion.valence .plus i := by
  cases i
  · exact isValenceFlavor_of_quark_mem (by simp) (by simp)
  · exact isValenceFlavor_of_antiquark_mem (by simp) (by simp)

/-- Both flavours are valence flavours of the negative pion: the down quark and the up
antiquark are its valence constituents, and the down antiquark and the up quark are not. -/
theorem isValenceFlavor_pion_minus (i : UpDownFlavor) : IsValenceFlavor Pion.valence .minus i := by
  cases i
  · exact isValenceFlavor_of_antiquark_mem (by simp) (by simp)
  · exact isValenceFlavor_of_quark_mem (by simp) (by simp)

/-- No flavour is a valence flavour of the neutral pion: for each flavour both the quark and the
antiquark are valence constituents, so a flavour-neutral hadron does not distinguish them. -/
theorem not_isValenceFlavor_pion_zero (i : UpDownFlavor) :
    ¬ IsValenceFlavor Pion.valence .zero i := by
  rw [isValenceFlavor_iff]
  rintro (⟨-, hq'⟩ | ⟨-, hq⟩)
  · exact hq' (by cases i <;> simp)
  · exact hq (by cases i <;> simp)

/-- The valence content of the pion triplet is compatible with charge conjugation. -/
theorem valenceInvariant_pion_conj : ValenceInvariant Pion.valence Pion.conj Species.conj :=
  pionMultiplet.valenceInvariant_conj

/-- The valence content of the pion triplet is compatible with the isospin reflection, which acts
on the triplet as the antiparticle map. -/
theorem valenceInvariant_pion_swap :
    ValenceInvariant Pion.valence Pion.conj (Species.map UpDownFlavor.swap) := by
  rw [valenceInvariant_iff]
  intro h s
  cases h
  all_goals
    simp only [Pion.conj, Pion.valence, Finset.mem_insert,
      Finset.mem_singleton, (Species.map_involutive UpDownFlavor.swap_involutive).eq_iff,
      Species.map_quark, Species.map_antiquark, UpDownFlavor.swap_up, UpDownFlavor.swap_down]
    -- `simp only` already closes the two charged cases; the neutral one needs the reordering.
    try tauto

end EpsilonEridani.Particles.Meson
