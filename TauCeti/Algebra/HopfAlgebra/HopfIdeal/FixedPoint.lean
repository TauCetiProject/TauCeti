/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Equalizer

/-!
# The fixed-point Hopf ideal of a family of bialgebra endomorphisms

For a commutative Hopf `R`-algebra `H` and bialgebra endomorphisms `f : ι → (H →ₐc[R] H)`, this file
defines the **fixed-point Hopf ideal** `TauCeti.HopfIdeal.fixedPoint f` as the supremum of
`HopfIdeal.equalizer (f i) (BialgHom.id R H)`. Contravariantly, `(Spec H)^f` is a closed subgroup
scheme of `Spec H`: a ring homomorphism kills `(fixedPoint f).toIdeal` iff it is invariant under
every `f i` (`fixedPoint_le_ker_iff`), and `fixedPoint f = ⊥` iff every `f i = id`
(`fixedPoint_eq_bot_iff`). Bundled categorical versions and Edixhoven's smoothness theorem live in
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.FixedPoint`.

## Main declarations

* `TauCeti.HopfIdeal.fixedPoint`: the fixed-point Hopf ideal of `f : ι → (H →ₐc[R] H)`.
* `TauCeti.HopfIdeal.fixedPoint_le_iff`, `TauCeti.HopfIdeal.fixedPoint_le_ker_iff`, and
  `TauCeti.HopfIdeal.fixedPoint_eq_bot_iff`: universal properties and triviality criterion.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), Propositions 3.1
  and 3.4, pp. 293–295.
* J. S. Milne, *Algebraic Groups*, Cambridge University Press (2017), §1.h.
-/

public section

namespace TauCeti.HopfIdeal

universe u v w

variable {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H] {ι : Sort w}

/-- The **fixed-point Hopf ideal** of bialgebra endomorphisms `f : ι → (H →ₐc[R] H)`: the supremum
of `equalizer (f i) (BialgHom.id R H)`, cutting out `(Spec H)^f` as a closed subgroup scheme. -/
def fixedPoint (f : ι → (H →ₐc[R] H)) : HopfIdeal R H :=
  ⨆ i, equalizer (f i) (BialgHom.id R H)

/-- `fixedPoint f` is the supremum of `equalizer (f i) (BialgHom.id R H)`. -/
theorem fixedPoint_def (f : ι → (H →ₐc[R] H)) :
    fixedPoint f = ⨆ i, equalizer (f i) (BialgHom.id R H) := (rfl)

/-- The underlying ideal of `fixedPoint f` is the supremum of the displacement ideals. -/
theorem fixedPoint_toIdeal (f : ι → (H →ₐc[R] H)) :
    (fixedPoint f).toIdeal = ⨆ i, equalizerIdeal (f i) (BialgHom.id R H) := by simp [fixedPoint_def]

/-- Every displacement `f i a - a` lies in `fixedPoint f`. -/
theorem sub_mem_fixedPoint (f : ι → (H →ₐc[R] H)) (i : ι) (a : H) : f i a - a ∈ fixedPoint f := by
  rw [← mem_toIdeal, fixedPoint_toIdeal]
  exact Submodule.mem_iSup_of_mem i (sub_mem_equalizerIdeal (f i) (BialgHom.id R H) a)

/-- `(fixedPoint f).toIdeal` is the smallest ideal containing every displacement `f i a - a`. -/
theorem fixedPoint_toIdeal_le_iff {f : ι → (H →ₐc[R] H)} {J : Ideal H} :
    (fixedPoint f).toIdeal ≤ J ↔ ∀ (i : ι) (a : H), f i a - a ∈ J := by
  rw [fixedPoint_toIdeal, iSup_le_iff]
  exact forall_congr' fun _ ↦ equalizerIdeal_le_iff

/-- `fixedPoint f` is the smallest Hopf ideal containing every displacement `f i a - a`. -/
theorem fixedPoint_le_iff {f : ι → (H →ₐc[R] H)} {J : HopfIdeal R H} :
    fixedPoint f ≤ J ↔ ∀ (i : ι) (a : H), f i a - a ∈ J := by
  rw [← toIdeal_le_toIdeal, fixedPoint_toIdeal_le_iff]; simp only [mem_toIdeal]

/-- A ring homomorphism into a semiring kills `(fixedPoint f).toIdeal` iff it is `f`-invariant. -/
theorem fixedPoint_le_ker_iff {A : Type*} [Semiring A] (f : ι → (H →ₐc[R] H)) (φ : H →+* A) :
    (fixedPoint f).toIdeal ≤ RingHom.ker φ ↔ ∀ (i : ι) (a : H), φ (f i a) = φ a := by
  rw [fixedPoint_toIdeal_le_iff]
  refine forall₂_congr fun i a ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [RingHom.mem_ker] at h; rw [← sub_add_cancel (f i a) a, map_add, h, zero_add]
  · rw [RingHom.mem_ker, sub_eq_add_neg, map_add, h, ← map_add, add_neg_cancel, map_zero]

/-- `fixedPoint f` vanishes if and only if every `f i` is the identity bialgebra morphism. -/
@[simp]
theorem fixedPoint_eq_bot_iff {f : ι → (H →ₐc[R] H)} :
    fixedPoint f = ⊥ ↔ ∀ i, f i = BialgHom.id R H := by
  rw [eq_bot_iff, fixedPoint_le_iff]
  simp only [mem_bot, sub_eq_zero, BialgHom.id_apply, DFunLike.ext_iff]

end TauCeti.HopfIdeal
