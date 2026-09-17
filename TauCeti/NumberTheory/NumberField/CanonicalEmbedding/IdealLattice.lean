/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import TauCeti.NumberTheory.NumberField.FractionalIdeal

/-!
# The index of one ideal lattice in another

An invertible fractional ideal `I` of a number field `K` is a full `ℤ`-lattice in `K`, and its
image `mixedEmbedding.idealLattice K I` is a full lattice in the mixed space.  If `J ≤ I` are two
such ideals, the index of `J` in `I` is the ratio of their absolute norms.  This is the
lattice-theoretic meaning of the norm of a fractional ideal: for an integral ideal `𝔞`, the
lattice of `I * 𝔞` has index `N 𝔞` in the lattice of `I`, which is how congruence conditions
modulo `𝔞` are counted among the lattice points of `I`.

The index is computed in `K` by `NumberField.relIndex_fractionalIdeal_eq_absNorm_div_absNorm`, and
transported to the mixed space along the injective embedding.

## Main results

* `NumberField.mixedEmbedding.relIndex_idealLattice`: the index of the lattice of `J` in the
  lattice of `I` is `absNorm J / absNorm I`.
* `NumberField.mixedEmbedding.relIndex_idealLattice_mul_mk0`: the lattice of `I * 𝔞` has index
  `N 𝔞` in the lattice of `I`.
* `NumberField.mixedEmbedding.covolume_idealLattice_mul_mk0`: the covolume of the lattice of
  `I * 𝔞` is `N 𝔞` times the covolume of the lattice of `I`.
-/

public section

open Module NumberField
open scoped nonZeroDivisors

namespace NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- The ideal lattice of `I` is the image of `I` under the mixed embedding, as an additive
subgroup. -/
theorem idealLattice_toAddSubgroup (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (idealLattice K I).toAddSubgroup =
      (I : Submodule (𝓞 K) K).toAddSubgroup.map (mixedEmbedding K).toAddMonoidHom := by
  ext x
  simp [eq_comm]

/-- **The index of one ideal lattice in another is the ratio of the norms.**  For invertible
fractional ideals `J ≤ I` of a number field, the lattice of `J` has index `absNorm J / absNorm I`
in the lattice of `I`. -/
theorem relIndex_idealLattice {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJI : (J : FractionalIdeal (𝓞 K)⁰ K) ≤ I) :
    ((idealLattice K J).toAddSubgroup.relIndex (idealLattice K I).toAddSubgroup : ℚ) =
      FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 K)⁰ K) /
        FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [idealLattice_toAddSubgroup, idealLattice_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ (mixedEmbedding_injective K),
    relIndex_fractionalIdeal_eq_absNorm_div_absNorm hJI]

/-- **The index of the lattice of `I * 𝔞`.**  For an integral ideal `𝔞`, the lattice of `I * 𝔞`
has index `N 𝔞` in the lattice of `I`. -/
theorem relIndex_idealLattice_mul_mk0 (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (𝔞 : (Ideal (𝓞 K))⁰) :
    (idealLattice K (I * FractionalIdeal.mk0 K 𝔞)).toAddSubgroup.relIndex
      (idealLattice K I).toAddSubgroup = Ideal.absNorm (𝔞 : Ideal (𝓞 K)) := by
  have hI : FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.absNorm_eq_zero_iff.not.mpr I.ne_zero
  have := relIndex_idealLattice (I := I) (J := I * FractionalIdeal.mk0 K 𝔞)
    (mul_le_of_le_one_right' FractionalIdeal.coeIdeal_le_one)
  rw [Units.val_mul, map_mul, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm,
    mul_div_cancel_left₀ _ hI] at this
  exact_mod_cast this

open scoped Classical in
/-- **The covolume of the lattice of `I * 𝔞`** is `N 𝔞` times the covolume of the lattice of
`I`. -/
theorem covolume_idealLattice_mul_mk0 (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (𝔞 : (Ideal (𝓞 K))⁰) :
    ZLattice.covolume (idealLattice K (I * FractionalIdeal.mk0 K 𝔞)) =
      Ideal.absNorm (𝔞 : Ideal (𝓞 K)) * ZLattice.covolume (idealLattice K I) := by
  rw [covolume_idealLattice, covolume_idealLattice, Units.val_mul, map_mul,
    FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm]
  push_cast
  ring

end NumberField.mixedEmbedding
