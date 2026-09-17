/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# The index of one ideal lattice in another

An invertible fractional ideal `I` of a number field `K` is a full `ℤ`-lattice in `K`, and its
image `mixedEmbedding.idealLattice K I` is a full lattice in the mixed space.  If `J ≤ I` are two
such ideals, the index of `J` in `I` is the ratio of their absolute norms.  This is the
lattice-theoretic meaning of the norm of a fractional ideal: for an integral ideal `𝔞`, the
lattice of `I * 𝔞` has index `N 𝔞` in the lattice of `I`, which is how congruence conditions
modulo `𝔞` are counted among the lattice points of `I`.

The index is computed in `K` from the determinant formula
`NumberField.det_basisOfFractionalIdeal_eq_absNorm`, and transported to the mixed space along the
injective embedding.

## Main results

* `NumberField.relIndex_fractionalIdeal_eq_absNorm_div_absNorm`: the index of `J` in `I`, as
  additive subgroups of `K`, is `absNorm J / absNorm I`.
* `NumberField.mixedEmbedding.relIndex_idealLattice`: the same index for the ideal lattices in the
  mixed space.
-/

public section

open Module NumberField
open scoped nonZeroDivisors

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **The index of a fractional ideal in a larger one is the ratio of the norms.**  For invertible
fractional ideals `J ≤ I` of a number field, the index of `J` in `I`, as additive subgroups of the
field, is `absNorm J / absNorm I`. -/
theorem relIndex_fractionalIdeal_eq_absNorm_div_absNorm {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJI : (J : FractionalIdeal (𝓞 K)⁰ K) ≤ I) :
    ((J : Submodule (𝓞 K) K).toAddSubgroup.relIndex (I : Submodule (𝓞 K) K).toAddSubgroup : ℚ) =
      FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 K)⁰ K) /
        FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  -- Reindex the `ℚ`-bases of `K` coming from `ℤ`-bases of `I` and `J` by the index type of the
  -- integral basis, so that all three bases share one index type.
  have equiv (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Free.ChooseBasisIndex ℤ L :=
    Fintype.equivOfCardEq <| by
      rw [← finrank_eq_card_chooseBasisIndex, ← finrank_eq_card_chooseBasisIndex,
        fractionalIdeal_rank]
  let bI := (basisOfFractionalIdeal K I).reindex (equiv I).symm
  let bJ := (basisOfFractionalIdeal K J).reindex (equiv J).symm
  have closure_eq (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      (L : Submodule (𝓞 K) K).toAddSubgroup =
        AddSubgroup.closure (Set.range ((basisOfFractionalIdeal K L).reindex (equiv L).symm)) := by
    rw [Basis.range_reindex, ← Submodule.span_int_eq_addSubgroupClosure]
    ext x
    exact (mem_span_basisOfFractionalIdeal K).symm
  have hI : |(integralBasis K).det bI| = FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) :=
    det_basisOfFractionalIdeal_eq_absNorm K I (equiv I)
  have hJ : |(integralBasis K).det bJ| = FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 K)⁰ K) :=
    det_basisOfFractionalIdeal_eq_absNorm K J (equiv J)
  rw [AddSubgroup.relIndex_eq_abs_det _ _ hJI bJ bI (closure_eq J) (closure_eq I), ← hI, ← hJ,
    ← (integralBasis K).det_mul_det bI bJ, abs_mul,
    mul_div_cancel_left₀ _ (abs_ne_zero.mpr ((integralBasis K).isUnit_det bI).ne_zero)]

namespace mixedEmbedding

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

end mixedEmbedding

end NumberField
