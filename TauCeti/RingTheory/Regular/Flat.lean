/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Regular.Flat

/-!
# Weakly regular sequences descend along faithfully flat base change

Let `S` be a faithfully flat `R`-algebra and `N` the base change of an `R`-module `M` to `S`.
Mathlib proves that the image in `S` of a weakly `M`-regular sequence is weakly `N`-regular
(`RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange`), for `S` flat. This file proves
the converse for `S` faithfully flat: a sequence of `R` is weakly `M`-regular as soon as its image
is weakly `N`-regular. Multiplication by `x` on `N` is the base change of multiplication by `x` on
`M`, and a faithfully flat base change reflects injectivity. The quotients `N ⧸ x N` are again base
changes of `M ⧸ x M`, which gives the induction along the sequence.

## Main results

* `IsBaseChange.isSMulRegular_algebraMap_iff`: `x` is regular on `M` exactly when its image is
  regular on the faithfully flat base change `N`.
* `IsBaseChange.isWeaklyRegular_map_algebraMap_iff`: a sequence is weakly `M`-regular exactly when
  its image is weakly `N`-regular.
* `RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff_of_faithfullyFlat`: the case `M = R`.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 7.2 and §16.
-/

public section

open Module RingTheory.Sequence

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [FaithfullyFlat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

namespace IsBaseChange

/-- An element of `R` is regular on `M` exactly when its image in a faithfully flat `R`-algebra `S`
is regular on the base change of `M` to `S`. -/
theorem isSMulRegular_algebraMap_iff {f : M →ₗ[R] N} (hf : IsBaseChange S f) (x : R) :
    IsSMulRegular N (algebraMap R S x) ↔ IsSMulRegular M x := by
  -- multiplication by `x` on `N` is the base change of multiplication by `x` on `M`
  have h : ⇑(LinearMap.lsmul S N (algebraMap R S x)) =
      hf.equiv ∘ (LinearMap.lsmul R M x).lTensor S ∘ hf.equiv.symm := by
    rw [← LinearMap.coe_restrictScalars R, ← hf.map_id_lsmul_eq_lsmul_algebraMap]
    exact funext fun y ↦ IsTensorProduct.inductionOn hf y
      (fun s m ↦ (IsTensorProduct.map_eq hf hf _ _ s m).trans
        (by simp [TensorProduct.smul_tmul', IsBaseChange.equiv_tmul, smul_comm x s]))
      (fun _ _ hx hy ↦ by simp [hx, hy])
  rw [isSMulRegular_iff_ker_lsmul_eq_bot, isSMulRegular_iff_ker_lsmul_eq_bot, LinearMap.ker_eq_bot,
    LinearMap.ker_eq_bot, h, EquivLike.comp_injective, EquivLike.injective_comp,
    FaithfullyFlat.lTensor_injective_iff_injective]

/-- **Weakly regular sequences descend along faithfully flat base change.** A sequence of `R` is
weakly regular on `M` exactly when its image in a faithfully flat `R`-algebra `S` is weakly
regular on the base change of `M` to `S`. -/
theorem isWeaklyRegular_map_algebraMap_iff {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    (rs : List R) : IsWeaklyRegular N (rs.map (algebraMap R S)) ↔ IsWeaklyRegular M rs := by
  induction rs generalizing M N with
  | nil => simp
  | cons x _ ih =>
    simp only [List.map_cons, isWeaklyRegular_cons_iff]
    -- `N ⧸ x N` is the base change of `M ⧸ x M`
    have e := (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop x M S).symm ≪≫ₗ
      QuotSMulTop.congr ((algebraMap R S) x) hf.equiv
    have hg : IsBaseChange S <|
        e.toLinearMap.restrictScalars R ∘ₗ TensorProduct.mk R S (QuotSMulTop x M) 1 :=
      IsBaseChange.of_equiv e (fun _ ↦ by simp)
    rw [hf.isSMulRegular_algebraMap_iff, ih hg]

end IsBaseChange

/-- A sequence of `R` is weakly `R`-regular exactly when its image in a faithfully flat
`R`-algebra `S` is weakly `S`-regular. -/
theorem RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff_of_faithfullyFlat (rs : List R) :
    IsWeaklyRegular S (rs.map (algebraMap R S)) ↔ IsWeaklyRegular R rs :=
  (IsBaseChange.linearMap R S).isWeaklyRegular_map_algebraMap_iff rs
