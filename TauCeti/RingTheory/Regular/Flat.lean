/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Regular.Flat

/-!
# Faithfully flat descent of regular elements and weakly regular sequences

Mathlib shows that a flat base change preserves regular elements and weakly regular sequences
(`IsSMulRegular.of_flat_of_isBaseChange` and
`RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange`).
This file proves the converse for a faithfully flat base change: if `S` is a faithfully flat
`R`-algebra and `N` is the base change of an `R`-module `M` to `S`, then `x : R` is regular on `M`
exactly when its image in `S` is regular on `N`, and a list `rs` of elements of `R` is weakly
regular on `M` exactly when its image in `S` is weakly regular on `N`.

Multiplication by the image of `x` on `N` is the base change of multiplication by `x` on `M`, and
a faithfully flat base change reflects injectivity
(`Module.FaithfullyFlat.lTensor_injective_iff_injective`). For sequences, the base change of
`M ⧸ x M` is `N ⧸ x N`, so the statement follows by induction along the list.

## Main results

* `IsBaseChange.isSMulRegular_algebraMap_iff_of_faithfullyFlat`: regularity of `x` descends along
  a faithfully flat base change.
* `RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff_of_faithfullyFlat_of_isBaseChange` and
  `RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff_of_faithfullyFlat`: weak regularity of
  a sequence descends along a faithfully flat base change.
-/

public section

open Module TensorProduct

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [FaithfullyFlat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- **Faithfully flat descent of regular elements.** If `N` is the base change of `M` to a
faithfully flat `R`-algebra `S`, then the image of `x : R` in `S` is regular on `N` exactly when
`x` is regular on `M`. -/
theorem IsBaseChange.isSMulRegular_algebraMap_iff_of_faithfullyFlat {f : M →ₗ[R] N}
    (hf : IsBaseChange S f) (x : R) : IsSMulRegular N (algebraMap R S x) ↔ IsSMulRegular M x := by
  -- multiplication by `x` on `N` is the base change of multiplication by `x` on `M`
  have key (z : S ⊗[R] M) : hf.equiv ((LinearMap.lsmul R M x).lTensor S z) =
      algebraMap R S x • hf.equiv z := by
    induction z using TensorProduct.inductionOn with
    | tmul s m => simp [smul_tmul', IsBaseChange.equiv_tmul, smul_assoc]
    | add a b ha hb => simp [ha, hb]
  have h : (algebraMap R S x • · : N → N) =
      hf.equiv ∘ (LinearMap.lsmul R M x).lTensor S ∘ hf.equiv.symm :=
    funext fun y ↦ by simp [key]
  rw [IsSMulRegular, IsSMulRegular, h, EquivLike.comp_injective, EquivLike.injective_comp]
  exact FaithfullyFlat.lTensor_injective_iff_injective R S _

namespace RingTheory.Sequence

/-- **Faithfully flat descent of weakly regular sequences.** If `N` is the base change of `M` to a
faithfully flat `R`-algebra `S`, then the image in `S` of a list `rs` of elements of `R` is weakly
regular on `N` exactly when `rs` is weakly regular on `M`. -/
theorem isWeaklyRegular_map_algebraMap_iff_of_faithfullyFlat_of_isBaseChange {f : M →ₗ[R] N}
    (hf : IsBaseChange S f) (rs : List R) :
    IsWeaklyRegular N (rs.map (algebraMap R S)) ↔ IsWeaklyRegular M rs := by
  induction rs generalizing M N with
  | nil => simp
  | cons x _ ih =>
    simp only [List.map_cons, isWeaklyRegular_cons_iff]
    -- the base change of `M ⧸ x M` is `N ⧸ x N`, as in `IsWeaklyRegular.of_flat_of_isBaseChange`
    have e := (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop x M S).symm ≪≫ₗ
      QuotSMulTop.congr ((algebraMap R S) x) hf.equiv
    have hg : IsBaseChange S <|
        e.toLinearMap.restrictScalars R ∘ₗ TensorProduct.mk R S (QuotSMulTop x M) 1 :=
      IsBaseChange.of_equiv e (fun _ ↦ by simp)
    rw [hf.isSMulRegular_algebraMap_iff_of_faithfullyFlat, ih hg]

/-- **Faithfully flat descent of weakly regular sequences in a ring.** For a faithfully flat
`R`-algebra `S`, the image in `S` of a list `rs` of elements of `R` is weakly regular on `S` exactly
when `rs` is weakly regular on `R`. -/
theorem isWeaklyRegular_map_algebraMap_iff_of_faithfullyFlat (rs : List R) :
    IsWeaklyRegular S (rs.map (algebraMap R S)) ↔ IsWeaklyRegular R rs :=
  isWeaklyRegular_map_algebraMap_iff_of_faithfullyFlat_of_isBaseChange
    (IsBaseChange.linearMap R S) rs

end RingTheory.Sequence
