/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Quotient
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.Product

/-!
# Trivial solvable radicals of direct products

If two finite-type affine groups have trivial solvable radical, so does their direct product.
The groups themselves need not be smooth or connected. A connected normal smooth solvable
subgroup of the product has such an image in each factor, so both projection images are
trivial. The tensor-product universal property then makes the subgroup itself trivial.

This is the radical calculation used to assemble semisimple groups from their factors.
It uses `HopfIdeal.IsSolvableRadicalCandidate.comap_of_injective` for the projection images
and retains the scheme-theoretic subgroup throughout.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 6 and 21.
* T. A. Springer, *Linear Algebraic Groups*, Chapter 8.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k]

/-- The direct product of two finite-type affine groups with trivial solvable radical has
trivial solvable radical. No smoothness or connectedness of the ambient groups is required. -/
theorem solvableRadicalDefiningIdeal_tensorProduct_eq_augmentation
    (H K : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : solvableRadicalDefiningIdeal H = HopfIdeal.augmentation k H)
    (hK : solvableRadicalDefiningIdeal K = HopfIdeal.augmentation k K) :
    solvableRadicalDefiningIdeal (tensorProduct H K) =
      HopfIdeal.augmentation k (tensorProduct H K) := by
  rw [solvableRadicalDefiningIdeal_eq_augmentation_iff]
  intro I hI
  let P := tensorProduct H K
  let Q := quotient P I
  let q := (CommHopfAlgCat.mkQuotient P.obj I).hom.toAlgHom
  -- Project the candidate subgroup to each factor and use triviality of their radicals.
  have hleft : Function.Injective (toBialgHom (includeLeft H K)) := by
    intro x y hxy
    rw [includeLeft_apply, includeLeft_apply] at hxy
    exact Algebra.TensorProduct.includeLeft_injective (S := k)
      (_root_.Bialgebra.algebraMap_injective K) hxy
  have hright : Function.Injective (toBialgHom (includeRight H K)) := by
    intro x y hxy
    rw [includeRight_apply, includeRight_apply] at hxy
    exact Algebra.TensorProduct.includeRight_injective
      (_root_.Bialgebra.algebraMap_injective H) hxy
  have hIH : I.comap (toBialgHom (includeLeft H K)) = HopfIdeal.augmentation k H :=
    (solvableRadicalDefiningIdeal_eq_augmentation_iff H).mp hH _
      (hI.comap_of_injective (includeLeft H K).hom hleft)
  have hIK : I.comap (toBialgHom (includeRight H K)) = HopfIdeal.augmentation k K :=
    (solvableRadicalDefiningIdeal_eq_augmentation_iff K).mp hK _
      (hI.comap_of_injective (includeRight H K).hom hright)
  have hqH (x : H) : q (x ⊗ₜ[k] (1 : K)) = algebraMap k Q (Coalgebra.counit x) := by
    exact AlgHom.apply_eq_counit_of_augmentation_le_ker
      (q.comp Algebra.TensorProduct.includeLeft) (fun x hx ↦ by
        have hx' := HopfIdeal.mem_comap.mp (hIH ▸ HopfIdeal.mem_toIdeal.mp hx)
        rw [includeLeft_apply] at hx'
        exact (CommHopfAlgCat.mkQuotient_eq_zero_iff P.obj I _).mpr hx') x
  have hqK (y : K) : q ((1 : H) ⊗ₜ[k] y) = algebraMap k Q (Coalgebra.counit y) := by
    exact AlgHom.apply_eq_counit_of_augmentation_le_ker
      (q.comp Algebra.TensorProduct.includeRight) (fun y hy ↦ by
        have hy' := HopfIdeal.mem_comap.mp (hIK ▸ HopfIdeal.mem_toIdeal.mp hy)
        rw [includeRight_apply] at hy'
        exact (CommHopfAlgCat.mkQuotient_eq_zero_iff P.obj I _).mpr hy') y
  have hq : q = (Algebra.ofId k Q).comp (Bialgebra.counitAlgHom k P) := by
    -- Scalar restrictions on both factors determine the quotient map on their tensor product.
    apply Algebra.TensorProduct.ext'
    intro x y
    calc
      q (x ⊗ₜ[k] y) = q ((x ⊗ₜ[k] (1 : K)) * ((1 : H) ⊗ₜ[k] y)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      _ = algebraMap k Q (Coalgebra.counit x) * algebraMap k Q (Coalgebra.counit y) := by
        rw [map_mul, hqH, hqK]
      _ = _ := by
        rw [AlgHom.comp_apply, Algebra.ofId_apply, Bialgebra.counitAlgHom_apply,
          TensorProduct.counit_tmul, smul_eq_mul, map_mul, mul_comm]
  apply le_antisymm (HopfIdeal.le_augmentation k P I)
  intro x hx
  apply (CommHopfAlgCat.mkQuotient_eq_zero_iff P.obj I x).mp
  have hx0 := (HopfIdeal.mem_augmentation k P).mp hx
  have h := DFunLike.congr_fun hq x
  simpa only [q, AlgHom.comp_apply, Algebra.ofId_apply, Bialgebra.counitAlgHom_apply,
    BialgHom.coe_toAlgHom, hx0, map_zero] using h

end TauCeti.FiniteTypeCommHopfAlgCat
