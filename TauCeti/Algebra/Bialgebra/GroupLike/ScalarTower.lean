/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Bialgebra.GroupLike.BaseChange
public import TauCeti.Algebra.Bialgebra.GroupLike.ScalarAut
import TauCeti.Algebra.Bialgebra.BaseChange

/-!
# Characters over an extension of a splitting ring

For a tower `k → L → K`, a commutative `k`-bialgebra split over `L` has the same
characters over `L` and `K`, provided `L` is a domain, `L ⊗[k] A` is torsion-free
over `L`, and `Spec K` is connected.
The comparison extends the coefficients of a character, and intertwines compatible
scalar automorphisms of `L` and `K`. This identifies splitting-field characters with
geometric characters while retaining the Galois action.

The construction uses `groupLikeBaseChangeEquiv` and `baseChangeTowerBialgEquiv`.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {k L K A : Type*} [CommRing k] [CommRing L] [Algebra k L]
  [CommRing K] [Algebra k K] [Algebra L K] [IsScalarTower k L K]
  [CommRing A] [Bialgebra k A]
  [IsDomain L] [ConnectedSpace (PrimeSpectrum K)]
  [Module.IsTorsionFree L (L ⊗[k] A)]

/-- Extension of the coefficients of a character through a tower, when the intermediate
scalar extension is spanned by its group-like elements. -/
noncomputable def groupLikeScalarTowerEquiv
    (hspan : Submodule.span L
      (Set.range (_root_.GroupLike.val (R := L) (A := L ⊗[k] A))) = ⊤) :
    _root_.GroupLike L (L ⊗[k] A) ≃* _root_.GroupLike K (K ⊗[k] A) :=
  (groupLikeBaseChangeEquiv (K := K) hspan).trans
    (GroupLike.mapEquiv (Bialgebra.TensorProduct.baseChangeTowerBialgEquiv k L A K))

/-- The character comparison extends coefficients and leaves the original bialgebra fixed. -/
@[simp]
theorem val_groupLikeScalarTowerEquiv
    (hspan : Submodule.span L
      (Set.range (_root_.GroupLike.val (R := L) (A := L ⊗[k] A))) = ⊤)
    (x : _root_.GroupLike L (L ⊗[k] A)) :
    (groupLikeScalarTowerEquiv (K := K) hspan x).val =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom k L K) (AlgHom.id k A) x.val := by
  simp only [groupLikeScalarTowerEquiv, MulEquiv.trans_apply,
    groupLikeBaseChangeEquiv_apply, GroupLike.val_mapEquiv, val_groupLikeBaseChange]
  induction x.val using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul a b => simp [Algebra.smul_def]

/-- Compatible scalar automorphisms commute with extending a character through a tower.

This is an explicit rewrite rule: `simp` cannot infer `σ` from the left-hand side.
Use it with the chosen compatible automorphisms and their compatibility proof. -/
theorem groupLikeScalarTowerEquiv_smul
    (hspan : Submodule.span L
      (Set.range (_root_.GroupLike.val (R := L) (A := L ⊗[k] A))) = ⊤)
    (σ : K ≃ₐ[k] K) (τ : L ≃ₐ[k] L)
    (hστ : ∀ a, σ (algebraMap L K a) = algebraMap L K (τ a))
    (x : _root_.GroupLike L (L ⊗[k] A)) :
    groupLikeScalarTowerEquiv (K := K) hspan (τ • x) =
      σ • groupLikeScalarTowerEquiv (K := K) hspan x := by
  apply _root_.GroupLike.val_injective
  simp only [ScalarAut.val_smul, val_groupLikeScalarTowerEquiv]
  induction x.val using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul a b => simp only [ScalarAut.smul_tmul, Algebra.TensorProduct.map_tmul,
      IsScalarTower.toAlgHom_apply, AlgHom.id_apply, hστ]

end TauCeti
