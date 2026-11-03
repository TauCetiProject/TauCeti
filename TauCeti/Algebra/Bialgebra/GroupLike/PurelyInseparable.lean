/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph
-/
module

public import TauCeti.Algebra.Bialgebra.GroupLike.ScalarTower
public import TauCeti.Algebra.Coalgebra.GroupLike.BaseChange
public import TauCeti.FieldTheory.PurelyInseparable.TensorProduct
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Purely inseparable descent of split bialgebras

If the group-like elements of a commutative bialgebra span after a purely inseparable
field extension, each of them descends uniquely, and the original group-like elements
already span. No finite-generation or perfectness hypothesis is required.

The two pullbacks of a character to the tensor square agree by connected-spectrum
rigidity. A linear functional taking one to one then descends its coefficients.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {k L A : Type*} [Field k] [Field L] [Algebra k L]
  [CommRing A] [Bialgebra k A]

private theorem exists_one_tmul_of_equal_pullbacks (z : L ⊗[k] A)
    (hz : Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeLeft : L →ₐ[k] L ⊗[k] L) (AlgHom.id k A) z =
      Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeRight : L →ₐ[k] L ⊗[k] L) (AlgHom.id k A) z) :
    ∃ a : A, (1 : L) ⊗ₜ[k] a = z := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k (one_ne_zero : (1 : L) ≠ 0)
  let c : L ⊗[k] L →ₗ[k] L := (TensorProduct.lid k L).toLinearMap.comp (f.rTensor L)
  let a : L ⊗[k] A →ₗ[k] A := (TensorProduct.lid k A).toLinearMap.comp (f.rTensor A)
  have hleft (x : L ⊗[k] A) :
      c.rTensor A (Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeLeft : L →ₐ[k] L ⊗[k] L)
        (AlgHom.id k A) x) = (1 : L) ⊗ₜ[k] a x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy, TensorProduct.tmul_add]
    | tmul l b => simp [c, a, TensorProduct.smul_tmul]
  have hright (x : L ⊗[k] A) :
      c.rTensor A (Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeRight : L →ₐ[k] L ⊗[k] L)
        (AlgHom.id k A) x) = x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul l b => simp [c, hf]
  exact ⟨a z, (hleft z).symm.trans ((congrArg (c.rTensor A) hz).trans (hright z))⟩

variable [IsPurelyInseparable k L]

/-- If a commutative bialgebra splits after a purely inseparable field extension,
its group-like elements descend uniquely. -/
theorem groupLikeBaseChange_bijective_of_isPurelyInseparable
    (hspan : Submodule.span L
      (Set.range (_root_.GroupLike.val (R := L) (A := L ⊗[k] A))) = ⊤) :
    Function.Bijective (groupLikeBaseChange (R := k) (K := L) (A := A)) := by
  have hinj : Function.Injective (groupLikeBaseChange (R := k) (K := L) (A := A)) := by
    intro g h heq
    apply _root_.GroupLike.val_injective
    apply sub_eq_zero.mp
    apply (Module.FaithfullyFlat.one_tmul_eq_zero_iff k _ (A := L) _).mp
    have hval := congrArg _root_.GroupLike.val heq
    simpa only [TensorProduct.tmul_sub, sub_eq_zero, val_groupLikeBaseChange] using hval
  refine ⟨hinj, ?_⟩
  intro g
  let B := L ⊗[k] L
  let : ConnectedSpace (PrimeSpectrum B) :=
    IsPurelyInseparable.connectedSpace_primeSpectrum_tensorProduct k L
  let δ₁ := Algebra.TensorProduct.map
    (Algebra.TensorProduct.includeLeft : L →ₐ[k] B) (AlgHom.id k A)
  let δ₂ := Algebra.TensorProduct.map
    (Algebra.TensorProduct.includeRight : L →ₐ[k] B) (AlgHom.id k A)
  have hleftMap : IsScalarTower.toAlgHom k L B =
      (Algebra.TensorProduct.includeLeft : L →ₐ[k] B) := by
    ext l
    rfl
  let σ : B ≃ₐ[k] B := Algebra.TensorProduct.comm k L L
  have hswap (x : L ⊗[k] A) : σ • δ₁ x = δ₂ x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
    | tmul l a => simp [δ₁, δ₂, σ]
  have hg₂ : IsGroupLikeElem B (δ₂ g.val) := by
    rw [← hswap]
    apply ScalarAut.isGroupLikeElem_smul
    simpa only [val_groupLikeScalarTowerHom, hleftMap] using
      (groupLikeScalarTowerHom (k := k) (K := B) (A := A) g).isGroupLikeElem_val
  obtain ⟨h, hh⟩ := (groupLikeScalarTowerEquiv (K := B) hspan).surjective ⟨δ₂ g.val, hg₂⟩
  have heq : δ₁ h.val = δ₂ g.val := by
    simpa only [val_groupLikeScalarTowerEquiv, hleftMap] using congrArg _root_.GroupLike.val hh
  let q := Algebra.TensorProduct.map (Algebra.TensorProduct.lmul' k (S := L)) (AlgHom.id k A)
  have hq₁ (x : L ⊗[k] A) : q (δ₁ x) = x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul l a => simp [q, δ₁]
  have hq₂ (x : L ⊗[k] A) : q (δ₂ x) = x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul l a => simp [q, δ₂]
  have hhg : h.val = g.val := by
    simpa only [hq₁, hq₂] using congrArg q heq
  rw [hhg] at heq
  obtain ⟨a, ha⟩ := exists_one_tmul_of_equal_pullbacks g.val heq
  have hga : IsGroupLikeElem k a := by
    rw [← isGroupLikeElem_one_tmul_iff (K := L), ha]
    exact g.isGroupLikeElem_val
  exact ⟨⟨a, hga⟩, _root_.GroupLike.val_injective
    (by simpa only [val_groupLikeBaseChange] using ha)⟩

/-- Spanning by group-like elements descends along a purely inseparable field extension
of a commutative bialgebra. -/
theorem span_groupLike_eq_top_of_isPurelyInseparable
    (hspan : Submodule.span L
      (Set.range (_root_.GroupLike.val (R := L) (A := L ⊗[k] A))) = ⊤) :
    Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := A))) = ⊤ := by
  let p := Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := A)))
  have hp : p.baseChange L = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    obtain ⟨h, rfl⟩ := (groupLikeBaseChange_bijective_of_isPurelyInseparable hspan).surjective g
    rw [val_groupLikeBaseChange]
    exact Submodule.tmul_mem_baseChange_of_mem 1
      (show h.val ∈ p from Submodule.subset_span ⟨h, rfl⟩)
  apply Submodule.baseChange_injective (A := L)
  simpa only [Submodule.baseChange_top] using hp

end TauCeti
