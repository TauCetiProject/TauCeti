/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph
-/
module

public import TauCeti.Algebra.Bialgebra.GroupLike.ScalarTower
public import TauCeti.Algebra.Coalgebra.GroupLike.BaseChange
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import TauCeti.FieldTheory.PurelyInseparable.BaseChange
import TauCeti.RingTheory.Flat.EffectiveDescent
import TauCeti.RingTheory.Idempotents.Connected.Spectrum

/-!
# Purely inseparable descent of split bialgebras

If the group-like elements of a commutative bialgebra span after a purely inseparable
field extension, each of them descends uniquely, and the original group-like elements
already span. No finite-generation or perfectness hypothesis is required. For coordinate
algebras this says that a group of multiplicative type split by a purely inseparable
extension is already split.

The two pullbacks of a character to the tensor square agree by connected-spectrum
rigidity: the tensor square is a local ring
(`TauCeti.IsPurelyInseparable.isLocalRing_tensorProduct`). Exactness of the Amitsur complex
(`Module.FaithfullyFlat.exact_mk_one_lTensor_sub_mk_one`) then descends its coefficients.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.18 and Corollary 12.20.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {k L A : Type*} [Field k] [Field L] [Algebra k L] [IsPurelyInseparable k L]
  [CommRing A] [Bialgebra k A]

/-- The two pullbacks of a character of a split bialgebra to the tensor square of a purely
inseparable extension agree. -/
private theorem map_includeLeft_val_eq_map_includeRight_val
    (hspan : Submodule.span L
      (Set.range (_root_.GroupLike.val (R := L) (A := L ⊗[k] A))) = ⊤)
    (g : _root_.GroupLike L (L ⊗[k] A)) :
    Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeLeft : L →ₐ[k] L ⊗[k] L) (AlgHom.id k A) g.val =
      Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeRight : L →ₐ[k] L ⊗[k] L) (AlgHom.id k A) g.val := by
  let B := L ⊗[k] L
  -- The tensor square is a local ring, so its spectrum is connected.
  have : ConnectedSpace (PrimeSpectrum B) :=
    inferInstanceAs (ConnectedSpace (PrimeSpectrum (L ⊗[k] L)))
  let δ₁ := Algebra.TensorProduct.map
    (Algebra.TensorProduct.includeLeft : L →ₐ[k] B) (AlgHom.id k A)
  let δ₂ := Algebra.TensorProduct.map
    (Algebra.TensorProduct.includeRight : L →ₐ[k] B) (AlgHom.id k A)
  have hleftMap : IsScalarTower.toAlgHom k L B =
      (Algebra.TensorProduct.includeLeft : L →ₐ[k] B) := by
    ext l
    rfl
  -- Swapping the factors of `B` exchanges the pullbacks, so `δ₂ g` is a character over `B`.
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
  -- Rigidity over the connected spectrum of `B`: it is the first pullback of a character `h`.
  obtain ⟨h, hh⟩ := (groupLikeScalarTowerEquiv (K := B) hspan).surjective ⟨δ₂ g.val, hg₂⟩
  have heq : δ₁ h.val = δ₂ g.val := by
    simpa only [val_groupLikeScalarTowerEquiv, hleftMap] using congrArg _root_.GroupLike.val hh
  -- Multiplication `B → L` retracts both pullbacks, which identifies `h` with `g`.
  let q := Algebra.TensorProduct.map (Algebra.TensorProduct.lmul' k (S := L)) (AlgHom.id k A)
  have hq₁ : q.comp δ₁ = AlgHom.id k (L ⊗[k] A) := by
    rw [← Algebra.TensorProduct.map_comp, Algebra.TensorProduct.lmul'_comp_includeLeft,
      AlgHom.comp_id, Algebra.TensorProduct.map_id]
  have hq₂ : q.comp δ₂ = AlgHom.id k (L ⊗[k] A) := by
    rw [← Algebra.TensorProduct.map_comp, Algebra.TensorProduct.lmul'_comp_includeRight,
      AlgHom.comp_id, Algebra.TensorProduct.map_id]
  have hhg : h.val = g.val := by
    simpa only [← AlgHom.comp_apply, hq₁, hq₂, AlgHom.id_apply] using congrArg q heq
  rwa [hhg] at heq

/-- If a commutative bialgebra splits after a purely inseparable field extension,
its group-like elements descend uniquely. -/
theorem groupLikeBaseChange_bijective_of_isPurelyInseparable
    (hspan : Submodule.span L
      (Set.range (_root_.GroupLike.val (R := L) (A := L ⊗[k] A))) = ⊤) :
    Function.Bijective (groupLikeBaseChange (R := k) (K := L) (A := A)) := by
  refine ⟨groupLikeBaseChange_injective, fun g ↦ ?_⟩
  -- Reassociate the two pullbacks of `g` into the Amitsur complex of `k → L`.
  let e := TensorProduct.assoc k L L A
  have h₁ (x : L ⊗[k] A) :
      e (Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeLeft : L →ₐ[k] L ⊗[k] L) (AlgHom.id k A) x) =
        (TensorProduct.mk k L A 1).lTensor L x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul l a => simp [e]
  have h₂ (x : L ⊗[k] A) :
      e (Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeRight : L →ₐ[k] L ⊗[k] L) (AlgHom.id k A) x) =
        TensorProduct.mk k L (L ⊗[k] A) 1 x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul l a => simp [e]
  have hg : ((TensorProduct.mk k L A 1).lTensor L - TensorProduct.mk k L (L ⊗[k] A) 1)
      g.val = 0 := by
    rw [LinearMap.sub_apply, sub_eq_zero, ← h₁, ← h₂,
      map_includeLeft_val_eq_map_includeRight_val hspan g]
  -- Amitsur exactness descends the coefficients of `g`.
  obtain ⟨a, ha⟩ := (Module.FaithfullyFlat.exact_mk_one_lTensor_sub_mk_one L A g.val).mp hg
  rw [TensorProduct.mk_apply] at ha
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
    exact p.tmul_mem_baseChange_of_mem 1 (Submodule.subset_span ⟨h, rfl⟩)
  apply Submodule.baseChange_injective (A := L)
  simpa only [Submodule.baseChange_top] using hp

end TauCeti
