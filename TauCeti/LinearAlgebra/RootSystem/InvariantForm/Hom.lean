/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
public import TauCeti.LinearAlgebra.RootSystem.HomInvariance
public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.MulAction

/-!
# Invariant forms under morphisms of root pairings

A morphism `f : P.Hom Q` of root pairings intertwines the reflection at a root of `P` with the
reflection at the corresponding root of `Q`, so an invariant form `B` of `Q` pulls back to the
invariant form `(x, y) ↦ B (f x) (f y)` of `P`, written `comap f B`. Pulling back is functorial and
commutes with rescaling, preserves positive definiteness when the weight map is injective, and
along an equivalence of root pairings it is a bijection of invariant forms.

A morphism of finite root pairings preserves the canonical root form: its index bijection
reindexes the sum of products of coroot values. The weight map need not be bijective, and the
roots need not span the weight space. In particular diagram automorphisms preserve lengths
also on weights outside the root lattice. So the canonical invariant form of `Q` pulls back to that
of `P`.

## Main definitions

* `RootPairing.InvariantForm.comap`: the pullback of an invariant form along a morphism.
* `RootPairing.InvariantForm.comapEquiv`: pulling back along an equivalence, as a bijection of
  invariant forms.

## Main results

* `RootPairing.Hom.rootForm_weightMap`: a morphism of finite root pairings preserves the canonical
  root form.
* `RootPairing.InvariantForm.comap_toInvariantForm`: the canonical invariant form pulls back to the
  canonical invariant form.
* `RootPairing.InvariantForm.posDef_comap`, `RootPairing.InvariantForm.posDef_comap_iff`: the
  pullback along a morphism with injective weight map of a positive-definite form is positive
  definite, and along an equivalence the converse holds.
-/

public section

namespace RootPairing.Hom

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂}
  [Fintype ι] [Fintype ι₂]

/-- A morphism of finite root pairings preserves the canonical root form on weights. -/
@[simp]
theorem rootForm_weightMap (f : P.Hom Q) (x y : M) :
    Q.RootForm (f.weightMap x) (f.weightMap y) = P.RootForm x y := by
  simp only [RootPairing.rootForm_apply_apply]
  rw [← f.indexEquiv.sum_comp]
  simp only [coroot'_weightMap]

end RootPairing.Hom

namespace RootPairing.InvariantForm

variable {ι ι₂ ι₃ R M N M₂ N₂ M₃ N₃ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  [AddCommGroup M₃] [Module R M₃] [AddCommGroup N₃] [Module R N₃]
  {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂} {S : RootPairing ι₃ R M₃ N₃}

/-- The **pullback of an invariant form** along a morphism of root pairings `f : P.Hom Q`: the
invariant form `(x, y) ↦ B (f x) (f y)` of `P`. -/
def comap (f : P.Hom Q) (B : Q.InvariantForm) : P.InvariantForm where
  form := B.form.compl₁₂ f.weightMap f.weightMap
  symm := ⟨fun x y ↦ by simpa using B.symm.eq (f.weightMap x) (f.weightMap y)⟩
  ne_zero i := by simpa [Hom.root_weightMap_apply] using B.ne_zero (f.indexEquiv i)
  isOrthogonal_reflection i x y := by simp [Hom.weightMap_reflection]

@[simp]
theorem comap_form_apply (f : P.Hom Q) (B : Q.InvariantForm) (x y : M) :
    (comap f B).form x y = B.form (f.weightMap x) (f.weightMap y) :=
  (rfl)

@[simp]
theorem comap_id (B : P.InvariantForm) : comap (Hom.id P) B = B := by
  ext x y
  simp

theorem comap_comp (g : Q.Hom S) (f : P.Hom Q) (B : S.InvariantForm) :
    comap (g.comp f) B = comap f (comap g B) := by
  ext x y
  simp

@[simp]
theorem comap_smul (f : P.Hom Q) (c : Rˣ) (B : Q.InvariantForm) :
    comap f (c • B) = c • comap f B := by
  ext x y
  simp

/-- **The canonical invariant form pulls back to the canonical invariant form** along a morphism of
finite anisotropic root pairings. -/
@[simp]
theorem comap_toInvariantForm [Fintype ι] [Fintype ι₂] [P.IsAnisotropic] [Q.IsAnisotropic]
    (f : P.Hom Q) : comap f Q.toInvariantForm = P.toInvariantForm := by
  ext x y
  simp

/-- Pulling back invariant forms along an equivalence of root pairings is a bijection, with inverse
the pullback along the inverse equivalence. -/
noncomputable def comapEquiv (e : P.Equiv Q) : Q.InvariantForm ≃ P.InvariantForm where
  toFun := comap e.toHom
  invFun := comap (Equiv.symm P Q e).toHom
  left_inv B := by
    ext x y
    simp [← Equiv.weightEquiv_apply]
  right_inv B := by
    ext x y
    simp

@[simp]
theorem comapEquiv_apply (e : P.Equiv Q) (B : Q.InvariantForm) : comapEquiv e B = comap e.toHom B :=
  (rfl)

@[simp]
theorem comapEquiv_symm_apply (e : P.Equiv Q) (B : P.InvariantForm) :
    (comapEquiv e).symm B = comap (Equiv.symm P Q e).toHom B :=
  (rfl)

section Ordered

variable [PartialOrder R]

/-- The pullback of a positive-definite invariant form along a morphism with injective weight map
is positive definite. -/
theorem posDef_comap {f : P.Hom Q} (hf : Function.Injective f.weightMap) {B : Q.InvariantForm}
    (hB : B.form.toQuadraticMap.PosDef) : (comap f B).form.toQuadraticMap.PosDef := fun x hx ↦ by
  simpa using hB (f.weightMap x) ((map_ne_zero_iff _ hf).mpr hx)

/-- **Along an equivalence, an invariant form is positive definite exactly when its pullback
is.** -/
@[simp]
theorem posDef_comap_iff (e : P.Equiv Q) {B : Q.InvariantForm} :
    (comap e.toHom B).form.toQuadraticMap.PosDef ↔ B.form.toQuadraticMap.PosDef := by
  refine ⟨fun h ↦ ?_, posDef_comap e.bijective_weightMap.injective⟩
  have := posDef_comap (Equiv.symm P Q e).bijective_weightMap.injective h
  rwa [← comapEquiv_apply e B, ← comapEquiv_symm_apply, _root_.Equiv.symm_apply_apply] at this

end Ordered

end RootPairing.InvariantForm
