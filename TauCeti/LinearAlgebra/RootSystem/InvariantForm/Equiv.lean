/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
public import TauCeti.LinearAlgebra.RootSystem.EquivComp
public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Hom
public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.MulAction

/-!
# Transporting invariant forms along equivalences of root pairings

An equivalence of root pairings `e : P ≃ Q` carries the roots of `P` to the roots of `Q` and
intertwines the reflections, so pulling a bilinear form on the weight space of `Q` back along the
weight equivalence identifies the invariant forms of the two pairings. This file defines the
pushforward `RootPairing.InvariantForm.map e B`, the form `(x, y) ↦ B (e⁻¹ x, e⁻¹ y)`, and shows
that it is compatible with composition and inverses, with rescaling by units, and with positive
definiteness. The canonical root form is carried to the canonical root form, so for an automorphism
of a root pairing the canonical form is a fixed point.

## Main definitions

* `RootPairing.InvariantForm.map`: the pushforward of an invariant form along an equivalence.
* `RootPairing.InvariantForm.mapEquiv`: the resulting bijection between the invariant forms of two
  equivalent root pairings.

## Main results

* `RootPairing.Equiv.weightEquiv_symm_root`: the inverse weight equivalence sends roots to roots.
* `RootPairing.InvariantForm.map_map`: pushing forward along two equivalences is pushing forward
  along their composite.
* `RootPairing.InvariantForm.posDef_map_iff`: the pushforward is positive definite exactly when the
  form is.
* `RootPairing.InvariantForm.map_toInvariantForm`: the canonical root form is carried to the
  canonical root form.
-/

public section

namespace RootPairing

variable {ι R M N ι₂ M₂ N₂ ι₃ M₃ N₃ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  [AddCommGroup M₃] [Module R M₃] [AddCommGroup N₃] [Module R N₃]
  {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂} {S : RootPairing ι₃ R M₃ N₃}

/-! ### The inverse weight equivalence -/

namespace Equiv

/-- **The inverse weight equivalence of an equivalence of root pairings sends the roots of the
target back to the corresponding roots of the source.** -/
@[simp]
theorem weightEquiv_symm_root (e : P.Equiv Q) (i : ι₂) :
    e.weightEquiv.symm (Q.root i) = P.root (e.indexEquiv.symm i) := by
  rw [LinearEquiv.symm_apply_eq, weightEquiv_apply, Hom.root_weightMap_apply,
    _root_.Equiv.apply_symm_apply]

/-- The inverse weight equivalence of an equivalence of root pairings intertwines the reflections
of the target and of the source. -/
theorem weightEquiv_symm_reflection (e : P.Equiv Q) (i : ι₂) (x : M₂) :
    e.weightEquiv.symm (Q.reflection i x) =
      P.reflection (e.indexEquiv.symm i) (e.weightEquiv.symm x) := by
  rw [LinearEquiv.symm_apply_eq, weightEquiv_reflection, _root_.Equiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

end Equiv

namespace InvariantForm

/-- The **pushforward of an invariant form** along an equivalence of root pairings `e : P ≃ Q`:
the invariant form `(x, y) ↦ B (e⁻¹ x, e⁻¹ y)` of `Q`. -/
noncomputable def map (e : P.Equiv Q) (B : P.InvariantForm) : Q.InvariantForm where
  form := LinearMap.BilinForm.congr e.weightEquiv B.form
  symm := ⟨fun x y ↦ by simpa using B.symm.eq _ _⟩
  ne_zero i := by simpa using B.ne_zero (e.indexEquiv.symm i)
  isOrthogonal_reflection i x y := by
    simp [e.weightEquiv_symm_reflection,
      B.isOrthogonal_reflection (e.indexEquiv.symm i) (e.weightEquiv.symm x)
        (e.weightEquiv.symm y)]

@[simp]
theorem map_form_apply (e : P.Equiv Q) (B : P.InvariantForm) (x y : M₂) :
    (B.map e).form x y = B.form (e.weightEquiv.symm x) (e.weightEquiv.symm y) :=
  (rfl)

@[simp]
theorem map_id (B : P.InvariantForm) : B.map (Equiv.id P) = B := by
  ext x y
  have h (z : M) : (Equiv.id P).weightEquiv.symm z = z :=
    (LinearEquiv.symm_apply_eq _).mpr (by simp)
  rw [map_form_apply, h, h]

/-- **Pushing forward along two equivalences is pushing forward along their composite.** -/
@[simp]
theorem map_map (e : P.Equiv Q) (f : Q.Equiv S) (B : P.InvariantForm) :
    (B.map e).map f = B.map (f.comp e) := by
  ext x y
  simp

/-- Pushing forward along an equivalence and then along its inverse is the identity. -/
theorem map_symm_map (e : P.Equiv Q) (B : P.InvariantForm) :
    (B.map e).map (Equiv.symm P Q e) = B := by
  simp

/-- Pushing forward along the inverse of an equivalence and then along it is the identity. -/
theorem map_map_symm (e : P.Equiv Q) (B : Q.InvariantForm) :
    (B.map (Equiv.symm P Q e)).map e = B := by
  simp

/-- An equivalence of root pairings identifies their invariant forms. -/
@[expose, simps]
noncomputable def mapEquiv (e : P.Equiv Q) : P.InvariantForm ≃ Q.InvariantForm where
  toFun := map e
  invFun := map (Equiv.symm P Q e)
  left_inv := map_symm_map e
  right_inv := map_map_symm e

/-- The pushforward commutes with rescaling by a unit. -/
@[simp]
theorem map_smul (e : P.Equiv Q) (c : Rˣ) (B : P.InvariantForm) : (c • B).map e = c • B.map e :=
  (rfl)

/-- **The pushforward of a positive-definite form is positive definite**, and conversely. -/
theorem posDef_map_iff [LinearOrder R] {e : P.Equiv Q} {B : P.InvariantForm} :
    (B.map e).form.toQuadraticMap.PosDef ↔ B.form.toQuadraticMap.PosDef := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · simpa using h (e.weightEquiv x) (e.weightEquiv.map_ne_zero_iff.mpr hx)
  · simpa using h (e.weightEquiv.symm x) (e.weightEquiv.symm.map_ne_zero_iff.mpr hx)

/-- **The canonical root form is carried to the canonical root form.** In particular it is fixed by
every automorphism of a finite root pairing. -/
@[simp]
theorem map_toInvariantForm [Fintype ι] [Fintype ι₂] [P.IsAnisotropic] [Q.IsAnisotropic]
    (e : P.Equiv Q) : P.toInvariantForm.map e = Q.toInvariantForm := by
  ext x y
  simpa using (e.toHom.rootForm_weightMap (e.weightEquiv.symm x) (e.weightEquiv.symm y)).symm

end InvariantForm

end RootPairing
