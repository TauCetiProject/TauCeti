/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.Abel
import TauCeti.LinearAlgebra.End.Aeval
import TauCeti.LinearAlgebra.LinearMap.Ker

/-!
# Extending endomorphisms along a split surjection

For linear maps `π : F →ₗ[R] M` and `σ : M →ₗ[R] F` with `π ∘ₗ σ = id`,
`LinearMap.splitEnd π σ h` extends an endomorphism of `M` to `F` by the identity on `ker π`.
This is a monoid homomorphism, and an extended endomorphism is invertible exactly when the
original one is. The construction requires no freeness, finiteness or projectivity assumptions.

The evaluation and intertwining lemmas describe the extension without unfolding it. The affine
formula `LinearMap.splitEnd_one_sub` is useful for characteristic polynomials, while the
construction and its unit criterion also underlie determinants on finite projective modules.
`LinearMap.kerSplitEndEquiv` identifies the kernel of an extension with the original kernel;
in particular, extending by the identity does not add generalized spectral vectors at zero.

Evaluating a polynomial with zero constant term commutes with extending an endomorphism by zero
along a retract (`LinearMap.aeval_comp_comp_of_retract`). Consequently, for any polynomial `p`
with invertible constant term, `LinearMap.kerAevalEquivOfRetract` identifies
`ker (p(σ ∘ u ∘ π))` with `ker (p(u))` via the retraction and section.
-/

public section

namespace LinearMap

variable {R M F : Type*} [Semiring R] [AddCommGroup F] [Module R F]

section AddCommMonoid

variable [AddCommMonoid M] [Module R M]

/-- Extend an endomorphism of a retract `M` of `F` by the identity on `ker π`. -/
def splitEnd (π : F →ₗ[R] M) (σ : M →ₗ[R] F) (h : π ∘ₗ σ = id) :
    Module.End R M →* Module.End R F where
  toFun f := σ ∘ₗ f ∘ₗ π + (1 - σ ∘ₗ π)
  map_one' := by rw [Module.End.one_eq_id, id_comp, add_sub_cancel]
  map_mul' f g := by
    have h' (x : M) : π (σ x) = x := congr($h x)
    ext x
    simp only [LinearMap.add_apply, comp_apply, LinearMap.sub_apply, _root_.one_apply_eq_self,
      _root_.mul_apply_eq_comp,
      map_add, map_sub, h']
    abel

/-- The extension acts by `f` on `σ(M)` and by the identity on `ker π`. -/
theorem splitEnd_apply (π : F →ₗ[R] M) (σ : M →ₗ[R] F) (h : π ∘ₗ σ = id)
    (f : Module.End R M) :
    splitEnd π σ h f = σ ∘ₗ f ∘ₗ π + (1 - σ ∘ₗ π) :=
  (rfl)

/-- The section intertwines the original endomorphism and its extension. -/
@[simp]
theorem splitEnd_comp (π : F →ₗ[R] M) (σ : M →ₗ[R] F) (h : π ∘ₗ σ = id)
    (f : Module.End R M) :
    splitEnd π σ h f ∘ₗ σ = σ ∘ₗ f := by
  simp [splitEnd_apply, add_comp, sub_comp, comp_assoc, h, Module.End.one_eq_id]

end AddCommMonoid

variable [AddCommGroup M] [Module R M]
  (π : F →ₗ[R] M) (σ : M →ₗ[R] F) (h : π ∘ₗ σ = id)

/-- The retraction intertwines the extension and the original endomorphism. -/
@[simp]
theorem comp_splitEnd (f : Module.End R M) :
    π ∘ₗ splitEnd π σ h f = f ∘ₗ π := by
  simp [splitEnd_apply, comp_add, comp_sub, ← comp_assoc, h, Module.End.one_eq_id]

/-- The retraction and section identify the kernel of an extension by the identity with
its original kernel. No freeness or finiteness hypothesis is needed. -/
def kerSplitEndEquiv (f : Module.End R M) :
    ker (splitEnd π σ h f) ≃ₗ[R] ker f := by
  have h' (x : M) : π (σ x) = x := congr($h x)
  have hπ (x : ker (splitEnd π σ h f)) : f (π x) = 0 := by
    have hx := congr($(comp_splitEnd π σ h f) x)
    simpa only [comp_apply, mem_ker.mp x.property, map_zero] using hx.symm
  refine LinearEquiv.ofLinearMap
    ((π.comp (ker (splitEnd π σ h f)).subtype).codRestrict _ fun x ↦ hπ x)
    ((σ.comp (ker f).subtype).codRestrict _ ?_) ?_ ?_
  · intro x
    have hx := congr($(splitEnd_comp π σ h f) x)
    simpa only [mem_ker, comp_apply, Submodule.subtype_apply,
      mem_ker.mp x.property, map_zero] using hx
  · ext x
    exact h' x
  · ext x
    have hx := mem_ker.mp x.property
    simp only [splitEnd_apply, LinearMap.add_apply, LinearMap.sub_apply, comp_apply,
      _root_.one_apply_eq_self,
      hπ x, map_zero, zero_add, sub_eq_zero] at hx
    exact hx.symm

/-- The kernel equivalence for an extension applies the retraction. -/
@[simp]
theorem coe_kerSplitEndEquiv_apply (f : Module.End R M) (x : ker (splitEnd π σ h f)) :
    (kerSplitEndEquiv π σ h f x : M) = π x :=
  (rfl)

/-- The inverse kernel equivalence for an extension applies the section. -/
@[simp]
theorem coe_kerSplitEndEquiv_symm_apply (f : Module.End R M) (x : ker f) :
    ((kerSplitEndEquiv π σ h f).symm x : F) = σ x :=
  (rfl)

/-- Extending an endomorphism is an affine operation around the identity. -/
theorem splitEnd_eq_one_add (f : Module.End R M) :
    splitEnd π σ h f = 1 + σ ∘ₗ (f - 1) ∘ₗ π := by
  simp only [splitEnd_apply, sub_comp, comp_sub, Module.End.one_eq_id, id_comp]
  abel

/-- Extending `1 - f` gives `1 - σ ∘ₗ f ∘ₗ π`. -/
@[simp]
theorem splitEnd_one_sub (f : Module.End R M) :
    splitEnd π σ h (1 - f) = 1 - σ ∘ₗ f ∘ₗ π := by
  simp only [splitEnd_apply, sub_comp, comp_sub, Module.End.one_eq_id, id_comp]
  abel

/-- Extending by the identity preserves and reflects invertibility. -/
@[simp]
theorem isUnit_splitEnd_iff (f : Module.End R M) : IsUnit (splitEnd π σ h f) ↔ IsUnit f := by
  refine ⟨fun hg ↦ ?_, fun hf ↦ hf.map _⟩
  obtain ⟨g, hfg, hgf⟩ := isUnit_iff_exists.mp hg
  refine isUnit_iff_exists.mpr ⟨π ∘ₗ g ∘ₗ σ, ?_, ?_⟩
  · calc
      f * (π ∘ₗ g ∘ₗ σ) = π ∘ₗ (splitEnd π σ h f * g) ∘ₗ σ := by
        simp only [Module.End.mul_eq_comp, ← comp_assoc, comp_splitEnd]
      _ = 1 := by simp [hfg, Module.End.one_eq_id, h]
  · calc
      (π ∘ₗ g ∘ₗ σ) * f = π ∘ₗ (g * splitEnd π σ h f) ∘ₗ σ := by
        simp [Module.End.mul_eq_comp, comp_assoc, splitEnd_comp]
      _ = 1 := by simp [hgf, Module.End.one_eq_id, h]

section Polynomial

/-- Extending an endomorphism along a retract `π ∘ₗ σ = id` commutes with evaluating a
polynomial whose constant coefficient is zero. -/
theorem aeval_comp_comp_of_retract {R M F : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid F] [Module R F]
    {π : F →ₗ[R] M} {σ : M →ₗ[R] F} (h : π ∘ₗ σ = id)
    (u : Module.End R M) {p : Polynomial R} (hp : p.coeff 0 = 0) :
    Polynomial.aeval (σ ∘ₗ u ∘ₗ π) p = σ ∘ₗ Polynomial.aeval u p ∘ₗ π := by
  obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.2 hp
  have hπ : u ∘ₗ π = π ∘ₗ (σ ∘ₗ u ∘ₗ π) := by
    rw [← comp_assoc, ← comp_assoc, h, id_comp]
  rw [map_mul, Polynomial.aeval_X, map_mul, Polynomial.aeval_X,
    Module.End.mul_eq_comp, Module.End.mul_eq_comp]
  calc (σ ∘ₗ u ∘ₗ π) ∘ₗ Polynomial.aeval (σ ∘ₗ u ∘ₗ π) q
      = σ ∘ₗ u ∘ₗ (π ∘ₗ Polynomial.aeval (σ ∘ₗ u ∘ₗ π) q) := by simp only [comp_assoc]
    _ = σ ∘ₗ u ∘ₗ (Polynomial.aeval u q ∘ₗ π) := by
          rw [← Module.End.aeval_comp_of_comp_eq hπ q]
    _ = σ ∘ₗ (u ∘ₗ Polynomial.aeval u q) ∘ₗ π := by simp only [comp_assoc]

variable {R M F : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup F] [Module R F]

/-- For a split surjection `π ∘ₗ σ = id` and a polynomial `p` with invertible constant term, the
retraction and section identify `ker (p(σ ∘ u ∘ π))` with `ker (p(u))`. -/
noncomputable def kerAevalEquivOfRetract (π : F →ₗ[R] M) (σ : M →ₗ[R] F) (h : π ∘ₗ σ = id)
    (u : Module.End R M) {p : Polynomial R} (hp : IsUnit (p.coeff 0)) :
    ker (Polynomial.aeval (σ ∘ₗ u ∘ₗ π) p) ≃ₗ[R] ker (Polynomial.aeval u p) := by
  let c : R := ↑hp.unit⁻¹
  have hc : c * p.coeff 0 = 1 := hp.unit.inv_mul
  have hc_unit : IsUnit c := hp.unit⁻¹.isUnit
  set B : Polynomial R := 1 - Polynomial.C c * p
  have hB0 : B.coeff 0 = 0 := by simp [B, hc]
  have hB_ext := aeval_comp_comp_of_retract h u hB0
  have hsplit : splitEnd π σ h (c • Polynomial.aeval u p) =
      c • Polynomial.aeval (σ ∘ₗ u ∘ₗ π) p := by
    have h1 : c • Polynomial.aeval u p = 1 - Polynomial.aeval u B := by
      simp [B, Algebra.algebraMap_eq_smul_one]
    have h2 : c • Polynomial.aeval (σ ∘ₗ u ∘ₗ π) p =
        1 - Polynomial.aeval (σ ∘ₗ u ∘ₗ π) B := by
      simp [B, Algebra.algebraMap_eq_smul_one]
    rw [h1, splitEnd_one_sub, ← hB_ext, ← h2]
  exact (LinearEquiv.ofEq _ _ (by rw [← ker_smul_of_isUnit _ hc_unit, ← hsplit])).trans
    ((kerSplitEndEquiv π σ h (c • Polynomial.aeval u p)).trans
      (LinearEquiv.ofEq _ _ (ker_smul_of_isUnit _ hc_unit)))

/-- The forward map of `kerAevalEquivOfRetract` applies the retraction. -/
@[simp]
theorem coe_kerAevalEquivOfRetract_apply (π : F →ₗ[R] M) (σ : M →ₗ[R] F) (h : π ∘ₗ σ = id)
    (u : Module.End R M) {p : Polynomial R} (hp : IsUnit (p.coeff 0))
    (x : ker (Polynomial.aeval (σ ∘ₗ u ∘ₗ π) p)) :
    (kerAevalEquivOfRetract π σ h u hp x : M) = π x :=
  (rfl)

/-- The inverse map of `kerAevalEquivOfRetract` applies the section. -/
@[simp]
theorem coe_kerAevalEquivOfRetract_symm_apply (π : F →ₗ[R] M) (σ : M →ₗ[R] F) (h : π ∘ₗ σ = id)
    (u : Module.End R M) {p : Polynomial R} (hp : IsUnit (p.coeff 0))
    (x : ker (Polynomial.aeval u p)) :
    ((kerAevalEquivOfRetract π σ h u hp).symm x : F) = σ x :=
  (rfl)

end Polynomial

end LinearMap
