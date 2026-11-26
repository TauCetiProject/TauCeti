/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorAlgebra.HermitianMetric
public import TauCeti.LinearAlgebra.ExteriorPower.Complexification

/-!
# Complexification of exterior sesquilinear Gram forms

Complex-valued exterior forms on a real module `V` naturally live in two isomorphic models: the
tensor-product complexification `ℂ ⊗[ℝ] ExteriorAlgebra ℝ V`, which carries the sesquilinearly
complexified real exterior Gram form `(B.sesqExteriorAlgebra).sesqComplexification`, and the
complex exterior algebra `ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)`, on which complex Clifford/Chevalley maps
and complexified wedge bases act via `B.sesqComplexification.sesqExteriorAlgebra`. For any real
bilinear form `B : LinearMap.BilinForm ℝ V`, this file transports these sesquilinear Gram forms
between the two models across `ExteriorAlgebra.baseChangeEquiv ℝ V ℂ` (building on the
exterior-power comparison in `TauCeti.LinearAlgebra.ExteriorPower.Complexification`), and relates
`sesqComplexification B.sesqExteriorAlgebra` to homogeneous degrees. When `B` is symmetric, the
transported forms are Hermitian, feeding complexified Euclidean exterior metrics and the
basis-free spinor-endomorphism and spinor-tensor metric comparisons.

Let `B : LinearMap.BilinForm ℝ V` be a real bilinear form on `V`, with sesquilinear complexification
`B.sesqComplexification` on `ℂ ⊗[ℝ] V`:

* on the exterior algebra, `ExteriorAlgebra.baseChangeEquiv ℝ V ℂ` intertwines
  `B.sesqComplexification.sesqExteriorAlgebra` on `ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)` with
  `LinearMap.BilinForm.sesqComplexification B.sesqExteriorAlgebra` on `ℂ ⊗[ℝ] ExteriorAlgebra ℝ V`;
* on `ℂ ⊗[ℝ] ExteriorAlgebra ℝ V`, the complexified Gram form restricts in homogeneous degree `n`
  along `(⋀[ℝ]^n V).subtype.baseChange ℂ` to
  `LinearMap.BilinForm.sesqComplexification (B.sesqExteriorPower n)`, and makes distinct
  complexified exterior powers `(⋀[ℝ]^p V).baseChange ℂ` and `(⋀[ℝ]^q V).baseChange ℂ` orthogonal.

No finiteness, flatness, or basis assumption is needed for the comparison theorems.

## Main results

* `LinearMap.BilinForm.sesqExteriorAlgebra_sesqComplexification_baseChangeEquiv` and
  `LinearMap.BilinForm.sesqComplexification_sesqExteriorAlgebra_baseChangeEquiv_symm`:
  compatibility of `sesqExteriorAlgebra` with `sesqComplexification` across
  `ExteriorAlgebra.baseChangeEquiv ℝ V ℂ`.
* `LinearMap.BilinForm.sesqComplexification_sesqExteriorAlgebra_subtype_baseChange`,
  `LinearMap.BilinForm.sesqComplexification_sesqExteriorAlgebra_eq_zero_of_mem_baseChange_of_ne`,
  and
  `LinearMap.BilinForm.sesqComplexification_sesqExteriorAlgebra_subtype_baseChange_eq_zero_of_ne`:
  degree-`n` restriction and degree orthogonality on `ℂ ⊗[ℝ] ExteriorAlgebra ℝ V`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., World Scientific (2020),
  §2.2.4.
-/

public section

open scoped TensorProduct
open LinearMap (BilinForm)
open Matrix

namespace LinearMap.BilinForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Complexified exterior Gram form in homogeneous degree `n`**: on `ℂ ⊗[ℝ] ExteriorAlgebra ℝ V`,
restricting `B.sesqExteriorAlgebra.sesqComplexification` along `(⋀[ℝ]^n V).subtype.baseChange ℂ`
gives `(B.sesqExteriorPower n).sesqComplexification`. -/
@[simp]
theorem sesqComplexification_sesqExteriorAlgebra_subtype_baseChange (B : BilinForm ℝ V) (n : ℕ)
    (x y : ℂ ⊗[ℝ] ⋀[ℝ]^n V) :
    sesqComplexification B.sesqExteriorAlgebra
        ((⋀[ℝ]^n V).subtype.baseChange ℂ x) ((⋀[ℝ]^n V).subtype.baseChange ℂ y) =
      sesqComplexification (B.sesqExteriorPower n) x y :=
  sesqComplexification_baseChange_baseChange
    (B := B.sesqExteriorPower n) (B' := B.sesqExteriorAlgebra)
    (B.sesqExteriorAlgebra_coe_coe) x y

/-- **Distinct complexified exterior powers are orthogonal**: for `p ≠ q`, the subspaces
`(⋀[ℝ]^p V).baseChange ℂ` and `(⋀[ℝ]^q V).baseChange ℂ` of `ℂ ⊗[ℝ] ExteriorAlgebra ℝ V` are
orthogonal with respect to `B.sesqExteriorAlgebra.sesqComplexification`. -/
theorem sesqComplexification_sesqExteriorAlgebra_eq_zero_of_mem_baseChange_of_ne
    (B : BilinForm ℝ V) {p q : ℕ} (hpq : p ≠ q) {x y : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V}
    (hx : x ∈ (⋀[ℝ]^p V).baseChange ℂ) (hy : y ∈ (⋀[ℝ]^q V).baseChange ℂ) :
    sesqComplexification B.sesqExteriorAlgebra x y = 0 := by
  rw [Submodule.baseChange_eq_span] at hx hy
  induction hx using Submodule.span_induction with
  | mem _ hu =>
    obtain ⟨u, hu, rfl⟩ := hu
    induction hy using Submodule.span_induction with
    | mem _ hv =>
      obtain ⟨v, hv, rfl⟩ := hv
      simp [B.sesqExteriorAlgebra_eq_zero_of_mem_exteriorPower_of_ne hpq hu hv]
    | zero => simp
    | add _ _ _ _ hv₁ hv₂ => simp [TensorProduct.mk_apply] at hv₁ hv₂ ⊢; simp [hv₁, hv₂]
    | smul c _ _ hv => simp [TensorProduct.mk_apply] at hv ⊢; simp [hv]
  | zero => simp
  | add _ _ _ _ hu₁ hu₂ => simp [hu₁, hu₂]
  | smul c _ _ hu => simp [hu]

/-- **Distinct complexified exterior powers are orthogonal** (on `subtype.baseChange` images): for
`p ≠ q`, `(⋀[ℝ]^p V).subtype.baseChange ℂ x` and `(⋀[ℝ]^q V).subtype.baseChange ℂ y` are
orthogonal with respect to `B.sesqExteriorAlgebra.sesqComplexification`. -/
theorem sesqComplexification_sesqExteriorAlgebra_subtype_baseChange_eq_zero_of_ne
    (B : BilinForm ℝ V) {p q : ℕ} (hpq : p ≠ q)
    (x : ℂ ⊗[ℝ] ⋀[ℝ]^p V) (y : ℂ ⊗[ℝ] ⋀[ℝ]^q V) :
    sesqComplexification B.sesqExteriorAlgebra
        ((⋀[ℝ]^p V).subtype.baseChange ℂ x) ((⋀[ℝ]^q V).subtype.baseChange ℂ y) = 0 := by
  have hmem {k : ℕ} (z : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
      (⋀[ℝ]^k V).subtype.baseChange ℂ z ∈ (⋀[ℝ]^k V).baseChange ℂ := by
    have h : LinearMap.range ((⋀[ℝ]^k V).subtype.baseChange ℂ) = (⋀[ℝ]^k V).baseChange ℂ := by
      rw [← LinearMap.baseChange_range, Submodule.range_subtype]
    exact h ▸ LinearMap.mem_range_self _ z
  exact B.sesqComplexification_sesqExteriorAlgebra_eq_zero_of_mem_baseChange_of_ne hpq
    (hmem x) (hmem y)

/-- **Complexification commutes with exterior Gram forms on the exterior algebra**: under
`ExteriorAlgebra.baseChangeEquiv ℝ V ℂ`, `B.sesqComplexification.sesqExteriorAlgebra` on
`ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)` agrees with `B.sesqExteriorAlgebra.sesqComplexification` on
`ℂ ⊗[ℝ] ExteriorAlgebra ℝ V`. -/
@[simp]
theorem sesqExteriorAlgebra_sesqComplexification_baseChangeEquiv (B : BilinForm ℝ V)
    (x y : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    B.sesqComplexification.sesqExteriorAlgebra
        (ExteriorAlgebra.baseChangeEquiv ℝ V ℂ x) (ExteriorAlgebra.baseChangeEquiv ℝ V ℂ y) =
      sesqComplexification B.sesqExteriorAlgebra x y := by
  let e := (ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).symm.toLinearMap
  have h : ((sesqComplexification B.sesqExteriorAlgebra).comp e).compl₂ e =
      B.sesqComplexification.sesqExteriorAlgebra := by
    rw [LinearMap.eq_sesqExteriorAlgebra_iff]
    refine ⟨fun n u v ↦ ?_, fun hpq u v ↦ ?_⟩
    · simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, e,
        ← TauCeti.exteriorPower.subtype_baseChange_equivBaseChange,
        sesqComplexification_sesqExteriorAlgebra_subtype_baseChange,
        sesqComplexification_sesqExteriorPower_equivBaseChange]
    · simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, e,
        ← TauCeti.exteriorPower.subtype_baseChange_equivBaseChange]
      exact B.sesqComplexification_sesqExteriorAlgebra_subtype_baseChange_eq_zero_of_ne hpq _ _
  simpa [e] using
    (LinearMap.congr_fun₂ h (ExteriorAlgebra.baseChangeEquiv ℝ V ℂ x)
      (ExteriorAlgebra.baseChangeEquiv ℝ V ℂ y)).symm

/-- Inverse form of `sesqExteriorAlgebra_sesqComplexification_baseChangeEquiv`. -/
@[simp]
theorem sesqComplexification_sesqExteriorAlgebra_baseChangeEquiv_symm (B : BilinForm ℝ V)
    (x y : ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)) :
    sesqComplexification B.sesqExteriorAlgebra
        ((ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).symm x)
        ((ExteriorAlgebra.baseChangeEquiv ℝ V ℂ).symm y) =
      B.sesqComplexification.sesqExteriorAlgebra x y := by
  rw [← sesqExteriorAlgebra_sesqComplexification_baseChangeEquiv,
    AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

end LinearMap.BilinForm
