/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Unipotent
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
public import TauCeti.Geometry.Symplectic.StandardCompatible
public import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# The symplectic shear

The shear `S(q, p) = (q + p, p)` of `V × V` (`TauCeti.symplecticShear`), for a real normed space
`V`, is unipotent. When `V` is an inner product space, it is a linear symplectomorphism of the
standard symplectic form
`ω₀((q, p), (q', p')) = ⟪q, p'⟫ - ⟪p, q'⟫` (`TauCeti.isSymplectomorphism_symplecticShear`). For
`V = ℝ` it is the map `(q, p) ↦ (q + p, p)` of the plane, which preserves the area form
`dq ∧ dp`. It shows that the preserved metric cannot be dropped from the theorem that the fixed
locus of a group of symplectomorphisms preserving a Riemannian metric is a symplectic submanifold:

* its fixed locus is the plane `V × {0}` (`TauCeti.fixedPoints_symplecticShear`), which is a
  Lagrangian subspace (`TauCeti.SymplecticForm.isLagrangian_prod_top_bot`), not a symplectic one;
* accordingly it preserves no Riemannian metric on `V × V` (for `V ≠ 0`): no Riemannian isometry
  of `V × V` is the shear (`TauCeti.RiemannianIsometry.coe_ne_symplecticShear`).

The second statement is read off the differential at the fixed point `0`, which is `S` itself.
Since `(S - 1)² = 0`, the shear is unipotent (`TauCeti.isNilpotent_symplecticShear_sub_one`), and a
unipotent isometry of an inner product is the identity
(`TauCeti.RiemannianIsometry.fixedPointDerivative_eq_one_of_isNilpotent`). In coordinates on
`ℝ²`: an invariant inner product would satisfy `⟪e₁, e₂⟫ = ⟪S e₁, S e₂⟫ = ⟪e₁, e₁ + e₂⟫`, which
forces `‖e₁‖ = 0`. The same pointwise argument rules out every anisotropic bilinear form
(`TauCeti.not_isIsometry_symplecticShear`), so the obstruction does not use smoothness or
completeness of the metric.

## Main definitions

* `TauCeti.symplecticShear`: the shear `(q, p) ↦ (q + p, p)` of `V × V`.

## Main results

* `TauCeti.isSymplectomorphism_symplecticShear`: the shear preserves `ω₀`.
* `TauCeti.fixedPoints_symplecticShear`: its fixed points are the plane `V × {0}`, which is
  Lagrangian for `ω₀` by `TauCeti.SymplecticForm.isLagrangian_prod_top_bot`.
* `TauCeti.not_isIsometry_symplecticShear`: for `V ≠ 0`, the shear preserves no anisotropic
  bilinear form.
* `TauCeti.RiemannianIsometry.coe_ne_symplecticShear`: for `V ≠ 0`, the shear is not a
  Riemannian isometry of `V × V` for any Riemannian metric.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Homework 21, exercise 2 (fixed loci of symplectic actions preserving a metric).
-/

public section

open LinearMap
open scoped InnerProductSpace Manifold

namespace TauCeti

section Shear

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable (V) in
/-- The shear `(q, p) ↦ (q + p, p)` of `V × V`, with inverse `(q, p) ↦ (q - p, p)`: the shear
`(p, q) ↦ (p, q + p)` of `ContinuousLinearEquiv.skewProd` conjugated by swapping the factors. -/
noncomputable def symplecticShear : (V × V) ≃L[ℝ] (V × V) :=
  (ContinuousLinearEquiv.prodComm ℝ V V).trans
    (((ContinuousLinearEquiv.refl ℝ V).skewProd (ContinuousLinearEquiv.refl ℝ V)
      (ContinuousLinearMap.id ℝ V)).trans (ContinuousLinearEquiv.prodComm ℝ V V))

@[simp]
theorem symplecticShear_apply (x : V × V) : symplecticShear V x = (x.1 + x.2, x.2) := (rfl)

@[simp]
theorem symplecticShear_symm_apply (x : V × V) :
    (symplecticShear V).symm x = (x.1 - x.2, x.2) := (rfl)

/-- A point is fixed by the shear exactly when its second component vanishes. -/
theorem symplecticShear_apply_eq_self_iff (x : V × V) : symplecticShear V x = x ↔ x.2 = 0 := by
  rw [symplecticShear_apply, Prod.ext_iff]
  simp

/-- The fixed points of the shear form the plane `V × {0}`, that is `p = 0`. -/
theorem fixedPoints_symplecticShear :
    Function.fixedPoints (symplecticShear V) =
      ((⊤ : Submodule ℝ V).prod (⊥ : Submodule ℝ V) : Set (V × V)) := by
  ext x
  rw [Function.mem_fixedPoints, Function.IsFixedPt, symplecticShear_apply_eq_self_iff]
  simp

/-- The shear is unipotent: `(S - 1)² = 0`. -/
theorem isNilpotent_symplecticShear_sub_one :
    IsNilpotent ((symplecticShear V).toLinearEquiv.toLinearMap - 1) :=
  ⟨2, LinearMap.ext fun x ↦ Prod.ext (by simp [pow_two]) (by simp [pow_two])⟩

/-- For `V ≠ 0`, the shear is not the identity. -/
theorem symplecticShear_toLinearMap_ne_one [Nontrivial V] :
    (symplecticShear V).toLinearEquiv.toLinearMap ≠ 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  intro h
  have := congrArg Prod.fst (LinearMap.congr_fun h (0, v))
  simp [hv] at this

/-- For `V ≠ 0`, the shear preserves no anisotropic bilinear form on `V × V`. -/
theorem not_isIsometry_symplecticShear [Nontrivial V] {B : LinearMap.BilinForm ℝ (V × V)}
    (hB : B.toQuadraticMap.Anisotropic) :
    ¬ BilinForm.IsIsometry B (symplecticShear V).toLinearEquiv.toLinearMap := fun h ↦
  symplecticShear_toLinearMap_ne_one
    (h.eq_one_of_isNilpotent_sub_one hB isNilpotent_symplecticShear_sub_one)

/-- For `V ≠ 0`, the shear of `V × V` is an isometry of no Riemannian metric on `V × V`: its
differential at the fixed point `0` is the shear itself, a unipotent map other than the identity. -/
theorem RiemannianIsometry.coe_ne_symplecticShear [Nontrivial V]
    [Bundle.RiemannianBundle (fun x : V × V ↦ TangentSpace 𝓘(ℝ, V × V) x)]
    (Φ : RiemannianIsometry 𝓘(ℝ, V × V) 𝓘(ℝ, V × V) (V × V) (V × V)) :
    ⇑Φ ≠ symplecticShear V := by
  intro hΦ
  have hD : HasMFDerivAt 𝓘(ℝ, V × V) 𝓘(ℝ, V × V) Φ 0
      (symplecticShear V : (V × V) →L[ℝ] (V × V)) := by
    rw [hΦ]
    exact (symplecticShear V).hasFDerivAt.hasMFDerivAt
  let x₀ : {x // Φ x = x} := ⟨0, by simp [hΦ]⟩
  have hD₀ : fixedPointDerivative 𝓘(ℝ, V × V) Φ x₀ =
      (symplecticShear V).toLinearEquiv.toLinearMap :=
    hD.fixedPointDerivative_eq (x := x₀)
  have h := Φ.fixedPointDerivative_eq_one_of_isNilpotent x₀
    (hD₀ ▸ isNilpotent_symplecticShear_sub_one)
  exact symplecticShear_toLinearMap_ne_one (hD₀ ▸ h)

end Shear

section Symplectic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The shear `(q, p) ↦ (q + p, p)` is a linear symplectomorphism of the standard symplectic form
`ω₀((q, p), (q', p')) = ⟪q, p'⟫ - ⟪p, q'⟫`. -/
theorem isSymplectomorphism_symplecticShear :
    SymplecticForm.IsSymplectomorphism stdSymplecticForm stdSymplecticForm
      (symplecticShear V).toLinearEquiv := by
  rw [SymplecticForm.isSymplectomorphism_iff]
  intro x y
  simp only [ContinuousLinearEquiv.coe_toLinearEquiv, symplecticShear_apply,
    stdSymplecticForm_apply, inner_add_left, inner_add_right]
  ring

end Symplectic

end TauCeti
