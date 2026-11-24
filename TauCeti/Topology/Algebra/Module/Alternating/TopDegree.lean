/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import Mathlib.LinearAlgebra.Determinant

/-!
# Top-degree continuous alternating forms

Top-degree scalar-valued continuous alternating forms over a commutative ring are determined
by their basis coefficient, which vanishes only for the zero form. Pullback by a continuous
linear endomorphism multiplies that coefficient by its determinant. Pullback along a continuous
linear map `A : E → F` multiplies it by the determinant of `C⁻¹ ∘ A` for any continuous linear
equivalence `C : E ≃ F`, the target coefficient being taken in the transported basis. Above the
top degree, continuous alternating maps on a finite-dimensional space over a division ring vanish.
A top-degree form on a product `V × W` that agrees with a product of top-degree forms on `V` and
`W` on one block basis `((B₁, 0), (0, B₂))` agrees with it on every block family
`((u, 0), (0, w))`.
No compatibility between the topology and the module structure is required for those statements.
-/

public section

namespace ContinuousAlternatingMap

variable {R E ι : Type*} [CommRing R] [TopologicalSpace R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E] [Fintype ι] [DecidableEq ι]

/-- A top-degree alternating form is determined by its scalar coefficient in a basis. -/
theorem apply_eq_det_mul (ω : E [⋀^ι]→L[R] R) (b : Module.Basis ι R E) (v : ι → E) :
    ω v = b.det v * ω b := by
  have h := congrArg (fun f : E [⋀^ι]→ₗ[R] R ↦ f v) (ω.toAlternatingMap.eq_smul_basis_det b)
  simpa only [coe_toAlternatingMap, _root_.smul_apply, smul_eq_mul, mul_comm] using h

omit [Fintype ι] [DecidableEq ι] in
/-- Pullback of a top-degree coefficient multiplies by the determinant. -/
theorem compContinuousLinearMap_apply_basis [Finite ι] (ω : E [⋀^ι]→L[R] R)
    (b : Module.Basis ι R E) (A : E →L[R] E) :
    (ω.compContinuousLinearMap A) b = A.toLinearMap.det * ω b := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rw [compContinuousLinearMap_apply, apply_eq_det_mul ω b]
  simp only [← ContinuousLinearMap.coe_coe A, b.det_comp, b.det_self, mul_one]

omit [Fintype ι] [DecidableEq ι] in
/-- Pullback along a continuous linear map `A : E → F` multiplies the coefficient of a
top-degree form by the determinant of `A` read in `E` through a continuous linear equivalence
`C : E ≃ F`: the coefficient of `A^* ω` in a basis `b` of `E` is `det (C⁻¹ ∘ A)` times the
coefficient of `ω` in the basis `C ∘ b` of `F`. -/
theorem compContinuousLinearMap_apply_basis_map [Finite ι] {F : Type*} [AddCommGroup F]
    [Module R F] [TopologicalSpace F] (ω : F [⋀^ι]→L[R] R) (b : Module.Basis ι R E)
    (A : E →L[R] F) (C : E ≃L[R] F) :
    (ω.compContinuousLinearMap A) b =
      ((C.symm : F →L[R] E) ∘L A).toLinearMap.det * ω (b.map C.toLinearEquiv) := by
  have hA : ω.compContinuousLinearMap A =
      (ω.compContinuousLinearMap (C : E →L[R] F)).compContinuousLinearMap
        ((C.symm : F →L[R] E) ∘L A) := by
    ext v
    simp [Function.comp_def]
  rw [hA, compContinuousLinearMap_apply_basis, compContinuousLinearMap_apply,
    Module.Basis.coe_map, ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.coe_coe]

omit [Fintype ι] [DecidableEq ι] in
/-- A top-degree alternating form vanishes on a basis exactly when it is zero. -/
@[simp]
theorem map_basis_eq_zero_iff [Finite ι] (ω : E [⋀^ι]→L[R] R) (b : Module.Basis ι R E) :
    ω b = 0 ↔ ω = 0 := by
  rw [← coe_toAlternatingMap, AlternatingMap.map_basis_eq_zero_iff,
    ← toAlternatingMap_zero, toAlternatingMap_injective.eq_iff]

omit [Fintype ι] [DecidableEq ι] in
/-- A nonzero top-degree alternating form is nonzero on every basis. -/
theorem map_basis_ne_zero_iff [Finite ι] (ω : E [⋀^ι]→L[R] R) (b : Module.Basis ι R E) :
    ω b ≠ 0 ↔ ω ≠ 0 :=
  not_congr (ω.map_basis_eq_zero_iff b)

section AboveTopDegree

variable {K E F ι : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
  [TopologicalSpace E] [AddCommGroup F] [Module K F] [TopologicalSpace F]

/-- A continuous alternating map in more variables than the dimension of its domain is zero. -/
theorem eq_zero_of_finrank_lt [Module.Finite K E] [Fintype ι] (f : E [⋀^ι]→L[K] F)
    (h : Module.finrank K E < Fintype.card ι) : f = 0 := by
  ext v
  exact f.toAlternatingMap.map_linearDependent v fun hv ↦ hv.fintype_card_le_finrank.not_gt h

end AboveTopDegree

section Prod

variable {V W : Type*} [AddCommGroup V] [Module R V] [TopologicalSpace V] [AddCommGroup W]
  [Module R W] [TopologicalSpace W] {k l K : ℕ}

/-- **Top-degree forms on a product are multiplicative on block families once they are on one
block basis.** Let `Φ`, `Φ₁` and `Φ₂` be top-degree forms on `V × W`, `V` and `W`. If
`Φ((B₁, 0), (0, B₂)) = Φ₁(B₁) · Φ₂(B₂)` for bases `B₁` of `V` and `B₂` of `W`, then
`Φ((u, 0), (0, w)) = Φ₁(u) · Φ₂(w)` for all families `u` in `V` and `w` in `W`: these are the
images of the bases under linear maps `f₁` and `f₂`, and the block family is their image under
`f₁ × f₂`, of determinant `det f₁ · det f₂`. -/
theorem apply_append_eq_mul_of_apply_basis (hK : K = k + l) (Φ : (V × W) [⋀^Fin K]→L[R] R)
    (Φ₁ : V [⋀^Fin k]→L[R] R) (Φ₂ : W [⋀^Fin l]→L[R] R) (B₁ : Module.Basis (Fin k) R V)
    (B₂ : Module.Basis (Fin l) R W) (B : Module.Basis (Fin K) R (V × W))
    (hB : ⇑B = fun r ↦ Fin.append (fun i ↦ (B₁ i, (0 : W))) (fun j ↦ ((0 : V), B₂ j))
      (Fin.cast hK r))
    (h : Φ B = Φ₁ B₁ * Φ₂ B₂) (u : Fin k → V) (w : Fin l → W) :
    Φ (fun r ↦ Fin.append (fun i ↦ (u i, (0 : W))) (fun j ↦ ((0 : V), w j)) (Fin.cast hK r)) =
      Φ₁ u * Φ₂ w := by
  have := Module.Free.of_basis B₁
  have := Module.Free.of_basis B₂
  have := Module.Finite.of_basis B₁
  have := Module.Finite.of_basis B₂
  set f₁ := B₁.constr R u
  set f₂ := B₂.constr R w
  have hu : u = f₁ ∘ B₁ := funext fun i ↦ (B₁.constr_basis R u i).symm
  have hw : w = f₂ ∘ B₂ := funext fun j ↦ (B₂.constr_basis R w j).symm
  have happ : (fun r ↦ Fin.append (fun i ↦ (u i, (0 : W))) (fun j ↦ ((0 : V), w j))
      (Fin.cast hK r)) = (f₁.prodMap f₂) ∘ B := by
    rw [hB]
    funext r
    simp only [Function.comp_apply]
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) (Fin.cast hK r) <;> simp [f₁, f₂]
  rw [happ, apply_eq_det_mul Φ B, h, B.det_comp, B.det_self, LinearMap.det_prodMap, hu, hw,
    apply_eq_det_mul Φ₁ B₁ (f₁ ∘ B₁), B₁.det_comp, B₁.det_self, apply_eq_det_mul Φ₂ B₂ (f₂ ∘ B₂),
    B₂.det_comp, B₂.det_self]
  ring

end Prod

end ContinuousAlternatingMap
