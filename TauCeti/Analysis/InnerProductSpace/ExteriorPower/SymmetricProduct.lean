/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Trace
public import TauCeti.LinearAlgebra.ExteriorPower.SymmetricProduct

/-!
# Metric properties of the symmetric exterior product on the exterior square

On finite-dimensional real inner product spaces, the inner product of `symmMap₂ f g (a ∧ b)` with
`u ∧ w` is half the Kulkarni–Nomizu expression in the matrix coefficients of `f` and `g`.
Consequently:

* `(symmMap₂ f g)* = symmMap₂ f* g*`, so symmetric endomorphisms `f, g` have a symmetric
  exterior product `symmMap₂ f g`;
* `tr(symmMap₂ f g) = (tr f · tr g - tr(f ∘ g)) / 2`, and in particular
  `tr(symmMap₂ f id) = ((dim E - 1) / 2) tr f`.

## Main results

* `exteriorPower.inner_symmMap₂_ιMulti_two`: inner product of `symmMap₂ f g (a ∧ b)` against
  `u ∧ w`.
* `exteriorPower.inner_symmMap₂_left` and `exteriorPower.adjoint_symmMap₂`:
  `(symmMap₂ f g)* = symmMap₂ f* g*`.
* `LinearMap.IsSymmetric.symmMap₂`: symmetry of `symmMap₂ f g` for symmetric `f` and `g`.
* `exteriorPower.trace_symmMap₂`, `exteriorPower.trace_symmMap₂_id_right`, and
  `exteriorPower.trace_symmMap₂_id_left`: trace formulas on `⋀[ℝ]^2 E`.

## References

* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*, Ann. of
  Math. (2) 167 (2008), 1079–1097, §1–2.
-/

public section

namespace exteriorPower

open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
/-- The inner product of `symmMap₂ f g (a ∧ b)` with `u ∧ w` is half the Kulkarni–Nomizu
combination of the inner products `⟪f ·, ·⟫` and `⟪g ·, ·⟫`. -/
theorem inner_symmMap₂_ιMulti_two (f g : E →ₗ[ℝ] F) (a b : E) (u w : F) :
    ⟪symmMap₂ f g (ιMulti ℝ 2 ![a, b]), ιMulti ℝ 2 ![u, w]⟫ =
      (⟪f a, u⟫ * ⟪g b, w⟫ + ⟪g a, u⟫ * ⟪f b, w⟫ -
        ⟪f a, w⟫ * ⟪g b, u⟫ - ⟪g a, w⟫ * ⟪f b, u⟫) / 2 := by
  rw [symmMap₂_apply_ιMulti, real_inner_smul_left, inner_add_left,
    inner_ιMulti_two, inner_ιMulti_two, invOf_eq_inv]
  ring

/-- Moving `symmMap₂ f g` across the bivector inner product replaces `f` and `g` by their
adjoints. -/
theorem inner_symmMap₂_left (f g : E →ₗ[ℝ] F) (x : ⋀[ℝ]^2 E) (y : ⋀[ℝ]^2 F) :
    ⟪symmMap₂ f g x, y⟫ = ⟪x, symmMap₂ f.adjoint g.adjoint y⟫ := by
  have hbil : (innerₗ (⋀[ℝ]^2 F)).compl₁₂ (symmMap₂ f g) LinearMap.id =
      (innerₗ (⋀[ℝ]^2 E)).compl₂ (symmMap₂ f.adjoint g.adjoint) := by
    refine linearMap_ext (AlternatingMap.ext fun v ↦ linearMap_ext (AlternatingMap.ext fun w ↦ ?_))
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.compl₁₂_apply,
      LinearMap.compl₂_apply, LinearMap.id_apply, innerₗ_apply_apply]
    have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
    have hw : w = ![w 0, w 1] := (FinVec.etaExpand_eq w).symm
    rw [hv, hw, inner_symmMap₂_ιMulti_two, real_inner_comm _ (ιMulti ℝ 2 _),
      inner_symmMap₂_ιMulti_two]
    simp only [LinearMap.adjoint_inner_left, real_inner_comm]
    ring
  exact LinearMap.congr_fun₂ hbil x y

/-- The adjoint of `symmMap₂ f g` on `⋀[ℝ]^2` is `symmMap₂ f* g*`. -/
@[simp]
theorem adjoint_symmMap₂ (f g : E →ₗ[ℝ] F) :
    (symmMap₂ f g).adjoint = symmMap₂ f.adjoint g.adjoint := by
  apply LinearMap.ext
  intro x
  refine ext_inner_right ℝ fun y ↦ ?_
  rw [LinearMap.adjoint_inner_left, real_inner_comm, inner_symmMap₂_left, real_inner_comm]

/-- The symmetric exterior product of two symmetric endomorphisms of `E` is a symmetric
endomorphism of `⋀[ℝ]^2 E`. -/
theorem _root_.LinearMap.IsSymmetric.symmMap₂ {f g : Module.End ℝ E}
    (hf : f.IsSymmetric) (hg : g.IsSymmetric) :
    (exteriorPower.symmMap₂ f g).IsSymmetric := fun x y ↦ by
  rw [inner_symmMap₂_left, hf.adjoint_eq, hg.adjoint_eq]

/-- The trace of `symmMap₂ f g` on `⋀[ℝ]^2 E` is `(tr f · tr g - tr(f ∘ g)) / 2`. Neither `f` nor
`g` need be symmetric. -/
theorem trace_symmMap₂ (f g : Module.End ℝ E) :
    LinearMap.trace ℝ (⋀[ℝ]^2 E) (symmMap₂ f g) =
      (LinearMap.trace ℝ E f * LinearMap.trace ℝ E g - LinearMap.trace ℝ E (f ∘ₗ g)) / 2 := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hsum := b.sum_inner_ιMulti_two_eq_two_mul_trace (symmMap₂ f g)
  simp_rw [inner_symmMap₂_ιMulti_two] at hsum
  have hdiag (h : Module.End ℝ E) : ∑ i, ⟪h (b i), b i⟫ = LinearMap.trace ℝ E h := by
    rw [LinearMap.trace_eq_sum_inner h b]
    exact Finset.sum_congr rfl fun i _ ↦ real_inner_comm _ _
  have hoff (h₁ h₂ : Module.End ℝ E) :
      ∑ i, ∑ j, ⟪h₁ (b i), b j⟫ * ⟪h₂ (b j), b i⟫ = LinearMap.trace ℝ E (h₂ ∘ₗ h₁) := by
    have hinner (i : Fin (Module.finrank ℝ E)) :
        ∑ j, ⟪h₁ (b i), b j⟫ * ⟪h₂ (b j), b i⟫ = ⟪(h₂ ∘ₗ h₁) (b i), b i⟫ := by
      have hp := b.sum_inner_mul_inner (h₁ (b i)) (h₂.adjoint (b i))
      calc
        ∑ j, ⟪h₁ (b i), b j⟫ * ⟪h₂ (b j), b i⟫
          = ∑ j, ⟪h₁ (b i), b j⟫ * ⟪b j, h₂.adjoint (b i)⟫ := by
              refine Finset.sum_congr rfl fun j _ ↦ ?_
              rw [LinearMap.adjoint_inner_right]
        _ = ⟪h₁ (b i), h₂.adjoint (b i)⟫ := hp
        _ = ⟪(h₂ ∘ₗ h₁) (b i), b i⟫ := by rw [LinearMap.adjoint_inner_right]; rfl
    rw [Finset.sum_congr rfl fun i _ ↦ hinner i, hdiag]
  have h1 : ∑ i, ∑ j, ⟪f (b i), b i⟫ * ⟪g (b j), b j⟫ =
      LinearMap.trace ℝ E f * LinearMap.trace ℝ E g := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, hdiag]
  have h2 : ∑ i, ∑ j, ⟪g (b i), b i⟫ * ⟪f (b j), b j⟫ =
      LinearMap.trace ℝ E g * LinearMap.trace ℝ E f := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, hdiag]
  have hfg : LinearMap.trace ℝ E (g ∘ₗ f) = LinearMap.trace ℝ E (f ∘ₗ g) :=
    LinearMap.trace_comp_comm' f g
  have h3 := hoff f g
  have h4 := hoff g f
  simp_rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [h1, h2, h3, h4, hfg] at hsum
  linarith

/-- The trace of `symmMap₂ f id` on `⋀[ℝ]^2 E` is `((dim E - 1) / 2) tr f`. -/
theorem trace_symmMap₂_id_right (f : Module.End ℝ E) :
    LinearMap.trace ℝ (⋀[ℝ]^2 E) (symmMap₂ f LinearMap.id) =
      ((Module.finrank ℝ E : ℝ) - 1) / 2 * LinearMap.trace ℝ E f := by
  rw [trace_symmMap₂, LinearMap.trace_id, LinearMap.comp_id]
  ring

/-- The trace of `symmMap₂ id f` on `⋀[ℝ]^2 E` is `((dim E - 1) / 2) tr f`. -/
theorem trace_symmMap₂_id_left (f : Module.End ℝ E) :
    LinearMap.trace ℝ (⋀[ℝ]^2 E) (symmMap₂ LinearMap.id f) =
      ((Module.finrank ℝ E : ℝ) - 1) / 2 * LinearMap.trace ℝ E f := by
  rw [symmMap₂_comm, trace_symmMap₂_id_right]

end exteriorPower
