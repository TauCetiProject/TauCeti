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
public import TauCeti.LinearAlgebra.ExteriorPower.KulkarniNomizu

/-!
# Metric properties of the wedge product of linear maps on the exterior square

On finite-dimensional real inner product spaces, the inner product of `(f ∧ g)(a ∧ b)` with
`u ∧ w` is half the Kulkarni–Nomizu expression in the matrix coefficients of `f` and `g`.
Consequently:

* `(f ∧ g)* = f* ∧ g*`, so symmetric endomorphisms `f, g` have a symmetric wedge product `f ∧ g`;
* `tr(f ∧ g) = (tr f · tr g - tr(f ∘ g)) / 2`, and in particular
  `tr(f ∧ id) = ((dim E - 1) / 2) tr f`.

## Main results

* `exteriorPower.inner_wedgeEnd_ιMulti_two`: inner product of `(f ∧ g)(a ∧ b)` against `u ∧ w`.
* `exteriorPower.inner_wedgeEnd_left` and `exteriorPower.adjoint_wedgeEnd`: `(f ∧ g)* = f* ∧ g*`.
* `LinearMap.IsSymmetric.wedgeEnd`: symmetry of `f ∧ g` for symmetric `f` and `g`.
* `exteriorPower.trace_wedgeEnd` and `exteriorPower.trace_wedgeEnd_id_right`: trace formulas on
  `⋀[ℝ]^2 E`.

## References

* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*, Ann. of
  Math. (2) 167 (2008), 1079–1097, §1.
-/

public section

namespace exteriorPower

open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
/-- The inner product of `(f ∧ g)(a ∧ b)` with `u ∧ w` is half the Kulkarni–Nomizu combination of
the inner products `⟪f ·, ·⟫` and `⟪g ·, ·⟫`. -/
theorem inner_wedgeEnd_ιMulti_two (f g : E →ₗ[ℝ] F) (a b : E) (u w : F) :
    ⟪wedgeEnd f g (ιMulti ℝ 2 ![a, b]), ιMulti ℝ 2 ![u, w]⟫ =
      (⟪f a, u⟫ * ⟪g b, w⟫ + ⟪g a, u⟫ * ⟪f b, w⟫ -
        ⟪f a, w⟫ * ⟪g b, u⟫ - ⟪g a, w⟫ * ⟪f b, u⟫) / 2 := by
  rw [wedgeEnd_apply_ιMulti_two, real_inner_smul_left, inner_add_left,
    inner_ιMulti_two, inner_ιMulti_two]
  ring

/-- Moving `wedgeEnd f g` across the bivector inner product replaces `f` and `g` by their
adjoints. -/
theorem inner_wedgeEnd_left (f g : E →ₗ[ℝ] F) (x : ⋀[ℝ]^2 E) (y : ⋀[ℝ]^2 F) :
    ⟪wedgeEnd f g x, y⟫ = ⟪x, wedgeEnd f.adjoint g.adjoint y⟫ := by
  have hbil : (innerₗ (⋀[ℝ]^2 F)).compl₁₂ (wedgeEnd f g) LinearMap.id =
      (innerₗ (⋀[ℝ]^2 E)).compl₂ (wedgeEnd f.adjoint g.adjoint) := by
    refine linearMap_ext (AlternatingMap.ext fun v ↦ linearMap_ext (AlternatingMap.ext fun w ↦ ?_))
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.compl₁₂_apply,
      LinearMap.compl₂_apply, LinearMap.id_apply, innerₗ_apply_apply]
    have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
    have hw : w = ![w 0, w 1] := (FinVec.etaExpand_eq w).symm
    rw [hv, hw, inner_wedgeEnd_ιMulti_two, real_inner_comm _ (ιMulti ℝ 2 _),
      inner_wedgeEnd_ιMulti_two]
    simp only [LinearMap.adjoint_inner_left, real_inner_comm]
    ring
  exact LinearMap.congr_fun₂ hbil x y

/-- The Hilbert–Schmidt adjoint of `f ∧ g` on `⋀[ℝ]^2` is `f* ∧ g*`. -/
@[simp]
theorem adjoint_wedgeEnd (f g : E →ₗ[ℝ] F) :
    (wedgeEnd f g).adjoint = wedgeEnd f.adjoint g.adjoint := by
  apply LinearMap.ext
  intro x
  refine ext_inner_right ℝ fun y ↦ ?_
  rw [LinearMap.adjoint_inner_left, real_inner_comm, inner_wedgeEnd_left, real_inner_comm]

/-- The wedge product of two symmetric endomorphisms of `E` is a symmetric endomorphism of
`⋀[ℝ]^2 E`. -/
theorem _root_.LinearMap.IsSymmetric.wedgeEnd {f g : Module.End ℝ E}
    (hf : f.IsSymmetric) (hg : g.IsSymmetric) :
    (exteriorPower.wedgeEnd f g).IsSymmetric := by
  have hfa : f.adjoint = f := LinearMap.ext fun x ↦ ext_inner_right ℝ fun y ↦ by
    rw [LinearMap.adjoint_inner_left, ← hf x y]
  have hga : g.adjoint = g := LinearMap.ext fun x ↦ ext_inner_right ℝ fun y ↦ by
    rw [LinearMap.adjoint_inner_left, ← hg x y]
  intro x y
  rw [inner_wedgeEnd_left, hfa, hga]

/-- The trace of `f ∧ g` on `⋀[ℝ]^2 E` is `(tr f · tr g - tr(f ∘ g)) / 2`. Neither `f` nor `g`
need be symmetric. -/
theorem trace_wedgeEnd (f g : Module.End ℝ E) :
    LinearMap.trace ℝ (⋀[ℝ]^2 E) (wedgeEnd f g) =
      (LinearMap.trace ℝ E f * LinearMap.trace ℝ E g - LinearMap.trace ℝ E (f ∘ₗ g)) / 2 := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hsum := b.sum_inner_ιMulti_two_eq_two_mul_trace (wedgeEnd f g)
  simp_rw [inner_wedgeEnd_ιMulti_two] at hsum
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

/-- The trace of `f ∧ id` on `⋀[ℝ]^2 E` is `((dim E - 1) / 2) tr f`. -/
theorem trace_wedgeEnd_id_right (f : Module.End ℝ E) :
    LinearMap.trace ℝ (⋀[ℝ]^2 E) (wedgeEnd f LinearMap.id) =
      ((Module.finrank ℝ E : ℝ) - 1) / 2 * LinearMap.trace ℝ E f := by
  rw [trace_wedgeEnd, LinearMap.trace_id, LinearMap.comp_id]
  ring

/-- The trace of `id ∧ f` on `⋀[ℝ]^2 E` is `((dim E - 1) / 2) tr f`. -/
theorem trace_wedgeEnd_id_left (f : Module.End ℝ E) :
    LinearMap.trace ℝ (⋀[ℝ]^2 E) (wedgeEnd LinearMap.id f) =
      ((Module.finrank ℝ E : ℝ) - 1) / 2 * LinearMap.trace ℝ E f := by
  rw [wedgeEnd_comm, trace_wedgeEnd_id_right]

end exteriorPower
