/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Analysis.Complex.Wirtinger.Weak
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Floer
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic

/-!
# The weak Cauchy–Riemann equation: comparisons

This file compares the planar weak equation `TauCeti.IsWeakCauchyRiemannOn` of
`TauCeti.Analysis.Complex.CauchyRiemann.Weak` with three existing notions.

* `TauCeti.isWeakCauchyRiemannOn_iff_isPseudoholomorphicOn`: for a smooth almost complex
  structure `J` on a finite-dimensional real normed space `V`, the standard structure `i` on the
  domain `ℂ`, and `u` of class `C¹` on an open set, the homogeneous weak equation with the field
  `J(u)` is Tau Ceti's `IsPseudoholomorphicOn`. Testing on `∂ₛ` suffices because the two
  coordinate vectors are related by `i`; `TauCeti.forall_map_I_mul_eq_iff` is the linear algebra.
* `TauCeti.IsWeakCauchyRiemannOn.hasWeakConjWirtingerDerivOn`: for the constant structure `i` on
  a complex space, a weak solution has weak conjugate Wirtinger derivative `η(z, u)/2`; in
  particular the homogeneous equation is `\bar∂u = 0` weakly.
* `TauCeti.isWeakCauchyRiemannOn_floer_iff`: Floer's equation
  `∂ₛu + J(u)(∂ₜu - X(u)) = 0` is the inhomogeneous equation whose term is twice the value on
  `∂ₛ` of the normalized Floer forcing term `TauCeti.InhomogeneousTerm.floer`, namely `J X`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Sections 2.1 and 8.1.
-/

public noncomputable section

open Complex MeasureTheory TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {p : ENNReal} {Ω : Opens ℂ}
  {u : ℂ → V}

/-- A real-linear map `L : ℂ → V` intertwines multiplication by `i` with a complex structure `A`
exactly when `L 1 + A (L i) = 0`: the value on `∂ₜ` is determined by the value on `∂ₛ`. -/
theorem forall_map_I_mul_eq_iff {L : ℂ →L[ℝ] V} {A : V →L[ℝ] V} (hA : ∀ v, A (A v) = -v) :
    (∀ w, L (I * w) = A (L w)) ↔ L 1 + A (L I) = 0 := by
  have hdecomp : ∀ w : ℂ, L w = w.re • L 1 + w.im • L I := fun w => by
    have hw : w = w.re • (1 : ℂ) + w.im • I := by simp
    conv_lhs => rw [hw]
    rw [map_add, map_smul, map_smul]
  constructor
  · intro h
    have h1 := h 1
    rw [mul_one] at h1
    rw [h1, hA, add_neg_cancel]
  · intro h w
    have hI : L I = A (L 1) := by
      have h' := congrArg A h
      rw [map_add, hA, map_zero] at h'
      exact (add_neg_eq_zero.1 h').symm
    rw [hdecomp, hdecomp w, map_add, map_smul, map_smul, hI, hA]
    simp only [mul_re, I_re, I_im, zero_mul, one_mul, zero_sub, mul_im]
    module

section Pseudoholomorphic

variable [FiniteDimensional ℝ V]

/-- **Comparison with `IsPseudoholomorphicOn`.** For a smooth almost complex structure `J` on a
finite-dimensional space `V`, the standard structure on `ℂ`, and `u` of class `C¹` on an open set
`Ω`, the homogeneous weak equation for the field `J(u)`, for any exponent, is pseudoholomorphy of
`u` on `Ω`. -/
theorem isWeakCauchyRiemannOn_iff_isPseudoholomorphicOn
    (J : SmoothAlmostComplexStructure 𝓘(ℝ, V) V) (hu : ContDiffOn ℝ 1 u Ω) :
    IsWeakCauchyRiemannOn p Ω (fun _ x => J.toEndomorphism x) (fun _ _ => 0) u ↔
      IsPseudoholomorphicOn (AlmostComplexStructure.ofComplexModule ℂ).constSmooth J u Ω := by
  rw [isWeakCauchyRiemannOn_iff_of_contDiffOn hu
    (J.contDiff_toEndomorphism.continuous.comp_continuousOn hu.continuousOn) continuousOn_const,
    isPseudoholomorphicOn_iff]
  refine forall₂_congr fun z hz => ?_
  have hdiff : DifferentiableAt ℝ u z :=
    (hu.differentiableOn one_ne_zero).differentiableAt (Ω.isOpen.mem_nhds hz)
  have hnhds : (Ω : Set ℂ) ∈ nhds z := Ω.isOpen.mem_nhds hz
  have hj : ∀ w : ℂ, (AlmostComplexStructure.ofComplexModule ℂ).constSmooth z w = I * w :=
    fun w => (AlmostComplexStructure.constSmooth_apply _ z w).trans (by simp; rfl)
  refine (forall_map_I_mul_eq_iff (L := fderiv ℝ u z)
    (A := (J.toEndomorphism (u z) : V →L[ℝ] V)) (J.apply_apply (u z))).symm.trans ?_
  constructor
  · intro h
    refine IsPseudoholomorphicAt.isPseudoholomorphicWithinAt
      ((isPseudoholomorphicAt_iff_isJHolomorphicAt _ _ _ _).2
        ((isJHolomorphicAt_iff _ _ _ _).2 ⟨fderiv ℝ u z, hdiff.hasFDerivAt, ?_⟩))
    exact (SmoothAlmostComplexStructure.isComplexLinearMap_almostComplexStructureAt_model_iff
      _ _ _ _ _).2 fun w => (congrArg (fderiv ℝ u z) (hj w)).trans (h w)
  · intro h
    obtain ⟨f', hf', hlin⟩ := (isJHolomorphicAt_iff _ _ _ _).1
      ((isPseudoholomorphicAt_iff_isJHolomorphicAt _ _ _ _).1
        (h.isPseudoholomorphicAt_of_mem_nhds hnhds))
    rw [hf'.fderiv]
    intro w
    exact (congrArg f' (hj w)).symm.trans
      ((SmoothAlmostComplexStructure.isComplexLinearMap_almostComplexStructureAt_model_iff
        _ _ _ _ _).1 hlin w)

end Pseudoholomorphic

section Wirtinger

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {η : ℂ → F → F} {w : ℂ → F}

/-- **The constant structure `i`.** For multiplication by `i` on a complex space, a weak solution
of the equation with inhomogeneous term `η` has weak conjugate Wirtinger derivative
`η(z, w(z))/2`, the normalization `\bar∂ = (∂ₛ + i ∂ₜ)/2`. -/
theorem IsWeakCauchyRiemannOn.hasWeakConjWirtingerDerivOn
    (h : IsWeakCauchyRiemannOn p Ω (fun _ _ => I • ContinuousLinearMap.id ℝ F) η w) :
    HasWeakConjWirtingerDerivOn volume Ω w (fun z => (2 : ℂ)⁻¹ • η z (w z)) := by
  obtain ⟨-, -, D, hD, -, hae⟩ := isWeakCauchyRiemannOn_iff.1 h
  refine hD.hasWeakConjWirtingerDerivOn.congr_ae_deriv ?_
  filter_upwards [hae] with z hz
  rw [← hz]
  simp

/-- For the constant structure `i`, the homogeneous weak equation gives `\bar∂w = 0` weakly. -/
theorem IsWeakCauchyRiemannOn.hasWeakConjWirtingerDerivOn_zero
    (h : IsWeakCauchyRiemannOn p Ω (fun _ _ => I • ContinuousLinearMap.id ℝ F) (fun _ _ => 0) w) :
    HasWeakConjWirtingerDerivOn volume Ω w 0 := by
  have h' := h.hasWeakConjWirtingerDerivOn
  simp only [smul_zero] at h'
  exact h'

end Wirtinger

section Floer

variable {n : ℕ∞}
  (J : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, V) V 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) n)
  (X : (ℝ × ℝ) × V → V) (hX : ContDiff ℝ n X)

/-- **Floer's equation.** With the planar field of a domain-dependent structure `J` on the strip
coordinates `(s, t)`, the inhomogeneous equation whose term is twice the value on `∂ₛ` of the
normalized Floer forcing term is Floer's equation `∂ₛu + J(u)(∂ₜu - X(u)) = 0`. The term is
`2 · ½ J X = J X`. -/
theorem isWeakCauchyRiemannOn_floer_iff :
    IsWeakCauchyRiemannOn p Ω
        (fun z x => show V →L[ℝ] V from J.toEndomorphism ((z.re, z.im), x))
        (fun z x => (2 : ℝ) • (InhomogeneousTerm.floer J X hX).val.tangentHom
          ((z.re, z.im), x) (1, 0)) u ↔
      ContinuousOn u Ω ∧ MemLpLoc p Ω u ∧ ∃ D : ℂ → ℂ →L[ℝ] V,
        HasWeakFDerivOn volume Ω u D ∧ MemLpLoc p Ω D ∧
          ∀ᵐ z ∂volume.restrict (Ω : Set ℂ), D z 1 +
            (show V →L[ℝ] V from J.toEndomorphism ((z.re, z.im), u z))
              (D z I - X ((z.re, z.im), u z)) = 0 := by
  refine isWeakCauchyRiemannOn_iff.trans ?_
  refine and_congr_right' (and_congr_right' (exists_congr fun D =>
    and_congr_right' (and_congr_right' (Filter.eventually_congr
      (Filter.Eventually.of_forall fun z => ?_)))))
  have key : ∀ (A : V →L[ℝ] V) (a b x : V),
      a + A b = (2 : ℝ) • (2⁻¹ : ℝ) • A x ↔ a + A (b - x) = 0 := fun A a b x => by
    rw [smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul, map_sub, ← add_sub_assoc, sub_eq_zero]
  rw [InhomogeneousTerm.floer_apply_real]
  exact key _ _ _ _

end Floer

end TauCeti
