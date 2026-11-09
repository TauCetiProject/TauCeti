/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Map
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Prod

/-!
# The boundary Maslov index on the disc

Let `E` be a finite-dimensional complex normed space. A bundle pair `(E, F)` over the closed unit
disc `D` is a complex vector bundle over `D` together with a totally real subbundle `F` of its
restriction to the boundary circle. Every complex bundle over `D` is trivial, and in a
trivialization `D × E` the subbundle `F` is a loop `Λ` of maximal totally real subspaces of `E`
(`TauCeti.TotallyRealLoop`), parametrized by `t ↦ e^{2πit}`. The boundary Maslov index `μ(E, F)`
is the Maslov index `μ(Λ)` of that loop (McDuff--Salamon, Theorem C.3.6). This file proves the
properties that make this a well-defined invariant with the expected axioms on the disc.

* **Independence of the trivialization.** Two trivializations differ by a continuous map
  `B : D → GL(E)`, and the loop read in the second trivialization is `t ↦ B (e^{2πit}) (Λ t)`. Its
  Maslov index is `μ(Λ)` (`TauCeti.TotallyRealLoop.maslovIndex_map_of_continuousOn_closedBall`):
  by the product formula `μ(B Λ) = μ(Λ) + 2 deg (det B)` (`TauCeti.TotallyRealLoop.maslovIndex_map`)
  it suffices that the loop of normalized determinants of `B` along the boundary has degree zero,
  and it is null-homotopic through the loops `t ↦ det B (s e^{2πit})`, `s ∈ [0, 1]`. The general
  statement behind it is that the Maslov index of `B Λ` only depends on the free homotopy class of
  the loop `B` of automorphisms (`TauCeti.TotallyRealLoop.maslovIndex_map_eq_of_homotopy`).
* **Normalization.** On `E = ℂ` with the real line `ℝ ⊆ ℂ`
  (`TauCeti.isMaximalTotallyReal_span_one`), the loop `θ ↦ e^{ikθ/2} ℝ`, `θ = 2πt`, is the `k`-fold
  half-turn `TauCeti.TotallyRealLoop.rotationZPow` and has Maslov index `k`; in rank `n` the
  `k`-fold half-turn has index `k n` (`TauCeti.TotallyRealLoop.maslovIndex_rotationZPow`).
* **Orientation.** Reversing the orientation of the boundary circle reverses the loop
  (`TauCeti.TotallyRealLoop.symm`) and negates the index
  (`TauCeti.TotallyRealLoop.maslovIndex_symm`), so `e^{-ikθ/2} ℝ` has index `-k`.
* **Additivity** under direct sums is `TauCeti.TotallyRealLoop.maslovIndex_prod`, and
  **naturality** under a constant change of frame is
  `TauCeti.TotallyRealLoop.maslovIndex_map_const`.

The definition of `μ(E, F)` for bundle pairs over general compact surfaces with boundary, as the
first Chern number of the doubled bundle, and its loop formula as a sum over boundary circles are
not treated here.

## Main declarations

* `TauCeti.TotallyRealLoop.maslovIndex_map_eq_of_homotopy`: moving a loop by homotopic loops of
  automorphisms gives loops with the same Maslov index.
* `TauCeti.TotallyRealLoop.maslovIndex_map_of_continuousOn_closedBall`: moving a loop by the
  boundary values of a continuous map from the closed disc to the automorphisms preserves the
  Maslov index.
* `TauCeti.isMaximalTotallyReal_span_one`: the real line `ℝ ⊆ ℂ` is maximal totally real.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.3, Theorems C.3.5 and C.3.6 (the boundary
  Maslov index of a bundle pair, its axioms, and its computation in a trivialization).
-/

public section

open Metric Module Real
open scoped unitInterval

namespace TauCeti

/-- The real line `ℝ ⊆ ℂ`, the real span of `1`, is a maximal totally real subspace of `ℂ`: every
complex number is uniquely `a + i b` with `a, b` real. -/
theorem isMaximalTotallyReal_span_one :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ ℂ Complex.I).restrictScalars ℝ)
      (Submodule.span ℝ {(1 : ℂ)}) := by
  have hmap : (Submodule.span ℝ {(1 : ℂ)}).map
      ((LinearMap.lsmul ℂ ℂ Complex.I).restrictScalars ℝ) = Submodule.span ℝ {Complex.I} := by
    rw [Submodule.map_span, Set.image_singleton]
    simp
  rw [isMaximalTotallyReal_iff, hmap]
  constructor
  · rw [Submodule.disjoint_def]
    intro z hz hz'
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hz'
    have := congrArg Complex.re hb
    simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self] at this
    simp [← this]
  · rw [codisjoint_iff, eq_top_iff]
    intro z _
    refine Submodule.mem_sup.2 ⟨z.re • 1,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
      z.im • Complex.I, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    apply Complex.ext <;> simp

namespace TotallyRealLoop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (Λ : TotallyRealLoop E)

/-- The normalized determinant `det A / ‖det A‖` of a complex-linear automorphism, a point of the
circle. -/
private noncomputable def normalizedDet (A : E ≃L[ℂ] E) : Circle :=
  ⟨LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E) / ‖LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E)‖,
    mem_sphere_zero_iff_norm.2 (by simp [A.toLinearEquiv.isUnit_det'.ne_zero])⟩

omit [FiniteDimensional ℂ E] in
private theorem det_eq_norm_mul_normalizedDet (A : E ≃L[ℂ] E) :
    LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E) =
      ‖LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E)‖ * (normalizedDet A : ℂ) := by
  have hd : LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E) ≠ 0 := A.toLinearEquiv.isUnit_det'.ne_zero
  rw [normalizedDet, mul_div_cancel₀ _ (by simpa using hd)]

omit [FiniteDimensional ℂ E] in
private theorem continuous_normalizedDet {X : Type*} [TopologicalSpace X] {A : X → E ≃L[ℂ] E}
    (hA : Continuous fun x => (A x : E →L[ℂ] E)) : Continuous fun x => normalizedDet (A x) := by
  have hd : Continuous fun x => LinearMap.det ((A x).toLinearEquiv : E →ₗ[ℂ] E) :=
    ContinuousLinearMap.continuous_det.comp hA
  refine Continuous.subtype_mk (hd.div (Complex.continuous_ofReal.comp hd.norm) fun x => ?_) _
  simpa using (A x).toLinearEquiv.isUnit_det'.ne_zero

/-- **Homotopy invariance in the frame.** If `B` is a free homotopy of loops of complex-linear
automorphisms, `B (s, 0) = B (s, 1)` for every `s`, then moving a loop of maximal totally real
subspaces by `B (0, ·)` or by `B (1, ·)` gives loops with the same Maslov index. -/
theorem maslovIndex_map_eq_of_homotopy (B : I × I → E ≃L[ℂ] E)
    (hB : Continuous fun p => (B p : E →L[ℂ] E)) (hB01 : ∀ s, B (s, 0) = B (s, 1)) :
    (Λ.map (fun t => B (0, t)) (hB.comp (Continuous.prodMk_right 0)) (hB01 0)).maslovIndex =
      (Λ.map (fun t => B (1, t)) (hB.comp (Continuous.prodMk_right 1)) (hB01 1)).maslovIndex := by
  -- The free homotopy of loops of normalized determinants.
  let F : C(I × I, Circle) := ⟨fun p => normalizedDet (B p), continuous_normalizedDet hB⟩
  let γ (s : I) : Path (F (s, 0)) (F (s, 0)) :=
    { toFun := fun t => F (s, t)
      continuous_toFun := by fun_prop
      source' := rfl
      target' := by simp only [F, ContinuousMap.coe_mk, hB01 s] }
  rw [Λ.maslovIndex_map _ _ _ (γ 0) fun t => det_eq_norm_mul_normalizedDet _,
    Λ.maslovIndex_map _ _ _ (γ 1) fun t => det_eq_norm_mul_normalizedDet _,
    Circle.degree_eq_of_homotopy (γ 0) (γ 1) F (fun _ => rfl) (fun _ => rfl)
      fun s => (γ s).target'.symm]

/-- **Independence of the trivialization on the disc.** Let `B` be a continuous map from the closed
unit disc to the complex-linear automorphisms of `E`, and `b t = B (e^{2πit})` its loop of
boundary values. Moving a loop of maximal totally real subspaces by `b` does not change its Maslov
index: the loop of determinants of `b` extends over the disc, so it has degree zero. -/
theorem maslovIndex_map_of_continuousOn_closedBall (B : ℂ → E ≃L[ℂ] E)
    (hB : ContinuousOn (fun z => (B z : E →L[ℂ] E)) (closedBall 0 1))
    (b : I → E ≃L[ℂ] E) (hb : Continuous fun t => (b t : E →L[ℂ] E)) (hb01 : b 0 = b 1)
    (hbB : ∀ t, b t = B (Circle.expLoop t)) :
    (Λ.map b hb hb01).maslovIndex = Λ.maslovIndex := by
  -- Contract the boundary circle to the centre through the circles of radius `s`.
  let H (p : I × I) : E ≃L[ℂ] E := B ((p.1 : ℝ) * (Circle.expLoop p.2 : ℂ))
  have hmem (p : I × I) : ((p.1 : ℝ) * (Circle.expLoop p.2 : ℂ) : ℂ) ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg p.1.2.1]
    exact p.1.2.2
  have hH : Continuous fun p => (H p : E →L[ℂ] E) :=
    hB.comp_continuous (by fun_prop) hmem
  have hH01 (s : I) : H (s, 0) = H (s, 1) := by
    simp only [H, Circle.expLoop.source, Circle.expLoop.target]
  have h₀ : Λ.map (fun t => H (0, t)) (hH.comp (Continuous.prodMk_right 0)) (hH01 0) =
      Λ.map (fun _ => B 0) continuous_const rfl :=
    ext fun t => by simp [H]
  have h₁ : Λ.map (fun t => H (1, t)) (hH.comp (Continuous.prodMk_right 1)) (hH01 1) =
      Λ.map b hb hb01 :=
    ext fun t => by simp [H, hbB]
  rw [← h₁, ← Λ.maslovIndex_map_eq_of_homotopy H hH hH01, h₀, maslovIndex_map_const]

/-! ### Checks -/

/-- The convention witness: the half-turn `θ ↦ e^{iθ/2} ℝ` of the real line in `ℂ` has Maslov
index `1`, not `1 / 2`. -/
example : (rotation isMaximalTotallyReal_span_one).maslovIndex = 1 := by
  simp

/-- The normalization `μ(ℂ, e^{ikθ/2} ℝ) = k` on the disc, for every integer `k`. -/
example (k : ℤ) : (rotationZPow isMaximalTotallyReal_span_one k).maslovIndex = k := by
  simp

/-- Orientation: traversed backwards, the loop `e^{ikθ/2} ℝ` has Maslov index `-k`. -/
example (k : ℤ) : (rotationZPow isMaximalTotallyReal_span_one k).symm.maslovIndex = -k := by
  simp

/-- Additivity: `(ℂ², ℝ ⊕ e^{iθ} ℝ)` has Maslov index `0 + 2 = 2`. -/
example :
    ((const isMaximalTotallyReal_span_one).prod
      (rotationZPow isMaximalTotallyReal_span_one 2)).maslovIndex = 2 := by
  simp

/-- The extension hypothesis of `maslovIndex_map_of_continuousOn_closedBall` cannot be dropped:
multiplication by `z` on the boundary circle, which does not extend over the disc as a family of
automorphisms since `z` vanishes at the centre, adds `2` to the Maslov index of `e^{ikθ/2} ℝ`. -/
example (k : ℤ) :
    ((rotationZPow isMaximalTotallyReal_span_one k).map
      (fun t => ContinuousLinearEquiv.smulLeft
        (Units.mk0 (Circle.expLoop t : ℂ) (Circle.coe_ne_zero _)))
      (by
        have h (t : I) : ((ContinuousLinearEquiv.smulLeft
            (Units.mk0 (Circle.expLoop t : ℂ) (Circle.coe_ne_zero _)) : ℂ ≃L[ℂ] ℂ) : ℂ →L[ℂ] ℂ) =
            (Circle.expLoop t : ℂ) • ContinuousLinearMap.id ℂ ℂ := by
          ext
          simp
        simp_rw [h]
        fun_prop)
      (by simp)).maslovIndex = k + 2 := by
  rw [maslovIndex_map _ _ _ _ (Circle.expLoop) fun t => ?_, Circle.degree_expLoop]
  · simp
  · simp [Complex.norm_exp]

end TotallyRealLoop

end TauCeti
