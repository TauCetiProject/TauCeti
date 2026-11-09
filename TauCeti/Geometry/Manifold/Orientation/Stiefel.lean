/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Stiefel
public import TauCeti.Geometry.Manifold.Orientation.TopForm
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# Orientations of the manifold of orthonormal two-frames

Let `E` be a real inner product space of dimension `n = m + 2`. The Stiefel manifold
`TauCeti.stiefel E 2` of orthonormal pairs `(u, v)`, the unit tangent bundle of the unit sphere of
`E`, is the regular level set of the Gram map `w ↦ (⟪w 0, w 0⟫, ⟪w 0, w 1⟫, ⟪w 1, w 1⟫)` in
`Fin 2 → E`, of dimension `2 n - 3 = 2 m + 1`. At `w = (u, v)` the three vectors

`ν₁ = (u, 0)`, `ν₂ = (v, u)`, `ν₃ = (0, v)`

are normal to it: the derivative of the Gram map sends them to twice the three coordinate
functions, and kills the tangent space (`TauCeti.range_mfderiv_coe_stiefel`). So a top form `Ω`
on `Fin 2 → E` that does not vanish contracts with them to a nowhere-vanishing top form
`(t₁, …, t₂ₘ₊₁) ↦ Ω(ν₁, ν₂, ν₃, t₁, …, t₂ₘ₊₁)` on the Stiefel manifold, the analogue for this
codimension-three level set of the contraction of a volume form with the position vector that
orients a sphere (`Orientation.sphereOrientation`). It defines the orientation
`TauCeti.stiefelTwoOrientation Ω` of the Stiefel manifold
(`TauCeti.orientation_eq_orientationAt_stiefelTwoOrientation_iff`). No inner product is needed on
`Fin 2 → E`, which with its sup norm is not an inner product space: the orientation depends only
on the orientation of `Fin 2 → E` that `Ω` determines.

The **frame reflection** `(u, v) ↦ (u, -v)` (`TauCeti.stiefelTwoReflection`) is the restriction
of the linear map `L (a, b) = (a, -b)` of determinant `(-1)ⁿ`. It sends the normals at `(u, v)` to
`ν₁`, `-ν₂` and `ν₃` at `(u, -v)`, so it pulls the top form back to `-(-1)ⁿ = (-1)ⁿ⁺¹` times
itself: it preserves these orientations when `n` is odd and reverses them when `n` is even
(`TauCeti.isOrientationPreservingAt_stiefelTwoReflection`,
`TauCeti.isOrientationReversingAt_stiefelTwoReflection`). This is the sign by which the two
preimages of a point under the rotation map of Barraud–Damian–Humilière–Oancea's
Proposition 6.17 are compared.

## Main declarations

* `TauCeti.stiefelTwoOrientation`: the orientation of `TauCeti.stiefel E 2` by contraction of a
  nonzero top form on `Fin 2 → E` with the normals `(u, 0)`, `(v, u)`, `(0, v)`.
* `TauCeti.orientation_eq_orientationAt_stiefelTwoOrientation_iff`: a tangent basis is positive
  exactly when the contraction is positive on it.
* `TauCeti.isOrientationPreservingAt_stiefelTwoReflection`,
  `TauCeti.isOrientationReversingAt_stiefelTwoReflection`: it preserves the orientation in odd
  dimension and reverses it in even dimension.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 15 (orientations of regular level sets).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2 (Proposition 6.17).
-/

public section

noncomputable section

open Module Set TauCeti.Manifold.Orientation
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {m : ℕ} [Fact (finrank ℝ E = m + 1 + 1)]

/-- The model space of the Stiefel manifold of orthonormal two-frames of `E`. -/
local notation "𝓢" => 𝓘(ℝ, Fin (2 * finrank ℝ E - Nat.choose (2 + 1) 2) → ℝ)

/-- The contraction `w ↦ Ω((w₀, 0), (w₁, w₀), (0, w₁), ·)` of a top form on `Fin 2 → E` with the
three normals of the Stiefel manifold. -/
private def stiefelNormalForm (Ω : (Fin 2 → E) [⋀^Fin (2 * m + 1 + 1 + 1 + 1)]→L[ℝ] ℝ) :
    RoughForm 𝓘(ℝ, Fin 2 → E) (Fin 2 → E) ℝ (2 * m + 1) :=
  fun w ↦ ((Ω.curryLeft ![w 0, 0]).curryLeft ![w 1, w 0]).curryLeft ![0, w 1]

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = m + 1 + 1)] in
private theorem continuous_stiefelNormalForm
    (Ω : (Fin 2 → E) [⋀^Fin (2 * m + 1 + 1 + 1 + 1)]→L[ℝ] ℝ) :
    Continuous fun w : Fin 2 → E ↦
      ((Ω.curryLeft ![w 0, 0]).curryLeft ![w 1, w 0]).curryLeft ![0, w 1] := by
  have h₁ : Continuous fun w : Fin 2 → E ↦ Ω.curryLeft ![w 0, 0] :=
    Ω.curryLeft.continuous.comp (by fun_prop)
  have h₂ : Continuous fun w : Fin 2 → E ↦ (Ω.curryLeft ![w 0, 0]).curryLeft ![w 1, w 0] :=
    ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Fin 2 → E)).continuous.comp
      h₁).clm_apply (by fun_prop)
  exact ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Fin 2 → E)).continuous.comp
    h₂).clm_apply (by fun_prop)

/-- The top form `(t₁, …, t₂ₘ₊₁) ↦ Ω(ν₁, ν₂, ν₃, t₁, …, t₂ₘ₊₁)` on the Stiefel manifold, read in
`Fin 2 → E` through the inclusion. -/
private def stiefelTopForm (Ω : (Fin 2 → E) [⋀^Fin (2 * m + 1 + 1 + 1 + 1)]→L[ℝ] ℝ) :
    RoughForm 𝓢 (stiefel E 2) ℝ (2 * m + 1) :=
  mpullback 𝓢 𝓘(ℝ, Fin 2 → E) ((↑) : stiefel E 2 → Fin 2 → E) (stiefelNormalForm Ω)

omit [Fact (finrank ℝ E = m + 1 + 1)] in
private theorem stiefelTopForm_apply (Ω : (Fin 2 → E) [⋀^Fin (2 * m + 1 + 1 + 1 + 1)]→L[ℝ] ℝ)
    (w : stiefel E 2) (t : Fin (2 * m + 1) → TangentSpace 𝓢 w) :
    stiefelTopForm Ω w t = Ω (Fin.cons ![w.1 0, 0] (Fin.cons ![w.1 1, w.1 0] (Fin.cons ![0, w.1 1]
      fun i ↦ mfderiv 𝓢 𝓘(ℝ, Fin 2 → E) ((↑) : stiefel E 2 → Fin 2 → E) w (t i)))) :=
  mpullback_apply _ _ _ _

omit [Fact (finrank ℝ E = m + 1 + 1)] in
private theorem isSmoothForm_stiefelTopForm
    (Ω : (Fin 2 → E) [⋀^Fin (2 * m + 1 + 1 + 1 + 1)]→L[ℝ] ℝ) :
    IsSmoothForm 𝓢 0 (stiefelTopForm Ω) :=
  (isSmoothForm_modelSpace_iff.2 (contDiff_zero.2 (continuous_stiefelNormalForm Ω))).mpullback
    (contMDiff_coe_stiefel E 2)

/-- Three vectors whose images under a linear map `D` are linearly independent, followed by a
linearly independent family in the kernel of `D`, are linearly independent. It is stated for an
arbitrary length `k`, so that the nested `Fin.cons` indices are not normalized. -/
private theorem linearIndependent_cons_cons_cons_of_map {R M N : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (D : M →ₗ[R] N) {k : ℕ} {v : Fin k → M}
    (hv : LinearIndependent R v) (hDv : ∀ i, D (v i) = 0) {x y z : M}
    (hxyz : LinearIndependent R ![D x, D y, D z]) :
    LinearIndependent R (Fin.cons x (Fin.cons y (Fin.cons z v)) : Fin (k + 1 + 1 + 1) → M) := by
  rw [Fintype.linearIndependent_iff] at hxyz ⊢
  intro g hg
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at hg
  have hD := congrArg D hg
  simp only [map_add, map_smul, map_sum, hDv, smul_zero, Finset.sum_const_zero, add_zero,
    map_zero] at hD
  have h3 := hxyz ![g 0, g (Fin.succ 0), g (Fin.succ (Fin.succ 0))] (by
    simpa [Fin.sum_univ_three, add_assoc] using hD)
  have hg0 : g 0 = 0 := h3 0
  have hg1 : g (Fin.succ 0) = 0 := h3 1
  have hg2 : g (Fin.succ (Fin.succ 0)) = 0 := h3 2
  rw [hg0, hg1, hg2] at hg
  simp only [zero_smul, zero_add] at hg
  have hrest := (Fintype.linearIndependent_iff.1 hv) _ hg
  intro i
  exact Fin.cases hg0 (fun i ↦ Fin.cases hg1 (fun i ↦ Fin.cases hg2 (fun i ↦ hrest i) i) i) i

omit [Fact (finrank ℝ E = m + 1 + 1)] in
/-- **The normals and a tangent frame span `Fin 2 → E`.** At a frame `w = (u, v)`, the normals
`(u, 0)`, `(v, u)`, `(0, v)` followed by the image of a tangent basis of the Stiefel manifold are
linearly independent. The derivative of the Gram map kills the tangent vectors and sends the
normals to twice the coordinate functions at `s(0, 0)`, `s(0, 1)` and `s(1, 1)`. -/
theorem linearIndependent_stiefelTwo_normal_cons (w : stiefel E 2)
    (b : Basis (Fin (2 * m + 1)) ℝ (TangentSpace 𝓢 w)) :
    LinearIndependent ℝ (Fin.cons ![w.1 0, 0] (Fin.cons ![w.1 1, w.1 0] (Fin.cons ![0, w.1 1]
      fun i ↦ mfderiv 𝓢 𝓘(ℝ, Fin 2 → E) ((↑) : stiefel E 2 → Fin 2 → E) w (b i))) :
        Fin (2 * m + 1 + 1 + 1 + 1) → Fin 2 → E) := by
  obtain ⟨hu, hv, huv⟩ := mem_stiefel_two_iff.1 w.2
  set ι := mfderiv 𝓢 𝓘(ℝ, Fin 2 → E) ((↑) : stiefel E 2 → Fin 2 → E) w
  have hker (t : TangentSpace 𝓢 w) : gramSym2Deriv E 2 w.1 (ι t) = 0 := by
    have h : ι t ∈ LinearMap.range ι.toLinearMap := ⟨t, rfl⟩
    rwa [range_mfderiv_coe_stiefel] at h
  have hvu : ⟪w.1 1, w.1 0⟫ = 0 := by rw [real_inner_comm, huv]
  refine linearIndependent_cons_cons_cons_of_map (gramSym2Deriv E 2 w.1).toLinearMap
    ((b.linearIndependent.map' _ (LinearMap.ker_eq_bot.2 (injective_mfderiv_coe_stiefel w))))
    (fun i ↦ hker (b i)) ?_
  -- The images of the normals take the values `2, 0, 0`, `0, 2, 0` and `0, 0, 2` at the pairs
  -- `s(0, 0)`, `s(0, 1)` and `s(1, 1)`.
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h00 := congrFun hc s(0, 0)
  have h01 := congrFun hc s(0, 1)
  have h11 := congrFun hc s(1, 1)
  simp [Fin.sum_univ_three, huv, hvu, hu, hv] at h00 h01 h11
  intro i
  fin_cases i <;> assumption

private theorem stiefelTopForm_ne_zero (Ω : (Fin 2 → E) [⋀^Fin (2 * m + 1 + 1 + 1 + 1)]→L[ℝ] ℝ)
    (hΩ : Ω ≠ 0) (w : stiefel E 2) : stiefelTopForm Ω w ≠ 0 := by
  let b := finBasisOfFinrankEq ℝ (TangentSpace 𝓢 w) (finrank_stiefelTwoModel (m := m))
  have hli := linearIndependent_stiefelTwo_normal_cons w b
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by
    rw [Fintype.card_fin, Module.finrank_pi_fintype, (Fact.out : finrank ℝ E = m + 1 + 1)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring)
  intro h
  have hb := DFunLike.congr_fun h ⇑b
  rw [stiefelTopForm_apply] at hb
  exact (Ω.map_basis_ne_zero_iff B).2 hΩ (by simpa [B] using hb)

/-- The **orientation of the Stiefel manifold** of orthonormal two-frames of `E` determined by a
nonzero top form `Ω` on `Fin 2 → E`: a tangent basis `t` at `(u, v)` is positive exactly when
`Ω((u, 0), (v, u), (0, v), t₁, …, t₂ₘ₊₁) > 0`
(`TauCeti.orientation_eq_orientationAt_stiefelTwoOrientation_iff`). -/
def stiefelTwoOrientation (Ω : (Fin 2 → E) [⋀^Fin (2 * m + 1 + 1 + 1 + 1)]→L[ℝ] ℝ) (hΩ : Ω ≠ 0) :
    Manifold.Orientation 𝓢 (stiefel E 2) (Fin (2 * m + 1)) :=
  ofTopForm finrank_stiefelTwoModel (stiefelTopForm Ω) (isSmoothForm_stiefelTopForm Ω)
    (stiefelTopForm_ne_zero Ω hΩ)

/-- A tangent basis `t` of the Stiefel manifold at `(u, v)` is positive for
`TauCeti.stiefelTwoOrientation Ω` exactly when `Ω((u, 0), (v, u), (0, v), t₁, …, t₂ₘ₊₁)`, read in
`Fin 2 → E` through the derivative of the inclusion, is positive. -/
theorem orientation_eq_orientationAt_stiefelTwoOrientation_iff
    (Ω : (Fin 2 → E) [⋀^Fin (2 * m + 1 + 1 + 1 + 1)]→L[ℝ] ℝ) (hΩ : Ω ≠ 0) {w : stiefel E 2}
    (t : Basis (Fin (2 * m + 1)) ℝ (TangentSpace 𝓢 w)) :
    t.orientation = (stiefelTwoOrientation Ω hΩ).orientationAt w ↔
      0 < Ω (Fin.cons ![w.1 0, 0] (Fin.cons ![w.1 1, w.1 0] (Fin.cons ![0, w.1 1]
        fun i ↦ mfderiv 𝓢 𝓘(ℝ, Fin 2 → E) ((↑) : stiefel E 2 → Fin 2 → E) w (t i)))) := by
  rw [stiefelTwoOrientation, orientation_eq_orientationAt_ofTopForm_iff, stiefelTopForm_apply]

/-! ### The frame reflection -/

/-- The linear map `(a, b) ↦ (a, -b)` of `Fin 2 → E`. -/
private def frameFlip : (Fin 2 → E) →L[ℝ] Fin 2 → E :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0, -ContinuousLinearMap.proj 1]

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = m + 1 + 1)] in
private theorem frameFlip_apply (w : Fin 2 → E) : frameFlip w = ![w 0, -w 1] := by
  ext i : 1
  fin_cases i <;> rfl

omit [Fact (finrank ℝ E = m + 1 + 1)] in
/-- The map `(a, b) ↦ (a, -b)` has determinant `(-1)ⁿ`, where `n = finrank ℝ E`. -/
private theorem det_frameFlip :
    LinearMap.det (frameFlip (E := E) : (Fin 2 → E) →ₗ[ℝ] Fin 2 → E) = (-1) ^ finrank ℝ E := by
  have h : (frameFlip (E := E) : (Fin 2 → E) →ₗ[ℝ] Fin 2 → E) =
      LinearMap.pi fun i ↦ (![LinearMap.id, -LinearMap.id] i : E →ₗ[ℝ] E).comp
        (LinearMap.proj i) := by
    refine LinearMap.ext fun w ↦ funext fun i ↦ ?_
    fin_cases i <;> simp [frameFlip_apply]
  rw [h, LinearMap.det_pi, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.det_id, one_mul]
  rw [← neg_one_smul ℝ (LinearMap.id : E →ₗ[ℝ] E), LinearMap.det_smul, LinearMap.det_id, mul_one]

/-- The derivative of the frame reflection, read in `Fin 2 → E`, is `(a, b) ↦ (a, -b)`. -/
private theorem mfderiv_coe_mfderiv_stiefelTwoReflection (w : stiefel E 2)
    (t : TangentSpace 𝓢 w) :
    mfderiv 𝓢 𝓘(ℝ, Fin 2 → E) ((↑) : stiefel E 2 → Fin 2 → E) (stiefelTwoReflection w)
        (mfderiv 𝓢 𝓢 stiefelTwoReflection w t) =
      frameFlip (mfderiv 𝓢 𝓘(ℝ, Fin 2 → E) ((↑) : stiefel E 2 → Fin 2 → E) w t) := by
  have hι (w' : stiefel E 2) : MDifferentiableAt 𝓢 𝓘(ℝ, Fin 2 → E)
      ((↑) : stiefel E 2 → Fin 2 → E) w' :=
    ((contMDiff_coe_stiefel E 2 (r := 1)) w').mdifferentiableAt one_ne_zero
  have hK : MDifferentiableAt 𝓢 𝓢 (stiefelTwoReflection (E := E)) w :=
    ((contMDiff_stiefelTwoReflection (r := 1)) w).mdifferentiableAt one_ne_zero
  have hcomp : ((↑) : stiefel E 2 → Fin 2 → E) ∘ stiefelTwoReflection =
      frameFlip ∘ ((↑) : stiefel E 2 → Fin 2 → E) := by
    funext w'
    simp [frameFlip_apply]
  rw [← mfderiv_comp_apply w (hι _) hK, hcomp,
    mfderiv_comp_apply w frameFlip.mdifferentiableAt (hι w), ContinuousLinearMap.mfderiv_eq]
  rfl

/-- The frame reflection pulls the top form of `TauCeti.stiefelTwoOrientation Ω` back to
`(-1)ⁿ⁺¹` times itself: the normals `(u, 0)`, `(v, u)`, `(0, v)` at `(u, v)` are carried by
`(a, b) ↦ (a, -b)` to `(u, 0)`, `-(-v, u)`, `(0, -v)`, the normals at `(u, -v)` up to the sign of
the second. -/
private theorem mpullback_stiefelTwoReflection_stiefelTopForm
    (Ω : (Fin 2 → E) [⋀^Fin (2 * m + 1 + 1 + 1 + 1)]→L[ℝ] ℝ) (w : stiefel E 2) :
    mpullback 𝓢 𝓢 stiefelTwoReflection (stiefelTopForm Ω) w =
      (-(-1) ^ finrank ℝ E : ℝ) • stiefelTopForm Ω w := by
  have hF : finrank ℝ (Fin 2 → E) = 2 * m + 1 + 1 + 1 + 1 := by
    rw [Module.finrank_pi_fintype, (Fact.out : finrank ℝ E = m + 1 + 1)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  ext t
  rw [mpullback_apply, stiefelTopForm_apply, ContinuousAlternatingMap.smul_apply,
    stiefelTopForm_apply]
  simp only [mfderiv_coe_mfderiv_stiefelTwoReflection, coe_stiefelTwoReflection]
  -- Write the normals at `(u, -v)` as the images of the normals at `(u, v)`.
  have h₁ : (![w.1 0, 0] : Fin 2 → E) = frameFlip ![w.1 0, 0] := by simp [frameFlip_apply]
  have h₂ : (![-w.1 1, w.1 0] : Fin 2 → E) = -frameFlip ![w.1 1, w.1 0] := by
    simp [frameFlip_apply]
  have h₃ : (![0, -w.1 1] : Fin 2 → E) = frameFlip ![0, w.1 1] := by simp [frameFlip_apply]
  have hcons : ∀ (x y z : Fin 2 → E) (r : Fin (2 * m + 1) → Fin 2 → E),
      Ω (Fin.cons x (Fin.cons (-y) (Fin.cons z r))) = -Ω (Fin.cons x (Fin.cons y (Fin.cons z r))) :=
    fun x y z r ↦ by
      -- Evaluating `Ω` on `Fin.cons` is, by definition, evaluating its iterated `curryLeft`.
      change ((Ω.curryLeft x).curryLeft (-y)).curryLeft z r =
        -((Ω.curryLeft x).curryLeft y).curryLeft z r
      rw [map_neg, ← neg_one_smul ℝ ((Ω.curryLeft x).curryLeft y),
        ContinuousAlternatingMap.curryLeft_smul]
      simp
  have hfam : ∀ (x y z : Fin 2 → E) (r : Fin (2 * m + 1) → TangentSpace 𝓘(ℝ, Fin 2 → E) w.1),
      (Fin.cons (frameFlip x) (Fin.cons (frameFlip y) (Fin.cons (frameFlip z)
        fun i ↦ frameFlip (r i))) : Fin (2 * m + 1 + 1 + 1 + 1) → Fin 2 → E) =
        frameFlip ∘ Fin.cons x (Fin.cons y (Fin.cons z r)) := fun x y z r ↦ by
    funext i
    exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i) i) i
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  conv_lhs => rw [h₁, h₂, h₃]
  have hflip (v : Fin (2 * m + 1 + 1 + 1 + 1) → Fin 2 → E) :
      Ω (frameFlip ∘ v) = (-1) ^ finrank ℝ E * Ω v := by
    have h := Ω.apply_comp_eq_det_mul (finBasisOfFinrankEq ℝ (Fin 2 → E) hF)
      ((frameFlip (E := E) : (Fin 2 → E) →L[ℝ] Fin 2 → E) : (Fin 2 → E) →ₗ[ℝ] Fin 2 → E) v
    rwa [det_frameFlip] at h
  rw [hcons, hfam, hflip, smul_eq_mul]
  ring

/-- **The frame reflection in odd dimension.** When `n = m + 2` is odd, the frame reflection
`(u, v) ↦ (u, -v)` preserves the orientation `TauCeti.stiefelTwoOrientation Ω`. -/
theorem isOrientationPreservingAt_stiefelTwoReflection (hm : Odd m)
    (Ω : (Fin 2 → E) [⋀^Fin (2 * m + 1 + 1 + 1 + 1)]→L[ℝ] ℝ) (hΩ : Ω ≠ 0) (w : stiefel E 2) :
    IsOrientationPreservingAt (stiefelTwoOrientation Ω hΩ) (stiefelTwoOrientation Ω hΩ)
      stiefelTwoReflection w := by
  refine isOrientationPreservingAt_ofTopForm_of_mpullback_eq_smul _ _ _ _ _ _ (c := 1)
    one_pos ?_
  have hc : (-(-1) ^ finrank ℝ E : ℝ) = 1 := by
    rw [(Fact.out : finrank ℝ E = m + 1 + 1), pow_succ, pow_succ, hm.neg_one_pow]
    norm_num
  rw [mpullback_stiefelTwoReflection_stiefelTopForm, hc]

/-- **The frame reflection in even dimension.** When `n = m + 2` is even, the frame reflection
`(u, v) ↦ (u, -v)` reverses the orientation `TauCeti.stiefelTwoOrientation Ω`. -/
theorem isOrientationReversingAt_stiefelTwoReflection (hm : Even m)
    (Ω : (Fin 2 → E) [⋀^Fin (2 * m + 1 + 1 + 1 + 1)]→L[ℝ] ℝ) (hΩ : Ω ≠ 0) (w : stiefel E 2) :
    IsOrientationReversingAt (stiefelTwoOrientation Ω hΩ) (stiefelTwoOrientation Ω hΩ)
      stiefelTwoReflection w := by
  refine isOrientationReversingAt_ofTopForm_of_mpullback_eq_smul _ _ _ _ _ _ (c := -1)
    (by norm_num) ?_
  have hc : (-(-1) ^ finrank ℝ E : ℝ) = -1 := by
    rw [(Fact.out : finrank ℝ E = m + 1 + 1), pow_succ, pow_succ, hm.neg_one_pow]
    norm_num
  rw [mpullback_stiefelTwoReflection_stiefelTopForm, hc]

end TauCeti
