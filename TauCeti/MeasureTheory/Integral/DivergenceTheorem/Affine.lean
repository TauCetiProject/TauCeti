/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Topology.Algebra.Module.Determinant

/-!
# The divergence theorem on affine parallelepipeds

Mathlib's `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'` integrates the
divergence of a family of fields `F i : ℝⁿ⁺¹ → E` over an axis-aligned box `[a, b]` and returns
the signed sum of the face integrals. This file names that boundary sum, `TauCeti.boxBoundarySum`,
and transports the theorem to the parallelepiped `A([0, 1]ⁿ⁺¹)` cut out by an affine map
`A u = p + L u`.

The transport is the *Piola transform*. For a linear map `L` of `ℝⁿ` with matrix `M` and a field
`F`, the Piola transform along `A` is the field on the parameter cube with components

`H j u = ∑ i, (adjugate M) j i • F i (p + L u)`,

that is `H = det L • L⁻¹ (F ∘ A)` when `L` is invertible. Its divergence is the pulled back
divergence of `F` times the signed determinant (Piola's identity):

`∑ j, ∂ⱼ H j u = det L • ∑ i, ∂ᵢ F i (p + L u)`.

For an affine map only the first derivative of `A` enters, so the identity reduces to
`M * adjugate M = det M • 1` and holds wherever `F` is differentiable at `A u`, with no condition
on `L`. Applying the box divergence theorem to `H` on `[0, 1]ⁿ⁺¹` gives the divergence theorem
for the parallelepiped, with boundary term the *affine flux boundary*
`TauCeti.affineFluxBoundary L p F = boxBoundarySum 0 1 (H)`, under the same pointwise hypotheses
as Mathlib's box theorem: continuity on the closed parallelepiped and differentiability off a
countable set in its interior. No continuity of the derivative is required. In particular the
flux of a field whose divergence vanishes in the interior is zero.

## Main declarations

* `TauCeti.boxBoundarySum a b F`: the signed sum of the face integrals of the fields `F i` over
  the box `[a, b]`, front faces minus back faces.
* `TauCeti.integral_divergence_eq_boxBoundarySum`: the divergence theorem on a box in this form.
* `TauCeti.affinePiolaTransform L p F`: the Piola transform of `F` along `u ↦ p + L u`.
* `TauCeti.affinePiolaTransform_eq_det_smul`: for invertible `L` it is `det L • L⁻¹ (F ∘ A)`.
* `TauCeti.sum_fderiv_affinePiolaTransform`: Piola's identity for the divergence.
* `TauCeti.affineFluxBoundary L p F`: the boundary flux of `F` through `A([0, 1]ⁿ⁺¹)`.
* `TauCeti.det_smul_integral_divergence_eq_affineFluxBoundary`: the divergence theorem on an
  affine parallelepiped.
* `TauCeti.affineFluxBoundary_eq_zero`: a field with vanishing divergence in the interior has
  zero affine boundary flux.

## References

* P. G. Ciarlet, *Mathematical Elasticity, Vol. I: Three-Dimensional Elasticity*, North-Holland
  (1988), §1.7, Theorem 1.7-1, for the Piola transform and Piola's identity.
-/

public section

noncomputable section

open Set MeasureTheory

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-! ### The boundary sum of a box -/

/-- The signed boundary sum of a family of fields `F i : ℝⁿ⁺¹ → E` over the box `[a, b]`: for
each direction `i`, the integral of `F i` over the front face `x i = b i` minus its integral over
the back face `x i = a i`. Each face is parametrized by the remaining coordinates, which range
over `[a ∘ i.succAbove, b ∘ i.succAbove]`, and the point of the face is
`i.insertNth (b i) x` or `i.insertNth (a i) x`. This is the right-hand side of the divergence
theorem `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'`. -/
def boxBoundarySum (a b : Fin (n + 1) → ℝ) (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) : E :=
  ∑ i : Fin (n + 1),
    ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (i.insertNth (b i) x)) -
      ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (i.insertNth (a i) x))

theorem boxBoundarySum_def (a b : Fin (n + 1) → ℝ) (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) :
    boxBoundarySum a b F = ∑ i : Fin (n + 1),
      ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (i.insertNth (b i) x)) -
        ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (i.insertNth (a i) x)) :=
  (rfl)

/-- **Divergence theorem** on a box, with boundary term `TauCeti.boxBoundarySum`: if each `F i`
is continuous on `[a, b]` and has derivative `F' i x` at every point of the open box off a
countable set, and the divergence `∑ i, F' i x (Pi.single i 1)` is integrable on `[a, b]`, then
its integral is the boundary sum. -/
theorem integral_divergence_eq_boxBoundarySum {a b : Fin (n + 1) → ℝ} (hle : a ≤ b)
    {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    {F' : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] E}
    {s : Set (Fin (n + 1) → ℝ)} (hs : s.Countable) (hc : ∀ i, ContinuousOn (F i) (Icc a b))
    (hd : ∀ x ∈ (univ.pi fun i ↦ Ioo (a i) (b i)) \ s, ∀ i, HasFDerivAt (F i) (F' i x) x)
    (hi : IntegrableOn (fun x ↦ ∑ i, F' i x (Pi.single i 1)) (Icc a b)) :
    ∫ x in Icc a b, ∑ i, F' i x (Pi.single i 1) = boxBoundarySum a b F :=
  integral_divergence_of_hasFDerivAt_off_countable' a b hle F F' s hs hc hd hi

/-! ### The affine Piola transform -/

/-- The *Piola transform* of a family of fields `F i : ℝⁿ → E` along the affine map
`u ↦ p + L u`: the family `u ↦ ∑ i, (adjugate M) j i • F i (p + L u)`, where `M` is the matrix
of `L`. For invertible `L` this is `det L • L⁻¹ (F (p + L u))`, see
`TauCeti.affinePiolaTransform_eq_det_smul`. Its divergence is `det L` times the divergence of `F`
at `p + L u`, see `TauCeti.sum_fderiv_affinePiolaTransform`. -/
def affinePiolaTransform (L : (Fin n → ℝ) →L[ℝ] Fin n → ℝ) (p : Fin n → ℝ)
    (F : Fin n → (Fin n → ℝ) → E) : Fin n → (Fin n → ℝ) → E :=
  fun j u ↦ ∑ i, (LinearMap.toMatrix' (L : (Fin n → ℝ) →ₗ[ℝ] Fin n → ℝ)).adjugate j i •
    F i (p + L u)

theorem affinePiolaTransform_apply (L : (Fin n → ℝ) →L[ℝ] Fin n → ℝ) (p : Fin n → ℝ)
    (F : Fin n → (Fin n → ℝ) → E) (j : Fin n) (u : Fin n → ℝ) :
    affinePiolaTransform L p F j u =
      ∑ i, (LinearMap.toMatrix' (L : (Fin n → ℝ) →ₗ[ℝ] Fin n → ℝ)).adjugate j i •
        F i (p + L u) :=
  (rfl)

/-- For an invertible `L`, the Piola transform is `det L • L⁻¹ (F ∘ A)`: its `j`-th component is
`det L • ∑ i, (L⁻¹)ⱼᵢ • F i (p + L u)`, where `(L⁻¹)ⱼᵢ = L.symm (Pi.single i 1) j` is the
`(j, i)` entry of the matrix of `L⁻¹`. -/
theorem affinePiolaTransform_eq_det_smul (L : (Fin n → ℝ) ≃L[ℝ] Fin n → ℝ) (p : Fin n → ℝ)
    (F : Fin n → (Fin n → ℝ) → E) (j : Fin n) (u : Fin n → ℝ) :
    affinePiolaTransform (L : (Fin n → ℝ) →L[ℝ] Fin n → ℝ) p F j u =
      (L : (Fin n → ℝ) →L[ℝ] Fin n → ℝ).det •
        ∑ i, L.symm (Pi.single i 1) j • F i (p + L u) := by
  set M := LinearMap.toMatrix' ((L : (Fin n → ℝ) →L[ℝ] Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] Fin n → ℝ)
  -- The matrix `N` of `L⁻¹` satisfies `N * M = 1`, so
  -- `adjugate M = N * (M * adjugate M) = det M • N`.
  have hNM : LinearMap.toMatrix'
      ((L.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] Fin n → ℝ) * M = 1 := by
    rw [← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_id]
    congr 1
    exact LinearMap.ext fun v ↦ L.symm_apply_apply v
  have hadj : M.adjugate = M.det • LinearMap.toMatrix'
      ((L.symm : (Fin n → ℝ) →L[ℝ] Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] Fin n → ℝ) := by
    rw [← one_mul M.adjugate, ← hNM, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul,
      Matrix.mul_one]
  rw [affinePiolaTransform_apply, hadj, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [M, mul_smul, LinearMap.toMatrix'_apply, ContinuousLinearMap.det]

/-- The divergence of the Piola transform is `det L` times the divergence at `p + L u`, written
for arbitrary candidate derivatives `F' i`. -/
private theorem sum_adjugate_smul_comp_apply_single (L : (Fin n → ℝ) →L[ℝ] Fin n → ℝ)
    (F' : Fin n → (Fin n → ℝ) →L[ℝ] E) :
    ∑ j, (∑ i, (LinearMap.toMatrix' (L : (Fin n → ℝ) →ₗ[ℝ] Fin n → ℝ)).adjugate j i •
        (F' i).comp L) (Pi.single j 1) =
      L.det • ∑ i, F' i (Pi.single i 1) := by
  set M := LinearMap.toMatrix' (L : (Fin n → ℝ) →ₗ[ℝ] Fin n → ℝ)
  simp only [sum_apply, smul_apply, ContinuousLinearMap.comp_apply]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- `∑ j, (adjugate M) j i • Pi.single j 1` is the `i`-th column of `adjugate M`, which `L` sends
  -- to `det L • Pi.single i 1` because `M * adjugate M = det M • 1`.
  have hcol : ∑ j, M.adjugate j i • (Pi.single j 1 : Fin n → ℝ) =
      Matrix.mulVec M.adjugate (Pi.single i 1) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hL : L (Matrix.mulVec M.adjugate (Pi.single i 1)) = L.det • Pi.single i 1 := by
    rw [← ContinuousLinearMap.coe_coe, ← LinearMap.toMatrix'_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec, LinearMap.det_toMatrix']
  rw [← map_smul, ← hL, ← hcol, map_sum, map_sum]
  simp only [map_smul]

/-- The derivative of the Piola transform: if each `F i` has derivative `F' i` at `p + L u`, then
the `j`-th component of the Piola transform has derivative
`∑ i, (adjugate M) j i • (F' i).comp L` at `u`. -/
theorem hasFDerivAt_affinePiolaTransform {L : (Fin n → ℝ) →L[ℝ] Fin n → ℝ} {p : Fin n → ℝ}
    {F : Fin n → (Fin n → ℝ) → E} {F' : Fin n → (Fin n → ℝ) →L[ℝ] E} {u : Fin n → ℝ}
    (hF : ∀ i, HasFDerivAt (F i) (F' i) (p + L u)) (j : Fin n) :
    HasFDerivAt (affinePiolaTransform L p F j)
      (∑ i, (LinearMap.toMatrix' (L : (Fin n → ℝ) →ₗ[ℝ] Fin n → ℝ)).adjugate j i •
        (F' i).comp L) u := by
  have hA : HasFDerivAt (fun u ↦ p + L u) L u := (hasFDerivAt_const_add_iff p).2 L.hasFDerivAt
  exact HasFDerivAt.fun_sum fun i _ ↦ ((hF i).comp u hA).const_smul _

/-- **Piola's identity** for an affine map: the divergence of the Piola transform of `F` along
`u ↦ p + L u` is `det L` times the divergence of `F` at `p + L u`. The determinant is signed. -/
theorem sum_fderiv_affinePiolaTransform {L : (Fin n → ℝ) →L[ℝ] Fin n → ℝ} {p : Fin n → ℝ}
    {F : Fin n → (Fin n → ℝ) → E} {u : Fin n → ℝ}
    (hF : ∀ i, DifferentiableAt ℝ (F i) (p + L u)) :
    ∑ j, fderiv ℝ (affinePiolaTransform L p F j) u (Pi.single j 1) =
      L.det • ∑ i, fderiv ℝ (F i) (p + L u) (Pi.single i 1) := by
  rw [← sum_adjugate_smul_comp_apply_single]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [(hasFDerivAt_affinePiolaTransform (fun i ↦ (hF i).hasFDerivAt) j).fderiv]

/-! ### The divergence theorem on an affine parallelepiped -/

/-- The boundary flux of a family of fields `F i : ℝⁿ⁺¹ → E` through the parallelepiped
`A([0, 1]ⁿ⁺¹)`, `A u = p + L u`: the boundary sum over the unit cube of the Piola transform of `F`
along `A`. It is the boundary term of the divergence theorem on the parallelepiped,
`TauCeti.det_smul_integral_divergence_eq_affineFluxBoundary`, where the determinant of `L` enters
with its sign. -/
def affineFluxBoundary (L : (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ) (p : Fin (n + 1) → ℝ)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) : E :=
  boxBoundarySum 0 1 (affinePiolaTransform L p F)

theorem affineFluxBoundary_def (L : (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ)
    (p : Fin (n + 1) → ℝ) (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) :
    affineFluxBoundary L p F = boxBoundarySum 0 1 (affinePiolaTransform L p F) :=
  (rfl)

/-- The Piola transform along the identity is the original field. -/
@[simp]
theorem affinePiolaTransform_id_zero (F : Fin n → (Fin n → ℝ) → E) :
    affinePiolaTransform (ContinuousLinearMap.id ℝ (Fin n → ℝ)) 0 F = F := by
  ext j u
  simp [affinePiolaTransform_apply, ContinuousLinearMap.coe_id, LinearMap.toMatrix'_id,
    Matrix.one_apply]

/-- For the identity map, the affine flux boundary is the boundary sum of the unit cube. -/
@[simp]
theorem affineFluxBoundary_id_zero (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) :
    affineFluxBoundary (ContinuousLinearMap.id ℝ (Fin (n + 1) → ℝ)) 0 F = boxBoundarySum 0 1 F := by
  rw [affineFluxBoundary_def, affinePiolaTransform_id_zero]

/-- **Divergence theorem on an affine parallelepiped.** Let `A u = p + L u`. If each `F i` is
continuous on `A([0, 1]ⁿ⁺¹)`, has derivative `F' i (A u)` at `A u` for every `u` in the open unit
cube off a countable set, and the pulled back divergence `u ↦ ∑ i, F' i (A u) (Pi.single i 1)`
is integrable on `[0, 1]ⁿ⁺¹`, then `det L` times its integral is the affine flux boundary. -/
theorem det_smul_integral_divergence_eq_affineFluxBoundary
    {L : (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ} {p : Fin (n + 1) → ℝ}
    {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    {F' : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] E}
    {s : Set (Fin (n + 1) → ℝ)} (hs : s.Countable)
    (hc : ∀ i, ContinuousOn (F i) ((fun u ↦ p + L u) '' Icc 0 1))
    (hd : ∀ u ∈ (univ.pi fun _ ↦ Ioo (0 : ℝ) 1) \ s, ∀ i,
      HasFDerivAt (F i) (F' i (p + L u)) (p + L u))
    (hi : IntegrableOn (fun u ↦ ∑ i, F' i (p + L u) (Pi.single i 1)) (Icc 0 1)) :
    L.det • ∫ u in Icc 0 1, ∑ i, F' i (p + L u) (Pi.single i 1) = affineFluxBoundary L p F := by
  set H' : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] E := fun j u ↦
    ∑ i, (LinearMap.toMatrix' (L : (Fin (n + 1) → ℝ) →ₗ[ℝ] Fin (n + 1) → ℝ)).adjugate j i •
      (F' i (p + L u)).comp L
  have hdiv (u : Fin (n + 1) → ℝ) : ∑ j, H' j u (Pi.single j 1) =
      L.det • ∑ i, F' i (p + L u) (Pi.single i 1) :=
    sum_adjugate_smul_comp_apply_single L fun i ↦ F' i (p + L u)
  have hA : ContinuousOn (fun u ↦ p + L u) (Icc 0 1) :=
    (continuous_const.add L.continuous).continuousOn
  have hcont (j : Fin (n + 1)) : ContinuousOn (affinePiolaTransform L p F j) (Icc 0 1) := by
    rw [show affinePiolaTransform L p F j = _ from funext (affinePiolaTransform_apply L p F j)]
    exact continuousOn_finsetSum _ fun i _ ↦ ((hc i).comp hA (mapsTo_image _ _)).const_smul _
  have hi' : IntegrableOn (fun u ↦ ∑ j, H' j u (Pi.single j 1)) (Icc 0 1) := by
    simp only [hdiv]
    exact hi.smul L.det
  rw [affineFluxBoundary_def, ← integral_divergence_eq_boxBoundarySum (F' := H') zero_le_one hs
    hcont (fun u hu j ↦ hasFDerivAt_affinePiolaTransform (hd u hu) j) hi']
  simp only [hdiv, integral_smul]

/-- A family of fields whose divergence vanishes in the interior of the parallelepiped
`A([0, 1]ⁿ⁺¹)`, `A u = p + L u`, away from the image of a countable set, and which is continuous
on the closed parallelepiped, has zero affine flux boundary. -/
theorem affineFluxBoundary_eq_zero
    {L : (Fin (n + 1) → ℝ) →L[ℝ] Fin (n + 1) → ℝ} {p : Fin (n + 1) → ℝ}
    {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    {F' : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] E}
    {s : Set (Fin (n + 1) → ℝ)} (hs : s.Countable)
    (hc : ∀ i, ContinuousOn (F i) ((fun u ↦ p + L u) '' Icc 0 1))
    (hd : ∀ u ∈ (univ.pi fun _ ↦ Ioo (0 : ℝ) 1) \ s, ∀ i,
      HasFDerivAt (F i) (F' i (p + L u)) (p + L u))
    (hdiv : ∀ u ∈ (univ.pi fun _ ↦ Ioo (0 : ℝ) 1) \ s, ∑ i, F' i (p + L u) (Pi.single i 1) = 0) :
    affineFluxBoundary L p F = 0 := by
  -- The divergence vanishes almost everywhere on the closed cube: up to a null set the cube is
  -- its interior, and the countable set `s` is null.
  have hae : (fun u ↦ ∑ i, F' i (p + L u) (Pi.single i 1)) =ᵐ[volume.restrict (Icc 0 1)] 0 := by
    rw [volume_pi, ← Measure.restrict_congr_set Measure.univ_pi_Ioo_ae_eq_Icc, ← volume_pi]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo),
      ae_restrict_of_ae (hs.ae_notMem volume)] with u hu hus
    exact hdiv u ⟨hu, hus⟩
  rw [← det_smul_integral_divergence_eq_affineFluxBoundary hs hc hd
    (integrableOn_zero.congr_fun_ae hae.symm), integral_congr_ae hae]
  simp

end TauCeti
