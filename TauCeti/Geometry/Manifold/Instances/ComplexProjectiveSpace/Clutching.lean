/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Tangent.Clutching

/-!
# The first Chern number of complex projective space on a line

The holomorphic tangent bundle of complex projective space `CPᵐ` is a complex vector bundle of
rank `m`. This file computes its clutching number (`TauCeti.clutchingNumber`) on a projective
line: it is `m + 1`. This is the clutching description of `c₁(TCPᵐ)[line] = m + 1`, the Chern
number that gives the quantum variable `q^[line]` of `CPᵐ` its degree `2 (m + 1)`; as in
`TauCeti.clutchingNumber`, no comparison with a cohomological first Chern class is made here. For
`m = 1` it is the value `2` of `TauCeti.clutchingNumber_tangentSpace_riemannSphereSquare` on the
Riemann sphere. The statements are for `m = n + 1`, so that the line exists.

**The line.** The coordinate line `X₂ = ⋯ = X_m = 0` of `CPⁿ⁺¹` is the image of the Riemann sphere
under `TauCeti.ComplexProjectiveSpace.coordinateLine`, which sends `z ∈ ℂ` to `[1 : z : 0 : ⋯ : 0]`
and `∞` to `[0 : 1 : 0 : ⋯ : 0]`. Composed with the standard sphere
`TauCeti.riemannSphereSquare`, it is a sphere `TauCeti.ComplexProjectiveSpace.lineSquare n` based at
`[0 : 1 : 0 : ⋯ : 0]`.

**The frame.** In the affine chart `X₀ ≠ 0`, the line is `w = (z, 0, …, 0)`, and in the chart
`X₁ ≠ 0` it is `w' = (z⁻¹, 0, …, 0)`. The transition `w' = w₀⁻¹ (1, w₁, …, w_m)` has derivative
`diag(-z⁻², z⁻¹, …, z⁻¹)` along the line. Write `z = 2 c s` on the open square, for the offset `c`
of the point from the centre of the square and the scale `s = (1 - r²)^(-1/2)` of the standard
sphere. The frame used here is `diag(s², s, …, s)` in the chart `X₀ ≠ 0`, so that in the chart
`X₁ ≠ 0` it reads `diag(-(2 c)⁻², (2 c)⁻¹, …, (2 c)⁻¹)`, which is continuous up to the boundary of
the square. Its determinant on the boundary is `-(2 c)^(-(n + 2))`, so the clutching function is
`-ω^(n + 2)` for the direction `ω = c / |c|` from the centre, which turns once around the circle as
the boundary is run once. Hence the clutching number is `n + 2`
(`TauCeti.ComplexProjectiveSpace.clutchingNumber_tangentSpace_lineSquare`).

## Main declarations

* `TauCeti.ComplexProjectiveSpace.coordinateLine`: the coordinate line `OnePoint ℂ → CPⁿ⁺¹`.
* `TauCeti.ComplexProjectiveSpace.lineSquare`: the line as a sphere based at `[0 : 1 : 0 : ⋯ : 0]`.
* `TauCeti.ComplexProjectiveSpace.clutchingNumber_tangentSpace_lineSquare`: the clutching number
  of the holomorphic tangent bundle of `CPⁿ⁺¹` on the line is `n + 2`.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (the first Chern class of the tangent bundle of complex projective space).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Appendix C.1 (the first Chern number by clutching).
-/

public section

open Bundle Filter Set Topology
open scoped Manifold OnePoint unitInterval Topology.Homotopy

noncomputable section

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ}

/-! ### The coordinate line -/

/-- In the chart `X₁ ≠ 0`, the point `[1 : z : 0 : ⋯ : 0]` has the coordinates
`(z⁻¹, 0, …, 0)`. -/
private theorem affineChart_one_affineParam_zero_single (z : ℂ) :
    affineChart 1 (affineParam 0 (Pi.single 0 z : Fin (n + 1) → ℂ)) = Pi.single 0 z⁻¹ := by
  ext j
  rw [← affineChart_symm_apply, affineChart_transition]
  induction j using Fin.cases with
  | zero => simp
  | succ j => simp [Fin.succAbove, Fin.lt_def]

private theorem affineParam_zero_single_mem_affineOpen_one {z : ℂ} (hz : z ≠ 0) :
    affineParam 0 (Pi.single 0 z : Fin (n + 1) → ℂ) ∈ affineOpen 1 := by
  rw [affineParam_mem_affineOpen_iff]
  simpa using hz

/-- For `z ≠ 0`, the point `[1 : z : 0 : ⋯ : 0]` is `[z⁻¹ : 1 : 0 : ⋯ : 0]`. -/
private theorem affineParam_zero_single_eq {z : ℂ} (hz : z ≠ 0) :
    affineParam 0 (Pi.single 0 z : Fin (n + 1) → ℂ) = affineParam 1 (Pi.single 0 z⁻¹) := by
  rw [← affineChart_one_affineParam_zero_single, ← affineChart_symm_apply (k := 1)]
  exact ((affineChart 1).left_inv
    ((affineChart_source 1).symm ▸ affineParam_zero_single_mem_affineOpen_one hz)).symm

variable (n) in
/-- The **coordinate line** `X₂ = ⋯ = X_m = 0` of `CPⁿ⁺¹`, parametrized by the Riemann sphere:
`z ↦ [1 : z : 0 : ⋯ : 0]` and `∞ ↦ [0 : 1 : 0 : ⋯ : 0]`. -/
def coordinateLine : C(OnePoint ℂ, ComplexProjectiveSpace (n + 1)) where
  toFun x := x.elim (affineParam 1 0) fun z ↦ affineParam 0 (Pi.single 0 z)
  continuous_toFun := by
    refine continuous_iff_continuousAt.2 fun x ↦ ?_
    induction x using OnePoint.rec with
    | infty =>
      -- Near `∞`, read the line in the chart `X₁ ≠ 0`, where it is `z ↦ (z⁻¹, 0, …, 0)`.
      rw [OnePoint.continuousAt_infty']
      have h : Tendsto (fun z : ℂ ↦ affineParam 1 (Pi.single 0 z⁻¹ : Fin (n + 1) → ℂ))
          (coclosedCompact ℂ) (𝓝 (affineParam 1 0)) := by
        rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
        have := ((continuous_affineParam (n := n + 1) 1).comp
          (continuous_single (A := fun _ : Fin (n + 1) ↦ ℂ) 0)).tendsto 0
        simpa [Function.comp_def] using this.comp tendsto_inv₀_cobounded
      have h0 : {(0 : ℂ)}ᶜ ∈ coclosedCompact ℂ := by
        rw [mem_coclosedCompact_iff]
        simp
      refine h.congr' ?_
      filter_upwards [h0] with z hz
      simp [affineParam_zero_single_eq (n := n) hz]
    | coe z =>
      rw [OnePoint.continuousAt_coe]
      exact ((continuous_affineParam 0).comp
        (continuous_single (A := fun _ : Fin (n + 1) ↦ ℂ) 0)).continuousAt

/-- The coordinate line sends `z ∈ ℂ` to `[1 : z : 0 : ⋯ : 0]`. -/
@[simp]
theorem coordinateLine_coe (z : ℂ) :
    coordinateLine n z = affineParam 0 (Pi.single 0 z) :=
  (rfl)

/-- The coordinate line sends `∞` to `[0 : 1 : 0 : ⋯ : 0]`. -/
@[simp]
theorem coordinateLine_infty : coordinateLine n ∞ = affineParam 1 0 :=
  (rfl)

variable (n) in
/-- The **coordinate line as a sphere** `I² / ∂I² → CPⁿ⁺¹`, based at `[0 : 1 : 0 : ⋯ : 0]`: the
coordinate line composed with the standard sphere `TauCeti.riemannSphereSquare` of the Riemann
sphere. -/
def lineSquare : Ω^ (Fin 2) (ComplexProjectiveSpace (n + 1)) (affineParam 1 0) :=
  ⟨(coordinateLine n).comp riemannSphereSquare.val, fun y hy ↦ by
    simp [riemannSphereSquare_apply_of_mem hy]⟩

/-- The line sphere is the coordinate line composed with the standard sphere of the Riemann
sphere. -/
theorem lineSquare_apply (y : Fin 2 → I) :
    lineSquare n y = coordinateLine n (riemannSphereSquare y) :=
  (rfl)

/-- The line sphere sends the boundary of the square to `[0 : 1 : 0 : ⋯ : 0]`. -/
@[simp]
theorem lineSquare_apply_of_mem {y : Fin 2 → I} (hy : y ∈ Cube.boundary (Fin 2)) :
    lineSquare n y = affineParam 1 0 :=
  (lineSquare n).property y hy

/-- At a point of the open square, the line sphere is `[1 : z : 0 : ⋯ : 0]` for
`z = 2 c / √(1 - r²)`, with the offset `c` from the centre and the sup radius `r = cubeRadius y`. -/
theorem lineSquare_apply_of_notMem {y : Fin 2 → I} (hy : y ∉ Cube.boundary (Fin 2)) :
    lineSquare n y = affineParam 0 (Pi.single 0
      (2 * squareCenterOffset y / (√(1 - cubeRadius y ^ 2) : ℝ))) := by
  rw [lineSquare_apply, riemannSphereSquare_apply_of_notMem hy, coordinateLine_coe]

/-! ### The tangent coordinate change along the line -/

/-- The chart transition from `X₀ ≠ 0` to `X₁ ≠ 0` is `w ↦ w₀⁻¹ (1, w₁, …, w_m)`. -/
private theorem affineChart_one_affineParam_zero (w : Fin (n + 1) → ℂ) :
    affineChart 1 (affineParam 0 w) = (w 0)⁻¹ • Function.update w 0 1 := by
  ext j
  rw [← affineChart_symm_apply, affineChart_transition]
  induction j using Fin.cases with
  | zero => simp [div_eq_inv_mul]
  | succ j => simp [Fin.succAbove, Fin.lt_def, div_eq_inv_mul]

private theorem hasFDerivAt_affineChart_one_affineParam_zero {w : Fin (n + 1) → ℂ}
    (hw : w 0 ≠ 0) :
    HasFDerivAt (fun w ↦ affineChart 1 (affineParam 0 w))
      ((w 0)⁻¹ • (ContinuousLinearMap.id ℂ _ -
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) 0).smulRight
            (Pi.single 0 1)) +
        ((-((w 0) ^ 2)⁻¹) •
          ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) 0).smulRight
            (Function.update w 0 1)) w := by
  simp_rw [affineChart_one_affineParam_zero]
  have hc : HasFDerivAt (fun w : Fin (n + 1) → ℂ ↦ (w 0)⁻¹)
      ((-((w 0) ^ 2)⁻¹) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) 0)
      w := by
    refine ((hasDerivAt_inv hw).hasFDerivAt.comp (x := w)
      (hasFDerivAt_apply (𝕜 := ℂ) (F' := fun _ : Fin (n + 1) ↦ ℂ) 0 w)).congr_fderiv ?_
    ext v : 1
    simp [mul_comm]
  -- `w ↦ update w 0 1` is affine, with linear part `v ↦ v - v₀ e₀`.
  have hf : HasFDerivAt (fun w : Fin (n + 1) → ℂ ↦ Function.update w 0 1)
      (ContinuousLinearMap.id ℂ _ -
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) 0).smulRight
            (Pi.single 0 1)) w := by
    convert ((ContinuousLinearMap.id ℂ (Fin (n + 1) → ℂ) -
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ) 0).smulRight
        (Pi.single 0 1)).hasFDerivAt (x := w)).add_const (Pi.single 0 1) using 1
    ext u j
    induction j using Fin.cases <;> simp
  exact hc.smul hf

/-- Along the line, the tangent coordinate change from the chart `X₀ ≠ 0` to the chart `X₁ ≠ 0` is
`diag(-z⁻², z⁻¹, …, z⁻¹)` at `[1 : z : 0 : ⋯ : 0]`. -/
private theorem tangentCoordChange_affineParam_zero_single {z : ℂ} (hz : z ≠ 0)
    (v : Fin (n + 1) → ℂ) :
    tangentCoordChange 𝓘(ℂ, Fin (n + 1) → ℂ) (affineParam (n := n + 1) 0 0) (affineParam 1 0)
        (affineParam 0 (Pi.single 0 z)) v =
      Fin.cons (-((z ^ 2)⁻¹ * v 0)) fun j ↦ z⁻¹ * v j.succ := by
  have hb : affineParam 0 (Pi.single 0 z : Fin (n + 1) → ℂ) ∈
      (extChartAt 𝓘(ℂ, Fin (n + 1) → ℂ) (affineParam 0 (0 : Fin (n + 1) → ℂ))).source ∩
        (extChartAt 𝓘(ℂ, Fin (n + 1) → ℂ) (affineParam 1 (0 : Fin (n + 1) → ℂ))).source := by
    simp only [extChartAt_source, chartAt_affineParam_zero]
    rw [affineChart_source, affineChart_source]
    exact ⟨by simp [affineParam_mem_affineOpen_iff], affineParam_zero_single_mem_affineOpen_one hz⟩
  have h := hasFDerivWithinAt_tangentCoordChange hb
  have hw : (Pi.single 0 z : Fin (n + 1) → ℂ) 0 ≠ 0 := by simpa using hz
  simp only [extChartAt_coe, extChartAt_coe_symm, chartAt_affineParam_zero,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    Function.comp_apply, range_id, hasFDerivWithinAt_univ] at h
  have h0 : affineChart 0 (affineParam 0 (Pi.single 0 z : Fin (n + 1) → ℂ)) = Pi.single 0 z := by
    rw [← affineChart_symm_apply]
    exact (affineChart 0).right_inv (by simp)
  rw [h0] at h
  have h' := h.congr_of_eventuallyEq (f₁ := fun w ↦ affineChart 1 (affineParam 0 w))
    (Eventually.of_forall fun w ↦ by simp)
  rw [h'.unique (hasFDerivAt_affineChart_one_affineParam_zero hw)]
  ext j
  induction j using Fin.cases <;> simp

/-- The preferred trivialization of the tangent bundle of `CPⁿ⁺¹` at `affineParam k 0`, the
trivialization of the homogeneous-ratio chart `X_k ≠ 0`. -/
private abbrev triv (n : ℕ) (k : Fin (n + 2)) :=
  trivializationAt (Fin (n + 1) → ℂ) (TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ))
    (affineParam (n := n + 1) k 0)

private theorem mem_triv_baseSet_iff (k : Fin (n + 2)) (b : ComplexProjectiveSpace (n + 1)) :
    b ∈ (triv n k).baseSet ↔ b ∈ affineOpen k := by
  simp

/-- A vector given in the trivialization of the chart `X₀ ≠ 0` reads in the trivialization of the
chart `X₁ ≠ 0` through the tangent coordinate change. -/
private theorem triv_one_triv_zero_symm {b : ComplexProjectiveSpace (n + 1)}
    (h₀ : b ∈ (triv n 0).baseSet) (h₁ : b ∈ (triv n 1).baseSet) (w : Fin (n + 1) → ℂ) :
    (triv n 1).continuousLinearEquivAt ℂ b h₁ (((triv n 0).continuousLinearEquivAt ℂ b h₀).symm w) =
      tangentCoordChange 𝓘(ℂ, Fin (n + 1) → ℂ) (affineParam (n := n + 1) 0 0)
        (affineParam 1 0) b w := by
  rw [Trivialization.coe_continuousLinearEquivAt_eq,
    Trivialization.symm_continuousLinearEquivAt_eq]
  exact TauCeti.Manifold.continuousLinearMapAt_symmL_coordChange h₀ h₁ w

/-! ### A frame of the tangent bundle along the line -/

private theorem lineSquare_eq_sphereScale {y : Fin 2 → I} (hy : y ∉ Cube.boundary (Fin 2)) :
    lineSquare n y =
      affineParam 0 (Pi.single 0 ((sphereScale y : ℂ) * (2 * squareCenterOffset y))) := by
  rw [lineSquare_apply, riemannSphereSquare_eq_sphereScale hy, coordinateLine_coe]

/-- The coefficients `(s², s, …, s)` of the frame in the chart `X₀ ≠ 0`. -/
private def innerCoeff (y : Fin 2 → I) : Fin (n + 1) → ℂ :=
  Fin.cons ((sphereScale y : ℂ) ^ 2) fun _ ↦ (sphereScale y : ℂ)

/-- The coefficients `(-(2 c)⁻², (2 c)⁻¹, …, (2 c)⁻¹)` of the frame in the chart `X₁ ≠ 0`. -/
private def outerCoeff (y : Fin 2 → I) : Fin (n + 1) → ℂ :=
  Fin.cons (-((2 * squareCenterOffset y) ^ 2)⁻¹) fun _ ↦ (2 * squareCenterOffset y)⁻¹

private theorem innerCoeff_ne_zero {y : Fin 2 → I} (hy : y ∉ Cube.boundary (Fin 2))
    (j : Fin (n + 1)) : innerCoeff y j ≠ 0 := by
  induction j using Fin.cases <;> simp [innerCoeff, sphereScale_ne_zero hy]

private theorem outerCoeff_ne_zero {y : Fin 2 → I} (hy : squareCenterOffset y ≠ 0)
    (j : Fin (n + 1)) : outerCoeff y j ≠ 0 := by
  induction j using Fin.cases <;> simp [outerCoeff, hy]

private theorem lineSquare_mem_affineOpen_zero {y : Fin 2 → I} (hy : y ∉ Cube.boundary (Fin 2)) :
    lineSquare n y ∈ affineOpen 0 := by
  rw [lineSquare_apply_of_notMem hy, affineParam_mem_affineOpen_iff]
  simp

private theorem lineSquare_mem_affineOpen_one {y : Fin 2 → I} (hy : squareCenterOffset y ≠ 0) :
    lineSquare n y ∈ affineOpen 1 := by
  by_cases hb : y ∈ Cube.boundary (Fin 2)
  · rw [lineSquare_apply_of_mem hb, affineParam_zero_mem_affineOpen_iff]
  · rw [lineSquare_eq_sphereScale hb]
    exact affineParam_zero_single_mem_affineOpen_one
      (mul_ne_zero (Complex.ofReal_ne_zero.2 (sphereScale_ne_zero hb))
        (mul_ne_zero two_ne_zero hy))

open Classical in
/-- The frame `diag(s², s, …, s)` of the tangent bundle along the line, in the chart `X₀ ≠ 0` on
the open square, extended to the boundary by its reading `diag(-(2 c)⁻², (2 c)⁻¹, …, (2 c)⁻¹)` in
the chart `X₁ ≠ 0`. -/
private def frame (y : Fin 2 → I) :
    (Fin (n + 1) → ℂ) ≃L[ℂ] TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) (lineSquare n y) :=
  if hy : y ∈ Cube.boundary (Fin 2) then
    (ContinuousLinearEquiv.piCongrRight fun j ↦ ContinuousLinearEquiv.unitsEquivAut ℂ
        (Units.mk0 _ (outerCoeff_ne_zero (squareCenterOffset_ne_zero_of_mem hy) j))).trans
      ((triv n 1).continuousLinearEquivAt ℂ _ ((mem_triv_baseSet_iff _ _).2
        (lineSquare_mem_affineOpen_one (squareCenterOffset_ne_zero_of_mem hy)))).symm
  else
    (ContinuousLinearEquiv.piCongrRight fun j ↦ ContinuousLinearEquiv.unitsEquivAut ℂ
        (Units.mk0 _ (innerCoeff_ne_zero hy j))).trans
      ((triv n 0).continuousLinearEquivAt ℂ _ ((mem_triv_baseSet_iff _ _).2
        (lineSquare_mem_affineOpen_zero hy))).symm

/-- On the open square, the frame reads as `diag(s², s, …, s)` in the chart `X₀ ≠ 0`. -/
private theorem triv_zero_frame {y : Fin 2 → I} (hy : y ∉ Cube.boundary (Fin 2))
    (h : lineSquare n y ∈ (triv n 0).baseSet) (v : Fin (n + 1) → ℂ) :
    (triv n 0).continuousLinearEquivAt ℂ _ h (frame y v) = innerCoeff y * v := by
  simp only [frame, hy, dite_false, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  ext j
  simp [mul_comm]

/-- Away from the centre of the square, the frame reads as `diag(-(2 c)⁻², (2 c)⁻¹, …, (2 c)⁻¹)`
in the chart `X₁ ≠ 0`. -/
private theorem triv_one_frame {y : Fin 2 → I} (hc : squareCenterOffset y ≠ 0)
    (h : lineSquare n y ∈ (triv n 1).baseSet) (v : Fin (n + 1) → ℂ) :
    (triv n 1).continuousLinearEquivAt ℂ _ h (frame y v) = outerCoeff y * v := by
  by_cases hy : y ∈ Cube.boundary (Fin 2)
  · simp only [frame, hy, dite_true, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply]
    ext j
    simp [mul_comm]
  · -- At `z = 2 c s`, `diag(-z⁻², z⁻¹, …) diag(s², s, …) = diag(-(2 c)⁻², (2 c)⁻¹, …)`.
    have h₀ : lineSquare n y ∈ (triv n 0).baseSet :=
      (mem_triv_baseSet_iff _ _).2 (lineSquare_mem_affineOpen_zero hy)
    have hs := Complex.ofReal_ne_zero.2 (sphereScale_ne_zero hy)
    simp only [frame, hy, dite_false, ContinuousLinearEquiv.trans_apply]
    rw [triv_one_triv_zero_symm h₀ h, lineSquare_eq_sphereScale hy,
      tangentCoordChange_affineParam_zero_single (mul_ne_zero hs (mul_ne_zero two_ne_zero hc))]
    ext j
    induction j using Fin.cases <;>
    · simp only [innerCoeff, outerCoeff, ContinuousLinearEquiv.piCongrRight_apply,
        ContinuousLinearEquiv.unitsEquivAut_apply, Units.val_mk0, Pi.mul_apply, Fin.cons_zero,
        Fin.cons_succ]
      field_simp

/-- If, near `q₀`, the frame lies over the chart `X_k ≠ 0` and reads there as `a y * v` for
coefficients `a` continuous at `q₀`, then the frame is continuous at `q₀` as a map into the total
space of the tangent bundle. -/
private theorem continuousAt_frame_of_triv (k : Fin (n + 2)) {p : (Fin 2 → I) → Prop}
    (hmem : ∀ y, p y → lineSquare n y ∈ affineOpen k) {a : (Fin 2 → I) → Fin (n + 1) → ℂ}
    (hread : ∀ y, p y → ∀ (h : lineSquare n y ∈ (triv n k).baseSet) v,
      (triv n k).continuousLinearEquivAt ℂ _ h (frame y v) = a y * v)
    {q₀ : (Fin 2 → I) × (Fin (n + 1) → ℂ)} (hp : ∀ᶠ q in 𝓝 q₀, p q.1)
    (ha : ContinuousAt (fun q : (Fin 2 → I) × (Fin (n + 1) → ℂ) ↦ a q.1) q₀) :
    ContinuousAt (fun q : (Fin 2 → I) × (Fin (n + 1) → ℂ) ↦
      TotalSpace.mk' (Fin (n + 1) → ℂ) (E := TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ))
        (lineSquare n q.1) (frame q.1 q.2)) q₀ := by
  have hproj : ContinuousAt (fun q : (Fin 2 → I) × (Fin (n + 1) → ℂ) ↦ lineSquare n q.1) q₀ :=
    ((lineSquare n).val.continuous.comp continuous_fst).continuousAt
  refine (triv n k).continuousAt_of_comp_left hproj
    ((mem_triv_baseSet_iff _ _).2 (hmem _ hp.self_of_nhds)) ?_
  refine (hproj.prodMk (ha.mul continuousAt_snd)).congr (hp.mono fun q hq ↦ ?_)
  have h := (mem_triv_baseSet_iff _ _).2 (hmem _ hq)
  rw [Function.comp_apply, Trivialization.apply_eq_prod_continuousLinearEquivAt ℂ _ _ h,
    hread _ hq h]
  rfl

/-- **The frame is continuous** as a map into the total space of the tangent bundle, including at
the boundary of the square. -/
private theorem continuous_frame :
    Continuous fun q : (Fin 2 → I) × (Fin (n + 1) → ℂ) ↦
      TotalSpace.mk' (Fin (n + 1) → ℂ) (E := TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ))
        (lineSquare n q.1) (frame q.1 q.2) := by
  refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
  by_cases hb : q₀.1 ∈ Cube.boundary (Fin 2)
  · -- Near the boundary, read the frame in the chart `X₁ ≠ 0`.
    have hc : squareCenterOffset q₀.1 ≠ 0 := squareCenterOffset_ne_zero_of_mem hb
    have h2c : ContinuousAt (fun q : (Fin 2 → I) × (Fin (n + 1) → ℂ) ↦
        2 * squareCenterOffset q.1) q₀ :=
      (continuous_const.mul (continuous_squareCenterOffset.comp continuous_fst)).continuousAt
    have h2c0 : 2 * squareCenterOffset q₀.1 ≠ 0 := mul_ne_zero two_ne_zero hc
    exact continuousAt_frame_of_triv 1 (fun _ ↦ lineSquare_mem_affineOpen_one)
      (fun _ ↦ triv_one_frame)
      ((continuous_squareCenterOffset.comp continuous_fst).continuousAt.eventually_ne hc)
      (((h2c.pow 2).inv₀ (pow_ne_zero 2 h2c0)).neg.finCons
        (continuousAt_pi.2 fun _ ↦ h2c.inv₀ h2c0))
  · -- In the open square, read the frame in the chart `X₀ ≠ 0`.
    have hs : ContinuousAt (fun q : (Fin 2 → I) × (Fin (n + 1) → ℂ) ↦
        (sphereScale q.1 : ℂ)) q₀ :=
      Complex.continuous_ofReal.continuousAt.comp
        ((continuousAt_sphereScale hb).comp continuous_fst.continuousAt)
    exact continuousAt_frame_of_triv 0 (fun _ ↦ lineSquare_mem_affineOpen_zero)
      (fun _ ↦ triv_zero_frame)
      (continuous_fst.continuousAt.preimage_mem_nhds
        (Cube.isClosed_boundary.isOpen_compl.mem_nhds hb))
      ((hs.pow 2).finCons (continuousAt_pi.2 fun _ ↦ hs))

/-! ### The clutching number -/

/-- On the boundary of the square, the clutching function of the frame in the chart `X₁ ≠ 0` is
`-ω^(n + 2)`, for the direction `ω` of the point from the centre. -/
private theorem clutchingFunction_frame {y : Fin 2 → I} (hy : y ∈ Cube.boundary (Fin 2)) :
    clutchingFunction (lineSquare n) frame (triv n 1) y =
      -(squareCenterDirection y ^ (n + 2)) := by
  have hc := squareCenterOffset_ne_zero_of_mem hy
  have hb : lineSquare n y ∈ (triv n 1).baseSet :=
    (mem_triv_baseSet_iff _ _).2 (lineSquare_mem_affineOpen_one hc)
  -- In the chart `X₁ ≠ 0` the frame is the diagonal matrix of `outerCoeff y`, so its determinant
  -- is `-(2 c)^(-(n + 2))`.
  have hdet : LinearMap.det
      (((frame y).trans ((triv n 1).continuousLinearEquivAt ℂ _ hb)).toLinearEquiv :
        (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) =
        -((2 * squareCenterOffset y) ^ (n + 2))⁻¹ := by
    have h : (((frame y).trans ((triv n 1).continuousLinearEquivAt ℂ _ hb)).toLinearEquiv :
        (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) =
          Matrix.toLin' (Matrix.diagonal (outerCoeff y)) :=
      LinearMap.ext fun v ↦ by
        ext j
        simp [triv_one_frame hc, Matrix.mulVec_diagonal]
    rw [h, LinearMap.det_toLin', Matrix.det_diagonal, Fin.prod_univ_succ]
    simp only [outerCoeff, Fin.cons_zero, Fin.cons_succ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    -- Treat `2 c` as an atom, so that `ring` does not split off the numeral `2⁻¹`.
    generalize 2 * squareCenterOffset y = w
    ring
  -- Its normalization `-(2 c)^(-(n + 2)) / |2 c|^(-(n + 2))` is the inverse of `-ω^(n + 2)`.
  have hphase : (-((2 * squareCenterOffset y) ^ (n + 2))⁻¹ /
      (((2 * ‖squareCenterOffset y‖) ^ (n + 2))⁻¹ : ℝ))⁻¹ =
        -(squareCenterOffset y / (‖squareCenterOffset y‖ : ℂ)) ^ (n + 2) := by
    have hn : ((‖squareCenterOffset y‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hc
    push_cast
    simp only [mul_pow, div_pow]
    field_simp
  rw [clutchingFunction_of_mem hb]
  refine Circle.ext ?_
  rw [Circle.coe_inv, ContinuousLinearEquiv.coe_normalizedDet, hdet]
  simpa [coe_squareCenterDirection hc] using hphase

/-- **The clutching first Chern number of complex projective space on a line.** The clutching
number of the holomorphic tangent bundle of `CPⁿ⁺¹` on the coordinate line is `n + 2`. This is the
clutching description of `c₁(TCPᵐ)[line] = m + 1`; it is not compared here with a cohomological
`c₁`. -/
theorem clutchingNumber_tangentSpace_lineSquare :
    clutchingNumber (Fin (n + 1) → ℂ) (TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ)) (lineSquare n) =
      n + 2 := by
  rw [clutchingNumber_eq_squareBoundaryDegree (lineSquare n) (triv n 1)
      ((mem_triv_baseSet_iff _ _).2 ((affineParam_zero_mem_affineOpen_iff _ _).2 rfl))
      continuous_frame,
    squareBoundaryDegree_congr (Γ' := (fun _ ↦ -1) * squareCenterDirection ^ (n + 2))
      fun y hy ↦ by simp [clutchingFunction_frame hy],
    squareBoundaryDegree_mul continuousOn_const (continuousOn_squareCenterDirection.pow _),
    squareBoundaryDegree_pow continuousOn_squareCenterDirection, squareBoundaryDegree_const,
    squareBoundaryDegree_squareCenterDirection]
  push_cast
  ring

/-- The clutching number homomorphism `π₂(CPⁿ⁺¹) → ℤ` of the holomorphic tangent bundle takes the
value `n + 2` on the class of the coordinate line. -/
theorem clutchingNumberHom_tangentSpace_lineSquare :
    clutchingNumberHom (Fin (n + 1) → ℂ) (TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ)) (affineParam 1 0)
        (Additive.ofMul (Quotient.mk _ (lineSquare n))) = n + 2 := by
  rw [clutchingNumberHom_apply_mk, clutchingNumber_tangentSpace_lineSquare]

end TauCeti.ComplexProjectiveSpace
