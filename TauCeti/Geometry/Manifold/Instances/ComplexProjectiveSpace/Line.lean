/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.FubiniStudySphere
public import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.Clutching
public import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.Symplectic
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# The Fubini–Study area of a line in complex projective space

The coordinate line `TauCeti.ComplexProjectiveSpace.coordinateLine n` of `CPⁿ⁺¹` parametrizes the
line `X₂ = ⋯ = X_(n+1) = 0` by the Riemann sphere, `z ↦ [1 : z : 0 : ⋯ : 0]` and
`∞ ↦ [0 : 1 : 0 : ⋯ : 0]`. This file shows that it is holomorphic, and that it pulls the
Fubini–Study form `ω_FS` of `CPⁿ⁺¹` (`TauCeti.ComplexProjectiveSpace.fubiniStudyForm`) back to the
Fubini–Study form of the Riemann sphere (`OnePoint.fubiniStudyForm`). Since that form has area `1`
on the standard sphere, a line of `CPⁿ⁺¹` has Fubini–Study area `1`: the integral of `ω_FS` over
the class of the line sphere `TauCeti.ComplexProjectiveSpace.lineSquare n` in `π₂(CPⁿ⁺¹)` is `1`.
This is the normalization `ω_FS[line] = 1` of the Fubini–Study form: the symplectic area of the
class of a line, the period of `CPⁿ⁺¹` with which capped Hamiltonian Floer theory filters its
Novikov coefficients. The other period of the same class, its first Chern number, is the clutching
number `n + 2` of the tangent bundle on the line sphere
(`TauCeti.ComplexProjectiveSpace.clutchingNumber_tangentSpace_lineSquare`).

* **Holomorphy.** Near a finite point the line is `z ↦ affineParam 0 (z, 0, …, 0)`, read through
  the affine chart of the Riemann sphere; near `∞` it is `w ↦ affineParam 1 (w, 0, …, 0)`, read
  through the inverted chart, since `[1 : z : 0 : ⋯ : 0] = [z⁻¹ : 1 : 0 : ⋯ : 0]` for `z ≠ 0`
  (`TauCeti.ComplexProjectiveSpace.contMDiff_coordinateLine`).
* **The pullback.** At a finite point `z`, the Fubini–Study form of `CPⁿ⁺¹` in the chart `X₀ ≠ 0`
  is given by the Hermitian form `(r ⟪a, b⟫ - ⟪a, w⟫ ⟪w, b⟫) / (π r²)`, `r = 1 + ∑ |w_l|²`
  (`TauCeti.ComplexProjectiveSpace.fubiniStudyHermitian_affineVector_insertZeroL`). Along the line
  `w = (z, 0, …, 0)` only tangent vectors `a = b = (1, 0, …, 0)` are seen, and the form gives
  `((1 + |z|²) - |z|²) / (π (1 + |z|²)²) = 1 / (π (1 + |z|²)²)`, the density of the Fubini–Study
  form of the Riemann sphere. Two smooth forms which agree on the dense set of finite points are
  equal (`TauCeti.SmoothBundleForm.eq_of_forall_mem_dense`), which gives
  `TauCeti.ComplexProjectiveSpace.mpullback_coordinateLine_fubiniStudyForm`.
* **The area.** By naturality of the integral over spheres (`TauCeti.sphereIntegral_mpullback`),
  the integral of `ω_FS` over the line sphere is that of `OnePoint.fubiniStudyForm` over the
  standard sphere of the Riemann sphere, which is `1`
  (`OnePoint.sphereIntegral_fubiniStudyForm_riemannSphereSquare`); hence
  `TauCeti.ComplexProjectiveSpace.sphereIntegral_fubiniStudyForm_lineSquare`.

## Main results

* `TauCeti.ComplexProjectiveSpace.contMDiff_coordinateLine`: the coordinate line is holomorphic;
  `TauCeti.ComplexProjectiveSpace.contMDiff_coordinateLine_real` is the same statement for the
  underlying real manifolds.
* `TauCeti.ComplexProjectiveSpace.mpullback_coordinateLine_fubiniStudyForm`: the coordinate line
  pulls the Fubini–Study form of `CPⁿ⁺¹` back to that of the Riemann sphere.
* `TauCeti.ComplexProjectiveSpace.sphereIntegral_fubiniStudyForm_lineSquare`: the Fubini–Study
  area of the class of a line is `1`.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0,
  Section 2 (the Fubini–Study metric, normalized so that a line has area one).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Section 11.1 (the symplectic area and first Chern number of the line class of `CPⁿ`).
-/

public section

open Bundle Filter Set Topology ComplexConjugate
open scoped Manifold OnePoint ContDiff Topology.Homotopy TauCeti.ComplexManifold

noncomputable section

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ}

/-! ### Holomorphy of the coordinate line -/

/-- The map `z ↦ affineParam k (z, 0, …, 0)` into `CPⁿ⁺¹` is holomorphic. For `k = 0` it is the
parametrization `z ↦ [1 : z : 0 : ⋯ : 0]` of the finite part of the coordinate line, and for
`k = 1` it is `w ↦ [w : 1 : 0 : ⋯ : 0]`, the coordinate line read near `∞`. -/
private theorem contMDiff_affineParam_single (k : Fin (n + 2)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω
      fun z : ℂ ↦ affineParam k (Pi.single 0 z : Fin (n + 1) → ℂ) :=
  ((contMDiff_affineChart_symm k ω).comp
    (contDiff_single (𝕜 := ℂ) (fun _ : Fin (n + 1) ↦ ℂ) ω 0).contMDiff).congr fun _ ↦
    (affineChart_symm_apply k _).symm

/-- **The coordinate line is holomorphic.** The map `z ↦ [1 : z : 0 : ⋯ : 0]`, `∞ ↦
[0 : 1 : 0 : ⋯ : 0]` from the Riemann sphere to `CPⁿ⁺¹` is a holomorphic map of complex
manifolds. -/
theorem contMDiff_coordinateLine :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (coordinateLine n) := by
  intro x
  induction x using OnePoint.rec with
  | infty =>
    -- Near `∞`, the line read through the inverted chart is `w ↦ [w : 1 : 0 : ⋯ : 0]`.
    have hev : ⇑(coordinateLine n) =ᶠ[𝓝 (∞ : OnePoint ℂ)]
        (fun w : ℂ ↦ affineParam 1 (Pi.single 0 w : Fin (n + 1) → ℂ)) ∘ OnePoint.invChart := by
      filter_upwards [OnePoint.invChart.open_source.mem_nhds (by simp)] with x hx
      induction x using OnePoint.rec with
      | infty => simp
      | coe z =>
        have hz : z ≠ 0 := by rintro rfl; simp at hx
        simp [affineParam_zero_single_eq hz]
    exact ((contMDiff_affineParam_single 1 _).comp _
      (contMDiffAt_of_mem_maximalAtlas OnePoint.invChart_mem_maximalAtlas
        (by simp))).congr_of_eventuallyEq hev
  | coe z =>
    -- Near a finite point, the line read through the affine chart is `z ↦ [1 : z : 0 : ⋯ : 0]`.
    have hev : ⇑(coordinateLine n) =ᶠ[𝓝 (z : OnePoint ℂ)]
        (fun w : ℂ ↦ affineParam 0 (Pi.single 0 w : Fin (n + 1) → ℂ)) ∘ OnePoint.affineChart := by
      filter_upwards [OnePoint.affineChart.open_source.mem_nhds (by simp)] with x hx
      induction x using OnePoint.rec with
      | infty => simp at hx
      | coe z => simp
    exact ((contMDiff_affineParam_single 0 _).comp _
      (contMDiffAt_of_mem_maximalAtlas OnePoint.affineChart_mem_maximalAtlas
        (by simp))).congr_of_eventuallyEq hev

/-- The coordinate line is a smooth map of the underlying real manifolds, of every order. -/
theorem contMDiff_coordinateLine_real {r : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) r (coordinateLine n) := by
  simpa only [modelWithCornersSelf_restrictScalars] using
    ((contMDiff_coordinateLine (n := n)).restrictScalars ℝ).of_le le_top

/-! ### The pullback of the Fubini–Study form -/

/-- At a finite point `z`, the derivative of the coordinate line, read in the affine chart of the
Riemann sphere, is the derivative of the chart parametrization `affineParam 0` at
`(z, 0, …, 0)` on the vector `(v, 0, …, 0)`. -/
private theorem mfderiv_coordinateLine_coe (z v : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (coordinateLine n) (z : OnePoint ℂ) v =
      mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (affineParam 0)
        (Pi.single 0 z : Fin (n + 1) → ℂ) (Pi.single 0 v : Fin (n + 1) → ℂ) := by
  have hcoe := OnePoint.hasMFDerivAt_coe z
  have hline : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (coordinateLine n) z :=
    (contMDiff_coordinateLine_real (r := 1) _).mdifferentiableAt one_ne_zero
  have hparam : MDifferentiableAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (affineParam 0)
      (Pi.single 0 z : Fin (n + 1) → ℂ) :=
    (contMDiff_affineParam_real 0 1 _).mdifferentiableAt one_ne_zero
  have hsingle := hasFDerivAt_single (𝕜 := ℝ) (E := fun _ : Fin (n + 1) ↦ ℂ) (i := 0) z
  -- On `ℂ`, the coordinate line is the chart parametrization composed with `z ↦ (z, 0, …, 0)`.
  have hcomp : (coordinateLine n ∘ ((↑) : ℂ → OnePoint ℂ)) =
      affineParam 0 ∘ fun x : ℂ ↦ (Pi.single 0 x : Fin (n + 1) → ℂ) :=
    funext coordinateLine_coe
  have h₁ : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (coordinateLine n ∘ ((↑) : ℂ → OnePoint ℂ))
      z v : Fin (n + 1) → ℂ) =
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (coordinateLine n) (z : OnePoint ℂ) v := by
    rw [mfderiv_comp z hline hcoe.mdifferentiableAt, hcoe.mfderiv]
    -- The tangent space of `ℂ` at `z` is `ℂ` itself, so the composite with the identity of `ℂ`
    -- applies `mfderiv (coordinateLine n) z` to `v`.
    rfl
  have h₂ : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ)
      (affineParam 0 ∘ fun x : ℂ ↦ (Pi.single 0 x : Fin (n + 1) → ℂ)) z v : Fin (n + 1) → ℂ) =
        mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (affineParam 0)
          (Pi.single 0 z : Fin (n + 1) → ℂ) (Pi.single 0 v : Fin (n + 1) → ℂ) := by
    rw [mfderiv_comp z hparam hsingle.differentiableAt.mdifferentiableAt, mfderiv_eq_fderiv,
      hsingle.fderiv]
    refine congrArg (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (affineParam 0)
      (Pi.single 0 z : Fin (n + 1) → ℂ)) ?_
    -- `NormedSpace.fromTangentSpace` is the identity of the model space.
    change ContinuousLinearMap.pi (Pi.single 0 (ContinuousLinearMap.id ℝ ℂ)) v =
      (Pi.single 0 v : Fin (n + 1) → ℂ)
    funext j
    by_cases hj : j = 0
    · subst hj
      simp
    · simp [hj]
  rw [← h₁, ← h₂, hcomp]

/-- At a finite point `z`, the Fubini–Study form of `CPⁿ⁺¹` pulled back along the coordinate line
is `Im (conj v * w) / (π (1 + |z|²)²)`, the Fubini–Study form of the Riemann sphere. -/
private theorem eval₂_mpullback_coordinateLine_fubiniStudyForm_coe (z v w : ℂ) :
    SmoothBundleForm.eval₂
        (SmoothForm.mpullback (coordinateLine n) contMDiff_coordinateLine_real
          (fubiniStudyForm (n + 1))) (z : OnePoint ℂ) v w =
      OnePoint.fubiniStudyDensity z * (conj v * w).im := by
  refine (SmoothForm.eval₂_mpullback _ _ _ _ v w).trans ?_
  rw [mfderiv_coordinateLine_coe z v, mfderiv_coordinateLine_coe z w, coordinateLine_coe]
  refine (SmoothForm.eval₂_mpullback (affineParam 0) (contMDiff_affineParam_real 0 _) _ _ _
    _).symm.trans ?_
  refine (eval₂_mpullback_affineParam_fubiniStudyForm 0 (Pi.single 0 z) (Pi.single 0 v)
    (Pi.single 0 w)).trans ?_
  -- Along `(z, 0, …, 0)` only the entries in position `0` contribute to the sums.
  have hsum (a b : ℂ) : ∑ l, conj ((Pi.single 0 a : Fin (n + 1) → ℂ) l) *
      (Pi.single 0 b : Fin (n + 1) → ℂ) l = conj a * b := by
    rw [Finset.sum_eq_single 0 (fun l _ hl ↦ by simp [hl]) (by simp)]
    simp
  have hnorm : ∑ l, ‖(Pi.single 0 z : Fin (n + 1) → ℂ) l‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [Finset.sum_eq_single 0 (fun l _ hl ↦ by simp [hl]) (by simp)]
    simp
  rw [fubiniStudyHermitian_affineVector_insertZeroL, hsum, hsum, hsum, hnorm,
    OnePoint.fubiniStudyDensity_def]
  -- The numerator is `(1 + |z|²) conj v w - |z|² conj v w = conj v w`.
  have hnum : ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * (conj v * w) - conj v * z * (conj z * w) = conj v * w := by
    rw [show conj v * z * (conj z * w) = (conj z * z) * (conj v * w) by ring, Complex.conj_mul']
    push_cast
    ring
  rw [hnum, Complex.div_ofReal_im, div_eq_inv_mul]

/-- **The coordinate line pulls the Fubini–Study form back to the Fubini–Study form.** Along the
coordinate line `z ↦ [1 : z : 0 : ⋯ : 0]` of `CPⁿ⁺¹`, the Fubini–Study form of `CPⁿ⁺¹` pulls back
to the Fubini–Study form of the Riemann sphere. -/
@[simp]
theorem mpullback_coordinateLine_fubiniStudyForm :
    SmoothForm.mpullback (coordinateLine n) contMDiff_coordinateLine_real
        (fubiniStudyForm (n + 1)) = OnePoint.fubiniStudyForm := by
  -- The two forms agree at the finite points, which are dense in the Riemann sphere.
  refine SmoothBundleForm.eq_of_forall_mem_dense OnePoint.denseRange_coe ?_
  rintro _ ⟨z, rfl⟩
  refine SmoothBundleForm.apply_eq_of_eval₂_eq fun (v w : ℂ) ↦ ?_
  rw [eval₂_mpullback_coordinateLine_fubiniStudyForm_coe, OnePoint.eval₂_fubiniStudyForm_coe]

/-! ### The area of a line -/

/-- **A line has Fubini–Study area `1`.** The integral of the Fubini–Study form of `CPⁿ⁺¹` over
the class of the line sphere `lineSquare n` in `π₂(CPⁿ⁺¹, [0 : 1 : 0 : ⋯ : 0])` is `1`. On the
same class the first Chern number of the tangent bundle is `n + 2`
(`TauCeti.ComplexProjectiveSpace.clutchingNumber_tangentSpace_lineSquare`). -/
theorem sphereIntegral_fubiniStudyForm_lineSquare :
    sphereIntegral (fubiniStudyForm (n + 1)).val (affineParam 1 0) ⟦lineSquare n⟧ = 1 := by
  have hφ : IsSmoothForm 𝓘(ℝ, Fin (n + 1) → ℂ) 1 (fubiniStudyForm (n + 1)).val :=
    (fubiniStudyForm (n + 1)).isSmoothForm.of_le (by simp)
  have hdφ := (SmoothForm.isClosed_def _).1 (isSymplectic_fubiniStudyForm (n := n + 1)).isClosed
  -- The line sphere is the image of the standard sphere of the Riemann sphere.
  have hmap : (⟦lineSquare n⟧ : HomotopyGroup (Fin 2) (ComplexProjectiveSpace (n + 1))
      (affineParam 1 0)) =
        HomotopyGroup.map (coordinateLine n) coordinateLine_infty ⟦riemannSphereSquare⟧ := by
    rw [HomotopyGroup.map_mk]
    exact congrArg _ (GenLoop.ext _ _ fun y ↦ by simp [lineSquare_apply])
  -- Naturality of the integral, with the base point `coordinateLine n ∞ = affineParam 1 0`.
  have hnat : ∀ y (hy : coordinateLine n ∞ = y),
      sphereIntegral (fubiniStudyForm (n + 1)).val y
          (HomotopyGroup.map (coordinateLine n) hy ⟦riemannSphereSquare⟧) =
        sphereIntegral (SmoothForm.mpullback (coordinateLine n) contMDiff_coordinateLine_real
          (fubiniStudyForm (n + 1))).val ∞ ⟦riemannSphereSquare⟧ := by
    rintro _ rfl
    rw [SmoothForm.coe_mpullback]
    exact (sphereIntegral_mpullback contMDiff_coordinateLine_real hφ hdφ _).symm
  rw [hmap, hnat _ coordinateLine_infty, mpullback_coordinateLine_fubiniStudyForm,
    OnePoint.sphereIntegral_fubiniStudyForm_riemannSphereSquare]

end TauCeti.ComplexProjectiveSpace
