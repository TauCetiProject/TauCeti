/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.AreaDisc
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Prod
public import TauCeti.Geometry.Symplectic.Manifold.Torus.Basic
public import TauCeti.Analysis.InnerProductSpace.PiL2
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Symplectic.Manifold.Rescale

/-!
# Embedding a bounded piece of the cylinder into `S²(a) × T`

Gromov's proof of the nonsqueezing theorem embeds a bounded part of the cylinder
`{z ∈ ℂⁿ | |z₀| < R}` symplectically into the closed symplectic manifold `S²(a) × T²ⁿ⁻²`, for
`a > π R²`, and counts holomorphic spheres there. This file constructs that embedding.

The target is the product of the sphere `S²(a) = (OnePoint ℂ, a • ω_FS)` of area `a` with a torus
`T = ∀ i : ι ⊕ ι, AddCircle (p i)` carrying its standard symplectic form `ω_T`
(`TauCeti.torusSymplecticForm`), with the product form `pr₁*(a • ω_FS) + pr₂*ω_T`
(`TauCeti.SmoothTwoForm.prod`); it is symplectic for `a ≠ 0`
(`TauCeti.isSymplectic_smul_fubiniStudyForm_prod_torusSymplecticForm`).

* `TauCeti.sphereTorusChart a p c hr` is the product of the inverse of the disc chart
  `OnePoint.areaDiscChart a`, which maps the open disc of radius `√(a / π)` onto the sphere minus
  `∞`, with the torus chart `TauCeti.complexPiTorusChart p c hr` on the ball of radius `r` about `c`
  in `ι → ℂ`. For `a > 0` it is a partial diffeomorphism from `ball 0 √(a / π) × ball c r` into
  `S²(a) × T` pulling the product form back to the standard form `dx ∧ dy ⊕ ω₀` of `ℂ × (ι → ℂ)`
  (`TauCeti.eval₂_mfderiv_sphereTorusChart`).
* `TauCeti.euclideanSphereTorusChart a p c hr` reads the first chart on complex Euclidean space
  `ℂᵐ⁺¹ = EuclideanSpace ℂ (Fin (m + 1))`, splitting off the first coordinate:
  `x ↦ (x 0, (x (i + 1))ᵢ)`. For `a > 0` it pulls the product form back to the standard
  symplectic form `Im ⟪v, w⟫` of `ℂᵐ⁺¹` (`TauCeti.eval₂_mfderiv_euclideanSphereTorusChart`).

Every bounded set `s ⊆ ℂᵐ⁺¹` whose first coordinates satisfy `|x₀| < R`, with `π R² ≤ a`, lies in
the source of `euclideanSphereTorusChart a p 0 hr` for one radius `r` and all periods `p i ≥ 2 r`
(`TauCeti.exists_forall_subset_euclideanSphereTorusChart_source`). In particular this applies to
the image of a compact ball under a continuous map into the cylinder of radius `R`, and composing a
symplectic embedding of the ball into the cylinder with the chart gives a symplectic embedding into
`S²(a) × T`.

## Main definitions

* `TauCeti.sphereTorusChart`: for `a > 0`, the symplectic embedding of `ball 0 √(a / π) × ball c r`
  in `ℂ × (ι → ℂ)` into `S²(a) × T`.
* `TauCeti.euclideanSphereTorusChart`: the same embedding read on `EuclideanSpace ℂ (Fin (m + 1))`.

## Main results

* `TauCeti.isSymplectic_smul_fubiniStudyForm_prod_torusSymplecticForm`: `S²(a) × T` is symplectic.
* `TauCeti.eval₂_mfderiv_sphereTorusChart`: for `a > 0`, the first chart pulls the product form
  back to `dx ∧ dy ⊕ ω₀`.
* `TauCeti.eval₂_mfderiv_euclideanSphereTorusChart`: for `a > 0`, the second chart pulls the
  product form back to `Im ⟪v, w⟫`.
* `TauCeti.exists_forall_subset_euclideanSphereTorusChart_source`: bounded pieces of the cylinder
  lie in its source once the periods are large.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Mathematicae 82
  (1985), 307–347, §0.3.A (the nonsqueezing theorem, proved through `S² × T²ⁿ⁻²`).
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Section 9.3.
-/

public section

noncomputable section

open Set Metric
open scoped Manifold ContDiff InnerProductSpace TauCeti.ComplexManifold

namespace TauCeti

/-! ### The symplectic manifold `S²(a) × T` -/

section Product

variable {ι : Type*} [Fintype ι] (a : ℝ) (p : ι ⊕ ι → ℝ) [∀ i, Fact (0 < p i)]

/-- **The product `S²(a) × T` is symplectic.** For `a ≠ 0`, the product of the sphere of area `a`,
`(OnePoint ℂ, a • ω_FS)`, with the standard symplectic torus is a symplectic manifold. -/
theorem isSymplectic_smul_fubiniStudyForm_prod_torusSymplecticForm (ha : a ≠ 0) :
    ((a • OnePoint.fubiniStudyForm).prod (torusSymplecticForm p)).IsSymplectic :=
  (OnePoint.isSymplectic_fubiniStudyForm.smul a ha).prod (isSymplectic_torusSymplecticForm p)

/-- **The symplectic embedding of a polydisc into `S²(a) × T`.** The product of the inverse of the
disc chart of the sphere of area `a` with the torus chart on the ball of radius `r` about `c`, when
`2 r` is at most every period. For `a > 0` its source is `ball 0 √(a / π) × ball c r`
(`TauCeti.sphereTorusChart_source`), and it pulls the product form `a • ω_FS ⊕ ω_T` back to the
standard form `dx ∧ dy ⊕ ω₀` (`TauCeti.eval₂_mfderiv_sphereTorusChart`). -/
def sphereTorusChart (c : ι → ℂ) {r : ℝ} (hr : ∀ i, 2 * r ≤ p i) :
    PartialDiffeomorph (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ι → ℂ))
      (𝓘(ℝ, ℂ).prod (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))) (ℂ × (ι → ℂ))
      (OnePoint ℂ × ∀ i, AddCircle (p i)) ∞ :=
  (OnePoint.areaDiscChart a).symm.prod (complexPiTorusChart p c hr)

variable {a p} (c : ι → ℂ) {r : ℝ} (hr : ∀ i, 2 * r ≤ p i)

/-- The chart is the inverse of the disc chart on the first factor and the covering map of the
torus on the second. -/
@[simp]
theorem sphereTorusChart_apply (z : ℂ × (ι → ℂ)) :
    sphereTorusChart a p c hr z =
      ((OnePoint.areaDiscChart a).symm z.1, complexPiTorusCover p z.2) := by
  simp [sphereTorusChart]

/-- For `a > 0`, the source of the chart is the polydisc `ball 0 √(a / π) × ball c r`. -/
@[simp]
theorem sphereTorusChart_source (ha : 0 < a) :
    (sphereTorusChart a p c hr).source = ball 0 √(a / Real.pi) ×ˢ ball c r := by
  simp [sphereTorusChart, OnePoint.areaDiscChart_target ha]

/-- The target of the chart is the product of the sphere minus `∞` with the image of the ball under
the covering map of the torus. -/
@[simp]
theorem sphereTorusChart_target :
    (sphereTorusChart a p c hr).target =
      {(OnePoint.infty : OnePoint ℂ)}ᶜ ×ˢ (complexPiTorusCover p '' ball c r) := by
  simp [sphereTorusChart]

/-- **The chart is symplectic.** For `a > 0`, at every point of its source the chart pulls the
product form `a • ω_FS ⊕ ω_T` of `S²(a) × T` back to the standard form `dx ∧ dy ⊕ ω₀` of
`ℂ × (ι → ℂ)`. -/
theorem eval₂_mfderiv_sphereTorusChart (ha : 0 < a) {z : ℂ × (ι → ℂ)}
    (hz : z ∈ (sphereTorusChart a p c hr).source) (v w : ℂ × (ι → ℂ)) :
    ((a • OnePoint.fubiniStudyForm).prod (torusSymplecticForm p)).eval₂
        (sphereTorusChart a p c hr z)
        (mfderiv (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ι → ℂ))
          (𝓘(ℝ, ℂ).prod (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)))
          (sphereTorusChart a p c hr) z v)
        (mfderiv (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ι → ℂ))
          (𝓘(ℝ, ℂ).prod (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)))
          (sphereTorusChart a p c hr) z w) =
      stdComplexSymplecticForm.prod (stdComplexPiSymplecticForm ι) v w := by
  rw [sphereTorusChart_source c hr ha] at hz
  have hz₁ : z.1 ∈ (OnePoint.areaDiscChart a).target := by
    rw [OnePoint.areaDiscChart_target ha]
    exact hz.1
  -- The chart is the product map of its two factors, so its derivative acts componentwise.
  have hmap : ⇑(sphereTorusChart a p c hr) =
      Prod.map (OnePoint.areaDiscChart a).symm (complexPiTorusCover p) :=
    funext (sphereTorusChart_apply c hr)
  have hd₁ := (OnePoint.areaDiscChart a).symm.mdifferentiableAt (by simp) hz₁
  have hd₂ := (contMDiff_complexPiTorusCover p (n := 1)).mdifferentiable one_ne_zero z.2
  rw [hmap, mfderiv_prodMap hd₁ hd₂, SmoothTwoForm.eval₂_prod, SymplecticForm.prod_apply]
  rw [Manifold.tangentSpaceProdEquiv_apply, Manifold.tangentSpaceProdEquiv_apply]
  -- The derivative of the product map acts on each component by the factor derivatives.
  exact congrArg₂ (· + ·)
    (OnePoint.eval₂_smul_fubiniStudyForm_mfderiv_areaDiscChart_symm ha
      ((OnePoint.mem_areaDiscChart_target ha).1 hz₁) v.1 w.1)
    (eval₂_torusSymplecticForm_mfderiv_complexPiTorusCover p z.2 v.2 w.2)

end Product

/-! ### The embedding on complex Euclidean space -/

section Euclidean

variable {m : ℕ}

variable (a : ℝ) (p : Fin m ⊕ Fin m → ℝ) [∀ i, Fact (0 < p i)]

/-- **The symplectic embedding of a piece of the cylinder into `S²(a) × T`.** On complex Euclidean
space `ℂᵐ⁺¹`, the map `x ↦ (φ⁻¹ (x 0), ρ (x (i + 1))ᵢ)`, where `φ` is the disc chart of the sphere
of area `a` and `ρ = TauCeti.complexPiTorusCover p` the covering map of the torus, as a partial
diffeomorphism. For `a > 0` it is defined where `|x 0| < √(a / π)` and `(x (i + 1))ᵢ` lies in the
ball of radius `r` about `c` (`TauCeti.mem_euclideanSphereTorusChart_source`), and it pulls the
product form `a • ω_FS ⊕ ω_T` back to the standard symplectic form `Im ⟪v, w⟫`
(`TauCeti.eval₂_mfderiv_euclideanSphereTorusChart`). It is the splitting
`EuclideanSpace.consPiEquivL` of `ℂᵐ⁺¹` into `ℂ × ℂᵐ` followed by `TauCeti.sphereTorusChart`. -/
def euclideanSphereTorusChart (c : Fin m → ℂ) {r : ℝ} (hr : ∀ i, 2 * r ≤ p i) :
    PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin (m + 1)))
      (𝓘(ℝ, ℂ).prod (ModelWithCorners.pi fun _ : Fin m ⊕ Fin m ↦ 𝓘(ℝ)))
      (EuclideanSpace ℂ (Fin (m + 1))) (OnePoint ℂ × ∀ i, AddCircle (p i)) ∞ :=
  (EuclideanSpace.consPiEquivL ℂ ℝ m).symm.toPartialDiffeomorphProd.trans
    (sphereTorusChart a p c hr)

variable {a p} (c : Fin m → ℂ) {r : ℝ} (hr : ∀ i, 2 * r ≤ p i)

/-- The chart sends `x` to `(φ⁻¹ (x 0), ρ (x (i + 1))ᵢ)`, where `φ` is the disc chart of the
sphere and `ρ` the covering map of the torus. -/
@[simp]
theorem euclideanSphereTorusChart_apply (x : EuclideanSpace ℂ (Fin (m + 1))) :
    euclideanSphereTorusChart a p c hr x =
      ((OnePoint.areaDiscChart a).symm (x 0), complexPiTorusCover p fun i ↦ x i.succ) := by
  simp [euclideanSphereTorusChart]

/-- For `a > 0`, a point `x` lies in the source of the chart exactly when `|x 0| < √(a / π)` and
`(x (i + 1))ᵢ` lies in the ball of radius `r` about `c`. -/
theorem mem_euclideanSphereTorusChart_source (ha : 0 < a) {x : EuclideanSpace ℂ (Fin (m + 1))} :
    x ∈ (euclideanSphereTorusChart a p c hr).source ↔
      ‖x 0‖ < √(a / Real.pi) ∧ (fun i ↦ x i.succ) ∈ ball c r := by
  simp [euclideanSphereTorusChart, sphereTorusChart_source c hr ha]

/-- The target of the chart is the product of the sphere minus `∞` with the image of the ball under
the covering map of the torus. -/
@[simp]
theorem euclideanSphereTorusChart_target :
    (euclideanSphereTorusChart a p c hr).target =
      {(OnePoint.infty : OnePoint ℂ)}ᶜ ×ˢ (complexPiTorusCover p '' ball c r) := by
  simp [euclideanSphereTorusChart]

/-- **The chart is symplectic.** For `a > 0`, at every point of its source the chart pulls the
product form `a • ω_FS ⊕ ω_T` of `S²(a) × T` back to the standard symplectic form `Im ⟪v, w⟫` of
`ℂᵐ⁺¹`. -/
theorem eval₂_mfderiv_euclideanSphereTorusChart (ha : 0 < a) {x : EuclideanSpace ℂ (Fin (m + 1))}
    (hx : x ∈ (euclideanSphereTorusChart a p c hr).source) (v w : EuclideanSpace ℂ (Fin (m + 1))) :
    ((a • OnePoint.fubiniStudyForm).prod (torusSymplecticForm p)).eval₂
        (euclideanSphereTorusChart a p c hr x)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin (m + 1)))
          (𝓘(ℝ, ℂ).prod (ModelWithCorners.pi fun _ : Fin m ⊕ Fin m ↦ 𝓘(ℝ)))
          (euclideanSphereTorusChart a p c hr) x v)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin (m + 1)))
          (𝓘(ℝ, ℂ).prod (ModelWithCorners.pi fun _ : Fin m ⊕ Fin m ↦ 𝓘(ℝ)))
          (euclideanSphereTorusChart a p c hr) x w) =
      (⟪v, w⟫_ℂ).im := by
  -- The splitting `ℂᵐ⁺¹ ≅ ℂ × ℂᵐ` underlying the chart.
  set L := (EuclideanSpace.consPiEquivL ℂ ℝ m).symm
  have hL (u : EuclideanSpace ℂ (Fin (m + 1))) : L u = (u 0, fun i ↦ u i.succ) :=
    EuclideanSpace.consPiEquivL_symm_apply u
  have hchart : euclideanSphereTorusChart a p c hr =
      L.toPartialDiffeomorphProd.trans (sphereTorusChart a p c hr) :=
    rfl
  have hLd := L.hasMFDerivAt_toPartialDiffeomorphProd (n := ∞) x
  rw [ContinuousLinearEquiv.coe_toPartialDiffeomorphProd] at hLd
  have hx' : L x ∈ (sphereTorusChart a p c hr).source := by
    rw [hchart, PartialDiffeomorph.trans_source,
      ContinuousLinearEquiv.coe_toPartialDiffeomorphProd] at hx
    exact hx.2
  -- The chain rule through the splitting.
  have hcomp (u : EuclideanSpace ℂ (Fin (m + 1))) :
      mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin (m + 1)))
          (𝓘(ℝ, ℂ).prod (ModelWithCorners.pi fun _ : Fin m ⊕ Fin m ↦ 𝓘(ℝ)))
          (euclideanSphereTorusChart a p c hr) x u =
        mfderiv (𝓘(ℝ, ℂ).prod 𝓘(ℝ, Fin m → ℂ))
          (𝓘(ℝ, ℂ).prod (ModelWithCorners.pi fun _ : Fin m ⊕ Fin m ↦ 𝓘(ℝ)))
          (sphereTorusChart a p c hr) (L x) (L u) := by
    rw [hchart, PartialDiffeomorph.coe_trans, ContinuousLinearEquiv.coe_toPartialDiffeomorphProd,
      mfderiv_comp x ((sphereTorusChart a p c hr).mdifferentiableAt (by simp) hx')
        hLd.mdifferentiableAt, hLd.mfderiv]
    -- `rw` cannot use this lemma: the tangent spaces of the intermediate manifold `ℂ × ℂᵐ` and the
    -- model space `ℂ × ℂᵐ` are only definitionally equal.
    exact ContinuousLinearMap.comp_apply _ _ _
  have hpt : euclideanSphereTorusChart a p c hr x = sphereTorusChart a p c hr (L x) := by
    rw [hchart, PartialDiffeomorph.coe_trans, ContinuousLinearEquiv.coe_toPartialDiffeomorphProd,
      Function.comp_apply]
  rw [hcomp, hcomp, hpt]
  refine (eval₂_mfderiv_sphereTorusChart c hr ha hx' _ _).trans ?_
  simp only [SymplecticForm.prod_apply, hL, stdComplexSymplecticForm_apply,
    stdComplexPiSymplecticForm_apply, PiLp.inner_apply, Fin.sum_univ_succ, Complex.add_im,
    Complex.im_sum]
  congr 1
  · simp [Complex.mul_im]
    ring
  · exact Finset.sum_congr rfl fun i _ ↦ by simp [Complex.mul_im]; ring

/-- **Bounded pieces of the cylinder lie in the source for large periods.** If `s ⊆ ℂᵐ⁺¹` is bounded
and `|x 0| < R` for every `x ∈ s`, with `π R² ≤ a`, then there is a radius `r` such that `s` lies in
the source of `TauCeti.euclideanSphereTorusChart a p 0 hr` for all periods `p i ≥ 2 r`. -/
theorem exists_forall_subset_euclideanSphereTorusChart_source
    {s : Set (EuclideanSpace ℂ (Fin (m + 1)))} (hs : Bornology.IsBounded s) {R : ℝ}
    (hR : Real.pi * R ^ 2 ≤ a) (hsR : ∀ x ∈ s, ‖x 0‖ < R) :
    ∃ r : ℝ, ∀ (p : Fin m ⊕ Fin m → ℝ) [∀ i, Fact (0 < p i)] (hr : ∀ i, 2 * r ≤ p i),
      s ⊆ (euclideanSphereTorusChart a p 0 hr).source := by
  obtain ⟨C, hC⟩ := hs.exists_norm_le
  refine ⟨max C 0 + 1, fun p _ hr x hx ↦ ?_⟩
  have hR₀ : 0 < R := (norm_nonneg _).trans_lt (hsR x hx)
  have ha : 0 < a := (by positivity : 0 < Real.pi * R ^ 2).trans_le hR
  refine (mem_euclideanSphereTorusChart_source 0 hr ha).2 ⟨(hsR x hx).trans_le ?_, ?_⟩
  · exact Real.le_sqrt_of_sq_le ((le_div_iff₀' Real.pi_pos).2 hR)
  · rw [mem_ball_zero_iff]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (norm_nonneg x)).2
      fun i ↦ PiLp.norm_apply_le x i.succ) ?_
    linarith [hC x hx, le_max_left C 0]

end Euclidean

end TauCeti
