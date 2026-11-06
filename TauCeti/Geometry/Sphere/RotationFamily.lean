/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Analysis.InnerProductSpace.Sphere.Trigonometric
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import TauCeti.Geometry.Manifold.RegularValue

/-!
# The rotation family of great circles through a point of a sphere

Fix a point `p` of the unit sphere `Sⁿ` of a real inner product space `E` of dimension `n + 1`.
Read in `E`, the tangent space of `Sⁿ` at `p` is the orthogonal complement `(ℝ ∙ p)ᗮ`
(Mathlib's `range_mvfderiv_subtypeVal`), an inner product space of dimension `n`. So the unit
tangent vectors at `p` form the unit sphere `T¹_p Sⁿ` of `(ℝ ∙ p)ᗮ`, an `(n - 1)`-sphere with its
own stereographic manifold structure.

The **rotation family** at `p` is the map

`R : T¹_p Sⁿ × S¹ → Sⁿ`, `R (v, θ) = cos θ • p + sin θ • v`,

with `S¹ = ℝ ⧸ 2πℤ` (`TauCeti.sphereRotationFamily`). For fixed `v` it runs once around the great
circle through `p` in the direction `v`; every great circle through `p` arises twice, from `v` and
from `-v`. This map, of a closed `n`-manifold to `Sⁿ`, has degree `1 + (-1) ^ (n - 1)`, that is `2`
for odd `n` and `0` for even `n`. This file proves the following facts about `R`, on which that
computation rests; the degree itself is not computed here.

* `R` is smooth (`TauCeti.contMDiff_sphereRotationFamily`).
* `R` is invariant under the involution `(v, θ) ↦ (-v, -θ)`
  (`TauCeti.sphereRotationFamily_neg_neg`).
* `R` sends `(v, θ)` to `p` exactly when `θ = 0` and to `-p` exactly when `θ = π`.
* Over a point `q ≠ ±p`, the fibre of `R` consists of exactly two points, exchanged by the
  involution (`TauCeti.preimage_sphereRotationFamily_singleton`,
  `TauCeti.ncard_preimage_sphereRotationFamily_singleton`).
* Every point `q ≠ ±p` is a regular value of `R`
  (`TauCeti.isRegularValue_sphereRotationFamily`).

So over such `q` the degree is the sum of the orientation signs of `R` at the two preimages, which
differ by the orientation sign of the involution: the antipodal map of `S^(n-1)` times the
reflection `θ ↦ -θ` of the circle.

## Main definitions

* `TauCeti.sphereRotationFamily p`: the rotation family `T¹_p Sⁿ × S¹ → Sⁿ` at `p`.

## Main results

* `TauCeti.coe_sphereRotationFamily`, `TauCeti.coe_sphereRotationFamily_coe`: the formula for `R`,
  and on a real angle `t`, `R (v, t) = cos t • p + sin t • v`.
* `TauCeti.contMDiff_sphereRotationFamily`: the rotation family is smooth.
* `TauCeti.sphereRotationFamily_neg_neg`: it is invariant under `(v, θ) ↦ (-v, -θ)`.
* `TauCeti.sphereRotationFamily_eq_self_iff`, `TauCeti.sphereRotationFamily_eq_neg_self_iff`: its
  values `p` and `-p`.
* `TauCeti.surjective_sphereRotationFamily`: it is surjective.
* `TauCeti.sphereRotationFamily_eq_iff`, `TauCeti.preimage_sphereRotationFamily_singleton`,
  `TauCeti.ncard_preimage_sphereRotationFamily_singleton`: its fibre over a point other than `±p`
  is a pair of points exchanged by the involution.
* `TauCeti.isRegularPoint_sphereRotationFamily`, `TauCeti.isRegularValue_sphereRotationFamily`:
  every point mapped to neither `p` nor `-p` is a regular point, and every point other than `±p`
  is a regular value.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.3, second proof of
  Proposition 6.34.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
-/

public section

noncomputable section

open Metric Module Real Set Function
open scoped RealInnerProductSpace Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : sphere (0 : E) 1)

/-! ### The rotation family -/

/-- A unit vector orthogonal to `p` and the point `p` are orthonormal, so `cos t • p + sin t • v`
lies on the unit sphere. -/
private theorem cos_smul_add_sin_smul_mem_sphere (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) (t : ℝ) :
    cos t • (p : E) + sin t • ((v : (ℝ ∙ (p : E))ᗮ) : E) ∈ sphere (0 : E) 1 := by
  have hv : ((v : (ℝ ∙ (p : E))ᗮ) : E) ∈ sphere (0 : E) 1 := by
    simp [Submodule.norm_coe]
  have hpv : ⟪(p : E), ((v : (ℝ ∙ (p : E))ᗮ) : E)⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.1 (v : (ℝ ∙ (p : E))ᗮ).2
  simpa using norm_cos_smul_add_sin_smul p ⟨_, hv⟩ hpv t

/-- The **rotation family** at a point `p` of the unit sphere `Sⁿ ⊆ E`:
`(v, θ) ↦ cos θ • p + sin θ • v`, for `v` a unit vector orthogonal to `p` (a unit tangent vector of
`Sⁿ` at `p`) and `θ ∈ ℝ ⧸ 2πℤ`. For fixed `v` it is the great circle through `p` with initial
velocity `v`. -/
def sphereRotationFamily (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × AddCircle (2 * π)) :
    sphere (0 : E) 1 :=
  ⟨cos_periodic.lift x.2 • (p : E) + sin_periodic.lift x.2 • ((x.1 : (ℝ ∙ (p : E))ᗮ) : E), by
    obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective x.2
    rw [← ht, Periodic.lift_coe, Periodic.lift_coe]
    exact cos_smul_add_sin_smul_mem_sphere p x.1 t⟩

/-- On a real angle `t`, the rotation family is `cos t • p + sin t • v`. -/
@[simp]
theorem coe_sphereRotationFamily_coe (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) (t : ℝ) :
    (sphereRotationFamily p (v, (t : AddCircle (2 * π))) : E) =
      cos t • (p : E) + sin t • ((v : (ℝ ∙ (p : E))ᗮ) : E) := by
  simp [sphereRotationFamily]

/-- The rotation family, with the cosine and sine of an angle of `ℝ ⧸ 2πℤ` read through their
periodic lifts. -/
theorem coe_sphereRotationFamily (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × AddCircle (2 * π)) :
    (sphereRotationFamily p x : E) =
      cos_periodic.lift x.2 • (p : E) + sin_periodic.lift x.2 • ((x.1 : (ℝ ∙ (p : E))ᗮ) : E) :=
  (rfl)

variable {p}

/-- The angle `0` of the rotation family is the point `p`. -/
@[simp]
theorem sphereRotationFamily_zero (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    sphereRotationFamily p (v, 0) = p := by
  ext
  simpa using coe_sphereRotationFamily_coe p v 0

/-- The angle `π` of the rotation family is the antipode `-p`. -/
@[simp]
theorem sphereRotationFamily_pi (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    sphereRotationFamily p (v, (π : AddCircle (2 * π))) = -p := by
  ext
  simp

/-- The rotation family is invariant under the involution `(v, θ) ↦ (-v, -θ)`: the great circle
through `p` in the direction `-v`, traversed backwards, is the one in the direction `v`. -/
@[simp]
theorem sphereRotationFamily_neg_neg (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)
    (θ : AddCircle (2 * π)) :
    sphereRotationFamily p (-v, -θ) = sphereRotationFamily p (v, θ) := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  rw [← AddCircle.coe_neg]
  ext
  rw [coe_sphereRotationFamily_coe, coe_sphereRotationFamily_coe]
  simp

/-- The inner product of a value of the rotation family with `p` is the cosine of the angle. -/
theorem inner_sphereRotationFamily_coe (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) (t : ℝ) :
    ⟪(p : E), sphereRotationFamily p (v, (t : AddCircle (2 * π)))⟫ = cos t := by
  have hpv : ⟪(p : E), ((v : (ℝ ∙ (p : E))ᗮ) : E)⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.1 (v : (ℝ ∙ (p : E))ᗮ).2
  have hp : ⟪(p : E), (p : E)⟫ = 1 := by simp
  rw [coe_sphereRotationFamily_coe, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, hpv, hp]
  ring

/-- Away from `±p`, the sine of the angle of the rotation family is nonzero. -/
private theorem sin_ne_zero_of_sphereRotationFamily_ne {v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1}
    {t : ℝ} (hp : sphereRotationFamily p (v, (t : AddCircle (2 * π))) ≠ p)
    (hn : sphereRotationFamily p (v, (t : AddCircle (2 * π))) ≠ -p) : sin t ≠ 0 := by
  intro ht
  have hc : cos t = 1 ∨ cos t = -1 := by
    have := cos_sq_add_sin_sq t
    rw [ht] at this
    exact sq_eq_one_iff.1 (by linarith)
  rcases hc with hc | hc
  · exact hp (Subtype.ext (by simp [hc, ht]))
  · exact hn (Subtype.ext (by simp [hc, ht]))

/-- The rotation family takes the value `p` exactly at the angle `0`. -/
theorem sphereRotationFamily_eq_self_iff {x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × AddCircle (2 * π)} :
    sphereRotationFamily p x = p ↔ x.2 = 0 := by
  obtain ⟨v, θ⟩ := x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  refine ⟨fun h ↦ ?_, fun h ↦ by simp only at h; simp [h]⟩
  have hc : cos t = 1 := by
    rw [← inner_sphereRotationFamily_coe v t, h]
    simp
  obtain ⟨k, hk⟩ := (cos_eq_one_iff t).1 hc
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨k, by simpa [zsmul_eq_mul] using hk⟩

/-- The rotation family takes the value `-p` exactly at the angle `π`. -/
theorem sphereRotationFamily_eq_neg_self_iff
    {x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × AddCircle (2 * π)} :
    sphereRotationFamily p x = -p ↔ x.2 = (π : AddCircle (2 * π)) := by
  obtain ⟨v, θ⟩ := x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  refine ⟨fun h ↦ ?_, fun h ↦ by simp only at h; simp [h]⟩
  have hc : cos (t - π) = 1 := by
    rw [cos_sub_pi, ← inner_sphereRotationFamily_coe v t, h]
    simp
  obtain ⟨k, hk⟩ := (cos_eq_one_iff _).1 hc
  have h0 : ((t - π : ℝ) : AddCircle (2 * π)) = 0 :=
    (AddCircle.coe_eq_zero_iff _).2 ⟨k, by simpa [zsmul_eq_mul] using hk⟩
  rw [AddCircle.coe_sub, sub_eq_zero] at h0
  exact h0

/-! ### The fibres -/

/-- **The fibres of the rotation family.** Over a point other than `±p`, which is the value of the
rotation family at `x₀`, the rotation family takes that value exactly at `x₀` and at its image
`(-v₀, -θ₀)` under the involution. -/
theorem sphereRotationFamily_eq_iff {x x₀ : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × AddCircle (2 * π)}
    (hp : sphereRotationFamily p x₀ ≠ p) (hn : sphereRotationFamily p x₀ ≠ -p) :
    sphereRotationFamily p x = sphereRotationFamily p x₀ ↔ x = x₀ ∨ x = (-x₀.1, -x₀.2) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  swap
  · rintro (rfl | rfl)
    · rfl
    · exact sphereRotationFamily_neg_neg _ _
  obtain ⟨v, θ⟩ := x
  obtain ⟨v₀, θ₀⟩ := x₀
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  obtain ⟨t₀, rfl⟩ := QuotientAddGroup.mk_surjective θ₀
  have hs₀ := sin_ne_zero_of_sphereRotationFamily_ne hp hn
  have hc : cos t = cos t₀ := by
    rw [← inner_sphereRotationFamily_coe v t, ← inner_sphereRotationFamily_coe v₀ t₀, h]
  -- The components orthogonal to `p` agree: `sin t • v = sin t₀ • v₀`.
  have hE := congrArg Subtype.val h
  rw [coe_sphereRotationFamily_coe, coe_sphereRotationFamily_coe, hc, add_right_inj] at hE
  -- `Real.Angle` is by definition `ℝ ⧸ 2πℤ`, so angles with the same cosine agree up to sign.
  rcases (Real.Angle.cos_eq_iff_coe_eq_or_eq_neg.1 hc :
    (t : AddCircle (2 * π)) = t₀ ∨ (t : AddCircle (2 * π)) = -(t₀ : AddCircle (2 * π))) with ht | ht
  · have hs : sin t = sin t₀ := by
      rw [← Periodic.lift_coe sin_periodic t, ← Periodic.lift_coe sin_periodic t₀]
      exact congrArg _ ht
    rw [hs] at hE
    left
    refine Prod.ext (Subtype.ext (Subtype.ext ?_)) ht
    exact smul_right_injective E hs₀ hE
  · have hs : sin t = -sin t₀ := by
      rw [← Periodic.lift_coe sin_periodic t, ← sin_neg, ← Periodic.lift_coe sin_periodic (-t₀),
        AddCircle.coe_neg]
      exact congrArg _ ht
    rw [hs, neg_smul, ← smul_neg] at hE
    right
    refine Prod.ext (Subtype.ext (Subtype.ext ?_)) ht
    simpa [neg_eq_iff_eq_neg] using smul_right_injective E hs₀ hE

/-- Every point other than `±p` is the value of the rotation family at the point
`(v, arccos ⟪p, q⟫)`, where `v` is the normalized component of `q` orthogonal to `p`. -/
private theorem exists_sphereRotationFamily_eq {q : sphere (0 : E) 1} (hp : q ≠ p)
    (hn : q ≠ -p) : ∃ x, sphereRotationFamily p x = q := by
  set c := ⟪(p : E), (q : E)⟫
  set w : E := (q : E) - c • (p : E)
  have hpp : ⟪(p : E), (p : E)⟫ = 1 := by simp
  have hqq : ⟪(q : E), (q : E)⟫ = 1 := by simp
  have hw_mem : w ∈ (ℝ ∙ (p : E))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
      real_inner_smul_right, hpp]
    ring
  have hw_sq : ‖w‖ ^ 2 = 1 - c ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [w, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hpp, hqq, real_inner_comm (p : E) (q : E), c]
    ring
  -- `w ≠ 0`, since otherwise `q = c • p` with `c ^ 2 = 1`, so `q = ±p`.
  have hw0 : w ≠ 0 := by
    intro h0
    have hqc : (q : E) = c • (p : E) := sub_eq_zero.1 h0
    have hc : c ^ 2 = 1 := by
      have := hw_sq
      rw [h0, norm_zero] at this
      linarith
    rcases sq_eq_one_iff.1 hc with hc | hc
    · exact hp (Subtype.ext (by rw [hqc, hc, one_smul]))
    · exact hn (Subtype.ext (by rw [hqc, hc, neg_one_smul, coe_neg_sphere]))
  have hc1 : c ^ 2 < 1 := by
    have : 0 < ‖w‖ ^ 2 := by positivity
    linarith
  have hnw : ‖w‖ = √(1 - c ^ 2) := by
    rw [← hw_sq, sqrt_sq (norm_nonneg w)]
  let v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 :=
    ⟨‖w‖⁻¹ • ⟨w, hw_mem⟩, by
      simp [norm_smul, ← Submodule.norm_coe, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw0)]⟩
  refine ⟨(v, (arccos c : AddCircle (2 * π))), Subtype.ext ?_⟩
  rw [coe_sphereRotationFamily_coe, cos_arccos (by nlinarith) (by nlinarith), sin_arccos, ← hnw]
  simp only [v, Submodule.coe_smul, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hw0),
    one_smul, w, add_sub_cancel]

/-- **The fibre of the rotation family over a point other than `±p`** consists of a point `x` and
its image `(-v, -θ)` under the involution, and these two points are distinct. -/
theorem preimage_sphereRotationFamily_singleton {q : sphere (0 : E) 1} (hp : q ≠ p)
    (hn : q ≠ -p) :
    ∃ x, sphereRotationFamily p ⁻¹' {q} = {x, (-x.1, -x.2)} ∧ (-x.1, -x.2) ≠ x := by
  obtain ⟨x, rfl⟩ := exists_sphereRotationFamily_eq hp hn
  refine ⟨x, ?_, fun h ↦ ?_⟩
  · ext y
    simp [sphereRotationFamily_eq_iff hp hn]
  · -- A unit vector is not its own negative.
    have h1 := congrArg (fun y ↦ ((y.1 : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) : (ℝ ∙ (p : E))ᗮ)) h
    simp only [coe_neg_sphere] at h1
    have h0 : (x.1 : (ℝ ∙ (p : E))ᗮ) = 0 := by
      have h2 : (2 : ℝ) • (x.1 : (ℝ ∙ (p : E))ᗮ) = 0 := by
        rw [two_smul]
        nth_rw 1 [← h1]
        exact neg_add_cancel _
      exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
    have := norm_eq_of_mem_sphere x.1
    rw [h0, norm_zero] at this
    exact zero_ne_one this

/-- The fibre of the rotation family over a point other than `±p` has exactly two points. -/
theorem ncard_preimage_sphereRotationFamily_singleton {q : sphere (0 : E) 1} (hp : q ≠ p)
    (hn : q ≠ -p) : (sphereRotationFamily p ⁻¹' {q}).ncard = 2 := by
  obtain ⟨x, hx, hne⟩ := preimage_sphereRotationFamily_singleton hp hn
  rw [hx, ncard_pair hne.symm]

/-! ### Smoothness and regular values -/

local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

variable {m : ℕ} [Fact (finrank ℝ E = m + 1 + 1)]

/-- The orthogonal complement of a point of the unit sphere `S^(m+1)` has dimension `m + 1`, so its
unit sphere, the unit tangent sphere at that point, is an `m`-sphere. -/
instance fact_finrank_orthogonal_span_singleton (p : sphere (0 : E) 1) :
    Fact (finrank ℝ (ℝ ∙ (p : E))ᗮ = m + 1) :=
  ⟨Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)⟩

/-- The ambient expression `(w, t) ↦ cos t • p + sin t • w` of the rotation family, on
`(ℝ ∙ p)ᗮ × ℝ`. -/
private def rotationAmbient (p : sphere (0 : E) 1) (y : (ℝ ∙ (p : E))ᗮ × ℝ) : E :=
  cos y.2 • (p : E) + sin y.2 • (y.1 : E)

omit [Fact (finrank ℝ E = m + 1 + 1)] in
/-- The derivative of the ambient rotation family at `(w, t)`:
`(δw, δt) ↦ δt • (-sin t • p + cos t • w) + sin t • δw`. -/
private theorem hasFDerivAt_rotationAmbient (y : (ℝ ∙ (p : E))ᗮ × ℝ) :
    HasFDerivAt (rotationAmbient p)
      (sin y.2 • ((ℝ ∙ (p : E))ᗮ.subtypeL.comp (ContinuousLinearMap.fst ℝ _ ℝ)) +
        (ContinuousLinearMap.snd ℝ (ℝ ∙ (p : E))ᗮ ℝ).smulRight
          (-sin y.2 • (p : E) + cos y.2 • (y.1 : E))) y := by
  have hcos : HasFDerivAt (fun y : (ℝ ∙ (p : E))ᗮ × ℝ ↦ cos y.2)
      (-sin y.2 • ContinuousLinearMap.snd ℝ (ℝ ∙ (p : E))ᗮ ℝ) y :=
    (hasDerivAt_cos y.2).comp_hasFDerivAt y hasFDerivAt_snd
  have hsin : HasFDerivAt (fun y : (ℝ ∙ (p : E))ᗮ × ℝ ↦ sin y.2)
      (cos y.2 • ContinuousLinearMap.snd ℝ (ℝ ∙ (p : E))ᗮ ℝ) y :=
    (hasDerivAt_sin y.2).comp_hasFDerivAt y hasFDerivAt_snd
  have hw : HasFDerivAt (fun y : (ℝ ∙ (p : E))ᗮ × ℝ ↦ (y.1 : E))
      ((ℝ ∙ (p : E))ᗮ.subtypeL.comp (ContinuousLinearMap.fst ℝ _ ℝ)) y :=
    ((ℝ ∙ (p : E))ᗮ.subtypeL.comp (ContinuousLinearMap.fst ℝ _ ℝ)).hasFDerivAt
  refine ((hcos.smul_const (p : E)).add (hsin.smul hw)).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun z ↦ ?_
  simp
  module

omit [Fact (finrank ℝ E = m + 1 + 1)] in
/-- Where `sin t ≠ 0`, the derivative of the ambient rotation family is injective: its component
along `p` recovers `δt`, and then `sin t • δw` recovers `δw`. -/
private theorem injective_fderiv_rotationAmbient {y : (ℝ ∙ (p : E))ᗮ × ℝ} (hy : sin y.2 ≠ 0) :
    Injective (fderiv ℝ (rotationAmbient p) y) := by
  rw [(hasFDerivAt_rotationAmbient y).fderiv, injective_iff_map_eq_zero]
  rintro ⟨δw, δt⟩ h
  simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
    ContinuousLinearMap.coe_comp, comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd',
    Submodule.subtypeL_apply] at h
  have hpw : ∀ u : (ℝ ∙ (p : E))ᗮ, ⟪(p : E), (u : E)⟫ = 0 := fun u ↦
    Submodule.mem_orthogonal_singleton_iff_inner_right.1 u.2
  have hpp : ⟪(p : E), (p : E)⟫ = 1 := by simp
  have hip := congrArg (fun z ↦ ⟪(p : E), z⟫) h
  simp only [inner_add_right, real_inner_smul_right, hpw, hpp, inner_zero_right] at hip
  have hδt : δt = 0 := by
    have : δt * sin y.2 = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hy
  subst hδt
  simp only [zero_smul, add_zero, smul_eq_zero, hy, false_or, ZeroMemClass.coe_eq_zero] at h
  simpa using h

/-- On real angles, the rotation family read in `E` is the ambient rotation family. -/
private theorem coe_comp_sphereRotationFamily_comp_coe :
    ((↑) : sphere (0 : E) 1 → E) ∘ sphereRotationFamily p ∘
        Prod.map id ((↑) : ℝ → AddCircle (2 * π)) =
      rotationAmbient p ∘ Prod.map ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → _) id := by
  ext ⟨v, t⟩
  simp [rotationAmbient]

/-- The rotation family read on real angles is smooth. -/
private theorem contMDiff_sphereRotationFamily_comp_coe {n : ℕ∞ω} :
    ContMDiff ((𝓡 m).prod 𝓘(ℝ)) (𝓡 (m + 1)) n
      (sphereRotationFamily p ∘ Prod.map id ((↑) : ℝ → AddCircle (2 * π))) := by
  have hE : ContMDiff ((𝓡 m).prod 𝓘(ℝ)) 𝓘(ℝ, E) n
      (fun y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × ℝ ↦ rotationAmbient p ((y.1 : _), y.2)) := by
    have hF : ContDiff ℝ n (rotationAmbient p) :=
      ((contDiff_cos.comp contDiff_snd).smul contDiff_const).add
        ((contDiff_sin.comp contDiff_snd).smul
          ((ℝ ∙ (p : E))ᗮ.subtypeL.contDiff.comp contDiff_fst))
    exact hF.contMDiff.comp ((contMDiff_coe_sphere.comp contMDiff_fst).prodMk_space contMDiff_snd)
  convert hE.codRestrict_sphere (fun y ↦ cos_smul_add_sin_smul_mem_sphere p y.1 y.2) using 1
  ext y
  exact congrFun (coe_comp_sphereRotationFamily_comp_coe (p := p)) y

/-- **The rotation family is smooth.** -/
theorem contMDiff_sphereRotationFamily {n : ℕ∞ω} :
    ContMDiff ((𝓡 m).prod 𝓘(ℝ)) (𝓡 (m + 1)) n (sphereRotationFamily p) :=
  ((AddCircle.isLocalDiffeomorph_coe (2 * π) n).contMDiff_comp_prodMap_iff
    QuotientAddGroup.mk_surjective le_rfl).1 contMDiff_sphereRotationFamily_comp_coe

/-- Where `sin t ≠ 0`, the rotation family read on real angles has injective derivative at `(v, t)`:
read in `E`, it is the derivative of the ambient rotation family composed with that of the
inclusion of the unit tangent sphere, and both are injective. -/
private theorem injective_mfderiv_sphereRotationFamily_comp_coe
    {v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1} {t : ℝ} (hs : sin t ≠ 0) :
    Injective (mfderiv ((𝓡 m).prod 𝓘(ℝ)) (𝓡 (m + 1))
      (sphereRotationFamily p ∘ Prod.map id ((↑) : ℝ → AddCircle (2 * π))) (v, t)) := by
  have hcoe : MDifferentiableAt (𝓡 m) 𝓘(ℝ, (ℝ ∙ (p : E))ᗮ)
      ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → (ℝ ∙ (p : E))ᗮ) v :=
    contMDiff_coe_sphere.mdifferentiableAt (n := 1) one_ne_zero
  have hψ : MDifferentiableAt ((𝓡 m).prod 𝓘(ℝ)) (𝓘(ℝ, (ℝ ∙ (p : E))ᗮ).prod 𝓘(ℝ))
      (Prod.map ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → (ℝ ∙ (p : E))ᗮ) (id : ℝ → ℝ)) (v, t) :=
    hcoe.prodMap mdifferentiableAt_id
  have hF : HasMFDerivAt (𝓘(ℝ, (ℝ ∙ (p : E))ᗮ).prod 𝓘(ℝ)) 𝓘(ℝ, E) (rotationAmbient p)
      ((v : (ℝ ∙ (p : E))ᗮ), t) (fderiv ℝ (rotationAmbient p) ((v : (ℝ ∙ (p : E))ᗮ), t)) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (hasFDerivAt_rotationAmbient _).differentiableAt.hasFDerivAt.hasMFDerivAt
  have hinjψ : Injective (mfderiv ((𝓡 m).prod 𝓘(ℝ)) (𝓘(ℝ, (ℝ ∙ (p : E))ᗮ).prod 𝓘(ℝ))
      (Prod.map ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → (ℝ ∙ (p : E))ᗮ) (id : ℝ → ℝ)) (v, t)) := by
    have h₁ := injective_mvfderiv_subtypeVal_sphere (n := m) v
    rw [mvfderiv, ContinuousLinearMap.coe_comp] at h₁
    rw [mfderiv_prodMap (p := (v, t)) hcoe mdifferentiableAt_id, mfderiv_id]
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    -- The two components of `hab`, through the definition of `ContinuousLinearMap.prodMap`.
    exact Prod.ext (h₁.of_comp (congrArg (fun z : (ℝ ∙ (p : E))ᗮ × ℝ ↦ z.1) hab))
      (congrArg (fun z : (ℝ ∙ (p : E))ᗮ × ℝ ↦ z.2) hab)
  have hinjE : Injective (mfderiv ((𝓡 m).prod 𝓘(ℝ)) 𝓘(ℝ, E)
      (rotationAmbient p ∘ Prod.map ((↑) : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 → _) id) (v, t)) := by
    rw [(hF.comp (v, t) hψ.hasMFDerivAt).mfderiv, ContinuousLinearMap.coe_comp]
    exact (injective_fderiv_rotationAmbient (p := p) hs).comp hinjψ
  rw [← coe_comp_sphereRotationFamily_comp_coe, mfderiv_comp (v, t)
    ((contMDiff_coe_sphere (n := m + 1)).mdifferentiableAt (n := 1) one_ne_zero)
    ((contMDiff_sphereRotationFamily_comp_coe (n := 1)).mdifferentiableAt one_ne_zero),
    ContinuousLinearMap.coe_comp] at hinjE
  exact hinjE.of_comp

/-- **Regular points of the rotation family.** At a point not mapped to `±p`, that is, at an angle
other than `0` and `π`, the derivative of the rotation family is surjective. -/
theorem isRegularPoint_sphereRotationFamily
    {x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × AddCircle (2 * π)} (hp : sphereRotationFamily p x ≠ p)
    (hn : sphereRotationFamily p x ≠ -p) :
    IsRegularPoint ((𝓡 m).prod 𝓘(ℝ)) (𝓡 (m + 1)) (sphereRotationFamily p) x := by
  obtain ⟨v, θ⟩ := x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  -- An injective linear map between spaces of the same dimension `m + 1` is surjective.
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin m) × ℝ) =
      finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) := by
    simp
  have hsurj : Surjective (mfderiv ((𝓡 m).prod 𝓘(ℝ)) (𝓡 (m + 1))
      (sphereRotationFamily p ∘ Prod.map id ((↑) : ℝ → AddCircle (2 * π))) (v, t)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (mfderiv ((𝓡 m).prod 𝓘(ℝ)) (𝓡 (m + 1))
      (sphereRotationFamily p ∘ Prod.map id ((↑) : ℝ → AddCircle (2 * π))) (v, t) :
        EuclideanSpace ℝ (Fin m) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))).toLinearMap)).1
    (injective_mfderiv_sphereRotationFamily_comp_coe (sin_ne_zero_of_sphereRotationFamily_ne hp hn))
  -- The derivative of the rotation family read on real angles factors through that of `R`.
  rw [mfderiv_comp (v, t)
    ((contMDiff_sphereRotationFamily (n := 1)).mdifferentiableAt one_ne_zero)
    (mdifferentiableAt_id.prodMap (AddCircle.hasMFDerivAt_coe _ t).mdifferentiableAt),
    ContinuousLinearMap.coe_comp] at hsurj
  rw [isRegularPoint_iff]
  exact hsurj.of_comp

/-- **Regular values of the rotation family.** Every point other than `±p` is a regular value. -/
theorem isRegularValue_sphereRotationFamily {q : sphere (0 : E) 1} (hp : q ≠ p) (hn : q ≠ -p) :
    IsRegularValue ((𝓡 m).prod 𝓘(ℝ)) (𝓡 (m + 1)) (sphereRotationFamily p) q := by
  rw [isRegularValue_iff]
  rintro x rfl
  exact isRegularPoint_sphereRotationFamily hp hn

end TauCeti
