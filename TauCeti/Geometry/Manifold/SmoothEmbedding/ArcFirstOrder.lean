/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Sphere.Boost
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Concordance
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
import TauCeti.Analysis.InnerProductSpace.LinearIsometry
import TauCeti.Analysis.InnerProductSpace.Reflection
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Making a concordance standard to first order along an arc

Let `F : S¹ × ℝ → Sⁿ × ℝ` be a smooth concordance between circle embeddings `K` and `K'` into the
unit sphere `Sⁿ` of a real inner product space, with `n ≥ 3`, and let `L : S¹ → Sⁿ` be a loop with
which `K` and `K'` agree to first order at a point `z₀`. If `F` maps the line `{z₀} × ℝ` onto the
straight line `{L z₀} × ℝ`, then `F` can be replaced by a concordance `G` from `K` to `K'` which
still maps that line onto the straight line, and agrees with the strip `L × id` to first order
along it (`TauCeti.SmoothEmbedding.Concordance.exists_mfderiv_eq_prodMap`). For knots in
connected-sum position and `L` the great circle, this is the first-order normalization of a
concordance along the arc `{-i} × ℝ`, after which the concordance can be made the standard strip
near that arc.

Along the line, the derivative of `F` sends the time direction to the time direction, and the
circle direction to a vector `(A t, b t)` of `T_v Sⁿ × ℝ`, where `v = L z₀`, while the strip sends
it to `(W, 0)`. Three moves correct this, and none of them changes `F` near its two ends.

* A smooth family of linear isometries `Q t` fixing `v` turns the direction of `A t` into that of
  `W` (`TauCeti.exists_contDiff_linearIsometryEquiv_apply_eq`). Each `Q t` is a product of four
  hyperplane reflections, through an auxiliary unit vector orthogonal to `v` which avoids the
  antipodes of the directions of all the `A t`. Such a vector exists because the cone over a curve
  misses a point of a space of dimension at least three; this is where `n ≥ 3` is used.
* A smooth family of boosts toward `-v` (`TauCeti.sphereBoost`) fixes `v` and rescales the
  tangent vectors at `v` by `‖W‖ / ‖A t‖`. Applying `Q t` and then this boost at level `t` is a
  diffeomorphism of `Sⁿ × ℝ` preserving the levels (`TauCeti.boostRotateDiffeomorph`).
* The time shear `(z, t) ↦ (z, t - b t * h z)` of the source (`TauCeti.timeShear`), where `h` is a
  small function on the circle vanishing at `z₀` with velocity `1` there, cancels the time
  component `b t`.

The derivatives of the result and of `L × id` along the line are compared slice by slice along
`Circle.exp` (`TauCeti.mfderiv_eq_of_deriv_comp_circleExp_eq_prod`).

## Main definitions

* `TauCeti.timeShear β h`: the time shear `(x, t) ↦ (x, t + β t * h x)` of a cylinder `M × ℝ`.
* `TauCeti.boostRotate u α Q`: at level `s`, the linear isometry `Q s` followed by the boost of
  rapidity `α s` toward `u`.
* `TauCeti.boostRotateDiffeomorph`: the level-preserving diffeomorphism of `Sⁿ × ℝ` which
  `boostRotate` defines.

## Main results

* `TauCeti.SmoothEmbedding.Concordance.exists_mfderiv_eq_prodMap`: a concordance which maps the
  line over `z₀` onto the straight line can be made to agree with `L × id` to first order along
  it.
* `TauCeti.injective_timeShear`, `TauCeti.isProperMap_timeShear`, `TauCeti.isImmersion_timeShear`:
  a time shear with positive time derivative and bounded displacement is an injective proper
  immersion.
* `TauCeti.fderiv_boostRotate_apply_zero`: the derivative of `boostRotate` at its fixed point.
* `TauCeti.mfderiv_eq_of_deriv_comp_circleExp_eq_prod`: two maps of `S¹ × ℝ` into `Sⁿ × ℝ` which
  agree on a line `{z₀} × ℝ` have the same derivative at `(z₀, t)` when their slices at time `t`
  have the same velocity at `z₀` along `Circle.exp`.
* `TauCeti.deriv_coe_fst_comp_circleExp_ne_zero`: for such a map with injective derivative, the
  sphere component of the slice has nonzero velocity.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer (1976),
  Chapter 8, for concordances and isotopies of embeddings.
* J. F. P. Hudson, *Concordance, isotopy, and diffeotopy*, Ann. of Math. 91 (1970), 425–448.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Graduate Texts in Mathematics 175,
  Springer (1997), Chapter 1, for the connected sum of knots.
-/

public section

noncomputable section

open Set Function Filter Manifold Topology Metric
open scoped Manifold ContDiff

namespace TauCeti

/-! ### Time shears of a cylinder -/

section TimeShear

/-- The **time shear** `(x, t) ↦ (x, t + β t * h x)` of the cylinder `M × ℝ`. -/
def timeShear {M : Type*} (β : ℝ → ℝ) (h : M → ℝ) (p : M × ℝ) : M × ℝ :=
  (p.1, p.2 + β p.2 * h p.1)

/-- A time shear moves `(x, t)` to `(x, t + β t * h x)`. -/
@[simp]
theorem timeShear_apply {M : Type*} (β : ℝ → ℝ) (h : M → ℝ) (x : M) (t : ℝ) :
    timeShear β h (x, t) = (x, t + β t * h x) :=
  (rfl)

/-- For a fixed point `x`, the time coordinate of a time shear is strictly increasing in time when
its derivative `1 + β' t * h x` is positive. -/
theorem strictMono_timeShear_snd {M : Type*} {β : ℝ → ℝ} {h : M → ℝ} (hβ : Differentiable ℝ β)
    (hpos : ∀ x t, 0 < 1 + deriv β t * h x) (x : M) :
    StrictMono fun t => (timeShear β h (x, t)).2 := by
  refine strictMono_of_deriv_pos fun t => ?_
  have hd : HasDerivAt (fun t => t + β t * h x) (1 + deriv β t * h x) t :=
    (hasDerivAt_id t).add ((hβ t).hasDerivAt.mul_const (h x))
  simpa only [timeShear_apply] using hd.deriv ▸ hpos x t

/-- A time shear whose time derivative is positive is injective. -/
theorem injective_timeShear {M : Type*} {β : ℝ → ℝ} {h : M → ℝ} (hβ : Differentiable ℝ β)
    (hpos : ∀ x t, 0 < 1 + deriv β t * h x) : Injective (timeShear β h) := by
  rintro ⟨x, t⟩ ⟨x', t'⟩ he
  simp only [timeShear_apply, Prod.mk.injEq] at he
  obtain ⟨rfl, he⟩ := he
  exact Prod.ext rfl ((strictMono_timeShear_snd hβ hpos x).injective he)

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]

/-- A time shear of a cylinder over a compact space, with bounded displacement, is proper. -/
theorem isProperMap_timeShear [CompactSpace M] [T2Space M] {β : ℝ → ℝ} {h : M → ℝ}
    (hβ : Continuous β) (hh : Continuous h) {C : ℝ} (hC : ∀ x t, |β t * h x| ≤ C) :
    IsProperMap (timeShear β h) := by
  have hc : Continuous (timeShear β h) :=
    continuous_fst.prodMk (continuous_snd.add ((hβ.comp continuous_snd).mul (hh.comp
      continuous_fst)))
  refine isProperMap_iff_isCompact_preimage.2 ⟨hc, fun K hK => ?_⟩
  obtain ⟨a, ha⟩ := (hK.image continuous_snd).bddBelow
  obtain ⟨b, hb⟩ := (hK.image continuous_snd).bddAbove
  refine (isCompact_univ.prod (isCompact_Icc (a := a - C) (b := b + C))).of_isClosed_subset
    (hK.isClosed.preimage hc) ?_
  rintro ⟨x, t⟩ hp
  have hlo : a ≤ t + β t * h x := ha ⟨_, hp, rfl⟩
  have hhi : t + β t * h x ≤ b := hb ⟨_, hp, rfl⟩
  have := abs_le.1 (hC x t)
  exact ⟨mem_univ x, by linarith, by linarith⟩

/-- The time coordinate `(x, t) ↦ t + β t * h x` of a time shear by smooth `β` and `h` is
smooth. -/
private theorem contMDiff_timeShear_snd {β : ℝ → ℝ} {h : M → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hh : ContMDiff IM 𝓘(ℝ) ∞ h) :
    ContMDiff (IM.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ fun q : M × ℝ => q.2 + β q.2 * h q.1 := by
  have hm : ContMDiff (IM.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ fun q : M × ℝ => β q.2 • h q.1 :=
    (hβ.contMDiff.comp contMDiff_snd).smul (hh.comp contMDiff_fst)
  simp only [smul_eq_mul] at hm
  exact contMDiff_snd.add hm

/-- A time shear by smooth `β` and `h` is smooth. -/
theorem contMDiff_timeShear {β : ℝ → ℝ} {h : M → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hh : ContMDiff IM 𝓘(ℝ) ∞ h) :
    ContMDiff (IM.prod 𝓘(ℝ)) (IM.prod 𝓘(ℝ)) ∞ (timeShear β h) :=
  contMDiff_fst.prodMk (contMDiff_timeShear_snd hβ hh)

variable [IM.Boundaryless] [IsManifold IM ∞ M] in
/-- A smooth time shear whose time derivative `1 + β' t * h x` never vanishes is an immersion. -/
theorem isImmersion_timeShear [FiniteDimensional ℝ EM] {β : ℝ → ℝ} {h : M → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hh : ContMDiff IM 𝓘(ℝ) ∞ h) (hpos : ∀ x t, 1 + deriv β t * h x ≠ 0) :
    IsImmersion (IM.prod 𝓘(ℝ)) (IM.prod 𝓘(ℝ)) ∞ (timeShear β h) := by
  refine isImmersion_iff_forall_isImmersionAt.2 fun q => ?_
  refine (contMDiff_timeShear_snd hβ hh).isImmersionAt_fst_prod (by simp) ?_
  refine IsDiffImmersionAt.of_injective_of_finiteDimensional ?_
  have hd : HasDerivAt (fun t => t + β t * h q.1) (1 + deriv β q.2 * h q.1) q.2 :=
    (hasDerivAt_id q.2).add ((hβ.differentiable (by simp) q.2).hasDerivAt.mul_const (h q.1))
  rw [mfderiv_eq_fderiv, hd.hasFDerivAt.fderiv]
  intro r r' hr
  simpa [hpos q.1 q.2] using hr

end TimeShear

/-! ### Rotations followed by boosts, level by level -/

section BoostRotate

open Module Real
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {u : E} {α : ℝ → ℝ} {Q : ℝ → E ≃ₗᵢ[ℝ] E}

/-- The linear isometry `Q s` followed by the boost of rapidity `α s` toward `u`, applied at level
`s` to the vector `x`. -/
def boostRotate (u : E) (α : ℝ → ℝ) (Q : ℝ → E ≃ₗᵢ[ℝ] E) (p : ℝ × E) : E :=
  sphereBoost u (α p.1) (Q p.1 p.2)

/-- At level `s`, `boostRotate` applies `Q s` and then the boost of rapidity `α s`. -/
@[simp]
theorem boostRotate_apply (s : ℝ) (x : E) :
    boostRotate u α Q (s, x) = sphereBoost u (α s) (Q s x) :=
  (rfl)

/-- `boostRotate` maps the unit sphere to itself. -/
theorem norm_boostRotate (hu : ‖u‖ = 1) (s : ℝ) {x : E} (hx : ‖x‖ = 1) :
    ‖boostRotate u α Q (s, x)‖ = 1 :=
  norm_sphereBoost hu (by rwa [LinearIsometryEquiv.norm_map]) _

/-- The map `boostRotate` is smooth at every point of `ℝ × Sⁿ`. -/
theorem contDiffAt_boostRotate (hu : ‖u‖ = 1) (hα : ContDiff ℝ ∞ α)
    (hQ : ContDiff ℝ ∞ fun p : ℝ × E => Q p.1 p.2) (s : ℝ) {x : E} (hx : ‖x‖ = 1) :
    ContDiffAt ℝ ∞ (boostRotate u α Q) (s, x) := by
  have hx' : ‖Q s x‖ = 1 := by rwa [LinearIsometryEquiv.norm_map]
  exact (contDiffAt_sphereBoost (cosh_add_sinh_mul_inner_pos hu hx' _).ne').comp (s, x)
    ((hα.comp contDiff_fst).prodMk hQ).contDiffAt

/-- Level by level, the rotation `Q s` followed by the boost of rapidity `α s` toward the unit
vector `u` is a diffeomorphism of `Sⁿ × ℝ` preserving the level `s`: its inverse at level `s` is
the boost of rapidity `-α s` followed by `(Q s)⁻¹`. -/
def boostRotateDiffeomorph (hu : ‖u‖ = 1) (hα : ContDiff ℝ ∞ α)
    (hQ : ContDiff ℝ ∞ fun p : ℝ × E => Q p.1 p.2) :
    (sphere (0 : E) 1 × ℝ) ≃ₘ^∞⟮(𝓡 n).prod 𝓘(ℝ), (𝓡 n).prod 𝓘(ℝ)⟯ (sphere (0 : E) 1 × ℝ) where
  toFun p := (⟨boostRotate u α Q (p.2, p.1), mem_sphere_zero_iff_norm.2
    (norm_boostRotate hu _ (norm_eq_of_mem_sphere p.1))⟩, p.2)
  invFun p := (⟨(Q p.2).symm (sphereBoost u (-α p.2) p.1), mem_sphere_zero_iff_norm.2 (by
    rw [LinearIsometryEquiv.norm_map]; exact norm_sphereBoost hu (norm_eq_of_mem_sphere p.1) _)⟩,
    p.2)
  left_inv p := by
    have hx : ‖Q p.2 p.1‖ = 1 := by rw [LinearIsometryEquiv.norm_map]; exact norm_eq_of_mem_sphere _
    refine Prod.ext (Subtype.ext ?_) rfl
    simp only [boostRotate_apply]
    rw [sphereBoost_sphereBoost hu hx, neg_add_cancel, sphereBoost_zero, id,
      LinearIsometryEquiv.symm_apply_apply]
  right_inv p := by
    refine Prod.ext (Subtype.ext ?_) rfl
    simp only [boostRotate_apply, LinearIsometryEquiv.apply_symm_apply]
    rw [sphereBoost_sphereBoost hu (norm_eq_of_mem_sphere p.1), add_neg_cancel, sphereBoost_zero,
      id]
  contMDiff_toFun := by
    refine ContMDiff.prodMk ?_ contMDiff_snd
    refine ContMDiff.codRestrict_sphere (fun p => ?_) _
    have hin : ContMDiff ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × E) ∞
        fun p : sphere (0 : E) 1 × ℝ => (p.2, (p.1 : E)) :=
      contMDiff_snd.prodMk_space (contMDiff_coe_sphere.comp contMDiff_fst)
    exact (contDiffAt_boostRotate hu hα hQ p.2 (norm_eq_of_mem_sphere p.1)).contMDiffAt.comp p
      (hin p)
  contMDiff_invFun := by
    refine ContMDiff.prodMk ?_ contMDiff_snd
    refine ContMDiff.codRestrict_sphere (fun p => ?_) _
    have hb : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞
        (fun p : sphere (0 : E) 1 × ℝ => sphereBoost u (-α p.2) p.1) p := by
      have hin : ContMDiff ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × E) ∞
          fun p : sphere (0 : E) 1 × ℝ => (-α p.2, (p.1 : E)) :=
        ((hα.contMDiff.comp contMDiff_snd).neg).prodMk_space
          (contMDiff_coe_sphere.comp contMDiff_fst)
      exact (contDiffAt_sphereBoost (cosh_add_sinh_mul_inner_pos hu
        (norm_eq_of_mem_sphere p.1) _).ne').contMDiffAt.comp p (hin p)
    have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
    exact (ContDiff.linearIsometryEquiv_symm_apply hQ).contMDiff.contMDiffAt.comp p
      ((contMDiff_snd p).prodMk_space hb)

/-- The sphere component of `boostRotateDiffeomorph` is `boostRotate` at the level of the
point. -/
@[simp]
theorem coe_boostRotateDiffeomorph_apply_fst (hu : ‖u‖ = 1) (hα : ContDiff ℝ ∞ α)
    (hQ : ContDiff ℝ ∞ fun p : ℝ × E => Q p.1 p.2) (p : sphere (0 : E) 1 × ℝ) :
    ((boostRotateDiffeomorph (n := n) hu hα hQ p).1 : E) = boostRotate u α Q (p.2, p.1) :=
  (rfl)

/-- `boostRotateDiffeomorph` preserves the levels. -/
@[simp]
theorem boostRotateDiffeomorph_apply_snd (hu : ‖u‖ = 1) (hα : ContDiff ℝ ∞ α)
    (hQ : ContDiff ℝ ∞ fun p : ℝ × E => Q p.1 p.2) (p : sphere (0 : E) 1 × ℝ) :
    (boostRotateDiffeomorph (n := n) hu hα hQ p).2 = p.2 :=
  (rfl)

/-- At a point `-u` fixed by every `Q s`, the derivative of `boostRotate` in a direction `(0, ξ)`
with `Q s ξ` tangent to the sphere at `-u` is `Q s ξ` stretched by `exp (α s)`. -/
theorem fderiv_boostRotate_apply_zero (hu : ‖u‖ = 1) (hα : ContDiff ℝ ∞ α)
    (hQ : ContDiff ℝ ∞ fun p : ℝ × E => Q p.1 p.2) (s : ℝ) (hQu : Q s (-u) = -u) {ξ : E}
    (hξ : ⟪Q s ξ, u⟫ = 0) :
    fderiv ℝ (boostRotate u α Q) (s, -u) (0, ξ) = exp (α s) • Q s ξ := by
  have hD := ((contDiffAt_boostRotate hu hα hQ s (by rw [norm_neg, hu])).differentiableAt
    (by simp)).hasFDerivAt
  -- The slice `x ↦ boostRotate u α Q (s, x)` is the boost after the linear isometry `Q s`.
  have h₁ := hD.comp (-u) (hasFDerivAt_prodMk_right s (-u))
  have hB : HasFDerivAt (sphereBoost u (α s)) (fderiv ℝ (sphereBoost u (α s)) (-u)) (Q s (-u)) := by
    rw [hQu]
    exact (differentiableAt_sphereBoost (cosh_add_sinh_mul_inner_pos hu
      (by rw [norm_neg, hu]) _).ne').hasFDerivAt
  have h₂ := hB.comp (-u) (Q s).toContinuousLinearEquiv.hasFDerivAt
  have h := congrArg (fun L : E →L[ℝ] E => L ξ) (h₁.unique h₂)
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.inr_apply] at h
  rw [h]
  exact fderiv_sphereBoost_neg_self_apply hu _ hξ

end BoostRotate

/-! ### Maps of the cylinder over the circle, read along `Circle.exp` -/

section CircleCylinder

open Module
open scoped RealInnerProductSpace

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- **The first order of a map of the cylinder along a line.** Two maps `f` and `g` of the
cylinder `S¹ × ℝ` into `Sⁿ × ℝ`, differentiable at `(exp (θ i), t)`, which agree on the whole line
`{exp (θ i)} × ℝ`, and whose slices `θ' ↦ f (exp (θ' i), t)` and `θ' ↦ g (exp (θ' i), t)` have the
same velocity at `θ` in `E × ℝ`, have the same derivative at `(exp (θ i), t)`. -/
theorem mfderiv_eq_of_deriv_comp_circleExp_eq_prod {f g : Circle × ℝ → sphere (0 : E) 1 × ℝ}
    {θ t : ℝ} (hf : MDifferentiableAt ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) f (Circle.exp θ, t))
    (hg : MDifferentiableAt ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) g (Circle.exp θ, t))
    (hline : ∀ s, f (Circle.exp θ, s) = g (Circle.exp θ, s))
    (h₁ : deriv (fun θ' => ((f (Circle.exp θ', t)).1 : E)) θ =
      deriv (fun θ' => ((g (Circle.exp θ', t)).1 : E)) θ)
    (h₂ : deriv (fun θ' => (f (Circle.exp θ', t)).2) θ =
      deriv (fun θ' => (g (Circle.exp θ', t)).2) θ) :
    mfderiv ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) f (Circle.exp θ, t) =
      mfderiv ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) g (Circle.exp θ, t) := by
  have hslice {k : Circle × ℝ → sphere (0 : E) 1 × ℝ}
      (hk : MDifferentiableAt ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) k (Circle.exp θ, t)) :
      MDifferentiableAt (𝓡 1) ((𝓡 n).prod 𝓘(ℝ)) (fun z => k (z, t)) (Circle.exp θ) :=
    hk.comp (Circle.exp θ) (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  have hf₁ := hslice hf
  have hg₁ := hslice hg
  rw [mfderiv_prod_eq_add_comp hf, mfderiv_prod_eq_add_comp hg]
  congr 2
  · -- The slices at time `t` agree to first order: compare their two components.
    change mfderiv (𝓡 1) ((𝓡 n).prod 𝓘(ℝ)) (fun z => ((f (z, t)).1, (f (z, t)).2)) _ =
      mfderiv (𝓡 1) ((𝓡 n).prod 𝓘(ℝ)) (fun z => ((g (z, t)).1, (g (z, t)).2)) _
    rw [mfderiv_prodMk hf₁.fst hf₁.snd, mfderiv_prodMk hg₁.fst hg₁.snd]
    congr 1
    · exact mfderiv_eq_of_deriv_coe_comp_circleExp_eq hf₁.fst hg₁.fst
        (congrArg Prod.fst (hline t)) h₁
    · exact mfderiv_eq_of_deriv_comp_circleExp_eq hf₁.snd hg₁.snd h₂
  · -- On the line `{exp (θ i)} × ℝ` the two maps agree.
    rw [show (fun z : ℝ => f (Circle.exp θ, z)) = fun z => g (Circle.exp θ, z) from funext hline]

/-- A map `Γ` of the cylinder `S¹ × ℝ` into `Sⁿ × ℝ` which is the line `s ↦ (y, s)` over
`exp (θ i)`, and has injective derivative at `(exp (θ i), t)`, has a slice
`θ' ↦ Γ (exp (θ' i), t)` whose sphere component has nonzero velocity at `θ`. Otherwise the
derivative of `Γ` would kill a vector `(u, -c)`, with `u` tangent to the circle and `c` the time
component of the slice velocity. -/
theorem deriv_coe_fst_comp_circleExp_ne_zero {Γ : Circle × ℝ → sphere (0 : E) 1 × ℝ}
    {θ t : ℝ} {y : sphere (0 : E) 1}
    (hΓ : MDifferentiableAt ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) Γ (Circle.exp θ, t))
    (hinj : Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) Γ (Circle.exp θ, t)))
    (hline : ∀ s, Γ (Circle.exp θ, s) = (y, s)) :
    deriv (fun θ' => ((Γ (Circle.exp θ', t)).1 : E)) θ ≠ 0 := by
  intro h0
  set u : EuclideanSpace ℝ (Fin 1) := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp θ 1
  have hu : u ≠ 0 := fun h =>
    one_ne_zero (show (1 : ℝ) = 0 from injective_mfderiv_circleExp θ (h.trans (map_zero _).symm))
  have hΓ₁ : MDifferentiableAt (𝓡 1) ((𝓡 n).prod 𝓘(ℝ)) (fun z => Γ (z, t)) (Circle.exp θ) :=
    hΓ.comp (Circle.exp θ) (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  -- The sphere component of the slice has zero derivative in the direction `u`.
  have h₁ : mfderiv (𝓡 1) (𝓡 n) (fun z => (Γ (z, t)).1) (Circle.exp θ) u = 0 := by
    have h := smul_deriv_coe_comp_circleExp hΓ₁.fst 1
    rw [h0, smul_zero] at h
    exact injective_mvfderiv_subtypeVal_sphere _ (h.symm.trans (map_zero _).symm)
  set c : ℝ := mfderiv (𝓡 1) 𝓘(ℝ) (fun z => (Γ (z, t)).2) (Circle.exp θ) u
  set w : TangentSpace ((𝓡 1).prod 𝓘(ℝ)) (Circle.exp θ, t) := (u, -c)
  -- The two components of the derivative of `Γ` in the direction `w` vanish.
  have ha : mfderiv ((𝓡 1).prod 𝓘(ℝ)) (𝓡 n) (fun q => (Γ q).1) (Circle.exp θ, t) w = 0 := by
    rw [mfderiv_prod_eq_add_apply hΓ.fst]
    have hs : (fun s : ℝ => (Γ (Circle.exp θ, s)).1) = fun _ => y :=
      funext fun s => by rw [hline]
    rw [hs, mfderiv_const]
    exact (add_zero _).trans h₁
  have hb : mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) (fun q => (Γ q).2) (Circle.exp θ, t) w = 0 := by
    rw [mfderiv_prod_eq_add_apply hΓ.snd]
    have hs : (fun s : ℝ => (Γ (Circle.exp θ, s)).2) = fun s => s :=
      funext fun s => by rw [hline]
    have hid : mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun s : ℝ => (Γ (Circle.exp θ, s)).2) t =
        ContinuousLinearMap.id ℝ ℝ := by
      rw [hs]
      exact mfderiv_id
    rw [hid]
    exact add_neg_cancel c
  have hkey : mfderiv ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) Γ (Circle.exp θ, t) w = 0 := by
    have hdecomp := mfderiv_prodMk hΓ.fst hΓ.snd
    rw [hdecomp]
    exact Prod.ext ha hb
  exact hu (congrArg Prod.fst (hinj (hkey.trans (map_zero _).symm)) :)

/-- A smooth real function on the circle, of absolute value at most `δ`, which vanishes at
`exp (θ₀ i)` and has velocity `1` there along `Circle.exp`: `κ arctan (sin (θ - θ₀) / κ)` with
`κ = δ / 2`. -/
private theorem exists_contMDiff_circle_hasDerivAt (θ₀ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h : Circle → ℝ, ContMDiff (𝓡 1) 𝓘(ℝ) ∞ h ∧ h (Circle.exp θ₀) = 0 ∧
      HasDerivAt (fun θ => h (Circle.exp θ)) 1 θ₀ ∧ ∀ z, |h z| ≤ δ := by
  set κ := δ / 2
  have hκ : 0 < κ := half_pos hδ
  set g : ℂ → ℝ := fun w => κ * Real.arctan (w.im / κ)
  have hg : ContDiff ℝ ∞ g :=
    contDiff_const.mul (Real.contDiff_arctan.comp (Complex.imCLM.contDiff.div_const κ))
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ fun z : Circle => (((Circle.exp θ₀)⁻¹ * z : Circle) : ℂ) :=
    contMDiff_coe_sphere.comp contMDiff_mul_left
  have he (θ : ℝ) : g (((Circle.exp θ₀)⁻¹ * Circle.exp θ : Circle) : ℂ) =
      κ * Real.arctan (Real.sin (θ - θ₀) / κ) := by
    simp only [g, inv_mul_eq_div, ← Circle.exp_sub, Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
  refine ⟨fun z => g (((Circle.exp θ₀)⁻¹ * z : Circle) : ℂ), hg.contMDiff.comp hc, ?_, ?_,
    fun z => ?_⟩
  · simp [g]
  · have hs : HasDerivAt (fun θ => Real.sin (θ - θ₀) / κ) (Real.cos (θ₀ - θ₀) * 1 / κ) θ₀ :=
      ((Real.hasDerivAt_sin _).comp θ₀ ((hasDerivAt_id θ₀).sub_const θ₀)).div_const κ
    have hd : HasDerivAt (fun θ => κ * Real.arctan (Real.sin (θ - θ₀) / κ)) 1 θ₀ := by
      convert ((Real.hasDerivAt_arctan _).comp θ₀ hs).const_mul κ using 1
      · rfl
      · rw [sub_self, Real.sin_zero, Real.cos_zero]
        field_simp
        ring
    exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall he)
  · set x := (((Circle.exp θ₀)⁻¹ * z : Circle) : ℂ).im / κ
    have hx : |Real.arctan x| ≤ 2 := (abs_lt.2 ⟨Real.neg_pi_div_two_lt_arctan x,
      Real.arctan_lt_pi_div_two x⟩).le.trans (by linarith [Real.pi_le_four])
    calc |g (((Circle.exp θ₀)⁻¹ * z : Circle) : ℂ)| = κ * |Real.arctan x| := by
          simp only [g, abs_mul, abs_of_pos hκ, x]
      _ ≤ κ * 2 := mul_le_mul_of_nonneg_left hx hκ.le
      _ = δ := by simp only [κ]; ring

end CircleCylinder

/-! ### Making a concordance standard to first order along an arc -/

section FirstOrder

open Module Real
open scoped RealInnerProductSpace

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

namespace SmoothEmbedding.Concordance

variable {K K' : SmoothEmbedding (𝓡 1) (𝓡 n) ∞ Circle (sphere (0 : E) 1)}

/-- **Choosing the shear.** For a smooth `β : ℝ → ℝ` with compact support and `ε > 0`, some
smooth `h` on the circle vanishes at `exp (θ₀ i)`, has velocity `1` there along `Circle.exp`, and
is so small that the time shear `(x, t) ↦ (x, t + β t * h x)` moves times by less than `ε` and has
positive time derivative `1 + β' t * h x`. -/
private theorem exists_shear_circle (θ₀ : ℝ) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hcs : HasCompactSupport β) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : Circle → ℝ, ContMDiff (𝓡 1) 𝓘(ℝ) ∞ h ∧ h (Circle.exp θ₀) = 0 ∧
      HasDerivAt (fun θ => h (Circle.exp θ)) 1 θ₀ ∧
        ∀ x t, |β t * h x| < ε ∧ 0 < 1 + deriv β t * h x := by
  obtain ⟨C₁, hC₁⟩ := hβ.continuous.bounded_above_of_compact_support hcs
  obtain ⟨C₂, hC₂⟩ := (hβ.continuous_deriv (by simp)).bounded_above_of_compact_support hcs.deriv
  set C := max (max C₁ C₂) 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hβC (t : ℝ) : |β t| ≤ C :=
    (hC₁ t).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hβ'C (t : ℝ) : |deriv β t| ≤ C :=
    (hC₂ t).trans ((le_max_right _ _).trans (le_max_left _ _))
  -- With `|h| ≤ δ`, both displacements are at most `C δ < min ε 1 / 2`.
  have hm : 0 < min ε 1 := lt_min hε one_pos
  set δ := min ε 1 / (2 * (C + 1))
  have hδ : 0 < δ := div_pos hm (by positivity)
  have hCδ : C * δ < min ε 1 / 2 := by
    calc C * δ = min ε 1 / 2 * (C / (C + 1)) := by simp only [δ]; field_simp
      _ < min ε 1 / 2 * 1 :=
        mul_lt_mul_of_pos_left ((div_lt_one (by positivity)).2 (by linarith)) (by positivity)
      _ = min ε 1 / 2 := mul_one _
  obtain ⟨h, hh, hh0, hhd, hhδ⟩ := exists_contMDiff_circle_hasDerivAt θ₀ hδ
  refine ⟨h, hh, hh0, hhd, fun x t => ?_⟩
  have hε1 := min_le_left ε 1
  have h11 := min_le_right ε 1
  have h₁ : |deriv β t * h x| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul (hβ'C t) (hhδ x) (abs_nonneg _) hC0).trans_lt (by linarith)
  refine ⟨?_, by linarith [neg_abs_le (deriv β t * h x)]⟩
  rw [abs_mul]
  exact (mul_le_mul (hβC t) (hhδ x) (abs_nonneg _) hC0).trans_lt (by linarith)

/-- A concordance between circle embeddings into `Sⁿ`, read in the coordinates
`(θ, t) ↦ (exp (θ i), t)` of the cylinder and in `E × ℝ`. -/
private def track (F : Concordance K K') (q : ℝ × ℝ) : E × ℝ :=
  (((F (Circle.exp q.1, q.2)).1 : E), (F (Circle.exp q.1, q.2)).2)

private theorem contDiff_track (F : Concordance K K') : ContDiff ℝ ∞ (track F) := by
  have hc : ContMDiff 𝓘(ℝ, ℝ × ℝ) ((𝓡 1).prod 𝓘(ℝ)) ∞ fun q : ℝ × ℝ => (Circle.exp q.1, q.2) :=
    (contMDiff_circleExp.comp contDiff_fst.contMDiff).prodMk contDiff_snd.contMDiff
  have hι : ContMDiff ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, E × ℝ) ∞
      fun p : sphere (0 : E) 1 × ℝ => ((p.1 : E), p.2) :=
    (contMDiff_coe_sphere.comp contMDiff_fst).prodMk_space contMDiff_snd
  exact contMDiff_iff_contDiff.1 (hι.comp (F.toSmoothEmbedding.contMDiff.comp hc))

/-- The partial derivative of the track in the circle direction is the velocity of its slice. -/
private theorem hasDerivAt_track_left (F : Concordance K K') (θ t : ℝ) :
    HasDerivAt (fun θ' => track F (θ', t)) (fderiv ℝ (track F) (θ, t) (1, 0)) θ := by
  have h := ((contDiff_track F).differentiable (by simp) (θ, t)).hasFDerivAt.comp_hasDerivAt θ
    ((hasDerivAt_id' θ).prodMk (hasDerivAt_const θ t))
  exact h

/-- The partial derivative of the track in the time direction. -/
private theorem hasDerivAt_track_right (F : Concordance K K') (θ t : ℝ) :
    HasDerivAt (fun s => track F (θ, s)) (fderiv ℝ (track F) (θ, t) (0, 1)) t := by
  have h := ((contDiff_track F).differentiable (by simp) (θ, t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t θ).prodMk (hasDerivAt_id' t))
  exact h

/-- **Making a concordance standard to first order along an arc.** Let `F` be a concordance
between smooth circle embeddings `K` and `K'` into the unit sphere `Sⁿ`, `n ≥ 3`, which maps the
line `{z₀} × ℝ` onto the straight line `{L z₀} × ℝ`, where `K` and `K'` have the same derivative
at `z₀` as the loop `L`. Then some concordance `G` from `K` to `K'` maps that line onto the same
straight line and has the same derivative as the strip `L × id` at every point `(z₀, t)`. -/
theorem exists_mfderiv_eq_prodMap (hn : 3 ≤ n) (F : Concordance K K')
    {L : Circle → sphere (0 : E) 1} {z₀ : Circle}
    (hK : mfderiv (𝓡 1) (𝓡 n) K z₀ = mfderiv (𝓡 1) (𝓡 n) L z₀)
    (hK' : mfderiv (𝓡 1) (𝓡 n) K' z₀ = mfderiv (𝓡 1) (𝓡 n) L z₀)
    (h₀ : ∀ t, F (z₀, t) = (L z₀, t)) :
    ∃ G : Concordance K K', (∀ t, G (z₀, t) = (L z₀, t)) ∧
      ∀ t, mfderiv ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) G (z₀, t) =
        mfderiv ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) (Prod.map L _root_.id) (z₀, t) := by
  -- Read `F` along the line `{exp (θ₀ i)} × ℝ`: there its circle velocity is `(A t, b t)`. A
  -- level-preserving rotation followed by a boost, `Ψ`, turns `A t` into the velocity `W` of `L`,
  -- and a time shear `φ` of the source cancels `b t`, so `G = Ψ ∘ F ∘ φ` is the concordance.
  obtain ⟨θ₀, rfl⟩ := Circle.exp_surjective z₀
  obtain ⟨εl, hεl, hFl⟩ := F.isCollaredTrack.exists_pos_apply_eq_left
  obtain ⟨εr, hεr, hFr⟩ := F.isCollaredTrack.exists_pos_apply_eq_right
  set v : E := (L (Circle.exp θ₀) : E) with hv_def
  have hv : ‖v‖ = 1 := norm_eq_of_mem_sphere _
  -- `K` and `K'` pass through `L (exp θ₀)`, and `L` is differentiable there.
  have hKL : K (Circle.exp θ₀) = L (Circle.exp θ₀) := by
    have h := h₀ 0
    rw [hFl _ 0 hεl.le] at h
    exact congrArg Prod.fst h
  have hK'L : K' (Circle.exp θ₀) = L (Circle.exp θ₀) := by
    have h := h₀ 1
    rw [hFr _ 1 (by linarith)] at h
    exact congrArg Prod.fst h
  have hu₁ : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp θ₀ 1 ≠ 0 := fun h =>
    one_ne_zero (show (1 : ℝ) = 0 from injective_mfderiv_circleExp θ₀ (h.trans (map_zero _).symm))
  have hLd : MDifferentiableAt (𝓡 1) (𝓡 n) L (Circle.exp θ₀) := by
    by_contra hnd
    have hinj := (K.isImmersion.isDiffImmersionAt (by simp) (Circle.exp θ₀)).mfderiv_injective
    have h0 := congrArg (fun D : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
      D (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp θ₀ 1)) hK
    simp only [mfderiv_zero_of_not_mdifferentiableAt hnd] at h0
    exact hu₁ (hinj (h0.trans (map_zero _).symm))
  -- The velocity `W` of `L` at `θ₀` is that of `K` and of `K'`.
  have hKW : deriv (fun θ => (K (Circle.exp θ) : E)) θ₀ =
      deriv (fun θ => (L (Circle.exp θ) : E)) θ₀ :=
    deriv_coe_comp_circleExp_eq_of_mfderiv_eq (K.contMDiff.mdifferentiableAt (by simp)) hLd hKL hK
  have hK'W : deriv (fun θ => (K' (Circle.exp θ) : E)) θ₀ =
      deriv (fun θ => (L (Circle.exp θ) : E)) θ₀ :=
    deriv_coe_comp_circleExp_eq_of_mfderiv_eq (K'.contMDiff.mdifferentiableAt (by simp)) hLd hK'L
      hK'
  set W : E := deriv (fun θ => (L (Circle.exp θ) : E)) θ₀ with hW_def
  -- The velocity `(A t, b t)` of the slice of `F` at time `t`, read in `E × ℝ`.
  set A : ℝ → E := fun t => (fderiv ℝ (track F) (θ₀, t) (1, 0)).1 with hA_def
  set b : ℝ → ℝ := fun t => (fderiv ℝ (track F) (θ₀, t) (1, 0)).2 with hb_def
  have hAb : ContDiff ℝ ∞ fun t => fderiv ℝ (track F) (θ₀, t) (1, 0) :=
    ((contDiff_infty_iff_fderiv.1 (contDiff_track F)).2.comp
      (contDiff_const.prodMk contDiff_id)).clm_apply contDiff_const
  have hA : ContDiff ℝ ∞ A := contDiff_fst.comp hAb
  have hb : ContDiff ℝ ∞ b := contDiff_snd.comp hAb
  have hAslice (t : ℝ) : A t = deriv (fun θ => ((F (Circle.exp θ, t)).1 : E)) θ₀ :=
    ((ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt.comp_hasDerivAt θ₀
      (hasDerivAt_track_left F θ₀ t)).deriv.symm
  have hbslice (t : ℝ) : b t = deriv (fun θ => (F (Circle.exp θ, t)).2) θ₀ :=
    ((ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt.comp_hasDerivAt θ₀
      (hasDerivAt_track_left F θ₀ t)).deriv.symm
  -- On the collars, the slices are those of `K` and `K'`.
  have hAl (t : ℝ) (ht : t ≤ εl) : A t = W := by
    rw [hAslice, ← hKW]
    congr 1
    funext θ
    rw [hFl _ t ht]
  have hbl (t : ℝ) (ht : t ≤ εl) : b t = 0 := by
    rw [hbslice]
    simp only [hFl _ t ht, deriv_const]
  have hAr (t : ℝ) (ht : 1 - εr ≤ t) : A t = W := by
    rw [hAslice, ← hK'W]
    congr 1
    funext θ
    rw [hFr _ t ht]
  have hbr (t : ℝ) (ht : 1 - εr ≤ t) : b t = 0 := by
    rw [hbslice]
    simp only [hFr _ t ht, deriv_const]
  -- Along the line, the track is `s ↦ (v, s)`.
  have htrack_line (s : ℝ) : track F (θ₀, s) = (v, s) := by
    simp only [track, h₀ s, hv_def]
  have hτ (t : ℝ) : fderiv ℝ (track F) (θ₀, t) (0, 1) = (0, 1) := by
    refine (hasDerivAt_track_right F θ₀ t).unique ?_
    rw [show (fun s => track F (θ₀, s)) = fun s => (v, s) from funext htrack_line]
    exact (hasDerivAt_const t v).prodMk (hasDerivAt_id' t)
  have hA0 (t : ℝ) : A t ≠ 0 := by
    rw [hAslice]
    exact deriv_coe_fst_comp_circleExp_ne_zero
      (F.toSmoothEmbedding.contMDiff.mdifferentiableAt (by simp))
      ((F.toSmoothEmbedding.isImmersion.isDiffImmersionAt (by simp) _).mfderiv_injective) h₀
  have hAv (t : ℝ) : ⟪A t, v⟫ = 0 := by
    have hmd : MDifferentiableAt (𝓡 1) (𝓡 n) (fun z => (F (z, t)).1) (Circle.exp θ₀) :=
      (F.toSmoothEmbedding.contMDiff.mdifferentiableAt (by simp)).fst.comp (Circle.exp θ₀)
        (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    have h := inner_deriv_coe_comp_circleExp_eq_zero hmd
    rw [h₀ t] at h
    rw [hAslice, real_inner_comm]
    exact h
  have hW : W ≠ 0 := hAl 0 hεl.le ▸ hA0 0
  -- A smooth family of rotations fixing `v` turns the direction of `A t` into that of `W`.
  set u : ℝ → E := fun t => ‖A t‖⁻¹ • A t with hu_def
  have hu : ContDiff ℝ ∞ u :=
    ((hA.norm ℝ hA0).inv fun t => norm_ne_zero_iff.2 (hA0 t)).smul hA
  have hu0 : u 0 = ‖W‖⁻¹ • W := by simp only [hu_def, hAl 0 hεl.le]
  have hfin : 2 < finrank ℝ (ℝ ∙ v)ᗮ := by
    rw [Submodule.finrank_orthogonal_span_singleton (n := n)
      (norm_ne_zero_iff.1 (hv.symm ▸ one_ne_zero))]
    omega
  obtain ⟨Q, hQ, hQv, hQu, hQ1⟩ := exists_contDiff_linearIsometryEquiv_apply_eq (k := ∞)
    (by simp) hfin hu (fun t => norm_smul_inv_norm (hA0 t))
    (fun t => by rw [hu_def, real_inner_smul_left, hAv, mul_zero]) 0
  -- A smooth family of boosts toward `-v` then corrects the speed.
  set α : ℝ → ℝ := fun t => Real.log (‖W‖ / ‖A t‖) with hα_def
  have hα : ContDiff ℝ ∞ α :=
    (contDiff_const.div (hA.norm ℝ hA0) fun t => norm_ne_zero_iff.2 (hA0 t)).log fun t =>
      (div_pos (norm_pos_iff.2 hW) (norm_pos_iff.2 (hA0 t))).ne'
  have hv' : ‖-v‖ = 1 := by rw [norm_neg, hv]
  set Ψ := boostRotateDiffeomorph (n := n) hv' hα hQ
  have hΨ (y : sphere (0 : E) 1) (s : ℝ) :
      Ψ (y, s) = (⟨boostRotate (-v) α Q (s, y), (Ψ (y, s)).1.2⟩, s) := rfl
  have hΨid (t : ℝ) (hAt : A t = W) (y : sphere (0 : E) 1) : Ψ (y, t) = (y, t) := by
    have hut : u t = u 0 := by simp only [hu_def, hAt, hAl 0 hεl.le]
    refine Prod.ext (Subtype.ext ?_) rfl
    rw [hΨ]
    simp only [boostRotate_apply, hQ1 t hut, hα_def, hAt, div_self (norm_ne_zero_iff.2 hW),
      Real.log_one, sphereBoost_zero, _root_.id]
  have hΨv (t : ℝ) : Ψ (L (Circle.exp θ₀), t) = (L (Circle.exp θ₀), t) := by
    refine Prod.ext (Subtype.ext ?_) rfl
    rw [hΨ]
    have h := sphereBoost_neg_self hv' (α t)
    rw [neg_neg] at h
    simp only [boostRotate_apply]
    rw [← hv_def, hQv, h]
  -- A time shear by `β = -b` removes the time component of the slice velocity.
  set β : ℝ → ℝ := fun t => -b t with hβ_def
  have hβ : ContDiff ℝ ∞ β := hb.neg
  have hβ0 (t : ℝ) (ht : t ∉ Icc εl (1 - εr)) : β t = 0 := by
    rcases not_and_or.1 ht with ht | ht
    · simp only [hβ_def, hbl t (not_le.1 ht).le, neg_zero]
    · simp only [hβ_def, hbr t (not_le.1 ht).le, neg_zero]
  have hcs : HasCompactSupport β := HasCompactSupport.intro isCompact_Icc hβ0
  set ε := min εl εr
  have hε : 0 < ε := lt_min hεl hεr
  obtain ⟨h, hh, hh0, hhd, hsmall⟩ := exists_shear_circle θ₀ hβ hcs hε
  have hpos (x : Circle) (t : ℝ) : 0 < 1 + deriv β t * h x := (hsmall x t).2
  -- The sheared track `F ∘ φ` is a smooth embedding.
  set φ := timeShear β h with hφ_def
  have hφinj := injective_timeShear (hβ.differentiable (by simp)) hpos
  have hφprop : IsProperMap φ :=
    isProperMap_timeShear hβ.continuous hh.continuous fun x t => (hsmall x t).1.le
  have hφimm := isImmersion_timeShear hβ hh fun x t => (hpos x t).ne'
  have hFinj : Injective F := F.toSmoothEmbedding.isEmbedding.injective
  have hFφ : IsSmoothEmbedding ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞ (F ∘ φ) := by
    refine IsImmersion.isSmoothEmbedding_of_isProperMap ?_ (hFinj.comp hφinj)
      ((F.isCollaredTrack.isClosedEmbedding F.toSmoothEmbedding.contMDiff.continuous
        hFinj).isProperMap.comp hφprop)
    refine isImmersion_iff_forall_isImmersionAt.2 fun p => ?_
    refine (F.toSmoothEmbedding.contMDiff.comp (contMDiff_timeShear hβ hh)).contMDiffOn
      |>.isImmersionAt_of_hasLeftInverse_mfderiv isOpen_univ (mem_univ p) (by simp) ?_
    exact isDiffImmersionAt_iff.1 ((F.toSmoothEmbedding.isImmersion.isDiffImmersionAt
      (by simp) _).comp (hφimm.isDiffImmersionAt (by simp) p))
  -- The new concordance applies `Ψ` after the sheared track.
  set G₀ := (SmoothEmbedding.ofIsSmoothEmbedding _ hFφ).transDiffeomorph Ψ with hG₀_def
  have hG₀ (p : Circle × ℝ) : G₀ p = Ψ (F (φ p)) := by
    simp only [hG₀_def, SmoothEmbedding.transDiffeomorph_apply,
      SmoothEmbedding.ofIsSmoothEmbedding_apply, Function.comp_apply]
  have hcol : IsCollaredTrack K K' G₀ := by
    refine ⟨⟨ε, hε, fun x t ht => ?_⟩, ⟨ε, hε, fun x t ht => ?_⟩, fun x t ht => ?_⟩
    · have htl : t ≤ εl := ht.trans (min_le_left _ _)
      rw [hG₀, hφ_def, timeShear_apply,
        show β t = 0 by simp only [hβ_def, hbl t htl, neg_zero], zero_mul, add_zero,
        hFl x t htl, hΨid t (hAl t htl)]
    · have htr : 1 - εr ≤ t := le_trans (by linarith [min_le_right εl εr]) ht
      rw [hG₀, hφ_def, timeShear_apply,
        show β t = 0 by simp only [hβ_def, hbr t htr, neg_zero], zero_mul, add_zero,
        hFr x t htr, hΨid t (hAr t htr)]
    · rw [hG₀, show (Ψ (F (φ (x, t)))).2 = (F (φ (x, t))).2 from rfl, hφ_def, timeShear_apply]
      refine F.isCollaredTrack.snd_apply_mem_Ioo x _ ?_
      by_cases hβt : β t = 0
      · rw [hβt, zero_mul, add_zero]
        exact ht
      · have hI : t ∈ Icc εl (1 - εr) := by
          by_contra hI
          exact hβt (hβ0 t hI)
        have hb := abs_lt.1 (hsmall x t).1
        constructor <;> linarith [min_le_left εl εr, min_le_right εl εr, hI.1, hI.2]
  let G : Concordance K K' := ⟨G₀, hcol⟩
  have hG (p : Circle × ℝ) : G p = Ψ (F (φ p)) := hG₀ p
  have hGline (s : ℝ) : G (Circle.exp θ₀, s) = (L (Circle.exp θ₀), s) := by
    rw [hG, hφ_def, timeShear_apply, hh0, mul_zero, add_zero, h₀, hΨv]
  refine ⟨G, hGline, fun t => ?_⟩
  -- Along the slice at time `t`, the shear moves the time by `σ θ = t + β t * h (exp θ)`.
  set σ : ℝ → ℝ := fun θ => t + β t * h (Circle.exp θ) with hσ_def
  have hσ : HasDerivAt σ (β t * 1) θ₀ := (hhd.const_mul (β t)).const_add t
  have hσ₀ : σ θ₀ = t := by simp only [hσ_def, hh0, mul_zero, add_zero]
  have hY : HasDerivAt (fun θ => track F (θ, σ θ)) (A t, 0) θ₀ := by
    have h₁ : HasDerivAt (fun θ => track F (θ, σ θ)) (fderiv ℝ (track F) (θ₀, t) (1, β t * 1))
        θ₀ :=
      ((contDiff_track F).differentiable (by simp) (θ₀, t)).hasFDerivAt.comp_hasDerivAt_of_eq
        θ₀ ((hasDerivAt_id' θ₀).prodMk hσ) (by rw [hσ₀])
    convert h₁ using 1
    have hsplit : ((1 : ℝ), β t * 1) = ((1 : ℝ), (0 : ℝ)) + β t • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [hsplit, map_add, map_smul, hτ]
    ext
    · simp [hA_def]
    · simp [hb_def, hβ_def]
  have hfst : HasDerivAt (fun θ => (track F (θ, σ θ)).1) (A t) θ₀ :=
    (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt.comp_hasDerivAt θ₀ hY
  have hsnd : HasDerivAt (fun θ => (track F (θ, σ θ)).2) 0 θ₀ :=
    (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt.comp_hasDerivAt θ₀ hY
  refine mfderiv_eq_of_deriv_comp_circleExp_eq_prod
    (G.toSmoothEmbedding.contMDiff.mdifferentiableAt (by simp))
    (hLd.prodMap mdifferentiableAt_id) hGline ?_ ?_
  · -- The sphere component: the rotation and boost turn `A t` into `W`.
    have hBR : HasFDerivAt (boostRotate (-v) α Q) (fderiv ℝ (boostRotate (-v) α Q) (t, v))
        (t, v) :=
      ((contDiffAt_boostRotate hv' hα hQ t hv).differentiableAt (by simp)).hasFDerivAt
    have hD : HasDerivAt
        (fun θ => boostRotate (-v) α Q ((track F (θ, σ θ)).2, (track F (θ, σ θ)).1))
        (fderiv ℝ (boostRotate (-v) α Q) (t, v) (0, A t)) θ₀ :=
      hBR.comp_hasDerivAt_of_eq θ₀ (hsnd.prodMk hfst) (by rw [hσ₀, htrack_line])
    have hval := fderiv_boostRotate_apply_zero hv' hα hQ t (by rw [neg_neg, hQv])
      (ξ := A t) (by rw [inner_neg_right, ← hQv t, LinearIsometryEquiv.inner_map_map, hAv,
        neg_zero])
    rw [neg_neg] at hval
    have hAu : A t = ‖A t‖ • u t := by
      rw [hu_def, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 (hA0 t)), one_smul]
    rw [show (fun θ => ((G (Circle.exp θ, t)).1 : E)) =
        fun θ => boostRotate (-v) α Q ((track F (θ, σ θ)).2, (track F (θ, σ θ)).1) from
          funext fun θ => by rw [hG]; rfl,
      hD.deriv, hval, hAu, map_smul, hQu, hu0, hα_def,
      Real.exp_log (div_pos (norm_pos_iff.2 hW) (norm_pos_iff.2 (hA0 t))), smul_smul, smul_smul,
      show ‖W‖ / ‖A t‖ * ‖A t‖ * ‖W‖⁻¹ = 1 by
        field_simp [norm_ne_zero_iff.2 (hA0 t), norm_ne_zero_iff.2 hW], one_smul]
    rfl
  · -- The time component: the shear cancels the time velocity `b t`.
    rw [show (fun θ => (G (Circle.exp θ, t)).2) = fun θ => (track F (θ, σ θ)).2 from
        funext fun θ => by rw [hG]; rfl,
      hsnd.deriv]
    simp

end SmoothEmbedding.Concordance

end FirstOrder

end TauCeti
