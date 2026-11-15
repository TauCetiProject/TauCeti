/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Euclidean.Complex
public import TauCeti.Geometry.Manifold.Degree.Global
public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.TangentSection
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.SmoothApprox
import TauCeti.Analysis.InnerProductSpace.Sphere.Trigonometric
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Sphere.Connected

/-!
# The hairy ball theorem and tangent fields on spheres

Every continuous tangent vector field on an even-dimensional unit sphere `Sⁿ` of a real inner
product space `E` (`dim_ℝ E = n + 1`) vanishes at some point: both in ambient form for maps
`v : E → E` continuous on `sphere (0 : E) 1` with `⟪v x, x⟫ = 0`
(`TauCeti.exists_eq_zero_of_inner_eq_zero`), and intrinsically for continuous sections of
`TangentBundle (𝓡 n) (sphere (0 : E) 1)` (`TauCeti.exists_eq_zero_of_continuous_section`).

The proof uses the Brouwer mapping degree rather than Euler characteristics:
1. For `n = 0`, `E` is one-dimensional, so any vector orthogonal to a unit vector already vanishes.
2. Suppose `n ≥ 1` and `v : sphere (0 : E) 1 → E` is continuous, orthogonal to `x` at every `x`,
   and nowhere zero. Smooth approximation on `Sⁿ` within radius `‖v x‖ / 2`, followed by
   orthogonal projection onto `(x : E)ᗮ` and radial normalization, yields a smooth unit tangent map
   `w : sphere (0 : E) 1 → E` (`TauCeti.exists_contMDiff_unit_tangent_sphere`).
3. The great-circle homotopy `TauCeti.greatCircleHomotopy`,
   `(x, t) ↦ cos(π t) • x + sin(π t) • w x`, smoothly deforms the identity of `Sⁿ` to the
   antipodal map `x ↦ -x`. Homotopy invariance of the mapping degree gives `1 = (-1) ^ (n + 1)`,
   forcing `n` to be odd (`TauCeti.odd_of_inner_sphere_eq_zero_of_ne_zero`).

Conversely, when `n` is odd, `dim_ℝ E = n + 1` is even, so `E` admits an orthogonal linear isometry
equivalence `L` with `⟪L x, x⟫ = 0` everywhere
(`TauCeti.exists_linearIsometryEquiv_inner_self_eq_zero`), induced in coordinates by the paired
quarter-turn `(x₀, x₁, x₂, x₃, …) ↦ (-x₁, x₀, -x₃, x₂, …)` (`TauCeti.pairedCoordinateRotation`).
Lifting `L` through `TauCeti.sphereTangentSection` yields a real-analytic unit-norm tangent vector
field on `Sⁿ` (`TauCeti.oddSphereTangentSection` on `EuclideanSpace ℝ (Fin (2 * (m + 1)))`, and
`TauCeti.exists_contMDiff_section_norm_eq_one_of_odd` in general). Consequently `Sⁿ` admits a
nowhere-vanishing continuous (or `C^m`) tangent vector field if and only if `n` is odd
(`TauCeti.exists_continuous_section_ne_zero_iff`, `TauCeti.exists_contMDiff_section_ne_zero_iff`).

## Main definitions

* `TauCeti.greatCircleHomotopy`: the great-circle homotopy `(x, t) ↦ cos(π t) • x + sin(π t) • w x`
  on `sphere (0 : E) 1 × Icc (0 : ℝ) 1` associated to a unit tangent map `w`.
* `TauCeti.oddSphereTangentSection`: the canonical real-analytic unit tangent vector field on
  `sphere (0 : EuclideanSpace ℝ (Fin (2 * (m + 1)))) 1` induced by
  `TauCeti.pairedCoordinateRotation`.

## Main statements

* `TauCeti.exists_contMDiff_unit_tangent_sphere`: a nowhere-vanishing continuous ambient tangent
  map on `Sⁿ` can be replaced by a smooth unit ambient tangent map.
* `TauCeti.odd_of_inner_sphere_eq_zero_of_ne_zero`: if `Sⁿ` carries a nowhere-vanishing continuous
  ambient tangent map, then `n` is odd.
* `TauCeti.exists_eq_zero_of_inner_sphere_eq_zero`, `TauCeti.exists_eq_zero_of_inner_eq_zero`: the
  ambient hairy ball theorem on even-dimensional spheres.
* `TauCeti.exists_eq_zero_of_continuous_section`: the intrinsic tangent-bundle section form of the
  hairy ball theorem on even-dimensional spheres.
* `TauCeti.exists_contMDiff_section_norm_eq_one_of_odd`: every odd-dimensional sphere carries a
  real-analytic unit tangent vector field.
* `TauCeti.exists_contMDiff_section_ne_zero_iff`, `TauCeti.exists_continuous_section_ne_zero_iff`,
  `TauCeti.exists_continuous_inner_sphere_eq_zero_ne_zero_iff`,
  `TauCeti.exists_continuousOn_inner_eq_zero_ne_zero_iff`: `Sⁿ` carries a nowhere-vanishing
  continuous or `C^m` tangent field if and only if `n` is odd.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Problem 16-6.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, Princeton University Press (1965),
  §5.
-/

public section

open Bundle Metric Module Set TopologicalSpace
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace TauCeti

section GreatCircleHomotopy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The great-circle homotopy `sphere (0 : E) 1 × Icc (0 : ℝ) 1 → sphere (0 : E) 1` sending
`(x, t)` to `cos (π t) • x + sin (π t) • w x` along a unit tangent map `w`. At `t = 0` it is the
identity and at `t = 1` it is the antipodal map. -/
def greatCircleHomotopy (w : sphere (0 : E) 1 → E)
    (hw_norm : ∀ x : sphere (0 : E) 1, ‖w x‖ = 1)
    (hw_orth : ∀ x : sphere (0 : E) 1, ⟪w x, (x : E)⟫ = 0)
    (p : sphere (0 : E) 1 × Icc (0 : ℝ) 1) : sphere (0 : E) 1 :=
  ⟨Real.cos (Real.pi * p.2) • (p.1 : E) + Real.sin (Real.pi * p.2) • w p.1,
    mem_sphere_zero_iff_norm.2 <|
      norm_cos_smul_add_sin_smul p.1 ⟨w p.1, mem_sphere_zero_iff_norm.2 (hw_norm p.1)⟩
        (by rw [real_inner_comm]; exact hw_orth p.1) (Real.pi * p.2)⟩

/-- Ambient formula for `TauCeti.greatCircleHomotopy`. -/
@[simp]
theorem coe_greatCircleHomotopy (w : sphere (0 : E) 1 → E)
    (hw_norm : ∀ x : sphere (0 : E) 1, ‖w x‖ = 1)
    (hw_orth : ∀ x : sphere (0 : E) 1, ⟪w x, (x : E)⟫ = 0)
    (p : sphere (0 : E) 1 × Icc (0 : ℝ) 1) :
    (greatCircleHomotopy w hw_norm hw_orth p : E) =
      Real.cos (Real.pi * p.2) • (p.1 : E) + Real.sin (Real.pi * p.2) • w p.1 :=
  (rfl)

/-- At `t = 0`, `TauCeti.greatCircleHomotopy` is the identity of the unit sphere. -/
@[simp]
theorem greatCircleHomotopy_zero (w : sphere (0 : E) 1 → E)
    (hw_norm : ∀ x : sphere (0 : E) 1, ‖w x‖ = 1)
    (hw_orth : ∀ x : sphere (0 : E) 1, ⟪w x, (x : E)⟫ = 0) (x : sphere (0 : E) 1) :
    greatCircleHomotopy w hw_norm hw_orth (x, 0) = x := by
  ext
  simp

/-- At `t = 1`, `TauCeti.greatCircleHomotopy` is the antipodal map of the unit sphere. -/
@[simp]
theorem greatCircleHomotopy_one (w : sphere (0 : E) 1 → E)
    (hw_norm : ∀ x : sphere (0 : E) 1, ‖w x‖ = 1)
    (hw_orth : ∀ x : sphere (0 : E) 1, ⟪w x, (x : E)⟫ = 0) (x : sphere (0 : E) 1) :
    greatCircleHomotopy w hw_norm hw_orth (x, 1) = -x := by
  ext
  simp

/-- If `w` is continuous on the unit sphere, then `TauCeti.greatCircleHomotopy w hw_norm hw_orth`
is continuous, without any finite-dimensionality assumption on `E`. -/
theorem continuous_greatCircleHomotopy {w : sphere (0 : E) 1 → E} (hw : Continuous w)
    (hw_norm : ∀ x : sphere (0 : E) 1, ‖w x‖ = 1)
    (hw_orth : ∀ x : sphere (0 : E) 1, ⟪w x, (x : E)⟫ = 0) :
    Continuous (greatCircleHomotopy w hw_norm hw_orth) := by
  have ht : Continuous (fun p : sphere (0 : E) 1 × Icc (0 : ℝ) 1 ↦ Real.pi * (p.2 : ℝ)) :=
    continuous_const.mul (continuous_subtype_val.comp continuous_snd)
  exact (((Real.continuous_cos.comp ht).smul (continuous_subtype_val.comp continuous_fst)).add
    ((Real.continuous_sin.comp ht).smul (hw.comp continuous_fst))).subtype_mk _

end GreatCircleHomotopy

section GeneralSphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

variable (n) in
/-- If the unit sphere `Sⁿ` carries a nowhere-vanishing continuous map `v : sphere (0 : E) 1 → E`
orthogonal to the radius vector everywhere, then it carries a smooth unit-norm map
`w : sphere (0 : E) 1 → E` orthogonal to the radius vector everywhere. -/
theorem exists_contMDiff_unit_tangent_sphere {v : sphere (0 : E) 1 → E}
    (hv : Continuous v) (ht : ∀ x : sphere (0 : E) 1, ⟪v x, (x : E)⟫ = 0)
    (hne : ∀ x : sphere (0 : E) 1, v x ≠ 0) :
    ∃ w : sphere (0 : E) 1 → E,
      ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ w ∧
        (∀ x : sphere (0 : E) 1, ‖w x‖ = 1) ∧
        ∀ x : sphere (0 : E) 1, ⟪w x, (x : E)⟫ = 0 := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  obtain ⟨u, hu_dist, -⟩ := hv.exists_contMDiff_approx (𝓡 n) (⊤ : ℕ∞) (hv.norm.div_const 2)
    fun x ↦ half_pos (norm_pos_iff.2 (hne x))
  let q : sphere (0 : E) 1 → E := fun x ↦ u x - ⟪(x : E), u x⟫ • (x : E)
  have hq_smooth : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ q :=
    u.contMDiff.sub ((contDiff_inner.contMDiff.comp
      (contMDiff_coe_sphere.prodMk_space u.contMDiff)).smul contMDiff_coe_sphere)
  have hq_orth (x : sphere (0 : E) 1) : ⟪q x, (x : E)⟫ = 0 := by
    dsimp only [q]
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      norm_eq_of_mem_sphere, one_pow, mul_one, real_inner_comm (x : E), sub_self]
  have hq_ne (x : sphere (0 : E) 1) : q x ≠ 0 := by
    intro hq0
    have hvu : ⟪v x, u x⟫ = 0 := by
      have := congrArg (inner ℝ (v x)) hq0
      simpa only [q, inner_sub_right, real_inner_smul_right, ht x, mul_zero, sub_zero,
        inner_zero_right] using this
    have hsq : ‖v x‖ ^ 2 ≤ ‖v x‖ * dist (u x) (v x) := by
      calc ‖v x‖ ^ 2 = ⟪v x, v x - u x⟫ := by
            rw [inner_sub_right, real_inner_self_eq_norm_sq, hvu, sub_zero]
        _ ≤ ‖v x‖ * ‖v x - u x‖ := real_inner_le_norm _ _
        _ = ‖v x‖ * dist (u x) (v x) := by rw [dist_comm, dist_eq_norm]
    nlinarith [hu_dist x, norm_pos_iff.2 (hne x)]
  let q' : sphere (0 : E) 1 → (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens E) :=
    fun x ↦ ⟨q x, hq_ne x⟩
  have hq'_smooth : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ q' := by
    rw [← TauCeti.ContMDiff.subtypeVal_comp_iff]
    exact hq_smooth
  refine ⟨fun x ↦ NormedSpace.normalize (q x), contMDiff_normalize_compl_zero.comp hq'_smooth,
    fun x ↦ NormedSpace.norm_normalize_eq_one_iff.2 (hq_ne x), fun x ↦ ?_⟩
  simp only [NormedSpace.normalize, real_inner_smul_left, hq_orth x, mul_zero]

/-- If `w` is `C^m` on the unit sphere, then `TauCeti.greatCircleHomotopy w hw_norm hw_orth` is
`C^m` on `sphere (0 : E) 1 × Icc (0 : ℝ) 1`. -/
theorem contMDiff_greatCircleHomotopy {m : ℕ∞ω} {w : sphere (0 : E) 1 → E}
    (hw : ContMDiff (𝓡 n) 𝓘(ℝ, E) m w)
    (hw_norm : ∀ x : sphere (0 : E) 1, ‖w x‖ = 1)
    (hw_orth : ∀ x : sphere (0 : E) 1, ⟪w x, (x : E)⟫ = 0) :
    ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡 n) m (greatCircleHomotopy w hw_norm hw_orth) := by
  have ht : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) 𝓘(ℝ) m
      (fun p : sphere (0 : E) 1 × Icc (0 : ℝ) 1 ↦ Real.pi * (p.2 : ℝ)) :=
    contMDiff_const.mul (contMDiff_subtypeVal_Icc.comp contMDiff_snd)
  exact (((Real.contDiff_cos.contMDiff.comp ht).smul
    (contMDiff_coe_sphere.comp contMDiff_fst)).add
      ((Real.contDiff_sin.contMDiff.comp ht).smul (hw.comp contMDiff_fst))).codRestrict_sphere _

variable (n) in
/-- If the unit sphere `Sⁿ` carries a nowhere-vanishing continuous map `v : sphere (0 : E) 1 → E`
orthogonal to the radius vector everywhere, then `n` is odd. -/
theorem odd_of_inner_sphere_eq_zero_of_ne_zero {v : sphere (0 : E) 1 → E}
    (hv : Continuous v) (ht : ∀ x : sphere (0 : E) 1, ⟪v x, (x : E)⟫ = 0)
    (hne : ∀ x : sphere (0 : E) 1, v x ≠ 0) : Odd n := by
  have hE : finrank ℝ E = n + 1 := Fact.out
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : Nontrivial E := finrank_pos_iff (R := ℝ).1 (by rw [hE]; exact Nat.succ_pos n)
  obtain ⟨x₀⟩ : Nonempty (sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  rcases eq_or_ne n 0 with rfl | hn0
  · have hspan : (ℝ ∙ (x₀ : E)) = ⊤ := Submodule.eq_top_of_finrank_eq <|
      (finrank_span_singleton (ne_zero_of_mem_unit_sphere x₀)).trans hE.symm
    have hmem : v x₀ ∈ (ℝ ∙ (x₀ : E))ᗮ :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.2 (ht x₀)
    rw [hspan, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at hmem
    exact absurd hmem (hne x₀)
  · have : NeZero n := ⟨hn0⟩
    have := connectedSpace_sphere (E := E) n
    obtain ⟨w, hw_smooth, hw_norm, hw_orth⟩ := exists_contMDiff_unit_tangent_sphere n hv ht hne
    let o := (finBasisOfFinrankEq ℝ E hE).orientation.sphereOrientation
    have hdeg := degree_eq_of_homotopy o o (contMDiff_id (I := 𝓡 n))
      (contMDiff_neg_sphere (n := n))
      (contMDiff_greatCircleHomotopy hw_smooth hw_norm hw_orth)
      (greatCircleHomotopy_zero w hw_norm hw_orth)
      (greatCircleHomotopy_one w hw_norm hw_orth)
    rw [degree_id, o.degree_neg_sphere] at hdeg
    by_contra hnotodd
    rw [(Nat.not_odd_iff_even.1 hnotodd).add_one.neg_one_pow] at hdeg
    omega

/-- **The hairy ball theorem (sphere-domain ambient form).** Every continuous map
`v : sphere (0 : E) 1 → E` on an even-dimensional unit sphere satisfying `⟪v x, (x : E)⟫ = 0`
vanishes at some point. -/
theorem exists_eq_zero_of_inner_sphere_eq_zero (hn : Even n) {v : sphere (0 : E) 1 → E}
    (hv : Continuous v) (ht : ∀ x : sphere (0 : E) 1, ⟪v x, (x : E)⟫ = 0) :
    ∃ x : sphere (0 : E) 1, v x = 0 := by
  by_contra! hne
  exact Nat.not_odd_iff_even.2 hn (odd_of_inner_sphere_eq_zero_of_ne_zero n hv ht hne)

/-- **The hairy ball theorem (ambient form).** Every map `v : E → E` that is continuous on an
even-dimensional unit sphere `Sⁿ ⊆ E` and tangent to it (`⟪v x, x⟫ = 0` for all `x ∈ Sⁿ`) vanishes
at some point of `Sⁿ`. -/
theorem exists_eq_zero_of_inner_eq_zero (hn : Even n) {v : E → E}
    (hv : ContinuousOn v (sphere (0 : E) 1))
    (ht : ∀ x ∈ sphere (0 : E) 1, ⟪v x, x⟫ = 0) :
    ∃ x ∈ sphere (0 : E) 1, v x = 0 := by
  obtain ⟨x, hx⟩ := exists_eq_zero_of_inner_sphere_eq_zero hn
    (continuousOn_iff_continuous_domRestrict.1 hv) fun x ↦ ht x x.2
  exact ⟨x, x.2, hx⟩

/-- **The hairy ball theorem (tangent-bundle section form).** Every continuous section of the
tangent bundle of an even-dimensional unit sphere `sphere (0 : E) 1` over `𝓡 n` vanishes at some
point. -/
theorem exists_eq_zero_of_continuous_section (hn : Even n)
    {V : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
    (hV : Continuous
      (fun x ↦ (⟨x, V x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1)))) :
    ∃ x, V x = 0 := by
  obtain ⟨x, hx⟩ := exists_eq_zero_of_inner_sphere_eq_zero hn
    (continuous_mvfderiv_subtypeVal_sphere_section hV)
    (fun x ↦ inner_mvfderiv_subtypeVal_sphere_coe x (V x))
  exact ⟨x, injective_mvfderiv_subtypeVal_sphere x (hx.trans (map_zero _).symm)⟩

/-- Every odd-dimensional unit sphere carries a real-analytic ambient map `v : E → E` orthogonal to
every vector and of unit norm on the unit sphere. -/
theorem exists_contDiff_inner_eq_zero_norm_eq_one_of_odd (hn : Odd n) :
    ∃ v : E → E, ContDiff ℝ ω v ∧ (∀ x : E, ⟪v x, x⟫ = 0) ∧
      ∀ x ∈ sphere (0 : E) 1, ‖v x‖ = 1 := by
  have hE : finrank ℝ E = n + 1 := Fact.out
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have hEven : Even (finrank ℝ E) := hE ▸ hn.add_one
  obtain ⟨L, hL⟩ := exists_linearIsometryEquiv_inner_self_eq_zero hEven
  refine ⟨L, (L.toContinuousLinearEquiv : E →L[ℝ] E).contDiff, hL, fun x hx ↦ ?_⟩
  rw [L.norm_map, norm_eq_of_mem_sphere ⟨x, hx⟩]

/-- Every odd-dimensional unit sphere carries a `C^m` unit-norm section of its tangent bundle, at
every regularity `m : ℕ∞ω`. -/
theorem exists_contMDiff_section_norm_eq_one_of_odd {m : ℕ∞ω} (hn : Odd n) :
    ∃ V : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x,
      ContMDiff (𝓡 n) (𝓡 n).tangent m
        (fun x ↦ (⟨x, V x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) ∧
      ∀ x : sphere (0 : E) 1, ‖V x‖ = 1 := by
  obtain ⟨v, hv, horth, hnorm⟩ := exists_contDiff_inner_eq_zero_norm_eq_one_of_odd (E := E) hn
  refine ⟨sphereTangentSection n (fun x ↦ v x) (fun x ↦ horth x), ?_, fun x ↦ ?_⟩
  · rw [contMDiff_sphereTangentSection_iff]
    exact (hv.of_le le_top).contMDiff.comp contMDiff_coe_sphere
  · rw [norm_sphereTangentSection, hnorm x x.2]

/-- **Tangent field dichotomy (`C^m` section form).** The unit sphere `Sⁿ` carries a
nowhere-vanishing `C^m` section of its tangent bundle if and only if `n` is odd. -/
theorem exists_contMDiff_section_ne_zero_iff {m : ℕ∞ω} :
    (∃ V : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x,
      ContMDiff (𝓡 n) (𝓡 n).tangent m
        (fun x ↦ (⟨x, V x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) ∧
      ∀ x : sphere (0 : E) 1, V x ≠ 0) ↔ Odd n := by
  constructor
  · rintro ⟨V, hV, hne⟩
    by_contra hnotodd
    obtain ⟨x, hx⟩ :=
      exists_eq_zero_of_continuous_section (Nat.not_odd_iff_even.1 hnotodd) hV.continuous
    exact hne x hx
  · intro hn
    obtain ⟨V, hV, hnorm⟩ := exists_contMDiff_section_norm_eq_one_of_odd (E := E) (m := m) hn
    exact ⟨V, hV, fun x ↦ norm_ne_zero_iff.1 (by rw [hnorm x]; exact one_ne_zero)⟩

/-- **Tangent field dichotomy (continuous section form).** The unit sphere `Sⁿ` carries a
nowhere-vanishing continuous section of its tangent bundle if and only if `n` is odd. -/
theorem exists_continuous_section_ne_zero_iff :
    (∃ V : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x,
      Continuous (fun x ↦ (⟨x, V x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) ∧
      ∀ x : sphere (0 : E) 1, V x ≠ 0) ↔ Odd n := by
  simpa only [contMDiff_zero_iff (I := 𝓡 n) (I' := (𝓡 n).tangent)] using
    exists_contMDiff_section_ne_zero_iff (E := E) (n := n) (m := 0)

/-- **Tangent field dichotomy (sphere-domain ambient form).** The unit sphere `Sⁿ` carries a
nowhere-vanishing continuous map `v : sphere (0 : E) 1 → E` with `⟪v x, (x : E)⟫ = 0` everywhere
if and only if `n` is odd. -/
theorem exists_continuous_inner_sphere_eq_zero_ne_zero_iff :
    (∃ v : sphere (0 : E) 1 → E,
      Continuous v ∧ (∀ x : sphere (0 : E) 1, ⟪v x, (x : E)⟫ = 0) ∧
        ∀ x : sphere (0 : E) 1, v x ≠ 0) ↔ Odd n := by
  constructor
  · rintro ⟨v, hv, ht, hne⟩
    exact odd_of_inner_sphere_eq_zero_of_ne_zero n hv ht hne
  · intro hn
    obtain ⟨v, hv, horth, hnorm⟩ := exists_contDiff_inner_eq_zero_norm_eq_one_of_odd (E := E) hn
    refine ⟨fun x ↦ v x, hv.continuous.comp continuous_subtype_val, fun x ↦ horth x, fun x ↦ ?_⟩
    exact norm_ne_zero_iff.1 (by rw [hnorm x x.2]; exact one_ne_zero)

/-- **Tangent field dichotomy (ambient form).** There exists a map `v : E → E` continuous on the
unit sphere `Sⁿ ⊆ E`, tangent to it (`⟪v x, x⟫ = 0` on `Sⁿ`), and nowhere vanishing on `Sⁿ` if and
only if `n` is odd. -/
theorem exists_continuousOn_inner_eq_zero_ne_zero_iff :
    (∃ v : E → E,
      ContinuousOn v (sphere (0 : E) 1) ∧
        (∀ x ∈ sphere (0 : E) 1, ⟪v x, x⟫ = 0) ∧
        ∀ x ∈ sphere (0 : E) 1, v x ≠ 0) ↔ Odd n := by
  constructor
  · rintro ⟨v, hv, ht, hne⟩
    exact odd_of_inner_sphere_eq_zero_of_ne_zero n
      (continuousOn_iff_continuous_domRestrict.1 hv) (fun x ↦ ht x x.2) (fun x ↦ hne x x.2)
  · intro hn
    obtain ⟨v, hv, horth, hnorm⟩ := exists_contDiff_inner_eq_zero_norm_eq_one_of_odd (E := E) hn
    refine ⟨v, hv.continuous.continuousOn, fun x _ ↦ horth x, fun x hx ↦ ?_⟩
    exact norm_ne_zero_iff.1 (by rw [hnorm x hx]; exact one_ne_zero)

end GeneralSphere

section OddEuclideanSphere

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

/-- The canonical real-analytic unit tangent vector field on the odd-dimensional Euclidean sphere
`S^(2m+1) = sphere (0 : EuclideanSpace ℝ (Fin (2 * (m + 1)))) 1`, whose ambient image at `x` is the
paired quarter-turn `TauCeti.pairedCoordinateRotation (m + 1) x`
(`(x₀, x₁, x₂, x₃, …) ↦ (-x₁, x₀, -x₃, x₂, …)`). -/
def oddSphereTangentSection (m : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (2 * (m + 1)))) 1) :
    TangentSpace (𝓡 (2 * m + 1)) x :=
  sphereTangentSection (2 * m + 1) (fun y ↦ pairedCoordinateRotation (m + 1) y)
    (fun y ↦ inner_pairedCoordinateRotation_self (n := m + 1) y) x

/-- Pushing `TauCeti.oddSphereTangentSection m x` into `EuclideanSpace ℝ (Fin (2 * (m + 1)))`
recovers `TauCeti.pairedCoordinateRotation (m + 1) x`. -/
theorem mvfderiv_subtypeVal_oddSphereTangentSection (m : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (2 * (m + 1)))) 1) :
    mvfderiv (𝓡 (2 * m + 1))
        ((↑) : sphere (0 : EuclideanSpace ℝ (Fin (2 * (m + 1)))) 1 →
          EuclideanSpace ℝ (Fin (2 * (m + 1))))
        x (oddSphereTangentSection m x) =
      pairedCoordinateRotation (m + 1) x := by
  rw [oddSphereTangentSection, mvfderiv_subtypeVal_sphereTangentSection]

/-- Manifold differential form of `TauCeti.mvfderiv_subtypeVal_oddSphereTangentSection`. -/
@[simp]
theorem mfderiv_subtypeVal_oddSphereTangentSection (m : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (2 * (m + 1)))) 1) :
    mfderiv (𝓡 (2 * m + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * (m + 1))))
        ((↑) : sphere (0 : EuclideanSpace ℝ (Fin (2 * (m + 1)))) 1 →
          EuclideanSpace ℝ (Fin (2 * (m + 1))))
        x (oddSphereTangentSection m x) =
      pairedCoordinateRotation (m + 1) x := by
  rw [oddSphereTangentSection, mfderiv_subtypeVal_sphereTangentSection]

/-- `TauCeti.oddSphereTangentSection m` has unit round norm at every point of `S^(2m+1)`. -/
theorem norm_oddSphereTangentSection (m : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (2 * (m + 1)))) 1) :
    ‖oddSphereTangentSection m x‖ = 1 := by
  rw [oddSphereTangentSection, norm_sphereTangentSection, LinearIsometryEquiv.norm_map,
    norm_eq_of_mem_sphere]

/-- `TauCeti.oddSphereTangentSection m` vanishes nowhere on `S^(2m+1)`. -/
theorem oddSphereTangentSection_ne_zero (m : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (2 * (m + 1)))) 1) :
    oddSphereTangentSection m x ≠ 0 :=
  norm_ne_zero_iff.1 (by rw [norm_oddSphereTangentSection]; exact one_ne_zero)

/-- `TauCeti.oddSphereTangentSection m` is `C^k` at every regularity `k : ℕ∞ω` (in particular
real-analytic). -/
theorem contMDiff_oddSphereTangentSection {k : ℕ∞ω} (m : ℕ) :
    ContMDiff (𝓡 (2 * m + 1)) (𝓡 (2 * m + 1)).tangent k
      (fun x ↦ (⟨x, oddSphereTangentSection m x⟩ :
        TangentBundle (𝓡 (2 * m + 1))
          (sphere (0 : EuclideanSpace ℝ (Fin (2 * (m + 1)))) 1))) := by
  dsimp only [oddSphereTangentSection]
  rw [contMDiff_sphereTangentSection_iff]
  exact ((pairedCoordinateRotation (m + 1)).toContinuousLinearEquiv :
    EuclideanSpace ℝ (Fin (2 * (m + 1))) →L[ℝ]
      EuclideanSpace ℝ (Fin (2 * (m + 1)))).contDiff.contMDiff.comp contMDiff_coe_sphere

/-- `TauCeti.oddSphereTangentSection m` is a continuous section of the tangent bundle of
`S^(2m+1)`. -/
theorem continuous_oddSphereTangentSection (m : ℕ) :
    Continuous
      (fun x ↦ (⟨x, oddSphereTangentSection m x⟩ :
        TangentBundle (𝓡 (2 * m + 1))
          (sphere (0 : EuclideanSpace ℝ (Fin (2 * (m + 1)))) 1))) :=
  (contMDiff_oddSphereTangentSection (k := 0) m).continuous

end OddEuclideanSphere

end TauCeti
