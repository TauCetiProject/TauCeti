/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Global
public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import Mathlib.Topology.Homotopy.Basic
import TauCeti.Analysis.InnerProductSpace.SkewIsometry
import TauCeti.Analysis.InnerProductSpace.Sphere.Trigonometric
import TauCeti.Geometry.Manifold.SmoothApprox
import TauCeti.Geometry.Sphere.Connected

/-!
# The hairy ball theorem

Let `E` be a real inner product space of dimension `n + 1` with `n` even, and let `Sⁿ` be its unit
sphere. The antipodal map of `Sⁿ` is not homotopic to the identity
(`TauCeti.not_homotopic_id_neg_sphere`), and so every continuous tangent vector field on `Sⁿ`
vanishes somewhere. The latter is stated twice: for a map `v : E → E` continuous on `Sⁿ` with
`⟪v x, x⟫ = 0` there (`TauCeti.exists_eq_zero_of_inner_eq_zero`), and for a continuous section of
the tangent bundle of Mathlib's manifold `sphere (0 : E) 1`
(`TauCeti.exists_eq_zero_of_continuous_section`), which the derivative of the inclusion carries to
a field of the first kind.

For `n ≥ 2` the proof is by the mapping degree. Homotopic smooth maps into the compact manifold
`Sⁿ` are smoothly homotopic (`ContinuousMap.Homotopic.exists_contMDiff_homotopy`), smoothly
homotopic maps have the same degree (`TauCeti.degree_eq_of_homotopy`), the identity has degree `1`
and the antipodal map has degree `(-1)^(n+1) = -1`
(`TauCeti.Manifold.Orientation.degree_neg_sphere`).
For `n = 0` the sphere is the two points `±x` of a line, and the path `t ↦ H (t, x)` of a homotopy
`H` would join `x` to `-x`. A nowhere-vanishing continuous tangent field `v` gives a homotopy from
the identity to the antipodal map along great circles,
`(t, x) ↦ cos (π t) • x + sin (π t) • v x / ‖v x‖`.

The parity hypothesis is needed. In even dimension `n + 1` a linear isometry `J` with
`⟪J x, x⟫ = 0` (`TauCeti.exists_linearIsometryEquiv_inner_map_self_eq_zero`), such as
`(x₁, x₂, x₃, x₄, …) ↦ (-x₂, x₁, -x₄, x₃, …)`, is a nowhere-vanishing tangent field on `Sⁿ`; so `Sⁿ`
carries one exactly when `n` is odd (`TauCeti.exists_inner_eq_zero_and_ne_zero_iff_odd`). On the
unit circle of `ℂ` it is `z ↦ i z`.

## Main results

* `TauCeti.not_homotopic_id_neg_sphere`: the antipodal map of an even-dimensional unit sphere is
  not homotopic to the identity.
* `TauCeti.exists_eq_zero_of_inner_eq_zero`: a continuous tangent vector field on an
  even-dimensional unit sphere vanishes somewhere.
* `TauCeti.exists_eq_zero_of_continuous_section`: a continuous section of the tangent bundle of an
  even-dimensional unit sphere vanishes somewhere.
* `TauCeti.exists_inner_eq_zero_and_ne_zero_iff_odd`: the unit sphere `Sⁿ` carries a
  nowhere-vanishing continuous tangent field exactly when `n` is odd.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Problem 16-6 and Chapter 17, section Degree Theory.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5, Theorem 1 and its proof by the homotopy from the identity to the antipodal map.
-/

public section

noncomputable section

open Metric Module Set
open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- For `n ≥ 1`, a homotopy from the identity of `Sⁿ` to the antipodal map can be taken smooth,
so the two maps have the same degree; that forces `n` to be odd. -/
private theorem not_homotopic_id_neg_sphere_of_neZero [NeZero n] (hn : Even n) :
    ¬ (ContinuousMap.id (sphere (0 : E) 1)).Homotopic (-ContinuousMap.id _) := fun h ↦ by
  have hE : finrank ℝ E = n + 1 := Fact.out
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  have := connectedSpace_sphere (E := E) n
  have : Nonempty (sphere (0 : E) 1) :=
    ((NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).2 zero_le_one).to_subtype
  obtain ⟨K, hK, hK₀, hK₁⟩ := h.exists_contMDiff_homotopy (I := 𝓡 n) (J := 𝓡 n) ⊤ contMDiff_id
    contMDiff_neg_sphere
  -- Restrict the smooth homotopy `K : Sⁿ × ℝ → Sⁿ` to the times in `[0, 1]`.
  have hF : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡 n) ∞
      fun p : sphere (0 : E) 1 × Icc (0 : ℝ) 1 ↦ K (p.1, p.2) :=
    hK.comp (contMDiff_fst.prodMk (contMDiff_subtypeVal_Icc.comp contMDiff_snd))
  let o := (finBasisOfFinrankEq ℝ E hE).orientation.sphereOrientation
  have hdeg := degree_eq_of_homotopy o o contMDiff_id contMDiff_neg_sphere hF
    (fun x ↦ by simpa using hK₀ x) (fun x ↦ by simpa using hK₁ x)
  rw [degree_id, Manifold.Orientation.degree_neg_sphere, hn.add_one.neg_one_pow] at hdeg
  exact absurd hdeg (by decide)

/-- **The antipodal map of an even-dimensional sphere is not homotopic to the identity.** On the
unit sphere `Sⁿ` of a real inner product space of dimension `n + 1`, with `n` even, the identity
and the antipodal map `x ↦ -x` are not homotopic. -/
theorem not_homotopic_id_neg_sphere (hn : Even n) :
    ¬ (ContinuousMap.id (sphere (0 : E) 1)).Homotopic (-ContinuousMap.id _) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · -- `S⁰` is the two points `±x` of a line: along a homotopy `H`, the continuous function
    -- `t ↦ ⟪H (t, x), x⟫` only takes the values `±1` but goes from `1` to `-1`.
    rintro ⟨H⟩
    have hE : finrank ℝ E = 1 := Fact.out
    have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
    obtain ⟨x⟩ := ((NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).2 zero_le_one).to_subtype
    have hx1 : ⟪(x : E), (x : E)⟫_ℝ = 1 := by
      rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere, one_pow]
    have hφ : Continuous fun t : unitInterval ↦ ⟪(H (t, x) : E), (x : E)⟫_ℝ := by fun_prop
    obtain ⟨t, ht⟩ : (0 : ℝ) ∈ range fun t : unitInterval ↦ ⟪(H (t, x) : E), (x : E)⟫_ℝ :=
      intermediate_value_univ 1 0 hφ ⟨by simp, by simp⟩
    dsimp only at ht
    -- `H (t, x)` is a multiple `c • x` of norm one, so `c = ±1`, yet `⟪H (t, x), x⟫ = c` is `0`.
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' (x : E) (ne_zero_of_mem_unit_sphere x)).1 hE
      (H (t, x))
    have hc1 := norm_eq_of_mem_sphere (H (t, x))
    rw [← hc, norm_smul, norm_eq_of_mem_sphere, mul_one] at hc1
    rw [← hc, real_inner_smul_left, hx1, mul_one] at ht
    simp [ht] at hc1
  · have : NeZero n := ⟨hpos.ne'⟩
    exact not_homotopic_id_neg_sphere_of_neZero hn

/-- The hairy ball theorem for a continuous tangent field defined on the sphere: if it vanished
nowhere, the great circles `t ↦ cos (π t) • x + sin (π t) • v x / ‖v x‖` would be a homotopy from
the identity to the antipodal map. -/
private theorem exists_eq_zero_of_continuous_of_inner_eq_zero (hn : Even n)
    {v : sphere (0 : E) 1 → E} (hv : Continuous v) (ht : ∀ x, ⟪v x, (x : E)⟫_ℝ = 0) :
    ∃ x, v x = 0 := by
  by_contra! h0
  -- The unit tangent field `u = v / ‖v‖`.
  let u : sphere (0 : E) 1 → sphere (0 : E) 1 := fun x ↦
    ⟨‖v x‖⁻¹ • v x, by simp [norm_smul, norm_ne_zero_iff.2 (h0 x)]⟩
  have hu : Continuous u :=
    ((hv.norm.inv₀ fun x ↦ norm_ne_zero_iff.2 (h0 x)).smul hv).subtype_mk _
  have hxu (x : sphere (0 : E) 1) : ⟪(x : E), (u x : E)⟫_ℝ = 0 := by
    rw [real_inner_smul_right, real_inner_comm, ht, mul_zero]
  refine not_homotopic_id_neg_sphere hn ⟨
    { toFun p := ⟨Real.cos (Real.pi * p.1) • (p.2 : E) + Real.sin (Real.pi * p.1) • (u p.2 : E),
        mem_sphere_zero_iff_norm.2 (norm_cos_smul_add_sin_smul _ _ (hxu p.2) _)⟩
      continuous_toFun := by fun_prop
      map_zero_left x := Subtype.ext (by simp)
      map_one_left x := Subtype.ext (by simp) }⟩

/-- **The hairy ball theorem.** A continuous tangent vector field on an even-dimensional unit
sphere vanishes somewhere: if `v : E → E` is continuous on the unit sphere `Sⁿ` of a real inner
product space `E` of dimension `n + 1`, with `n` even, and `⟪v x, x⟫ = 0` for `x ∈ Sⁿ`, then
`v x = 0` for some `x ∈ Sⁿ`. -/
theorem exists_eq_zero_of_inner_eq_zero (hn : Even n) {v : E → E}
    (hv : ContinuousOn v (sphere (0 : E) 1))
    (ht : ∀ x ∈ sphere (0 : E) 1, ⟪v x, x⟫_ℝ = 0) :
    ∃ x ∈ sphere (0 : E) 1, v x = 0 := by
  obtain ⟨x, hx⟩ := exists_eq_zero_of_continuous_of_inner_eq_zero hn hv.domRestrict
    fun x ↦ ht x x.2
  exact ⟨x, x.2, hx⟩

/-- **The hairy ball theorem, section form.** A continuous section of the tangent bundle of the
unit sphere `Sⁿ` of a real inner product space of dimension `n + 1`, with `n` even, vanishes at
some point. -/
theorem exists_eq_zero_of_continuous_section (hn : Even n)
    {V : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
    (hV : Continuous fun x ↦ (⟨x, V x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) :
    ∃ x, V x = 0 := by
  -- Read in `E` through the derivative of the inclusion, `V` is a tangent field of `Sⁿ`.
  set ι : sphere (0 : E) 1 → E := (↑)
  have hT : Continuous fun p : TangentBundle (𝓡 n) (sphere (0 : E) 1) ↦
      (tangentMap (𝓡 n) 𝓘(ℝ, E) ι p).2 :=
    continuous_snd.comp ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).continuous.comp
      (contMDiff_coe_sphere.continuous_tangentMap le_rfl))
  have hv : Continuous fun x ↦ mvfderiv (𝓡 n) ι x (V x) :=
    (hT.comp hV).congr fun x ↦
      ((mvfderiv_apply_eq_mfderiv_apply _ x (V x)).trans tangentMap_snd.symm).symm
  obtain ⟨x, hx⟩ := exists_eq_zero_of_continuous_of_inner_eq_zero (n := n) hn hv fun x ↦ by
    have hmem : mvfderiv (𝓡 n) ι x (V x) ∈ (ℝ ∙ (x : E))ᗮ := by
      rw [← range_mvfderiv_subtypeVal (n := n)]
      exact LinearMap.mem_range_self _ _
    rw [real_inner_comm]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 hmem
  exact ⟨x, injective_mvfderiv_subtypeVal_sphere x (hx.trans (map_zero _).symm)⟩

/-- **Tangent fields on spheres.** The unit sphere `Sⁿ` of a real inner product space of dimension
`n + 1` carries a nowhere-vanishing continuous tangent vector field exactly when `n` is odd. For odd
`n` one such field is `x ↦ J x` for a linear isometry `J` with `⟪J x, x⟫ = 0`, which reads
`(x₁, x₂, x₃, x₄, …) ↦ (-x₂, x₁, -x₄, x₃, …)` in a suitable orthonormal basis. -/
theorem exists_inner_eq_zero_and_ne_zero_iff_odd :
    (∃ v : E → E, ContinuousOn v (sphere (0 : E) 1) ∧
      ∀ x ∈ sphere (0 : E) 1, ⟪v x, x⟫_ℝ = 0 ∧ v x ≠ 0) ↔ Odd n := by
  refine ⟨fun ⟨v, hv, h⟩ ↦ Nat.not_even_iff_odd.1 fun hn ↦ ?_, fun hn ↦ ?_⟩
  · obtain ⟨x, hx, h0⟩ := exists_eq_zero_of_inner_eq_zero hn hv fun x hx ↦ (h x hx).1
    exact (h x hx).2 h0
  · have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
    obtain ⟨J, hJ⟩ := exists_linearIsometryEquiv_inner_map_self_eq_zero (E := E)
      (by rw [Fact.out (p := finrank ℝ E = n + 1)]; exact hn.add_one)
    exact ⟨J, J.continuous.continuousOn, fun x hx ↦ ⟨hJ x, fun h ↦
      ne_zero_of_mem_unit_sphere ⟨x, hx⟩ (J.map_eq_zero_iff.1 h)⟩⟩

end TauCeti
