/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Global
public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
public import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Path
import TauCeti.AlgebraicTopology.Sphere.Zero
import TauCeti.Analysis.InnerProductSpace.Sphere.Trigonometric
import TauCeti.Analysis.Normed.Module.Normalize
import TauCeti.Geometry.Manifold.Riemannian.Sphere.TangentSection
import TauCeti.Geometry.Manifold.SmoothApprox
import TauCeti.Geometry.Sphere.Connected
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis

/-!
# The hairy ball theorem

Let `E` be a real inner product space of dimension `n + 1` with `n` even, and let `Sⁿ` be its unit
sphere. The antipodal map of `Sⁿ` is not homotopic to the identity
(`TauCeti.not_homotopic_id_neg_sphere`), and so every continuous tangent vector field on `Sⁿ`
vanishes somewhere. The latter is stated three times: for a continuous map `v : Sⁿ → E` with
`⟪v x, x⟫ = 0` (`TauCeti.exists_eq_zero_of_continuous_of_inner_eq_zero`), for a map `v : E → E`
continuous on `Sⁿ` with `⟪v x, x⟫ = 0` there (`TauCeti.exists_eq_zero_of_inner_eq_zero`), and for a
continuous section of the tangent bundle of Mathlib's manifold `sphere (0 : E) 1`
(`TauCeti.exists_eq_zero_of_continuous_section`), which the derivative of the inclusion carries to
a field of the first kind.

For `n ≥ 2` the proof is by the mapping degree. Homotopic smooth maps into the compact manifold
`Sⁿ` are smoothly homotopic (`ContinuousMap.Homotopic.exists_contMDiff_homotopy`), smoothly
homotopic maps have the same degree (`TauCeti.degree_eq_of_homotopy`), the identity has degree `1`
and the antipodal map has degree `(-1)^(n+1) = -1`
(`TauCeti.Manifold.Orientation.degree_neg_sphere`).
For `n = 0` the sphere is the two points `±x` of a line, and the path `t ↦ H (t, x)` of a homotopy
`H` would join `x` to `-x`, which lie in distinct path components
(`TauCeti.zerothHomotopy_mk_neg_ne`). A nowhere-vanishing continuous tangent field `v` gives a
homotopy from the identity to the antipodal map along great circles,
`(t, x) ↦ cos (π t) • x + sin (π t) • v x / ‖v x‖`.

The parity hypothesis is needed. In even dimension `n + 1` an orthogonal almost complex structure
`J` (`TauCeti.AlmostComplexStructure.exists_forall_norm_apply_eq`), such as
`(x₁, x₂, x₃, x₄, …) ↦ (-x₂, x₁, -x₄, x₃, …)`, satisfies `⟪J x, x⟫ = 0`
(`TauCeti.AlmostComplexStructure.inner_apply_self`) and lifts through
`TauCeti.sphereTangentSection` to a real-analytic unit-norm section of the tangent bundle of `Sⁿ`
(`TauCeti.exists_contMDiff_section_norm_eq_one_of_odd`). Consequently `Sⁿ` carries a
nowhere-vanishing tangent field — whether as a `C^m` section
(`TauCeti.exists_contMDiff_section_ne_zero_iff_odd`), a continuous section
(`TauCeti.exists_continuous_section_ne_zero_iff_odd`), a continuous sphere-domain map `Sⁿ → E`
(`TauCeti.exists_continuous_inner_eq_zero_and_ne_zero_iff_odd`), or an ambient map `E → E`
continuous on `Sⁿ` (`TauCeti.exists_continuousOn_inner_eq_zero_and_ne_zero_iff_odd`) — if and only
if `n` is odd. On the unit circle of `ℂ` one such field is `z ↦ i z`.

## Main results

* `TauCeti.not_homotopic_id_neg_sphere`: the antipodal map of an even-dimensional unit sphere is
  not homotopic to the identity.
* `TauCeti.exists_eq_zero_of_continuous_of_inner_eq_zero`: a continuous tangent vector field
  `v : Sⁿ → E` on an even-dimensional unit sphere vanishes somewhere.
* `TauCeti.exists_eq_zero_of_inner_eq_zero`: the same for a field `v : E → E` continuous on the
  even-dimensional unit sphere.
* `TauCeti.exists_eq_zero_of_continuous_section`: a continuous section of the tangent bundle of an
  even-dimensional unit sphere vanishes somewhere.
* `TauCeti.exists_contMDiff_section_norm_eq_one_of_odd`: an odd-dimensional unit sphere carries a
  `C^m` unit-norm section of its tangent bundle at every regularity `m : ℕ∞ω`.
* `TauCeti.exists_contMDiff_section_ne_zero_iff_odd`,
  `TauCeti.exists_continuous_section_ne_zero_iff_odd`,
  `TauCeti.exists_continuous_inner_eq_zero_and_ne_zero_iff_odd`,
  `TauCeti.exists_continuousOn_inner_eq_zero_and_ne_zero_iff_odd`: the unit sphere `Sⁿ` carries a
  nowhere-vanishing `C^m` or continuous tangent field (as a section, on `Sⁿ`, or ambiently on `E`)
  exactly when `n` is odd.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Problem 16-6 and Chapter 17, section Degree Theory.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5, Theorem 1 and its proof by the homotopy from the identity to the antipodal map.
-/

public section

noncomputable section

open Bundle Metric Module Set
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
  have := connectedSpace_sphere (E := E) n
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
  · -- `S⁰` is the two points `±x` of a line, in distinct path components, but along a homotopy
    -- `H` the path `t ↦ H (t, x)` joins `x` to `-x`.
    rintro ⟨H⟩
    have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (R := ℝ) (n := 0) Fact.out
    obtain ⟨x⟩ := ((NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).2 zero_le_one).to_subtype
    exact zerothHomotopy_mk_neg_ne Fact.out x (ZerothHomotopy.sound (H.evalAt x)).symm
  · have : NeZero n := ⟨hpos.ne'⟩
    exact not_homotopic_id_neg_sphere_of_neZero hn

/-- **The hairy ball theorem, sphere-domain form.** A continuous tangent vector field defined on
an even-dimensional unit sphere vanishes somewhere: if `v : Sⁿ → E` is continuous on the unit sphere
`Sⁿ` of a real inner product space `E` of dimension `n + 1`, with `n` even, and `⟪v x, x⟫ = 0` for
every `x`, then `v x = 0` for some `x`. If `v` vanished nowhere, the great circles
`t ↦ cos (π t) • x + sin (π t) • v x / ‖v x‖` would be a homotopy from the identity to the antipodal
map. -/
theorem exists_eq_zero_of_continuous_of_inner_eq_zero (hn : Even n)
    {v : sphere (0 : E) 1 → E} (hv : Continuous v) (ht : ∀ x, ⟪v x, (x : E)⟫_ℝ = 0) :
    ∃ x, v x = 0 := by
  by_contra! h0
  -- The unit tangent field `u = v / ‖v‖`.
  let u := normalizeToSphere v hv h0
  have hxu (x : sphere (0 : E) 1) : ⟪(x : E), (u x : E)⟫_ℝ = 0 := by
    rw [coe_normalizeToSphere_apply, NormedSpace.normalize, real_inner_smul_right, real_inner_comm,
      ht, mul_zero]
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
  obtain ⟨x, hx⟩ := exists_eq_zero_of_continuous_of_inner_eq_zero (n := n) hn
    (continuous_section_sphere_iff.1 hV)
    (fun x ↦ inner_mvfderiv_subtypeVal_sphere_coe x (V x))
  exact ⟨x, injective_mvfderiv_subtypeVal_sphere x (hx.trans (map_zero _).symm)⟩

/-- **Unit tangent vector fields on odd-dimensional spheres.** On the unit sphere `Sⁿ` of a real
inner product space `E` of dimension `n + 1`, with `n` odd, there exists a `C^m` section of the
tangent bundle of `Sⁿ` of unit round norm everywhere, at every regularity `m : ℕ∞ω` (including
real-analytic `m = ω`). One such section is the lift through `TauCeti.sphereTangentSection` of an
orthogonal almost complex structure on `E`. -/
theorem exists_contMDiff_section_norm_eq_one_of_odd {m : ℕ∞ω} (hn : Odd n) :
    ∃ V : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x,
      ContMDiff (𝓡 n) (𝓡 n).tangent m
        (fun x ↦ (⟨x, V x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) ∧
      ∀ x : sphere (0 : E) 1, ‖V x‖ = 1 := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  obtain ⟨J, hJ⟩ := AlmostComplexStructure.exists_forall_norm_apply_eq (V := E)
    (by rw [Fact.out (p := finrank ℝ E = n + 1)]; exact hn.add_one)
  let L : E →ₗᵢ[ℝ] E := ⟨J.toLinearMap, hJ⟩
  refine ⟨sphereTangentSection n (fun x ↦ L x)
    (fun x ↦ J.inner_apply_self L.inner_map_map x), ?_, fun x ↦ ?_⟩
  · rw [contMDiff_sphereTangentSection_iff]
    exact (L.toContinuousLinearMap.contDiff.of_le le_top).contMDiff.comp contMDiff_coe_sphere
  · rw [norm_sphereTangentSection, L.norm_map, norm_eq_of_mem_sphere x]

/-- **Tangent fields on spheres, `C^m` section form.** The unit sphere `Sⁿ` of a real inner product
space of dimension `n + 1` carries a nowhere-vanishing `C^m` section of its tangent bundle, at any
regularity `m : ℕ∞ω`, if and only if `n` is odd. -/
theorem exists_contMDiff_section_ne_zero_iff_odd {m : ℕ∞ω} :
    (∃ V : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x,
      ContMDiff (𝓡 n) (𝓡 n).tangent m
        (fun x ↦ (⟨x, V x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) ∧
      ∀ x : sphere (0 : E) 1, V x ≠ 0) ↔ Odd n := by
  refine ⟨fun ⟨V, hV, hne⟩ ↦ Nat.not_even_iff_odd.1 fun hn ↦ ?_, fun hn ↦ ?_⟩
  · obtain ⟨x, hx⟩ := exists_eq_zero_of_continuous_section hn hV.continuous
    exact hne x hx
  · obtain ⟨V, hV, hnorm⟩ := exists_contMDiff_section_norm_eq_one_of_odd (E := E) (m := m) hn
    exact ⟨V, hV, fun x ↦ norm_ne_zero_iff.1 (by rw [hnorm x]; exact one_ne_zero)⟩

/-- **Tangent fields on spheres, continuous section form.** The unit sphere `Sⁿ` of a real inner
product space of dimension `n + 1` carries a nowhere-vanishing continuous section of its tangent
bundle if and only if `n` is odd. -/
theorem exists_continuous_section_ne_zero_iff_odd :
    (∃ V : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x,
      Continuous (fun x ↦ (⟨x, V x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) ∧
      ∀ x : sphere (0 : E) 1, V x ≠ 0) ↔ Odd n := by
  simp_rw [← contMDiff_zero_iff (I := 𝓡 n) (I' := (𝓡 n).tangent)]
  exact exists_contMDiff_section_ne_zero_iff_odd (E := E) (n := n) (m := 0)

/-- **Tangent fields on spheres, sphere-domain form.** The unit sphere `Sⁿ` of a real inner product
space `E` of dimension `n + 1` carries a continuous map `v : Sⁿ → E` with `⟪v x, x⟫ = 0` and
`v x ≠ 0` everywhere if and only if `n` is odd. -/
theorem exists_continuous_inner_eq_zero_and_ne_zero_iff_odd :
    (∃ v : sphere (0 : E) 1 → E, Continuous v ∧
      ∀ x : sphere (0 : E) 1, ⟪v x, (x : E)⟫_ℝ = 0 ∧ v x ≠ 0) ↔ Odd n := by
  rw [← exists_continuous_section_ne_zero_iff_odd (E := E) (n := n)]
  refine ⟨fun ⟨v, hv, h⟩ ↦ ⟨sphereTangentSection n v fun x ↦ (h x).1,
      (continuous_sphereTangentSection_iff v _).2 hv,
      fun x ↦ (sphereTangentSection_eq_zero_iff v _ x).not.2 (h x).2⟩,
    fun ⟨V, hV, hne⟩ ↦ ⟨fun x ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (V x),
      continuous_section_sphere_iff.1 hV, fun x ↦ ⟨inner_mvfderiv_subtypeVal_sphere_coe x (V x),
        fun h0 ↦ hne x (injective_mvfderiv_subtypeVal_sphere x (h0.trans (map_zero _).symm))⟩⟩⟩

/-- **Tangent fields on spheres.** The unit sphere `Sⁿ` of a real inner product space of dimension
`n + 1` carries a nowhere-vanishing continuous tangent vector field exactly when `n` is odd. For odd
`n` one such field is `x ↦ J x` for an orthogonal almost complex structure `J`, which reads
`(x₁, x₂, x₃, x₄, …) ↦ (-x₂, x₁, -x₄, x₃, …)` in a suitable orthonormal basis. -/
theorem exists_continuousOn_inner_eq_zero_and_ne_zero_iff_odd :
    (∃ v : E → E, ContinuousOn v (sphere (0 : E) 1) ∧
      ∀ x ∈ sphere (0 : E) 1, ⟪v x, x⟫_ℝ = 0 ∧ v x ≠ 0) ↔ Odd n := by
  refine ⟨fun ⟨v, hv, h⟩ ↦ Nat.not_even_iff_odd.1 fun hn ↦ ?_, fun hn ↦ ?_⟩
  · obtain ⟨x, hx, h0⟩ := exists_eq_zero_of_inner_eq_zero hn hv fun x hx ↦ (h x hx).1
    exact (h x hx).2 h0
  · have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
    obtain ⟨J, hJ⟩ := AlmostComplexStructure.exists_forall_norm_apply_eq (V := E)
      (by rw [Fact.out (p := finrank ℝ E = n + 1)]; exact hn.add_one)
    let L : E →ₗᵢ[ℝ] E := ⟨J.toLinearMap, hJ⟩
    exact ⟨J, L.continuous.continuousOn, fun x hx ↦ ⟨J.inner_apply_self L.inner_map_map x,
      J.map_ne_zero_iff.2 (ne_zero_of_mem_unit_sphere ⟨x, hx⟩)⟩⟩

end TauCeti
