/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Topology.Homotopy.Basic
import TauCeti.Analysis.InnerProductSpace.Sphere.Trigonometric
import TauCeti.Geometry.Manifold.Degree.Global
import TauCeti.Geometry.Manifold.Orientation.Sphere
import TauCeti.Geometry.Manifold.SmoothApprox
import TauCeti.Geometry.Manifold.VectorField.Sphere
import TauCeti.Geometry.Sphere.Connected

/-!
# The hairy ball theorem

Every continuous tangent vector field on an even-dimensional unit sphere vanishes at some point
(`TauCeti.exists_eq_zero_of_inner_eq_zero`), and so does every continuous section of its tangent
bundle (`TauCeti.exists_eq_zero_of_continuous_section`). More generally, a unit sphere `Sⁿ`
carries a nowhere-vanishing continuous (or `C^m`, for any `m : ℕ∞ω`) tangent vector field if and
only if `n` is odd (`TauCeti.exists_continuousOn_inner_eq_zero_ne_zero_iff_odd`,
`TauCeti.exists_contMDiff_section_ne_zero_sphere_iff_odd`), and the identity map of `Sⁿ` is
homotopic to the antipodal map if and only if `n` is odd
(`TauCeti.homotopic_id_neg_sphere_iff_odd`).

The proof is the mapping-degree argument of Milnor and Lee:
1. A nowhere-vanishing continuous tangent vector field on `Sⁿ` can be smoothed and normalized to a
   `C^∞` unit tangent vector field `w : Sⁿ → E`
   (`TauCeti.exists_contMDiff_unit_tangent_sphere_of_ne_zero`).
2. Rotating each `x ∈ Sⁿ` towards `w x` along the great circle
   `F(x, t) = cos(π t) • x + sin(π t) • w x` defines a smooth homotopy from the identity to the
   antipodal map `x ↦ -x` (`TauCeti.exists_contMDiff_homotopy_id_neg_sphere`).
3. For `n ≥ 1`, homotopy invariance of the mapping degree (`TauCeti.degree_eq_of_homotopy`) equates
   `deg(id) = 1` with `deg(-id) = (-1)^(n+1)` (`TauCeti.Manifold.Orientation.degree_neg_sphere`),
   forcing `n` to be odd (`TauCeti.odd_of_contMDiff_homotopy_id_neg_sphere`). On `S⁰`, the
   intermediate value theorem produces a unit vector orthogonal to `x` in the `1`-dimensional
   ambient space `E`, which is impossible.
4. Conversely, when `n` is odd, `dim E = n + 1` is even and an orthogonal almost complex structure
   on `E` restricts to a real-analytic (`C^ω`) unit tangent vector field on `Sⁿ`
   (`TauCeti.exists_contDiff_unit_tangent_of_odd`,
   `TauCeti.exists_contMDiff_unit_section_sphere_of_odd`), whose great-circle homotopy deforms the
   identity to the antipodal map.

As an immediate topological consequence, every continuous self-map `f : Sⁿ → Sⁿ` of an
even-dimensional sphere satisfies `f x = x` or `f x = -x` at some point `x`: its tangential
projection `x ↦ f x - ⟪x, f x⟫ x` must vanish somewhere
(`TauCeti.exists_eq_or_eq_neg_sphere_of_even`, `TauCeti.exists_eq_neg_sphere_of_even`,
`TauCeti.exists_fixedPoint_sphere_of_even`).

## Main results

* `TauCeti.exists_contMDiff_homotopy_id_neg_sphere`: a `C^∞` unit tangent vector field on `Sⁿ`
  gives a `C^∞` great-circle homotopy from `id` to the antipodal map.
* `TauCeti.odd_of_contMDiff_homotopy_id_neg_sphere`, `TauCeti.odd_of_contMDiff_unit_tangent_sphere`:
  the existence of a smooth homotopy from `id` to `-id` on `Sⁿ`, or of a smooth unit tangent vector
  field, forces `Odd n`.
* `TauCeti.exists_eq_zero_of_inner_eq_zero`, `TauCeti.exists_eq_zero_of_continuous_inner_eq_zero`:
  the hairy ball theorem for continuous ambient tangent vector fields on even-dimensional spheres.
* `TauCeti.exists_eq_zero_of_continuous_section`: the hairy ball theorem for continuous sections of
  `TangentBundle (𝓡 n) (sphere (0 : E) 1)`.
* `TauCeti.exists_continuousOn_inner_eq_zero_ne_zero_iff_odd`,
  `TauCeti.exists_continuous_inner_eq_zero_ne_zero_sphere_iff_odd`,
  `TauCeti.exists_contMDiff_section_ne_zero_sphere_iff_odd`,
  `TauCeti.exists_continuous_section_ne_zero_sphere_iff_odd`: a unit sphere `Sⁿ` admits a
  nowhere-vanishing continuous or `C^m` tangent vector field if and only if `n` is odd.
* `TauCeti.homotopic_id_neg_sphere_iff_odd`: the identity of `Sⁿ` is homotopic to the antipodal map
  if and only if `n` is odd.
* `TauCeti.exists_eq_or_eq_neg_sphere_of_even`, `TauCeti.exists_eq_neg_sphere_of_even`,
  `TauCeti.exists_fixedPoint_sphere_of_even`: every continuous self-map of an even-dimensional
  sphere fixes a point or sends a point to its antipode.

## References

* L. E. J. Brouwer, *Über Abbildung von Mannigfaltigkeiten*, Mathematische Annalen **71** (1912),
  97–115.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5; J. Milnor, *Analytic proofs of the "hairy ball theorem" and the Brouwer fixed point theorem*,
  Amer. Math. Monthly **85** (1978), 521–524.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Problem 16-6 and Chapter 17 (Degree Theory).
-/

public section

noncomputable section

open Bundle Metric Module Set
open scoped ContDiff InnerProductSpace Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-! ### Great-circle homotopy and degree obstruction -/

variable (n) in
/-- An orthogonal pair of unit vectors in `E` forces `finrank ℝ E ≥ 2`, ruling out the
zero-dimensional sphere `S⁰`. -/
private theorem one_le_of_orthogonal_unit (x : sphere (0 : E) 1) {u : E} (hu : ‖u‖ = 1)
    (hux : ⟪u, (x : E)⟫_ℝ = 0) : 1 ≤ n := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have horth : Orthonormal ℝ ![(x : E), u] := by
    refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
    · fin_cases i
      · exact norm_eq_of_mem_sphere x
      · exact hu
    · fin_cases i <;> fin_cases j <;> simp_all [real_inner_comm]
  have hle := horth.linearIndependent.fintype_card_le_finrank
  rw [Fintype.card_fin, Fact.out (p := finrank ℝ E = n + 1)] at hle
  omega

/-- **Great-circle homotopy to the antipodal map.** A `C^∞` unit tangent vector field
`w : sphere (0 : E) 1 → E` rotates each point `x` along the great circle towards `w x`, giving a
smooth homotopy `F : sphere (0 : E) 1 × Icc (0 : ℝ) 1 → sphere (0 : E) 1` from the identity to
the antipodal map: `F (x, t) = cos(π t) • x + sin(π t) • w x`. -/
theorem exists_contMDiff_homotopy_id_neg_sphere {w : sphere (0 : E) 1 → E}
    (hw : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ w) (ht : ∀ x, ⟪w x, (x : E)⟫_ℝ = 0)
    (hnorm : ∀ x, ‖w x‖ = 1) :
    ∃ F : sphere (0 : E) 1 × Icc (0 : ℝ) 1 → sphere (0 : E) 1,
      ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡 n) ∞ F ∧
        (∀ x, F (x, 0) = x) ∧ ∀ x, F (x, 1) = -x := by
  let g : sphere (0 : E) 1 × Icc (0 : ℝ) 1 → E := fun p ↦
    Real.cos (Real.pi * (p.2 : ℝ)) • (p.1 : E) + Real.sin (Real.pi * (p.2 : ℝ)) • w p.1
  have hg_mem (p : sphere (0 : E) 1 × Icc (0 : ℝ) 1) : g p ∈ sphere (0 : E) 1 := by
    let q : sphere (0 : E) 1 := ⟨w p.1, mem_sphere_zero_iff_norm.2 (hnorm p.1)⟩
    have hpq : ⟪(p.1 : E), (q : E)⟫_ℝ = 0 := by
      rw [real_inner_comm]
      exact ht p.1
    exact mem_sphere_zero_iff_norm.2 (norm_cos_smul_add_sin_smul p.1 q hpq (Real.pi * (p.2 : ℝ)))
  have hθ : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : sphere (0 : E) 1 × Icc (0 : ℝ) 1 ↦ (p.2 : ℝ)) :=
    (contMDiff_subtypeVal_Icc (x := 0) (y := 1) (n := ∞)).comp contMDiff_snd
  have hcos : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : sphere (0 : E) 1 × Icc (0 : ℝ) 1 ↦ Real.cos (Real.pi * (p.2 : ℝ))) :=
    (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).contMDiff.comp hθ
  have hsin : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : sphere (0 : E) 1 × Icc (0 : ℝ) 1 ↦ Real.sin (Real.pi * (p.2 : ℝ))) :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contMDiff.comp hθ
  have hg : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) 𝓘(ℝ, E) ∞ g :=
    (hcos.smul (contMDiff_coe_sphere.comp contMDiff_fst)).add
      (hsin.smul (hw.comp contMDiff_fst))
  refine ⟨codRestrict g (sphere (0 : E) 1) hg_mem, hg.codRestrict_sphere hg_mem,
    fun x ↦ Subtype.ext ?_, fun x ↦ Subtype.ext ?_⟩
  · simp [g]
  · simp [g]

/-- If the identity map of the unit sphere `Sⁿ` is smoothly homotopic to the antipodal map, then
`n` is odd: for `n ≥ 1` the identity has degree `1` whereas the antipodal map has degree
`(-1)^(n+1)`, while on `S⁰` any path from `x` to `-x` crosses `x^⊥`. -/
theorem odd_of_contMDiff_homotopy_id_neg_sphere
    {F : sphere (0 : E) 1 × Icc (0 : ℝ) 1 → sphere (0 : E) 1}
    (hF : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡 n) ∞ F)
    (h₀ : ∀ x, F (x, 0) = x) (h₁ : ∀ x, F (x, 1) = -x) :
    Odd n := by
  have hE : finrank ℝ E = n + 1 := Fact.out
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  rcases eq_or_ne n 0 with rfl | hn0
  · -- On `S⁰`, the inner product `t ↦ ⟪F(x, t), x⟫` goes from `1` to `-1`, so it hits `0`.
    obtain ⟨x⟩ : Nonempty (sphere (0 : E) 1) :=
      (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
    let φ : ℝ → ℝ := fun t ↦ ⟪(F (x, projIcc 0 1 zero_le_one t) : E), (x : E)⟫_ℝ
    have hφ : Continuous φ := by
      have hFc : Continuous (fun t : ℝ ↦ (F (x, projIcc 0 1 zero_le_one t) : E)) :=
        continuous_subtype_val.comp
          (hF.continuous.comp (continuous_const.prodMk continuous_projIcc))
      exact hFc.inner continuous_const
    have hφ₀ : φ 0 = 1 := by
      simp [φ, projIcc_left, h₀, norm_eq_of_mem_sphere]
    have hφ₁ : φ 1 = -1 := by
      simp [φ, projIcc_right, h₁, norm_eq_of_mem_sphere]
    have h0_mem : (0 : ℝ) ∈ Icc (φ 1) (φ 0) := by
      rw [hφ₀, hφ₁]
      constructor <;> norm_num
    obtain ⟨t, -, ht⟩ := intermediate_value_Icc' zero_le_one hφ.continuousOn h0_mem
    have h1 := one_le_of_orthogonal_unit 0 x
      (norm_eq_of_mem_sphere (F (x, projIcc 0 1 zero_le_one t))) ht
    omega
  · -- On connected spheres `Sⁿ` (`n ≥ 1`), homotopy invariance equates `1` with `(-1)^(n+1)`.
    have : NeZero n := ⟨hn0⟩
    have := connectedSpace_sphere (E := E) n
    let o := (finBasisOfFinrankEq ℝ E hE).orientation.sphereOrientation
    have hdeg := degree_eq_of_homotopy o o contMDiff_id contMDiff_neg_sphere hF h₀ h₁
    rw [degree_id, Manifold.Orientation.degree_neg_sphere] at hdeg
    refine Nat.not_even_iff_odd.1 fun hn ↦ ?_
    rw [hn.add_one.neg_one_pow] at hdeg
    norm_num at hdeg

/-- If the unit sphere `Sⁿ` admits a `C^∞` unit tangent vector field, then `n` is odd. -/
theorem odd_of_contMDiff_unit_tangent_sphere {w : sphere (0 : E) 1 → E}
    (hw : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ w) (ht : ∀ x, ⟪w x, (x : E)⟫_ℝ = 0)
    (hnorm : ∀ x, ‖w x‖ = 1) :
    Odd n := by
  obtain ⟨F, hF, h₀, h₁⟩ := exists_contMDiff_homotopy_id_neg_sphere hw ht hnorm
  exact odd_of_contMDiff_homotopy_id_neg_sphere hF h₀ h₁

/-! ### The hairy ball theorem -/

/-- **The hairy ball theorem** (subtype form): every continuous tangent vector field
`v : sphere (0 : E) 1 → E` on an even-dimensional unit sphere vanishes at some point. -/
theorem exists_eq_zero_of_continuous_inner_eq_zero (hn : Even n) {v : sphere (0 : E) 1 → E}
    (hv : Continuous v) (ht : ∀ x, ⟪v x, (x : E)⟫_ℝ = 0) :
    ∃ x, v x = 0 := by
  by_contra! hne
  obtain ⟨w, hw, hwt, hwn⟩ := exists_contMDiff_unit_tangent_sphere_of_ne_zero (n := n) hv ht hne
  exact Nat.not_odd_iff_even.2 hn (odd_of_contMDiff_unit_tangent_sphere hw hwt hwn)

/-- **The hairy ball theorem** [Lee, Problem 16-6; Milnor, §5]: on an even-dimensional unit sphere
`Sⁿ ⊆ E` (`dim E = n + 1`, `n` even), every continuous ambient vector field `v : E → E` that is
tangent to `Sⁿ` (`⟪v x, x⟫_ℝ = 0` for all `x ∈ Sⁿ`) vanishes at some point of `Sⁿ`. -/
theorem exists_eq_zero_of_inner_eq_zero (hn : Even n) {v : E → E}
    (hv : ContinuousOn v (Metric.sphere (0 : E) 1))
    (ht : ∀ x ∈ Metric.sphere (0 : E) 1, ⟪v x, x⟫_ℝ = 0) :
    ∃ x ∈ Metric.sphere (0 : E) 1, v x = 0 := by
  obtain ⟨x, hx⟩ := exists_eq_zero_of_continuous_inner_eq_zero hn
    (continuousOn_iff_continuous_domRestrict.1 hv) fun x ↦ ht (x : E) x.2
  exact ⟨(x : E), x.2, hx⟩

/-- **The hairy ball theorem for tangent-bundle sections**: every continuous section `V` of the
tangent bundle of an even-dimensional unit sphere `Sⁿ` vanishes at some point. -/
theorem exists_eq_zero_of_continuous_section (hn : Even n)
    {V : (x : Metric.sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
    (hV : Continuous
      (fun x ↦ (⟨x, V x⟩ : TangentBundle (𝓡 n) (Metric.sphere (0 : E) 1)))) :
    ∃ x, V x = 0 := by
  have hv : Continuous (fun x ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (V x)) :=
    continuous_section_sphere_iff.1 hV
  have ht (x : sphere (0 : E) 1) :
      ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (V x), (x : E)⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact inner_coe_mvfderiv_subtypeVal_sphere x (V x)
  obtain ⟨x, hx⟩ := exists_eq_zero_of_continuous_inner_eq_zero hn hv ht
  exact ⟨x, injective_mvfderiv_subtypeVal_sphere x (hx.trans (map_zero _).symm)⟩

/-! ### Parity dichotomies for vector fields and antipodal homotopy -/

/-- A unit sphere `Sⁿ ⊆ E` admits a continuous nowhere-vanishing ambient tangent vector field if
and only if `n` is odd. -/
theorem exists_continuousOn_inner_eq_zero_ne_zero_iff_odd :
    (∃ v : E → E, ContinuousOn v (sphere (0 : E) 1) ∧
      (∀ x ∈ sphere (0 : E) 1, ⟪v x, x⟫_ℝ = 0) ∧ ∀ x ∈ sphere (0 : E) 1, v x ≠ 0) ↔ Odd n := by
  constructor
  · rintro ⟨v, hv, ht, hne⟩
    refine Nat.not_even_iff_odd.1 fun hn ↦ ?_
    obtain ⟨x, hx, hvx⟩ := exists_eq_zero_of_inner_eq_zero hn hv ht
    exact hne x hx hvx
  · intro hn
    obtain ⟨v, hv, ht, hnorm⟩ := exists_contDiff_unit_tangent_of_odd (E := E) hn
    refine ⟨v, hv.continuous.continuousOn, fun x _ ↦ ht x, fun x hx ↦ ?_⟩
    rw [← norm_ne_zero_iff, hnorm x hx]
    exact one_ne_zero

/-- A unit sphere `Sⁿ` admits a continuous nowhere-vanishing tangent map `v : sphere (0 : E) 1 → E`
if and only if `n` is odd. -/
theorem exists_continuous_inner_eq_zero_ne_zero_sphere_iff_odd :
    (∃ v : sphere (0 : E) 1 → E, Continuous v ∧
      (∀ x, ⟪v x, (x : E)⟫_ℝ = 0) ∧ ∀ x, v x ≠ 0) ↔ Odd n := by
  constructor
  · rintro ⟨v, hv, ht, hne⟩
    refine Nat.not_even_iff_odd.1 fun hn ↦ ?_
    obtain ⟨x, hvx⟩ := exists_eq_zero_of_continuous_inner_eq_zero hn hv ht
    exact hne x hvx
  · intro hn
    obtain ⟨v, hv, ht, hnorm⟩ := exists_contDiff_unit_tangent_of_odd (E := E) hn
    refine ⟨fun x ↦ v (x : E), hv.continuous.comp continuous_subtype_val, fun x ↦ ht (x : E),
      fun x ↦ ?_⟩
    rw [← norm_ne_zero_iff, hnorm (x : E) x.2]
    exact one_ne_zero

/-- For every regularity `m : ℕ∞ω` (from `C⁰` through `C^∞` and `C^ω`), the unit sphere `Sⁿ` admits
a nowhere-vanishing `C^m` section of its tangent bundle if and only if `n` is odd. -/
theorem exists_contMDiff_section_ne_zero_sphere_iff_odd {m : ℕ∞ω} :
    (∃ V : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x,
      ContMDiff (𝓡 n) (𝓡 n).tangent m
        (fun x ↦ (⟨x, V x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) ∧
      ∀ x, V x ≠ 0) ↔ Odd n := by
  constructor
  · rintro ⟨V, hV, hne⟩
    refine Nat.not_even_iff_odd.1 fun hn ↦ ?_
    obtain ⟨x, hvx⟩ := exists_eq_zero_of_continuous_section hn hV.continuous
    exact hne x hvx
  · intro hn
    obtain ⟨V, hV, hnorm⟩ := exists_contMDiff_unit_section_sphere_of_odd (E := E) hn
    refine ⟨V, hV.of_le le_top, fun x ↦ ?_⟩
    rw [← norm_ne_zero_iff, hnorm x]
    exact one_ne_zero

/-- The unit sphere `Sⁿ` admits a nowhere-vanishing continuous section of its tangent bundle if and
only if `n` is odd. -/
theorem exists_continuous_section_ne_zero_sphere_iff_odd :
    (∃ V : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x,
      Continuous (fun x ↦ (⟨x, V x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) ∧
      ∀ x, V x ≠ 0) ↔ Odd n := by
  simp only [← contMDiff_zero_iff (I := 𝓡 n) (I' := (𝓡 n).tangent)]
  exact exists_contMDiff_section_ne_zero_sphere_iff_odd

/-- **Antipodal homotopy dichotomy.** The identity map of the unit sphere `Sⁿ` is homotopic to the
antipodal map `x ↦ -x` if and only if `n` is odd. -/
theorem homotopic_id_neg_sphere_iff_odd :
    (ContinuousMap.id (sphere (0 : E) 1)).Homotopic
      ⟨fun x ↦ -x, continuous_neg⟩ ↔ Odd n := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  constructor
  · intro h
    obtain ⟨K, hK, hK₀, hK₁⟩ :=
      h.exists_contMDiff_homotopy (I := 𝓡 n) (J := 𝓡 n) ⊤ contMDiff_id
        (contMDiff_neg_sphere (n := n) (m := ∞))
    have hF : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡 n) ∞
        (fun p : sphere (0 : E) 1 × Icc (0 : ℝ) 1 ↦ K (p.1, (p.2 : ℝ))) :=
      hK.comp (contMDiff_id.prodMap (contMDiff_subtypeVal_Icc (x := 0) (y := 1) (n := ∞)))
    exact odd_of_contMDiff_homotopy_id_neg_sphere hF hK₀ hK₁
  · intro hn
    obtain ⟨v, hv, hvt, hvn⟩ := exists_contDiff_unit_tangent_of_odd (E := E) hn
    have hw : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (fun x : sphere (0 : E) 1 ↦ v (x : E)) :=
      (hv.contMDiff.of_le le_top).comp contMDiff_coe_sphere
    obtain ⟨F, hF, hF₀, hF₁⟩ :=
      exists_contMDiff_homotopy_id_neg_sphere hw (fun x ↦ hvt (x : E)) (fun x ↦ hvn (x : E) x.2)
    exact ⟨{
      toFun := fun p ↦ F (p.2, p.1)
      continuous_toFun := hF.continuous.comp continuous_swap
      map_zero_left := hF₀
      map_one_left := hF₁ }⟩

/-! ### Fixed-point and antipodal-point consequences on even spheres -/

/-- Every continuous self-map of an even-dimensional unit sphere either fixes a point or sends some
point to its antipode. Applying the hairy ball theorem to the tangential component
`x ↦ f x - ⟪x, f x⟫ x` produces a point `x` where `f x` is collinear with `x`; since both lie on
the unit sphere, `f x = x` or `f x = -x`. -/
theorem exists_eq_or_eq_neg_sphere_of_even (hn : Even n)
    {f : sphere (0 : E) 1 → sphere (0 : E) 1} (hf : Continuous f) :
    ∃ x, f x = x ∨ f x = -x := by
  obtain ⟨x, hx⟩ := exists_eq_zero_of_continuous_section hn
    (continuous_sphereTangentSection (n := n) (continuous_subtype_val.comp hf))
  have hcol : (f x : E) = ⟪(x : E), (f x : E)⟫_ℝ • (x : E) := by
    have h0 := congrArg (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x) hx
    rw [mvfderiv_coe_sphereTangentSection, map_zero] at h0
    exact sub_eq_zero.1 h0
  have habs : |⟪(x : E), (f x : E)⟫_ℝ| = 1 := by
    have hnorm := congrArg norm hcol
    simpa [norm_smul, norm_eq_of_mem_sphere] using hnorm.symm
  rcases abs_eq (zero_le_one' ℝ) |>.1 habs with hc | hc
  · exact ⟨x, Or.inl (Subtype.ext (by rw [hcol, hc, one_smul]))⟩
  · exact ⟨x, Or.inr (Subtype.ext (by rw [hcol, hc, neg_one_smul]; rfl))⟩

/-- Every fixed-point-free continuous self-map of an even-dimensional unit sphere sends some point
to its antipode. -/
theorem exists_eq_neg_sphere_of_even (hn : Even n)
    {f : sphere (0 : E) 1 → sphere (0 : E) 1} (hf : Continuous f) (hfix : ∀ x, f x ≠ x) :
    ∃ x, f x = -x := by
  obtain ⟨x, hx | hx⟩ := exists_eq_or_eq_neg_sphere_of_even hn hf
  · exact absurd hx (hfix x)
  · exact ⟨x, hx⟩

/-- Every continuous self-map of an even-dimensional unit sphere that sends no point to its
antipode has a fixed point. -/
theorem exists_fixedPoint_sphere_of_even (hn : Even n)
    {f : sphere (0 : E) 1 → sphere (0 : E) 1} (hf : Continuous f) (hant : ∀ x, f x ≠ -x) :
    ∃ x, f x = x := by
  obtain ⟨x, hx | hx⟩ := exists_eq_or_eq_neg_sphere_of_even hn hf
  · exact ⟨x, hx⟩
  · exact absurd hx (hant x)

end TauCeti
