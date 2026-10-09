/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyFinite
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Affine
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.VertexSector

/-!
# Stabilizers of ideal vertices in locally finite tessellations

Let `P` be a convex hyperbolic polygon with an ideal vertex `ξ`, and let `Γ ≤ PSL(2, ℝ)` be a
subgroup whose translates of `P` form a locally finite family. Then every nonidentity element of
`Γ` fixing `ξ` is parabolic.

Such an element fixes a point of the ideal boundary, so it is not elliptic. If it were
hyperbolic, then after moving `ξ` to `∞` it would act as `z ↦ μ * z + c` with `μ ≠ 1`, and either
it or its inverse would contract towards its second fixed point `x₀ ∈ ℝ`. Near `∞`, `P` is a
vertical strip, and the contracting powers carry it into thinner and thinner strips approaching the
vertical geodesic over `x₀`. So infinitely many distinct translates of `P` meet every neighbourhood
of `x₀ + i`, contradicting local finiteness.

Applied to the cycle transformations of a side-paired polygon, this gives the parabolic cycle
condition of Poincaré's polygon theorem at every ideal vertex of a locally finite fundamental
polygon (`ConvexPolygon.SidePairing.isParabolic_cycleMap_of_locallyFinite`).

## Main result

* `ConvexPolygon.isParabolic_of_smul_eq_self_of_locallyFinite`: in a locally finite tessellation,
  a nonidentity element fixing an ideal vertex is parabolic.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, Chapter 9 (locally finite fundamental domains and their cycles).
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, Chapter 4 (fundamental regions and their vertices at infinity).
-/

public section

open Filter Matrix.ProjectiveSpecialLinearGroup Set Topology UpperHalfPlane
open scoped MatrixGroups OnePoint Pointwise

namespace TauCeti.UpperHalfPlane.ConvexPolygon

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n}

/-- A contracting affine map at an ideal vertex destroys local finiteness: if `g` moves the ideal
vertex `ξ` of `P` to `∞` and `g S g⁻¹` acts as `z ↦ μ * z + c` with `0 < μ < 1`, then the
translates of `P` by the powers of `S` accumulate at `g⁻¹ • (x₀ + i)`, where `x₀` is the fixed point
of `z ↦ μ * z + c` on `ℝ`. -/
private theorem not_locallyFinite_of_coe_conj_smul_eq {j : Fin n} {ξ : OnePoint ℝ}
    (hj : P.vertex j = .inr ξ) {g : PSL(2, ℝ)} (hg : g • ξ = ∞) {Γ : Subgroup PSL(2, ℝ)}
    {S : PSL(2, ℝ)} (hS : S ∈ Γ) {μ c : ℝ} (hμ₀ : 0 < μ) (hμ₁ : μ < 1)
    (hSz : ∀ z : ℍ, (((g * S * g⁻¹) • z : ℍ) : ℂ) = μ * z + c) :
    ¬ LocallyFinite fun δ : Γ ↦ (δ : PSL(2, ℝ)) • P.carrier := by
  intro hlf
  -- the powers of `g S g⁻¹` contract towards the fixed point `x₀ = c / (1 - μ)`
  set x₀ : ℝ := c / (1 - μ)
  have hx₀ : (μ : ℂ) * x₀ + c = x₀ := by
    have : μ * x₀ + c = x₀ := by
      simp only [x₀]
      field_simp [(sub_pos.2 hμ₁).ne']
      ring
    exact_mod_cast this
  have hpow (k : ℕ) (z : ℍ) :
      (((g * S ^ k * g⁻¹) • z : ℍ) : ℂ) = x₀ + ((μ ^ k : ℝ) : ℂ) * (z - x₀) := by
    induction k generalizing z with
    | zero => simp
    | succ k ih =>
      rw [show g * S ^ (k + 1) * g⁻¹ = g * S * g⁻¹ * (g * S ^ k * g⁻¹) by group, mul_smul, hSz,
        ih]
      push_cast
      linear_combination hx₀
  -- above some height, `g • P` is the vertical strip of its vertex at `∞`
  have hQ : (g • P).vertex j = .inr ∞ := by rw [vertex_smul, hj, Sum.smul_inr, hg]
  obtain ⟨A, hA⟩ := (atImInfty_mem _).1
    ((g • P).eventuallyEq_carrier_vertexSector_atImInfty hQ).mem_iff
  set u := (toComplex ((g • P).vertex (j + 1))).re
  have huv := (g • P).re_toComplex_vertex_add_one_lt_of_vertex_eq_inr_infty hQ
  -- the point on the left edge of the strip at height `t k = μ⁻ᵏ` is moved to height `1`
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℝ, t = fun k ↦ μ⁻¹ ^ k := ⟨_, rfl⟩
  have hμt (k : ℕ) : (μ : ℂ) ^ k * t k = 1 := by
    have : μ ^ k * t k = 1 := by rw [ht, ← mul_pow, mul_inv_cancel₀ hμ₀.ne', one_pow]
    exact_mod_cast this
  have ht₀ (k : ℕ) : 0 < t k := by
    rw [ht]
    positivity
  let w (k : ℕ) : ℍ := ⟨u + t k * Complex.I, by simpa using ht₀ k⟩
  have hw {k : ℕ} (hk : A ≤ t k) : w k ∈ (g • P).carrier :=
    (hA (w k) (by simpa [w] using hk)).2
      (((g • P).mem_vertexSector_iff_of_vertex_eq_inr_infty hQ _).2
        ⟨by simp [w, u], by simpa [w, u] using huv.le⟩)
  set z₀ : ℍ := ⟨x₀ + Complex.I, by simp⟩
  have hlim : Tendsto (fun k ↦ (g * S ^ k * g⁻¹) • w k) atTop (𝓝 z₀) := by
    rw [UpperHalfPlane.isEmbedding_coe.tendsto_nhds_iff]
    have hμk : Tendsto (fun k : ℕ ↦ (x₀ : ℂ) + ((μ ^ k : ℝ) : ℂ) * (u - x₀) + Complex.I)
        atTop (𝓝 ((x₀ : ℂ) + ((0 : ℝ) : ℂ) * (u - x₀) + Complex.I)) :=
      (((Complex.continuous_ofReal.tendsto 0).comp
        (tendsto_pow_atTop_nhds_zero_of_lt_one hμ₀.le hμ₁)).mul_const _ |>.const_add _).add_const _
    convert hμk using 2 with k
    · rw [Function.comp_apply, hpow]
      push_cast
      linear_combination Complex.I * hμt k
    · simp [z₀]
  -- the powers `S ^ k` are pairwise distinct, as `g S^k g⁻¹` moves `i` to height `μ ^ k`
  have him (k : ℕ) : ((g * S ^ k * g⁻¹) • UpperHalfPlane.I).im = μ ^ k := by
    rw [← UpperHalfPlane.coe_im, hpow]
    simp [-Complex.ofReal_pow]
  -- local finiteness at `g⁻¹ • z₀` allows only finitely many of the distinct powers `S ^ k`
  obtain ⟨U, hU, hfin⟩ := hlf (g⁻¹ • z₀)
  obtain ⟨N, hN⟩ := ((hlim.const_smul g⁻¹).eventually_mem hU |>.and
    (show ∀ᶠ k in atTop, A ≤ t k by
      rw [ht]
      exact (tendsto_pow_atTop_atTop_of_one_lt ((one_lt_inv₀ hμ₀).2 hμ₁)).eventually_ge_atTop A))
    |>.exists_forall_of_atTop
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ ↦ (⟨S ^ (k + N), pow_mem hS _⟩ : Γ))
    (fun k l hkl ↦ ?_) (fun k ↦ ?_) hfin
  · have h := congrArg (fun δ : Γ ↦ ((g * (δ : PSL(2, ℝ)) * g⁻¹) • UpperHalfPlane.I).im) hkl
    simp only [him] at h
    exact Nat.add_right_cancel (pow_right_injective₀ hμ₀ hμ₁.ne h)
  · refine ⟨g⁻¹ • (g * S ^ (k + N) * g⁻¹) • w (k + N), ?_, (hN _ (Nat.le_add_left _ _)).1⟩
    rw [smul_smul, show g⁻¹ * (g * S ^ (k + N) * g⁻¹) = S ^ (k + N) * g⁻¹ by group, mul_smul]
    refine smul_mem_smul_set (mem_smul_set_iff_inv_smul_mem.1 ?_)
    rw [← carrier_smul]
    exact hw (hN _ (Nat.le_add_left _ _)).2

/-- **Nonidentity stabilizers of an ideal vertex are parabolic in a locally finite tessellation.**
Let `ξ` be an ideal vertex of the convex polygon `P`, and let the translates of `P` by a subgroup
`Γ` of `PSL(2, ℝ)` form a locally finite family. Then every nonidentity element of `Γ` fixing `ξ`
is parabolic. -/
theorem isParabolic_of_smul_eq_self_of_locallyFinite {j : Fin n} {ξ : OnePoint ℝ}
    (hj : P.vertex j = .inr ξ) {Γ : Subgroup PSL(2, ℝ)}
    (hlf : LocallyFinite fun δ : Γ ↦ (δ : PSL(2, ℝ)) • P.carrier) {γ : PSL(2, ℝ)} (hγ : γ ∈ Γ)
    (hfix : γ • ξ = ξ) (hne : γ ≠ 1) : IsParabolic γ := by
  -- move `ξ` to `∞`, where `γ` becomes an affine map `z ↦ μ * z + c`
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, ℝ) ξ (∞ : OnePoint ℝ)
  have hfix' : (g * γ * g⁻¹) • (∞ : OnePoint ℝ) = ∞ := by
    rw [mul_smul, mul_smul, ← hg, inv_smul_smul, hfix]
  obtain ⟨μ, hμ, c, hγz⟩ := exists_coe_smul_eq_mul_add_of_smul_infty hfix'
  rcases lt_trichotomy μ 1 with hlt | rfl | hgt
  · exact absurd hlf (not_locallyFinite_of_coe_conj_smul_eq hj hg hγ hμ hlt hγz)
  · -- `μ = 1`: the conjugate is the translation by `c`, which is nonzero as `γ ≠ 1`
    have heq : g * γ * g⁻¹ = upperRightHom c :=
      FaithfulSMul.eq_of_smul_eq_smul fun z ↦ UpperHalfPlane.coe_injective (by
        rw [hγz, upperRightHom_smul, coe_vadd]
        push_cast
        ring)
    have hc : c ≠ 0 := by
      rintro rfl
      rw [AddChar.map_zero_eq_one, mul_inv_eq_one, mul_eq_left] at heq
      exact hne heq
    rw [← isParabolic_conj_iff g, heq]
    exact isParabolic_upperRightHom_iff.2 hc
  · -- `μ > 1`: the inverse `z ↦ μ⁻¹ * (z - c)` contracts
    refine absurd hlf (not_locallyFinite_of_coe_conj_smul_eq hj hg (Γ.inv_mem hγ) (c := -c / μ)
      (inv_pos.2 hμ) (inv_lt_one_of_one_lt₀ hgt) fun z ↦ ?_)
    have h := hγz ((g * γ⁻¹ * g⁻¹) • z)
    rw [← mul_smul, show g * γ * g⁻¹ * (g * γ⁻¹ * g⁻¹) = 1 by group, one_smul] at h
    have hμC : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
    push_cast
    field_simp
    linear_combination -h

end TauCeti.UpperHalfPlane.ConvexPolygon
