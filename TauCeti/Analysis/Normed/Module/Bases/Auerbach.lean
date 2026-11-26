/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.Compact

/-!
# Auerbach's lemma for a compact family of linear forms

Let `U` be a finite-dimensional vector space over a field `K`, `𝒜` a compact topological space,
`(ℓ_a)_{a ∈ 𝒜}` a family of linear forms on `U` whose only common zero is `0`, and `φ : K →+* L`
a ring homomorphism into a normed field `L` such that `a ↦ φ (ℓ a v)` is continuous for every
`v : U`. Then there exist `a : Fin (finrank K U) → 𝒜` and a basis
`z : Module.Basis (Fin (finrank K U)) K U` such that `ℓ (a i) (z j) = δ_{ij}` and
`‖φ (ℓ x (z k))‖ ≤ 1` for all `x : 𝒜` and all `k`.

For `K = L = ℝ` or `ℂ` and the unit sphere of the dual of a normed space, this recovers the
classical Auerbach basis.

## Main statements

* `TauCeti.exists_auerbachBasis`: existence of an Auerbach basis for a compact separating family
  of linear forms measured through a ring homomorphism into a normed field.

## References

* L. Alpöge, Lean formalization of the Riemann hypothesis for Dirichlet `L`-functions,
  <https://github.com/leanprover-community/riemann-hypothesis>.
-/

public section

namespace TauCeti

private lemma exists_evalMatrix_det_ne_zero {K U 𝒜 : Type*} [Field K] [AddCommGroup U]
    [Module K U] [FiniteDimensional K U] (ℓ : 𝒜 → Module.Dual K U)
    (hsep : ∀ v : U, (∀ a : 𝒜, ℓ a v = 0) → v = 0) :
    let n := Module.finrank K U
    let b := Module.finBasis K U
    ∃ f : Fin n → 𝒜, (Matrix.of fun i j => ℓ (f i) (b j)).det ≠ 0 := by
  intro n b
  have hspan : Submodule.span K (Set.range ℓ) = ⊤ :=
    Submodule.span_eq_top_of_ne_zero fun v hv => by
      by_contra! h
      exact hv (hsep v fun a => h _ ⟨a, rfl⟩)
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent K (Set.range ℓ)
  let bs : Module.Basis s K (Module.Dual K U) :=
    Module.Basis.mk hs_li (by rw [Subtype.range_coe, hs_span, hspan])
  have : Finite s := Module.Finite.finite_basis bs
  let _ : Fintype s := Fintype.ofFinite s
  have hcard : Fintype.card s = n := by
    have hfr := Module.finrank_eq_card_basis bs
    rw [Subspace.dual_finrank_eq] at hfr
    exact hfr.symm
  let e : Fin n ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  have hmem : ∀ i : Fin n, (e i : Module.Dual K U) ∈ Set.range ℓ := fun i => hs_sub (e i).property
  choose f hf using hmem
  refine ⟨f, ?_⟩
  intro hdet
  have hdetT : (Matrix.transpose (Matrix.of fun i j => ℓ (f i) (b j))).det = 0 := by
    rw [Matrix.det_transpose]; exact hdet
  obtain ⟨g, hg_ne, hg0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
  have hli : LinearIndependent K (fun i : Fin n => ℓ (f i)) := by
    have h1 := hs_li.comp e e.injective
    simpa [Function.comp_def, hf] using h1
  have hg_zero : ∀ i : Fin n, g i = 0 := by
    refine (Fintype.linearIndependent_iff.mp hli) g (b.ext fun j => ?_)
    have hj := congrFun hg0 j
    simpa [Matrix.mulVec, dotProduct, LinearMap.sum_apply, LinearMap.smul_apply, mul_comm] using hj
  exact hg_ne (funext hg_zero)

private lemma norm_eval_le_one_of_isMaxOn {K U 𝒜 L : Type*} [Field K] [AddCommGroup U] [Module K U]
    [NormedField L] {n : ℕ} (φ : K →+* L) (ℓ : 𝒜 → Module.Dual K U)
    (b : Module.Basis (Fin n) K U) (a : Fin n → 𝒜)
    (ha_max : ∀ f : Fin n → 𝒜,
      ‖φ (Matrix.of fun i j => ℓ (f i) (b j)).det‖ ≤
      ‖φ (Matrix.of fun i j => ℓ (a i) (b j)).det‖)
    (ha_det : (Matrix.of fun i j => ℓ (a i) (b j)).det ≠ 0)
    (z : Module.Basis (Fin n) K U)
    (hz : ∀ k, z k = ∑ j : Fin n, (Matrix.of fun i r => ℓ (a i) (b r))⁻¹ j k • b j)
    (x : 𝒜) (k : Fin n) :
    ‖φ (ℓ x (z k))‖ ≤ 1 := by
  classical
  let M : (Fin n → 𝒜) → Matrix (Fin n) (Fin n) K := fun f => Matrix.of fun i j => ℓ (f i) (b j)
  let N : Matrix (Fin n) (Fin n) K := (M a)⁻¹
  have hMN : M a * N = 1 := Matrix.mul_nonsing_inv (M a) (isUnit_iff_ne_zero.mpr ha_det)
  let a' : Fin n → 𝒜 := Function.update a k x
  have hprod : M a' * N =
      Matrix.updateRow (1 : Matrix (Fin n) (Fin n) K) k (fun j => ℓ x (z j)) := by
    ext i j
    by_cases hik : i = k
    · subst hik
      simp [M, N, a', Matrix.mul_apply, Matrix.updateRow_apply, hz, map_sum, map_smul, mul_comm]
    · have h := congrFun (congrFun hMN i) j
      simpa [M, a', hik, Matrix.mul_apply, Matrix.updateRow_apply] using h
  have hdet_eq : ℓ x (z k) * (M a).det = (M a').det := by
    have h1 := congrArg Matrix.det hprod
    rw [Matrix.det_mul, ← Matrix.cramer_transpose_apply, Matrix.transpose_one,
      Matrix.cramer_one] at h1
    have h2 := congrArg (· * (M a).det) h1
    rw [mul_assoc, ← Matrix.det_mul, Matrix.nonsing_inv_mul (M a) (isUnit_iff_ne_zero.mpr ha_det),
      Matrix.det_one, mul_one] at h2
    exact h2.symm
  have hnorm_le : ‖φ (ℓ x (z k))‖ * ‖φ (M a).det‖ ≤ 1 * ‖φ (M a).det‖ := by
    rw [← norm_mul, ← map_mul, hdet_eq, one_mul]
    exact ha_max a'
  exact le_of_mul_le_mul_right hnorm_le (norm_pos_iff.mpr ((map_ne_zero φ).mpr ha_det))

/-- **Auerbach's lemma for a compact family of linear forms.**
Let `U` be a finite-dimensional vector space over a field `K`, `𝒜` a compact topological space,
`(ℓ_a)_{a ∈ 𝒜}` a family of linear forms on `U` whose only common zero is `0`, and `φ : K →+* L`
a ring homomorphism into a normed field `L` such that `a ↦ φ (ℓ a v)` is continuous for every
`v : U`. Then there exist `a : Fin (finrank K U) → 𝒜` and a basis
`z : Module.Basis (Fin (finrank K U)) K U` such that `ℓ (a i) (z j) = if i = j then 1 else 0`
and `‖φ (ℓ x (z k))‖ ≤ 1` for all `x : 𝒜` and all `k`. -/
theorem exists_auerbachBasis {K U 𝒜 L : Type*} [Field K] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] [TopologicalSpace 𝒜] [CompactSpace 𝒜] [NormedField L]
    (φ : K →+* L) (ℓ : 𝒜 → Module.Dual K U)
    (hcont : ∀ v : U, Continuous fun a : 𝒜 => φ (ℓ a v))
    (hsep : ∀ v : U, (∀ a : 𝒜, ℓ a v = 0) → v = 0) :
    ∃ (a : Fin (Module.finrank K U) → 𝒜) (z : Module.Basis (Fin (Module.finrank K U)) K U),
      (∀ i j, ℓ (a i) (z j) = if i = j then 1 else 0) ∧
      ∀ (x : 𝒜) (k : Fin (Module.finrank K U)), ‖φ (ℓ x (z k))‖ ≤ 1 := by
  classical
  set n := Module.finrank K U
  let b := Module.finBasis K U
  by_cases hn0 : n = 0
  · have : IsEmpty (Fin n) := by rw [hn0]; infer_instance
    exact ⟨isEmptyElim, b, fun i => isEmptyElim i, fun _ k => isEmptyElim k⟩
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn0⟩⟩
  obtain ⟨f₀, hf₀⟩ := exists_evalMatrix_det_ne_zero ℓ hsep
  have : Nonempty (Fin n → 𝒜) := ⟨f₀⟩
  let M : (Fin n → 𝒜) → Matrix (Fin n) (Fin n) K := fun f => Matrix.of fun i j => ℓ (f i) (b j)
  have hM_cont : Continuous fun f : Fin n → 𝒜 => ‖φ (M f).det‖ := by
    have hmap : ∀ f : Fin n → 𝒜, φ (M f).det = ((M f).map φ).det := fun f => φ.map_det (M f)
    simp_rw [hmap]
    refine continuous_norm.comp (Continuous.matrix_det ?_)
    exact continuous_pi fun i => continuous_pi fun j => (hcont (b j)).comp (continuous_apply i)
  obtain ⟨a, -, ha_max⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hM_cont.continuousOn
  have ha_det : (M a).det ≠ 0 := by
    intro h0
    have hle : ‖φ (M f₀).det‖ ≤ ‖φ (M a).det‖ := ha_max (Set.mem_univ f₀)
    rw [h0, map_zero, norm_zero] at hle
    exact (norm_pos_iff.mpr ((map_ne_zero φ).mpr hf₀)).not_ge hle
  have hMN : M a * (M a)⁻¹ = 1 := Matrix.mul_nonsing_inv (M a) (isUnit_iff_ne_zero.mpr ha_det)
  let zvec : Fin n → U := fun k => ∑ j : Fin n, (M a)⁻¹ j k • b j
  have hdual : ∀ i k, ℓ (a i) (zvec k) = if i = k then 1 else 0 := fun i k => by
    have h := congrFun (congrFun hMN i) k
    simpa [zvec, M, Matrix.mul_apply, Matrix.one_apply, map_sum, map_smul, mul_comm] using h
  have hz_li : LinearIndependent K zvec := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    simpa [map_sum, map_smul, hdual] using congrArg (ℓ (a i)) hc
  have hz_span : ⊤ ≤ Submodule.span K (Set.range zvec) := by
    rw [top_le_iff]
    exact hz_li.span_eq_top_of_card_eq_finrank (Fintype.card_fin n)
  let z : Module.Basis (Fin n) K U := Module.Basis.mk hz_li hz_span
  have hz_apply : ∀ k, z k = zvec k := fun k => Module.Basis.mk_apply hz_li hz_span k
  exact ⟨a, z, fun i j => by rw [hz_apply]; exact hdual i j, fun x k =>
    norm_eval_le_one_of_isMaxOn φ ℓ b a (fun f => ha_max (Set.mem_univ f)) ha_det z hz_apply x k⟩

end TauCeti
