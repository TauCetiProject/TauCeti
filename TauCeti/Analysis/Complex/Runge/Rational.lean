/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.Module.PerfectSpace
import TauCeti.Analysis.Complex.Pompeiu.Discretization
import TauCeti.Analysis.Complex.Runge.Approximation
import TauCeti.Analysis.Normed.Field.Inversion
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Geometry.Manifold.Connected
import TauCeti.Topology.Compactification.OnePoint.FilledHull
import TauCeti.Topology.Perfect

/-!
# Rational Runge approximation with prescribed poles in the Riemann sphere

Given a compact subset `K ⊆ ℂ` and a prescribed pole set `A ⊆ OnePoint ℂ` that meets every
connected component of `(((↑) : ℂ → OnePoint ℂ) '' K)ᶜ` in the Riemann sphere `OnePoint ℂ`, every
function holomorphic on an open neighbourhood of `K` can be uniformly approximated on `K` by
rational functions of the form `z ↦ P.eval z + ∑ a ∈ s, (Q a).eval (z - a)⁻¹` with finite poles
`a ∈ s` lying in `A \ K`, `(Q a).coeff 0 = 0`, and `P = 0` whenever `∞ ∉ A`
(`IsCompact.exists_polynomial_add_sum_eval_sub_inv_norm_sub_lt`).

The proof discretizes the Cauchy–Pompeiu representation
(`IsCompact.exists_norm_sub_sum_mul_sub_inv_smul_le`) into a finite linear combination of simple
fractions `(z - ζ)⁻¹` with `ζ ∉ K`, and then pushes each pole `ζ` across its complementary
component: either to `∞ ∈ A` via the polynomial Runge theorem on `TauCeti.filledHull K`, or to a
finite pole `b ∈ A` in the same component of `Kᶜ` via inversion at `b`
(`IsCompact.exists_polynomial_eval_sub_inv_norm_sub_lt`).

## Main results

* `IsCompact.exists_polynomial_eval_sub_inv_norm_sub_lt`: single-pole pushing across a connected
  component of `Kᶜ` into polynomials in `(z - b)⁻¹` with vanishing constant term.
* `IsCompact.exists_polynomial_add_sum_eval_sub_inv_norm_sub_lt`: rational Runge approximation on
  `K` with poles restricted to a set `A : Set (OnePoint ℂ)` meeting every complementary component
  of `K` in `OnePoint ℂ`.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorems 13.5–13.9.
* A. Rainer, *Advanced Complex Analysis*, Corollary 11.4.
-/

public section

open Polynomial Set TauCeti
open scoped OnePoint

private theorem sub_inv_notMem_filledHull_image {K : Set ℂ} (hK : IsClosed K) {ζ b : ℂ}
    (hb : b ∈ connectedComponentIn Kᶜ ζ) (hζb : ζ ≠ b) :
    (ζ - b)⁻¹ ∉ filledHull ((fun z ↦ (z - b)⁻¹) '' K) := by
  intro hζ'_hull
  have hζK : ζ ∉ K := connectedComponentIn_nonempty_iff.mp ⟨b, hb⟩
  set D : Set ℂ := connectedComponentIn Kᶜ ζ
  have hD_open : IsOpen D := hK.isOpen_compl.connectedComponentIn
  have hDb_pre : IsPreconnected (D \ {b}) :=
    isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank (E := ℂ) (by simp) hD_open
      isPreconnected_connectedComponentIn isClosed_singleton (finite_singleton b).isDiscrete
  have hφD_pre : IsPreconnected ((fun z ↦ (z - b)⁻¹) '' (D \ {b})) := hDb_pre.image _
    ((continuous_id.sub continuous_const).continuousOn.inv₀ fun _ hz ↦ sub_ne_zero.mpr hz.right)
  have hφD_compl : (fun z ↦ (z - b)⁻¹) '' (D \ {b}) ⊆ ((fun z ↦ (z - b)⁻¹) '' K)ᶜ := by
    rintro _ ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, heq⟩
    have h12 : z₁ = z₂ := by simpa using heq.symm
    exact connectedComponentIn_subset Kᶜ ζ hz₁.left (h12 ▸ hz₂)
  have hsub := hφD_pre.subset_connectedComponentIn
    ⟨ζ, ⟨mem_connectedComponentIn hζK, hζb⟩, rfl⟩ hφD_compl
  have hnot_cl : b ∉ closure (D \ {b}) :=
    (isBounded_image_inv_sub_iff (q := b) (U := D \ {b}) fun h ↦ h.right rfl).mp
      ((mem_filledHull_iff.mp hζ'_hull).subset hsub)
  exact hnot_cl (hD_open.subset_closure_sdiff_of_isDiscrete
    ((finite_singleton b).subset inter_subset_right).isDiscrete hb)

/-- **Single-pole pole pushing across a complementary component.** If `K ⊆ ℂ` is compact and `b`
lies in the connected component of `ζ` in `Kᶜ`, then for every `η > 0` the simple fraction
`z ↦ (z - ζ)⁻¹` is uniformly approximated on `K` within `η` by `z ↦ R.eval (z - b)⁻¹` for a
polynomial `R : ℂ[X]` with `R.coeff 0 = 0`. -/
theorem IsCompact.exists_polynomial_eval_sub_inv_norm_sub_lt {K : Set ℂ} (hK : IsCompact K)
    {ζ b : ℂ} (hb : b ∈ connectedComponentIn Kᶜ ζ) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℂ[X], R.coeff 0 = 0 ∧ ∀ z ∈ K, ‖(z - ζ)⁻¹ - R.eval (z - b)⁻¹‖ < η := by
  by_cases hζb : ζ = b
  · subst hζb
    exact ⟨X, coeff_X_zero, fun z _ ↦ by simpa using hη⟩
  have hζK : ζ ∉ K := connectedComponentIn_nonempty_iff.mp ⟨b, hb⟩
  have hbK : b ∉ K := connectedComponentIn_subset Kᶜ ζ hb
  set φ : ℂ → ℂ := fun z ↦ (z - b)⁻¹
  set K' : Set ℂ := φ '' K
  set ζ' : ℂ := φ ζ
  have hK' : IsCompact K' := hK.image_of_continuousOn
    ((continuous_id.sub continuous_const).continuousOn.inv₀ fun z hz ↦
      sub_ne_zero.mpr fun (h : z = b) ↦ hbK (h ▸ hz))
  have hζ'_not_hull : ζ' ∉ filledHull K' := sub_inv_notMem_filledHull_image hK.isClosed hb hζb
  -- Approximate `w ↦ -ζ' * (w - ζ')⁻¹` by `Q₀` on `filledHull K'`, then set `R = X * Q₀`.
  obtain ⟨M, hM⟩ := hK'.isBounded.exists_norm_le
  obtain ⟨δ, hδ, hMδ⟩ := exists_pos_mul_lt hη M
  have hf' : DifferentiableOn ℂ (fun w : ℂ ↦ -ζ' * (w - ζ')⁻¹) {ζ'}ᶜ :=
    (differentiableOn_const (-ζ')).mul
      ((differentiableOn_id.sub (differentiableOn_const ζ')).inv fun _ hw ↦ sub_ne_zero.mpr hw)
  obtain ⟨Q₀, hQ₀⟩ :=
    (hK'.isCompact_filledHull
      |>.isConnected_compl_iff_forall_differentiableOn_exists_polynomial_norm_sub_lt.mp
      (isConnected_compl_filledHull (by simp) hK'.isBounded)) {ζ'}ᶜ isOpen_compl_singleton
      (fun _ hw (h : _ = ζ') ↦ hζ'_not_hull (h ▸ hw)) _ hf' δ hδ
  refine ⟨X * Q₀, by simp, fun z hz ↦ ?_⟩
  have hzb : z - b ≠ 0 := sub_ne_zero.mpr fun (h : z = b) ↦ hbK (h ▸ hz)
  have hζb' : ζ - b ≠ 0 := sub_ne_zero.mpr hζb
  have hzζ : z - ζ ≠ 0 := sub_ne_zero.mpr fun (h : z = ζ) ↦ hζK (h ▸ hz)
  have hmobius : φ z * (-ζ' * (φ z - ζ')⁻¹) = (z - ζ)⁻¹ := by
    have hdiff : φ z - ζ' = -(z - ζ) / ((z - b) * (ζ - b)) := by
      dsimp only [φ, ζ']; field_simp [hzb, hζb']; ring
    rw [hdiff, inv_div]; dsimp only [φ, ζ']; field_simp [hzb, hζb', hzζ]
  have hid : (z - ζ)⁻¹ - (X * Q₀).eval (φ z) = φ z * (-ζ' * (φ z - ζ')⁻¹ - Q₀.eval (φ z)) := by
    simp only [eval_mul, eval_X, mul_sub, hmobius]
  rw [hid, norm_mul]
  have hφz_le : ‖φ z‖ ≤ M := hM (φ z) (mem_image_of_mem φ hz)
  exact (mul_le_mul hφz_le (hQ₀ (φ z) (subset_filledHull (mem_image_of_mem φ hz))).le
    (norm_nonneg _) ((norm_nonneg _).trans hφz_le)).trans_lt hMδ

private theorem exists_polynomial_or_eval_sub_inv_norm_sub_lt {K : Set ℂ} {A : Set (OnePoint ℂ)}
    (hK : IsCompact K)
    (hA : ∀ x ∈ (((↑) : ℂ → OnePoint ℂ) '' K)ᶜ,
      (A ∩ connectedComponentIn (((↑) : ℂ → OnePoint ℂ) '' K)ᶜ x).Nonempty)
    {ζ : ℂ} (hζK : ζ ∉ K) {η : ℝ} (hη : 0 < η) :
    ((∞ : OnePoint ℂ) ∈ A ∧ ∃ P : ℂ[X], ∀ z ∈ K, ‖(z - ζ)⁻¹ - P.eval z‖ < η) ∨
      ∃ (b : ℂ) (R : ℂ[X]), (b : OnePoint ℂ) ∈ A ∧ b ∉ K ∧ R.coeff 0 = 0 ∧
        ∀ z ∈ K, ‖(z - ζ)⁻¹ - R.eval (z - b)⁻¹‖ < η := by
  set S : Set (OnePoint ℂ) := ((↑) : ℂ → OnePoint ℂ) '' K
  have hζS : (ζ : OnePoint ℂ) ∈ Sᶜ := fun ⟨_, hy, hyζ⟩ ↦ hζK (OnePoint.coe_injective hyζ ▸ hy)
  obtain ⟨p, hpA, hpC⟩ := hA (ζ : OnePoint ℂ) hζS
  rcases p with _ | b
  · -- The component of `ζ` in `Sᶜ` contains `∞`, so `ζ` lies outside `filledHull K`.
    have hζ_not_hull : ζ ∉ filledHull K := by
      intro hζ_hull
      rw [connectedComponentIn_compl_image_coe hK.isClosed ⟨hζ_hull, hζK⟩] at hpC
      obtain ⟨_, -, h_eq⟩ := hpC
      exact OnePoint.coe_ne_infty _ h_eq
    have hf_inv : DifferentiableOn ℂ (fun z : ℂ ↦ (z - ζ)⁻¹) {ζ}ᶜ :=
      (differentiableOn_id.sub (differentiableOn_const ζ)).inv fun _ hz ↦ sub_ne_zero.mpr hz
    obtain ⟨P, hP⟩ :=
      (hK.isCompact_filledHull
        |>.isConnected_compl_iff_forall_differentiableOn_exists_polynomial_norm_sub_lt.mp
        (isConnected_compl_filledHull (by simp) hK.isBounded)) {ζ}ᶜ isOpen_compl_singleton
        (fun _ hz (h : _ = ζ) ↦ hζ_not_hull (h ▸ hz)) _ hf_inv η hη
    exact Or.inl ⟨hpA, P, fun z hz ↦ hP z (subset_filledHull hz)⟩
  · -- A finite allowed pole `b` lies in the same component of `Kᶜ` as `ζ`.
    have hbK : b ∉ K := fun hbK ↦ connectedComponentIn_subset Sᶜ _ hpC (mem_image_of_mem _ hbK)
    have hb_comp : b ∈ connectedComponentIn Kᶜ ζ := by
      by_cases hζ_hull : ζ ∈ filledHull K
      · rw [connectedComponentIn_compl_image_coe hK.isClosed ⟨hζ_hull, hζK⟩] at hpC
        obtain ⟨y, hy, hyb⟩ := hpC
        exact OnePoint.coe_injective hyb ▸ hy
      · have hb_not_hull : b ∉ filledHull K := by
          intro hb_hull
          have hζ_in : (ζ : OnePoint ℂ) ∈ connectedComponentIn Sᶜ (b : OnePoint ℂ) :=
            connectedComponentIn_eq hpC ▸ mem_connectedComponentIn hζS
          rw [connectedComponentIn_compl_image_coe hK.isClosed ⟨hb_hull, hbK⟩] at hζ_in
          obtain ⟨y, hy, hyζ⟩ := hζ_in
          exact hζ_hull ((mem_filledHull_iff_of_mem_connectedComponentIn
            (OnePoint.coe_injective hyζ ▸ hy)).mpr hb_hull)
        rwa [← compl_filledHull_eq_connectedComponentIn (by simp) hK.isBounded hζ_hull]
    obtain ⟨R, hR0, hR⟩ := hK.exists_polynomial_eval_sub_inv_norm_sub_lt hb_comp hη
    exact Or.inr ⟨b, R, hpA, hbK, hR0, hR⟩

private theorem exists_polynomial_add_sum_eval_sub_inv_of_sum {K : Set ℂ} {A : Set (OnePoint ℂ)}
    (hK : IsCompact K)
    (hA : ∀ x ∈ (((↑) : ℂ → OnePoint ℂ) '' K)ᶜ,
      (A ∩ connectedComponentIn (((↑) : ℂ → OnePoint ℂ) '' K)ᶜ x).Nonempty)
    {N : ℕ} (c ζ : Fin N → ℂ) (hζ : ∀ j, ζ j ∉ K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (P : ℂ[X]) (s : Finset ℂ) (Q : ℂ → ℂ[X]),
      (∀ a ∈ s, (a : OnePoint ℂ) ∈ A ∧ a ∉ K) ∧
      ((∞ : OnePoint ℂ) ∉ A → P = 0) ∧
      (∀ a ∈ s, (Q a).coeff 0 = 0) ∧
      ∀ z ∈ K, ‖(∑ j, c j * (z - ζ j)⁻¹) - (P.eval z + ∑ a ∈ s, (Q a).eval (z - a)⁻¹)‖ ≤ δ := by
  classical
  obtain ⟨η, hη, hScη⟩ := exists_pos_mul_lt hδ (∑ j : Fin N, ‖c j‖)
  -- Step 1: Push each simple pole `ζ j` either to `∞ ∈ A` (recorded by `u j = true`, yielding a
  -- polynomial `P_fn j`) or to a finite pole `b_fn j ∈ A \ K` (recorded by `u j = false`, yielding
  -- a polynomial `R_fn j` in `(z - b_fn j)⁻¹` without constant term).
  have hstep (j : Fin N) : ∃ (u : Bool) (Pj : ℂ[X]) (bj : ℂ) (Rj : ℂ[X]),
      if u then (∞ : OnePoint ℂ) ∈ A ∧ ∀ z ∈ K, ‖(z - ζ j)⁻¹ - Pj.eval z‖ < η
      else (bj : OnePoint ℂ) ∈ A ∧ bj ∉ K ∧ Rj.coeff 0 = 0 ∧
        ∀ z ∈ K, ‖(z - ζ j)⁻¹ - Rj.eval (z - bj)⁻¹‖ < η := by
    rcases exists_polynomial_or_eval_sub_inv_norm_sub_lt hK hA (hζ j) hη with
      ⟨hinf, Pj, hPj⟩ | ⟨bj, Rj, hbjA, hbjK, hRj0, hRj⟩
    · exact ⟨true, Pj, 0, 0, hinf, hPj⟩
    · exact ⟨false, 0, bj, Rj, hbjA, hbjK, hRj0, hRj⟩
  choose u P_fn b_fn R_fn hu using hstep
  -- Step 2: Sum the poles pushed to `∞` into `P`, and group the finite poles fiberwise over
  -- `s = J_fin.image b_fn` into `Q a`.
  set J_inf : Finset (Fin N) := Finset.univ.filter (fun j ↦ u j = true)
  set J_fin : Finset (Fin N) := Finset.univ.filter (fun j ↦ ¬ u j = true)
  set P : ℂ[X] := ∑ j ∈ J_inf, C (c j) * P_fn j
  set s : Finset ℂ := J_fin.image b_fn
  set Q : ℂ → ℂ[X] := fun a ↦ ∑ j ∈ J_fin with b_fn j = a, C (c j) * R_fn j
  refine ⟨P, s, Q, fun a ha ↦ ?_, fun hinfA ↦ Finset.sum_eq_zero fun j hj ↦ ?_,
    fun a _ ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    have huf : u j = false := Bool.eq_false_iff.mpr (Finset.mem_filter.mp hj).right
    have hj_prop := hu j; rw [huf] at hj_prop
    exact ⟨hj_prop.1, hj_prop.2.1⟩
  · have hut : u j = true := (Finset.mem_filter.mp hj).right
    have hj_prop := hu j; rw [hut] at hj_prop
    exact (hinfA hj_prop.1).elim
  · simp only [Q, finsetSum_coeff, coeff_C_mul]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have huf : u j = false :=
      Bool.eq_false_iff.mpr (Finset.mem_filter.mp (Finset.mem_filter.mp hj).left).right
    have hj_prop := hu j; rw [huf] at hj_prop
    rw [hj_prop.2.2.1, mul_zero]
  · -- Step 3: Regroup `∑ a ∈ s, (Q a).eval (z - a)⁻¹` back over `J_fin` via `Finset.sum_image'`,
    -- recombine `J_inf` and `J_fin`, and sum the per-term `η`-estimates.
    set approx : Fin N → ℂ := fun j ↦
      if u j = true then (P_fn j).eval z else (R_fn j).eval (z - b_fn j)⁻¹
    have hsum_Q : ∑ a ∈ s, (Q a).eval (z - a)⁻¹ = ∑ j ∈ J_fin, c j * approx j :=
      (Finset.sum_image' (fun j ↦ (C (c j) * R_fn j).eval (z - b_fn j)⁻¹) fun j _ ↦ by
        rw [eval_finsetSum]
        exact Finset.sum_congr rfl fun i hi ↦ by rw [(Finset.mem_filter.mp hi).right]).trans <|
        Finset.sum_congr rfl fun j hj ↦ by
          simp [approx, ite_eq_right (Finset.mem_filter.mp hj).right]
    have hsum_P : P.eval z = ∑ j ∈ J_inf, c j * approx j := by
      simp only [P, eval_finsetSum, eval_mul, eval_C]
      exact Finset.sum_congr rfl fun j hj ↦ by
        simp [approx, ite_eq_left (Finset.mem_filter.mp hj).right]
    have herr_j (j : Fin N) : ‖(z - ζ j)⁻¹ - approx j‖ ≤ η := by
      have hj_prop := hu j
      cases huj : u j <;> rw [huj] at hj_prop
      · simpa [approx, huj] using (hj_prop.2.2.2 z hz).le
      · simpa [approx, huj] using (hj_prop.2 z hz).le
    rw [hsum_P, hsum_Q, Finset.sum_filter_add_sum_filter_not, ← Finset.sum_sub_distrib]
    calc ‖∑ j, (c j * (z - ζ j)⁻¹ - c j * approx j)‖
        ≤ ∑ j, ‖c j‖ * η := (norm_sum_le _ _).trans <| Finset.sum_le_sum fun j _ ↦ by
            rw [← mul_sub, norm_mul]; exact mul_le_mul_of_nonneg_left (herr_j j) (norm_nonneg _)
      _ = (∑ j, ‖c j‖) * η := (Finset.sum_mul _ _ _).symm
      _ ≤ δ := hScη.le

/-- **Rational Runge theorem with prescribed pole set in the Riemann sphere.** Let `K ⊆ ℂ` be
compact, let `f : ℂ → ℂ` be holomorphic on an open neighbourhood `U` of `K`, and let
`A : Set (OnePoint ℂ)` meet every connected component of the complement of `K` in `OnePoint ℂ`. For
every `ε > 0`, `f` can be uniformly approximated on `K` within `ε` by a rational function
`z ↦ P.eval z + ∑ a ∈ s, (Q a).eval (z - a)⁻¹` whose finite poles `a ∈ s` lie in `A` outside `K`,
with `(Q a).coeff 0 = 0` for each `a ∈ s` and `P = 0` whenever `∞ ∉ A`. -/
theorem IsCompact.exists_polynomial_add_sum_eval_sub_inv_norm_sub_lt
    {K U : Set ℂ} {A : Set (OnePoint ℂ)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hA : ∀ x ∈ (((↑) : ℂ → OnePoint ℂ) '' K)ᶜ,
      (A ∩ connectedComponentIn (((↑) : ℂ → OnePoint ℂ) '' K)ᶜ x).Nonempty)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : ℂ[X]) (s : Finset ℂ) (Q : ℂ → ℂ[X]),
      (∀ a ∈ s, (a : OnePoint ℂ) ∈ A ∧ a ∉ K) ∧
      ((∞ : OnePoint ℂ) ∉ A → P = 0) ∧
      (∀ a ∈ s, (Q a).coeff 0 = 0) ∧
      ∀ z ∈ K, ‖f z - (P.eval z + ∑ a ∈ s, (Q a).eval (z - a)⁻¹)‖ < ε := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn (hf.continuousOn.mono hLU)
  obtain ⟨δ, hδ, hMδ⟩ := exists_pos_mul_lt (half_pos hε) M
  obtain ⟨N, ζ, w, hζ, hrat⟩ :=
    hK.exists_norm_sub_sum_mul_sub_inv_smul_le isOpen_interior hKL hδ
  set c : Fin N → ℂ := fun j ↦ w j * f (ζ j)
  obtain ⟨P, s, Q, hsA, hP0, hQ0, hpush⟩ := exists_polynomial_add_sum_eval_sub_inv_of_sum hK hA
    c ζ (fun j ↦ (hζ j).right) (half_pos hε)
  refine ⟨P, s, Q, hsA, hP0, hQ0, fun z hz ↦ ?_⟩
  have herr_rat : ‖f z - ∑ j, c j * (z - ζ j)⁻¹‖ < ε / 2 := by
    have h1 := hrat f M (hf.mono (interior_subset.trans hLU))
      (fun u hu ↦ hM u (interior_subset hu)) z hz
    have heq : (∑ j, (w j * (z - ζ j)⁻¹) • f (ζ j)) = ∑ j, c j * (z - ζ j)⁻¹ :=
      Finset.sum_congr rfl fun j _ ↦ by dsimp only [c]; rw [smul_eq_mul]; ring
    rw [heq] at h1
    exact h1.trans_lt (mul_comm δ M ▸ hMδ)
  calc ‖f z - (P.eval z + ∑ a ∈ s, (Q a).eval (z - a)⁻¹)‖
      ≤ ‖f z - ∑ j, c j * (z - ζ j)⁻¹‖ +
          ‖(∑ j, c j * (z - ζ j)⁻¹) - (P.eval z + ∑ a ∈ s, (Q a).eval (z - a)⁻¹)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := by linarith [hpush z hz]
    _ = ε := add_halves ε
