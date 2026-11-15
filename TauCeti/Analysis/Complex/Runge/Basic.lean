/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import TauCeti.Analysis.Complex.Runge.Operator
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.Runge.SimpleFraction
import TauCeti.Analysis.Normed.Module.FilledHull

/-!
# Runge's approximation theorem and characterization of the holomorphic hull

This file completes Runge's approximation theorem for plane domains and identifies the
`Ω`-holomorphic hull of a compact set `K ⊆ Ω` with its topological relative fill in `Ω`.

* **Runge equivalence (`TauCeti.isRungeCompactPair_iff_approximation`)**: for an open set `Ω ⊆ ℂ`
  and a compact subset `K ⊆ Ω`, `(Ω, K)` is a Runge compact pair (`IsFilledIn K Ω`) if and only if
  every function holomorphic on an open neighborhood of `K` can be uniformly approximated on `K` by
  functions holomorphic on `Ω`.
* **Topological formula for `holomorphicHull` (`TauCeti.holomorphicHull_eq_fill`)**: for open `Ω`
  and compact `K ⊆ Ω`, `holomorphicHull Ω K` is compact and equals `K` union those points
  `z ∈ Ω \ K` whose connected component in `Ω \ K` has compact closure contained in `Ω`. In
  particular, `holomorphicHull Ω K = K ↔ IsFilledIn K Ω` (`holomorphicHull_eq_self_iff_isFilledIn`),
  and on `Ω = univ` the holomorphic hull agrees with `TauCeti.filledHull K`
  (`IsCompact.holomorphicHull_univ_eq_filledHull`).
* **Polynomial Runge theorem
  (`IsCompact.isConnected_compl_iff_forall_exists_polynomial_norm_sub_lt`)**:
  for a compact set `K ⊆ ℂ`, `Kᶜ` is connected if and only if `(fun z (_ : Fin 1) ↦ z) '' K` is
  polynomially convex (`IsCompact.isConnected_compl_iff_isPolynomiallyConvex`), if and only if every
  function holomorphic on an open neighborhood of `K` is uniformly approximable on `K` by complex
  polynomials.

## Main results

* `TauCeti.IsRungeCompactPair.exists_differentiableOn_norm_sub_lt`: uniform `Ω`-holomorphic
  approximation on `K` of any function holomorphic near `K`.
* `TauCeti.isRungeCompactPair_iff_approximation`: equivalence between `IsRungeCompactPair Ω K` and
  uniform `Ω`-holomorphic approximation on `K`.
* `TauCeti.holomorphicHull_eq_fill`: `holomorphicHull Ω K` is compact and equals `K` union the
  relatively compact connected components of `Ω \ K`.
* `TauCeti.holomorphicHull_eq_self_iff_isFilledIn` and
  `TauCeti.isRungeCompactPair_iff_holomorphicHull_eq_self`: hull characterizations of filledness.
* `IsCompact.holomorphicHull_univ_eq_filledHull`,
  `IsCompact.isConnected_compl_iff_isPolynomiallyConvex`, and
  `IsCompact.isConnected_compl_iff_forall_exists_polynomial_norm_sub_lt`: whole-plane, polynomial
  convexity, and polynomial Runge specializations.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 11.1, Lemma 11.3, and Corollary 11.4.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorems 13.9 and 13.7.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.1
  and Theorem 1.3.3.
-/

public section

open Bornology Filter Metric Polynomial Set Topology
open scoped ENNReal NNReal

namespace TauCeti

/-- **Scalar Runge approximation.** If `(Ω, K)` is a Runge compact pair and `f` is holomorphic on
an open neighborhood `U` of `K`, then `f` can be uniformly approximated on `K` within any `ε > 0`
by a function holomorphic on all of `Ω`. -/
theorem IsRungeCompactPair.exists_differentiableOn_norm_sub_lt {Ω K U : Set ℂ}
    (hRunge : IsRungeCompactPair Ω K) (hU : IsOpen U) (hKU : K ⊆ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  obtain ⟨L, hL_cpt, -, hLUΩ, hop⟩ := exists_finite_rank_runge_operator hRunge hU hKU
  have hf_cont : ContinuousOn f L := hf.continuousOn.mono (hLUΩ.trans inter_subset_left)
  obtain ⟨M, hM⟩ := (hL_cpt.image_of_continuousOn hf_cont).isBounded.subset_closedBall 0
  set B : ℝ := max M 0 + 1
  have hB_pos : 0 < B := by positivity
  have hfB : ∀ z ∈ L, ‖f z‖ ≤ B := fun z hz ↦
    (mem_closedBall_zero_iff.mp (hM ⟨z, hz, rfl⟩)).trans <|
      (le_max_left M 0).trans (by linarith)
  obtain ⟨N, ζ, w, g₀, -, hg₀, happrox⟩ := hop (ε / (2 * B)) (by positivity)
  refine ⟨fun z ↦ ∑ j : Fin N, w j * f (ζ j) * g₀ j z, ?_, fun z hz ↦ ?_⟩
  · refine DifferentiableOn.fun_sum fun j _ ↦ ?_
    simpa only [mul_assoc] using (hg₀ j).const_mul (w j * f (ζ j))
  · refine (happrox f hf B hB_pos.le hfB z hz).trans_lt ?_
    have hB_ne : B ≠ 0 := hB_pos.ne'
    have heq : ε / (2 * B) * B = ε / 2 := by field_simp [hB_ne]
    rw [heq]
    exact half_lt_self hε

/-- If `z ↦ (z - a)⁻¹` is uniformly approximable on a compact set `K` by `Ω`-holomorphic functions
for a point `a ∈ Ω \ K`, then `a ∉ holomorphicHull Ω K`. -/
theorem _root_.IsCompact.notMem_holomorphicHull_of_forall_pos_exists_norm_inv_sub_lt
    {Ω K : Set ℂ} (hK : IsCompact K) {a : ℂ} (ha : a ∈ Ω \ K)
    (happrox : ∀ ε > 0, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧
      ∀ z ∈ K, ‖(z - a)⁻¹ - g z‖ < ε) :
    a ∉ holomorphicHull Ω K := by
  intro haH
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall a
  set M : ℝ := max R 0 + 1
  have hM_pos : 0 < M := by positivity
  have hza_le {z : ℂ} (hz : z ∈ K) : ‖z - a‖ ≤ M := by
    rw [← dist_eq_norm]
    exact (mem_closedBall.mp (hR hz)).trans ((le_max_left R 0).trans (by linarith))
  obtain ⟨g, hg, hg_err⟩ := happrox (2 * M)⁻¹ (by positivity)
  let h : ℂ → ℂ := 1 - (fun z ↦ z - a) * g
  have hh : DifferentiableOn ℂ h Ω :=
    (differentiableOn_const 1).sub ((differentiableOn_id.sub_const a).mul hg)
  have hh_le : ∀ z ∈ K, ‖h z‖ ≤ 1 / 2 := fun z hz ↦ by
    have hne : z - a ≠ 0 := sub_ne_zero.mpr fun hza ↦ ha.2 (hza ▸ hz)
    have h_eq : h z = (z - a) * ((z - a)⁻¹ - g z) := by
      simp only [h, Pi.sub_apply, Pi.one_apply, Pi.mul_apply]
      field_simp [hne]
    rw [h_eq, norm_mul]
    calc ‖z - a‖ * ‖(z - a)⁻¹ - g z‖
      _ ≤ M * (2 * M)⁻¹ :=
          mul_le_mul (hza_le hz) (hg_err z hz).le (norm_nonneg _) hM_pos.le
      _ = 1 / 2 := by
          have hM_ne : M ≠ 0 := hM_pos.ne'
          field_simp [hM_ne]
  have ha_le : ‖h a‖ ≤ 1 / 2 := (mem_holomorphicHull_iff.mp haH).2 h hh (1 / 2) hh_le
  have ha_one : ‖h a‖ = 1 := by simp [h]
  linarith

/-- **Runge's approximation theorem.** For an open set `Ω ⊆ ℂ` and a compact subset `K ⊆ Ω`,
`(Ω, K)` is a Runge compact pair if and only if every function holomorphic on an open neighborhood
of `K` is uniformly approximable on `K` by functions holomorphic on `Ω`. -/
theorem isRungeCompactPair_iff_approximation {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsRungeCompactPair Ω K ↔
      ∀ U : Set ℂ, IsOpen U → K ⊆ U →
      ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
        ∀ ε > 0, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧
          ∀ z ∈ K, ‖f z - g z‖ < ε := by
  refine ⟨fun hRunge U hU hKU f hf ε hε ↦
    hRunge.exists_differentiableOn_norm_sub_lt hU hKU hf hε, fun happrox ↦ ?_⟩
  refine isRungeCompactPair_iff.mpr ⟨hΩ, hK, hKΩ, isFilledIn_iff.mpr fun a ha ⟨hcpt, hclΩ⟩ ↦ ?_⟩
  have ha_hull : a ∈ holomorphicHull Ω K :=
    connectedComponentIn_sdiff_subset_holomorphicHull hΩ hK.isClosed hcpt hclΩ
      (mem_connectedComponentIn ha)
  have hKUa : K ⊆ {a}ᶜ := fun z hz (hza : z = a) ↦ ha.2 (hza ▸ hz)
  have hf_inv : DifferentiableOn ℂ (fun z : ℂ ↦ (z - a)⁻¹) {a}ᶜ :=
    (differentiableOn_id.sub_const a).inv fun z hz ↦ sub_ne_zero.mpr hz
  exact hK.notMem_holomorphicHull_of_forall_pos_exists_norm_inv_sub_lt ha
    (fun ε hε ↦ happrox {a}ᶜ isOpen_compl_singleton hKUa _ hf_inv ε hε) ha_hull

/-- **Topological characterization of `holomorphicHull`.** For an open set `Ω ⊆ ℂ` and a compact
subset `K ⊆ Ω`, the hull `holomorphicHull Ω K` is compact and equals `K` union the connected
components of `Ω \ K` whose closures are compact and contained in `Ω`. -/
theorem holomorphicHull_eq_fill {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsCompact (holomorphicHull Ω K) ∧
      holomorphicHull Ω K = K ∪ {z | z ∈ Ω \ K ∧
        IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
        closure (connectedComponentIn (Ω \ K) z) ⊆ Ω} := by
  refine ⟨hK.holomorphicHull hKΩ, ?_⟩
  let F : Set ℂ := K ∪ {z | z ∈ Ω \ K ∧
    IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
    closure (connectedComponentIn (Ω \ K) z) ⊆ Ω}
  have hF_sub_hull : F ⊆ holomorphicHull Ω K := by
    rintro z (hzK | ⟨hz, hcpt, hclΩ⟩)
    · exact subset_holomorphicHull hKΩ hzK
    · exact connectedComponentIn_sdiff_subset_holomorphicHull hΩ hK.isClosed hcpt hclΩ
        (mem_connectedComponentIn hz)
  have hFΩ : F ⊆ Ω := hF_sub_hull.trans holomorphicHull_subset_left
  -- For `x ∈ Ω \ F`, the entire component of `x` in `Ω \ K` stays inside `Ω \ F`.
  have hcomp_disj {x : ℂ} (hx : x ∈ Ω \ F) :
      connectedComponentIn (Ω \ K) x ⊆ Ω \ F := by
    intro y hy
    have hyΩK : y ∈ Ω \ K := connectedComponentIn_subset (Ω \ K) x hy
    refine ⟨hyΩK.1, ?_⟩
    rintro (hyK | ⟨-, hcpt, hclΩ⟩)
    · exact hyΩK.2 hyK
    · rw [← connectedComponentIn_eq hy] at hcpt hclΩ
      exact hx.2 (Or.inr ⟨⟨hx.1, fun hxK ↦ hx.2 (Or.inl hxK)⟩, hcpt, hclΩ⟩)
  have hΩF_open : IsOpen (Ω \ F) := by
    refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
    have hxΩK : x ∈ Ω \ K := ⟨hx.1, fun hxK ↦ hx.2 (Or.inl hxK)⟩
    exact ⟨connectedComponentIn (Ω \ K) x, hcomp_disj hx,
      (hΩ.sdiff hK.isClosed).connectedComponentIn, mem_connectedComponentIn hxΩK⟩
  have hF_eq_sdiff : F = holomorphicHull Ω K \ (Ω \ F) := by
    ext z
    exact ⟨fun hz ↦ ⟨hF_sub_hull hz, fun h ↦ h.2 hz⟩,
      fun ⟨hzH, hznot⟩ ↦ by_contra fun hzF ↦ hznot ⟨holomorphicHull_subset_left hzH, hzF⟩⟩
  have hF_cpt : IsCompact F := hF_eq_sdiff ▸ (hK.holomorphicHull hKΩ).diff hΩF_open
  have hF_fill : IsFilledIn F Ω := isFilledIn_iff.mpr fun x hx ⟨hcpt, hclΩ⟩ ↦ by
    have hxΩK : x ∈ Ω \ K := ⟨hx.1, fun hxK ↦ hx.2 (Or.inl hxK)⟩
    have hcomp_eq : connectedComponentIn (Ω \ F) x = connectedComponentIn (Ω \ K) x := by
      refine Subset.antisymm
        (connectedComponentIn_mono x (sdiff_subset_sdiff Subset.rfl subset_union_left)) ?_
      exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hxΩK) (hcomp_disj hx)
    rw [hcomp_eq] at hcpt hclΩ
    exact hx.2 (Or.inr ⟨hxΩK, hcpt, hclΩ⟩)
  refine Subset.antisymm (fun a haH ↦ by_contra fun haF ↦ ?_) hF_sub_hull
  have haΩK : a ∈ Ω \ K := ⟨holomorphicHull_subset_left haH, fun haK ↦ haF (Or.inl haK)⟩
  refine hK.notMem_holomorphicHull_of_forall_pos_exists_norm_inv_sub_lt haΩK
    (fun ε hε ↦ ?_) haH
  obtain ⟨g, hg, hgF⟩ :=
    hF_fill.exists_differentiableOn_norm_inv_sub_lt hΩ hF_cpt hFΩ haF hε
  exact ⟨g, hg, fun z hz ↦ hgF z (Or.inl hz)⟩

/-- A compact subset `K` of an open set `Ω ⊆ ℂ` equals its `Ω`-holomorphic hull if and only if `K`
is filled in `Ω`. -/
theorem holomorphicHull_eq_self_iff_isFilledIn {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    holomorphicHull Ω K = K ↔ IsFilledIn K Ω := by
  rw [(holomorphicHull_eq_fill hΩ hK hKΩ).2, isFilledIn_iff]
  exact ⟨fun h x hx ⟨hcpt, hclΩ⟩ ↦ hx.2 (h ▸ Or.inr ⟨hx, hcpt, hclΩ⟩),
    fun h ↦ Subset.antisymm (union_subset Subset.rfl fun x ⟨hx, hcpt, hclΩ⟩ ↦
      (h x hx ⟨hcpt, hclΩ⟩).elim) subset_union_left⟩

/-- For an open set `Ω ⊆ ℂ` and a compact subset `K ⊆ Ω`, `(Ω, K)` is a Runge compact pair if and
only if `holomorphicHull Ω K = K`. -/
theorem isRungeCompactPair_iff_holomorphicHull_eq_self {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsRungeCompactPair Ω K ↔ holomorphicHull Ω K = K := by
  rw [isRungeCompactPair_iff, holomorphicHull_eq_self_iff_isFilledIn hΩ hK hKΩ]
  exact ⟨fun h ↦ h.2.2.2, fun h ↦ ⟨hΩ, hK, hKΩ, h⟩⟩

/-- On the whole complex plane, the holomorphic hull of a compact set `K ⊆ ℂ` coincides with its
topological filled hull `filledHull K`. -/
theorem _root_.IsCompact.holomorphicHull_univ_eq_filledHull {K : Set ℂ} (hK : IsCompact K) :
    holomorphicHull univ K = filledHull K := by
  refine Subset.antisymm ?_ ?_
  · rw [(holomorphicHull_eq_fill isOpen_univ hK (subset_univ K)).2]
    rintro z (hzK | ⟨-, hcpt, -⟩)
    · exact subset_filledHull hzK
    · rw [← compl_eq_univ_sdiff] at hcpt
      exact mem_filledHull_iff.mpr (hcpt.isBounded.subset subset_closure)
  · have hfill : filledHull (holomorphicHull univ K) = holomorphicHull univ K :=
      (isFilledIn_univ_iff (hK.holomorphicHull (subset_univ K)).isClosed).mp
        (hK.isFilledIn_holomorphicHull isOpen_univ (subset_univ K))
    exact (filledHull_mono (subset_holomorphicHull (subset_univ K))).trans_eq hfill

/-- For a compact set `K ⊆ ℂ`, `(univ, K)` is a Runge compact pair if and only if `Kᶜ` is
connected. -/
theorem _root_.IsCompact.isRungeCompactPair_univ_iff_isConnected_compl {K : Set ℂ}
    (hK : IsCompact K) : IsRungeCompactPair univ K ↔ IsConnected Kᶜ := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  rw [isRungeCompactPair_iff, isFilledIn_univ_iff hK.isClosed]
  refine ⟨fun h ↦ h.2.2.2 ▸ isConnected_compl_filledHull hrank hK.isBounded, fun hconn ↦ ?_⟩
  refine ⟨isOpen_univ, hK, subset_univ K, filledHull_eq_self hconn.isPreconnected fun hKc ↦ ?_⟩
  exact NormedSpace.unbounded_univ ℝ ℂ (union_compl_self K ▸ hK.isBounded.union hKc)

/-- For a compact set `K ⊆ ℂ`, `Kᶜ` is connected if and only if `(fun z (_ : Fin 1) ↦ z) '' K` is
polynomially convex in `Fin 1 → ℂ`. -/
theorem _root_.IsCompact.isConnected_compl_iff_isPolynomiallyConvex {K : Set ℂ}
    (hK : IsCompact K) :
    IsConnected Kᶜ ↔ IsPolynomiallyConvex ((fun z (_ : Fin 1) ↦ z) '' K) := by
  rw [← hK.isRungeCompactPair_univ_iff_isConnected_compl,
    isRungeCompactPair_iff_holomorphicHull_eq_self isOpen_univ hK (subset_univ K),
    hK.isBounded.holomorphicHull_univ_eq_self_iff_isPolynomiallyConvex]

/-- **Polynomial Runge theorem.** For a compact subset `K ⊆ ℂ`, `Kᶜ` is connected if and only if
every function holomorphic on an open neighborhood of `K` can be uniformly approximated on `K` by
complex polynomials. -/
theorem _root_.IsCompact.isConnected_compl_iff_forall_exists_polynomial_norm_sub_lt {K : Set ℂ}
    (hK : IsCompact K) :
    IsConnected Kᶜ ↔
      ∀ U : Set ℂ, IsOpen U → K ⊆ U →
      ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
        ∀ ε > 0, ∃ P : Polynomial ℂ, ∀ z ∈ K, ‖f z - P.eval z‖ < ε := by
  rw [← hK.isRungeCompactPair_univ_iff_isConnected_compl,
    isRungeCompactPair_iff_approximation isOpen_univ hK (subset_univ K)]
  refine ⟨fun h U hU hKU f hf ε hε ↦ ?_, fun h U hU hKU f hf ε hε ↦ ?_⟩
  · obtain ⟨g, hg, hfg⟩ := h U hU hKU f hf (ε / 2) (half_pos hε)
    have hg_ent : Differentiable ℂ g := differentiableOn_univ.mp hg
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    set R : ℝ≥0 := (max r 0 + 1).toNNReal
    have hR_val : (R : ℝ) = max r 0 + 1 := Real.coe_toNNReal _ (by positivity)
    have hps := hg_ent.hasFPowerSeriesOnBall 0 (R := (1 : ℝ≥0)) one_pos
    have hu := hps.tendstoUniformlyOn (r' := R) ENNReal.coe_lt_top
    obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.mp hu (ε / 2) (half_pos hε)).exists
    set p := cauchyPowerSeries g 0 (1 : ℝ≥0)
    let P : Polynomial ℂ := ∑ k ∈ Finset.range N, Polynomial.C (p.coeff k) * Polynomial.X ^ k
    have heval (z : ℂ) : P.eval z = p.partialSum N z := by
      simp only [P, FormalMultilinearSeries.partialSum, eval_finsetSum, eval_mul, eval_pow,
        eval_C, eval_X, FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
    refine ⟨P, fun z hz ↦ ?_⟩
    have hzR : z ∈ ball (0 : ℂ) R := by
      rw [mem_ball, hR_val]
      exact (mem_closedBall.mp (hr hz)).trans_lt (by linarith [le_max_left r 0])
    have hgP : ‖g z - P.eval z‖ < ε / 2 := by
      have hNz : ‖g (0 + z) - p.partialSum N z‖ < ε / 2 := by
        simpa only [dist_eq_norm] using hN z hzR
      rwa [zero_add, ← heval] at hNz
    calc ‖f z - P.eval z‖
      _ = ‖(f z - g z) + (g z - P.eval z)‖ := by congr 1; abel
      _ ≤ ‖f z - g z‖ + ‖g z - P.eval z‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hfg z hz) hgP
      _ = ε := add_halves ε
  · obtain ⟨P, hP⟩ := h U hU hKU f hf ε hε
    exact ⟨fun z ↦ P.eval z, P.differentiableOn, hP⟩

end TauCeti
