/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnit.Basic
public import TauCeti.Analysis.CStarAlgebra.Ideal
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# Quasicentral approximate units in closed ideals of C⋆-algebras

An approximate unit `l` of a closed two-sided ideal `I` in a C⋆-algebra `A` is *quasicentral* if
`‖(e : A) * a - a * (e : A)‖ → 0` along `l` for every `a : A`. Arveson proved that every closed
two-sided ideal of a C⋆-algebra admits a quasicentral increasing approximate unit.

Quasicentral approximate units allow elements of `A` to commute asymptotically with ideal cutoffs
`e` and complementary cutoffs `1 - e` in short exact sequences `0 → I → A → A ⧸ I → 0`. They
underpin quotient-norm formulas `‖π a‖ = lim ‖a - a * e‖`, asymptotic multiplicativity of linear
splittings, Voiculescu–Weyl–von Neumann and Kasparov absorption arguments, and boundary maps in
operator K-theory. Since functional-calculus cutoffs from a single positive element in `I` need
not commute asymptotically with all elements of `A`, this file constructs quasicentral approximate
units by convex averaging.

General transport lemmas for asymptotic centrality (preservation under real convexification and
under continuous surjective nonunital ring homomorphisms) live in
`TauCeti.Analysis.Normed.Ring.Convex` and `TauCeti.Topology.Algebra.Ring.Basic`.

## Main results

* `NonUnitalStarSubalgebra.exists_quasicentral_isIncreasingApproximateUnit` and
  `TwoSidedIdeal.exists_quasicentral_isIncreasingApproximateUnit`: **Arveson's theorem** producing
  a quasicentral increasing approximate unit that eventually strictly contracts and dominates any
  given strict positive contraction `u₀`, together with the finite-family approximation forms
  `NonUnitalStarSubalgebra.exists_quasicentral_approx` and
  `TwoSidedIdeal.exists_quasicentral_approx`.
* `NonUnitalStarSubalgebra.exists_seq_quasicentral_isIncreasingApproximateUnit` and
  `TwoSidedIdeal.exists_seq_quasicentral_isIncreasingApproximateUnit`: when `A` is separable, there
  is a monotone sequence `u : ℕ → I` of nonnegative strict contractions forming a quasicentral
  increasing approximate unit of `I`.

## References

* W. Arveson, *Notes on extensions of C*-algebras*, Duke Math. J. 44 (1977), 329–355.
* B. Blackadar, *Operator Algebras*, II.4.3.
-/

public section

open Filter Topology
open scoped CStarAlgebra ComplexOrder

namespace NonUnitalStarSubalgebra

section Arveson

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Off-diagonal inner-product estimate in Arveson's averaging argument: if `p` right-approximates
`star d₁` within `δ` and `w₂` right-approximates both `p` and `p * a` within `δ`, then
`‖star d₁ * d₂‖ ≤ 2 * ‖a‖ * (‖a‖ + 2) * δ`. -/
private theorem norm_star_commutator_mul_le {w₁ w₂ p a : A}
    (hw₁ : ‖w₁‖ ≤ 1) (hw₂ : ‖w₂‖ ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (hp_d₁ : ‖star (w₁ * a - a * w₁) * p - star (w₁ * a - a * w₁)‖ ≤ δ)
    (hw₂_p : ‖p * w₂ - p‖ ≤ δ)
    (hw₂_pa : ‖(p * a) * w₂ - p * a‖ ≤ δ) :
    ‖star (w₁ * a - a * w₁) * (w₂ * a - a * w₂)‖ ≤ 2 * ‖a‖ * (‖a‖ + 2) * δ := by
  let d₁ : A := w₁ * a - a * w₁
  let d₂ : A := w₂ * a - a * w₂
  have hd₁ : ‖star d₁‖ ≤ 2 * ‖a‖ := (norm_star d₁).trans_le <|
    (TauCeti.norm_commutator_le w₁ a).trans (by nlinarith [norm_nonneg a])
  have hd₂ : ‖d₂‖ ≤ 2 * ‖a‖ :=
    (TauCeti.norm_commutator_le w₂ a).trans (by nlinarith [norm_nonneg a])
  have hid : star d₁ * d₂ =
      (star d₁ - star d₁ * p) * d₂ + star d₁ * ((p * w₂ - p) * a - ((p * a) * w₂ - p * a)) := by
    dsimp only [d₂]
    noncomm_ring
  rw [hid]
  have h1 : ‖(star d₁ - star d₁ * p) * d₂‖ ≤ δ * (2 * ‖a‖) := by
    refine (norm_mul_le _ _).trans (mul_le_mul ?_ hd₂ (norm_nonneg _) hδ)
    rwa [norm_sub_rev]
  have h2 : ‖star d₁ * ((p * w₂ - p) * a - ((p * a) * w₂ - p * a))‖ ≤
      (2 * ‖a‖) * (δ * ‖a‖ + δ) := by
    refine (norm_mul_le _ _).trans (mul_le_mul hd₁ ?_ (norm_nonneg _) (by positivity))
    refine (norm_sub_le _ _).trans (add_le_add ?_ hw₂_pa)
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hw₂_p (norm_nonneg a))
  linarith [(norm_add_le ((star d₁ - star d₁ * p) * d₂)
    (star d₁ * ((p * w₂ - p) * a - ((p * a) * w₂ - p * a)))).trans (add_le_add h1 h2)]

/-- Pairwise inner-product bound for the commutators `d k = w k * a - a * w k` in Arveson's
averaging argument, combining diagonal norm bounds with off-diagonal approximate orthogonality. -/
private theorem norm_star_commutator_pair_le {N : ℕ} {w p : Fin N → A} {a : A} {M δ : ℝ}
    (hw : ∀ k, ‖w k‖ ≤ 1) (haM : ‖a‖ ≤ M) (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (hp : ∀ k, ‖star (w k * a - a * w k) * p k - star (w k * a - a * w k)‖ ≤ δ)
    (hcross : ∀ j k, j < k → ‖p j * w k - p j‖ ≤ δ ∧ ‖(p j * a) * w k - p j * a‖ ≤ δ)
    (j k : Fin N) :
    ‖star (w j * a - a * w j) * (w k * a - a * w k)‖ ≤
      (if j = k then 4 * M ^ 2 else 0) + 2 * M * (M + 2) * δ := by
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · have hle := norm_star_commutator_mul_le (hw j) (hw k) hδ
      (hp j) (hcross j k hjk).1 (hcross j k hjk).2
    simp only [hjk.ne, ↓reduceIte, zero_add]
    exact hle.trans (by gcongr)
  · simp only [↓reduceIte, CStarRing.norm_star_mul_self, ← sq]
    have hdj : ‖w j * a - a * w j‖ ≤ 2 * M :=
      (TauCeti.norm_commutator_le (w j) a).trans
        (by nlinarith [hw j, norm_nonneg a, norm_nonneg (w j)])
    calc ‖w j * a - a * w j‖ ^ 2
        ≤ (2 * M) ^ 2 := sq_le_sq' (by linarith [norm_nonneg (w j * a - a * w j)]) hdj
      _ = 4 * M ^ 2 := by ring
      _ ≤ 4 * M ^ 2 + 2 * M * (M + 2) * δ := le_add_of_nonneg_right (by positivity)
  · have hle := norm_star_commutator_mul_le (hw k) (hw j) hδ
      (hp k) (hcross k j hkj).1 (hcross k j hkj).2
    simp only [hkj.ne', ↓reduceIte, zero_add]
    rw [← norm_star, star_mul, star_star]
    exact hle.trans (by gcongr)

/-- C⋆-identity bound on the average commutator `(N : ℝ)⁻¹ • ∑ k, (w k * a - a * w k)` when the
chain `(w, p)` satisfies Arveson's approximate orthogonality relations. -/
private theorem norm_avg_commutator_lt {N : ℕ} {w p : Fin N → A} {a : A} {M ε : ℝ}
    (hw : ∀ k, ‖w k‖ ≤ 1) (haM : ‖a‖ ≤ M) (hM : 1 ≤ M) (hε : 0 < ε)
    (hN : 8 * M ^ 2 / ε ^ 2 < (N : ℝ))
    (hp : ∀ k, ‖star (w k * a - a * w k) * p k - star (w k * a - a * w k)‖ ≤
      ε ^ 2 / (8 * M * (M + 2)))
    (hcross : ∀ j k, j < k → ‖p j * w k - p j‖ ≤ ε ^ 2 / (8 * M * (M + 2)) ∧
      ‖(p j * a) * w k - p j * a‖ ≤ ε ^ 2 / (8 * M * (M + 2))) :
    ‖(N : ℝ)⁻¹ • ∑ k : Fin N, (w k * a - a * w k)‖ < ε := by
  let δ : ℝ := ε ^ 2 / (8 * M * (M + 2))
  have hδ : 0 < δ := by positivity
  have hN_pos : 0 < (N : ℝ) := lt_trans (by positivity) hN
  let d : Fin N → A := fun k => w k * a - a * w k
  have hD_sq : ‖∑ k : Fin N, d k‖ ^ 2 ≤
      (N : ℝ) * (4 * M ^ 2) + (N : ℝ) ^ 2 * (2 * M * (M + 2) * δ) := by
    rw [sq, ← CStarRing.norm_star_mul_self, star_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans <| (Finset.sum_le_sum fun j _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ =>
        norm_star_commutator_pair_le hw haM hM hδ.le hp hcross j k)).trans ?_
    simp [Finset.sum_add_distrib, sq, mul_assoc]
  refine lt_of_pow_lt_pow_left₀ 2 hε.le ?_
  rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_pow]
  have hN' : 8 * M ^ 2 < (N : ℝ) * ε ^ 2 := (div_lt_iff₀ (sq_pos_of_pos hε)).mp hN
  have hlt : 4 * M ^ 2 / (N : ℝ) < ε ^ 2 / 2 := (div_lt_iff₀ hN_pos).mpr (by linarith)
  calc ((N : ℝ)⁻¹) ^ 2 * ‖∑ k : Fin N, d k‖ ^ 2
      ≤ ((N : ℝ)⁻¹) ^ 2 * ((N : ℝ) * (4 * M ^ 2) + (N : ℝ) ^ 2 * (2 * M * (M + 2) * δ)) :=
        mul_le_mul_of_nonneg_left hD_sq (by positivity)
    _ = 4 * M ^ 2 / (N : ℝ) + ε ^ 2 / 4 := by dsimp only [δ]; field_simp [hN_pos.ne']; ring
    _ < ε ^ 2 := by linarith [sq_pos_of_pos hε]

variable [PartialOrder A] [StarOrderedRing A]

/-- Along the open-unit-ball restriction of `CStarAlgebra.approximateUnit S`, every positive
strict contraction `u₀` is eventually dominated by strict contractions. -/
private theorem eventually_le_and_norm_lt_one_ball (S : NonUnitalStarSubalgebra ℂ A)
    [IsClosed (S : Set A)] {u₀ : S} (hu₀ : 0 ≤ u₀) (hu₀_norm : ‖u₀‖ < 1) :
    ∀ᶠ y : S in (CStarAlgebra.isBasis_nonneg_sections S).filter ⊓ 𝓟 (Metric.ball 0 1),
      u₀ ≤ y ∧ ‖y‖ < 1 :=
  eventually_of_mem (((CStarAlgebra.isBasis_nonneg_sections S).hasBasis.inf_principal
    (Metric.ball 0 1)).mem_of_mem ⟨hu₀, hu₀_norm⟩) fun _ hy => ⟨hy.1, by simpa using hy.2⟩

/-- Single step in the inductive construction of Arveson's chain: given `p : Fin n → S`, choose a
strict contraction `w_new ≥ u₀` right-approximating `p` and `p * f`, and then choose `p_new`
right-approximating the adjoint commutators of `w_new` with `f`. -/
private theorem exists_quasicentral_step (S : NonUnitalStarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (hmul : ∀ a : A, ∀ x ∈ S, a * x ∈ S)
    {u₀ : S} (hu₀ : 0 ≤ u₀) (hu₀_norm : ‖u₀‖ < 1)
    {m n : ℕ} (f : Fin m → A) (p : Fin n → S) {δ : ℝ} (hδ : 0 < δ) :
    ∃ w_new p_new : S, (u₀ ≤ w_new ∧ ‖w_new‖ < 1) ∧
      (∀ j : Fin n, ‖(p j : A) * (w_new : A) - (p j : A)‖ ≤ δ ∧
        ∀ i, ‖((p j : A) * f i) * (w_new : A) - (p j : A) * f i‖ ≤ δ) ∧
      ∀ i, ‖star ((w_new : A) * f i - f i * (w_new : A)) * (p_new : A) -
        star ((w_new : A) * f i - f i * (w_new : A))‖ ≤ δ := by
  let l₀ : Filter S := (CStarAlgebra.isBasis_nonneg_sections S).filter ⊓ 𝓟 (Metric.ball 0 1)
  have hl₀ : l₀.IsIncreasingApproximateUnit :=
    TauCeti.CStarAlgebra.isIncreasingApproximateUnit_ball S
  have := hl₀.neBot
  have hu₀_mem := eventually_le_and_norm_lt_one_ball S hu₀ hu₀_norm
  have hp_mem : ∀ᶠ y : S in l₀, ∀ j : Fin n, ‖(p j : A) * (y : A) - (p j : A)‖ ≤ δ ∧
      ∀ i, ‖((p j : A) * f i) * (y : A) - (p j : A) * f i‖ ≤ δ :=
    eventually_all.mpr fun j =>
      ((tendsto_iff_norm_sub_tendsto_zero.mp (hl₀.tendsto_mul_left (p j))).eventually
        (ge_mem_nhds hδ)).and <| eventually_all.mpr fun i => by
        let pa : S :=
          ⟨(p j : A) * f i, StarMemClass.mul_mem_right_of_mul_mem_left hmul (f i) (p j).property⟩
        exact (tendsto_iff_norm_sub_tendsto_zero.mp (hl₀.tendsto_mul_left pa)).eventually
          (ge_mem_nhds hδ)
  obtain ⟨w_new, hw_u₀, hw_p⟩ := (hu₀_mem.and hp_mem).exists
  have h_pnew : ∀ᶠ q : S in CStarAlgebra.approximateUnit S, ∀ i,
      ‖star ((w_new : A) * f i - f i * (w_new : A)) * (q : A) -
        star ((w_new : A) * f i - f i * (w_new : A))‖ ≤ δ :=
    eventually_all.mpr fun i => by
      let sd : S := star ⟨(w_new : A) * f i - f i * (w_new : A),
        sub_mem (StarMemClass.mul_mem_right_of_mul_mem_left hmul (f i) w_new.property)
          (hmul (f i) _ w_new.property)⟩
      exact (tendsto_iff_norm_sub_tendsto_zero.mp
        ((CStarAlgebra.increasingApproximateUnit S).tendsto_mul_left sd)).eventually
        (ge_mem_nhds hδ)
  obtain ⟨p_new, hp_new⟩ := h_pnew.exists
  exact ⟨w_new, p_new, hw_u₀, hw_p, hp_new⟩

/-- Inductive selection of an `n`-element chain `w, p : Fin n → S`, where `w` consists of strict
contractions in `S` above `u₀` and `p` supplies auxiliary approximation witnesses whose commutators
with `f` satisfy Arveson's approximate orthogonality relations. -/
private theorem exists_quasicentral_chain (S : NonUnitalStarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (hmul : ∀ a : A, ∀ x ∈ S, a * x ∈ S)
    {u₀ : S} (hu₀ : 0 ≤ u₀) (hu₀_norm : ‖u₀‖ < 1)
    {m : ℕ} (f : Fin m → A) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∃ w p : Fin n → S,
      (∀ k, u₀ ≤ w k ∧ ‖w k‖ < 1) ∧
      (∀ k i, ‖star ((w k : A) * f i - f i * (w k : A)) * (p k : A) -
        star ((w k : A) * f i - f i * (w k : A))‖ ≤ δ) ∧
      (∀ j k, j < k → ‖(p j : A) * (w k : A) - (p j : A)‖ ≤ δ ∧
        ∀ i, ‖((p j : A) * f i) * (w k : A) - (p j : A) * f i‖ ≤ δ) := by
  induction n with
  | zero =>
    exact ⟨Fin.elim0, Fin.elim0, fun k => Fin.elim0 k, fun k => Fin.elim0 k, fun j => Fin.elim0 j⟩
  | succ n ih =>
    obtain ⟨w, p, hw_u₀, hp_F, hcross⟩ := ih
    obtain ⟨w_new, p_new, hw_new_u₀, hw_new_p, hp_new⟩ :=
      exists_quasicentral_step S hmul hu₀ hu₀_norm f p hδ
    refine ⟨Fin.snoc w w_new, Fin.snoc p p_new,
      Fin.lastCases (by simpa using hw_new_u₀) (fun k => by simpa using hw_u₀ k),
      Fin.lastCases (by simpa using hp_new) (fun k => by simpa using hp_F k), ?_⟩
    intro j k hjk
    refine k.lastCases (fun hj => ?_) (fun k₀ hj => ?_) hjk
    · refine j.lastCases (fun hlt => (lt_irrefl _ hlt).elim) (fun j₀ _ => ?_) hj
      simpa using hw_new_p j₀
    · refine j.lastCases (fun hlt => ((Fin.le_last _).not_gt hlt).elim) (fun j₀ hj₀ => ?_) hj
      simpa using hcross j₀ k₀ (Fin.castSucc_lt_castSucc_iff.mp hj₀)

/-- Quantitative finite-family commutator Arveson lemma: for any `u₀ ∈ S` (`0 ≤ u₀`, `‖u₀‖ < 1`),
finite family `f : Fin m → A`, and `ε > 0`, some `e ∈ S` with `u₀ ≤ e` and `‖e‖ < 1` commutes with
`f` up to `ε`. -/
private theorem exists_quasicentral_fin_approx (S : NonUnitalStarSubalgebra ℂ A)
    [IsClosed (S : Set A)] (hmul : ∀ a : A, ∀ x ∈ S, a * x ∈ S)
    {u₀ : S} (hu₀ : 0 ≤ u₀) (hu₀_norm : ‖u₀‖ < 1)
    {m : ℕ} (f : Fin m → A) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : S, u₀ ≤ e ∧ ‖e‖ < 1 ∧
      ∀ i, ‖(e : A) * f i - f i * (e : A)‖ < ε := by
  let M : ℝ := 1 + ∑ i : Fin m, ‖f i‖
  have hM : 1 ≤ M := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  obtain ⟨N, hN⟩ := exists_nat_gt (8 * M ^ 2 / ε ^ 2)
  have hN_pos : 0 < (N : ℝ) := lt_trans (by positivity) hN
  let δ : ℝ := ε ^ 2 / (8 * M * (M + 2))
  have hδ : 0 < δ := by positivity
  obtain ⟨w, p, hw_u₀, hp_F, hcross⟩ :=
    exists_quasicentral_chain S hmul hu₀ hu₀_norm f hδ N
  let e : S := (N : ℝ)⁻¹ • ∑ k : Fin N, w k
  have he_sum : e = ∑ k : Fin N, (N : ℝ)⁻¹ • w k := Finset.smul_sum
  have hsum_w : ∑ _k : Fin N, (N : ℝ)⁻¹ = 1 := by simp [mul_inv_cancel₀ hN_pos.ne']
  have he_u₀ : u₀ ≤ e := by
    rw [he_sum]
    exact (convex_Ici u₀).sum_mem (fun _ _ => by positivity) hsum_w fun k _ => (hw_u₀ k).1
  have he_norm : ‖e‖ < 1 := by
    have hmem : e ∈ Metric.ball (0 : S) 1 := by
      rw [he_sum]
      exact (convex_ball (0 : S) 1).sum_mem (fun _ _ => by positivity) hsum_w fun k _ => by
        simpa [Metric.mem_ball, dist_zero_right] using (hw_u₀ k).2
    simpa [Metric.mem_ball, dist_zero_right] using hmem
  refine ⟨e, he_u₀, he_norm, fun i => ?_⟩
  have hfiM : ‖f i‖ ≤ M :=
    (Finset.single_le_sum (f := fun j => ‖f j‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)).trans (by dsimp only [M]; linarith)
  have he_comm : (e : A) * f i - f i * (e : A) =
      (N : ℝ)⁻¹ • ∑ k : Fin N, ((w k : A) * f i - f i * (w k : A)) := by
    dsimp only [e]
    push_cast
    simp [smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum,
      Finset.sum_sub_distrib, smul_sub]
  rw [he_comm]
  exact norm_avg_commutator_lt (fun k => (hw_u₀ k).2.le) hfiM hM hε hN
    (fun k => hp_F k i) (fun j k hjk => ⟨(hcross j k hjk).1, (hcross j k hjk).2 i⟩)

/-- Quantitative finite-family **Arveson lemma** for closed star ideals: given a strict positive
contraction `u₀ ∈ S`, finite families `f : ι → A` and `g : κ → S`, and `ε > 0`, some strict
contraction `e ∈ S` with `u₀ ≤ e` simultaneously left-approximates `g` and commutes with `f` within
`ε`. -/
theorem exists_quasicentral_approx (S : NonUnitalStarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (hmul : ∀ a : A, ∀ x ∈ S, a * x ∈ S)
    {u₀ : S} (hu₀ : 0 ≤ u₀) (hu₀_norm : ‖u₀‖ < 1)
    {ι κ : Type*} [Finite ι] [Finite κ] (f : ι → A) (g : κ → S) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : S, u₀ ≤ e ∧ ‖e‖ < 1 ∧
      (∀ j, ‖e * g j - g j‖ < ε) ∧
      (∀ i, ‖(e : A) * f i - f i * (e : A)‖ < ε) := by
  let l₀ : Filter S := (CStarAlgebra.isBasis_nonneg_sections S).filter ⊓ 𝓟 (Metric.ball 0 1)
  have hl₀ : l₀.IsIncreasingApproximateUnit :=
    TauCeti.CStarAlgebra.isIncreasingApproximateUnit_ball S
  have := hl₀.neBot
  have hu₀_mem := eventually_le_and_norm_lt_one_ball S hu₀ hu₀_norm
  have hg_mem : ∀ᶠ y : S in l₀, ∀ j : κ, ‖y * g j - g j‖ < ε ^ 2 / (‖g j‖ + 1) :=
    eventually_all.mpr fun j =>
      (tendsto_iff_norm_sub_tendsto_zero.mp (hl₀.tendsto_mul_right (g j))).eventually
        (gt_mem_nhds (by positivity))
  obtain ⟨u₁, ⟨hu₀_u₁, hu₁_norm⟩, hu₁_g⟩ := (hu₀_mem.and hg_mem).exists
  have hu₁_0 : 0 ≤ u₁ := hu₀.trans hu₀_u₁
  let equiv := Finite.equivFin ι
  obtain ⟨e, hu₁_e, he_norm, he_f⟩ :=
    exists_quasicentral_fin_approx S hmul hu₁_0 hu₁_norm (f ∘ equiv.symm) hε
  refine ⟨e, hu₀_u₁.trans hu₁_e, he_norm, fun j => ?_, fun i => ?_⟩
  · refine lt_of_pow_lt_pow_left₀ 2 hε.le ?_
    have hgj_pos : 0 < ‖g j‖ + 1 := by positivity
    calc ‖e * g j - g j‖ ^ 2
        ≤ ‖g j‖ * ‖u₁ * g j - g j‖ :=
          TauCeti.CStarAlgebra.norm_mul_sub_sq_le_of_le (hu₁_0.trans hu₁_e) he_norm.le hu₁_e (g j)
      _ ≤ ‖g j‖ * (ε ^ 2 / (‖g j‖ + 1)) :=
          mul_le_mul_of_nonneg_left (hu₁_g j).le (norm_nonneg _)
      _ < (‖g j‖ + 1) * (ε ^ 2 / (‖g j‖ + 1)) :=
          mul_lt_mul_of_pos_right (lt_add_one _) (by positivity)
      _ = ε ^ 2 := mul_div_cancel₀ _ hgj_pos.ne'
  · simpa [equiv] using he_f (equiv i)

/-- **Arveson's theorem** for closed star ideals: every closed `NonUnitalStarSubalgebra ℂ A` closed
under left multiplication by `A` admits an increasing approximate unit `l` of strict contractions
eventually dominating any strict positive contraction `u₀` and quasicentral in `A`, meaning
`(e : A) * a - a * (e : A) → 0` along `l` for every `a : A`. -/
theorem exists_quasicentral_isIncreasingApproximateUnit
    (S : NonUnitalStarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (hmul : ∀ a : A, ∀ x ∈ S, a * x ∈ S) :
    ∃ l : Filter S, l.IsIncreasingApproximateUnit ∧
      (∀ u₀ : S, 0 ≤ u₀ → ‖u₀‖ < 1 → ∀ᶠ e in l, u₀ ≤ e ∧ ‖e‖ < 1) ∧
      ∀ a : A, Tendsto (fun e : S => (e : A) * a - a * (e : A)) l (𝓝 0) := by
  let Idx := {u₀ : S // 0 ≤ u₀ ∧ ‖u₀‖ < 1} × (Σ m : ℕ, Fin m → A) × {ε : ℝ // 0 < ε}
  let s : Idx → Set S := fun ⟨u₀, ⟨m, f⟩, ε⟩ =>
    {e : S | (u₀ : S) ≤ e ∧ ‖e‖ < 1 ∧ ∀ i : Fin m, ‖(e : A) * f i - f i * (e : A)‖ < (ε : ℝ)}
  have hbasis : IsBasis (fun _ : Idx => True) s := by
    refine ⟨⟨⟨⟨0, le_rfl, by simp⟩, ⟨0, Fin.elim0⟩, ⟨1, zero_lt_one⟩⟩, trivial⟩, ?_⟩
    rintro ⟨⟨u₁, hu₁⟩, ⟨m₁, f₁⟩, ⟨ε₁, hε₁⟩⟩ ⟨⟨u₂, hu₂⟩, ⟨m₂, f₂⟩, ⟨ε₂, hε₂⟩⟩ - -
    obtain ⟨u₃, ⟨hu₃_0, hu₃_1⟩, h13, h23⟩ :=
      CStarAlgebra.directedOn_nonneg_ball u₁ ⟨hu₁.1, by simpa using hu₁.2⟩
        u₂ ⟨hu₂.1, by simpa using hu₂.2⟩
    refine ⟨⟨⟨u₃, hu₃_0, by simpa using hu₃_1⟩, ⟨m₁ + m₂, Fin.addCases f₁ f₂⟩,
      ⟨min ε₁ ε₂, lt_min hε₁ hε₂⟩⟩, trivial,
      fun e ⟨heu₃, he1, heF⟩ => ⟨⟨h13.trans heu₃, he1, fun i => ?_⟩,
        ⟨h23.trans heu₃, he1, fun i => ?_⟩⟩⟩
    · simpa using (heF (Fin.castAdd m₂ i)).trans_le (min_le_left _ _)
    · simpa using (heF (Fin.natAdd m₁ i)).trans_le (min_le_right _ _)
  let l : Filter S := hbasis.filter
  have : l.NeBot := hbasis.hasBasis.neBot_iff.mpr fun {idx} _ => by
    obtain ⟨⟨u₀, hu₀_0, hu₀_1⟩, ⟨m, f⟩, ⟨ε, hε⟩⟩ := idx
    obtain ⟨e, he_u₀, he_norm, -, he_F⟩ :=
      exists_quasicentral_approx S hmul hu₀_0 hu₀_1 f Fin.elim0 hε
    exact ⟨e, he_u₀, he_norm, he_F⟩
  have hle : l ≤ CStarAlgebra.approximateUnit S := by
    rw [hbasis.hasBasis.le_basis_iff (CStarAlgebra.hasBasis_approximateUnit S)]
    intro u₀ hu₀
    exact ⟨⟨⟨u₀, hu₀⟩, ⟨0, Fin.elim0⟩, ⟨1, zero_lt_one⟩⟩, trivial,
      fun _ ⟨heu₀, he1, _⟩ => ⟨heu₀, by simpa using he1.le⟩⟩
  refine ⟨l, (CStarAlgebra.increasingApproximateUnit S).mono hle, fun u₀ hu₀_0 hu₀_1 => ?_,
    fun a => ?_⟩
  · exact eventually_of_mem
      (hbasis.hasBasis.mem_of_mem (i := ⟨⟨u₀, hu₀_0, hu₀_1⟩, ⟨0, Fin.elim0⟩, ⟨1, zero_lt_one⟩⟩)
        trivial)
      fun _ ⟨heu₀, he1, _⟩ => ⟨heu₀, he1⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    rw [hbasis.hasBasis.tendsto_iff Metric.nhds_basis_ball]
    intro ε hε
    refine ⟨⟨⟨0, le_rfl, by simp⟩, ⟨1, fun _ => a⟩, ⟨ε, hε⟩⟩, trivial, fun _ ⟨_, _, heF⟩ => ?_⟩
    simpa using heF 0

/-- Separable sequential form of Arveson's theorem for closed star ideals: when `A` is separable,
`S` admits a monotone sequence `u : ℕ → S` of nonnegative strict contractions forming a
quasicentral increasing approximate unit of `S`. -/
theorem exists_seq_quasicentral_isIncreasingApproximateUnit [TopologicalSpace.SeparableSpace A]
    (S : NonUnitalStarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (hmul : ∀ a : A, ∀ x ∈ S, a * x ∈ S) :
    ∃ u : ℕ → S, Monotone u ∧ (∀ n, 0 ≤ u n) ∧ (∀ n, ‖u n‖ < 1) ∧
      (atTop.map u).IsIncreasingApproximateUnit ∧
      ∀ a : A, Tendsto (fun n => (u n : A) * a - a * (u n : A)) atTop (𝓝 0) := by
  let gSeq : ℕ → S := TopologicalSpace.denseSeq S
  let fSeq : ℕ → A := TopologicalSpace.denseSeq A
  let Elem := {e : S // 0 ≤ e ∧ ‖e‖ < 1}
  let stepEx (n : ℕ) (x : Elem) := exists_quasicentral_approx S hmul x.property.1 x.property.2
    (fun i : Fin (n + 1) => fSeq i) (fun i : Fin (n + 1) => gSeq i)
    (Nat.one_div_pos_of_nat (n := n))
  let step (n : ℕ) (x : Elem) : Elem :=
    ⟨(stepEx n x).choose, x.property.1.trans (stepEx n x).choose_spec.1,
      (stepEx n x).choose_spec.2.1⟩
  have hstep_spec (n : ℕ) (x : Elem) : x.val ≤ (step n x).val ∧
      (∀ k ≤ n, ‖(step n x).val * gSeq k - gSeq k‖ < 1 / ((n : ℝ) + 1)) ∧
      (∀ k ≤ n, ‖((step n x).val : A) * fSeq k - fSeq k * ((step n x).val : A)‖ <
        1 / ((n : ℝ) + 1)) := by
    have hval : (step n x).val = (stepEx n x).choose := rfl
    rw [hval]
    have h := (stepEx n x).choose_spec
    exact ⟨h.1, fun k hk => h.2.2.1 ⟨k, Nat.lt_succ_of_le hk⟩,
      fun k hk => h.2.2.2 ⟨k, Nat.lt_succ_of_le hk⟩⟩
  let recSeq : ℕ → Elem := Nat.rec ⟨0, le_rfl, by simp⟩ step
  have hrec_succ (n : ℕ) : recSeq (n + 1) = step n (recSeq n) := rfl
  let u : ℕ → S := fun n => (recSeq (n + 1)).val
  have hu_step (n : ℕ) : (recSeq n).val ≤ u n ∧
      (∀ k ≤ n, ‖u n * gSeq k - gSeq k‖ < 1 / ((n : ℝ) + 1)) ∧
      (∀ k ≤ n, ‖(u n : A) * fSeq k - fSeq k * (u n : A)‖ < 1 / ((n : ℝ) + 1)) := by
    have hu_eq : u n = (step n (recSeq n)).val := congrArg Subtype.val (hrec_succ n)
    rw [hu_eq]
    exact hstep_spec n (recSeq n)
  have hu_approx : (atTop.map u).IsIncreasingApproximateUnit := by
    refine Filter.IsIncreasingApproximateUnit.of_tendsto_mul_right_of_dense
      (TopologicalSpace.denseRange_denseSeq S) ?_
      (eventually_map.mpr (.of_forall fun n => (recSeq (n + 1)).property.1))
      (eventually_map.mpr (.of_forall fun n => (recSeq (n + 1)).property.2.le))
    rintro _ ⟨k, rfl⟩
    rw [tendsto_map'_iff]
    exact TauCeti.tendsto_of_eventually_norm_sub_le_inv
      (eventually_atTop.mpr ⟨k, fun n hn => ((hu_step n).2.1 k hn).le⟩)
  have hu_comm (a : A) : Tendsto (fun n => (u n : A) * a - a * (u n : A)) atTop (𝓝 0) := by
    refine tendsto_map'_iff.mp <| TauCeti.tendsto_commutator_of_dense (C := 1)
      (eventually_map.mpr (.of_forall fun n => by simpa using (recSeq (n + 1)).property.2.le))
      (TopologicalSpace.denseRange_denseSeq A) ?_ a
    rintro _ ⟨k, rfl⟩
    rw [tendsto_map'_iff]
    exact TauCeti.tendsto_of_eventually_norm_sub_le_inv (eventually_atTop.mpr ⟨k, fun n hn => by
      simpa [Function.comp_def, sub_zero] using ((hu_step n).2.2 k hn).le⟩)
  exact ⟨u, monotone_nat_of_le_succ fun n => (hu_step (n + 1)).1,
    fun n => (recSeq (n + 1)).property.1, fun n => (recSeq (n + 1)).property.2, hu_approx, hu_comm⟩

end Arveson

end NonUnitalStarSubalgebra

namespace TwoSidedIdeal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (I : TwoSidedIdeal A) [IsClosed (I : Set A)]

/-- **Arveson's theorem:** every closed two-sided ideal `I` of a C⋆-algebra `A` admits a
quasicentral increasing approximate unit `l : Filter I` of strict contractions eventually
dominating any strict positive contraction `u₀`, meaning `l.IsIncreasingApproximateUnit` and
`(e : A) * a - a * (e : A) → 0` along `l` for every `a : A`. -/
theorem exists_quasicentral_isIncreasingApproximateUnit :
    ∃ l : Filter I, l.IsIncreasingApproximateUnit ∧
      (∀ u₀ : I, 0 ≤ u₀ → ‖u₀‖ < 1 → ∀ᶠ e in l, u₀ ≤ e ∧ ‖e‖ < 1) ∧
      ∀ a : A, Tendsto (fun e : I => (e : A) * a - a * (e : A)) l (𝓝 0) := by
  obtain ⟨lS, hlS, hstrict, hcomm⟩ :=
    I.toNonUnitalStarSubalgebra.exists_quasicentral_isIncreasingApproximateUnit
      I.mul_mem_toNonUnitalStarSubalgebra
  let φ := I.toNonUnitalStarSubalgebraEquiv.symm
  refine ⟨lS.map φ, hlS.map φ φ.surjective, fun u₀ hu₀_0 hu₀_1 => ?_, fun a => ?_⟩
  · rw [eventually_map]
    refine (hstrict (I.toNonUnitalStarSubalgebraEquiv u₀)
      (I.toNonUnitalStarSubalgebraEquiv_nonneg_iff.mpr hu₀_0)
      ((I.norm_toNonUnitalStarSubalgebraEquiv_apply u₀).symm ▸ hu₀_1)).mono fun e ⟨hle, hnorm⟩ =>
        ⟨I.le_toNonUnitalStarSubalgebraEquiv_symm_iff.mpr hle,
          (I.norm_toNonUnitalStarSubalgebraEquiv_symm_apply e).trans_lt hnorm⟩
  · rw [tendsto_map'_iff]
    exact (hcomm a).congr fun e => by
      simp only [Function.comp_apply, φ, I.coe_toNonUnitalStarSubalgebraEquiv_symm_apply]

/-- Quantitative finite-family **Arveson lemma** for closed two-sided ideals: given a strict
positive contraction `u₀ ∈ I`, finite families `f : ι → A` and `g : κ → I`, and `ε > 0`, some
strict contraction `e ∈ I` with `u₀ ≤ e` simultaneously left-approximates `g` and commutes with `f`
within `ε`. -/
theorem exists_quasicentral_approx {u₀ : I} (hu₀ : 0 ≤ u₀) (hu₀_norm : ‖u₀‖ < 1)
    {ι κ : Type*} [Finite ι] [Finite κ] (f : ι → A) (g : κ → I) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : I, u₀ ≤ e ∧ ‖e‖ < 1 ∧
      (∀ j, ‖e * g j - g j‖ < ε) ∧
      (∀ i, ‖(e : A) * f i - f i * (e : A)‖ < ε) := by
  let ψ := I.toNonUnitalStarSubalgebraEquiv
  obtain ⟨eS, heS_u₀, heS_norm, heS_g, heS_f⟩ :=
    I.toNonUnitalStarSubalgebra.exists_quasicentral_approx I.mul_mem_toNonUnitalStarSubalgebra
      (I.toNonUnitalStarSubalgebraEquiv_nonneg_iff.mpr hu₀)
      ((I.norm_toNonUnitalStarSubalgebraEquiv_apply u₀).symm ▸ hu₀_norm)
      f (fun j => ψ (g j)) hε
  refine ⟨ψ.symm eS, I.le_toNonUnitalStarSubalgebraEquiv_symm_iff.mpr heS_u₀,
    (I.norm_toNonUnitalStarSubalgebraEquiv_symm_apply eS).trans_lt heS_norm,
    fun j => ?_, fun i => ?_⟩
  · have heq : ψ.symm eS * g j - g j = ψ.symm (eS * ψ (g j) - ψ (g j)) := by simp
    rw [heq, I.norm_toNonUnitalStarSubalgebraEquiv_symm_apply]
    exact heS_g j
  · simpa only [ψ, I.coe_toNonUnitalStarSubalgebraEquiv_symm_apply] using heS_f i

/-- Separable sequential form of **Arveson's theorem:** when `A` is separable, every closed
two-sided ideal `I` of `A` admits a monotone sequence `u : ℕ → I` of nonnegative strict
contractions forming a quasicentral increasing approximate unit of `I`. -/
theorem exists_seq_quasicentral_isIncreasingApproximateUnit [TopologicalSpace.SeparableSpace A] :
    ∃ u : ℕ → I, Monotone u ∧ (∀ n, 0 ≤ u n) ∧ (∀ n, ‖u n‖ < 1) ∧
      (atTop.map u).IsIncreasingApproximateUnit ∧
      ∀ a : A, Tendsto (fun n => (u n : A) * a - a * (u n : A)) atTop (𝓝 0) := by
  obtain ⟨uS, huS_mono, huS_0, huS_1, huS_approx, huS_comm⟩ :=
    I.toNonUnitalStarSubalgebra.exists_seq_quasicentral_isIncreasingApproximateUnit
      I.mul_mem_toNonUnitalStarSubalgebra
  let φ := I.toNonUnitalStarSubalgebraEquiv.symm
  let u : ℕ → I := fun n => φ (uS n)
  refine ⟨u, fun _ _ hmn => I.toNonUnitalStarSubalgebraEquiv_symm_le_iff.mpr (huS_mono hmn),
    fun n => I.toNonUnitalStarSubalgebraEquiv_symm_nonneg_iff.mpr (huS_0 n),
    fun n => (I.norm_toNonUnitalStarSubalgebraEquiv_symm_apply (uS n)).trans_lt (huS_1 n),
    ?_, fun a => (huS_comm a).congr fun n => ?_⟩
  · have heq : atTop.map u = (atTop.map uS).map φ := (Filter.map_map).symm
    exact heq ▸ huS_approx.map φ φ.surjective
  · simp only [u, φ, I.coe_toNonUnitalStarSubalgebraEquiv_symm_apply]

end TwoSidedIdeal
