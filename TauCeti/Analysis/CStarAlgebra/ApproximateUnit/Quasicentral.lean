/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnit.Basic
public import TauCeti.Analysis.CStarAlgebra.Ideal
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Quasicentral approximate units in closed ideals of C⋆-algebras

An approximate unit `l` of a closed two-sided ideal `I` in a C⋆-algebra `A` is *quasicentral* if
`‖(e : A) * a - a * (e : A)‖ → 0` along `l` for every `a : A`. Arveson proved that every closed
two-sided ideal of a C⋆-algebra admits a quasicentral increasing approximate unit.

Naive functional-calculus roots of a single positive element in `I` need not be quasicentral (for
instance, on `K(ℓ²)` a rank-one perturbation can obstruct asymptotic commutation with a shift), so
convex averaging is essential. Rather than invoking Hahn–Banach separation on the strict topology,
we give a direct quantitative C⋆-norm proof: given `u₀ ∈ S` (`0 ≤ u₀`, `‖u₀‖ < 1`), finitely many
elements `f : Fin m → A` and `ε > 0`, we inductively select `w₀, …, w_{N-1} ∈ S` and auxiliary
elements `p₀, …, p_{N-1} ∈ S` in the unit ball so that `p_j` right-approximates
`star (w_j * a - a * w_j)` while subsequent `w_k` (`k > j`) right-approximate both `p_j` and
`p_j * a`. Writing `d_k = w_k * a - a * w_k`, the identity
`p_j * d_k = (p_j * w_k - p_j) * a - ((p_j * a) * w_k - p_j * a)` makes every off-diagonal inner
product `star d_j * d_k` small, so `‖∑_k d_k‖ ^ 2 = ‖∑_{j,k} star d_j * d_k‖` grows linearly in `N`
and the average `e = N⁻¹ • ∑_k w_k` satisfies `‖e * a - a * e‖ < ε` for all `a = f i`.

## Main results

* `TauCeti.CStarAlgebra.tendsto_commutator_lift'_convexHull` and
  `TauCeti.CStarAlgebra.tendsto_commutator_map_of_surjective`: asymptotic centrality is preserved
  by real convexification of the filter and by surjective star-algebra homomorphisms.
* `NonUnitalStarSubalgebra.exists_quasicentral_increasingApproximateUnit` and
  `TwoSidedIdeal.exists_quasicentral_increasingApproximateUnit`: **Arveson's theorem** for any
  closed star subalgebra closed under left multiplication by `A`, and for any closed two-sided
  ideal `I : TwoSidedIdeal A`.
* `NonUnitalStarSubalgebra.exists_seq_quasicentral_increasingApproximateUnit` and
  `TwoSidedIdeal.exists_seq_quasicentral_increasingApproximateUnit`: when `A` is separable, there
  is a monotone sequence `u : ℕ → I` of nonnegative strict contractions forming a quasicentral
  increasing approximate unit of `I`.

## References

* W. Arveson, *Notes on extensions of C*-algebras*, Duke Math. J. 44 (1977), 329–355.
* B. Blackadar, *Operator Algebras*, II.4.3.
-/

public section

open Filter Topology
open scoped CStarAlgebra

namespace TauCeti.CStarAlgebra

/-- Real convexification `l.lift' (convexHull ℝ)` preserves asymptotic centrality of any real-linear
map into a seminormed ring over `ℝ`. -/
theorem tendsto_commutator_lift'_convexHull {B A F : Type*} [AddCommMonoid B] [Module ℝ B]
    [SeminormedRing A] [NormedSpace ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    [FunLike F B A] [LinearMapClass F ℝ B A]
    {l : Filter B} (f : F) {a : A}
    (h : Tendsto (fun e => f e * a - a * f e) l (𝓝 0)) :
    Tendsto (fun e => f e * a - a * f e) (l.lift' (convexHull ℝ)) (𝓝 0) := by
  rw [Metric.tendsto_nhds] at h ⊢
  intro ε hε
  let T : B →ₗ[ℝ] A :=
    { toFun := fun e => f e * a - a * f e
      map_add' := fun x y => by
        simp only [map_add, add_mul, mul_add]
        abel
      map_smul' := fun r x => by
        simp only [map_smul, smul_mul_assoc, mul_smul_comm, smul_sub, RingHom.id_apply] }
  have hball : Convex ℝ {e : B | dist (T e) 0 < ε} := (convex_ball (0 : A) ε).linear_preimage T
  exact eventually_of_mem (mem_lift' (h ε hε)) fun x hx => convexHull_min subset_rfl hball hx

/-- Pushing a filter forward along a map into a normed ring preserves asymptotic centrality along
any surjective continuous multiplicative homomorphism on the ambient ring. -/
theorem tendsto_commutator_map_of_surjective {S A B F G : Type*}
    [NonUnitalNormedRing A] [NonUnitalNormedRing B]
    [FunLike F S A] [FunLike G A B] [NonUnitalRingHomClass G A B]
    {l : Filter S} (f : F) (π : G) (hπ_cont : Continuous π) (hπ_surj : Function.Surjective π)
    (h : ∀ a : A, Tendsto (fun e => f e * a - a * f e) l (𝓝 0)) (b : B) :
    Tendsto (fun e => π (f e) * b - b * π (f e)) l (𝓝 0) := by
  obtain ⟨a, rfl⟩ := hπ_surj b
  have hlim := (hπ_cont.tendsto 0).comp (h a)
  rw [map_zero] at hlim
  exact hlim.congr fun e => by simp [map_sub, map_mul]

end TauCeti.CStarAlgebra

namespace NonUnitalStarSubalgebra

section Arveson

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- A star subalgebra closed under left multiplication by `A` is also closed under right
multiplication by `A`, via `x * a = star (star a * star x)`. -/
private theorem mul_mem_right_of_mul_mem_left {S : NonUnitalStarSubalgebra ℂ A}
    (hmul : ∀ (a : A) {x : A}, x ∈ S → a * x ∈ S) {x : A} (hx : x ∈ S) (a : A) :
    x * a ∈ S := by
  simpa only [star_mul, star_star] using star_mem (hmul (star a) (star_mem hx))

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
  have hd₁ : ‖star d₁‖ ≤ 2 * ‖a‖ := by
    rw [norm_star]
    calc ‖w₁ * a - a * w₁‖ ≤ ‖w₁ * a‖ + ‖a * w₁‖ := norm_sub_le _ _
      _ ≤ ‖w₁‖ * ‖a‖ + ‖a‖ * ‖w₁‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 1 * ‖a‖ + ‖a‖ * 1 := add_le_add (mul_le_mul_of_nonneg_right hw₁ (norm_nonneg a))
          (mul_le_mul_of_nonneg_left hw₁ (norm_nonneg a))
      _ = 2 * ‖a‖ := by ring
  have hd₂ : ‖d₂‖ ≤ 2 * ‖a‖ := by
    calc ‖w₂ * a - a * w₂‖ ≤ ‖w₂ * a‖ + ‖a * w₂‖ := norm_sub_le _ _
      _ ≤ ‖w₂‖ * ‖a‖ + ‖a‖ * ‖w₂‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 1 * ‖a‖ + ‖a‖ * 1 := add_le_add (mul_le_mul_of_nonneg_right hw₂ (norm_nonneg a))
          (mul_le_mul_of_nonneg_left hw₂ (norm_nonneg a))
      _ = 2 * ‖a‖ := by ring
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
    have hdj : ‖w j * a - a * w j‖ ≤ 2 * M := by
      calc ‖w j * a - a * w j‖ ≤ ‖w j‖ * ‖a‖ + ‖a‖ * ‖w j‖ :=
            (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        _ ≤ 1 * M + M * 1 := add_le_add (mul_le_mul (hw j) haM (norm_nonneg _) zero_le_one)
            (mul_le_mul haM (hw j) (norm_nonneg _) (by positivity))
        _ = 2 * M := by ring
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

/-- Restricting `CStarAlgebra.approximateUnit B` to the open unit ball preserves the increasing
approximate unit property and ensures every member has norm strictly less than `1`. -/
private theorem increasingApproximateUnit_ball (B : Type*) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] :
    ((CStarAlgebra.isBasis_nonneg_sections B).filter ⊓
      𝓟 (Metric.ball 0 1)).IsIncreasingApproximateUnit := by
  let l₀ : Filter B := (CStarAlgebra.isBasis_nonneg_sections B).filter ⊓ 𝓟 (Metric.ball 0 1)
  have hbasis := (CStarAlgebra.isBasis_nonneg_sections B).hasBasis.inf_principal (Metric.ball 0 1)
  have : l₀.NeBot := hbasis.neBot_iff.mpr fun ⟨_, hx⟩ => ⟨_, ⟨le_rfl, by simpa using hx⟩⟩
  have hle : l₀ ≤ CStarAlgebra.approximateUnit B :=
    inf_le_inf_left _ (principal_mono.mpr Metric.ball_subset_closedBall)
  exact (CStarAlgebra.increasingApproximateUnit B).mono hle

/-- Single step in the inductive construction of Arveson's chain: given `p : Fin n → S`, choose a
strict contraction `w_new ≥ u₀` right-approximating `p` and `p * f`, and then choose `p_new`
right-approximating the adjoint commutators of `w_new` with `f`. -/
private theorem exists_quasicentral_step (S : NonUnitalStarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (hmul : ∀ (a : A) {x : A}, x ∈ S → a * x ∈ S)
    {u₀ : S} (hu₀ : 0 ≤ u₀) (hu₀_norm : ‖u₀‖ < 1)
    {m l n : ℕ} (f : Fin m → A) (g : Fin l → S) (p : Fin n → S)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ w_new p_new : S, (u₀ ≤ w_new ∧ ‖w_new‖ < 1) ∧
      (∀ i, ‖w_new * g i - g i‖ < ε) ∧
      (∀ j : Fin n, ‖(p j : A) * (w_new : A) - (p j : A)‖ ≤ δ ∧
        ∀ i, ‖((p j : A) * f i) * (w_new : A) - (p j : A) * f i‖ ≤ δ) ∧
      ∀ i, ‖star ((w_new : A) * f i - f i * (w_new : A)) * (p_new : A) -
        star ((w_new : A) * f i - f i * (w_new : A))‖ ≤ δ := by
  let l₀ : Filter S := (CStarAlgebra.isBasis_nonneg_sections S).filter ⊓ 𝓟 (Metric.ball 0 1)
  have hl₀ : l₀.IsIncreasingApproximateUnit := increasingApproximateUnit_ball S
  have := hl₀.neBot
  have hu₀_mem : ∀ᶠ y : S in l₀, u₀ ≤ y ∧ ‖y‖ < 1 :=
    eventually_of_mem (((CStarAlgebra.isBasis_nonneg_sections S).hasBasis.inf_principal
      (Metric.ball 0 1)).mem_of_mem ⟨hu₀, hu₀_norm⟩) fun y hy => ⟨hy.1, by simpa using hy.2⟩
  have hG_mem : ∀ᶠ y : S in l₀, ∀ i, ‖y * g i - g i‖ < ε :=
    eventually_all.mpr fun i =>
      (tendsto_iff_norm_sub_tendsto_zero.mp (hl₀.tendsto_mul_right (g i))).eventually
        (gt_mem_nhds hε)
  have hp_mem : ∀ᶠ y : S in l₀, ∀ j : Fin n, ‖(p j : A) * (y : A) - (p j : A)‖ ≤ δ ∧
      ∀ i, ‖((p j : A) * f i) * (y : A) - (p j : A) * f i‖ ≤ δ :=
    eventually_all.mpr fun j =>
      ((tendsto_iff_norm_sub_tendsto_zero.mp (hl₀.tendsto_mul_left (p j))).eventually
        (ge_mem_nhds hδ)).and <| eventually_all.mpr fun i => by
        let pa : S := ⟨(p j : A) * f i, mul_mem_right_of_mul_mem_left hmul (p j).2 (f i)⟩
        exact (tendsto_iff_norm_sub_tendsto_zero.mp (hl₀.tendsto_mul_left pa)).eventually
          (ge_mem_nhds hδ)
  obtain ⟨w_new, hw_u₀, hw_G, hw_p⟩ := (hu₀_mem.and (hG_mem.and hp_mem)).exists
  have h_pnew : ∀ᶠ q : S in CStarAlgebra.approximateUnit S, ∀ i,
      ‖star ((w_new : A) * f i - f i * (w_new : A)) * (q : A) -
        star ((w_new : A) * f i - f i * (w_new : A))‖ ≤ δ :=
    eventually_all.mpr fun i => by
      let sd : S := star ⟨(w_new : A) * f i - f i * (w_new : A),
        sub_mem (mul_mem_right_of_mul_mem_left hmul w_new.2 (f i)) (hmul (f i) w_new.2)⟩
      exact (tendsto_iff_norm_sub_tendsto_zero.mp
        ((CStarAlgebra.increasingApproximateUnit S).tendsto_mul_left sd)).eventually
        (ge_mem_nhds hδ)
  obtain ⟨p_new, hp_new⟩ := h_pnew.exists
  exact ⟨w_new, p_new, hw_u₀, hw_G, hw_p, hp_new⟩

/-- Inductive selection of an `n`-element chain `w, p : Fin n → S` of strict contractions in `S`
above `u₀` whose commutators with `f` satisfy Arveson's approximate orthogonality relations. -/
private theorem exists_quasicentral_chain (S : NonUnitalStarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (hmul : ∀ (a : A) {x : A}, x ∈ S → a * x ∈ S)
    {u₀ : S} (hu₀ : 0 ≤ u₀) (hu₀_norm : ‖u₀‖ < 1)
    {m l : ℕ} (f : Fin m → A) (g : Fin l → S) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (n : ℕ) :
    ∃ w p : Fin n → S,
      (∀ k, u₀ ≤ w k ∧ ‖w k‖ < 1) ∧
      (∀ k i, ‖w k * g i - g i‖ < ε) ∧
      (∀ k i, ‖star ((w k : A) * f i - f i * (w k : A)) * (p k : A) -
        star ((w k : A) * f i - f i * (w k : A))‖ ≤ δ) ∧
      (∀ j k, j < k → ‖(p j : A) * (w k : A) - (p j : A)‖ ≤ δ ∧
        ∀ i, ‖((p j : A) * f i) * (w k : A) - (p j : A) * f i‖ ≤ δ) := by
  induction n with
  | zero =>
    exact ⟨Fin.elim0, Fin.elim0, fun k => Fin.elim0 k, fun k => Fin.elim0 k,
      fun k => Fin.elim0 k, fun j => Fin.elim0 j⟩
  | succ n ih =>
    obtain ⟨w, p, hw_u₀, hw_G, hp_F, hcross⟩ := ih
    obtain ⟨w_new, p_new, hw_new_u₀, hw_new_G, hw_new_p, hp_new⟩ :=
      exists_quasicentral_step S hmul hu₀ hu₀_norm f g p hδ hε
    refine ⟨Fin.snoc w w_new, Fin.snoc p p_new,
      Fin.lastCases (by simpa using hw_new_u₀) (fun k => by simpa using hw_u₀ k),
      Fin.lastCases (by simpa using hw_new_G) (fun k => by simpa using hw_G k),
      Fin.lastCases (by simpa using hp_new) (fun k => by simpa using hp_F k), ?_⟩
    intro j k hjk
    refine k.lastCases (fun hj => ?_) (fun k₀ hj => ?_) hjk
    · refine j.lastCases (fun hlt => (lt_irrefl _ hlt).elim) (fun j₀ _ => ?_) hj
      simpa using hw_new_p j₀
    · refine j.lastCases (fun hlt => ((Fin.le_last _).not_gt hlt).elim) (fun j₀ hj₀ => ?_) hj
      simpa using hcross j₀ k₀ (Fin.castSucc_lt_castSucc_iff.mp hj₀)

/-- Averaging `N > 0` strict contractions above `u₀` preserves the lower bound `u₀ ≤ ·` and the
strict norm bound `‖·‖ < 1`. -/
private theorem cesaro_le_and_norm_lt_one {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] {N : ℕ} (hN : 0 < (N : ℝ)) {u₀ : B} {w : Fin N → B}
    (hw : ∀ k, u₀ ≤ w k ∧ ‖w k‖ < 1) :
    u₀ ≤ (N : ℝ)⁻¹ • ∑ k : Fin N, w k ∧ ‖(N : ℝ)⁻¹ • ∑ k : Fin N, w k‖ < 1 := by
  have hFin : Nonempty (Fin N) :=
    Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (Nat.cast_ne_zero.mp hN.ne'))
  refine ⟨?_, ?_⟩
  · have hsum : (N : ℝ) • u₀ ≤ ∑ k : Fin N, w k := by
      simpa [Finset.sum_const, Nat.cast_smul_eq_nsmul ℝ] using
        Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => (hw k).1
    have hsmul := smul_le_smul_of_nonneg_left hsum (inv_nonneg.mpr hN.le)
    rwa [inv_smul_smul₀ hN.ne'] at hsmul
  · calc ‖(N : ℝ)⁻¹ • ∑ k : Fin N, w k‖ ≤ (N : ℝ)⁻¹ * ∑ k : Fin N, ‖w k‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ < (N : ℝ)⁻¹ * ∑ _k : Fin N, (1 : ℝ) :=
          mul_lt_mul_of_pos_left
            (Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun k _ => (hw k).2)
            (inv_pos.mpr hN)
      _ = 1 := by simp [inv_mul_cancel₀ hN.ne']

/-- Quantitative finite-family Arveson lemma: for any `u₀ ∈ S` (`0 ≤ u₀`, `‖u₀‖ < 1`), finite
families `f : Fin m → A` and `g : Fin l → S`, and `ε > 0`, some `e ∈ S` with `u₀ ≤ e` and `‖e‖ < 1`
simultaneously left-approximates `g` and commutes with `f` up to `ε`. -/
private theorem exists_quasicentral_approx (S : NonUnitalStarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (hmul : ∀ (a : A) {x : A}, x ∈ S → a * x ∈ S)
    {u₀ : S} (hu₀ : 0 ≤ u₀) (hu₀_norm : ‖u₀‖ < 1)
    {m l : ℕ} (f : Fin m → A) (g : Fin l → S) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : S, u₀ ≤ e ∧ ‖e‖ < 1 ∧
      (∀ i, ‖e * g i - g i‖ < ε) ∧
      (∀ i, ‖(e : A) * f i - f i * (e : A)‖ < ε) := by
  let M : ℝ := 1 + ∑ i : Fin m, ‖f i‖
  have hM : 1 ≤ M := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  obtain ⟨N, hN⟩ := exists_nat_gt (8 * M ^ 2 / ε ^ 2)
  have hN_pos : 0 < (N : ℝ) := lt_trans (by positivity) hN
  have hFin : Nonempty (Fin N) :=
    Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (Nat.cast_ne_zero.mp hN_pos.ne'))
  let δ : ℝ := ε ^ 2 / (8 * M * (M + 2))
  obtain ⟨w, p, hw_u₀, hw_G, hp_F, hcross⟩ :=
    exists_quasicentral_chain S hmul hu₀ hu₀_norm f g (show 0 < δ by positivity) hε N
  let e : S := (N : ℝ)⁻¹ • ∑ k : Fin N, w k
  obtain ⟨he_u₀, he_norm⟩ := cesaro_le_and_norm_lt_one hN_pos hw_u₀
  refine ⟨e, he_u₀, he_norm, fun i => ?_, fun i => ?_⟩
  · have hrewrite : e * g i - g i = (N : ℝ)⁻¹ • ∑ k : Fin N, (w k * g i - g i) := by
      dsimp only [e]
      rw [smul_mul_assoc, Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_sub,
        inv_smul_smul₀ hN_pos.ne']
    rw [hrewrite, norm_smul, Real.norm_of_nonneg (by positivity)]
    calc (N : ℝ)⁻¹ * ‖∑ k : Fin N, (w k * g i - g i)‖
        ≤ (N : ℝ)⁻¹ * ∑ k : Fin N, ‖w k * g i - g i‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ < (N : ℝ)⁻¹ * ∑ _k : Fin N, ε :=
          mul_lt_mul_of_pos_left
            (Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun k _ => hw_G k i)
            (inv_pos.mpr hN_pos)
      _ = ε := by simp [inv_mul_cancel_left₀ hN_pos.ne']
  · have hfiM : ‖f i‖ ≤ M :=
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

/-- **Arveson's theorem** for closed star ideals: every closed `NonUnitalStarSubalgebra ℂ A` closed
under left multiplication by `A` admits an increasing approximate unit `l` that is quasicentral in
`A`, meaning `(e : A) * a - a * (e : A) → 0` along `l` for every `a : A`. -/
theorem exists_quasicentral_increasingApproximateUnit
    (S : NonUnitalStarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (hmul : ∀ (a : A) {x : A}, x ∈ S → a * x ∈ S) :
    ∃ l : Filter S, l.IsIncreasingApproximateUnit ∧
      ∀ a : A, Tendsto (fun e : S => (e : A) * a - a * (e : A)) l (𝓝 0) := by
  let Idx := {u₀ : S // 0 ≤ u₀ ∧ ‖u₀‖ < 1} × (Σ m : ℕ, Fin m → A) × {ε : ℝ // 0 < ε}
  let s : Idx → Set S := fun ⟨u₀, ⟨m, f⟩, ε⟩ =>
    {e : S | (u₀ : S) ≤ e ∧ ‖e‖ ≤ 1 ∧ ∀ i : Fin m, ‖(e : A) * f i - f i * (e : A)‖ < (ε : ℝ)}
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
    exact ⟨e, he_u₀, he_norm.le, he_F⟩
  have hle : l ≤ CStarAlgebra.approximateUnit S := by
    rw [hbasis.hasBasis.le_basis_iff (CStarAlgebra.hasBasis_approximateUnit S)]
    intro u₀ hu₀
    exact ⟨⟨⟨u₀, hu₀⟩, ⟨0, Fin.elim0⟩, ⟨1, zero_lt_one⟩⟩, trivial,
      fun _ ⟨heu₀, he1, _⟩ => ⟨heu₀, by simpa using he1⟩⟩
  refine ⟨l, (CStarAlgebra.increasingApproximateUnit S).mono hle, fun a => ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  rw [hbasis.hasBasis.tendsto_iff Metric.nhds_basis_ball]
  intro ε hε
  refine ⟨⟨⟨0, le_rfl, by simp⟩, ⟨1, fun _ => a⟩, ⟨ε, hε⟩⟩, trivial, fun _ ⟨_, _, heF⟩ => ?_⟩
  simpa using heF 0

/-- Criterion for a sequence of nonnegative contractions in a separable C⋆-algebra `B` to form an
increasing approximate unit: it suffices to left-approximate the first `n + 1` elements of
`TopologicalSpace.denseSeq B` within `1 / (n + 1)`. -/
private theorem isIncreasingApproximateUnit_of_denseSeq {B : Type*} [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
    {u : ℕ → B} (hu_nonneg : ∀ n, 0 ≤ u n) (hu_norm : ∀ n, ‖u n‖ ≤ 1)
    (hu_dense : ∀ n, ∀ k ≤ n,
      ‖u n * TopologicalSpace.denseSeq B k - TopologicalSpace.denseSeq B k‖ <
        1 / ((n : ℝ) + 1)) :
    (atTop.map u).IsIncreasingApproximateUnit := by
  have hright (x : B) : Tendsto (· * x) (atTop.map u) (𝓝 x) := by
    rw [tendsto_map'_iff, Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp (TopologicalSpace.denseRange_denseSeq B) x
      (ε / 3) (by positivity)
    obtain ⟨N, hN⟩ := exists_nat_gt (3 / ε)
    refine ⟨max k N, fun n hn => ?_⟩
    have hnε : 1 / ((n : ℝ) + 1) < ε / 3 := by
      rw [div_lt_iff₀ (by positivity)]
      have hN' : 3 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
      have hNn : (N : ℝ) * ε ≤ ((n : ℝ) + 1) * ε :=
        mul_le_mul_of_nonneg_right
          (by linarith [show (N : ℝ) ≤ n from Nat.cast_le.mpr (le_of_max_le_right hn)]) hε.le
      linarith
    have h1 : dist (u n * x) (u n * TopologicalSpace.denseSeq B k) < ε / 3 := by
      rw [dist_eq_norm, ← mul_sub]
      exact (norm_mul_le _ _).trans_lt
        ((mul_le_of_le_one_left (norm_nonneg _) (hu_norm n)).trans_lt (by rwa [← dist_eq_norm]))
    have h2 : dist (u n * TopologicalSpace.denseSeq B k)
        (TopologicalSpace.denseSeq B k) < ε / 3 := by
      rw [dist_eq_norm]
      exact (hu_dense n k (le_of_max_le_left hn)).trans hnε
    calc dist (u n * x) x
        ≤ dist (u n * x) (u n * TopologicalSpace.denseSeq B k) +
            dist (u n * TopologicalSpace.denseSeq B k) (TopologicalSpace.denseSeq B k) +
            dist (TopologicalSpace.denseSeq B k) x := dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add h1 h2) (by rwa [dist_comm])
      _ = ε := by ring
  have hsa : ∀ᶠ x in atTop.map u, IsSelfAdjoint x :=
    eventually_map.mpr (Eventually.of_forall fun n => (hu_nonneg n).isSelfAdjoint)
  exact
    { tendsto_mul_left := (CStarAlgebra.tendsto_mul_left_iff_tendsto_mul_right hsa).mpr hright
      tendsto_mul_right := hright
      eventually_nonneg := eventually_map.mpr (Eventually.of_forall hu_nonneg)
      eventually_norm := eventually_map.mpr (Eventually.of_forall hu_norm)
      neBot := map_neBot }

/-- If a contractive sequence `v : ℕ → B` in a separable C⋆-algebra commutes within `1 / (n + 1)`
with the first `n + 1` terms of `denseSeq B`, then `v n * a - a * v n → 0` for every `a : B`. -/
private theorem tendsto_commutator_of_denseSeq {B : Type*} [NonUnitalCStarAlgebra B]
    [TopologicalSpace.SeparableSpace B] {v : ℕ → B} (hv_norm : ∀ n, ‖v n‖ ≤ 1)
    (hv_comm : ∀ n, ∀ k ≤ n,
      ‖v n * TopologicalSpace.denseSeq B k - TopologicalSpace.denseSeq B k * v n‖ <
        1 / ((n : ℝ) + 1))
    (a : B) : Tendsto (fun n => v n * a - a * v n) atTop (𝓝 0) := by
  let fSeq : ℕ → B := TopologicalSpace.denseSeq B
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp (TopologicalSpace.denseRange_denseSeq B) a
    (ε / 3) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (3 / ε)
  refine ⟨max k N, fun n hn => ?_⟩
  have hnε : 1 / ((n : ℝ) + 1) < ε / 3 := by
    rw [div_lt_iff₀ (by positivity)]
    have hN' : 3 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
    have hNn : (N : ℝ) * ε ≤ ((n : ℝ) + 1) * ε :=
      mul_le_mul_of_nonneg_right
        (by linarith [show (N : ℝ) ≤ n from Nat.cast_le.mpr (le_of_max_le_right hn)]) hε.le
    linarith
  have hdiff : (v n * a - a * v n) - (v n * fSeq k - fSeq k * v n) =
      v n * (a - fSeq k) - (a - fSeq k) * v n := by noncomm_ring
  have ha_dist : ‖a - fSeq k‖ < ε / 3 := by rwa [← dist_eq_norm]
  have hpert : ‖v n * (a - fSeq k) - (a - fSeq k) * v n‖ < 2 * (ε / 3) := by
    calc ‖v n * (a - fSeq k) - (a - fSeq k) * v n‖
        ≤ ‖v n‖ * ‖a - fSeq k‖ + ‖a - fSeq k‖ * ‖v n‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ 1 * ‖a - fSeq k‖ + ‖a - fSeq k‖ * 1 :=
          add_le_add (mul_le_mul_of_nonneg_right (hv_norm n) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (hv_norm n) (norm_nonneg _))
      _ < 2 * (ε / 3) := by linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  calc ‖v n * a - a * v n‖
      ≤ ‖v n * fSeq k - fSeq k * v n‖ +
          ‖(v n * a - a * v n) - (v n * fSeq k - fSeq k * v n)‖ := norm_le_insert' _ _
    _ < ε / 3 + 2 * (ε / 3) := by
        rw [hdiff]
        exact add_lt_add ((hv_comm n k (le_of_max_le_left hn)).trans hnε) hpert
    _ = ε := by ring

/-- Separable sequential form of Arveson's theorem for closed star ideals: when `A` is separable,
`S` admits a monotone sequence `u : ℕ → S` of nonnegative strict contractions forming a
quasicentral increasing approximate unit of `S`. -/
theorem exists_seq_quasicentral_increasingApproximateUnit [TopologicalSpace.SeparableSpace A]
    (S : NonUnitalStarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (hmul : ∀ (a : A) {x : A}, x ∈ S → a * x ∈ S) :
    ∃ u : ℕ → S, Monotone u ∧ (∀ n, 0 ≤ u n) ∧ (∀ n, ‖u n‖ < 1) ∧
      (atTop.map u).IsIncreasingApproximateUnit ∧
      ∀ a : A, Tendsto (fun n => (u n : A) * a - a * (u n : A)) atTop (𝓝 0) := by
  let gSeq : ℕ → S := TopologicalSpace.denseSeq S
  let fSeq : ℕ → A := TopologicalSpace.denseSeq A
  let step : ℕ → {e : S // 0 ≤ e ∧ ‖e‖ < 1} →
      {e' : S // 0 ≤ e' ∧ ‖e'‖ < 1} := fun n ⟨u₀, hu₀_0, hu₀_1⟩ => by
    let h := exists_quasicentral_approx S hmul hu₀_0 hu₀_1
      (fun i : Fin (n + 1) => fSeq i) (fun i : Fin (n + 1) => gSeq i)
      (Nat.one_div_pos_of_nat (n := n))
    exact ⟨h.choose, hu₀_0.trans h.choose_spec.1, h.choose_spec.2.1⟩
  let recSeq : ℕ → {e : S // 0 ≤ e ∧ ‖e‖ < 1} := fun n => Nat.rec ⟨0, le_rfl, by simp⟩ step n
  let u : ℕ → S := fun n => (recSeq (n + 1)).1
  have hu_step (n : ℕ) : (recSeq n).1 ≤ u n ∧
      (∀ k, k ≤ n → ‖u n * gSeq k - gSeq k‖ < 1 / ((n : ℝ) + 1)) ∧
      (∀ k, k ≤ n → ‖(u n : A) * fSeq k - fSeq k * (u n : A)‖ < 1 / ((n : ℝ) + 1)) := by
    have hspec := (exists_quasicentral_approx S hmul (recSeq n).2.1 (recSeq n).2.2
      (fun i : Fin (n + 1) => fSeq i) (fun i : Fin (n + 1) => gSeq i)
      (Nat.one_div_pos_of_nat (n := n))).choose_spec
    exact ⟨hspec.1, fun k hk => hspec.2.2.1 ⟨k, Nat.lt_succ_of_le hk⟩,
      fun k hk => hspec.2.2.2 ⟨k, Nat.lt_succ_of_le hk⟩⟩
  have hu_nonneg (n : ℕ) : 0 ≤ u n := (recSeq (n + 1)).2.1
  have hu_norm (n : ℕ) : ‖u n‖ < 1 := (recSeq (n + 1)).2.2
  exact ⟨u, monotone_nat_of_le_succ fun n => (hu_step (n + 1)).1, hu_nonneg, hu_norm,
    isIncreasingApproximateUnit_of_denseSeq hu_nonneg (fun n => (hu_norm n).le)
      (fun n k hk => (hu_step n).2.1 k hk),
    tendsto_commutator_of_denseSeq (fun n => (hu_norm n).le)
      (fun n k hk => (hu_step n).2.2 k hk)⟩

end Arveson

end NonUnitalStarSubalgebra

namespace TwoSidedIdeal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (I : TwoSidedIdeal A) [IsClosed (I : Set A)]

/-- **Arveson's theorem:** every closed two-sided ideal `I` of a C⋆-algebra `A` admits a
quasicentral increasing approximate unit `l : Filter I`, meaning `l.IsIncreasingApproximateUnit`
and `(e : A) * a - a * (e : A) → 0` along `l` for every `a : A`. -/
theorem exists_quasicentral_increasingApproximateUnit :
    ∃ l : Filter I, l.IsIncreasingApproximateUnit ∧
      ∀ a : A, Tendsto (fun e : I => (e : A) * a - a * (e : A)) l (𝓝 0) := by
  obtain ⟨lS, hlS, hcomm⟩ :=
    I.toNonUnitalStarSubalgebra.exists_quasicentral_increasingApproximateUnit
      fun a _ hx => I.mem_toNonUnitalStarSubalgebra.mpr
        (I.mul_mem_left a _ (I.mem_toNonUnitalStarSubalgebra.mp hx))
  let φ := I.toNonUnitalStarSubalgebraEquiv.symm
  refine ⟨lS.map φ, hlS.map φ φ.surjective, fun a => ?_⟩
  rw [tendsto_map'_iff]
  exact (hcomm a).congr fun e => by
    simp only [Function.comp_apply, φ, I.coe_toNonUnitalStarSubalgebraEquiv_symm_apply]

/-- Separable sequential form of **Arveson's theorem:** when `A` is separable, every closed
two-sided ideal `I` of `A` admits a monotone sequence `u : ℕ → I` of nonnegative strict
contractions forming a quasicentral increasing approximate unit of `I`. -/
theorem exists_seq_quasicentral_increasingApproximateUnit [TopologicalSpace.SeparableSpace A] :
    ∃ u : ℕ → I, Monotone u ∧ (∀ n, 0 ≤ u n) ∧ (∀ n, ‖u n‖ < 1) ∧
      (atTop.map u).IsIncreasingApproximateUnit ∧
      ∀ a : A, Tendsto (fun n => (u n : A) * a - a * (u n : A)) atTop (𝓝 0) := by
  obtain ⟨uS, huS_mono, huS_0, huS_1, huS_approx, huS_comm⟩ :=
    I.toNonUnitalStarSubalgebra.exists_seq_quasicentral_increasingApproximateUnit
      fun a _ hx => I.mem_toNonUnitalStarSubalgebra.mpr
        (I.mul_mem_left a _ (I.mem_toNonUnitalStarSubalgebra.mp hx))
  let φ := I.toNonUnitalStarSubalgebraEquiv.symm
  let u : ℕ → I := fun n => φ (uS n)
  have hcoe (n : ℕ) : (u n : A) = (uS n : A) :=
    I.coe_toNonUnitalStarSubalgebraEquiv_symm_apply (uS n)
  have hu_mono : Monotone u := fun m n hmn =>
    Subtype.coe_le_coe.mp (by rw [hcoe, hcoe]; exact huS_mono hmn)
  have hu_0 (n : ℕ) : 0 ≤ u n := map_nonneg φ (huS_0 n)
  have hu_1 (n : ℕ) : ‖u n‖ < 1 := by
    change ‖(u n : A)‖ < 1
    rw [hcoe]
    exact huS_1 n
  have hu_approx : (atTop.map u).IsIncreasingApproximateUnit := by
    have heq : atTop.map u = (atTop.map uS).map φ := (Filter.map_map).symm
    exact heq ▸ huS_approx.map φ φ.surjective
  refine ⟨u, hu_mono, hu_0, hu_1, hu_approx, fun a => (huS_comm a).congr fun n => ?_⟩
  simp only [hcoe]

end TwoSidedIdeal
