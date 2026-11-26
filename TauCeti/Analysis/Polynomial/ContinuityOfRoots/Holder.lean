/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.Analysis.Polynomial.ContinuityOfRoots.Basic
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import TauCeti.Analysis.Polynomial.RootLocation

/-!
# Hölder dependence of the roots of a polynomial on its coefficients

The roots of a monic polynomial of degree `n` depend continuously on its coefficients, with
multiplicity (`Polynomial.Monic.exists_rel_roots_norm_sub_lt`), but not in a Lipschitz way: the
roots `±√ε` of `X² - ε` move by `√ε` when the constant coefficient moves by `ε`. Ostrowski's
theorem makes the dependence quantitative, with the Hölder exponent `1 / n`. For monic complex
polynomials `f` and `g` of degree `n ≥ 1` whose lower coefficients are bounded by `B` and differ
by at most `δ`, the roots of `f` and `g`, counted with multiplicity, can be matched one-to-one so
that matched roots are at distance at most

`(2n - 1) (n δ (B + 1)ⁿ⁻¹)^(1/n)`

(`Polynomial.Monic.rel_roots_norm_sub_le`). Applied at pairs of parameters, it shows that if a
family of monic polynomials of degree `n` has bounded coefficients, Hölder continuous of exponent
`α`, then its root multisets are Hölder continuous of exponent `α / n` for the distance of
optimal matchings. This is what is needed to pass Hölder regularity from the coefficients of a
family to symmetric functions of its roots that are not polynomial in the coefficients.

The one-sided estimate is elementary: if `g(z) = 0`, then `∏ ‖z - a‖ = ‖f(z)‖ = ‖(f - g)(z)‖` over
the roots `a` of `f`, so some root of `f` lies within `‖(f - g)(z)‖^(1/n)` of `z`
(`Polynomial.Splits.exists_mem_roots_norm_sub_pow_le`; compare
`Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt`). The matching needs more, because
several roots of `g` could cluster near a single simple root of `f`. It comes from a continuity
argument along a path of polynomials, which holds over any proper algebraically closed normed
field (`Polynomial.rel_roots_norm_sub_le_of_isPreconnected`): suppose `F x` are polynomials of
degree `n`, with coefficients continuous on a preconnected set `S`, whose roots stay within `ρ`
of the roots of `F x₀` for every `x ∈ S`. Group the distinct roots of `F x₀` into clusters,
the connected components of the graph joining two roots at distance at most `2ρ`. The closed
`ρ`-discs about different clusters are disjoint, so by continuity of roots the number of roots of
`F x` near each cluster is locally constant on `S`, hence constant. Matching the roots of `F x₀`
and `F x₁` within each cluster then moves a root by at most `ρ` plus the length `2ρ (n - 1)` of a
path through the cluster. For complex polynomials the straight path `f + t (g - f)`,
`t ∈ [0, 1]`, satisfies the hypothesis with the one-sided estimate.

## Main results

* `Polynomial.rel_roots_norm_sub_le_of_isPreconnected`: along a preconnected family of
  polynomials of degree `n` whose roots stay within `ρ` of those of `F x₀`, the roots of `F x₀`
  and `F x₁` match with multiplicity within `(2n - 1) ρ`.
* `Polynomial.Monic.rel_roots_norm_sub_le`: **Ostrowski's theorem** on the Hölder continuity of
  the roots of monic complex polynomials in their coefficients.

## References

* A. M. Ostrowski, *Solution of Equations in Euclidean and Banach Spaces*, Academic Press, 1973,
  Appendix A.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Chapter VIII.
-/

public section

open Filter Metric Set Topology

namespace Polynomial

section Path

variable {K : Type*} [NormedField K]

/-! ### Clusters of roots -/

/-- The graph on a finite set `R` of points joining two distinct points at distance at most
`2ρ`; its connected components are the clusters of `R` at scale `ρ`. -/
private def clusterGraph (R : Finset K) (ρ : ℝ) : SimpleGraph R :=
  SimpleGraph.fromRel fun a b => ‖(a : K) - b‖ ≤ 2 * ρ

private theorem clusterGraph_adj {R : Finset K} {ρ : ℝ} {a b : R} :
    (clusterGraph R ρ).Adj a b ↔ a ≠ b ∧ ‖(a : K) - b‖ ≤ 2 * ρ := by
  rw [clusterGraph, SimpleGraph.fromRel_adj, norm_sub_rev (b : K), or_self]

/-- Along a walk in the cluster graph, the endpoints are at distance at most `2ρ` times its
length. -/
private theorem norm_sub_le_of_walk {R : Finset K} {ρ : ℝ} {u v : R}
    (p : (clusterGraph R ρ).Walk u v) : ‖(u : K) - v‖ ≤ 2 * ρ * p.length := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    rw [SimpleGraph.Walk.length_cons, Nat.cast_add_one]
    linarith [norm_sub_le_norm_sub_add_norm_sub (a : K) b c, (clusterGraph_adj.1 h).2]

/-- Two points of the same cluster are at distance at most `2ρ (#R - 1)`: they are joined by a
path, which visits each point of `R` at most once. -/
private theorem norm_sub_le_of_reachable {R : Finset K} {ρ : ℝ} (hρ : 0 ≤ ρ) {u v : R}
    (h : (clusterGraph R ρ).Reachable u v) : ‖(u : K) - v‖ ≤ 2 * ρ * (R.card - 1) := by
  classical
  obtain ⟨p⟩ := h
  have hlen : p.bypass.length + 1 ≤ R.card := by
    simpa using p.bypass_isPath.length_lt
  have hlen' : (p.bypass.length : ℝ) ≤ R.card - 1 := by
    rw [le_sub_iff_add_le]
    exact_mod_cast hlen
  exact (norm_sub_le_of_walk p.bypass).trans (by gcongr)

open scoped Classical in
/-- The cluster label of a point `z`: the cluster of a point of `R` within `ρ` of `z`, if there is
one. -/
private noncomputable def clusterLabel (R : Finset K) (ρ : ℝ) (z : K) :
    Option (clusterGraph R ρ).ConnectedComponent :=
  if h : ∃ a : R, ‖z - a‖ ≤ ρ then some ((clusterGraph R ρ).connectedComponentMk h.choose)
  else none

/-- The cluster label of a point within `ρ` of a point `a` of `R` is the cluster of `a`: all
points of `R` within `ρ` of `z` are within `2ρ` of each other. -/
private theorem clusterLabel_eq {R : Finset K} {ρ : ℝ} {z : K} {a : R} (ha : ‖z - a‖ ≤ ρ) :
    clusterLabel R ρ z = some ((clusterGraph R ρ).connectedComponentMk a) := by
  have h : ∃ a : R, ‖z - a‖ ≤ ρ := ⟨a, ha⟩
  rw [clusterLabel, dite_eq_left h, Option.some_inj, SimpleGraph.ConnectedComponent.eq]
  by_cases hne : h.choose = a
  · rw [hne]
  · refine SimpleGraph.Adj.reachable (clusterGraph_adj.2 ⟨hne, ?_⟩)
    linarith [norm_sub_le_norm_sub_add_norm_sub (h.choose : K) z a, norm_sub_rev (h.choose : K) z,
      h.choose_spec]

/-- A gap between the distances of points of `R`: distances above `2ρ` are at least `2ρ + η`. -/
private theorem exists_pos_add_le_norm_sub (R : Finset K) (ρ : ℝ) :
    ∃ η > 0, ∀ a ∈ R, ∀ b ∈ R, 2 * ρ < ‖a - b‖ → 2 * ρ + η ≤ ‖a - b‖ := by
  classical
  set T := insert 1 (((R ×ˢ R).filter fun p : K × K => 2 * ρ < ‖p.1 - p.2‖).image
    fun p => ‖p.1 - p.2‖ - 2 * ρ)
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  refine ⟨T.min' hT, (Finset.lt_min'_iff _ _).2 fun x hx => ?_, fun a ha b hb hab => ?_⟩
  · rcases Finset.mem_insert.1 hx with rfl | hx
    · exact one_pos
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      exact sub_pos.2 (Finset.mem_filter.1 hp).2
  · have hmem : ‖a - b‖ - 2 * ρ ∈ T := Finset.mem_insert_of_mem <| Finset.mem_image.2
      ⟨(a, b), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha, hb⟩, hab⟩, rfl⟩
    linarith [T.min'_le _ hmem]

/-- Points within `ρ` of points of `R` and closer to each other than the gap `η` have the same
cluster label. -/
private theorem clusterLabel_eq_clusterLabel {R : Finset K} {ρ η : ℝ}
    (hη : ∀ a ∈ R, ∀ b ∈ R, 2 * ρ < ‖a - b‖ → 2 * ρ + η ≤ ‖a - b‖) {z w a b : K} (ha : a ∈ R)
    (hb : b ∈ R) (hza : ‖z - a‖ ≤ ρ) (hwb : ‖w - b‖ ≤ ρ) (hzw : ‖z - w‖ < η) :
    clusterLabel R ρ z = clusterLabel R ρ w := by
  rw [clusterLabel_eq (a := ⟨a, ha⟩) hza, clusterLabel_eq (a := ⟨b, hb⟩) hwb, Option.some_inj,
    SimpleGraph.ConnectedComponent.eq]
  have hab : ‖a - b‖ ≤ ‖a - z‖ + ‖z - w‖ + ‖w - b‖ := by
    linarith [norm_sub_le_norm_sub_add_norm_sub a z b, norm_sub_le_norm_sub_add_norm_sub z w b]
  have hab' : ‖a - b‖ ≤ 2 * ρ := by
    by_contra! h
    linarith [hη a ha b hb h, norm_sub_rev a z]
  by_cases hne : (⟨a, ha⟩ : R) = ⟨b, hb⟩
  · rw [hne]
  · exact SimpleGraph.Adj.reachable (clusterGraph_adj.2 ⟨hne, hab'⟩)

/-! ### Matching roots along a path of polynomials -/

variable [IsAlgClosed K] [ProperSpace K]

/-- **Matching roots along a path.** Let `F x` be polynomials of degree `n` over a proper
algebraically closed normed field, with coefficients continuous at the points of a preconnected
set `S`. Suppose that for every `x ∈ S` every root of `F x` lies within `ρ` of a root of `F x₀`,
where `x₀ ∈ S`. Then for every `x₁ ∈ S` the roots of `F x₀` and `F x₁`, counted with
multiplicity, can be matched one-to-one so that matched roots are at distance at most
`(2n - 1) ρ`. -/
theorem rel_roots_norm_sub_le_of_isPreconnected {B : Type*} [TopologicalSpace B]
    {F : B → K[X]} {S : Set B} (hS : IsPreconnected S) {n : ℕ}
    (hF : ∀ x ∈ S, ∀ i ≤ n, ContinuousAt (fun y => (F y).coeff i) x)
    (hdeg : ∀ x ∈ S, ∀ᶠ y in 𝓝 x, (F y).degree = n) {x₀ x₁ : B} (hx₀ : x₀ ∈ S) (hx₁ : x₁ ∈ S)
    {ρ : ℝ} (hρ : ∀ x ∈ S, ∀ z ∈ (F x).roots, ∃ a ∈ (F x₀).roots, ‖z - a‖ ≤ ρ) :
    (F x₀).roots.Rel (fun a z => ‖a - z‖ ≤ (2 * n - 1) * ρ) (F x₁).roots := by
  classical
  set R := (F x₀).roots.toFinset
  obtain ⟨η, hη, hgap⟩ := exists_pos_add_le_norm_sub R ρ
  -- The multiset of cluster labels of the roots of `F x` is locally constant on `S`, since
  -- nearby polynomials have roots matched within the gap `η`.
  set M := fun x => (F x).roots.map (clusterLabel R ρ)
  have hM : M x₀ = M x₁ := by
    let _ : TopologicalSpace (Multiset (Option (clusterGraph R ρ).ConnectedComponent)) := ⊥
    have : DiscreteTopology (Multiset (Option (clusterGraph R ρ).ConnectedComponent)) := ⟨rfl⟩
    refine hS.constant (fun x hx => ?_) hx₀ hx₁
    rw [ContinuousWithinAt, nhds_discrete, tendsto_pure]
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (eventually_rel_roots_norm_sub_lt (hF x hx) (hdeg x hx) hη), self_mem_nhdsWithin]
      with y hy hyS
    refine (Multiset.rel_eq.1 (Multiset.rel_map.2 (hy.mono fun z hz w hw hzw => ?_))).symm
    obtain ⟨a, ha, hza⟩ := hρ x hx z hz
    obtain ⟨b, hb, hwb⟩ := hρ y hyS w hw
    exact clusterLabel_eq_clusterLabel hgap (Multiset.mem_toFinset.2 ha)
      (Multiset.mem_toFinset.2 hb) hza hwb hzw
  -- Roots of `F x₀` and `F x₁` with the same cluster label are within `(2n - 1) ρ`.
  have hcard : (R.card : ℝ) ≤ n := by
    have hnat := natDegree_eq_of_degree_eq_some (hdeg x₀ hx₀).self_of_nhds
    exact_mod_cast (Multiset.toFinset_card_le _).trans ((card_roots' _).trans hnat.le)
  refine (Multiset.rel_map.1 (Multiset.rel_eq.2 hM)).mono fun a ha z hz hl => ?_
  obtain ⟨b, hb, hzb⟩ := hρ x₁ hx₁ z hz
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hzb
  have ha' : a ∈ R := Multiset.mem_toFinset.2 ha
  have hb' : b ∈ R := Multiset.mem_toFinset.2 hb
  rw [clusterLabel_eq (a := ⟨a, ha'⟩) (by simpa using hρ0), clusterLabel_eq (a := ⟨b, hb'⟩) hzb,
    Option.some_inj, SimpleGraph.ConnectedComponent.eq] at hl
  have hab := norm_sub_le_of_reachable hρ0 hl
  have : 2 * ρ * (R.card - 1) ≤ 2 * ρ * (n - 1) := by gcongr
  linarith [norm_sub_le_norm_sub_add_norm_sub a b z, norm_sub_rev b z]

end Path

/-! ### Ostrowski's theorem for complex polynomials -/

section Complex

/-- The straight path `f + t (g - f)` from `f` to `g`. -/
private noncomputable def segment (f g : ℂ[X]) (t : ℝ) : ℂ[X] :=
  f + (t : ℂ) • (g - f)

private theorem coeff_segment (f g : ℂ[X]) (t : ℝ) (i : ℕ) :
    (segment f g t).coeff i = f.coeff i + t * (g.coeff i - f.coeff i) := by
  simp [segment]

variable {f g : ℂ[X]}

private theorem degree_sub_lt_of_monic (hf : f.Monic) (hg : g.Monic)
    (hdeg : g.natDegree = f.natDegree) : (g - f).degree < f.degree := by
  have hd : g.degree = f.degree := by
    rw [degree_eq_natDegree hg.ne_zero, degree_eq_natDegree hf.ne_zero, hdeg]
  exact hd ▸ degree_sub_lt_left hd hg.ne_zero (by rw [hf.leadingCoeff, hg.leadingCoeff])

/-- The straight path between monic polynomials of the same degree consists of monic polynomials
of that degree. -/
private theorem monic_segment (hf : f.Monic) (hg : g.Monic) (hdeg : g.natDegree = f.natDegree)
    (t : ℝ) : (segment f g t).Monic :=
  hf.add_of_left ((degree_smul_le _ _).trans_lt (degree_sub_lt_of_monic hf hg hdeg))

private theorem degree_segment (hf : f.Monic) (hg : g.Monic) (hdeg : g.natDegree = f.natDegree)
    (t : ℝ) : (segment f g t).degree = f.natDegree := by
  rw [segment, degree_add_eq_left_of_degree_lt
    ((degree_smul_le _ _).trans_lt (degree_sub_lt_of_monic hf hg hdeg)),
    degree_eq_natDegree hf.ne_zero]

/-- On the segment, the lower coefficients stay bounded by a common bound `B` of those of the
endpoints. -/
private theorem norm_coeff_segment_le {B : ℝ} {i : ℕ} (hf : ‖f.coeff i‖ ≤ B)
    (hg : ‖g.coeff i‖ ≤ B) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(segment f g t).coeff i‖ ≤ B := by
  have h : (segment f g t).coeff i = ((1 - t : ℝ) : ℂ) * f.coeff i + (t : ℂ) * g.coeff i := by
    rw [coeff_segment]
    push_cast
    ring
  rw [h]
  calc _ ≤ ‖((1 - t : ℝ) : ℂ) * f.coeff i‖ + ‖(t : ℂ) * g.coeff i‖ := norm_add_le _ _
    _ = (1 - t) * ‖f.coeff i‖ + t * ‖g.coeff i‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.2 ht.2),
        Real.norm_of_nonneg ht.1]
    _ ≤ (1 - t) * B + t * B := by
      gcongr
      · exact sub_nonneg.2 ht.2
      · exact ht.1
    _ = B := by ring

/-- By Cauchy's bound, the roots of the polynomials on the segment have norm at most `B + 1`. -/
private theorem norm_le_of_mem_roots_segment (hf : f.Monic) (hg : g.Monic)
    (hdeg : g.natDegree = f.natDegree) {B : ℝ} (hB : 0 ≤ B)
    (hfB : ∀ i < f.natDegree, ‖f.coeff i‖ ≤ B) (hgB : ∀ i < f.natDegree, ‖g.coeff i‖ ≤ B)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ (segment f g t).roots) : ‖z‖ ≤ B + 1 := by
  have hm := monic_segment hf hg hdeg t
  have hb : cauchyBound (segment f g t) ≤ B.toNNReal + 1 := by
    rw [cauchyBound, hm.leadingCoeff, nnNorm_one, div_one,
      natDegree_eq_of_degree_eq_some (degree_segment hf hg hdeg t)]
    gcongr
    refine Finset.sup_le fun i hi => ?_
    exact (Real.le_toNNReal_iff_coe_le hB).2
      (norm_coeff_segment_le (hfB i (Finset.mem_range.1 hi)) (hgB i (Finset.mem_range.1 hi)) ht)
  have hlt : ‖z‖ < B.toNNReal + 1 := by
    exact_mod_cast ((isRoot_of_mem_roots hz).norm_lt_cauchyBound hm.ne_zero).trans_le hb
  linarith [Real.coe_toNNReal _ hB]

/-- The one-sided estimate: every root of `f + t (g - f)`, `0 ≤ t ≤ 1`, lies within
`(n δ (B + 1)ⁿ⁻¹)^(1/n)` of a root of `f`. -/
private theorem exists_mem_roots_norm_sub_le_of_mem_roots_segment (hf : f.Monic) (hg : g.Monic)
    (hdeg : g.natDegree = f.natDegree) (hn : f.natDegree ≠ 0) {B δ : ℝ} (hB : 0 ≤ B)
    (hfB : ∀ i < f.natDegree, ‖f.coeff i‖ ≤ B) (hgB : ∀ i < f.natDegree, ‖g.coeff i‖ ≤ B)
    (hδ : ∀ i < f.natDegree, ‖g.coeff i - f.coeff i‖ ≤ δ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {z : ℂ} (hz : z ∈ (segment f g t).roots) :
    ∃ a ∈ f.roots, ‖z - a‖ ≤
      (f.natDegree * δ * (B + 1) ^ (f.natDegree - 1)) ^ (f.natDegree⁻¹ : ℝ) := by
  set n := f.natDegree
  have hzB := norm_le_of_mem_roots_segment hf hg hdeg hB hfB hgB ht hz
  -- `f(z) = -t (g - f)(z)` since `z` is a root of `f + t (g - f)`
  have hfz : ‖f.eval z‖ ≤ ‖(g - f).eval z‖ := by
    have hroot := (isRoot_of_mem_roots hz).eq_zero
    rw [segment, eval_add, eval_smul, smul_eq_mul] at hroot
    rw [show f.eval z = -((t : ℂ) * (g - f).eval z) by linear_combination hroot]
    simpa [abs_of_nonneg ht.1] using mul_le_of_le_one_left (norm_nonneg ((g - f).eval z)) ht.2
  -- the lower coefficients of `g - f` are at most `δ`, and `‖z‖ ≤ B + 1`
  have hgfz : ‖(g - f).eval z‖ ≤ n * δ * (B + 1) ^ (n - 1) := by
    have hlt : (g - f).natDegree < n := by
      rcases eq_or_ne (g - f) 0 with h0 | h0
      · rw [h0, natDegree_zero]
        exact Nat.pos_of_ne_zero hn
      · exact natDegree_lt_natDegree h0 (degree_sub_lt_of_monic hf hg hdeg)
    rw [eval_eq_sum_range' hlt]
    calc _ ≤ ∑ i ∈ Finset.range n, ‖(g - f).coeff i * z ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range n, δ * (B + 1) ^ (n - 1) := Finset.sum_le_sum fun i hi => by
        have hi' := Finset.mem_range.1 hi
        rw [norm_mul, norm_pow, coeff_sub]
        refine mul_le_mul (hδ i hi') ?_ (by positivity) ((norm_nonneg _).trans (hδ i hi'))
        exact (pow_le_pow_left₀ (norm_nonneg _) hzB i).trans
          (pow_le_pow_right₀ (by linarith) (by omega))
      _ = n * δ * (B + 1) ^ (n - 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc]
  -- so the nearest root of `f` is within the `n`-th root of `‖f(z)‖`
  obtain ⟨a, ha, hpow⟩ := (IsAlgClosed.splits f).exists_mem_roots_norm_sub_pow_le hn z
  rw [hf.leadingCoeff, norm_one, one_mul] at hpow
  refine ⟨a, ha, ?_⟩
  calc ‖z - a‖ = (‖z - a‖ ^ n) ^ (n⁻¹ : ℝ) := (Real.pow_rpow_inv_natCast (norm_nonneg _) hn).symm
    _ ≤ _ := Real.rpow_le_rpow (by positivity) (hpow.trans (hfz.trans hgfz)) (by positivity)

/-- **Ostrowski's theorem.** Let `f` and `g` be monic complex polynomials of the same degree `n`,
whose coefficients below degree `n` are bounded by `B` and differ by at most `δ`. Then the roots
of `f` and `g`, counted with multiplicity, can be matched one-to-one so that matched roots are at
distance at most `(2n - 1) (n δ (B + 1)ⁿ⁻¹)^(1/n)`. So the roots depend Hölder continuously, with
exponent `1 / n`, on the coefficients, uniformly for bounded coefficients. -/
theorem Monic.rel_roots_norm_sub_le (hf : f.Monic) (hg : g.Monic)
    (hdeg : g.natDegree = f.natDegree) {B δ : ℝ} (hfB : ∀ i < f.natDegree, ‖f.coeff i‖ ≤ B)
    (hgB : ∀ i < f.natDegree, ‖g.coeff i‖ ≤ B)
    (hδ : ∀ i < f.natDegree, ‖g.coeff i - f.coeff i‖ ≤ δ) :
    f.roots.Rel (fun a z => ‖a - z‖ ≤ (2 * f.natDegree - 1) *
      (f.natDegree * δ * (B + 1) ^ (f.natDegree - 1)) ^ (f.natDegree⁻¹ : ℝ)) g.roots := by
  rcases eq_or_ne f.natDegree 0 with hn | hn
  · rw [hf.natDegree_eq_zero.1 hn, hg.natDegree_eq_zero.1 (hdeg.trans hn), roots_one]
    exact Multiset.Rel.zero
  have hB : 0 ≤ B := (norm_nonneg _).trans (hfB 0 (Nat.pos_of_ne_zero hn))
  have h0 : segment f g 0 = f := by simp [segment]
  have h1 : segment f g 1 = g := by simp [segment]
  have h := rel_roots_norm_sub_le_of_isPreconnected (F := segment f g) isPreconnected_Icc
    (fun _ _ i _ => by simp_rw [coeff_segment]; fun_prop)
    (fun _ _ => Eventually.of_forall (degree_segment hf hg hdeg))
    (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) fun t ht z hz => h0 ▸
      exists_mem_roots_norm_sub_le_of_mem_roots_segment hf hg hdeg hn hB hfB hgB hδ ht hz
  rwa [h0, h1] at h

end Complex

end Polynomial
