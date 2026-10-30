/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Compactoid subsets of normed spaces

A subset `S` of a seminormed space `E` over a normed field `K` is *compactoid*
(`TauCeti.IsCompactoidSet K S`) if for every `ε > 0` there are finitely many vectors
`v₁, …, vₙ` such that every `x ∈ S` lies within `ε` of a combination `∑ aᵢ • vᵢ` with all
`‖aᵢ‖ ≤ 1`. Over a nonarchimedean field the combinations with `‖aᵢ‖ ≤ 1` are exactly the
`K°`-submodule spanned by the `vᵢ`, so this is the condition that `S ⊆ U + span_{K°} F` for every
zero neighbourhood `U` and some finite `F` (`TauCeti.isCompactoidSet_iff_forall_mem_nhds`).

Compactoid sets replace relatively compact sets in nonarchimedean functional analysis: over a
field such as `ℂ_p`, which is not locally compact, a bounded subset of a line need not be totally
bounded, yet it is compactoid. Operators mapping the closed unit ball to a compactoid set are the
compact operators of nonarchimedean Banach space theory. Every totally bounded set is compactoid,
and over a field whose closed balls are compact, such as a nontrivially normed locally compact
field, the two notions agree (`TauCeti.isCompactoidSet_iff_totallyBounded`).

## Main definitions

* `TauCeti.IsCompactoidSet K S`: finite approximation of `S` by combinations with coefficients
  in the closed unit ball of `K`.

## Main results

* `TauCeti.isCompactoidSet_iff_forall_mem_nhds`: the formulation through zero neighbourhoods.
* `TauCeti.isCompactoidSet_of_forall_exists_finset`: approximation by finite subfamilies of a
  fixed family suffices.
* `TauCeti.isCompactoidSet_of_forall_exists_norm_sub_lt`: a set approximated arbitrarily well by
  compactoid sets is compactoid.
* `TauCeti.IsCompactoidSet.mono`, `TauCeti.IsCompactoidSet.union`,
  `TauCeti.IsCompactoidSet.add`, `TauCeti.isCompactoidSet_sum`, `TauCeti.IsCompactoidSet.smul`,
  `TauCeti.IsCompactoidSet.image`, `TauCeti.isCompactoidSet_closure_iff`: stability under
  subsets, finite unions, finite sums, scalar multiples, continuous linear images and closure.
* `TotallyBounded.isCompactoidSet`, `Set.Finite.isCompactoidSet`: totally bounded sets, in
  particular finite sets, are compactoid.
* `TauCeti.IsCompactoidSet.isBounded`: compactoid sets are bounded.
* `Bornology.IsBounded.isCompactoidSet`: in a finite-dimensional space over a complete nontrivially
  normed field, conversely, bounded sets are compactoid.
* `TauCeti.isCompactoidSet_iff_totallyBounded`: over a field whose closed balls are compact,
  compactoid sets are exactly the totally bounded sets.

## References

* N. De Grande-De Kimpe, *Non-archimedean nuclearity*, Groupe de travail d'analyse
  ultramétrique **9**, no. 3 (1981–1982), exp. J4, §§1.1, 2.1.
* W. H. Schikhof, *Banach spaces over nonarchimedean valued fields*, Topology Proceedings **24**
  (1999), 547–581, §§2.13, 2.15.
-/

public section

open Filter Topology Metric Pointwise

namespace TauCeti

variable {K E F : Type*}

section NormedField

variable [NormedField K] [SeminormedAddCommGroup E] [NormedSpace K E]
  [SeminormedAddCommGroup F] [NormedSpace K F]

variable (K) in
/-- A subset `S` of a seminormed `K`-space is **compactoid** if for every `ε > 0` there are
finitely many vectors `v i` such that every `x ∈ S` is within `ε` of some `∑ i, a i • v i` with
all `‖a i‖ ≤ 1`. -/
def IsCompactoidSet (S : Set E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (v : Fin n → E), ∀ x ∈ S,
    ∃ a : Fin n → K, (∀ i, ‖a i‖ ≤ 1) ∧ ‖x - ∑ i, a i • v i‖ < ε

/-- Unfolding `TauCeti.IsCompactoidSet`. -/
theorem isCompactoidSet_iff {S : Set E} :
    IsCompactoidSet K S ↔ ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (v : Fin n → E), ∀ x ∈ S,
      ∃ a : Fin n → K, (∀ i, ‖a i‖ ≤ 1) ∧ ‖x - ∑ i, a i • v i‖ < ε :=
  Iff.rfl

/-- A set is compactoid if and only if for every neighbourhood `U` of zero there are finitely many
vectors `v i` with `S ⊆ U + {∑ i, a i • v i | ‖a i‖ ≤ 1}`. -/
theorem isCompactoidSet_iff_forall_mem_nhds {S : Set E} :
    IsCompactoidSet K S ↔ ∀ U ∈ 𝓝 (0 : E), ∃ (n : ℕ) (v : Fin n → E), ∀ x ∈ S,
      ∃ a : Fin n → K, (∀ i, ‖a i‖ ≤ 1) ∧ x - ∑ i, a i • v i ∈ U := by
  refine ⟨fun hS U hU ↦ ?_, fun hS ε hε ↦ ?_⟩
  · obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨n, v, hv⟩ := hS ε hε
    exact ⟨n, v, fun x hx ↦ (hv x hx).imp fun a ha ↦ ⟨ha.1, hεU (mem_ball_zero_iff.2 ha.2)⟩⟩
  · obtain ⟨n, v, hv⟩ := hS _ (ball_mem_nhds 0 hε)
    exact ⟨n, v, fun x hx ↦ (hv x hx).imp fun a ha ↦ ⟨ha.1, mem_ball_zero_iff.1 ha.2⟩⟩

/-- To show that `S` is compactoid it suffices to approximate it, for every `ε > 0`, by
combinations of a finite subfamily of a fixed family `v`, with coefficients of norm at most one. -/
theorem isCompactoidSet_of_forall_exists_finset {ι : Type*} {S : Set E} (v : ι → E)
    (h : ∀ ε : ℝ, 0 < ε → ∃ t : Finset ι, ∀ x ∈ S,
      ∃ a : ι → K, (∀ i, ‖a i‖ ≤ 1) ∧ ‖x - ∑ i ∈ t, a i • v i‖ < ε) :
    IsCompactoidSet K S := by
  intro ε hε
  obtain ⟨t, ht⟩ := h ε hε
  refine ⟨t.card, fun k ↦ v (t.equivFin.symm k), fun x hx ↦ ?_⟩
  obtain ⟨a, ha, hx⟩ := ht x hx
  refine ⟨fun k ↦ a (t.equivFin.symm k), fun k ↦ ha _, ?_⟩
  rwa [Equiv.sum_comp t.equivFin.symm (fun i ↦ a i • v i), Finset.sum_coe_sort t fun i ↦ a i • v i]

/-- A subset of a compactoid set is compactoid. -/
theorem IsCompactoidSet.mono {S T : Set E} (hT : IsCompactoidSet K T) (hST : S ⊆ T) :
    IsCompactoidSet K S := fun ε hε ↦
  (hT ε hε).imp fun _ ↦ Exists.imp fun _ hv x hx ↦ hv x (hST hx)

/-- The empty set is compactoid. -/
@[simp]
theorem isCompactoidSet_empty : IsCompactoidSet K (∅ : Set E) :=
  fun _ _ ↦ ⟨0, Fin.elim0, by simp⟩

/-- The union of two compactoid sets is compactoid. -/
theorem IsCompactoidSet.union {S T : Set E} (hS : IsCompactoidSet K S)
    (hT : IsCompactoidSet K T) : IsCompactoidSet K (S ∪ T) := by
  intro ε hε
  obtain ⟨m, v, hv⟩ := hS ε hε
  obtain ⟨n, w, hw⟩ := hT ε hε
  refine ⟨m + n, Fin.append v w, ?_⟩
  rintro x (hx | hx)
  · obtain ⟨a, ha, hx⟩ := hv x hx
    refine ⟨Fin.append a 0, fun i ↦ Fin.addCases (by simpa using ha) (by simp) i, ?_⟩
    simpa [Fin.sum_univ_add] using hx
  · obtain ⟨b, hb, hx⟩ := hw x hx
    refine ⟨Fin.append 0 b, fun i ↦ Fin.addCases (by simp) (by simpa using hb) i, ?_⟩
    simpa [Fin.sum_univ_add] using hx

/-- The pointwise sum of two compactoid sets is compactoid. -/
theorem IsCompactoidSet.add {S T : Set E} (hS : IsCompactoidSet K S)
    (hT : IsCompactoidSet K T) : IsCompactoidSet K (S + T) := by
  intro ε hε
  obtain ⟨m, v, hv⟩ := hS (ε / 2) (half_pos hε)
  obtain ⟨n, w, hw⟩ := hT (ε / 2) (half_pos hε)
  refine ⟨m + n, Fin.append v w, ?_⟩
  rintro _ ⟨x, hx, y, hy, rfl⟩
  obtain ⟨a, ha, hx⟩ := hv x hx
  obtain ⟨b, hb, hy⟩ := hw y hy
  refine ⟨Fin.append a b, fun i ↦ Fin.addCases (by simpa using ha) (by simpa using hb) i, ?_⟩
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  calc ‖x + y - (∑ i, a i • v i + ∑ i, b i • w i)‖
      = ‖(x - ∑ i, a i • v i) + (y - ∑ i, b i • w i)‖ := by congr 1; abel
    _ ≤ ‖x - ∑ i, a i • v i‖ + ‖y - ∑ i, b i • w i‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hx hy
    _ = ε := add_halves ε

/-- A finite pointwise sum of compactoid sets is compactoid. -/
theorem isCompactoidSet_sum {ι : Type*} {s : Finset ι} (t : ι → Set E)
    (h : ∀ i ∈ s, IsCompactoidSet K (t i)) : IsCompactoidSet K (∑ i ∈ s, t i) :=
  Finset.sum_induction t (IsCompactoidSet K) (fun _ _ ↦ IsCompactoidSet.add)
    (fun _ _ ↦ ⟨0, Fin.elim0, fun x hx ↦ ⟨Fin.elim0, (·.elim0), by simp_all⟩⟩) h

/-- A set that lies, for every `ε > 0`, within distance `ε` of some compactoid set is compactoid.
-/
theorem isCompactoidSet_of_forall_exists_norm_sub_lt {S : Set E}
    (h : ∀ ε : ℝ, 0 < ε → ∃ T : Set E, IsCompactoidSet K T ∧ ∀ x ∈ S, ∃ y ∈ T, ‖x - y‖ < ε) :
    IsCompactoidSet K S := by
  intro ε hε
  obtain ⟨T, hT, hST⟩ := h (ε / 2) (half_pos hε)
  obtain ⟨n, v, hv⟩ := hT (ε / 2) (half_pos hε)
  refine ⟨n, v, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := hST x hx
  obtain ⟨a, ha, hy⟩ := hv y hy
  refine ⟨a, ha, ?_⟩
  calc ‖x - ∑ i, a i • v i‖ = ‖(x - y) + (y - ∑ i, a i • v i)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖x - y‖ + ‖y - ∑ i, a i • v i‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hxy hy
    _ = ε := add_halves ε

/-- The closure of a compactoid set is compactoid. -/
theorem IsCompactoidSet.closure {S : Set E} (hS : IsCompactoidSet K S) :
    IsCompactoidSet K (closure S) :=
  isCompactoidSet_of_forall_exists_norm_sub_lt fun ε hε ↦ ⟨S, hS, fun x hx ↦ by
    simpa only [← dist_eq_norm] using Metric.mem_closure_iff.1 hx ε hε⟩

/-- A set is compactoid if and only if its closure is. -/
@[simp]
theorem isCompactoidSet_closure_iff {S : Set E} :
    IsCompactoidSet K (closure S) ↔ IsCompactoidSet K S :=
  ⟨fun h ↦ h.mono subset_closure, IsCompactoidSet.closure⟩

/-- A compactoid set is bounded. -/
theorem IsCompactoidSet.isBounded {S : Set E} (hS : IsCompactoidSet K S) :
    Bornology.IsBounded S := by
  obtain ⟨n, v, hv⟩ := hS 1 one_pos
  refine isBounded_iff_forall_norm_le.2 ⟨1 + ∑ i, ‖v i‖, fun x hx ↦ ?_⟩
  obtain ⟨a, ha, hx⟩ := hv x hx
  have hsum : ‖∑ i, a i • v i‖ ≤ ∑ i, ‖v i‖ :=
    (norm_sum_le _ _).trans <| Finset.sum_le_sum fun i _ ↦
      (norm_smul_le _ _).trans <| mul_le_of_le_one_left (norm_nonneg _) (ha i)
  calc ‖x‖ = ‖(x - ∑ i, a i • v i) + ∑ i, a i • v i‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - ∑ i, a i • v i‖ + ‖∑ i, a i • v i‖ := norm_add_le _ _
    _ ≤ 1 + ∑ i, ‖v i‖ := add_le_add hx.le hsum

/-- The image of a compactoid set under a continuous linear map is compactoid. -/
theorem IsCompactoidSet.image {S : Set E} (hS : IsCompactoidSet K S) (u : E →L[K] F) :
    IsCompactoidSet K (u '' S) := by
  rw [isCompactoidSet_iff_forall_mem_nhds] at hS ⊢
  intro U hU
  obtain ⟨n, v, hv⟩ := hS _ (u.continuous.tendsto' 0 0 (map_zero u) hU)
  refine ⟨n, fun i ↦ u (v i), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, ha, hx⟩ := hv x hx
  exact ⟨a, ha, by simpa using hx⟩

/-- A scalar multiple of a compactoid set is compactoid. -/
theorem IsCompactoidSet.smul {S : Set E} (hS : IsCompactoidSet K S) (c : K) :
    IsCompactoidSet K (c • S) := by
  rw [← Set.image_smul]
  exact hS.image (c • ContinuousLinearMap.id K E)

end NormedField

section TotallyBounded

variable [NormedField K] [SeminormedAddCommGroup E] [NormedSpace K E]

/-- Over a field whose closed balls are compact, for instance a nontrivially normed locally
compact field such as `ℚ_p`, every compactoid set is totally bounded. -/
theorem IsCompactoidSet.totallyBounded [ProperSpace K] {S : Set E}
    (hS : IsCompactoidSet K S) : TotallyBounded S := by
  refine Metric.totallyBounded_iff.2 fun ε hε ↦ ?_
  obtain ⟨n, v, hv⟩ := hS (ε / 2) (half_pos hε)
  -- The combinations with coefficients in the closed unit ball form a compact set.
  have hcpt : IsCompact ((fun a : Fin n → K ↦ ∑ i, a i • v i) ''
      Set.univ.pi fun _ ↦ closedBall (0 : K) 1) :=
    (isCompact_univ_pi fun _ ↦ isCompact_closedBall 0 1).image <| by fun_prop
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.1 hcpt.totallyBounded (ε / 2) (half_pos hε)
  refine ⟨t, ht, fun x hx ↦ ?_⟩
  obtain ⟨a, ha, hx⟩ := hv x hx
  obtain ⟨y, hy, hay⟩ := Set.mem_iUnion₂.1 <| hcover
    ⟨a, fun i _ ↦ mem_closedBall_zero_iff.2 (ha i), rfl⟩
  refine Set.mem_iUnion₂.2 ⟨y, hy, ?_⟩
  rw [mem_ball] at hay ⊢
  calc dist x y ≤ dist x (∑ i, a i • v i) + dist (∑ i, a i • v i) y := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (by rwa [dist_eq_norm]) hay
    _ = ε := add_halves ε

end TotallyBounded

section FiniteDimensional

variable [NontriviallyNormedField K] [CompleteSpace K] [NormedAddCommGroup E] [NormedSpace K E]
  [FiniteDimensional K E]

/-- A bounded subset of a finite-dimensional normed space over a complete nontrivially normed
field is compactoid: after scaling by a scalar of large norm, its coordinates in a basis have norm
at most one. -/
theorem _root_.Bornology.IsBounded.isCompactoidSet {S : Set E} (hS : Bornology.IsBounded S) :
    IsCompactoidSet K S := by
  let b := Module.finBasis K E
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 (hS.image b.equivFunL.toContinuousLinearMap)
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm K (max M 0)
  have hc₀ : 0 < ‖c‖ := (le_max_right M 0).trans_lt hc
  refine fun ε hε ↦ ⟨_, fun i ↦ c • b i, fun x hx ↦ ⟨fun i ↦ b.repr x i * c⁻¹, fun i ↦ ?_, ?_⟩⟩
  · have hxM : ‖b.equivFunL x‖ ≤ M := by
      simpa only [ContinuousLinearEquiv.coe_coe] using hM _ ⟨x, hx, rfl⟩
    rw [norm_mul, norm_inv, mul_inv_le_iff₀ hc₀, one_mul, ← Module.Basis.equivFunL_apply]
    exact (norm_le_pi_norm (b.equivFunL x) i).trans <| hxM.trans <| (le_max_left M 0).trans hc.le
  · simpa [smul_smul, inv_mul_cancel_right₀ (norm_pos_iff.1 hc₀), b.sum_repr x] using hε

end FiniteDimensional

end TauCeti

section TotallyBounded

open TauCeti

variable {K E : Type*} [NormedField K] [SeminormedAddCommGroup E] [NormedSpace K E]

/-- A totally bounded set is compactoid. -/
theorem TotallyBounded.isCompactoidSet {S : Set E} (hS : TotallyBounded S) :
    IsCompactoidSet K S := by
  classical
  refine isCompactoidSet_of_forall_exists_finset id fun ε hε ↦ ?_
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.1 hS ε hε
  refine ⟨ht.toFinset, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcover hx)
  refine ⟨Pi.single y 1, fun z ↦ ?_, ?_⟩
  · rcases eq_or_ne z y with rfl | hzy <;> simp [*]
  · rw [Finset.sum_eq_single_of_mem y (ht.mem_toFinset.2 hy) fun z _ hzy ↦ by simp [hzy]]
    simpa [← dist_eq_norm] using hxy

/-- A finite set is compactoid. -/
theorem Set.Finite.isCompactoidSet {S : Set E} (hS : S.Finite) : IsCompactoidSet K S :=
  hS.totallyBounded.isCompactoidSet

/-- A compact set is compactoid. -/
theorem IsCompact.isCompactoidSet {S : Set E} (hS : IsCompact S) : IsCompactoidSet K S :=
  hS.totallyBounded.isCompactoidSet

/-- Over a field whose closed balls are compact, a set is compactoid if and only if it is totally
bounded. -/
theorem TauCeti.isCompactoidSet_iff_totallyBounded [ProperSpace K] {S : Set E} :
    IsCompactoidSet K S ↔ TotallyBounded S :=
  ⟨IsCompactoidSet.totallyBounded, TotallyBounded.isCompactoidSet⟩

end TotallyBounded
