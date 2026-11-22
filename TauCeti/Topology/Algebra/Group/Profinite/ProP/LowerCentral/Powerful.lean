/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Powerful
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Subgroup
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.LowerCentralSeries

/-!
# The lower `p`-series of a powerful group

Let `p` be a prime and `G` a powerful group (`TauCeti.IsPowerful`): its commutator subgroup lies in
the closed power subgroup `Gᵖ`, or in `G⁴` when `p = 2`. Write `λ_k = λ_k(G)` for the lower
`p`-series and `gr_k(G) = λ_k ⧸ λ_{k+1}` for its graded pieces, with the `p`-power operator
`π : gr_k(G) → gr_{k+1}(G)` and the bracket of `Graded/Basic.lean`.

The graded form of powerfulness is that `π` is **surjective** in every degree
(`TauCeti.IsPowerful.gradedPow_surjective`), as soon as the relevant term of the series is open.
In degree zero, `λ_1 = Gᵖ` (`TauCeti.IsPowerful.closedPowerSubgroup_eq_pLowerCentralSeries_one`)
says that `gr_1(G)` is spanned by the `p`-powers of degree-zero classes, and `π` is additive there:
for odd `p` always, and for `p = 2` because powerfulness makes the degree-zero brackets vanish
(`TauCeti.IsPowerful.gradedBracket_zero_zero_eq_zero_of_two`). In higher degrees `gr_{k+1}(G)` is
spanned by `π gr_k(G)` and the brackets `[gr_k(G), gr_0(G)]`, and once `gr_k(G) = π gr_{k-1}(G)`
every such bracket `[π w, y] = π [w, y]` is itself a `p`-power class; for `p = 2` and `k = 1` this
again uses the vanishing of the degree-zero brackets.

For a topologically finitely generated pro-`p` group this gives the structure of the lower
`p`-series of Dixon–du Sautoy–Mann–Segal, Theorem 3.6:

* `λ_k = G^{p^k}`: the lower `p`-series is the series of closed power subgroups
  (`TauCeti.IsPowerful.pLowerCentralSeries_eq_closedPowerSubgroup`);
* `λ_{k+1} = (λ_k)ᵖ`: each term is the closed power subgroup of the previous one, computed inside
  it (`TauCeti.IsPowerful.map_subtype_closedPowerSubgroup_pLowerCentralSeries`);
* each `λ_k` is again powerful (`TauCeti.isPowerful_pLowerCentralSeries`);
* the successive indices `[λ_k : λ_{k+1}]` are non-increasing
  (`TauCeti.IsPowerful.relIndex_pLowerCentralSeries_succ_le`), since `π` maps `gr_k(G)` onto
  `gr_{k+1}(G)`.

In a uniform group `π` is moreover injective, so the indices are constant; that converse is not
proved here.

## Main results

* `TauCeti.IsPowerful.gradedPow_add_zero`,
  `TauCeti.IsPowerful.gradedPow_gradedBracket_zero_zero`: in a powerful group `π` is additive in
  degree zero and `π [x, y] = [π x, y]` for degree-zero classes, for every prime `p`.
* `TauCeti.IsPowerful.gradedPow_surjective`, `TauCeti.IsPowerful.gradedPowIter_surjective`: `π`
  maps `gr_k(G)` onto `gr_{k+1}(G)`, and `π^k` maps `gr_0(G)` onto `gr_k(G)`.
* `TauCeti.IsPowerful.pLowerCentralSeries_eq_closedPowerSubgroup`: `λ_k = G^{p^k}`.
* `TauCeti.IsPowerful.map_subtype_closedPowerSubgroup_pLowerCentralSeries`: `λ_{k+1} = (λ_k)ᵖ`.
* `TauCeti.isPowerful_pLowerCentralSeries`: `λ_k` is powerful.
* `TauCeti.IsPowerful.relIndex_pLowerCentralSeries_succ_le`:
  `[λ_{k+1} : λ_{k+2}] ≤ [λ_k : λ_{k+1}]`.

## References

* J. D. Dixon, M. P. F. du Sautoy, A. Mann and D. Segal, *Analytic pro-`p` groups*, second
  edition, Chapter 3, Theorem 3.6.
-/

public section

namespace TauCeti

open Subgroup
open scoped commutatorElement

variable {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### The `p`-power operator of a powerful group -/

/-- **The degree-zero brackets of a powerful group vanish at `p = 2`**: the commutators lie in
`G⁴ ≤ λ_2`. -/
theorem IsPowerful.gradedBracket_zero_zero_eq_zero_of_two (hG : IsPowerful 2 G)
    (x y : gradedPiece 2 G 0) : gradedBracket 2 G 0 0 x y = 0 := by
  obtain ⟨g, rfl⟩ := gradedMkZero_surjective x
  obtain ⟨h, rfl⟩ := gradedMkZero_surjective y
  rw [gradedBracket_gradedMkZero, gradedMk_eq_zero_iff]
  have h4 : closedPowerSubgroup 4 G ≤ pLowerCentralSeries 2 G 2 :=
    (closedPowerSubgroup_le_iff (isClosed_pLowerCentralSeries 2)).mpr fun g ↦ by
      simpa using pow_pow_mem_pLowerCentralSeries (p := 2) (mem_pLowerCentralSeries_zero 2 g) 2
  exact h4 (isPowerful_two_iff.mp hG (commutator_mem_commutator (mem_top g) (mem_top h)))

/-- **In a powerful group `π` is additive in degree zero**, for a prime `p`: the defect
`(p choose 2) • [y, x]` vanishes, for odd `p` because `p` divides `p choose 2`, and for `p = 2`
because the degree-zero brackets vanish. -/
theorem IsPowerful.gradedPow_add_zero (hp : p.Prime) (hG : IsPowerful p G)
    (x y : gradedPiece p G 0) :
    gradedPow p G 0 (x + y) = gradedPow p G 0 x + gradedPow p G 0 y := by
  rcases hp.eq_two_or_odd' with rfl | hodd
  · rw [gradedPow_add_zero_of_two rfl, hG.gradedBracket_zero_zero_eq_zero_of_two, add_zero]
  · exact gradedPow_add_zero_of_odd hodd x y

/-- **In a powerful group `π` commutes with the bracket of two degree-zero classes**, for a prime
`p`: `π [x, y] = [π x, y]` in `gr_2(G)`. -/
theorem IsPowerful.gradedPow_gradedBracket_zero_zero (hp : p.Prime) (hG : IsPowerful p G)
    (x y : gradedPiece p G 0) :
    gradedPow p G 1 (gradedBracket p G 0 0 x y) = gradedBracket p G 1 0 (gradedPow p G 0 x) y := by
  rcases hp.eq_two_or_odd' with rfl | hodd
  · -- Both sides vanish: `[x, y] = 0`, and then `[π x, y] = π [x, y] + [[x, y], x] = 0`.
    have h := gradedPow_gradedBracket_zero_zero x y
    simp only [hG.gradedBracket_zero_zero_eq_zero_of_two x y, map_zero, AddMonoidHom.zero_apply,
      smul_zero, add_zero, gradedPow_zero] at h ⊢
    exact h
  · exact gradedPow_gradedBracket_left_zero_of_odd hodd x y

/-- The degree-zero case of `TauCeti.IsPowerful.gradedPow_surjective`: since `λ_1 = Gᵖ`, the
degree-one piece is spanned by the `p`-power classes, and `π` is additive. -/
private theorem IsPowerful.gradedPow_zero_surjective (hp : p.Prime) (hG : IsPowerful p G)
    (h : IsOpen (pLowerCentralSeries p G (0 + 1 + 1) : Set G)) :
    Function.Surjective (gradedPow p G 0) := by
  let f : gradedPiece p G 0 →+ gradedPiece p G 1 :=
    AddMonoidHom.mk' (gradedPow p G 0) (hG.gradedPow_add_zero hp)
  have hrange : LinearMap.range (f.toZModLinearMap p) = ⊤ := by
    have htop : gradedPieceOf p (closedPowerSubgroup p G) 1 = ⊤ := by
      rw [hG.closedPowerSubgroup_eq_pLowerCentralSeries_one]
      exact gradedPieceOf_pLowerCentralSeries_self 1
    rw [eq_top_iff, ← htop, closedPowerSubgroup_eq_topologicalClosure,
      gradedPieceOf_topologicalClosure h]
    refine gradedPieceOf_closure_le ?_ ?_
    · rintro _ ⟨g, rfl⟩
      exact pow_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero p g)
    · rintro _ ⟨g, rfl⟩
      exact ⟨gradedMkZero p G g, by
        rw [AddMonoidHom.coe_toZModLinearMap, AddMonoidHom.mk'_apply, gradedPow_gradedMkZero]⟩
  intro z
  exact LinearMap.range_eq_top.mp hrange z

/-- **`π` maps `gr_k(G)` onto `gr_{k+1}(G)` in a powerful group** whose term `λ_{k+2}` is open, for
a prime `p`. The piece `gr_{k+1}(G)` is spanned by `π gr_k(G)` and the brackets `[x, y]` with
`x ∈ gr_k(G)` and `y ∈ gr_0(G)`; by induction `x = π w`, and `[π w, y] = π [w, y]`. -/
theorem IsPowerful.gradedPow_surjective (hp : p.Prime) (hG : IsPowerful p G) {k : ℕ}
    (h : IsOpen (pLowerCentralSeries p G (k + 1 + 1) : Set G)) :
    Function.Surjective (gradedPow p G k) := by
  induction k with
  | zero => exact hG.gradedPow_zero_surjective hp h
  | succ k ih =>
    have ih := ih (Subgroup.isOpen_mono (pLowerCentralSeries_antitone (by omega)) h)
    have hf (x : gradedPiece p G (k + 1)) :
        (gradedPowAddMonoidHom p G (Nat.le_add_left 1 k)).toZModLinearMap p x =
          gradedPow p G (k + 1) x := by
      rw [AddMonoidHom.coe_toZModLinearMap, gradedPowAddMonoidHom_apply]
    have hrange : LinearMap.range
        ((gradedPowAddMonoidHom p G (Nat.le_add_left 1 k)).toZModLinearMap p) = ⊤ := by
      refine eq_top_of_forall_gradedPow_mem_of_forall_gradedBracket_mem h (fun x ↦ ⟨x, hf x⟩)
        fun x y ↦ ?_
      obtain ⟨w, rfl⟩ := ih x
      refine ⟨gradedBracket p G k 0 w y, ?_⟩
      rw [hf]
      cases k with
      | zero => exact hG.gradedPow_gradedBracket_zero_zero hp w y
      | succ k => exact gradedPow_gradedBracket_left_zero (Nat.le_add_left 1 k) w y
    intro z
    obtain ⟨x, hx⟩ := LinearMap.range_eq_top.mp hrange z
    exact ⟨x, (hf x).symm.trans hx⟩

/-- **`π^k` maps `gr_0(G)` onto `gr_k(G)` in a powerful group** whose term `λ_{k+1}` is open, for a
prime `p`: every element of `λ_k` is congruent modulo `λ_{k+1}` to a `p^k`-th power. -/
theorem IsPowerful.gradedPowIter_surjective (hp : p.Prime) (hG : IsPowerful p G) {k : ℕ}
    (h : IsOpen (pLowerCentralSeries p G (k + 1) : Set G)) :
    Function.Surjective (gradedPowIter p G k) := by
  induction k with
  | zero => exact fun x ↦ ⟨x, gradedPowIter_zero x⟩
  | succ k ih =>
    intro z
    obtain ⟨y, rfl⟩ := hG.gradedPow_surjective hp h z
    obtain ⟨x, rfl⟩ := ih (Subgroup.isOpen_mono (pLowerCentralSeries_antitone (by omega)) h) y
    exact ⟨x, gradedPowIter_succ k x⟩

/-! ### The lower `p`-series of a powerful pro-`p` group -/

section ProP

variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **The lower `p`-series of a powerful pro-`p` group is its series of power subgroups**:
`λ_k = G^{p^k}` for a topologically finitely generated powerful pro-`p` group and a prime `p`. -/
theorem IsPowerful.pLowerCentralSeries_eq_closedPowerSubgroup (hp : p.Prime) (hG : IsPowerful p G)
    (hP : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G) (k : ℕ) :
    pLowerCentralSeries p G k = closedPowerSubgroup (p ^ k) G := by
  refine le_antisymm ?_ ((closedPowerSubgroup_le_iff (isClosed_pLowerCentralSeries k)).mpr
    fun g ↦ by simpa using pow_pow_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero p g) k)
  -- By Nakayama's lemma it suffices that `λ_k ≤ G^{p^k} λ_{k+1}`, which is the surjectivity of
  -- `π^k` onto `gr_k(G)`.
  refine hP.le_of_le_topologicalClosure_sup_pLowerCentralStep hp isClosed_closedPowerSubgroup ?_
  rw [← pLowerCentralSeries_succ]
  refine fun x hx ↦ Subgroup.le_topologicalClosure _ ?_
  obtain ⟨g, hg⟩ := hG.gradedPowIter_surjective hp (hfg.isOpen_pLowerCentralSeries hp (k + 1))
    (gradedMk p G k ⟨x, hx⟩)
  obtain ⟨g, rfl⟩ := gradedMkZero_surjective g
  rw [gradedPowIter_gradedMkZero, gradedMk_eq_gradedMk_iff, QuotientGroup.eq] at hg
  simpa using mul_mem_sup (pow_mem_closedPowerSubgroup (n := p ^ k) g) hg

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- The closed power subgroup of `λ_k`, computed in `λ_k`, is closed in `G`. -/
private theorem isClosed_map_subtype_closedPowerSubgroup_pLowerCentralSeries (n k : ℕ) :
    IsClosed (((closedPowerSubgroup n (pLowerCentralSeries p G k)).map
      (pLowerCentralSeries p G k).subtype : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  exact (isClosed_pLowerCentralSeries k).isClosedEmbedding_subtypeVal.isClosedMap _
    isClosed_closedPowerSubgroup

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- The closed power subgroup `G^{p^k n}` lies in the closed power subgroup `(λ_k)ⁿ`, computed in
`λ_k`: a `p^k n`-th power is the `n`-th power of a `p^k`-th power, which lies in `λ_k`. -/
private theorem closedPowerSubgroup_le_map_subtype_closedPowerSubgroup (n k : ℕ) :
    closedPowerSubgroup (p ^ k * n) G ≤
      (closedPowerSubgroup n (pLowerCentralSeries p G k)).map
        (pLowerCentralSeries p G k).subtype := by
  refine (closedPowerSubgroup_le_iff
    (isClosed_map_subtype_closedPowerSubgroup_pLowerCentralSeries n k)).mpr fun g ↦ ?_
  have hg : g ^ p ^ k ∈ pLowerCentralSeries p G k := by
    simpa using pow_pow_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero p g) k
  exact ⟨⟨g ^ p ^ k, hg⟩ ^ n, pow_mem_closedPowerSubgroup _, by simp [pow_mul]⟩

/-- **Each term of the lower `p`-series of a powerful pro-`p` group is the closed power subgroup of
the previous one**: `λ_{k+1} = (λ_k)ᵖ`, the closed subgroup generated by the `p`-th powers of the
elements of `λ_k`, for a topologically finitely generated powerful pro-`p` group and a prime
`p`. -/
theorem IsPowerful.map_subtype_closedPowerSubgroup_pLowerCentralSeries (hp : p.Prime)
    (hG : IsPowerful p G) (hP : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G) (k : ℕ) :
    (closedPowerSubgroup p (pLowerCentralSeries p G k)).map (pLowerCentralSeries p G k).subtype =
      pLowerCentralSeries p G (k + 1) := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    refine (closedPowerSubgroup_le_iff ((isClosed_pLowerCentralSeries (k + 1)).preimage
      continuous_subtypeVal)).mpr fun x ↦ ?_
    rw [Subgroup.mem_comap, coe_subtype, Subgroup.coe_pow]
    exact pow_mem_pLowerCentralSeries x.property
  · rw [hG.pLowerCentralSeries_eq_closedPowerSubgroup hp hP hfg, pow_succ]
    exact closedPowerSubgroup_le_map_subtype_closedPowerSubgroup p k

/-- **The terms of the lower `p`-series of a powerful pro-`p` group are powerful**, for a
topologically finitely generated powerful pro-`p` group and a prime `p`. For `k ≥ 1` the
commutators of `λ_k` lie in `λ_{2k+1} ≤ λ_{k+2} = G^{p^{k+2}}`, which lies in `(λ_k)ᵖ` and, for
`p = 2`, in `(λ_k)⁴`. -/
theorem isPowerful_pLowerCentralSeries (hp : p.Prime) (hG : IsPowerful p G) (hP : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) (k : ℕ) :
    IsPowerful p (pLowerCentralSeries p G k) := by
  rw [isPowerful_iff,
    ← Subgroup.map_le_map_iff_of_injective (pLowerCentralSeries p G k).subtype_injective,
    commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  refine le_trans ?_ (closedPowerSubgroup_le_map_subtype_closedPowerSubgroup _ k)
  cases k with
  | zero =>
    rw [pLowerCentralSeries_zero, pow_zero, one_mul, ← commutator_def, ← isPowerful_iff]
    exact hG
  | succ k =>
    have hq : (if p = 2 then 4 else p) ∣ p ^ 2 := by
      split_ifs with h2
      · subst h2; norm_num
      · exact dvd_pow_self p two_ne_zero
    have hdvd : p ^ (k + 1) * (if p = 2 then 4 else p) ∣ p ^ (k + 1 + 2) := by
      rw [pow_add p (k + 1) 2]
      exact mul_dvd_mul_left _ hq
    calc ⁅pLowerCentralSeries p G (k + 1), pLowerCentralSeries p G (k + 1)⁆
        ≤ pLowerCentralSeries p G (k + 1 + (k + 1) + 1) := commutator_pLowerCentralSeries_le _ _
      _ ≤ pLowerCentralSeries p G (k + 1 + 2) := pLowerCentralSeries_antitone (by omega)
      _ = closedPowerSubgroup (p ^ (k + 1 + 2)) G :=
        hG.pLowerCentralSeries_eq_closedPowerSubgroup hp hP hfg _
      _ ≤ _ := closedPowerSubgroup_le_of_dvd hdvd

/-- **The successive indices of the lower `p`-series of a powerful group are non-increasing**:
`[λ_{k+1} : λ_{k+2}] ≤ [λ_k : λ_{k+1}]` for a topologically finitely generated powerful profinite
group and a prime `p`, because `π` maps `gr_k(G)` onto `gr_{k+1}(G)`. -/
theorem IsPowerful.relIndex_pLowerCentralSeries_succ_le (hp : p.Prime) (hG : IsPowerful p G)
    (hfg : IsTopologicallyFinitelyGenerated G) (k : ℕ) :
    (pLowerCentralSeries p G (k + 1 + 1)).relIndex (pLowerCentralSeries p G (k + 1)) ≤
      (pLowerCentralSeries p G (k + 1)).relIndex (pLowerCentralSeries p G k) := by
  have := hfg.finite_gradedPiece hp k
  have h := Nat.card_le_card_of_surjective (gradedPow p G k)
    (hG.gradedPow_surjective hp (hfg.isOpen_pLowerCentralSeries hp (k + 1 + 1)))
  exact h

end ProP

end TauCeti
