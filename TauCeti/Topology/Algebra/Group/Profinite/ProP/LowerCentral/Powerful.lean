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
* each `λ_k` is again powerful (`TauCeti.IsPowerful.to_pLowerCentralSeries`);
* the successive indices `[λ_k : λ_{k+1}]` are non-increasing
  (`TauCeti.IsPowerful.relIndex_pLowerCentralSeries_succ_le`), since `π` maps `gr_k(G)` onto
  `gr_{k+1}(G)`.

In a torsion-free powerful group `π` is moreover **injective**
(`TauCeti.IsPowerful.gradedPow_injective`), so the indices are constant. Modulo `λ_{j+2}` the
`p`-th power of a product `y * w` with `w ∈ λ_j` is `y ^ p * w ^ p`
(`TauCeti.IsPowerful.mk_mul_pow`); for `p = 2` this uses that powerfulness kills every bracket with
a degree-zero class (`TauCeti.IsPowerful.gradedBracket_eq_zero_of_two`). Successive approximation
then shows that if `x ^ p ∈ λ_{k+2}`, some `z ≡ x` modulo `λ_{k+1}` has `z ^ p = 1`
(`TauCeti.IsPowerful.exists_pow_eq_one_of_pow_mem`), which is `z = 1` in a torsion-free group.

## Main results

* `TauCeti.IsPowerful.gradedPow_add_zero`,
  `TauCeti.IsPowerful.gradedPow_gradedBracket_zero_zero`: in a powerful group `π` is additive in
  degree zero and `π [x, y] = [π x, y]` for degree-zero classes, for every prime `p`.
* `TauCeti.IsPowerful.gradedPow_surjective`, `TauCeti.IsPowerful.gradedPowIter_surjective`: `π`
  maps `gr_k(G)` onto `gr_{k+1}(G)`, and `π^k` maps `gr_0(G)` onto `gr_k(G)`.
* `TauCeti.IsPowerful.pLowerCentralSeries_eq_closedPowerSubgroup`: `λ_k = G^{p^k}`.
* `TauCeti.IsPowerful.map_subtype_closedPowerSubgroup_pLowerCentralSeries`: `λ_{k+1} = (λ_k)ᵖ`.
* `TauCeti.IsPowerful.to_pLowerCentralSeries`: `λ_k` is powerful.
* `TauCeti.IsPowerful.relIndex_pLowerCentralSeries_succ_le`:
  `[λ_{k+1} : λ_{k+2}] ≤ [λ_k : λ_{k+1}]`.
* `TauCeti.IsPowerful.gradedBracket_eq_zero_of_two`: for `p = 2`, `[x, y] = 0` for `y` of degree
  zero, that is `⁅λ_j, G⁆ ≤ λ_{j+2}`.
* `TauCeti.IsPowerful.mk_mul_pow`: `(y * w) ^ p ≡ y ^ p * w ^ p` modulo `λ_{j+2}` for `w ∈ λ_j`.
* `TauCeti.IsPowerful.exists_pow_eq_one_of_pow_mem`: if `x ^ p ∈ λ_{k+2}`, then some `z ≡ x`
  modulo `λ_{k+1}` satisfies `z ^ p = 1`.
* `TauCeti.IsPowerful.gradedPow_injective`: in a torsion-free powerful group `π` is injective.

## References

* J. D. Dixon, M. P. F. du Sautoy, A. Mann and D. Segal, *Analytic pro-`p` groups*, second
  edition, Chapter 3, Theorem 3.6, and Chapter 4, Theorem 4.5.
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
  have h4 : closedPowerSubgroup 4 G ≤ pLowerCentralSeries 2 G 2 := by
    simpa using closedPowerSubgroup_pow_le_pLowerCentralSeries (G := G) (p := 2) 2
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

/-- **The brackets with degree-zero classes vanish in a powerful group at `p = 2`**:
`[x, y] = 0` for `x ∈ gr_j(G)` and `y ∈ gr_0(G)`, as soon as `λ_{j+1}` is open. Equivalently
`⁅λ_j, G⁆ ≤ λ_{j+2}`. -/
theorem IsPowerful.gradedBracket_eq_zero_of_two (hG : IsPowerful 2 G) {j : ℕ}
    (h : IsOpen (pLowerCentralSeries 2 G (j + 1) : Set G)) (x : gradedPiece 2 G j)
    (y : gradedPiece 2 G 0) : gradedBracket 2 G j 0 x y = 0 := by
  -- In degree zero this is powerfulness; in higher degrees `x = π w` and `[π w, y] = π [w, y]`.
  induction j with
  | zero => exact hG.gradedBracket_zero_zero_eq_zero_of_two x y
  | succ j ih =>
    obtain ⟨w, rfl⟩ := hG.gradedPow_surjective Nat.prime_two h x
    have hw := ih (Subgroup.isOpen_mono (pLowerCentralSeries_antitone (by omega)) h) w
    cases j with
    | zero => rw [← hG.gradedPow_gradedBracket_zero_zero Nat.prime_two, hw, gradedPow_zero]
    | succ j => rw [← gradedPow_gradedBracket_left_zero (Nat.le_add_left 1 j), hw, gradedPow_zero]

/-- **The `p`-th power of a product with a deep factor in a powerful group**:
`(y * w) ^ p ≡ y ^ p * w ^ p` modulo `λ_{j+2}` for every `y` and every `w ∈ λ_j`, for a prime `p`,
as soon as `λ_{j+1}` is open. -/
theorem IsPowerful.mk_mul_pow (hp : p.Prime) (hG : IsPowerful p G) {j : ℕ}
    (h : IsOpen (pLowerCentralSeries p G (j + 1) : Set G)) (y : G) {w : G}
    (hw : w ∈ pLowerCentralSeries p G j) :
    (((y * w) ^ p : G) : G ⧸ pLowerCentralSeries p G (j + 1 + 1)) =
      ((y ^ p * w ^ p : G) : G ⧸ _) := by
  have hc : ⁅w, y⁆ ∈ pLowerCentralSeries p G (j + 1) :=
    commutator_mem_pLowerCentralSeries hw (mem_pLowerCentralSeries_zero p y)
  -- Modulo `λ_{j+2}` the commutator `⁅w, y⁆ ∈ λ_{j+1}` is central, so `(y * w) ^ p` is
  -- `y ^ p * w ^ p * ⁅w, y⁆ ^ (p choose 2)`. The defect lies in `λ_{j+2}`: for odd `p` because `p`
  -- divides `p choose 2`, and for `p = 2` because the bracket `[w, y]` vanishes.
  have hchoose : ⁅w, y⁆ ^ p.choose 2 ∈ pLowerCentralSeries p G (j + 1 + 1) := by
    have hmk : gradedMk p G (j + 1) ⟨_, hc⟩ = gradedBracket p G j 0
        (gradedMk p G j ⟨w, hw⟩) (gradedMkZero p G y) := by
      rw [gradedBracket_gradedMk_gradedMkZero]
    have hzero : p.choose 2 • gradedMk p G (j + 1) ⟨_, hc⟩ = 0 := by
      rcases hp.eq_two_or_odd' with rfl | hodd
      · rw [hmk, hG.gradedBracket_eq_zero_of_two h, smul_zero]
      · exact choose_two_nsmul_gradedPiece_eq_zero_of_odd hodd _
    rwa [← gradedMk_pow, gradedMk_eq_zero_iff] at hzero
  have hone :
      QuotientGroup.mk' (pLowerCentralSeries p G (j + 1 + 1)) (⁅w, y⁆ ^ p.choose 2) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hchoose
  have hcomm (g : G) : Commute (g : G ⧸ pLowerCentralSeries p G (j + 1 + 1)) (⁅w, y⁆ : G) :=
    commute_mk_of_mem_pLowerCentralSeries hc g
  simp only [← QuotientGroup.mk'_apply, map_pow, map_mul, map_commutatorElement] at hcomm hone ⊢
  rw [Commute.mul_pow_eq_pow_mul_pow_mul_commutatorElement_pow_choose_two (hcomm y) (hcomm w), hone,
    mul_one]

/-! ### The lower `p`-series of a powerful pro-`p` group -/

section ProP

variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **The lower `p`-series of a powerful pro-`p` group is its series of power subgroups**:
`λ_k = G^{p^k}` for a topologically finitely generated powerful pro-`p` group and a prime `p`. -/
theorem IsPowerful.pLowerCentralSeries_eq_closedPowerSubgroup (hp : p.Prime) (hG : IsPowerful p G)
    (hP : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G) (k : ℕ) :
    pLowerCentralSeries p G k = closedPowerSubgroup (p ^ k) G := by
  refine le_antisymm ?_ (closedPowerSubgroup_pow_le_pLowerCentralSeries k)
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
    exact closedPowerSubgroup_mul_le_map_subtype_closedPowerSubgroup
      (isClosed_pLowerCentralSeries k)
      fun g ↦ closedPowerSubgroup_pow_le_pLowerCentralSeries k (pow_mem_closedPowerSubgroup g)

/-- **The terms of the lower `p`-series of a powerful pro-`p` group are powerful**, for a
topologically finitely generated powerful pro-`p` group and a prime `p`. For `k ≥ 1` the
commutators of `λ_k` lie in `λ_{2k+1} ≤ λ_{k+2} = G^{p^{k+2}}`, which lies in `(λ_k)ᵖ` and, for
`p = 2`, in `(λ_k)⁴`. -/
theorem IsPowerful.to_pLowerCentralSeries (hp : p.Prime) (hG : IsPowerful p G) (hP : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) (k : ℕ) :
    IsPowerful p (pLowerCentralSeries p G k) := by
  rw [isPowerful_iff,
    ← Subgroup.map_le_map_iff_of_injective (pLowerCentralSeries p G k).subtype_injective,
    commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  refine le_trans ?_ (closedPowerSubgroup_mul_le_map_subtype_closedPowerSubgroup
    (isClosed_pLowerCentralSeries k)
    fun g ↦ closedPowerSubgroup_pow_le_pLowerCentralSeries k (pow_mem_closedPowerSubgroup g))
  cases k with
  | zero => simpa [commutator_def, isPowerful_iff] using hG
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
  rw [← natCard_gradedPiece, ← natCard_gradedPiece]
  exact Nat.card_le_card_of_surjective (gradedPow p G k)
    (hG.gradedPow_surjective hp (hfg.isOpen_pLowerCentralSeries hp (k + 1 + 1)))

/-- **Lifting a `p`-th power that lies too deep to an element of order dividing `p`.** In a
topologically finitely generated powerful pro-`p` group, for a prime `p`, if `x ^ p ∈ λ_{k+2}` then
some `z ≡ x` modulo `λ_{k+1}` has `z ^ p = 1`. -/
theorem IsPowerful.exists_pow_eq_one_of_pow_mem (hp : p.Prime) (hG : IsPowerful p G)
    (hP : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G) {k : ℕ} {x : G}
    (hx : x ^ p ∈ pLowerCentralSeries p G (k + 1 + 1)) :
    ∃ z : G, x⁻¹ * z ∈ pLowerCentralSeries p G (k + 1) ∧ z ^ p = 1 := by
  -- `C n` is the closed set of `z ≡ x` modulo `λ_{k+1}` with `z ^ p ∈ λ_{k+n+2}`. Each is nonempty,
  -- by successive corrections `z ↦ z * w⁻¹` with `w ∈ λ_{k+n+1}`, and compactness gives a point
  -- in all of them.
  let C (n : ℕ) : Set G := (x⁻¹ * ·) ⁻¹' (pLowerCentralSeries p G (k + 1) : Set G) ∩
    (· ^ p) ⁻¹' (pLowerCentralSeries p G (k + n + 1 + 1) : Set G)
  have hclosed (n : ℕ) : IsClosed (C n) :=
    ((isClosed_pLowerCentralSeries _).preimage (continuous_const.mul continuous_id)).inter
      ((isClosed_pLowerCentralSeries _).preimage (continuous_pow p))
  have hanti (n : ℕ) : C (n + 1) ⊆ C n :=
    Set.inter_subset_inter_right _ (Set.preimage_mono (pLowerCentralSeries_antitone (by omega)))
  have hne (n : ℕ) : (C n).Nonempty := by
    induction n with
    | zero => exact ⟨x, by simpa [C] using hx⟩
    | succ n ih =>
      obtain ⟨z, hz, hzp⟩ := ih
      -- Correct `z` by some `w ∈ λ_{k+n+1}` with `w ^ p ≡ z ^ p` modulo `λ_{k+n+3}`.
      obtain ⟨a, ha⟩ := hG.gradedPow_surjective (k := k + n + 1) hp
        (hfg.isOpen_pLowerCentralSeries hp _) (gradedMk p G _ ⟨z ^ p, hzp⟩)
      obtain ⟨w, rfl⟩ := gradedMk_surjective _ a
      rw [gradedPow_gradedMk, gradedMk_eq_gradedMk_iff, QuotientGroup.eq] at ha
      have hmul := hG.mk_mul_pow hp (hfg.isOpen_pLowerCentralSeries hp _) z (inv_mem w.property)
      rw [QuotientGroup.eq, inv_pow] at hmul
      -- `ha` says `(w ^ p)⁻¹ * z ^ p ∈ λ_{k+n+3}`, hence `z ^ p * (w ^ p)⁻¹` by normality.
      have hzw : z ^ p * ((w : G) ^ p)⁻¹ ∈ pLowerCentralSeries p G (k + n + 1 + 1 + 1) := by
        have := (pLowerCentralSeries_normal _).conj_mem _ ha ((w : G) ^ p)
        rwa [mul_inv_cancel_left] at this
      refine ⟨z * (w : G)⁻¹, ?_, ?_⟩
      · rw [Set.mem_preimage, SetLike.mem_coe, ← mul_assoc]
        exact mul_mem hz (inv_mem (pLowerCentralSeries_antitone (by omega) w.property))
      · have hmem := mul_mem hmul (inv_mem hzw)
        rwa [mul_inv_cancel_right, inv_mem_iff] at hmem
  obtain ⟨z, hz⟩ := (hclosed 0).isCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    C hanti hne hclosed
  rw [Set.mem_iInter] at hz
  refine ⟨z, (hz 0).1, Subgroup.mem_bot.mp ?_⟩
  rw [← hP.iInf_pLowerCentralSeries_eq_bot hp, Subgroup.mem_iInf]
  exact fun m ↦ pLowerCentralSeries_antitone (by omega) (hz m).2

/-- **In a torsion-free powerful group the `p`-power operator is injective**: `π` maps `gr_k(G)`
injectively to `gr_{k+1}(G)` for a topologically finitely generated, torsion-free, powerful pro-`p`
group and a prime `p`. With `TauCeti.IsPowerful.gradedPow_surjective` it is bijective. -/
theorem IsPowerful.gradedPow_injective [IsMulTorsionFree G] (hp : p.Prime) (hG : IsPowerful p G)
    (hP : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G) (k : ℕ) :
    Function.Injective (gradedPow p G k) := by
  -- `π` is additive in every degree, so it suffices that its kernel is trivial.
  have hadd (a b : gradedPiece p G k) : gradedPow p G k (a + b) =
      gradedPow p G k a + gradedPow p G k b := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact hG.gradedPow_add_zero hp a b
    · exact gradedPow_add_of_one_le hk a b
  refine (injective_iff_map_eq_zero (AddMonoidHom.mk' _ hadd)).mpr fun a ha ↦ ?_
  obtain ⟨x, rfl⟩ := gradedMk_surjective k a
  rw [AddMonoidHom.mk'_apply, gradedPow_gradedMk, gradedMk_eq_zero_iff] at ha
  obtain ⟨z, hz, hzp⟩ := hG.exists_pow_eq_one_of_pow_mem hp hP hfg ha
  obtain rfl : z = 1 := IsMulTorsionFree.eq_of_pow_eq_pow_of_commute hp.ne_zero
    (Commute.one_right z) (hzp.trans (one_pow p).symm)
  rw [gradedMk_eq_zero_iff]
  simpa using hz

end ProP

end TauCeti
