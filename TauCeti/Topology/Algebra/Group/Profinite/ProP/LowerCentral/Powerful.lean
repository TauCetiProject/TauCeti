/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Powerful
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Subgroup
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.LowerCentralSeries
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup

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

For an arbitrary profinite powerful pro-`p` group (no finite generation needed), compactness lifts
the finite theory of `TauCeti.GroupTheory.Powerful` to give the structure of the lower `p`-series
of Dixon–du Sautoy–Mann–Segal, Theorem 3.6:

* every element of `λ_k` is a `p ^ k`-th power
  (`TauCeti.IsPowerful.mem_pLowerCentralSeries_iff_exists_pow_pow`), so `λ_k = G^{p^k}`
  (`TauCeti.IsPowerful.pLowerCentralSeries_eq_closedPowerSubgroup`) and `λ_{k+1} = (λ_k)ᵖ`
  (`TauCeti.IsPowerful.map_subtype_closedPowerSubgroup_pLowerCentralSeries`);
* each `λ_k` is again powerful (`TauCeti.IsPowerful.to_pLowerCentralSeries`) and shifts the lower
  `p`-series by `k` (`TauCeti.IsPowerful.map_subtype_pLowerCentralSeries_pLowerCentralSeries`,
  `TauCeti.IsPowerful.pLowerCentralSeries_pLowerCentralSeries_eq_subgroupOf`);
* `π` is surjective in every degree without an openness assumption
  (`TauCeti.IsPowerful.gradedPow_surjective_of_isProP`), and under topological finite generation the
  successive indices `[λ_k : λ_{k+1}]` are non-increasing
  (`TauCeti.IsPowerful.relIndex_pLowerCentralSeries_succ_le`).

For torsion lifting and injectivity of `π`, modulo `λ_{j+2}` the `p`-th power of a product
`y * w` with `w ∈ λ_j` is `y ^ p * w ^ p` (`TauCeti.IsPowerful.mk_mul_pow` under openness, and
`TauCeti.IsPowerful.mk_mul_pow_of_isProP` for any profinite powerful pro-`p` group); for `p = 2`
this uses `TauCeti.IsPowerful.gradedBracket_eq_zero_of_two` or
`TauCeti.IsPowerful.commutator_pLowerCentralSeries_top_le_add_two`. Successive approximation then
shows that if `x ^ p ∈ λ_{k+2}`, some `z ≡ x` modulo `λ_{k+1}` has `z ^ p = 1`
(`TauCeti.IsPowerful.exists_pow_eq_one_of_pow_mem`), so injectivity of `π` characterizes absence
of `p`-torsion (`TauCeti.IsPowerful.forall_eq_one_of_pow_eq_one_iff_injective_gradedPow`) and
holds in every torsion-free powerful pro-`p` group (`TauCeti.IsPowerful.gradedPow_injective`).

## Main results

* `TauCeti.IsPowerful.gradedPow_add_zero`, `TauCeti.IsPowerful.gradedPow_add`,
  `TauCeti.IsPowerful.gradedPow_gradedBracket_zero_zero`: in a powerful group `π` is additive in
  every degree and `π [x, y] = [π x, y]` for degree-zero classes, for every prime `p`.
* `TauCeti.IsPowerful.gradedPow_surjective`, `TauCeti.IsPowerful.gradedPowIter_surjective`: `π`
  maps `gr_k(G)` onto `gr_{k+1}(G)`, and `π^k` maps `gr_0(G)` onto `gr_k(G)` under openness.
* `TauCeti.IsPowerful.mem_pLowerCentralSeries_iff_exists_pow_pow`,
  `TauCeti.IsPowerful.pLowerCentralSeries_eq_closedPowerSubgroup`: every element of `λ_k` is a
  `p ^ k`-th power, and `λ_k = G^{p^k}`.
* `TauCeti.IsPowerful.map_subtype_closedPowerSubgroup_pLowerCentralSeries`: `λ_{k+1} = (λ_k)ᵖ`.
* `TauCeti.IsPowerful.commutator_pLowerCentralSeries_top_le_add_two`: for `p = 2`,
  `⁅λ_k(G), G⁆ ≤ λ_{k+2}(G)`.
* `TauCeti.IsPowerful.to_pLowerCentralSeries`,
  `TauCeti.IsPowerful.map_subtype_pLowerCentralSeries_pLowerCentralSeries`,
  `TauCeti.IsPowerful.pLowerCentralSeries_pLowerCentralSeries_eq_subgroupOf`: `λ_k` is powerful and
  shifts the lower `p`-series by `k`.
* `TauCeti.IsPowerful.gradedPow_surjective_of_isProP`,
  `TauCeti.IsPowerful.relIndex_pLowerCentralSeries_succ_le`: surjectivity of `π` in a profinite
  powerful pro-`p` group and `[λ_{k+1} : λ_{k+2}] ≤ [λ_k : λ_{k+1}]`.
* `TauCeti.IsPowerful.gradedBracket_eq_zero_of_two`: for `p = 2`, `[x, y] = 0` for `y` of degree
  zero under openness.
* `TauCeti.IsPowerful.mk_mul_pow`, `TauCeti.IsPowerful.mk_mul_pow_of_isProP`:
  `(y * w) ^ p ≡ y ^ p * w ^ p` modulo `λ_{j+2}` for `w ∈ λ_j`.
* `TauCeti.IsPowerful.exists_pow_eq_one_of_pow_mem`,
  `TauCeti.IsPowerful.forall_eq_one_of_pow_eq_one_iff_injective_gradedPow`,
  `TauCeti.IsPowerful.gradedPow_injective`: torsion lifting and injectivity of `π`.

## References

* J. D. Dixon, M. P. F. du Sautoy, A. Mann and D. Segal, *Analytic pro-`p` groups*, second
  edition, Chapter 3 (Lemma 3.4, Theorem 3.6) and Chapter 4 (Lemma 4.2, Theorem 4.5).
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

/-- **In a powerful group `π` is additive in every degree**, for a prime `p`. -/
theorem IsPowerful.gradedPow_add (hp : p.Prime) (hG : IsPowerful p G) (k : ℕ)
    (x y : gradedPiece p G k) :
    gradedPow p G k (x + y) = gradedPow p G k x + gradedPow p G k y := by
  rcases k.eq_zero_or_pos with rfl | hk
  · exact hG.gradedPow_add_zero hp x y
  · exact gradedPow_add_of_one_le hk x y

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

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
private theorem IsPowerful.quotient_openNormalSubgroup_isPowerfullyEmbedded
    (hG : IsPowerful p G) (U : OpenNormalSubgroup G) :
    (⊤ : Subgroup (G ⧸ U.toSubgroup)).IsPowerfullyEmbedded p :=
  have := QuotientGroup.discreteTopology (hN := U.isOpen)
  isPowerful_iff_isPowerfullyEmbedded_top.mp (hG.quotient U.toSubgroup)

/-- **Every element of `λ_k(G)` is a `p ^ k`-th power** (Dixon–du Sautoy–Mann–Segal,
Theorem 3.6(iii)): in a profinite powerful pro-`p` group `G`, the `k`-th term of the lower
`p`-series consists precisely of the `p ^ k`-th powers. No finite generation is needed. -/
theorem IsPowerful.mem_pLowerCentralSeries_iff_exists_pow_pow (hp : p.Prime)
    (hG : IsPowerful p G) (hP : IsProP p G) (k : ℕ) {g : G} :
    g ∈ pLowerCentralSeries p G k ↔ ∃ x : G, x ^ (p ^ k) = g := by
  have := Fact.mk hp
  refine ⟨fun hg ↦ ?_, fun ⟨x, hx⟩ ↦ hx ▸ by
    simpa using pow_pow_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero p x) k⟩
  let F : OpenNormalSubgroup G → Set G := fun U ↦
    {x : G | (x : G ⧸ U.toSubgroup) ^ (p ^ k) = (g : G ⧸ U.toSubgroup)}
  have hF_closed : ∀ U, IsClosed (F U) := fun U ↦
    have := QuotientGroup.discreteTopology (hN := U.isOpen)
    (isClosed_singleton (x := (g : G ⧸ U.toSubgroup))).preimage
      ((continuous_pow (p ^ k)).comp QuotientGroup.continuous_mk)
  have hF_nonempty : ∀ U, (F U).Nonempty := fun U ↦ by
    have := U.toSubgroup.quotient_finite_of_isOpen U.isOpen
    have hgU : (g : G ⧸ U.toSubgroup) ∈
        (⊤ : Subgroup (G ⧸ U.toSubgroup)).pLowerCentralSeries p k :=
      map_mk_pLowerCentralSeries_openNormalSubgroup U k ▸ ⟨g, hg, rfl⟩
    have hU := hG.quotient_openNormalSubgroup_isPowerfullyEmbedded U
    obtain ⟨xQ, hxQ⟩ :=
      (hU.mem_pLowerCentralSeries_iff_exists_pow_pow (isProP_iff.mp hP U) k).mp hgU
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xQ
    exact ⟨x, hxQ⟩
  have hF_dir : Directed (· ⊇ ·) F := fun U V ↦ ⟨U ⊓ V,
    fun _ hx ↦ by
      simpa [F, map_pow] using congrArg
        (QuotientGroup.mapOfLE (inf_le_left : (U ⊓ V).toSubgroup ≤ U.toSubgroup)) hx,
    fun _ hx ↦ by
      simpa [F, map_pow] using congrArg
        (QuotientGroup.mapOfLE (inf_le_right : (U ⊓ V).toSubgroup ≤ V.toSubgroup)) hx⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed F hF_dir
    hF_nonempty (fun U ↦ (hF_closed U).isCompact) hF_closed
  refine ⟨x, eq_of_inv_mul_eq_one (Subgroup.eq_one_of_mem_iInf_openNormalSubgroup fun U ↦ ?_)⟩
  exact QuotientGroup.eq.mp (by rw [QuotientGroup.mk_pow]; exact Set.mem_iInter.mp hx U)

/-- **The lower `p`-series of a powerful pro-`p` group is its series of power subgroups**
(Dixon–du Sautoy–Mann–Segal, Theorem 3.6(ii)): `λ_k = G^{p^k}` for a profinite powerful pro-`p`
group and a prime `p`. No finite generation is needed. -/
theorem IsPowerful.pLowerCentralSeries_eq_closedPowerSubgroup (hp : p.Prime) (hG : IsPowerful p G)
    (hP : IsProP p G) (k : ℕ) :
    pLowerCentralSeries p G k = closedPowerSubgroup (p ^ k) G :=
  le_antisymm
    (fun _ hg ↦ let ⟨x, hx⟩ := (hG.mem_pLowerCentralSeries_iff_exists_pow_pow hp hP k).mp hg
      hx ▸ pow_mem_closedPowerSubgroup x)
    (closedPowerSubgroup_pow_le_pLowerCentralSeries k)

/-- **Each term of the lower `p`-series of a powerful pro-`p` group is the closed power subgroup of
the previous one**: `λ_{k+1} = (λ_k)ᵖ`, the closed subgroup generated by the `p`-th powers of the
elements of `λ_k`, for a profinite powerful pro-`p` group and a prime `p`. -/
theorem IsPowerful.map_subtype_closedPowerSubgroup_pLowerCentralSeries (hp : p.Prime)
    (hG : IsPowerful p G) (hP : IsProP p G) (k : ℕ) :
    (closedPowerSubgroup p (pLowerCentralSeries p G k)).map (pLowerCentralSeries p G k).subtype =
      pLowerCentralSeries p G (k + 1) := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    refine (closedPowerSubgroup_le_iff ((isClosed_pLowerCentralSeries (k + 1)).preimage
      continuous_subtypeVal)).mpr fun x ↦ ?_
    rw [Subgroup.mem_comap, coe_subtype, Subgroup.coe_pow]
    exact pow_mem_pLowerCentralSeries x.property
  · rw [hG.pLowerCentralSeries_eq_closedPowerSubgroup hp hP, pow_succ]
    exact closedPowerSubgroup_mul_le_map_subtype_closedPowerSubgroup
      (isClosed_pLowerCentralSeries k)
      fun g ↦ closedPowerSubgroup_pow_le_pLowerCentralSeries k (pow_mem_closedPowerSubgroup g)

/-- In a profinite powerful pro-`2` group, `⁅λ_k(G), G⁆ ≤ λ_{k+2}(G)` for every `k`. -/
theorem IsPowerful.commutator_pLowerCentralSeries_top_le_add_two (hG : IsPowerful 2 G)
    (hP : IsProP 2 G) (k : ℕ) :
    ⁅pLowerCentralSeries 2 G k, (⊤ : Subgroup G)⁆ ≤ pLowerCentralSeries 2 G (k + 2) := by
  have := Fact.mk Nat.prime_two
  rw [(pLowerCentralSeries 2 G (k + 2)).eq_iInf_sup_openNormalSubgroup
      (isClosed_pLowerCentralSeries (k + 2))]
  refine le_iInf fun U ↦ ?_
  have := U.toSubgroup.quotient_finite_of_isOpen U.isOpen
  have hmap : ⁅pLowerCentralSeries 2 G k, (⊤ : Subgroup G)⁆.map (QuotientGroup.mk' U.toSubgroup) ≤
      (pLowerCentralSeries 2 G (k + 2)).map (QuotientGroup.mk' U.toSubgroup) := by
    rw [map_commutator, map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
      map_mk_pLowerCentralSeries_openNormalSubgroup U k,
      map_mk_pLowerCentralSeries_openNormalSubgroup U (k + 2)]
    have hU := hG.quotient_openNormalSubgroup_isPowerfullyEmbedded U
    exact hU.commutator_pLowerCentralSeries_top_le_add_two (isProP_iff.mp hP U) k
  intro g hg
  obtain ⟨h, hh, hgh⟩ := Subgroup.mem_map.mp (hmap ⟨g, hg, rfl⟩)
  simpa using Subgroup.mul_mem_sup hh (QuotientGroup.eq.mp hgh)

/-- **The terms of the lower `p`-series of a powerful pro-`p` group are powerful**
(Dixon–du Sautoy–Mann–Segal, Theorem 3.6(i)), for a profinite powerful pro-`p` group and a prime
`p`. For `k ≥ 1` the commutators of `λ_k` lie in `λ_{2k+1} ≤ λ_{k+2} = G^{p^{k+2}}`, which lies in
`(λ_k)ᵖ` and, for `p = 2`, in `(λ_k)⁴`. -/
theorem IsPowerful.to_pLowerCentralSeries (hp : p.Prime) (hG : IsPowerful p G) (hP : IsProP p G)
    (k : ℕ) : IsPowerful p (pLowerCentralSeries p G k) := by
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
        hG.pLowerCentralSeries_eq_closedPowerSubgroup hp hP _
      _ ≤ _ := closedPowerSubgroup_le_of_dvd hdvd

/-- **Shift invariance of the lower `p`-series** (Dixon–du Sautoy–Mann–Segal, Theorem 3.6(iv)):
in a profinite powerful pro-`p` group `G`, the `j`-th term of the lower `p`-series of `λ_k(G)`
maps onto `λ_{k+j}(G)`. -/
theorem IsPowerful.map_subtype_pLowerCentralSeries_pLowerCentralSeries (hp : p.Prime)
    (hG : IsPowerful p G) (hP : IsProP p G) (k j : ℕ) :
    (pLowerCentralSeries p (pLowerCentralSeries p G k) j).map
        (pLowerCentralSeries p G k).subtype =
      pLowerCentralSeries p G (k + j) := by
  set H := pLowerCentralSeries p G k
  have hH_proP := hP.subgroup H
  have hH_pow := hG.to_pLowerCentralSeries hp hP k
  ext g
  rw [mem_map, hG.mem_pLowerCentralSeries_iff_exists_pow_pow hp hP (k + j)]
  refine ⟨?_, fun ⟨x, hx⟩ ↦ ?_⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := (hH_pow.mem_pLowerCentralSeries_iff_exists_pow_pow hp hH_proP j).mp hy
    obtain ⟨x, hx⟩ := (hG.mem_pLowerCentralSeries_iff_exists_pow_pow hp hP k).mp z.property
    exact ⟨x, by rw [pow_add, pow_mul, hx, ← Subgroup.coe_pow, Subgroup.coe_subtype]⟩
  · let z : H :=
      ⟨x ^ (p ^ k), (hG.mem_pLowerCentralSeries_iff_exists_pow_pow hp hP k).mpr ⟨x, rfl⟩⟩
    exact ⟨z ^ (p ^ j),
      (hH_pow.mem_pLowerCentralSeries_iff_exists_pow_pow hp hH_proP j).mpr ⟨z, rfl⟩,
      by rw [← hx, coe_subtype, coe_pow, ← pow_mul, ← pow_add]⟩

/-- In a profinite powerful pro-`p` group, the `j`-th term of the lower `p`-series of `λ_k(G)`
equals `λ_{k+j}(G).subgroupOf (λ_k(G))`. -/
theorem IsPowerful.pLowerCentralSeries_pLowerCentralSeries_eq_subgroupOf (hp : p.Prime)
    (hG : IsPowerful p G) (hP : IsProP p G) (k j : ℕ) :
    pLowerCentralSeries p (pLowerCentralSeries p G k) j =
      (pLowerCentralSeries p G (k + j)).subgroupOf (pLowerCentralSeries p G k) := by
  have h := congrArg (fun K ↦ K.comap (pLowerCentralSeries p G k).subtype)
    (hG.map_subtype_pLowerCentralSeries_pLowerCentralSeries hp hP k j)
  rwa [Subgroup.comap_map_eq_self_of_injective
    (pLowerCentralSeries p G k).subtype_injective] at h

/-- **Surjectivity of `π` in a profinite powerful pro-`p` group** (Dixon–du Sautoy–Mann–Segal,
Lemma 3.4): `gradedPow p G k` is surjective in every degree `k` without an openness assumption. -/
theorem IsPowerful.gradedPow_surjective_of_isProP (hp : p.Prime) (hG : IsPowerful p G)
    (hP : IsProP p G) (k : ℕ) : Function.Surjective (gradedPow p G k) := fun z ↦ by
  obtain ⟨⟨g, hg⟩, rfl⟩ := gradedMk_surjective (k + 1) z
  obtain ⟨x, rfl⟩ := (hG.mem_pLowerCentralSeries_iff_exists_pow_pow hp hP (k + 1)).mp hg
  refine ⟨gradedMk p G k ⟨x ^ (p ^ k),
    (hG.mem_pLowerCentralSeries_iff_exists_pow_pow hp hP k).mpr ⟨x, rfl⟩⟩, ?_⟩
  rw [gradedPow_gradedMk]
  exact congrArg (gradedMk p G (k + 1))
    (Subtype.ext (by rw [Subgroup.coe_mk, ← pow_mul, ← pow_succ]))

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

/-- **The `p`-th power of a product with a deep factor in a profinite powerful pro-`p` group**:
`(y * w) ^ p ≡ y ^ p * w ^ p` modulo `λ_{j+2}` for every `y` and every `w ∈ λ_j`, for a prime `p`,
without an openness assumption. -/
theorem IsPowerful.mk_mul_pow_of_isProP (hp : p.Prime) (hG : IsPowerful p G) (hP : IsProP p G)
    {j : ℕ} (y : G) {w : G} (hw : w ∈ pLowerCentralSeries p G j) :
    (((y * w) ^ p : G) : G ⧸ pLowerCentralSeries p G (j + 1 + 1)) =
      ((y ^ p * w ^ p : G) : G ⧸ _) := by
  have hwy := commutator_mem_pLowerCentralSeries hw (mem_pLowerCentralSeries_zero p y)
  rcases hp.eq_two_or_odd' with rfl | hp_odd
  · rw [QuotientGroup.mk_mul]
    exact (QuotientGroup.commute_mk_iff.mpr
      (hG.commutator_pLowerCentralSeries_top_le_add_two hP j
        (commutator_mem_commutator hw (mem_top y)))).symm.mul_pow 2
  · simpa only [QuotientGroup.mk_pow, QuotientGroup.mk_mul] using
      QuotientGroup.mk_mul_pow_eq_of_odd hp_odd
        (commutator_mem_pLowerCentralSeries_succ hwy y)
        (commutator_mem_pLowerCentralSeries_succ hwy w)
        (pow_mem_pLowerCentralSeries hwy)

/-- **Lifting a `p`-th power that lies too deep to an element of order dividing `p`**
(Dixon–du Sautoy–Mann–Segal, Lemma 4.2): in a profinite powerful pro-`p` group, for a prime `p`,
if `x ^ p ∈ λ_{k+2}` then some `z ≡ x` modulo `λ_{k+1}` has `z ^ p = 1`. No finite generation is
needed. -/
theorem IsPowerful.exists_pow_eq_one_of_pow_mem (hp : p.Prime) (hG : IsPowerful p G)
    (hP : IsProP p G) {k : ℕ} {x : G}
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
      obtain ⟨a, ha⟩ :=
        hG.gradedPow_surjective_of_isProP hp hP (k + n + 1) (gradedMk p G _ ⟨z ^ p, hzp⟩)
      obtain ⟨w, rfl⟩ := gradedMk_surjective _ a
      rw [gradedPow_gradedMk, gradedMk_eq_gradedMk_iff, QuotientGroup.eq] at ha
      have hmul := hG.mk_mul_pow_of_isProP hp hP z (inv_mem w.property)
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
  -- Intersecting the nested compact closed sets gives a limit `z ≡ x` with `z ^ p ∈ ⋂_m λ_m = ⊥`.
  obtain ⟨z, hz⟩ := (hclosed 0).isCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    C hanti hne hclosed
  rw [Set.mem_iInter] at hz
  refine ⟨z, (hz 0).1, Subgroup.mem_bot.mp ?_⟩
  rw [← hP.iInf_pLowerCentralSeries_eq_bot hp, Subgroup.mem_iInf]
  exact fun m ↦ pLowerCentralSeries_antitone (by omega) (hz m).2

/-- **Injectivity of `gradedPow` characterizes absence of `p`-torsion** in a profinite powerful
pro-`p` group (no finite generation needed). -/
theorem IsPowerful.forall_eq_one_of_pow_eq_one_iff_injective_gradedPow (hp : p.Prime)
    (hG : IsPowerful p G) (hP : IsProP p G) :
    (∀ g : G, g ^ p = 1 → g = 1) ↔ ∀ k, Function.Injective (gradedPow p G k) := by
  refine ⟨fun htors k ↦ ?_, fun hinj g hgp ↦ ?_⟩
  · refine (injective_iff_map_eq_zero (AddMonoidHom.mk' _ (hG.gradedPow_add hp k))).mpr
      fun a ha ↦ ?_
    obtain ⟨x, rfl⟩ := gradedMk_surjective k a
    rw [AddMonoidHom.mk'_apply, gradedPow_gradedMk, gradedMk_eq_zero_iff] at ha
    obtain ⟨z, hz, hzp⟩ := hG.exists_pow_eq_one_of_pow_mem hp hP ha
    obtain rfl : z = 1 := htors z hzp
    rw [gradedMk_eq_zero_iff]
    simpa using hz
  · have := hP.isMulTorsionFree_of_gradedPow_injective hp hinj
    exact IsMulTorsionFree.eq_of_pow_eq_pow_of_commute hp.ne_zero (Commute.one_right g)
      (hgp.trans (one_pow p).symm)

/-- **In a torsion-free powerful group the `p`-power operator is injective**: `π` maps `gr_k(G)`
injectively to `gr_{k+1}(G)` for a torsion-free, powerful profinite pro-`p` group and a prime `p`.
With `TauCeti.IsPowerful.gradedPow_surjective_of_isProP` it is bijective. -/
theorem IsPowerful.gradedPow_injective [IsMulTorsionFree G] (hp : p.Prime) (hG : IsPowerful p G)
    (hP : IsProP p G) (k : ℕ) : Function.Injective (gradedPow p G k) :=
  (hG.forall_eq_one_of_pow_eq_one_iff_injective_gradedPow hp hP).mp
    (fun g hg ↦ IsMulTorsionFree.eq_of_pow_eq_pow_of_commute hp.ne_zero
      (Commute.one_right g) (hg.trans (one_pow p).symm)) k

end ProP

end TauCeti
