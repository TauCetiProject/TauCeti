/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Regular
import TauCeti.Data.Fintype.BigOperators
import TauCeti.Algebra.Order.BigOperators.Sum.UnitWeights
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring

/-!
# Pair-color bounds for finite families of maps

A family of maps taking each coordinate into a prescribed finite cell is bounded by the
volume of its box times the density of any color required on two distinct coordinates.
The cells may overlap, and maps need not be injective. Additional pair-color or higher-order
conditions only restrict the family, so this bound applies without any regularity input.

With regularity, the number of maps is determined up to a small error. Let the coordinates be
linearly ordered, prescribe a color `c p` for each pair `p = (i, j)` with `i < j` of a set `E` of
such pairs, and suppose that the cells of every pair in `E` are disjoint and form an `ε`-regular
pair. Then the number of maps in the box realizing every prescribed color differs from the
volume of the box times the product of the prescribed color densities by at most
`#E * ε` times the volume. In a lower skeleton whose pair colors are `ε`-regular, this applies
to all pairs of any family of pairwise distinct vertex cells, with error `(n choose 2) * ε` times
the volume for `n` coordinates. No lower bound on the densities is needed.

The argument is the telescoping proof of the graph counting lemma, as in
`SimpleGraph.abs_card_induced_fin_three_sub_le` for three cells: the color indicators are
replaced by their densities one pair at a time. Once the other coordinates are fixed, the
remaining indicators split as a function of the `i`th value times a function of the `j`th value,
both with values in `[0, 1]`, so each replacement costs at most the test-function discrepancy of
the regular pair (`TauCeti.PairColorSystem.IsRegularPair.abs_sum_sum_mul_sub_le`).

## Main results

* `TauCeti.PairColorSystem.card_le_pairColorDensity_mul_prod`: the density bound for one
  prescribed pair color, without regularity.
* `TauCeti.PairColorSystem.abs_card_filter_colorOfPair_sub_prod_le`: the counting lemma for the
  prescribed colors of a set of pairs whose cells form regular pairs.
* `TauCeti.PairSkeleton3.IsPairColorRegular.abs_card_filter_colorOfPair_sub_prod_le`: the
  counting lemma for all pairs of distinct vertex cells of a regular lower skeleton.

## References

* Y. Zhao, *Graph Theory and Additive Combinatorics*, Cambridge University Press (2023),
  Chapter 4 (the graph counting lemma).
-/

public section

open Finset Fintype

namespace TauCeti

namespace PairColorSystem

variable {ι κ V : Type*} [Fintype ι]

/-- A family of maps in a finite box that requires one prescribed pair color has size at most
that pair's density times the box volume. Cells may overlap: the density denominator counts
only distinct pairs, which is at most the full rectangle size. -/
theorem card_le_pairColorDensity_mul_prod (S : PairColorSystem κ V)
    (T : Finset (ι → V)) (A : ι → Finset V) {i j : ι} (hij : i ≠ j) (c : κ)
    (hcell : ∀ g ∈ T, ∀ k, g k ∈ A k)
    (hcolor : ∀ g ∈ T, S.colorOfPair (g i) (g j) = some c) :
    (#T : ℝ) ≤ (pairColorDensity S c (A i) (A j) : ℝ) * ∏ k, (#(A k) : ℝ) := by
  classical
  let R := ∏ k ∈ univ \ {i, j}, #(A k)
  have hcount : #{g ∈ piFinset A | S.colorOfPair (g i) (g j) = some c} =
      R * #((A i ×ˢ A j).filter fun p => S.colorOfPair p.1 p.2 = some c) := by
    simp only [card_eq_sum_ones, sum_filter]
    rw [Fintype.sum_piFinset_apply_apply hij A
      (fun x y ↦ if S.colorOfPair x y = some c then (1 : ℕ) else 0)]
    simp only [sum_product, nsmul_eq_mul]
    rfl
  have hT : #T ≤ R * #((A i ×ˢ A j).filter
      fun p => S.colorOfPair p.1 p.2 = some c) := by
    rw [← hcount]
    exact card_le_card fun g hg ↦ mem_filter.mpr ⟨mem_piFinset.mpr (hcell g hg), hcolor g hg⟩
  have hvol : R * (#(A i) * #(A j)) = ∏ k, #(A k) := by
    rw [← prod_sdiff (by simp : {i, j} ⊆ (univ : Finset ι))]
    simp [R, hij, mul_comm]
  have hd : (0 : ℝ) ≤ pairColorDensity S c (A i) (A j) :=
    mod_cast pairColorDensity_nonneg S c (A i) (A j)
  have hnum := pairColorDensity_mul_card_support S c (A i) (A j)
  have hsupport : #((A i ×ˢ A j).filter fun p => p.1 ≠ p.2) ≤ #(A i) * #(A j) := by
    simpa using card_filter_le (A i ×ˢ A j) (fun p => p.1 ≠ p.2)
  have hnum' : (#((A i ×ˢ A j).filter
      fun p => S.colorOfPair p.1 p.2 = some c) : ℝ) ≤
      (pairColorDensity S c (A i) (A j) : ℝ) * (#(A i) * #(A j)) := by
    have heq : (pairColorDensity S c (A i) (A j) : ℝ) *
        #((A i ×ˢ A j).filter fun p => p.1 ≠ p.2) =
        #((A i ×ˢ A j).filter fun p => S.colorOfPair p.1 p.2 = some c) := by
      exact_mod_cast hnum
    rw [← heq]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hsupport) hd
  calc (#T : ℝ) ≤ R * #((A i ×ˢ A j).filter
          fun p => S.colorOfPair p.1 p.2 = some c) := by exact_mod_cast hT
    _ ≤ R * ((pairColorDensity S c (A i) (A j) : ℝ) * (#(A i) * #(A j))) :=
      mul_le_mul_of_nonneg_left hnum' (Nat.cast_nonneg R)
    _ = (pairColorDensity S c (A i) (A j) : ℝ) * ∏ k, (#(A k) : ℝ) := by
      rw [mul_left_comm]
      congr 1
      exact_mod_cast hvol

section Counting

open Function

variable [LinearOrder ι] [DecidableEq κ] {ε : ℝ}

/-- The indicator that the ordered pair `(x, y)` has color `c`. -/
private noncomputable def colorWeight (S : PairColorSystem κ V) (c : κ) (x y : V) : ℝ :=
  if S.colorOfPair x y = some c then 1 else 0

private lemma colorWeight_nonneg (S : PairColorSystem κ V) (c : κ) (x y : V) :
    0 ≤ colorWeight S c x y := by
  unfold colorWeight; split_ifs <;> norm_num

private lemma colorWeight_le_one (S : PairColorSystem κ V) (c : κ) (x y : V) :
    colorWeight S c x y ≤ 1 := by
  unfold colorWeight; split_ifs <;> norm_num

/-- The weight of a map `g` for the colored pairs in `E`: the indicator that `g` realizes each
of their colors. -/
private noncomputable def routeWeight (S : PairColorSystem κ V)
    (c : {p : ι × ι // p.1 < p.2} → κ) (E : Finset {p : ι × ι // p.1 < p.2}) (g : ι → V) : ℝ :=
  ∏ q ∈ E, colorWeight S (c q) (g q.1.1) (g q.1.2)

omit [Fintype ι] in
/-- With every coordinate except the two coordinates of `p` fixed by `h`, the weight of a set
`E` of pairs not containing `p` is a function of the value at `p.1.1` times a function of the
value at `p.1.2`. -/
private lemma routeWeight_update_update (S : PairColorSystem κ V)
    (c : {p : ι × ι // p.1 < p.2} → κ) {E : Finset {p : ι × ι // p.1 < p.2}}
    {p : {p : ι × ι // p.1 < p.2}} (hp : p ∉ E) (h : ι → V) (x y : V) :
    routeWeight S c E (update (update h p.1.1 x) p.1.2 y) =
      (∏ q ∈ E with q.1.1 ≠ p.1.2 ∧ q.1.2 ≠ p.1.2,
          colorWeight S (c q) (update h p.1.1 x q.1.1) (update h p.1.1 x q.1.2)) *
        ∏ q ∈ E with ¬(q.1.1 ≠ p.1.2 ∧ q.1.2 ≠ p.1.2),
          colorWeight S (c q) (update h p.1.2 y q.1.1) (update h p.1.2 y q.1.2) := by
  rw [routeWeight, ← prod_filter_mul_prod_filter_not E fun q ↦ q.1.1 ≠ p.1.2 ∧ q.1.2 ≠ p.1.2]
  congr 1
  · refine prod_congr rfl fun q hq ↦ ?_
    obtain ⟨-, h₁, h₂⟩ := mem_filter.mp hq
    rw [update_of_ne h₁, update_of_ne h₂]
  · refine prod_congr rfl fun q hq ↦ ?_
    obtain ⟨hqE, hqj⟩ := mem_filter.mp hq
    -- Two distinct strictly ordered pairs share at most one coordinate, so `q`, which meets
    -- `p.1.2`, avoids `p.1.1`.
    have hqi : q.1.1 ≠ p.1.1 ∧ q.1.2 ≠ p.1.1 := by
      have hqp : q.1 ≠ p.1 := Subtype.coe_injective.ne (ne_of_mem_of_not_mem hqE hp)
      have := q.2
      have := p.2
      rw [Ne, Prod.ext_iff] at hqp
      grind
    -- Away from `p.1.1`, overwriting `p.1.1` and then `p.1.2` agrees with overwriting `p.1.2`.
    have key (l : ι) (hl : l ≠ p.1.1) :
        update (update h p.1.1 x) p.1.2 y l = update h p.1.2 y l := by
      rcases eq_or_ne l p.1.2 with rfl | hlj
      · simp
      · simp [hlj, hl]
    rw [key _ hqi.1, key _ hqi.2]

/-- One telescoping step: testing the deviation of the color indicator of a pair `p` from its
density against the weight of the remaining pairs gives at most `ε` times the box volume. -/
private lemma abs_sum_colorWeight_sub_mul_routeWeight_le (S : PairColorSystem κ V)
    (A : ι → Finset V) (c : {p : ι × ι // p.1 < p.2} → κ) {E : Finset {p : ι × ι // p.1 < p.2}}
    {p : {p : ι × ι // p.1 < p.2}} (hp : p ∉ E) (hdisj : Disjoint (A p.1.1) (A p.1.2))
    (hreg : S.IsRegularPair ε (A p.1.1) (A p.1.2)) :
    |∑ g ∈ piFinset A, (colorWeight S (c p) (g p.1.1) (g p.1.2) -
        pairColorDensity S (c p) (A p.1.1) (A p.1.2)) * routeWeight S c E g| ≤
      ε * ∏ l, (#(A l) : ℝ) := by
  classical
  have hε : 0 ≤ ε := haveI : Nonempty κ := ⟨c p⟩; hreg.nonneg
  rcases (piFinset A).eq_empty_or_nonempty with hbox | ⟨g₀, hg₀⟩
  · rw [hbox, Finset.sum_empty, abs_zero]
    exact mul_nonneg hε (prod_nonneg fun _ _ ↦ Nat.cast_nonneg _)
  have hg₀' := mem_piFinset.mp hg₀
  have hne : p.1.1 ≠ p.1.2 := p.2.ne
  have hsplit := sum_piFinset_eq_sum_filter_sum_sum_update (M := ℝ) hne A (hg₀' _) (hg₀' _)
  -- The volume of the box is `#B * #(A p.1.1) * #(A p.1.2)`, where `B` fixes both coordinates.
  have hvol : (∏ l, (#(A l) : ℝ)) =
      #{h ∈ piFinset A | h p.1.1 = g₀ p.1.1 ∧ h p.1.2 = g₀ p.1.2} *
        (#(A p.1.1) * #(A p.1.2)) := by
    have := hsplit fun _ ↦ (1 : ℝ)
    simp only [sum_const, nsmul_eq_mul, mul_one] at this
    rw [← this, card_piFinset]
    push_cast
    ring
  rw [hsplit, hvol]
  refine (abs_sum_le_card_nsmul (B := ε * #(A p.1.1) * #(A p.1.2)) fun h _ ↦ ?_).trans_eq
    (by rw [nsmul_eq_mul]; ring)
  -- With the other coordinates fixed by `h`, the weight of `E` splits into a function `f` of the
  -- value at `p.1.1` times a function `g` of the value at `p.1.2`, both in `[0, 1]`.
  set f : V → ℝ := fun x ↦ ∏ q ∈ E with q.1.1 ≠ p.1.2 ∧ q.1.2 ≠ p.1.2,
    colorWeight S (c q) (update h p.1.1 x q.1.1) (update h p.1.1 x q.1.2)
  set g : V → ℝ := fun y ↦ ∏ q ∈ E with ¬(q.1.1 ≠ p.1.2 ∧ q.1.2 ≠ p.1.2),
    colorWeight S (c q) (update h p.1.2 y q.1.1) (update h p.1.2 y q.1.2)
  have hterm : ∑ x ∈ A p.1.1, ∑ y ∈ A p.1.2,
      (colorWeight S (c p) (update (update h p.1.1 x) p.1.2 y p.1.1)
          (update (update h p.1.1 x) p.1.2 y p.1.2) -
        pairColorDensity S (c p) (A p.1.1) (A p.1.2)) *
        routeWeight S c E (update (update h p.1.1 x) p.1.2 y) =
      ∑ x ∈ A p.1.1, ∑ y ∈ A p.1.2, f x * g y *
        ((if S.colorOfPair x y = some (c p) then 1 else 0) -
          pairColorDensity S (c p) (A p.1.1) (A p.1.2)) := by
    refine sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ ?_
    rw [routeWeight_update_update S c hp, update_of_ne hne, update_self, update_self,
      colorWeight]
    ring
  rw [hterm]
  have hw₀ (q : {p : ι × ι // p.1 < p.2}) (x y : V) := colorWeight_nonneg S (c q) x y
  have hw₁ (q : {p : ι × ι // p.1 < p.2}) (x y : V) := colorWeight_le_one S (c q) x y
  exact hreg.abs_sum_sum_mul_sub_le hdisj _ (fun _ _ ↦ prod_nonneg fun _ _ ↦ hw₀ _ _ _)
    (fun _ _ ↦ prod_le_one₀ (fun _ _ ↦ hw₀ _ _ _) fun _ _ ↦ hw₁ _ _ _)
    (fun _ _ ↦ prod_nonneg fun _ _ ↦ hw₀ _ _ _)
    (fun _ _ ↦ prod_le_one₀ (fun _ _ ↦ hw₀ _ _ _) fun _ _ ↦ hw₁ _ _ _)

/-- **Counting lemma for prescribed pair colors.** Let `A` assign a cell to each coordinate of a
linearly ordered finite type, and prescribe a color `c p` for every pair `p = (i, j)`, `i < j`,
of a set `E`. If the cells of every pair in `E` are disjoint and form an `ε`-regular pair, then
the number of maps `g` with `g i ∈ A i` realizing every prescribed color differs from
`∏ i, |A i|` times the product over `E` of the prescribed color densities by at most
`#E * ε * ∏ i, |A i|`. -/
theorem abs_card_filter_colorOfPair_sub_prod_le (S : PairColorSystem κ V) (A : ι → Finset V)
    (c : {p : ι × ι // p.1 < p.2} → κ) (E : Finset {p : ι × ι // p.1 < p.2})
    (hdisj : ∀ p ∈ E, Disjoint (A p.1.1) (A p.1.2))
    (hreg : ∀ p ∈ E, S.IsRegularPair ε (A p.1.1) (A p.1.2)) :
    |(#{g ∈ piFinset A | ∀ p ∈ E, S.colorOfPair (g p.1.1) (g p.1.2) = some (c p)} : ℝ) -
        (∏ i, (#(A i) : ℝ)) * ∏ p ∈ E, (pairColorDensity S (c p) (A p.1.1) (A p.1.2) : ℝ)| ≤
      #E * ε * ∏ i, (#(A i) : ℝ) := by
  set P : ℝ := ∏ i, (#(A i) : ℝ)
  have hP : 0 ≤ P := prod_nonneg fun _ _ ↦ Nat.cast_nonneg _
  suffices key : |∑ g ∈ piFinset A, routeWeight S c E g -
      P * ∏ p ∈ E, (pairColorDensity S (c p) (A p.1.1) (A p.1.2) : ℝ)| ≤ #E * ε * P by
    convert key using 4
    rw [natCast_card_filter]
    refine sum_congr rfl fun g _ ↦ ?_
    simp only [routeWeight, colorWeight, Finset.prod_boole]
    congr
  induction E using Finset.induction_on with
  | empty =>
    simp [routeWeight, P, card_piFinset]
  | insert p E hp ih =>
    have hdisjE : ∀ q ∈ E, Disjoint (A q.1.1) (A q.1.2) :=
      fun q hq ↦ hdisj q (mem_insert_of_mem hq)
    have hregE : ∀ q ∈ E, S.IsRegularPair ε (A q.1.1) (A q.1.2) :=
      fun q hq ↦ hreg q (mem_insert_of_mem hq)
    have hreg_p := hreg p (mem_insert_self p E)
    have hε : 0 ≤ ε := haveI : Nonempty κ := ⟨c p⟩; hreg_p.nonneg
    have hd₀ : (0 : ℝ) ≤ pairColorDensity S (c p) (A p.1.1) (A p.1.2) :=
      mod_cast pairColorDensity_nonneg _ _ _ _
    have hd₁ : (pairColorDensity S (c p) (A p.1.1) (A p.1.2) : ℝ) ≤ 1 :=
      mod_cast pairColorDensity_le_one _ _ _ _
    set d : ℝ := (pairColorDensity S (c p) (A p.1.1) (A p.1.2) : ℝ)
    have hstep := abs_sum_colorWeight_sub_mul_routeWeight_le S A c hp
      (hdisj p (mem_insert_self p E)) hreg_p
    have hih := ih hdisjE hregE
    -- Telescope: replace the indicator of `p` by its density `d`.
    have hsplit : ∑ g ∈ piFinset A, routeWeight S c (insert p E) g -
        P * ∏ q ∈ insert p E, (pairColorDensity S (c q) (A q.1.1) (A q.1.2) : ℝ) =
        ∑ g ∈ piFinset A, (colorWeight S (c p) (g p.1.1) (g p.1.2) - d) *
          routeWeight S c E g +
        d * (∑ g ∈ piFinset A, routeWeight S c E g -
          P * ∏ q ∈ E, (pairColorDensity S (c q) (A q.1.1) (A q.1.2) : ℝ)) := by
      simp only [routeWeight, prod_insert hp, sub_mul, sum_sub_distrib, ← mul_sum]
      ring
    rw [hsplit, card_insert_of_notMem hp]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ ε * P + 1 * (#E * ε * P) := by
        rw [abs_mul, abs_of_nonneg hd₀]
        gcongr
      _ = _ := by push_cast; ring

end Counting

end PairColorSystem

namespace PairSkeleton3

variable {ι κ V : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq κ] [Fintype V]
  [DecidableEq V] {S : PairSkeleton3 κ V} {ε : ℝ}

/-- **Counting lemma in a regular lower skeleton.** Let `A` assign pairwise distinct vertex
cells of an `ε`-regular lower skeleton to the coordinates of a linearly ordered finite type,
and prescribe a pair color `c p` for every pair `p = (i, j)` with `i < j`. Then the number of
maps `g` with `g i ∈ A i` realizing every prescribed color differs from `∏ i, |A i|` times the
product of the prescribed color densities by at most `(n choose 2) * ε * ∏ i, |A i|`, where `n`
is the number of coordinates. -/
theorem IsPairColorRegular.abs_card_filter_colorOfPair_sub_prod_le (h : S.IsPairColorRegular ε)
    (A : ι → Finset V) (hA : ∀ i, A i ∈ S.vertexPart.parts) (hA_inj : Function.Injective A)
    (c : {p : ι × ι // p.1 < p.2} → κ) :
    |(#{g ∈ piFinset A | ∀ p, S.pairColors.colorOfPair (g p.1.1) (g p.1.2) = some (c p)} : ℝ) -
        (∏ i, (#(A i) : ℝ)) *
          ∏ p, (pairColorDensity S.pairColors (c p) (A p.1.1) (A p.1.2) : ℝ)| ≤
      (Fintype.card ι).choose 2 * ε * ∏ i, (#(A i) : ℝ) := by
  have key := S.pairColors.abs_card_filter_colorOfPair_sub_prod_le A c univ
    (fun p _ ↦ S.vertexPart.disjoint (hA _) (hA _) (hA_inj.ne p.2.ne))
    (fun p _ ↦ h.isRegularPair (hA _) (hA _))
  simp only [mem_univ, true_imp_iff] at key
  rwa [card_univ, Fintype.card_subtype, Fintype.card_product_filter_lt] at key

end PairSkeleton3

end TauCeti
