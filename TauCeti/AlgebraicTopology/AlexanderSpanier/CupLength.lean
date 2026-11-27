/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ENat.Lattice
public import TauCeti.AlgebraicTopology.AlexanderSpanier.Continuity
public import TauCeti.AlgebraicTopology.AlexanderSpanier.Cup.Basic
import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Cup length in Alexander–Spanier cohomology

Let `Λ` be an algebra over a commutative ring `R`. The **cup length**
`TauCeti.AlexanderSpanier.cupLength R X Λ : ℕ∞` of a space `X` is the supremum of the lengths `n`
of the nonzero cup products `a₁ ⌣ ⋯ ⌣ aₙ` of classes `aᵢ` of positive degree in the
Alexander–Spanier cohomology `H*(X; Λ)` (`TauCeti.AlexanderSpanier.IsPositiveDegreeCupProduct`),
the supremum of the empty collection being `0`.

The cup-length estimates rest on the following vanishing statements.

* **Cup products vanish on unions.** If `α` restricts to zero on an open set `U` and `β` restricts
  to zero on an open set `V`, then `α ⌣ β` restricts to zero on `U ∪ V`
  (`TauCeti.AlexanderSpanier.cohomologyMap_subtypeVal_union_cohomologyCup_eq_zero`). A class that
  restricts to zero on `U` is represented by a cocycle which is itself locally zero on `U`, and the
  cup product of a cocycle locally zero on `U` with one locally zero on `V` is locally zero on
  `U ∪ V`.
* **Products vanish on covers by their factors.** A product `a₁ ⌣ ⋯ ⌣ aₙ` of positive-degree
  classes restricts to zero on `U₁ ∪ ⋯ ∪ Uₙ` whenever each `Uᵢ` is open and `aᵢ` restricts to zero
  on it (`TauCeti.AlexanderSpanier.IsPositiveDegreeCupProduct.exists_factors`).

Together with the vanishing of positive-degree classes near points on a uniform space
(`TauCeti.AlexanderSpanier.exists_mem_nhds_cohomologyMap_subtypeVal_apply_eq_zero`), these are the
inputs of the cup-length bound for flows with a Lyapunov function on compact spaces,
`Flow.cupLength_add_one_le_encard`. Neither local contractibility nor any other local property of
`X` enters.

## Main definitions

* `TauCeti.AlexanderSpanier.IsPositiveDegreeCupProduct R X Λ n x`: the class `x` of `H*(X; Λ)` is a
  cup product `a₁ ⌣ (a₂ ⌣ ⋯ ⌣ aₙ)` of `n ≥ 1` classes of positive degree.
* `TauCeti.AlexanderSpanier.cupLength R X Λ`: the cup length of `X` with coefficients in `Λ`.

## Main results

* `TauCeti.AlexanderSpanier.cohomologyMap_subtypeVal_union_cohomologyCup_eq_zero`: cup products
  vanish on unions of open sets.
* `TauCeti.AlexanderSpanier.IsPositiveDegreeCupProduct.exists_factors`: a product of
  positive-degree classes vanishes on a union of open sets on which its factors vanish.
* `TauCeti.AlexanderSpanier.le_cupLength`, `TauCeti.AlexanderSpanier.cupLength_le_iff`: the
  defining bounds of the cup length.

## References

* E. H. Spanier, *Algebraic Topology*, McGraw–Hill, 1966, Chapter 6, Sections 6.4 to 6.6.
* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
-/

public section

noncomputable section

open CategoryTheory Filter HomologicalComplex Set Topology

universe w u v

namespace TauCeti.AlexanderSpanier

/-! ### Cup products vanish on unions -/

section Representative

variable {R : Type w} [Ring R] {X : Type u} [TopologicalSpace X] {M : Type v} [AddCommGroup M]
  [Module R M]

omit [Ring R] [Module R M] in
/-- A function on tuples which is locally zero on an open set `U` vanishes on the tuples of points
of some neighbourhood in `X` of each point of `U`. -/
private lemma exists_mem_nhds_of_isLocallyZero_restrict {U : Set X} (hU : IsOpen U) {ι : Type*}
    {φ : (ι → X) → M} (hφ : IsLocallyZero fun y : ι → U ↦ φ (Subtype.val ∘ y)) {x : X}
    (hx : x ∈ U) : ∃ N ∈ 𝓝 x, ∀ y : ι → X, (∀ i, y i ∈ N) → φ y = 0 := by
  obtain ⟨N, hN, hφN⟩ := isLocallyZero_iff.1 hφ ⟨x, hx⟩
  obtain ⟨N', hN', hN'N⟩ := (mem_nhds_subtype U ⟨x, hx⟩ N).1 hN
  exact ⟨N' ∩ U, inter_mem hN' (hU.mem_nhds hx), fun y hy ↦
    hφN (fun i ↦ ⟨y i, (hy i).2⟩) fun i ↦ hN'N (hy i).1⟩

/-- **Representatives vanishing on a subspace.** A class of `Hⁿ(X; M)` which restricts to zero on a
subspace `U` is the class of a cocycle represented by a function which is locally zero on `U`. -/
private lemma exists_isLocallyZero_restrict_of_cohomologyMap_eq_zero {U : Set X} {n : ℕ}
    (c : cohomology R X M n)
    (hc : (cohomologyMap R M (ContinuousMap.subtypeVal U) n).hom c = 0) :
    ∃ (z : (cochainComplex R X M).cycles n) (φ : (Fin (n + 1) → X) → M),
      ((cochainComplex R X M).homologyπ n).hom z = c ∧
        ((cochainComplex R X M).iCycles n).hom z = cochainClass R X M n φ ∧
          IsLocallyZero fun y : Fin (n + 1) → U ↦ φ (Subtype.val ∘ y) := by
  classical
  obtain ⟨z, rfl⟩ := (cochainComplex R X M).moduleCat_homologyπ_surjective n c
  obtain ⟨φ, hφ⟩ := cochainClass_surjective (R := R) n (((cochainComplex R X M).iCycles n).hom z)
  -- Restricting `z` to `U` gives the class of the restriction of `φ`.
  have hres : ((cochainComplex R U M).iCycles n).hom
      (HomologicalComplex.cyclesMap (cochainComplexMap R M (ContinuousMap.subtypeVal U)) n z) =
        cochainClass R U M n fun y ↦ φ (Subtype.val ∘ y) :=
    iCycles_cyclesMap_apply_of_eq_cochainClass _ hφ.symm
  rw [HomologicalComplex.moduleCat_homologyMap_homologyπ] at hc
  cases n with
  | zero =>
    -- In degree zero there are no coboundaries: the restriction of `φ` is locally zero.
    have hn : ¬ (ComplexShape.up ℕ).Rel ((ComplexShape.up ℕ).prev 0) 0 := by simp
    have h0 := HomologicalComplex.moduleCat_eq_zero_of_homologyπ_eq_zero _ hn _ hc
    refine ⟨z, φ, rfl, hφ.symm, ?_⟩
    rw [← cochainClass_eq_zero_iff (R := R), ← hres, h0, map_zero]
  | succ m =>
    -- The restriction of `φ` is a coboundary `δψ` up to a locally zero function.
    obtain ⟨y, hy⟩ := ((cochainComplex R U M).moduleCat_homologyπ_eq_zero_iff
      (m := m) (by simp) _).1 hc
    obtain ⟨ψ, rfl⟩ := cochainClass_surjective (R := R) m y
    have hψ := cochainClass_eq_cochainClass_iff.1 <| show
      cochainClass R U M (m + 1) (fun y ↦ φ (Subtype.val ∘ y)) =
        cochainClass R U M (m + 1) fun y ↦
          ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) • ψ (y ∘ Fin.succAbove i) by
      rw [← hres, ← hy, HomologicalComplex.moduleCat_iCycles_toCycles_apply,
        cochainComplex_d_cochainClass]
    -- Extend `ψ` by zero to all tuples of `X`, and subtract its coboundary from `φ`.
    let ψ' : (Fin (m + 1) → X) → M := fun y ↦ if h : ∀ i, y i ∈ U then ψ fun i ↦ ⟨y i, h i⟩ else 0
    have hψ' (y : Fin (m + 1) → U) : ψ' (Subtype.val ∘ y) = ψ y := by
      simp only [ψ', Function.comp_apply, Subtype.coe_prop, implies_true, dite_true]
    refine ⟨z - ((cochainComplex R X M).toCycles m (m + 1)).hom (cochainClass R X M m ψ'),
      φ - fun y ↦ ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) • ψ' (y ∘ Fin.succAbove i), ?_, ?_, ?_⟩
    · rw [map_sub, sub_eq_self]
      exact ((cochainComplex R X M).moduleCat_homologyπ_eq_zero_iff (m := m) (by simp) _).2
        ⟨_, rfl⟩
    · rw [map_sub, map_sub, HomologicalComplex.moduleCat_iCycles_toCycles_apply,
        cochainComplex_d_cochainClass, hφ]
    · convert hψ using 2 with y
      simp only [Pi.sub_apply]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← hψ' (y ∘ Fin.succAbove i)]
      rfl

end Representative

section Union

variable {R : Type w} [CommRing R] {X : Type u} [TopologicalSpace X] {Λ : Type v} [Ring Λ]
  [Algebra R Λ]

/-- **Cup products vanish on unions.** If a class `α` restricts to zero on an open set `U` and a
class `β` restricts to zero on an open set `V`, then their cup product `α ⌣ β` restricts to zero
on `U ∪ V`. -/
theorem cohomologyMap_subtypeVal_union_cohomologyCup_eq_zero {U V : Set X} (hU : IsOpen U)
    (hV : IsOpen V) {p q n : ℕ} (h : p + q = n) {α : cohomology R X Λ p}
    {β : cohomology R X Λ q} (hα : (cohomologyMap R Λ (ContinuousMap.subtypeVal U) p).hom α = 0)
    (hβ : (cohomologyMap R Λ (ContinuousMap.subtypeVal V) q).hom β = 0) :
    (cohomologyMap R Λ (ContinuousMap.subtypeVal (U ∪ V)) n).hom
      (cohomologyCup R X Λ p q n h α β) = 0 := by
  obtain ⟨z, φ, rfl, hzφ, hφ⟩ := exists_isLocallyZero_restrict_of_cohomologyMap_eq_zero α hα
  obtain ⟨w, ψ, rfl, hwψ, hψ⟩ := exists_isLocallyZero_restrict_of_cohomologyMap_eq_zero β hβ
  rw [cohomologyCup_homologyπ, HomologicalComplex.moduleCat_homologyMap_homologyπ]
  -- The restriction of the product cocycle is already zero as a cochain on `U ∪ V`.
  have hzw : ((cochainComplex R X Λ).iCycles n).hom
      (TauCeti.CochainComplex.moduleCatCyclesMap₂ (cup R X Λ) (fun _ _ _ h a b ↦ d_cup h a b)
        p q n h z w) =
        cochainClass R X Λ n fun y ↦ φ (y ∘ Fin.castLE (by omega)) *
          ψ (y ∘ fun i ↦ Fin.cast (by omega) (Fin.natAdd p i)) := by
    rw [TauCeti.CochainComplex.iCycles_moduleCatCyclesMap₂, hzφ, hwψ, cup_cochainClass]
  suffices hc : (HomologicalComplex.cyclesMap
      (cochainComplexMap R Λ (ContinuousMap.subtypeVal (U ∪ V))) n).hom
        (TauCeti.CochainComplex.moduleCatCyclesMap₂ (cup R X Λ) (fun _ _ _ h a b ↦ d_cup h a b)
          p q n h z w) = 0 by
    rw [hc, map_zero]
  refine HomologicalComplex.moduleCat_iCycles_injective (cochainComplex R (U ∪ V : Set X) Λ) n ?_
  rw [iCycles_cyclesMap_apply_of_eq_cochainClass _ hzw, map_zero, cochainClass_eq_zero_iff]
  refine isLocallyZero_iff.2 fun x ↦ ?_
  rcases x.property with hxU | hxV
  · obtain ⟨N, hN, hφN⟩ := exists_mem_nhds_of_isLocallyZero_restrict hU hφ hxU
    refine ⟨Subtype.val ⁻¹' N, continuous_subtypeVal.continuousAt.preimage_mem_nhds hN,
      fun y hy ↦ ?_⟩
    exact mul_eq_zero_of_left (hφN _ fun i ↦ hy _) _
  · obtain ⟨N, hN, hψN⟩ := exists_mem_nhds_of_isLocallyZero_restrict hV hψ hxV
    refine ⟨Subtype.val ⁻¹' N, continuous_subtypeVal.continuousAt.preimage_mem_nhds hN,
      fun y hy ↦ ?_⟩
    exact mul_eq_zero_of_right _ (hψN _ fun i ↦ hy _)

end Union

/-! ### Cup length -/

section CupLength

variable (R : Type w) [CommRing R] (X : Type u) [TopologicalSpace X] (Λ : Type v) [Ring Λ]
  [Algebra R Λ]

/-- `IsPositiveDegreeCupProduct R X Λ n x`: the class `x ∈ Hᵈ(X; Λ)` of Alexander–Spanier
cohomology is a cup product `a₁ ⌣ (a₂ ⌣ ⋯ ⌣ aₙ)` of `n` classes `aᵢ ∈ H^{pᵢ}(X; Λ)` of positive
degree `pᵢ ≠ 0`, nested to the right, so that `n ≥ 1` and `d = p₁ + ⋯ + pₙ`. -/
inductive IsPositiveDegreeCupProduct : (n : ℕ) → {d : ℕ} → cohomology R X Λ d → Prop
  /-- A single class of positive degree is a product of length one. -/
  | single {p : ℕ} (hp : p ≠ 0) (a : cohomology R X Λ p) : IsPositiveDegreeCupProduct 1 a
  /-- A class of positive degree cupped with a product of length `n` is a product of length
  `n + 1`. -/
  | cup {n p q d : ℕ} (hp : p ≠ 0) (h : p + q = d) (a : cohomology R X Λ p)
      {y : cohomology R X Λ q} (hy : IsPositiveDegreeCupProduct n y) :
      IsPositiveDegreeCupProduct (n + 1) (cohomologyCup R X Λ p q d h a y)

/-- The **cup length** of a space `X` in Alexander–Spanier cohomology with coefficients in `Λ`: the
supremum of the lengths `n` of the nonzero cup products `a₁ ⌣ ⋯ ⌣ aₙ` of classes of positive
degree in `H*(X; Λ)` (`TauCeti.AlexanderSpanier.IsPositiveDegreeCupProduct`). It is `0` when
every class of positive degree vanishes, and `⊤` when there are nonzero such products of every
length. -/
def cupLength : ℕ∞ :=
  ⨆ (n : ℕ) (_ : ∃ (d : ℕ) (x : cohomology R X Λ d), IsPositiveDegreeCupProduct R X Λ n x ∧
    x ≠ 0), (n : ℕ∞)

variable {R X Λ}

/-- The defining property of the cup length: it bounds the length of every nonzero product of
positive-degree classes. -/
theorem le_cupLength {n d : ℕ} {x : cohomology R X Λ d}
    (hx : IsPositiveDegreeCupProduct R X Λ n x) (hx0 : x ≠ 0) : (n : ℕ∞) ≤ cupLength R X Λ :=
  le_iSup₂_of_le (f := fun (n : ℕ) _ ↦ (n : ℕ∞)) n ⟨d, x, hx, hx0⟩ le_rfl

/-- The cup length is at most `m` exactly when every nonzero product of positive-degree classes has
length at most `m`. -/
theorem cupLength_le_iff {m : ℕ∞} :
    cupLength R X Λ ≤ m ↔ ∀ (n d : ℕ) (x : cohomology R X Λ d),
      IsPositiveDegreeCupProduct R X Λ n x → x ≠ 0 → (n : ℕ∞) ≤ m := by
  simp only [cupLength, iSup₂_le_iff, forall_exists_index, and_imp]

/-- **A product vanishes on a union of open sets on which its factors vanish.** A product
`a₁ ⌣ ⋯ ⌣ aₙ` of positive-degree classes restricts to zero on `U₁ ∪ ⋯ ∪ Uₙ` whenever each `Uᵢ` is
open and the factor `aᵢ` restricts to zero on `Uᵢ`. The factors are recorded with their degrees as
`a : Fin n → Σ p, Hᵖ(X; Λ)`. -/
theorem IsPositiveDegreeCupProduct.exists_factors {n d : ℕ} {x : cohomology R X Λ d}
    (hx : IsPositiveDegreeCupProduct R X Λ n x) :
    ∃ a : Fin n → Σ p, cohomology R X Λ p, (∀ i, (a i).1 ≠ 0) ∧
      ∀ U : Fin n → Set X, (∀ i, IsOpen (U i)) →
        (∀ i, (cohomologyMap R Λ (ContinuousMap.subtypeVal (U i)) (a i).1).hom (a i).2 = 0) →
          (cohomologyMap R Λ (ContinuousMap.subtypeVal (⋃ i, U i)) d).hom x = 0 := by
  induction hx with
  | @single p hp a =>
    refine ⟨fun _ ↦ ⟨p, a⟩, fun _ ↦ hp, fun U _ hU ↦ ?_⟩
    exact cohomologyMap_subtypeVal_apply_eq_zero_of_subset R Λ
      (iUnion_subset fun i ↦ by rw [Subsingleton.elim i 0]) (hU 0)
  | @cup n p q d hp h a y _ ih =>
    obtain ⟨b, hb, hby⟩ := ih
    refine ⟨Fin.cons ⟨p, a⟩ b, fun i ↦ ?_, fun U hUo hU ↦ ?_⟩
    · cases i using Fin.cases with
      | zero => exact hp
      | succ j => exact hb j
    have ha : (cohomologyMap R Λ (ContinuousMap.subtypeVal (U 0)) p).hom a = 0 := hU 0
    have hy0 : (cohomologyMap R Λ (ContinuousMap.subtypeVal (⋃ i : Fin n, U i.succ)) q).hom y =
        0 := by
      refine hby (fun i ↦ U i.succ) (fun i ↦ hUo i.succ) fun i ↦ ?_
      have hi := hU i.succ
      rw [Fin.cons_succ] at hi
      exact hi
    refine cohomologyMap_subtypeVal_apply_eq_zero_of_subset R Λ ?_
      (cohomologyMap_subtypeVal_union_cohomologyCup_eq_zero (U := U 0) (V := ⋃ i : Fin n, U i.succ)
        (hUo 0) (isOpen_iUnion fun i ↦ hUo i.succ) h ha hy0)
    refine iUnion_subset fun i ↦ ?_
    cases i using Fin.cases with
    | zero => exact subset_union_left
    | succ j => exact (subset_iUnion (fun k ↦ U k.succ) j).trans subset_union_right

end CupLength

end TauCeti.AlexanderSpanier
