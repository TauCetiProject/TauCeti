/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Complement.AlternatingFour
public import TauCeti.GroupTheory.Complement.Invariant.Internal
public import TauCeti.GroupTheory.Complement.Sylow
public import TauCeti.GroupTheory.Perm.FinFour.Matching
import TauCeti.Algebra.Group.Subgroup.ZPowers

/-!
# Complements, crossed projections, and invariant-complement witnesses for the Klein four-group

This module instantiates the complement, crossed-projection, and prime-power invariant-complement
theorems on concrete subgroups of `alternatingGroup (Fin 4)` and `Equiv.Perm (Fin 4)`:

1. **Conjugation convention and crossed projections `A₄ → V₄`**:
   Using the three perfect-matching double transpositions
   `M₀ = (0 1)(2 3)`, `M₁ = (0 3)(1 2)`, `M₂ = (0 2)(1 3)` of `Fin 4`
   (`TauCeti.symmetricGroupFourMatching`), the three-cycle `g = (0 1 2)` satisfies
   `g • M₀ = M₁ ≠ M₂ = g⁻¹ • M₀`, witnessing the difference between left and right conjugation on
   `V₄`. Evaluating the four normalized crossed projections
   `alternatingGroup.kleinFourCrossedProjection` on `g` gives `c_0 g = M₀`, `c_1 g = M₁`,
   `c_2 g = M₂`, and `c_3 g = 1`, taking all four values in `V₄`; moreover
   `c_3 (g * M₀) = M₁ ≠ M₀ = c_3 g * c_3 M₀`, witnessing non-multiplicativity explicitly.

2. **Sylow detection and external `C₃`-invariant complements on `A₄` over `V₄`**:
   `IsPGroup.exists_isComplement'_iff_sylow` applies to `N = kleinFour (Fin 4)` (`p = 2`), where
   every Sylow `2`-subgroup equals `N` itself and admits the trivial local complement `⊥`.
   Under the conjugation action of `C₃ = ⟨(0 1 2)⟩` (`q = 3 ≠ 2 = p`),
   `Subgroup.exists_invariant_complement` produces a `C₃`-invariant complement, and among the four
   complements of `V₄` in `A₄` the unique `C₃`-invariant one is the stabilizer of `3 : Fin 4`.

3. **Invariant local complements in `S₄` with `W = A₄` and `N = V₄`**:
   * For `A = ⟨(1 2 3)⟩` (`q = 3 ≠ 2 = p`), `Subgroup.exists_invariant_local_complement` applies,
     and among the four local complements of `N` in `W`, `A` normalizes a unique one: the image of
     `MulAction.stabilizer (alternatingGroup (Fin 4)) 0` (which equals `A` itself).
   * For `A₂ = ⟨(1 2)⟩` (`q = 2 = p`), two of the four local complements (the stabilizers of the
     two fixed points `0` and `3` of `(1 2)`) remain `A₂`-normalized, showing that `p ≠ q` is
     sufficient but not necessary for an invariant local complement to exist.

4. **Sharpness of `p ≠ q`: `V₄` under `C₂` (`p = q = 2`)**:
   Inside `Equiv.Perm (Fin 4)`, let `V` be the image of `kleinFour (Fin 4)` and let `C₂ = ⟨(0 1)⟩`
   act on `V` by conjugation. The order-`2` subgroup `N₀ = ⟨M₀⟩` of `V` is normal, abelian, and
   centralized by `C₂`, and has exactly two local complements in the Sylow `2`-subgroup `V`,
   namely `⟨M₁⟩` and `⟨M₂⟩`. Conjugation by `(0 1)` swaps `M₁` and `M₂`, so neither complement is
   `C₂`-invariant. This yields concrete `p = q = 2` counterexamples to the conclusions of both
   `Subgroup.exists_invariant_local_complement` and `Subgroup.exists_invariant_complement` when all
   other hypotheses hold.
-/

public section

open scoped IsMulCommutative Pointwise

namespace TauCeti.Examples.KleinFourComplement

open Equiv Equiv.Perm alternatingGroup

attribute [local instance] Subgroup.conjugationAction

theorem card_fin_four : Nat.card (Fin 4) = 4 :=
  Nat.card_eq_fintype_card.trans rfl

/-! ### Double transpositions in `kleinFour (Fin 4)` and explicit `A₄ → V₄` witnesses -/

/-- The double transposition of the `m`-th perfect matching of `Fin 4`, viewed as an element of
`alternatingGroup.kleinFour (Fin 4)`: `0 ↦ (0 1)(2 3)`, `1 ↦ (0 3)(1 2)`, `2 ↦ (0 2)(1 3)`. -/
def kleinFourMatching (m : Fin 3) : kleinFour (Fin 4) :=
  ⟨⟨symmetricGroupFourMatching m, symmetricGroupFourMatching_mem_alternatingGroup m⟩,
    Subgroup.subset_closure
      (cycleType_eq_two_two_iff_exists_symmetricGroupFourMatching.mpr ⟨m, rfl⟩)⟩

@[simp]
theorem coe_kleinFourMatching (m : Fin 3) :
    ((kleinFourMatching m : kleinFour (Fin 4)) : Perm (Fin 4)) = symmetricGroupFourMatching m :=
  (rfl)

theorem kleinFourMatching_injective : Function.Injective kleinFourMatching := by
  intro m₁ m₂ h
  apply symmetricGroupFourMatching_injective
  exact congrArg (fun v : kleinFour (Fin 4) => ((v : alternatingGroup (Fin 4)) : Perm (Fin 4))) h

/-- Every element of `kleinFour (Fin 4)` is either `1` or `kleinFourMatching m` for some
`m : Fin 3`. -/
theorem eq_one_or_exists_kleinFourMatching (v : kleinFour (Fin 4)) :
    v = 1 ∨ ∃ m : Fin 3, v = kleinFourMatching m := by
  have hv := v.property
  rw [← SetLike.mem_coe, coe_kleinFour_of_card_eq_four card_fin_four] at hv
  rcases hv with h1 | hct
  · left
    exact Subtype.ext (Set.mem_singleton_iff.mp h1)
  · right
    obtain ⟨m, hm⟩ := cycleType_eq_two_two_iff_exists_symmetricGroupFourMatching.mp hct
    exact ⟨m, Subtype.ext (Subtype.ext hm)⟩

/-- The three-cycle `(0 1 2)` in `alternatingGroup (Fin 4)`. -/
def threeCycleZeroOneTwo : alternatingGroup (Fin 4) :=
  ⟨[0, 1, 2].formPerm, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[simp]
theorem coe_threeCycleZeroOneTwo :
    (threeCycleZeroOneTwo : Perm (Fin 4)) = [0, 1, 2].formPerm := (rfl)

/-- Left conjugation by `g = (0 1 2)` sends `M₀ = (0 1)(2 3)` to `M₁ = (0 3)(1 2)`. -/
theorem threeCycleZeroOneTwo_smul_matching_zero :
    threeCycleZeroOneTwo • kleinFourMatching 0 = kleinFourMatching 1 := by
  rw [← Subtype.coe_inj, ← Subtype.coe_inj, Subgroup.coe_conjugationAction_smul,
    Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_kleinFourMatching,
    coe_kleinFourMatching, coe_threeCycleZeroOneTwo, symmetricGroupFourMatching_zero,
    symmetricGroupFourMatching_one]
  decide

/-- Right conjugation `g⁻¹ • M₀ = g⁻¹ * M₀ * g` by `g = (0 1 2)` sends `M₀ = (0 1)(2 3)` to
`M₂ = (0 2)(1 3)`. -/
theorem threeCycleZeroOneTwo_inv_smul_matching_zero :
    threeCycleZeroOneTwo⁻¹ • kleinFourMatching 0 = kleinFourMatching 2 := by
  rw [← Subtype.coe_inj, ← Subtype.coe_inj, Subgroup.coe_conjugationAction_smul,
    Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, coe_kleinFourMatching,
    coe_kleinFourMatching, coe_threeCycleZeroOneTwo, symmetricGroupFourMatching_zero,
    symmetricGroupFourMatching_two]
  decide

/-- Left and right conjugation by `(0 1 2)` disagree on `(0 1)(2 3)` in `kleinFour (Fin 4)`. -/
theorem threeCycleZeroOneTwo_smul_ne_inv_smul :
    threeCycleZeroOneTwo • kleinFourMatching 0 ≠
      threeCycleZeroOneTwo⁻¹ • kleinFourMatching 0 := by
  rw [threeCycleZeroOneTwo_smul_matching_zero, threeCycleZeroOneTwo_inv_smul_matching_zero]
  exact fun h => absurd (kleinFourMatching_injective h) (by decide)

/-- Values of the four normalized crossed projections `A₄ → V₄` on `g = (0 1 2)`. -/
theorem kleinFourCrossedProjection_zero_threeCycle :
    kleinFourCrossedProjection card_fin_four (0 : Fin 4) threeCycleZeroOneTwo =
      kleinFourMatching 0 := by
  rw [kleinFourCrossedProjection_eq_iff, Subgroup.smul_def, Subgroup.smul_def,
    Subgroup.smul_def, Perm.smul_def, Perm.smul_def, coe_kleinFourMatching,
    coe_threeCycleZeroOneTwo, symmetricGroupFourMatching_zero]
  decide

theorem kleinFourCrossedProjection_one_threeCycle :
    kleinFourCrossedProjection card_fin_four (1 : Fin 4) threeCycleZeroOneTwo =
      kleinFourMatching 1 := by
  rw [kleinFourCrossedProjection_eq_iff, Subgroup.smul_def, Subgroup.smul_def,
    Subgroup.smul_def, Perm.smul_def, Perm.smul_def, coe_kleinFourMatching,
    coe_threeCycleZeroOneTwo, symmetricGroupFourMatching_one]
  decide

theorem kleinFourCrossedProjection_two_threeCycle :
    kleinFourCrossedProjection card_fin_four (2 : Fin 4) threeCycleZeroOneTwo =
      kleinFourMatching 2 := by
  rw [kleinFourCrossedProjection_eq_iff, Subgroup.smul_def, Subgroup.smul_def,
    Subgroup.smul_def, Perm.smul_def, Perm.smul_def, coe_kleinFourMatching,
    coe_threeCycleZeroOneTwo, symmetricGroupFourMatching_two]
  decide

theorem kleinFourCrossedProjection_three_threeCycle :
    kleinFourCrossedProjection card_fin_four (3 : Fin 4) threeCycleZeroOneTwo = 1 := by
  rw [kleinFourCrossedProjection_eq_one_iff, Subgroup.smul_def, Perm.smul_def,
    coe_threeCycleZeroOneTwo]
  decide

/-- Explicit witness that the crossed projection `c_3 : A₄ → V₄` is not multiplicative: for
`g = (0 1 2)` and `n = (0 1)(2 3)`, `c_3 (g * n) = (0 3)(1 2)` whereas
`c_3 g * c_3 n = (0 1)(2 3)`. -/
theorem kleinFourCrossedProjection_three_mul_matching_zero :
    kleinFourCrossedProjection card_fin_four (3 : Fin 4)
        (threeCycleZeroOneTwo * kleinFourMatching 0) =
      kleinFourMatching 1 ∧
    kleinFourCrossedProjection card_fin_four (3 : Fin 4) threeCycleZeroOneTwo *
        kleinFourCrossedProjection card_fin_four (3 : Fin 4) (kleinFourMatching 0) =
      kleinFourMatching 0 := by
  have hfix : threeCycleZeroOneTwo • (3 : Fin 4) = 3 := by
    rw [Subgroup.smul_def, Perm.smul_def, coe_threeCycleZeroOneTwo]
    decide
  refine ⟨?_, ?_⟩
  · rw [kleinFourCrossedProjection_mul_coe_of_stabilizer card_fin_four 3 hfix,
      threeCycleZeroOneTwo_smul_matching_zero]
  · rw [kleinFourCrossedProjection_three_threeCycle, kleinFourCrossedProjection_coe, one_mul]

theorem kleinFourCrossedProjection_three_mul_ne :
    kleinFourCrossedProjection card_fin_four (3 : Fin 4)
      (threeCycleZeroOneTwo * kleinFourMatching 0) ≠
    kleinFourCrossedProjection card_fin_four (3 : Fin 4) threeCycleZeroOneTwo *
      kleinFourCrossedProjection card_fin_four (3 : Fin 4) (kleinFourMatching 0) := by
  rw [kleinFourCrossedProjection_three_mul_matching_zero.1,
    kleinFourCrossedProjection_three_mul_matching_zero.2]
  exact fun h => absurd (kleinFourMatching_injective h) (by decide)

/-! ### Sylow detection and external `C₃`-invariant complements for `A₄` over `V₄` -/

/-- `kleinFour (Fin 4)` is a `2`-group (`|V₄| = 2²`). -/
theorem isPGroup_two_kleinFour_fin_four : IsPGroup 2 (kleinFour (Fin 4)) :=
  IsPGroup.of_card (n := 2) (kleinFour_card_of_card_eq_four card_fin_four)

/-- Sylow detection (`IsPGroup.exists_isComplement'_iff_sylow`) certifies that `kleinFour (Fin 4)`
has a complement in `alternatingGroup (Fin 4)` from the trivial local complement `⊥` inside any
Sylow `2`-subgroup `P` (since `P = kleinFour (Fin 4)`). -/
theorem exists_isComplement'_kleinFour_of_sylow
    (P : Sylow 2 (alternatingGroup (Fin 4))) :
    ∃ D : Subgroup (alternatingGroup (Fin 4)), (kleinFour (Fin 4)).IsComplement' D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ := (kleinFour_isKleinFour card_fin_four).isMulCommutative
  rw [isPGroup_two_kleinFour_fin_four.exists_isComplement'_iff_sylow P,
    two_sylow_eq_kleinFour_of_card_eq_four card_fin_four P]
  exact ⟨⊥, Subgroup.isLocalComplement_self_left.mpr rfl⟩

/-- The acting `3`-group `C₃ = ⟨(0 1 2)⟩` in `ConjAct (alternatingGroup (Fin 4))`. -/
def conjThreeCycleZeroOneTwoSubgroup : Subgroup (ConjAct (alternatingGroup (Fin 4))) :=
  Subgroup.zpowers (ConjAct.toConjAct threeCycleZeroOneTwo)

theorem isPGroup_three_conjThreeCycleZeroOneTwoSubgroup :
    IsPGroup 3 conjThreeCycleZeroOneTwoSubgroup :=
  IsPGroup.of_card_dvd_pow (n := 1) <| by
    have h3 : threeCycleZeroOneTwo ^ 3 = 1 := by
      rw [← Subtype.coe_inj, Subgroup.coe_pow, coe_threeCycleZeroOneTwo, Subgroup.coe_one]
      decide
    rw [conjThreeCycleZeroOneTwoSubgroup, Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, h3, map_one])

/-- `Subgroup.exists_invariant_complement` applies to the conjugation action of `C₃ = ⟨(0 1 2)⟩`
on `alternatingGroup (Fin 4)` (`p = 2 ≠ 3 = q`), producing a `C₃`-invariant complement of
`kleinFour (Fin 4)`. -/
theorem exists_invariant_complement_kleinFour_three
    (P : Sylow 2 (alternatingGroup (Fin 4))) :
    ∃ D : Subgroup (alternatingGroup (Fin 4)),
      (kleinFour (Fin 4)).IsComplement' D ∧
        ∀ a : conjThreeCycleZeroOneTwoSubgroup, ∀ d ∈ D, a • d ∈ D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ := (kleinFour_isKleinFour card_fin_four).isMulCommutative
  refine Subgroup.exists_invariant_complement (kleinFour (Fin 4)) isPGroup_two_kleinFour_fin_four
    isPGroup_three_conjThreeCycleZeroOneTwoSubgroup (by decide)
    (fun a n hn => instNormalKleinFour.conj_mem n hn (ConjAct.ofConjAct (a : ConjAct _))) P ?_
  rw [two_sylow_eq_kleinFour_of_card_eq_four card_fin_four P]
  exact ⟨⊥, Subgroup.isLocalComplement_self_left.mpr rfl⟩

/-- Among the four complements of `kleinFour (Fin 4)` in `alternatingGroup (Fin 4)`, the unique
complement invariant under conjugation by `C₃ = ⟨(0 1 2)⟩` is the stabilizer of `3 : Fin 4`. -/
theorem isComplement'_kleinFour_and_invariant_threeCycle_iff
    (D : Subgroup (alternatingGroup (Fin 4))) :
    ((kleinFour (Fin 4)).IsComplement' D ∧
        ∀ a : conjThreeCycleZeroOneTwoSubgroup, ∀ d ∈ D, a • d ∈ D) ↔
      D = MulAction.stabilizer (alternatingGroup (Fin 4)) (3 : Fin 4) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hD, hinv⟩
    obtain ⟨x, rfl⟩ := (isComplement'_kleinFour_iff_exists_stabilizer card_fin_four D).mp hD
    clear hD
    let a₀ : conjThreeCycleZeroOneTwoSubgroup := ⟨ConjAct.toConjAct threeCycleZeroOneTwo,
      Subgroup.mem_zpowers _⟩
    have hnorm : threeCycleZeroOneTwo ∈
        Subgroup.normalizer (MulAction.stabilizer (alternatingGroup (Fin 4)) x) := by
      rw [Subgroup.mem_normalizer_iff]
      refine fun d => ⟨fun hd => hinv a₀ d hd, fun hd => ?_⟩
      have heq : (a₀⁻¹ : conjThreeCycleZeroOneTwoSubgroup) •
          (threeCycleZeroOneTwo * d * threeCycleZeroOneTwo⁻¹) = d := by
        rw [Subgroup.smul_def, Subgroup.coe_inv, ConjAct.smul_def, ConjAct.ofConjAct_inv,
          ConjAct.ofConjAct_toConjAct]
        group
      exact heq ▸ hinv a₀⁻¹ (threeCycleZeroOneTwo * d * threeCycleZeroOneTwo⁻¹) hd
    clear hinv a₀
    rw [normalizer_stabilizer_of_card_eq_four card_fin_four x, MulAction.mem_stabilizer_iff,
      Subgroup.smul_def, Perm.smul_def, coe_threeCycleZeroOneTwo] at hnorm
    have hx3 : x = 3 := by
      revert x hnorm
      decide
    rw [hx3]
  · rintro rfl
    refine ⟨isComplement'_kleinFour_stabilizer card_fin_four 3, fun a d hd => ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.property
    have hg3 : threeCycleZeroOneTwo ∈
        MulAction.stabilizer (alternatingGroup (Fin 4)) (3 : Fin 4) := by
      rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, Perm.smul_def, coe_threeCycleZeroOneTwo]
      decide
    rw [Subgroup.smul_def, ← hk, ← map_zpow, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
    exact mul_mem (mul_mem (zpow_mem hg3 k) hd) (inv_mem (zpow_mem hg3 k))

/-! ### Invariant local complements in `S₄` with `W = A₄` and `N = V₄` -/

/-- The image of `kleinFour (Fin 4)` inside `Equiv.Perm (Fin 4)`. -/
def symmKleinFour : Subgroup (Perm (Fin 4)) :=
  (kleinFour (Fin 4)).map (alternatingGroup (Fin 4)).subtype

instance : symmKleinFour.Normal := by
  dsimp only [symmKleinFour]
  infer_instance

theorem isMulCommutative_symmKleinFour : IsMulCommutative symmKleinFour := by
  let _ := (kleinFour_isKleinFour card_fin_four).isMulCommutative
  exact Subgroup.map_isMulCommutative (kleinFour (Fin 4)) (alternatingGroup (Fin 4)).subtype

theorem card_symmKleinFour : Nat.card symmKleinFour = 4 := by
  rw [symmKleinFour, Subgroup.card_map_of_injective (alternatingGroup (Fin 4)).subtype_injective]
  exact kleinFour_card_of_card_eq_four card_fin_four

theorem isPGroup_two_symmKleinFour : IsPGroup 2 symmKleinFour :=
  IsPGroup.of_card (n := 2) card_symmKleinFour

theorem mem_symmKleinFour_iff (σ : Perm (Fin 4)) :
    σ ∈ symmKleinFour ↔ σ = 1 ∨ ∃ m : Fin 3, σ = symmetricGroupFourMatching m := by
  rw [symmKleinFour, ← ker_symmetricGroupFourMatchingHom, mem_ker_symmetricGroupFourMatchingHom_iff]

/-- The subgroup `A = ⟨(1 2 3)⟩` of `Equiv.Perm (Fin 4)` of order `3`. -/
def symmThreeCycleSubgroup : Subgroup (Perm (Fin 4)) :=
  Subgroup.zpowers ([1, 2, 3].formPerm : Perm (Fin 4))

theorem isPGroup_three_symmThreeCycleSubgroup : IsPGroup 3 symmThreeCycleSubgroup :=
  IsPGroup.of_card_dvd_pow (n := 1) <| by
    rw [symmThreeCycleSubgroup, Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by decide)

/-- The local complements of `symmKleinFour` in `alternatingGroup (Fin 4)` inside `Perm (Fin 4)`
are precisely the images of the four point stabilizers of `alternatingGroup (Fin 4)`. -/
theorem isLocalComplement_symmKleinFour_iff (D : Subgroup (Perm (Fin 4))) :
    symmKleinFour.IsLocalComplement D (alternatingGroup (Fin 4)) ↔
      ∃ a : Fin 4,
        D = (MulAction.stabilizer (alternatingGroup (Fin 4)) a).map
          (alternatingGroup (Fin 4)).subtype := by
  have hsub : symmKleinFour.subgroupOf (alternatingGroup (Fin 4)) = kleinFour (Fin 4) :=
    Subgroup.comap_map_eq_self_of_injective (alternatingGroup (Fin 4)).subtype_injective _
  have : (symmKleinFour.subgroupOf (alternatingGroup (Fin 4))).Normal := by
    rw [hsub]
    infer_instance
  refine ⟨fun h => ?_, ?_⟩
  · have hcomp : (kleinFour (Fin 4)).IsComplement' (D.subgroupOf (alternatingGroup (Fin 4))) := by
      rw [← hsub]
      exact h.isComplement'_subgroupOf
    obtain ⟨a, ha⟩ := (isComplement'_kleinFour_iff_exists_stabilizer card_fin_four _).mp hcomp
    exact ⟨a, by rw [← ha, Subgroup.map_subgroupOf_eq_of_le h.right_le]⟩
  · rintro ⟨a, rfl⟩
    have h := (Subgroup.isLocalComplement_top_iff.mpr
      (isComplement'_kleinFour_stabilizer card_fin_four a)).map
      (alternatingGroup (Fin 4)).subtype_injective
    simpa only [symmKleinFour, Subgroup.map_top, Subgroup.range_subtype] using h

/-- `Subgroup.exists_invariant_local_complement` applies to `W = A₄`, `N = V₄`, and `A = ⟨(1 2 3)⟩`
in `S₄` (`p = 2 ≠ 3 = q`), producing an `A`-normalized local complement of `V₄` in `A₄`. -/
theorem exists_invariant_local_complement_symmKleinFour
    (P : Sylow 2 (alternatingGroup (Fin 4))) :
    ∃ D : Subgroup (Perm (Fin 4)),
      symmKleinFour.IsLocalComplement D (alternatingGroup (Fin 4)) ∧
        symmThreeCycleSubgroup ≤ Subgroup.normalizer D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ := isMulCommutative_symmKleinFour
  have hsub : symmKleinFour.subgroupOf (alternatingGroup (Fin 4)) = kleinFour (Fin 4) :=
    Subgroup.comap_map_eq_self_of_injective (alternatingGroup (Fin 4)).subtype_injective _
  have : (symmKleinFour.subgroupOf (alternatingGroup (Fin 4))).Normal := by
    rw [hsub]
    infer_instance
  refine Subgroup.exists_invariant_local_complement (alternatingGroup (Fin 4))
    (Subgroup.map_subtype_le _) Subgroup.le_normalizer_of_normal Subgroup.le_normalizer_of_normal
    isPGroup_two_symmKleinFour isPGroup_three_symmThreeCycleSubgroup (by decide) P ?_
  rw [two_sylow_eq_kleinFour_of_card_eq_four card_fin_four P]
  exact ⟨⊥, Subgroup.isLocalComplement_self_left.mpr rfl⟩

/-- Among the four local complements of `V₄` in `A₄`, a subgroup `D` is normalized by
`A = ⟨(1 2 3)⟩` if and only if `D` is the `A₄`-stabilizer of `0 : Fin 4` (which equals `A`). -/
theorem isLocalComplement_symmKleinFour_and_threeCycle_le_normalizer_iff
    (D : Subgroup (Perm (Fin 4))) :
    symmKleinFour.IsLocalComplement D (alternatingGroup (Fin 4)) ∧
        symmThreeCycleSubgroup ≤ Subgroup.normalizer D ↔
      D = (MulAction.stabilizer (alternatingGroup (Fin 4)) (0 : Fin 4)).map
        (alternatingGroup (Fin 4)).subtype := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hD, hnorm⟩
    obtain ⟨a, rfl⟩ := (isLocalComplement_symmKleinFour_iff D).mp hD
    clear hD
    rw [normalizer_map_subtype_stabilizer_of_card_eq_four card_fin_four a, symmThreeCycleSubgroup,
      Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, Perm.smul_def] at hnorm
    have ha0 : a = 0 := by
      revert a hnorm
      decide
    rw [ha0]
  · rintro rfl
    refine ⟨(isLocalComplement_symmKleinFour_iff _).mpr ⟨0, rfl⟩, ?_⟩
    rw [normalizer_map_subtype_stabilizer_of_card_eq_four card_fin_four 0, symmThreeCycleSubgroup,
      Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, Perm.smul_def]
    decide

/-- At `p = q = 2`, the order-`2` subgroup `⟨(1 2)⟩` of `S₄` still normalizes two of the four
local complements of `V₄` in `A₄` (those fixing `0` and `3`), showing that `p ≠ q` in
`Subgroup.exists_invariant_local_complement` is sufficient but not necessary. -/
theorem isLocalComplement_symmKleinFour_and_swap_one_two_le_normalizer_iff
    (D : Subgroup (Perm (Fin 4))) :
    symmKleinFour.IsLocalComplement D (alternatingGroup (Fin 4)) ∧
        Subgroup.zpowers (swap (1 : Fin 4) 2) ≤ Subgroup.normalizer D ↔
      D = (MulAction.stabilizer (alternatingGroup (Fin 4)) (0 : Fin 4)).map
          (alternatingGroup (Fin 4)).subtype ∨
        D = (MulAction.stabilizer (alternatingGroup (Fin 4)) (3 : Fin 4)).map
          (alternatingGroup (Fin 4)).subtype := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hD, hnorm⟩
    obtain ⟨a, rfl⟩ := (isLocalComplement_symmKleinFour_iff D).mp hD
    clear hD
    rw [normalizer_map_subtype_stabilizer_of_card_eq_four card_fin_four a, Subgroup.zpowers_le,
      MulAction.mem_stabilizer_iff, Perm.smul_def] at hnorm
    have ha : a = 0 ∨ a = 3 := by
      revert a hnorm
      decide
    rcases ha with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · refine ⟨(isLocalComplement_symmKleinFour_iff _).mpr ⟨0, rfl⟩, ?_⟩
      rw [normalizer_map_subtype_stabilizer_of_card_eq_four card_fin_four 0, Subgroup.zpowers_le,
        MulAction.mem_stabilizer_iff, Perm.smul_def]
      decide
    · refine ⟨(isLocalComplement_symmKleinFour_iff _).mpr ⟨3, rfl⟩, ?_⟩
      rw [normalizer_map_subtype_stabilizer_of_card_eq_four card_fin_four 3, Subgroup.zpowers_le,
        MulAction.mem_stabilizer_iff, Perm.smul_def]
      decide

/-! ### Sharpness of `p ≠ q`: `V₄` under `C₂` has no invariant complement (`p = q = 2`) -/

/-- The order-`2` subgroup `⟨M_m⟩` of `symmKleinFour` generated by the `m`-th matching. -/
def matchingSubgroup (m : Fin 3) : Subgroup (Perm (Fin 4)) :=
  Subgroup.zpowers (symmetricGroupFourMatching m)

/-- The acting `2`-subgroup `C₂ = ⟨(0 1)⟩` of `Equiv.Perm (Fin 4)`. -/
def swapZeroOneSubgroup : Subgroup (Perm (Fin 4)) :=
  Subgroup.zpowers (swap (0 : Fin 4) 1)

theorem matching_sq_eq_one (m : Fin 3) : symmetricGroupFourMatching m ^ 2 = 1 := by
  fin_cases m <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, symmetricGroupFourMatching_zero,
      symmetricGroupFourMatching_one, symmetricGroupFourMatching_two] <;>
    decide

theorem matching_ne_one (m : Fin 3) : symmetricGroupFourMatching m ≠ 1 := by
  fin_cases m <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, symmetricGroupFourMatching_zero,
      symmetricGroupFourMatching_one, symmetricGroupFourMatching_two, ne_eq] <;>
    decide

theorem mem_matchingSubgroup_iff (m : Fin 3) (σ : Perm (Fin 4)) :
    σ ∈ matchingSubgroup m ↔ σ = 1 ∨ σ = symmetricGroupFourMatching m :=
  Subgroup.mem_zpowers_iff_of_sq_eq_one (matching_sq_eq_one m)

theorem matchingSubgroup_le_symmKleinFour (m : Fin 3) :
    matchingSubgroup m ≤ symmKleinFour := by
  rw [matchingSubgroup, Subgroup.zpowers_le, mem_symmKleinFour_iff]
  exact Or.inr ⟨m, rfl⟩

theorem card_matchingSubgroup (m : Fin 3) : Nat.card (matchingSubgroup m) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (Nat.card_zpowers _).trans (orderOf_eq_prime (matching_sq_eq_one m) (matching_ne_one m))

theorem isPGroup_two_matchingSubgroup (m : Fin 3) : IsPGroup 2 (matchingSubgroup m) :=
  IsPGroup.of_card_dvd_pow (n := 1) <| by
    rw [matchingSubgroup, Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (matching_sq_eq_one m)

theorem isPGroup_two_swapZeroOneSubgroup : IsPGroup 2 swapZeroOneSubgroup :=
  IsPGroup.of_card_dvd_pow (n := 1) <| by
    rw [swapZeroOneSubgroup, Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by decide)

theorem normal_matchingSubgroup_subgroupOf (m : Fin 3) :
    ((matchingSubgroup m).subgroupOf symmKleinFour).Normal := by
  let _ := isMulCommutative_symmKleinFour
  infer_instance

/-- `C₂ = ⟨(0 1)⟩` normalizes `N₀ = ⟨(0 1)(2 3)⟩` (in fact centralizes it). -/
theorem swapZeroOneSubgroup_le_normalizer_matchingSubgroup_zero :
    swapZeroOneSubgroup ≤ Subgroup.normalizer (matchingSubgroup 0) := by
  rw [swapZeroOneSubgroup, Subgroup.zpowers_le, Subgroup.mem_normalizer_iff_map_conj_eq,
    ← MulEquiv.toMonoidHom_eq_coe, matchingSubgroup, MonoidHom.map_zpowers]
  congr 1
  simp only [symmetricGroupFourMatching_zero]
  decide

/-- For `m ≠ 0`, `⟨M_m⟩` is a local complement of `⟨M₀⟩` in `symmKleinFour`. -/
theorem isLocalComplement_matchingSubgroup_zero {m : Fin 3} (hm : m ≠ 0) :
    (matchingSubgroup 0).IsLocalComplement (matchingSubgroup m) symmKleinFour := by
  refine ⟨?_, le_antisymm
    (sup_le (matchingSubgroup_le_symmKleinFour 0) (matchingSubgroup_le_symmKleinFour m)) ?_⟩
  · rw [eq_bot_iff]
    intro σ hσ
    obtain ⟨h0, hm'⟩ := Subgroup.mem_inf.mp hσ
    rw [mem_matchingSubgroup_iff] at h0 hm'
    rw [Subgroup.mem_bot]
    rcases h0 with rfl | rfl
    · rfl
    · rcases hm' with h | h
      · exact absurd h (matching_ne_one 0)
      · exact absurd (symmetricGroupFourMatching_injective h.symm) hm
  · intro σ hσ
    rw [mem_symmKleinFour_iff] at hσ
    rcases hσ with rfl | ⟨k, rfl⟩
    · exact Subgroup.one_mem _
    · have hmem : symmetricGroupFourMatching k = symmetricGroupFourMatching 0 ∨
          symmetricGroupFourMatching k = symmetricGroupFourMatching m ∨
          symmetricGroupFourMatching k =
            symmetricGroupFourMatching 0 * symmetricGroupFourMatching m := by
        fin_cases m
        · exact absurd rfl hm
        · fin_cases k <;>
            simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, symmetricGroupFourMatching_zero,
              symmetricGroupFourMatching_one, symmetricGroupFourMatching_two] <;>
            decide
        · fin_cases k <;>
            simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, symmetricGroupFourMatching_zero,
              symmetricGroupFourMatching_one, symmetricGroupFourMatching_two] <;>
            decide
      rcases hmem with hk | hk | hk <;> rw [hk]
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      · exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)

/-- The local complements of `⟨M₀⟩` in `symmKleinFour` are precisely `⟨M₁⟩` and `⟨M₂⟩`. -/
theorem isLocalComplement_matchingSubgroup_zero_iff (K : Subgroup (Perm (Fin 4))) :
    (matchingSubgroup 0).IsLocalComplement K symmKleinFour ↔
      K = matchingSubgroup 1 ∨ K = matchingSubgroup 2 := by
  have := normal_matchingSubgroup_subgroupOf 0
  refine ⟨fun hK => ?_, ?_⟩
  · have hcard : Nat.card K = 2 := by
      have hmul := hK.card_mul_card
      rw [card_matchingSubgroup 0, card_symmKleinFour] at hmul
      omega
    have hne : K ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hcard
      omega
    obtain ⟨σ, hσK, hσ1⟩ := (Subgroup.bot_or_exists_ne_one K).resolve_left hne
    have hσV := (mem_symmKleinFour_iff σ).mp (hK.right_le hσK)
    obtain ⟨m, rfl⟩ := hσV.resolve_left hσ1
    fin_cases m
    · exfalso
      have hmem : symmetricGroupFourMatching 0 ∈ matchingSubgroup 0 ⊓ K :=
        ⟨Subgroup.mem_zpowers _, hσK⟩
      rw [hK.inf_eq_bot, Subgroup.mem_bot] at hmem
      exact hσ1 hmem
    · left
      simp only [Fin.mk_one] at hσK
      exact (Subgroup.eq_of_le_of_card_ge (H := matchingSubgroup 1)
        (Subgroup.zpowers_le.mpr hσK) (by rw [hcard, card_matchingSubgroup 1])).symm
    · right
      simp only [Fin.reduceFinMk] at hσK
      exact (Subgroup.eq_of_le_of_card_ge (H := matchingSubgroup 2)
        (Subgroup.zpowers_le.mpr hσK) (by rw [hcard, card_matchingSubgroup 2])).symm
  · rintro (rfl | rfl) <;> exact isLocalComplement_matchingSubgroup_zero (by decide)

/-- Every Sylow `2`-subgroup of `symmKleinFour` maps onto `symmKleinFour`, so `⟨M₀⟩` has a local
complement (`⟨M₁⟩`) in the image of any Sylow `2`-subgroup of `symmKleinFour`. -/
theorem exists_isLocalComplement_matchingSubgroup_zero_sylow
    (P : Sylow 2 symmKleinFour) :
    ∃ K : Subgroup (Perm (Fin 4)),
      (matchingSubgroup 0).IsLocalComplement K (P.toSubgroup.map symmKleinFour.subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardP : Nat.card P.toSubgroup = Nat.card symmKleinFour := by
    rw [Sylow.card_eq_multiplicity, card_symmKleinFour]
    have h4 : 4 = 2 ^ 2 := by decide
    rw [h4, Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      Nat.prime_two.factorization_self]
  have hPtop : P.toSubgroup = ⊤ := Subgroup.eq_top_of_card_eq _ hcardP
  rw [hPtop, Subgroup.map_top, Subgroup.range_subtype]
  exact ⟨matchingSubgroup 1, isLocalComplement_matchingSubgroup_zero (by decide)⟩

/-- Sharpness of `p ≠ q` in `Subgroup.exists_invariant_local_complement`: for `W = symmKleinFour`,
`N = ⟨M₀⟩`, and `A = ⟨(0 1)⟩` in `S₄`, all hypotheses hold with `p = q = 2` except `2 ≠ 2`, yet no
local complement of `N` in `W` is normalized by `A` (since `(0 1)` swaps `M₁` and `M₂`). -/
theorem not_exists_invariant_local_complement_matchingSubgroup_zero :
    ¬ ∃ D : Subgroup (Perm (Fin 4)),
        (matchingSubgroup 0).IsLocalComplement D symmKleinFour ∧
          swapZeroOneSubgroup ≤ Subgroup.normalizer D := by
  rintro ⟨D, hD, hnorm⟩
  have hswap : swap (0 : Fin 4) 1 ∈ Subgroup.normalizer D :=
    hnorm (Subgroup.mem_zpowers _)
  rcases (isLocalComplement_matchingSubgroup_zero_iff D).mp hD with rfl | rfl
  · have hconj : swap 0 1 * symmetricGroupFourMatching 1 * (swap 0 1)⁻¹ ∈ matchingSubgroup 1 :=
      (Subgroup.mem_normalizer_iff.mp hswap _).mp (Subgroup.mem_zpowers _)
    rw [mem_matchingSubgroup_iff] at hconj
    rcases hconj with h | h <;>
      simp only [symmetricGroupFourMatching_one] at h <;>
      exact absurd h (by decide)
  · have hconj : swap 0 1 * symmetricGroupFourMatching 2 * (swap 0 1)⁻¹ ∈ matchingSubgroup 2 :=
      (Subgroup.mem_normalizer_iff.mp hswap _).mp (Subgroup.mem_zpowers _)
    rw [mem_matchingSubgroup_iff] at hconj
    rcases hconj with h | h <;>
      simp only [symmetricGroupFourMatching_two] at h <;>
      exact absurd h (by decide)

/-- Sharpness of `p ≠ q` in `Subgroup.exists_invariant_complement`: for the conjugation action of
`C₂ = ⟨(0 1)⟩` on `V₄ = symmKleinFour` and the normal abelian `2`-subgroup
`N = (matchingSubgroup 0).subgroupOf symmKleinFour`, `N` is `C₂`-stable and complemented in every
Sylow `2`-subgroup of `V₄`, yet admits no `C₂`-invariant complement in `V₄`. -/
theorem not_exists_invariant_complement_kleinFour_two :
    ¬ ∃ D : Subgroup symmKleinFour,
        ((matchingSubgroup 0).subgroupOf symmKleinFour).IsComplement' D ∧
          ∀ a : swapZeroOneSubgroup, ∀ d ∈ D, a • d ∈ D := by
  have := normal_matchingSubgroup_subgroupOf 0
  rintro ⟨D, hD, hinv⟩
  apply not_exists_invariant_local_complement_matchingSubgroup_zero
  refine ⟨D.map symmKleinFour.subtype, ?_, ?_⟩
  · have h := (Subgroup.isLocalComplement_top_iff (G := symmKleinFour)
      (N := (matchingSubgroup 0).subgroupOf symmKleinFour) (K := D)).mpr hD
    have hm := h.map symmKleinFour.subtype_injective
    simpa only [Subgroup.map_subgroupOf_eq_of_le (matchingSubgroup_le_symmKleinFour 0),
      Subgroup.map_top, Subgroup.range_subtype] using hm
  · rw [Subgroup.le_normalizer_iff]
    intro a ha d hd
    obtain ⟨d, hd, rfl⟩ := hd
    refine Subgroup.mem_map.mpr ⟨(⟨a, ha⟩ : swapZeroOneSubgroup) • d, hinv ⟨a, ha⟩ d hd, ?_⟩
    rw [Subgroup.coe_subtype, Subgroup.smul_def, Subgroup.coe_conjugationAction_smul]

end TauCeti.Examples.KleinFourComplement
