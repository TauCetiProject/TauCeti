/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.GaugeModuli.RelationModel.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import TauCeti.Analysis.Matrix.UnitaryGroup.ClockShift

/-!
# Genus-one coprime `SU(r)` moduli and clock–shift normal form

Let `ζ : ℂ` be a primitive `r`-th root of unity. At genus one, the twisted relation
`⁅A, B⁆ = ζ • 1` in `SU(r)` is equivalent to the Weyl commutation relation `A * B = ζ • (B * A)`
(`Matrix.specialUnitaryGroup.commutatorElement_eq_smul_one_iff`). By the clock–shift normal form
in `TauCeti.Analysis.Matrix.UnitaryGroup.ClockShift`, rescaling the unitary clock matrix
`C₀ = diag(1, ζ, …, ζ^{r-1})` and cyclic shift matrix `S₀` into `SU(r)` yields an explicit
solution (`Matrix.exists_clock_shift_specialUnitaryGroup`), and every solution in `SU(r)` is
simultaneously `SU(r)`-conjugate to this clock–shift pair
(`Matrix.exists_specialUnitaryGroup_conj_to_clock_shift`). Consequently, the genus-one
representation model `relationModuli r ζ 1` is a single point
(`TauCeti.GaugeModuli.relationModuli_genus_one`), hence simply connected, and the effective
`PSU(r)` action identifies `PSU(r)` homeomorphically with `relationSet r ζ 1`
(`TauCeti.GaugeModuli.psuOrbitHomeomorphGenusOne`).

As immediate consequences we also deduce nonemptiness of `relationSet r ζ g` and
`relationModuli r ζ g` for every positive genus `g ≥ 1`, triviality of the central-twist
`H¹(T²; μ_r)` action at genus one, and explicit rank-two checks: for `r = 2`, `ζ = -1`, the
Pauli-type pair `A = diag(i, -i)`, `B = !![0, 1; -1, 0]` satisfies `⁅A, B⁆ = -1`, `B A B⁻¹ = -A`,
and `A B A⁻¹ = -B` (witnessing non-freeness of the `H¹(X; ℤ/2)` action), whereas at the
non-coprime parameter `r = 2`, `ζ = 1`, the moduli `relationModuli 2 1 1` is not a subsingleton
(`TauCeti.GaugeModuli.not_subsingleton_relationModuli_two_one_one`) and the `SU(2)` action admits
non-central stabilizers (`TauCeti.GaugeModuli.exists_notMem_center_conjAct_smul_eq_self`).

## Main definitions

* `TauCeti.GaugeModuli.psuOrbitHomeomorphGenusOne`: for a primitive `r`-th root of unity `ζ`
  and any basepoint `x₀ : relationSet r ζ 1`, the orbit homeomorphism
  `PSU(r) ≃ₜ relationSet r ζ 1`.
* `TauCeti.GaugeModuli.rankTwoClock` and `TauCeti.GaugeModuli.rankTwoShift`: the explicit `SU(2)`
  witness pair `diag(i, -i)` and `!![0, 1; -1, 0]` for `r = 2`, `ζ = -1`.

## Main results

* `TauCeti.GaugeModuli.nonempty_relationSet_genus_one` and
  `TauCeti.GaugeModuli.relationModuli_genus_one`: existence and uniqueness up to simultaneous
  `SU(r)`-conjugation of a solution to `⁅A, B⁆ = ζ • 1`.
* `TauCeti.GaugeModuli.simplyConnectedSpace_relationModuli_genus_one`: simple connectivity of the
  genus-one moduli.
* `TauCeti.GaugeModuli.nonempty_relationSet_of_pos` and
  `TauCeti.GaugeModuli.nonempty_relationModuli_of_pos`: nonemptiness of the relation set and moduli
  for every genus `g ≥ 1`.
* `TauCeti.GaugeModuli.centerTwist_smul_relationModuli_genus_one`: the central-twist action is
  trivial at genus one.
* `TauCeti.GaugeModuli.rankTwoPair_mem_relationSet`,
  `TauCeti.GaugeModuli.exists_ne_one_centerTwist_fix_rankTwo_genus_one`,
  `TauCeti.GaugeModuli.rankTwoClock_notMem_center`,
  `TauCeti.GaugeModuli.exists_notMem_center_conjAct_smul_eq_self`, and
  `TauCeti.GaugeModuli.not_subsingleton_relationModuli_two_one_one`: explicit rank-two checks
  for `ζ = -1` and the non-coprime contrast `ζ = 1`.

## References

* Katrin Wehrheim and Chris T. Woodward, *Floer field theory for coprime rank and degree*,
  arXiv:1601.04924, §3 (Theorem 3.3.3(c) and Remark 3.3.7).
* Aliakbar Daemi, Kenji Fukaya, and Maksim Lipyanskiy, *Lagrangians, SO(3)-instantons and the
  Atiyah–Floer conjecture*, arXiv:2109.07032, Remark 2.2 and Lemma 2.43.
-/

public section

open Matrix Matrix.specialUnitaryGroup
open scoped commutatorElement

namespace TauCeti

namespace GaugeModuli

section GenusOneTheorems

/-- For every primitive `r`-th root of unity `ζ`, the genus-one twisted relation set
`relationSet r ζ 1` is nonempty. -/
theorem nonempty_relationSet_genus_one (r : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r) :
    Nonempty (relationSet r ζ 1) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨⟨1, mem_relationSet_one_iff.mpr (Subsingleton.elim _ _)⟩⟩
  have : NeZero r := ⟨by omega⟩
  obtain ⟨_, _, A₀, B₀, _, _, hAB⟩ := Matrix.exists_clock_shift_specialUnitaryGroup hζ
  exact ⟨⟨fun _ => (A₀, B₀), by simpa [mem_relationSet_one_iff] using hAB⟩⟩

/-- **Genus-one representation model.** For a primitive `r`-th root of unity `ζ`, the twisted
relation `⁅A, B⁆ = ζ • 1` has a solution in `SU(r)`, unique up to simultaneous `SU(r)`-conjugation,
so the genus-one moduli space `relationModuli r ζ 1` is a single point. -/
theorem relationModuli_genus_one (r : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r) :
    Nonempty (relationModuli r ζ 1) ∧ Subsingleton (relationModuli r ζ 1) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨⟨Quotient.mk _ ⟨1, mem_relationSet_one_iff.mpr (Subsingleton.elim _ _)⟩⟩,
      inferInstance⟩
  have : NeZero r := ⟨by omega⟩
  obtain ⟨c₁, c₂, A₀, B₀, hA₀, hB₀, hAB₀⟩ := Matrix.exists_clock_shift_specialUnitaryGroup hζ
  let x₀ : relationSet r ζ 1 := ⟨fun _ => (A₀, B₀), by simpa [mem_relationSet_one_iff] using hAB₀⟩
  have hconj (x : relationSet r ζ 1) :
      (Quotient.mk _ x : relationModuli r ζ 1) = Quotient.mk _ x₀ := by
    rw [quotient_mk_relationModuli_eq_iff]
    obtain ⟨u, huA, huB⟩ := Matrix.exists_specialUnitaryGroup_conj_to_clock_shift hζ hA₀ hB₀
      (x.1 0).1 (x.1 0).2 (mem_relationSet_one_iff.mp x.2)
    refine ⟨u, funext fun j => ?_⟩
    fin_cases j
    exact Prod.ext huA huB
  exact ⟨⟨Quotient.mk _ x₀⟩, ⟨fun a b => Quotient.inductionOn₂ a b fun x y =>
    (hconj x).trans (hconj y).symm⟩⟩

/-- At genus one, for a primitive `r`-th root of unity `ζ`, `relationModuli r ζ 1` is simply
connected. -/
theorem simplyConnectedSpace_relationModuli_genus_one (r : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r) :
    SimplyConnectedSpace (relationModuli r ζ 1) := by
  have h := relationModuli_genus_one r ζ hζ
  have : Nonempty (relationModuli r ζ 1) := h.1
  have : Subsingleton (relationModuli r ζ 1) := h.2
  exact SimplyConnectedSpace.ofContractible _

/-- **Genus-one orbit homeomorphism.** For a primitive `r`-th root of unity `ζ` and any basepoint
`x₀ : relationSet r ζ 1`, the effective `PSU(r)` action induces a homeomorphism
`PSU(r) ≃ₜ relationSet r ζ 1`. -/
noncomputable def psuOrbitHomeomorphGenusOne {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    (x₀ : relationSet r ζ 1) :
    (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range ≃ₜ relationSet r ζ 1 := by
  haveI : CompactSpace (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range :=
    isCompact_iff_compactSpace.mp isCompact_range_toPSL
  have hbij : Function.Bijective (fun p : (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range => p • x₀) := by
    constructor
    · intro p q hpq
      dsimp only at hpq
      have hfix : (q⁻¹ * p) • x₀ = x₀ := by
        rw [mul_smul, hpq, inv_smul_smul]
      have h1 : q⁻¹ * p = 1 := (psu_smul_relationSet_eq_self_iff hζ x₀ (q⁻¹ * p)).mp hfix
      exact (inv_mul_eq_one.mp h1).symm
    · intro x
      have hsub := (relationModuli_genus_one r ζ hζ).2
      have hq : (Quotient.mk _ x₀ : relationModuli r ζ 1) = Quotient.mk _ x :=
        Subsingleton.elim _ _
      obtain ⟨u, hu⟩ := (quotient_mk_relationModuli_eq_iff x₀ x).mp hq
      refine ⟨toPSL.rangeRestrict u, ?_⟩
      dsimp only
      rw [toPSL_rangeRestrict_smul_relationSet]
      exact Subtype.ext hu
  exact (continuous_id.smul continuous_const).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ hbij)

@[simp]
theorem psuOrbitHomeomorphGenusOne_apply {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    (x₀ : relationSet r ζ 1)
    (p : (toPSL : Matrix.specialUnitaryGroup (Fin r) ℂ →*
      ProjectiveSpecialLinearGroup (Fin r) ℂ).range) :
    psuOrbitHomeomorphGenusOne hζ x₀ p = p • x₀ :=
  (rfl)

/-- For every positive genus `g ≥ 1` and primitive `r`-th root of unity `ζ`, the twisted relation
set `relationSet r ζ g` is nonempty. -/
theorem nonempty_relationSet_of_pos (r : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r)
    (g : ℕ) (hg : 1 ≤ g) : Nonempty (relationSet r ζ g) := by
  obtain ⟨g', rfl⟩ := Nat.exists_eq_add_of_le' hg
  obtain ⟨⟨x₁, hx₁⟩⟩ := nonempty_relationSet_genus_one r ζ hζ
  let tuple : Fin (g' + 1) →
      Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ :=
    Fin.cons (x₁ 0) (fun _ : Fin g' => (1, 1))
  refine ⟨⟨tuple, ?_⟩⟩
  rw [mem_relationSet_iff]
  have hprod : (List.ofFn fun j : Fin (g' + 1) => ⁅(tuple j).1, (tuple j).2⁆).prod =
      ⁅(x₁ 0).1, (x₁ 0).2⁆ := by
    rw [List.ofFn_succ, List.prod_cons]
    simp [tuple, List.ofFn_const]
  rw [hprod]
  exact mem_relationSet_one_iff.mp hx₁

/-- For every positive genus `g ≥ 1` and primitive `r`-th root of unity `ζ`, the representation
model `relationModuli r ζ g` is nonempty. -/
theorem nonempty_relationModuli_of_pos (r : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r)
    (g : ℕ) (hg : 1 ≤ g) : Nonempty (relationModuli r ζ g) := by
  obtain ⟨x⟩ := nonempty_relationSet_of_pos r ζ hζ g hg
  exact ⟨Quotient.mk _ x⟩

/-- At genus one, the central-twist `H¹(T²; μ_r)` action on `relationModuli r ζ 1` is trivial. -/
theorem centerTwist_smul_relationModuli_genus_one (r : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r)
    (ε : Fin 1 → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ))
    (q : relationModuli r ζ 1) : ε • q = q := by
  have := (relationModuli_genus_one r ζ hζ).2
  exact Subsingleton.elim _ _

end GenusOneTheorems

section RankTwoChecks

/-- Membership criterion for a `2 × 2` complex matrix `!![a, b; c, d]` in `SU(2)`. -/
private theorem of_fin_two_mem_specialUnitaryGroup {a b c d : ℂ}
    (h00 : star a * a + star c * c = 1) (h01 : star a * b + star c * d = 0)
    (h11 : star b * b + star d * d = 1) (hdet : a * d - b * c = 1) :
    !![a, b; c, d] ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine mem_specialUnitaryGroup_iff.mpr ⟨?_, by simpa [Matrix.det_fin_two] using hdet⟩
  rw [Matrix.mem_unitaryGroup_iff']
  have h10 : star b * a + star d * c = 0 := by
    simpa [mul_comm] using congrArg star h01
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp_all [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]

/-- The diagonal matrix `diag(i, -i) ∈ SU(2)`. -/
def rankTwoClock : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ⟨!![Complex.I, 0; 0, -Complex.I],
    of_fin_two_mem_specialUnitaryGroup (by simp) (by simp) (by simp) (by simp)⟩

/-- The rotation matrix `!![0, 1; -1, 0] ∈ SU(2)`. -/
def rankTwoShift : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ⟨!![(0 : ℂ), 1; -1, 0],
    of_fin_two_mem_specialUnitaryGroup (by simp) (by simp) (by simp) (by simp)⟩

/-- For `r = 2`, `ζ = -1`, the pair `(rankTwoClock, rankTwoShift)` satisfies
`⁅A, B⁆ = -1` and hence belongs to `relationSet 2 (-1) 1`. -/
theorem rankTwoPair_mem_relationSet :
    (fun _ : Fin 1 => (rankTwoClock, rankTwoShift)) ∈ relationSet 2 (-1) 1 := by
  rw [mem_relationSet_one_iff, Matrix.specialUnitaryGroup.commutatorElement_eq_smul_one_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankTwoClock, rankTwoShift, Matrix.mul_apply, Fin.sum_univ_two]

/-- If `A, B ∈ SU(2)` anticommute (`A * B = -(B * A)`), then conjugating `B` by `A` equals
`(-1) * B`. -/
private theorem conjAct_smul_eq_negOne_mul_of_mul_eq_neg
    {A B : Matrix.specialUnitaryGroup (Fin 2) ℂ}
    (h : (A : Matrix (Fin 2) (Fin 2) ℂ) * (B : Matrix (Fin 2) (Fin 2) ℂ) =
      -((B : Matrix (Fin 2) (Fin 2) ℂ) * (A : Matrix (Fin 2) (Fin 2) ℂ))) :
    ConjAct.toConjAct A • B = Matrix.specialUnitaryGroup.negOne.1 * B := by
  have hAB : A * B = Matrix.specialUnitaryGroup.negOne.1 * (B * A) := by
    apply Subtype.ext
    simpa [Submonoid.coe_mul] using h
  rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, hAB, mul_assoc, mul_inv_cancel_right]

/-- Conjugating `rankTwoClock` by `rankTwoShift` multiplies it by `-1`. -/
theorem rankTwoShift_conj_rankTwoClock :
    ConjAct.toConjAct rankTwoShift • rankTwoClock =
      Matrix.specialUnitaryGroup.negOne.1 * rankTwoClock :=
  conjAct_smul_eq_negOne_mul_of_mul_eq_neg <| by
    have h := Matrix.specialUnitaryGroup.commutatorElement_eq_smul_one_iff.mp
      (mem_relationSet_one_iff.mp rankTwoPair_mem_relationSet)
    simpa using congrArg Neg.neg h.symm

/-- Conjugating `rankTwoShift` by `rankTwoClock` multiplies it by `-1`. -/
theorem rankTwoClock_conj_rankTwoShift :
    ConjAct.toConjAct rankTwoClock • rankTwoShift =
      Matrix.specialUnitaryGroup.negOne.1 * rankTwoShift :=
  conjAct_smul_eq_negOne_mul_of_mul_eq_neg <| by
    simpa using Matrix.specialUnitaryGroup.commutatorElement_eq_smul_one_iff.mp
      (mem_relationSet_one_iff.mp rankTwoPair_mem_relationSet)

/-- The central-twist `H¹(T²; ℤ/2)` action on `relationModuli 2 (-1) 1` is not free: the
nontrivial sign twist `(-1, 1)` fixes the class of `(rankTwoClock, rankTwoShift)`. -/
theorem exists_ne_one_centerTwist_fix_rankTwo_genus_one :
    ∃ (ε : Fin 1 → Subgroup.center (Matrix.specialUnitaryGroup (Fin 2) ℂ) ×
        Subgroup.center (Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (q : relationModuli 2 (-1) 1), ε ≠ 1 ∧ ε • q = q := by
  let ε : Fin 1 → Subgroup.center (Matrix.specialUnitaryGroup (Fin 2) ℂ) ×
      Subgroup.center (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    fun _ => (Matrix.specialUnitaryGroup.negOne, 1)
  let x : relationSet 2 (-1) 1 :=
    ⟨fun _ => (rankTwoClock, rankTwoShift), rankTwoPair_mem_relationSet⟩
  refine ⟨ε, Quotient.mk _ x, ?_, ?_⟩
  · intro h
    have h0 := congrArg Prod.fst (congrFun h 0)
    exact (Matrix.specialUnitaryGroup.negOne_ne_one_iff.mpr (by norm_num)) h0
  · rw [centerTwist_smul_relationModuli_mk]
    symm
    rw [quotient_mk_relationModuli_eq_iff]
    refine ⟨rankTwoShift, funext fun j => ?_⟩
    fin_cases j
    refine Prod.ext rankTwoShift_conj_rankTwoClock ?_
    simp [ε, x, ConjAct.smul_def]

/-- `rankTwoClock` is not central in `SU(2)`. Since it commutes with `1 ∈ relationSet 2 1 g`,
this shows that the primitive-root hypothesis cannot be omitted from
`relationSet_stabilizer_central`. -/
theorem rankTwoClock_notMem_center :
    rankTwoClock ∉ Subgroup.center (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  rw [Matrix.specialUnitaryGroup.mem_center_iff]
  rintro ⟨c, _, hc⟩
  have h00 := congr_fun₂ hc 0 0
  have h11 := congr_fun₂ hc 1 1
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, rankTwoClock, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one] at h00 h11
  have him := congrArg Complex.im (h00.symm.trans h11)
  norm_num at him

/-- At the non-coprime parameter `r = 2`, `ζ = 1`, the simultaneous `SU(2)`-conjugation action on
`relationSet 2 1 g` admits non-central stabilizers (for example `rankTwoClock` fixes the trivial
tuple `1`). -/
theorem exists_notMem_center_conjAct_smul_eq_self (g : ℕ) :
    ∃ (u : Matrix.specialUnitaryGroup (Fin 2) ℂ) (x : relationSet 2 1 g),
      u ∉ Subgroup.center (Matrix.specialUnitaryGroup (Fin 2) ℂ) ∧
        ConjAct.toConjAct u • x = x :=
  ⟨rankTwoClock, ⟨1, one_mem_relationSet 2 g⟩, rankTwoClock_notMem_center,
    Subtype.ext (smul_one _)⟩

/-- At the non-coprime parameter `r = 2`, `ζ = 1`, `g = 1`, the moduli space `relationModuli 2 1 1`
is not a subsingleton (distinguishing the classes of `(1, 1)` and `(rankTwoClock, 1)`). -/
theorem not_subsingleton_relationModuli_two_one_one : ¬ Subsingleton (relationModuli 2 1 1) := by
  intro hsub
  let x₁ : relationSet 2 1 1 := ⟨1, one_mem_relationSet 2 1⟩
  let x₂ : relationSet 2 1 1 := ⟨fun _ => (rankTwoClock, 1), by
    rw [mem_relationSet_one_iff]
    simp⟩
  have heq : (Quotient.mk _ x₁ : relationModuli 2 1 1) = Quotient.mk _ x₂ :=
    Subsingleton.elim _ _
  obtain ⟨u, hu⟩ := (quotient_mk_relationModuli_eq_iff x₁ x₂).mp heq
  have h0 : ConjAct.toConjAct u • (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) = rankTwoClock :=
    congrArg Prod.fst (congrFun hu 0)
  rw [smul_one] at h0
  have h00 := congr_fun₂ (congrArg Subtype.val h0) 0 0
  simp only [OneMemClass.coe_one, Matrix.one_apply_eq, rankTwoClock, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one] at h00
  have him := congrArg Complex.im h00
  norm_num at him

end RankTwoChecks

end GaugeModuli

end TauCeti
