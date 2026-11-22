/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Projective
public import TauCeti.NumberTheory.Modular.CosetTriple
public import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Cusp widths, elliptic points and the genus of a subgroup of `PSL(2, ℤ)`

Let `Γ' ≤ PSL(2, ℤ)` have a coset numbering `e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n`, with modular triple
`(σ0, σ1, σinf) = (ρ U, ρ S, ρ T)` (`TauCeti.ModularGroup.modularTriple`). The invariants of the
modular curve of `Γ'` are read off these permutations:

* the **cusp widths** `TauCeti.ModularGroup.cuspWidths Γ' e` are the cycle lengths of `σinf`,
  fixed points included, so they sum to the index `n`, and the **number of cusps**
  `TauCeti.ModularGroup.cuspCount Γ' e` is the number of cycles of `σinf`;
* the numbers of **elliptic points** of periods two and three,
  `TauCeti.ModularGroup.ellipticTwo Γ' e` and `TauCeti.ModularGroup.ellipticThree Γ' e`, are the
  numbers of fixed points of `σ1` and `σ0`;
* the **genus** is `(modularTriple Γ' e).genus`, defined from the Euler characteristic
  `χ = #cycles(σ0) + #cycles(σ1) + #cycles(σinf) - n` by `χ = 2 - 2g`.

All four are unchanged under renumbering the cosets and under conjugating `Γ'`, because Millington's
theorem (`TauCeti.ModularGroup.millington`) makes the corresponding modular triples isomorphic.
Since `σ1 ^ 2 = 1` and `σ0 ^ 3 = 1`, the non-fixed points of `σ1` and `σ0` fall into cycles of
lengths two and three. Counting cycles this way turns the Euler characteristic into the
**genus formula** `12 g + 3 ε₂ + 4 ε₃ + 6 ε∞ = 12 + n`, the combinatorial form of Diamond–Shurman's
Theorem 3.1.1.

The cycle of `σinf` through the coset of `σ⁻¹` (for `σ ∈ SL(2, ℤ)`) has length the integer
width at `∞` of the conjugate `σ⁻¹ (±Γ') σ` of the lift `±Γ' = Γ'.liftSL`, that is, the width of
the cusp `σ ∞` of `Γ'`.

## Main results

* `TauCeti.ModularGroup.sum_cuspWidths`, `TauCeti.ModularGroup.card_cuspWidths`: the widths sum
  to the index and there are `cuspCount` of them.
* `TauCeti.ModularGroup.minimalPeriod_permT_eq_integerCuspWidth`: the length of the cycle of
  `σinf` through the coset of `σ⁻¹` is the integer width of `σ⁻¹ (±Γ') σ` at `∞`.
* `TauCeti.ModularGroup.mem_cuspWidths_iff`: the cusp widths are exactly these widths, for
  `σ ∈ SL(2, ℤ)`.
* `TauCeti.ModularGroup.cuspWidths_eq_of_equivalent` and its companions for `cuspCount`,
  `ellipticTwo` and `ellipticThree`: the invariants depend only on the isomorphism class of the
  modular triple, hence not on the coset numbering (`TauCeti.ModularGroup.cuspWidths_congr`, …)
  and only on the conjugacy class of `Γ'` (`TauCeti.ModularGroup.cuspWidths_conjAct_smul`, …).
* `TauCeti.ModularGroup.ellipticTwo_modEq`, `TauCeti.ModularGroup.ellipticThree_modEq`:
  `ε₂ ≡ n (mod 2)` and `ε₃ ≡ n (mod 3)`.
* `TauCeti.ModularGroup.genus_formula`: `12 g + 3 ε₂ + 4 ε₃ + 6 ε∞ = 12 + n`.
* `TauCeti.ModularGroup.genus_modularTriple_eq_zero_iff`,
  `TauCeti.ModularGroup.six_dvd_of_ellipticTwo_eq_zero_of_ellipticThree_eq_zero`,
  `TauCeti.ModularGroup.six_le_of_genus_modularTriple_pos`: the genus vanishes exactly when
  `3 ε₂ + 4 ε₃ + 6 ε∞ = 12 + n`; without elliptic points `6 ∣ n`; and positive genus forces
  `n ≥ 6`.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics 228,
  Springer 2005, Theorem 3.1.1 and §§3.7–3.8.
* G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press 1971, §1.6 and Proposition 1.40.
-/

open Equiv Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise Finset

public section

namespace TauCeti.ModularGroup

open _root_.ModularGroup PermutationTriple

variable {n : ℕ}

/-! ### The invariants -/

/-- **The cusp widths** of `Γ'`: the cycle lengths of `permT Γ' e = (modularTriple Γ' e).σinf`,
with one part `1` for each fixed point. -/
noncomputable def cuspWidths (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Multiset ℕ :=
  (permT Γ' e).fullCycleType

/-- **The number of cusps** of `Γ'`: the number of cycles of `permT Γ' e`, fixed points
included. -/
noncomputable def cuspCount (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) : ℕ :=
  orbitCount (permT Γ' e)

/-- **The number of elliptic points of period two** of `Γ'`: the number of cosets fixed by
`permS Γ' e`, the permutation of `S`. -/
noncomputable def ellipticTwo (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) : ℕ :=
  #{i | permS Γ' e i = i}

/-- **The number of elliptic points of period three** of `Γ'`: the number of cosets fixed by
`(modularTriple Γ' e).σ0`, the permutation of `U = S T⁻¹`. -/
noncomputable def ellipticThree (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) : ℕ :=
  #{i | (modularTriple Γ' e).σ0 i = i}

variable (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)

theorem cuspWidths_def : cuspWidths Γ' e = (permT Γ' e).fullCycleType := (rfl)

theorem cuspCount_def : cuspCount Γ' e = orbitCount (permT Γ' e) := (rfl)

theorem ellipticTwo_def : ellipticTwo Γ' e = #{i | permS Γ' e i = i} := (rfl)

theorem ellipticThree_def : ellipticThree Γ' e = #{i | (modularTriple Γ' e).σ0 i = i} := (rfl)

/-- The cusp widths sum to the index `n`. -/
@[simp]
theorem sum_cuspWidths : (cuspWidths Γ' e).sum = n := by
  rw [cuspWidths, Perm.sum_fullCycleType, Fintype.card_fin]

/-- There are as many cusp widths as cusps. -/
@[simp]
theorem card_cuspWidths : Multiset.card (cuspWidths Γ' e) = cuspCount Γ' e := by
  rw [cuspWidths, cuspCount, Perm.fullCycleType_def, Perm.orbitCount_eq_card_parts_partition]

/-- Every cusp width is positive. -/
theorem pos_of_mem_cuspWidths {w : ℕ} (hw : w ∈ cuspWidths Γ' e) : 0 < w :=
  Perm.pos_of_mem_fullCycleType hw

/-- The number of elliptic points of period two is the number of parts `1` of the full cycle
type of `permS Γ' e`. -/
theorem ellipticTwo_eq_count_fullCycleType :
    ellipticTwo Γ' e = (permS Γ' e).fullCycleType.count 1 := by
  rw [ellipticTwo, Perm.count_one_fullCycleType_eq_card_filter]

/-- The number of elliptic points of period three is the number of parts `1` of the full cycle
type of `(modularTriple Γ' e).σ0`. -/
theorem ellipticThree_eq_count_fullCycleType :
    ellipticThree Γ' e = (modularTriple Γ' e).σ0.fullCycleType.count 1 := by
  rw [ellipticThree, Perm.count_one_fullCycleType_eq_card_filter]

/-! ### The width of a cusp -/

/-- `permT Γ' e ^ j` fixes the coset of `g` exactly when `g⁻¹ Tʲ g ∈ Γ'`. -/
theorem permT_pow_apply_eq_iff (g : PSL(2, ℤ)) (j : ℕ) :
    (permT Γ' e ^ j) (e g) = e g ↔ g⁻¹ * (T : PSL(2, ℤ)) ^ j * g ∈ Γ' := by
  simp only [permT, modularTriple_σinf, ← map_pow, Equiv.permutationRepresentation_apply,
    e.symm_apply_apply, e.apply_eq_iff_eq, MulAction.Quotient.smul_mk, smul_eq_mul]
  rw [QuotientGroup.eq, ← inv_mem_iff]
  group

/-- The image of `γ ∈ SL(2, ℤ)` in `GL(2, ℝ)` lies in the conjugate `σ⁻¹ (±Γ') σ` of the lift
`±Γ' = Γ'.liftSL` exactly when the image of `σ γ σ⁻¹` in `PSL(2, ℤ)` lies in `Γ'`. -/
theorem mapGL_mem_map_conjAct_liftSL_iff (σ γ : SL(2, ℤ)) :
    mapGL ℝ γ ∈ (ConjAct.toConjAct σ⁻¹ • Γ'.liftSL).map (mapGL ℝ) ↔
      ((σ * γ * σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) ∈ Γ' := by
  rw [_root_.Subgroup.mem_map_iff_mem mapGL_injective,
    _root_.Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    ConjAct.toConjAct_smul, _root_.Subgroup.mem_liftSL, inv_inv]

/-- **The width of the cusp `σ ∞`.** For `σ ∈ SL(2, ℤ)`, the cycle of `permT Γ' e` through the
coset of `σ⁻¹` has length the integer width at `∞` of the conjugate `σ⁻¹ (±Γ') σ` of the lift
`±Γ' = Γ'.liftSL`: both are the least `m > 0` with `σ Tᵐ σ⁻¹ ∈ ±Γ'`. -/
theorem minimalPeriod_permT_eq_integerCuspWidth (σ : SL(2, ℤ)) :
    Function.minimalPeriod (permT Γ' e) (e ((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ))) =
      TauCeti.Subgroup.integerCuspWidth
        ((ConjAct.toConjAct σ⁻¹ • Γ'.liftSL).map (mapGL ℝ)) := by
  refine Nat.dvd_right_iff_eq.mp fun j ↦ ?_
  rw [← Function.isPeriodicPt_iff_minimalPeriod_dvd, ← TauCeti.Subgroup.T_pow_mem_iff,
    coe_GL_eq_mapGL, ← map_pow, mapGL_mem_map_conjAct_liftSL_iff]
  simp only [Function.IsPeriodicPt, Function.IsFixedPt, Perm.iterate_eq_pow,
    permT_pow_apply_eq_iff]
  simp

/-- **The width at `∞`.** The cycle of `permT Γ' e` through the base coset has length the integer
width at `∞` of the lift `±Γ' = Γ'.liftSL`. -/
theorem minimalPeriod_permT_one_eq_integerCuspWidth :
    Function.minimalPeriod (permT Γ' e) (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) =
      TauCeti.Subgroup.integerCuspWidth (Γ'.liftSL.map (mapGL ℝ)) := by
  simpa using minimalPeriod_permT_eq_integerCuspWidth Γ' e 1

/-- The cusp widths are exactly the widths at `∞` of the conjugates `σ⁻¹ (±Γ') σ`, the widths of
the cusps `σ ∞`. -/
theorem mem_cuspWidths_iff {w : ℕ} :
    w ∈ cuspWidths Γ' e ↔ ∃ σ : SL(2, ℤ),
      TauCeti.Subgroup.integerCuspWidth ((ConjAct.toConjAct σ⁻¹ • Γ'.liftSL).map (mapGL ℝ)) =
        w := by
  simp_rw [← minimalPeriod_permT_eq_integerCuspWidth Γ' e, cuspWidths,
    Perm.mem_fullCycleType_iff]
  refine ⟨fun ⟨i, hi⟩ ↦ ?_, fun ⟨σ, hσ⟩ ↦ ⟨_, hσ⟩⟩
  obtain ⟨q, rfl⟩ := e.surjective i
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
  exact ⟨σ⁻¹, by rwa [inv_inv]⟩

/-- The width at `∞` of each conjugate `σ⁻¹ (±Γ') σ`, the width of the cusp `σ ∞`, is one of the
cusp widths. -/
theorem integerCuspWidth_mem_cuspWidths (σ : SL(2, ℤ)) :
    TauCeti.Subgroup.integerCuspWidth ((ConjAct.toConjAct σ⁻¹ • Γ'.liftSL).map (mapGL ℝ)) ∈
      cuspWidths Γ' e :=
  (mem_cuspWidths_iff Γ' e).mpr ⟨σ, rfl⟩

/-! ### The full modular group -/

section Top

variable (e : PSL(2, ℤ) ⧸ (⊤ : Subgroup PSL(2, ℤ)) ≃ Fin 1)

/-- The full modular group has a single cusp, of width one. -/
@[simp]
theorem cuspWidths_top : cuspWidths ⊤ e = {1} := by
  rw [cuspWidths, permT, modularTriple_top]
  simp

/-- The full modular group has one cusp. -/
@[simp]
theorem cuspCount_top : cuspCount ⊤ e = 1 := by
  rw [← card_cuspWidths, cuspWidths_top, Multiset.card_singleton]

/-- The full modular group has one elliptic point of period two, the orbit of `i`. -/
@[simp]
theorem ellipticTwo_top : ellipticTwo ⊤ e = 1 := by
  simp [ellipticTwo]

/-- The full modular group has one elliptic point of period three, the orbit of `e^{πi/3}`. -/
@[simp]
theorem ellipticThree_top : ellipticThree ⊤ e = 1 := by
  simp [ellipticThree]

end Top

/-! ### Invariance -/

section Invariance

variable {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)} {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}

/-- Isomorphic modular triples have the same cusp widths. -/
theorem cuspWidths_eq_of_equivalent
    (h : (modularTriple Γ₁ e₁).Equivalent (modularTriple Γ₂ e₂)) :
    cuspWidths Γ₁ e₁ = cuspWidths Γ₂ e₂ := by
  rw [cuspWidths, cuspWidths, permT, permT, fullCycleType_σinf_eq_of_equivalent h]

/-- Isomorphic modular triples have the same number of cusps. -/
theorem cuspCount_eq_of_equivalent
    (h : (modularTriple Γ₁ e₁).Equivalent (modularTriple Γ₂ e₂)) :
    cuspCount Γ₁ e₁ = cuspCount Γ₂ e₂ := by
  rw [← card_cuspWidths, ← card_cuspWidths, cuspWidths_eq_of_equivalent h]

/-- Isomorphic modular triples have the same number of elliptic points of period two. -/
theorem ellipticTwo_eq_of_equivalent
    (h : (modularTriple Γ₁ e₁).Equivalent (modularTriple Γ₂ e₂)) :
    ellipticTwo Γ₁ e₁ = ellipticTwo Γ₂ e₂ := by
  rw [ellipticTwo_eq_count_fullCycleType, ellipticTwo_eq_count_fullCycleType, permS, permS,
    fullCycleType_σ1_eq_of_equivalent h]

/-- Isomorphic modular triples have the same number of elliptic points of period three. -/
theorem ellipticThree_eq_of_equivalent
    (h : (modularTriple Γ₁ e₁).Equivalent (modularTriple Γ₂ e₂)) :
    ellipticThree Γ₁ e₁ = ellipticThree Γ₂ e₂ := by
  rw [ellipticThree_eq_count_fullCycleType, ellipticThree_eq_count_fullCycleType,
    fullCycleType_σ0_eq_of_equivalent h]

/-- The cusp widths do not depend on the coset numbering. -/
theorem cuspWidths_congr (e e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) : cuspWidths Γ' e = cuspWidths Γ' e' :=
  cuspWidths_eq_of_equivalent (equivalent_modularTriple Γ' e e')

/-- The number of cusps does not depend on the coset numbering. -/
theorem cuspCount_congr (e e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) : cuspCount Γ' e = cuspCount Γ' e' :=
  cuspCount_eq_of_equivalent (equivalent_modularTriple Γ' e e')

/-- The number of elliptic points of period two does not depend on the coset numbering. -/
theorem ellipticTwo_congr (e e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ellipticTwo Γ' e = ellipticTwo Γ' e' :=
  ellipticTwo_eq_of_equivalent (equivalent_modularTriple Γ' e e')

/-- The number of elliptic points of period three does not depend on the coset numbering. -/
theorem ellipticThree_congr (e e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ellipticThree Γ' e = ellipticThree Γ' e' :=
  ellipticThree_eq_of_equivalent (equivalent_modularTriple Γ' e e')

end Invariance

section Conjugation

variable (g : ConjAct PSL(2, ℤ)) (e' : PSL(2, ℤ) ⧸ g • Γ' ≃ Fin n)

/-- Conjugate subgroups have the same cusp widths, for any coset numberings. -/
theorem cuspWidths_conjAct_smul : cuspWidths (g • Γ') e' = cuspWidths Γ' e :=
  cuspWidths_eq_of_equivalent ((millington e' e).mpr ⟨g⁻¹, inv_smul_smul g Γ'⟩)

/-- Conjugate subgroups have the same number of cusps, for any coset numberings. -/
theorem cuspCount_conjAct_smul : cuspCount (g • Γ') e' = cuspCount Γ' e :=
  cuspCount_eq_of_equivalent ((millington e' e).mpr ⟨g⁻¹, inv_smul_smul g Γ'⟩)

/-- Conjugate subgroups have the same number of elliptic points of period two. -/
theorem ellipticTwo_conjAct_smul : ellipticTwo (g • Γ') e' = ellipticTwo Γ' e :=
  ellipticTwo_eq_of_equivalent ((millington e' e).mpr ⟨g⁻¹, inv_smul_smul g Γ'⟩)

/-- Conjugate subgroups have the same number of elliptic points of period three. -/
theorem ellipticThree_conjAct_smul : ellipticThree (g • Γ') e' = ellipticThree Γ' e :=
  ellipticThree_eq_of_equivalent ((millington e' e).mpr ⟨g⁻¹, inv_smul_smul g Γ'⟩)

end Conjugation

/-! ### Cycle counts of `σ1` and `σ0` and the genus formula -/

/-- `permS Γ' e` is an involution, so it has `(n + ε₂) / 2` cycles. -/
theorem two_mul_orbitCount_permS : 2 * orbitCount (permS Γ' e) = n + ellipticTwo Γ' e := by
  have := Perm.mul_orbitCount_of_pow_prime_eq_one (p := 2) (modularTriple_σ1_sq Γ' e)
  rwa [Fintype.card_fin, Nat.add_one_sub_one, one_mul] at this

/-- `(modularTriple Γ' e).σ0` has order dividing three, so it has `(n + 2 ε₃) / 3` cycles. -/
theorem three_mul_orbitCount_σ0 :
    3 * orbitCount (modularTriple Γ' e).σ0 = n + 2 * ellipticThree Γ' e := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := Perm.mul_orbitCount_of_pow_prime_eq_one (p := 3) (modularTriple_σ0_pow_three Γ' e)
  rwa [Fintype.card_fin] at this

/-- The number of elliptic points of period two is congruent to the index modulo `2`. -/
theorem ellipticTwo_modEq : ellipticTwo Γ' e ≡ n [MOD 2] := by
  have h := two_mul_orbitCount_permS Γ' e
  rw [Nat.ModEq]
  omega

/-- The number of elliptic points of period three is congruent to the index modulo `3`. -/
theorem ellipticThree_modEq : ellipticThree Γ' e ≡ n [MOD 3] := by
  have h := three_mul_orbitCount_σ0 Γ' e
  rw [Nat.ModEq]
  omega

/-- **The genus formula.** The genus `g` of the modular triple of `Γ'`, its numbers `ε₂`, `ε₃` of
elliptic points of periods two and three, and its number `ε∞` of cusps satisfy
`12 g + 3 ε₂ + 4 ε₃ + 6 ε∞ = 12 + n`, where `n` is the index. -/
theorem genus_formula :
    12 * (modularTriple Γ' e).genus + 3 * ellipticTwo Γ' e + 4 * ellipticThree Γ' e +
      6 * cuspCount Γ' e = 12 + n := by
  have hg := (isConnected_modularTriple Γ' e).two_sub_two_mul_genus
  have h2 := two_mul_orbitCount_permS Γ' e
  have h3 := three_mul_orbitCount_σ0 Γ' e
  rw [eulerChar_def] at hg
  rw [permS] at h2
  rw [cuspCount_def, permT]
  omega

/-- The genus of `Γ'` vanishes exactly when `3 ε₂ + 4 ε₃ + 6 ε∞ = 12 + n`. -/
theorem genus_modularTriple_eq_zero_iff :
    (modularTriple Γ' e).genus = 0 ↔
      3 * ellipticTwo Γ' e + 4 * ellipticThree Γ' e + 6 * cuspCount Γ' e = 12 + n := by
  have := genus_formula Γ' e
  omega

/-- Without elliptic points, as for a torsion-free `Γ'`, the index is divisible by `6`: it is
`6 (2 g - 2 + ε∞)`. -/
theorem six_dvd_of_ellipticTwo_eq_zero_of_ellipticThree_eq_zero (h2 : ellipticTwo Γ' e = 0)
    (h3 : ellipticThree Γ' e = 0) : 6 ∣ n := by
  have := genus_formula Γ' e
  omega

/-- A subgroup of positive genus has index at least `6`. -/
theorem six_le_of_genus_modularTriple_pos (h : 0 < (modularTriple Γ' e).genus) : 6 ≤ n := by
  have hg := genus_formula Γ' e
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp
    (Nat.pos_of_ne_zero (isConnected_modularTriple Γ' e).ne_zero)
  have hc : 0 < cuspCount Γ' e := by
    rw [cuspCount_def]
    exact (permT Γ' e).orbitCount_pos
  omega

end TauCeti.ModularGroup
