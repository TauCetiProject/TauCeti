/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import TauCeti.Combinatorics.PermutationTriple.EulerCharacteristic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Projective
public import TauCeti.NumberTheory.Modular.CosetTriple
import TauCeti.Combinatorics.PermutationTriple.ComputedInvariants
import TauCeti.Combinatorics.PermutationTriple.Decidable
import TauCeti.Combinatorics.PermutationTriple.Mirror

/-!
# Combinatorial invariants of the modular coset triple

Every finite-index subgroup `Γ' ≤ PSL(2, ℤ)` with a left-coset enumeration
`e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n` determines a modular coset triple
`TauCeti.ModularGroup.modularTriple Γ' e = (σ0, σ1, σinf)` (`permS = σ1`, `permT = σinf`,
`σ0 = ρ U`), from which the classical invariants of the modular curve `X(Γ')` can be read off
combinatorially:

* **Cusp widths and cusp count (`cuspWidths`, `cuspCount`).** The multiset of cusp widths is the
  full cycle type `(permT Γ' e).fullCycleType`, and the cusp count is `orbitCount (permT Γ' e)`.
  The cycle period of `permT` at the coset `g Γ'` is the least positive `h` with
  `g⁻¹ T ^ h g ∈ Γ'`, the cycles of `permT` biject onto the double cosets
  `Γ' \ PSL(2, ℤ) / ⟨T⟩` (`permTCycleEquivDoubleCoset`), and for `Γ'' ≤ Γ'` every cusp width of
  `Γ''` is a multiple of the width of the cusp of `Γ'` below it with the width ratios over a cusp
  summing to `[Γ' : Γ'']` (`minimalPeriod_permT_dvd_of_le`,
  `sum_widthRatio_permT_fiber_of_le`).
* **Elliptic point counts (`ellipticTwo`, `ellipticThree`).** The numbers of order-`2` and
  order-`3` elliptic points are the fixed-point counts of `permS` and `(modularTriple Γ' e).σ0`
  (equivalently of `permR = permS * permT`), satisfying
  `2 * orbitCount (permS Γ' e) = n + ellipticTwo Γ' e`,
  `3 * orbitCount (modularTriple Γ' e).σ0 = n + 2 * ellipticThree Γ' e`, and the congruences
  `ellipticTwo Γ' e ≡ n [MOD 2]` and `ellipticThree Γ' e ≡ n [MOD 3]`.
* **Genus and the integral genus formula (`genus`, `genus_formula`).** The genus is
  `(modularTriple Γ' e).genus`, satisfying the integral Riemann–Hurwitz identity
  `12 * genus + 3 * ellipticTwo + 4 * ellipticThree + 6 * cuspCount = 12 + n`, together with its
  torsion-free specializations (`6 ∣ n` when `ellipticTwo = ellipticThree = 0`, and `6 ≤ n`
  whenever `0 < genus`).
* **The invariant vector (`Invariants`, `invariants`) and non-completeness.** Packaging
  `(index, genus, ellipticTwo, ellipticThree, cuspWidths)` yields an invariant of conjugacy classes
  in `PSL(2, ℤ)` that is independent of the coset numbering, invariant under the opposite
  (right-coset) convention, and invariant under the mirror automorphism `conjJAut`. An explicit
  index-`7` mirror pair with invariant vector `(7, 0, 1, 1, {6, 1})` shows that `invariants` is
  not a complete conjugacy invariant (`exists_not_conj_invariants_eq`).

## References

* M. H. Millington, *Subgroups of the classical modular group*, J. London Math. Soc. (2) 1 (1969),
  351–357.
* C. Kurth, L. Long, *Computations with finite index subgroups of `PSL₂(ℤ)` using Farey
  symbols*, in *Advances in Algebra and Combinatorics*, World Scientific (2008), 225–242,
  arXiv:0710.1835.
* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics
  228, Springer, 2005, §3.1 (the genus formula for finite-index subgroups of `SL(2, ℤ)`).
-/

open Equiv Equiv.Perm Matrix
open scoped MatrixGroups Pointwise

public section

namespace TauCeti.ModularGroup

open _root_.ModularGroup PermutationTriple

variable {m n : ℕ}

/-! ### Cusp widths and cusp count -/

/-- The multiset of cusp widths of `Γ' ≤ PSL(2, ℤ)`, read as the full cycle type of
`permT Γ' e` (including `1`-cycles for fixed points). -/
noncomputable def cuspWidths (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Multiset ℕ :=
  (permT Γ' e).fullCycleType

/-- The defining formula for `cuspWidths`. -/
theorem cuspWidths_def (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspWidths Γ' e = (permT Γ' e).fullCycleType := (rfl)

/-- `cuspWidths Γ' e` is the `∞`-component of the cycle data of `modularTriple Γ' e`. -/
theorem cuspWidths_eq_cycleData (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspWidths Γ' e = (modularTriple Γ' e).cycleData.2.2 := by
  rw [cuspWidths_def, cycleData_σinf, fullCycleType_def, permT]

/-- The cusp widths of an index-`n` subgroup sum to `n`. -/
@[simp]
theorem sum_cuspWidths (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (cuspWidths Γ' e).sum = n := by
  simp [cuspWidths_def]

/-- Every cusp width is positive. -/
theorem pos_of_mem_cuspWidths {Γ' : Subgroup PSL(2, ℤ)} {e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n}
    {w : ℕ} (hw : w ∈ cuspWidths Γ' e) : 0 < w :=
  Equiv.Perm.pos_of_mem_fullCycleType hw

/-- Equivalent modular triples have the same multiset of cusp widths. -/
theorem cuspWidths_eq_of_equivalent {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : (modularTriple Γ₁ e₁).Equivalent (modularTriple Γ₂ e₂)) :
    cuspWidths Γ₁ e₁ = cuspWidths Γ₂ e₂ := by
  rw [cuspWidths_eq_cycleData, cuspWidths_eq_cycleData, cycleData_eq_of_equivalent h]

/-- The multiset of cusp widths does not depend on the coset enumeration. -/
theorem cuspWidths_congr (Γ' : Subgroup PSL(2, ℤ)) (e₁ e₂ : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspWidths Γ' e₁ = cuspWidths Γ' e₂ :=
  cuspWidths_eq_of_equivalent (equivalent_modularTriple Γ' e₁ e₂)

/-- Conjugate subgroups of `PSL(2, ℤ)` have the same multiset of cusp widths. -/
theorem cuspWidths_eq_of_conj {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : ∃ g : ConjAct PSL(2, ℤ), g • Γ₁ = Γ₂) :
    cuspWidths Γ₁ e₁ = cuspWidths Γ₂ e₂ :=
  cuspWidths_eq_of_equivalent ((millington e₁ e₂).mpr h)

/-- The mirror subgroup `Γ'.map conjJAut` has the same multiset of cusp widths as `Γ'`. -/
theorem cuspWidths_map_conjJAut (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (e' : PSL(2, ℤ) ⧸ Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ)) ≃ Fin n) :
    cuspWidths (Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))) e' = cuspWidths Γ' e := by
  rw [cuspWidths_eq_cycleData, cuspWidths_eq_cycleData,
    cycleData_eq_of_equivalent (equivalent_mirror_modularTriple Γ' e e'), cycleData_mirror]

/-- The full modular group `⊤` has a single cusp of width `1`. -/
@[simp]
theorem cuspWidths_top (e : PSL(2, ℤ) ⧸ (⊤ : Subgroup PSL(2, ℤ)) ≃ Fin 1) :
    cuspWidths ⊤ e = {1} := by
  rw [cuspWidths_def, permT, modularTriple_top, one_σinf, fullCycleType_one]
  rfl

/-- The number of cusps of `Γ' ≤ PSL(2, ℤ)`, read as the number of cycles (including fixed
points) of `permT Γ' e`. -/
noncomputable def cuspCount (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ℕ :=
  orbitCount (permT Γ' e)

/-- The defining formula for `cuspCount`. -/
theorem cuspCount_def (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspCount Γ' e = orbitCount (permT Γ' e) := (rfl)

/-- The cusp count is the number of parts in `cuspWidths Γ' e`. -/
theorem cuspCount_eq_card_cuspWidths (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspCount Γ' e = (cuspWidths Γ' e).card := by
  rw [cuspCount_def, cuspWidths_def, fullCycleType_def, orbitCount_eq_card_parts_partition]

/-- Every finite-index subgroup of `PSL(2, ℤ)` has at least one cusp. -/
theorem cuspCount_pos (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    0 < cuspCount Γ' e := by
  have : Nonempty (Fin n) := ⟨e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')⟩
  exact (permT Γ' e).orbitCount_pos

/-- An index-`n` subgroup of `PSL(2, ℤ)` has at most `n` cusps. -/
theorem cuspCount_le (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspCount Γ' e ≤ n := by
  simpa [cuspCount_def] using (permT Γ' e).orbitCount_le_card

/-- Equivalent modular triples have the same cusp count. -/
theorem cuspCount_eq_of_equivalent {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : (modularTriple Γ₁ e₁).Equivalent (modularTriple Γ₂ e₂)) :
    cuspCount Γ₁ e₁ = cuspCount Γ₂ e₂ := by
  rw [cuspCount_eq_card_cuspWidths, cuspCount_eq_card_cuspWidths, cuspWidths_eq_of_equivalent h]

/-- The cusp count does not depend on the coset enumeration. -/
theorem cuspCount_congr (Γ' : Subgroup PSL(2, ℤ)) (e₁ e₂ : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspCount Γ' e₁ = cuspCount Γ' e₂ :=
  cuspCount_eq_of_equivalent (equivalent_modularTriple Γ' e₁ e₂)

/-- Conjugate subgroups of `PSL(2, ℤ)` have the same cusp count. -/
theorem cuspCount_eq_of_conj {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : ∃ g : ConjAct PSL(2, ℤ), g • Γ₁ = Γ₂) :
    cuspCount Γ₁ e₁ = cuspCount Γ₂ e₂ :=
  cuspCount_eq_of_equivalent ((millington e₁ e₂).mpr h)

/-- The mirror subgroup `Γ'.map conjJAut` has the same cusp count as `Γ'`. -/
theorem cuspCount_map_conjJAut (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (e' : PSL(2, ℤ) ⧸ Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ)) ≃ Fin n) :
    cuspCount (Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))) e' = cuspCount Γ' e := by
  rw [cuspCount_eq_card_cuspWidths, cuspCount_eq_card_cuspWidths, cuspWidths_map_conjJAut]

/-- The full modular group `⊤` has `1` cusp. -/
@[simp]
theorem cuspCount_top (e : PSL(2, ℤ) ⧸ (⊤ : Subgroup PSL(2, ℤ)) ≃ Fin 1) :
    cuspCount ⊤ e = 1 := by
  rw [cuspCount_eq_card_cuspWidths, cuspWidths_top, Multiset.card_singleton]

/-! ### Cycle periods of `permT`, double cosets, and width ratios -/

/-- Integer powers of `permT Γ' e` act on `e (g Γ')` by left multiplication by `T ^ k`. -/
theorem permT_zpow_apply (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (g : PSL(2, ℤ)) (k : ℤ) :
    ((permT Γ' e) ^ k) (e (g : PSL(2, ℤ) ⧸ Γ')) =
      e ((((T : PSL(2, ℤ)) ^ k * g : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) := by
  rw [permT, modularTriple_σinf, ← map_zpow, Equiv.permutationRepresentation_apply,
    Equiv.symm_apply_apply, MulAction.Quotient.smul_mk, smul_eq_mul]

/-- Natural powers of `permT Γ' e` act on `e (g Γ')` by left multiplication by `T ^ k`. -/
theorem permT_pow_apply (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (g : PSL(2, ℤ)) (k : ℕ) :
    ((permT Γ' e) ^ k) (e (g : PSL(2, ℤ) ⧸ Γ')) =
      e ((((T : PSL(2, ℤ)) ^ k * g : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) := by
  simpa only [zpow_natCast] using permT_zpow_apply Γ' e g k

/-- The period of `permT Γ' e` at `e (g Γ')` divides `h` if and only if
`g⁻¹ T ^ h g ∈ Γ'`. -/
theorem minimalPeriod_permT_dvd_iff (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (g : PSL(2, ℤ)) (h : ℕ) :
    Function.minimalPeriod (permT Γ' e) (e (g : PSL(2, ℤ) ⧸ Γ')) ∣ h ↔
      g⁻¹ * (T : PSL(2, ℤ)) ^ h * g ∈ Γ' := by
  have hiter : (permT Γ' e)^[h] (e (g : PSL(2, ℤ) ⧸ Γ')) =
      e ((((T : PSL(2, ℤ)) ^ h * g : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) := by
    rw [← Equiv.Perm.coe_pow, permT_pow_apply]
  rw [← Function.isPeriodicPt_iff_minimalPeriod_dvd, Function.IsPeriodicPt, Function.IsFixedPt,
    hiter, e.apply_eq_iff_eq, QuotientGroup.eq]
  have hconj : ((T : PSL(2, ℤ)) ^ h * g)⁻¹ * g =
      (g⁻¹ * (T : PSL(2, ℤ)) ^ h * g)⁻¹ := by group
  rw [hconj, Subgroup.inv_mem_iff]

/-- Lifted to `SL(2, ℤ)`, the period of `permT Γ' e` at `e (σ Γ')` divides `h` if and only if
`σ⁻¹ T ^ h σ ∈ Γ'.liftSL`. -/
theorem minimalPeriod_permT_mk_dvd_iff (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (σ : SL(2, ℤ)) (h : ℕ) :
    Function.minimalPeriod (permT Γ' e) (e ((σ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) ∣ h ↔
      σ⁻¹ * _root_.ModularGroup.T ^ h * σ ∈ Γ'.liftSL := by
  rw [minimalPeriod_permT_dvd_iff, Subgroup.mem_liftSL, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]

/-- Every point has positive minimal period under `permT Γ' e`. -/
theorem minimalPeriod_permT_pos (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (x : Fin n) : 0 < Function.minimalPeriod (permT Γ' e) x := by
  refine Function.minimalPeriod_pos_of_mem_periodicPts ?_
  exact ⟨orderOf (permT Γ' e), orderOf_pos _, by
    rw [Function.IsPeriodicPt, Function.IsFixedPt, ← Equiv.Perm.coe_pow, pow_orderOf_eq_one,
      Equiv.Perm.coe_one, id_eq]⟩

/-- The period of `permT Γ' e` at `e (g Γ')` is the least positive integer `h` with
`g⁻¹ T ^ h g ∈ Γ'`. -/
theorem minimalPeriod_permT_eq_sInf (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (g : PSL(2, ℤ)) :
    Function.minimalPeriod (permT Γ' e) (e (g : PSL(2, ℤ) ⧸ Γ')) =
      sInf {h : ℕ | 0 < h ∧ g⁻¹ * (T : PSL(2, ℤ)) ^ h * g ∈ Γ'} := by
  set p := Function.minimalPeriod (permT Γ' e) (e (g : PSL(2, ℤ) ⧸ Γ'))
  have hp : 0 < p := minimalPeriod_permT_pos Γ' e _
  have hmem : p ∈ {h : ℕ | 0 < h ∧ g⁻¹ * (T : PSL(2, ℤ)) ^ h * g ∈ Γ'} :=
    ⟨hp, (minimalPeriod_permT_dvd_iff Γ' e g p).mp dvd_rfl⟩
  exact le_antisymm
    (le_csInf ⟨p, hmem⟩ fun h ⟨hh, hmem'⟩ ↦
      Nat.le_of_dvd hh ((minimalPeriod_permT_dvd_iff Γ' e g h).mpr hmem'))
    (Nat.sInf_le hmem)

/-- For `σ : SL(2, ℤ)`, the period of `permT Γ' e` at the coset `e (σ⁻¹ Γ')` (for the cusp
`σ • ∞`) is the least positive `h` with `σ T ^ h σ⁻¹ ∈ Γ'.liftSL`. -/
theorem minimalPeriod_permT_mk_inv_eq_sInf (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (σ : SL(2, ℤ)) :
    Function.minimalPeriod (permT Γ' e)
        (e (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) =
      sInf {h : ℕ | 0 < h ∧ σ * _root_.ModularGroup.T ^ h * σ⁻¹ ∈ Γ'.liftSL} := by
  rw [minimalPeriod_permT_eq_sInf]
  congr 1
  ext h
  simp [Subgroup.mem_liftSL, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]

/-- At the base coset `e 1` (the cusp `∞`), the period of `permT Γ' e` is the least positive `h`
with `T ^ h ∈ Γ'.liftSL`. -/
theorem minimalPeriod_permT_one (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Function.minimalPeriod (permT Γ' e) (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) =
      sInf {h : ℕ | 0 < h ∧ _root_.ModularGroup.T ^ h ∈ Γ'.liftSL} := by
  simpa using minimalPeriod_permT_mk_inv_eq_sInf Γ' e 1

/-- Two cosets `e (g₁ Γ')` and `e (g₂ Γ')` lie in the same cycle of `permT Γ' e` if and only
if `g₁⁻¹` and `g₂⁻¹` lie in the same double coset in `Γ' \ PSL(2, ℤ) / ⟨T⟩`. -/
theorem sameCycle_permT_iff_doubleCoset (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (g₁ g₂ : PSL(2, ℤ)) :
    (permT Γ' e).SameCycle (e (g₁ : PSL(2, ℤ) ⧸ Γ')) (e (g₂ : PSL(2, ℤ) ⧸ Γ')) ↔
      DoubleCoset.mk Γ' (Subgroup.zpowers (T : PSL(2, ℤ))) g₁⁻¹ =
        DoubleCoset.mk Γ' (Subgroup.zpowers (T : PSL(2, ℤ))) g₂⁻¹ := by
  rw [DoubleCoset.eq]
  constructor
  · rintro ⟨k, hk⟩
    rw [permT_zpow_apply, e.apply_eq_iff_eq, QuotientGroup.eq] at hk
    refine ⟨(((T : PSL(2, ℤ)) ^ k * g₁)⁻¹ * g₂)⁻¹, Γ'.inv_mem hk,
      (T : PSL(2, ℤ)) ^ (-k), Subgroup.zpow_mem_zpowers _ _, ?_⟩
    rw [_root_.zpow_neg]
    group
  · rintro ⟨γ, hγ, t, ht, h⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    refine ⟨-k, ?_⟩
    rw [permT_zpow_apply, e.apply_eq_iff_eq, QuotientGroup.eq]
    have hinv : g₂ = (T : PSL(2, ℤ)) ^ (-k) * g₁ * γ⁻¹ := by
      have := congrArg Inv.inv h
      simpa [_root_.mul_inv_rev, mul_assoc, _root_.zpow_neg] using this
    have hcalc : ((T : PSL(2, ℤ)) ^ (-k) * g₁)⁻¹ * g₂ = γ⁻¹ := by
      rw [hinv]
      group
    rw [hcalc]
    exact Γ'.inv_mem hγ

/-- **Double-coset bijection for cusps.** The cycles of `permT Γ' e` are in canonical bijection
with the double cosets `Γ' \ PSL(2, ℤ) / ⟨T⟩`, sending the cycle of `e (g Γ')` to
`Γ' g⁻¹ ⟨T⟩`. -/
noncomputable def permTCycleEquivDoubleCoset (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Quotient (SameCycle.setoid (permT Γ' e)) ≃
      DoubleCoset.Quotient (Γ' : Set PSL(2, ℤ)) (Subgroup.zpowers (T : PSL(2, ℤ))) := by
  let f : Fin n →
      DoubleCoset.Quotient (Γ' : Set PSL(2, ℤ)) (Subgroup.zpowers (T : PSL(2, ℤ))) :=
    fun x ↦ DoubleCoset.mk Γ' (Subgroup.zpowers (T : PSL(2, ℤ))) (Quotient.out (e.symm x))⁻¹
  have hf_mk (g : PSL(2, ℤ)) :
      f (e (g : PSL(2, ℤ) ⧸ Γ')) =
        DoubleCoset.mk Γ' (Subgroup.zpowers (T : PSL(2, ℤ))) g⁻¹ := by
    dsimp only [f]
    rw [e.symm_apply_apply]
    have hq : ((Quotient.out (g : PSL(2, ℤ) ⧸ Γ') : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ') =
        (g : PSL(2, ℤ) ⧸ Γ') := Quotient.out_eq _
    rw [QuotientGroup.eq] at hq
    rw [DoubleCoset.eq]
    refine ⟨((Quotient.out (g : PSL(2, ℤ) ⧸ Γ'))⁻¹ * g)⁻¹, Γ'.inv_mem hq,
      1, Subgroup.one_mem _, ?_⟩
    group
  have hiff (x y : Fin n) : (permT Γ' e).SameCycle x y ↔ f x = f y := by
    obtain ⟨qx, rfl⟩ := e.surjective x
    obtain ⟨qy, rfl⟩ := e.surjective y
    induction qx using QuotientGroup.induction_on with
    | H g₁ =>
      induction qy using QuotientGroup.induction_on with
      | H g₂ =>
        rw [hf_mk, hf_mk, sameCycle_permT_iff_doubleCoset]
  refine Equiv.ofBijective
    (Quotient.lift f fun x y h ↦ (hiff x y).mp h) ⟨?_, ?_⟩
  · intro q₁ q₂ hq
    induction q₁ using Quotient.ind with
    | _ x =>
      induction q₂ using Quotient.ind with
      | _ y =>
        exact Quotient.sound ((hiff x y).mpr hq)
  · intro d
    induction d using Quotient.ind' with
    | _ g =>
      refine ⟨Quotient.mk _ (e ((g⁻¹ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')), ?_⟩
      change f (e ((g⁻¹ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) = DoubleCoset.mk _ _ g
      rw [hf_mk, inv_inv]

/-- `permTCycleEquivDoubleCoset` sends the cycle of `e (g Γ')` to the double coset
`Γ' g⁻¹ ⟨T⟩`. -/
@[simp]
theorem permTCycleEquivDoubleCoset_mk (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (g : PSL(2, ℤ)) :
    permTCycleEquivDoubleCoset Γ' e (Quotient.mk _ (e (g : PSL(2, ℤ) ⧸ Γ'))) =
      DoubleCoset.mk Γ' (Subgroup.zpowers (T : PSL(2, ℤ))) g⁻¹ := by
  change DoubleCoset.mk Γ' (Subgroup.zpowers (T : PSL(2, ℤ)))
      (Quotient.out (e.symm (e (g : PSL(2, ℤ) ⧸ Γ'))))⁻¹ =
    DoubleCoset.mk Γ' (Subgroup.zpowers (T : PSL(2, ℤ))) g⁻¹
  rw [e.symm_apply_apply]
  have hq : ((Quotient.out (g : PSL(2, ℤ) ⧸ Γ') : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ') =
      (g : PSL(2, ℤ) ⧸ Γ') := Quotient.out_eq _
  rw [QuotientGroup.eq] at hq
  rw [DoubleCoset.eq]
  exact ⟨((Quotient.out (g : PSL(2, ℤ) ⧸ Γ'))⁻¹ * g)⁻¹, Γ'.inv_mem hq,
    1, Subgroup.one_mem _, by group⟩

/-- The cusp count equals the number of double cosets `Γ' \ PSL(2, ℤ) / ⟨T⟩`. -/
theorem cuspCount_eq_card_doubleCoset (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspCount Γ' e = Nat.card
      (DoubleCoset.Quotient (Γ' : Set PSL(2, ℤ)) (Subgroup.zpowers (T : PSL(2, ℤ)))) := by
  rw [cuspCount_def, orbitCount_def, Nat.card_congr (permTCycleEquivDoubleCoset Γ' e)]

/-- **Divisibility of cusp widths under subgroup inclusion.** If `Γ'' ≤ Γ'`, then the cusp width
of `Γ'` at `g Γ'` divides the cusp width of `Γ''` at `g Γ''`. -/
theorem minimalPeriod_permT_dvd_of_le {Γ'' Γ' : Subgroup PSL(2, ℤ)} (h : Γ'' ≤ Γ')
    (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m) (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (g : PSL(2, ℤ)) :
    Function.minimalPeriod (permT Γ' e') (e' (g : PSL(2, ℤ) ⧸ Γ')) ∣
      Function.minimalPeriod (permT Γ'' e'') (e'' (g : PSL(2, ℤ) ⧸ Γ'')) :=
  (minimalPeriod_permT_dvd_iff Γ' e' g _).mpr <|
    h ((minimalPeriod_permT_dvd_iff Γ'' e'' g _).mp dvd_rfl)

private theorem quotientEquivProdOfLE_mk_fst {Γ'' Γ' : Subgroup PSL(2, ℤ)} (h : Γ'' ≤ Γ')
    (g : PSL(2, ℤ)) :
    (Subgroup.quotientEquivProdOfLE h (g : PSL(2, ℤ) ⧸ Γ'')).1 = (g : PSL(2, ℤ) ⧸ Γ') :=
  rfl

/-- The canonical map on `permT`-cycles induced by a subgroup inclusion `Γ'' ≤ Γ'`, sending the
cycle of `e'' (g Γ'')` to the cycle of `e' (g Γ')`. -/
noncomputable def cuspCycleMapOfLE {Γ'' Γ' : Subgroup PSL(2, ℤ)} (h : Γ'' ≤ Γ')
    (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m) (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Quotient (SameCycle.setoid (permT Γ'' e'')) → Quotient (SameCycle.setoid (permT Γ' e')) :=
  Quotient.map (fun y ↦ e' (Subgroup.quotientEquivProdOfLE h (e''.symm y)).1)
    fun y₁ y₂ hy ↦ by
    obtain ⟨k, rfl⟩ := hy
    obtain ⟨q₁, rfl⟩ := e''.surjective y₁
    induction q₁ using QuotientGroup.induction_on with
    | H g =>
      refine ⟨k, ?_⟩
      rw [permT_zpow_apply, e''.symm_apply_apply, e''.symm_apply_apply,
        quotientEquivProdOfLE_mk_fst, quotientEquivProdOfLE_mk_fst, permT_zpow_apply]

/-- `cuspCycleMapOfLE` sends the cycle of `e'' (g Γ'')` to the cycle of `e' (g Γ')`. -/
@[simp]
theorem cuspCycleMapOfLE_mk {Γ'' Γ' : Subgroup PSL(2, ℤ)} (h : Γ'' ≤ Γ')
    (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m) (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (g : PSL(2, ℤ)) :
    cuspCycleMapOfLE h e'' e' (Quotient.mk _ (e'' (g : PSL(2, ℤ) ⧸ Γ''))) =
      Quotient.mk _ (e' (g : PSL(2, ℤ) ⧸ Γ')) := by
  change Quotient.mk _ (e' (Subgroup.quotientEquivProdOfLE h (e''.symm (e'' _))).1) = _
  rw [e''.symm_apply_apply, quotientEquivProdOfLE_mk_fst]

/-- The width of a `permT`-cycle, well-defined on `Quotient (SameCycle.setoid (permT Γ' e))`. -/
noncomputable def cuspCycleWidth (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Quotient (SameCycle.setoid (permT Γ' e)) → ℕ :=
  Quotient.lift (Function.minimalPeriod (permT Γ' e)) fun _ _ h ↦ h.minimalPeriod_eq

/-- On the cycle of `x`, `cuspCycleWidth` is `Function.minimalPeriod (permT Γ' e) x`. -/
@[simp]
theorem cuspCycleWidth_mk (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (x : Fin n) :
    cuspCycleWidth Γ' e (Quotient.mk _ x) = Function.minimalPeriod (permT Γ' e) x := (rfl)

/-- `cuspWidths Γ' e` is the multiset of `cuspCycleWidth Γ' e` over all `permT`-cycles. -/
theorem cuspWidths_eq_map_cuspCycleWidth (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    [Fintype (Quotient (SameCycle.setoid (permT Γ' e)))] :
    cuspWidths Γ' e = Finset.univ.val.map (cuspCycleWidth Γ' e) :=
  fullCycleType_eq_map_univ (permT Γ' e) (Equiv.refl _) fun _ ↦ rfl

/-- The period of `permT Γ' e` at any point `x` belongs to `cuspWidths Γ' e`. -/
theorem minimalPeriod_permT_mem_cuspWidths (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (x : Fin n) :
    Function.minimalPeriod (permT Γ' e) x ∈ cuspWidths Γ' e := by
  classical
  have := Fintype.ofFinite (Quotient (SameCycle.setoid (permT Γ' e)))
  rw [cuspWidths_eq_map_cuspCycleWidth]
  exact Multiset.mem_map.mpr ⟨Quotient.mk _ x, Finset.mem_univ _, rfl⟩

/-- For any inclusion `Γ'' ≤ Γ'`, the width of the image cusp divides the width of each cusp
above it. -/
theorem cuspCycleWidth_map_dvd {Γ'' Γ' : Subgroup PSL(2, ℤ)} (h : Γ'' ≤ Γ')
    (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m) (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (q : Quotient (SameCycle.setoid (permT Γ'' e''))) :
    cuspCycleWidth Γ' e' (cuspCycleMapOfLE h e'' e' q) ∣ cuspCycleWidth Γ'' e'' q := by
  induction q using Quotient.ind with
  | _ y =>
    obtain ⟨qy, rfl⟩ := e''.surjective y
    induction qy using QuotientGroup.induction_on with
    | H g =>
      rw [cuspCycleMapOfLE_mk, cuspCycleWidth_mk, cuspCycleWidth_mk]
      exact minimalPeriod_permT_dvd_of_le h e'' e' g

private theorem card_filter_cuspCycle_eq (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    [DecidableEq (Quotient (SameCycle.setoid (permT Γ' e)))]
    (q : Quotient (SameCycle.setoid (permT Γ' e))) :
    (Finset.univ.filter (fun y : Fin n ↦
        Quotient.mk (SameCycle.setoid (permT Γ' e)) y = q)).card =
      cuspCycleWidth Γ' e q := by
  induction q using Quotient.ind with
  | _ x =>
    rw [cuspCycleWidth_mk, ← Equiv.Perm.ncard_setOf_sameCycle, ← Set.ncard_coe_finset]
    congr 1
    ext y
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      Quotient.eq]
    exact ⟨SameCycle.symm, SameCycle.symm⟩

/-- **Sum of cusp widths over a cusp under subgroup inclusion.** For `Γ'' ≤ Γ'`, the widths of
the cusps of `Γ''` lying over a cusp `c` of `Γ'` sum to `[Γ' : Γ''] · width(c)`. -/
theorem sum_cuspCycleWidth_fiber_of_le {Γ'' Γ' : Subgroup PSL(2, ℤ)} (h : Γ'' ≤ Γ')
    (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m) (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (c : Quotient (SameCycle.setoid (permT Γ' e'))) :
    ∑ᶠ q ∈ {q | cuspCycleMapOfLE h e'' e' q = c}, cuspCycleWidth Γ'' e'' q =
      Γ''.relIndex Γ' * cuspCycleWidth Γ' e' c := by
  classical
  have : Fintype (Quotient (SameCycle.setoid (permT Γ'' e''))) := Fintype.ofFinite _
  let proj : Fin m → Fin n := fun y ↦ e' (Subgroup.quotientEquivProdOfLE h (e''.symm y)).1
  have hproj_mk (y : Fin m) :
      cuspCycleMapOfLE h e'' e' (Quotient.mk _ y) = Quotient.mk _ (proj y) := rfl
  have hsum :
      ∑ᶠ q ∈ {q | cuspCycleMapOfLE h e'' e' q = c}, cuspCycleWidth Γ'' e'' q =
        (Finset.univ.filter (fun y : Fin m ↦
          Quotient.mk (SameCycle.setoid (permT Γ' e')) (proj y) = c)).card := by
    have hSfin : ({q | cuspCycleMapOfLE h e'' e' q = c} : Set _).Finite := Set.toFinite _
    rw [finsum_mem_eq_finite_toFinset_sum _ hSfin]
    have htoFin : hSfin.toFinset =
        Finset.univ.filter (fun q ↦ cuspCycleMapOfLE h e'' e' q = c) := by
      ext q
      simp
    rw [htoFin, Finset.card_eq_sum_ones, ← Finset.sum_fiberwise_of_maps_to
      (g := Quotient.mk (SameCycle.setoid (permT Γ'' e'')))
      (t := Finset.univ.filter (fun q ↦ cuspCycleMapOfLE h e'' e' q = c))
      (fun y hy ↦ by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        rwa [hproj_mk])]
    refine Finset.sum_congr rfl fun q hq ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    rw [← Finset.card_eq_sum_ones]
    have hfilt : (Finset.univ.filter (fun y : Fin m ↦
        Quotient.mk (SameCycle.setoid (permT Γ' e')) (proj y) = c)).filter
          (fun y ↦ Quotient.mk (SameCycle.setoid (permT Γ'' e'')) y = q) =
        Finset.univ.filter
          (fun y : Fin m ↦ Quotient.mk (SameCycle.setoid (permT Γ'' e'')) y = q) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
      intro hy
      rw [← hproj_mk, hy, hq]
    rw [hfilt]
    exact (card_filter_cuspCycle_eq Γ'' e'' q).symm
  rw [hsum]
  let eqv : {y : Fin m // Quotient.mk (SameCycle.setoid (permT Γ' e')) (proj y) = c} ≃
      {x : Fin n // Quotient.mk (SameCycle.setoid (permT Γ' e')) x = c} ×
        (Γ' ⧸ Γ''.subgroupOf Γ') :=
    { toFun := fun ⟨y, hy⟩ ↦
        ⟨⟨proj y, hy⟩, (Subgroup.quotientEquivProdOfLE h (e''.symm y)).2⟩
      invFun := fun ⟨⟨x, hx⟩, r⟩ ↦
        ⟨e'' ((Subgroup.quotientEquivProdOfLE h).symm (e'.symm x, r)), by
          dsimp only [proj]
          rw [e''.symm_apply_apply, Equiv.apply_symm_apply, e'.apply_symm_apply]
          exact hx⟩
      left_inv := fun ⟨y, _⟩ ↦ Subtype.ext <| by
        dsimp only [proj]
        rw [e'.symm_apply_apply, Prod.mk.eta, Equiv.symm_apply_apply, e''.apply_symm_apply]
      right_inv := fun ⟨⟨x, _⟩, r⟩ ↦ Prod.ext
        (Subtype.ext <| by
          dsimp only [proj]
          rw [e''.symm_apply_apply, Equiv.apply_symm_apply, e'.apply_symm_apply])
        (by
          dsimp only
          rw [e''.symm_apply_apply, Equiv.apply_symm_apply]) }
  have hfin : Finite (Γ' ⧸ Γ''.subgroupOf Γ') :=
    have : Finite (PSL(2, ℤ) ⧸ Γ'') := Finite.of_equiv (Fin m) e''.symm
    have : Finite ((PSL(2, ℤ) ⧸ Γ') × (Γ' ⧸ Γ''.subgroupOf Γ')) :=
      Finite.of_equiv (PSL(2, ℤ) ⧸ Γ'') (Subgroup.quotientEquivProdOfLE h)
    have : Nonempty (PSL(2, ℤ) ⧸ Γ') := ⟨(1 : PSL(2, ℤ))⟩
    Finite.of_surjective (Prod.snd : (PSL(2, ℤ) ⧸ Γ') × _ → _) Prod.snd_surjective
  have := Fintype.ofFinite (Γ' ⧸ Γ''.subgroupOf Γ')
  rw [← Fintype.card_subtype, Fintype.card_congr eqv, Fintype.card_prod, mul_comm,
    ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, Fintype.card_subtype,
    card_filter_cuspCycle_eq Γ' e' c]
  rfl

/-- **Sum of width ratios (ramification indices) over a cusp.** For `Γ'' ≤ Γ'`, the cusp width
ratios `width(c'') / width(c)` over all cusps `c''` of `Γ''` lying above `c` sum to
`[Γ' : Γ'']`. -/
theorem sum_widthRatio_permT_fiber_of_le {Γ'' Γ' : Subgroup PSL(2, ℤ)} (h : Γ'' ≤ Γ')
    (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m) (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (c : Quotient (SameCycle.setoid (permT Γ' e'))) :
    ∑ᶠ q ∈ {q | cuspCycleMapOfLE h e'' e' q = c},
        (cuspCycleWidth Γ'' e'' q / cuspCycleWidth Γ' e' c) =
      Γ''.relIndex Γ' := by
  classical
  have hpos : 0 < cuspCycleWidth Γ' e' c := by
    induction c using Quotient.ind with
    | _ x => exact minimalPeriod_permT_pos Γ' e' x
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  have hSfin : ({q | cuspCycleMapOfLE h e'' e' q = c} : Set _).Finite := Set.toFinite _
  rw [← sum_cuspCycleWidth_fiber_of_le h e'' e' c,
    finsum_mem_eq_finite_toFinset_sum _ hSfin,
    finsum_mem_eq_finite_toFinset_sum _ hSfin, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q hq ↦ ?_
  rw [hSfin.mem_toFinset] at hq
  exact Nat.div_mul_cancel (hq ▸ cuspCycleWidth_map_dvd h e'' e' q)

/-! ### Elliptic points of order two and three -/

/-- The number of order-`2` elliptic points of `Γ' ≤ PSL(2, ℤ)`, read as the number of fixed
points of `permS Γ' e`. -/
noncomputable def ellipticTwo (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) : ℕ :=
  Fintype.card {x : Fin n // permS Γ' e x = x}

/-- The defining formula for `ellipticTwo`. -/
theorem ellipticTwo_def (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ellipticTwo Γ' e = Fintype.card {x : Fin n // permS Γ' e x = x} := (rfl)

/-- The number of order-`3` elliptic points of `Γ' ≤ PSL(2, ℤ)`, read as the number of fixed
points of `(modularTriple Γ' e).σ0`. -/
noncomputable def ellipticThree (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) : ℕ :=
  Fintype.card {x : Fin n // (modularTriple Γ' e).σ0 x = x}

/-- The defining formula for `ellipticThree`. -/
theorem ellipticThree_def (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ellipticThree Γ' e = Fintype.card {x : Fin n // (modularTriple Γ' e).σ0 x = x} := (rfl)

/-- `ellipticTwo Γ' e` counts the `1`-cycles in the full cycle type of `permS Γ' e`. -/
theorem ellipticTwo_eq_count_one_fullCycleType (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ellipticTwo Γ' e = (permS Γ' e).fullCycleType.count 1 := by
  rw [ellipticTwo_def, card_subtype_apply_eq, count_one_fullCycleType]

/-- `ellipticThree Γ' e` counts the `1`-cycles in the full cycle type of
`(modularTriple Γ' e).σ0`. -/
theorem ellipticThree_eq_count_one_fullCycleType (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ellipticThree Γ' e = (modularTriple Γ' e).σ0.fullCycleType.count 1 := by
  rw [ellipticThree_def, card_subtype_apply_eq, count_one_fullCycleType]

/-- `ellipticThree Γ' e` equally counts the fixed points of `permR Γ' e`, since `permR` is
conjugate to `σ0⁻¹`. -/
theorem ellipticThree_eq_card_fixed_permR (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ellipticThree Γ' e = Fintype.card {x : Fin n // permR Γ' e x = x} := by
  have hconj : permR Γ' e =
      (permS Γ' e)⁻¹ * (modularTriple Γ' e).σ0⁻¹ * ((permS Γ' e)⁻¹)⁻¹ := by
    simpa only [inv_inv] using permR_eq_permS_inv_mul_σ0_inv_mul_permS Γ' e
  rw [ellipticThree_eq_count_one_fullCycleType, card_subtype_apply_eq, ← count_one_fullCycleType,
    hconj, fullCycleType_conj, fullCycleType_inv]

/-- `permS Γ' e` fixes `e (g Γ')` if and only if `g⁻¹ S g ∈ Γ'`. -/
theorem permS_apply_eq_self_iff (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (g : PSL(2, ℤ)) :
    permS Γ' e (e (g : PSL(2, ℤ) ⧸ Γ')) = e (g : PSL(2, ℤ) ⧸ Γ') ↔
      g⁻¹ * (S : PSL(2, ℤ)) * g ∈ Γ' := by
  rw [permS, modularTriple_σ1, Equiv.permutationRepresentation_apply, Equiv.symm_apply_apply,
    MulAction.Quotient.smul_mk, smul_eq_mul, e.apply_eq_iff_eq, QuotientGroup.eq]
  have hconj : ((S : PSL(2, ℤ)) * g)⁻¹ * g = (g⁻¹ * (S : PSL(2, ℤ)) * g)⁻¹ := by group
  rw [hconj, Subgroup.inv_mem_iff]

/-- `(modularTriple Γ' e).σ0` fixes `e (g Γ')` if and only if `g⁻¹ U g ∈ Γ'`. -/
theorem modularTriple_σ0_apply_eq_self_iff (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (g : PSL(2, ℤ)) :
    (modularTriple Γ' e).σ0 (e (g : PSL(2, ℤ) ⧸ Γ')) = e (g : PSL(2, ℤ) ⧸ Γ') ↔
      g⁻¹ * (U : PSL(2, ℤ)) * g ∈ Γ' := by
  rw [modularTriple_σ0, Equiv.permutationRepresentation_apply, Equiv.symm_apply_apply,
    MulAction.Quotient.smul_mk, smul_eq_mul, e.apply_eq_iff_eq, QuotientGroup.eq]
  have hconj : ((U : PSL(2, ℤ)) * g)⁻¹ * g = (g⁻¹ * (U : PSL(2, ℤ)) * g)⁻¹ := by group
  rw [hconj, Subgroup.inv_mem_iff]

/-- `permR Γ' e` fixes `e (g Γ')` if and only if `g⁻¹ R g ∈ Γ'`. -/
theorem permR_apply_eq_self_iff (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (g : PSL(2, ℤ)) :
    permR Γ' e (e (g : PSL(2, ℤ) ⧸ Γ')) = e (g : PSL(2, ℤ) ⧸ Γ') ↔
      g⁻¹ * (R : PSL(2, ℤ)) * g ∈ Γ' := by
  rw [permR_eq_permS_mul_permT, permS, permT, modularTriple_σ1, modularTriple_σinf, ← map_mul,
    ← QuotientGroup.mk_mul, ← R_def, Equiv.permutationRepresentation_apply,
    Equiv.symm_apply_apply, MulAction.Quotient.smul_mk, smul_eq_mul, e.apply_eq_iff_eq,
    QuotientGroup.eq]
  have hconj : ((R : PSL(2, ℤ)) * g)⁻¹ * g = (g⁻¹ * (R : PSL(2, ℤ)) * g)⁻¹ := by group
  rw [hconj, Subgroup.inv_mem_iff]

/-- Every cycle of `permS Γ' e` has length `1` or `2`, so
`2 * orbitCount (permS Γ' e) = n + e₂`. -/
theorem two_mul_orbitCount_permS (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    2 * orbitCount (permS Γ' e) = n + ellipticTwo Γ' e := by
  simpa [ellipticTwo_def, Nat.card_eq_fintype_card] using
    (permS Γ' e).prime_mul_orbitCount_of_pow_eq_one Nat.prime_two (modularTriple_σ1_sq Γ' e)

/-- Every cycle of `(modularTriple Γ' e).σ0` has length `1` or `3`, so
`3 * orbitCount σ0 = n + 2 * e₃`. -/
theorem three_mul_orbitCount_σ0 (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    3 * orbitCount (modularTriple Γ' e).σ0 = n + 2 * ellipticThree Γ' e := by
  simpa [ellipticThree_def, Nat.card_eq_fintype_card] using
    (modularTriple Γ' e).σ0.prime_mul_orbitCount_of_pow_eq_one Nat.prime_three
      (modularTriple_σ0_pow_three Γ' e)

/-- `ellipticTwo Γ' e ≡ n [MOD 2]`: the parity of order-`2` elliptic points matches the index. -/
theorem ellipticTwo_modEq_index (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ellipticTwo Γ' e ≡ n [MOD 2] := by
  simpa [ellipticTwo_def, Nat.card_eq_fintype_card] using
    (permS Γ' e).card_subtype_apply_eq_modEq_of_pow_prime_eq_one Nat.prime_two
      (modularTriple_σ1_sq Γ' e)

/-- `ellipticThree Γ' e ≡ n [MOD 3]`: the number of order-`3` elliptic points is congruent to the
index modulo `3`. -/
theorem ellipticThree_modEq_index (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ellipticThree Γ' e ≡ n [MOD 3] := by
  simpa [ellipticThree_def, Nat.card_eq_fintype_card] using
    (modularTriple Γ' e).σ0.card_subtype_apply_eq_modEq_of_pow_prime_eq_one Nat.prime_three
      (modularTriple_σ0_pow_three Γ' e)

/-- `ellipticTwo Γ' e ≤ n`. -/
theorem ellipticTwo_le (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ellipticTwo Γ' e ≤ n := by
  simpa [ellipticTwo_def] using Fintype.card_subtype_le (fun x : Fin n ↦ permS Γ' e x = x)

/-- `ellipticThree Γ' e ≤ n`. -/
theorem ellipticThree_le (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ellipticThree Γ' e ≤ n := by
  simpa [ellipticThree_def] using
    Fintype.card_subtype_le (fun x : Fin n ↦ (modularTriple Γ' e).σ0 x = x)

/-- Equivalent modular triples have the same number of order-`2` elliptic points. -/
theorem ellipticTwo_eq_of_equivalent {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : (modularTriple Γ₁ e₁).Equivalent (modularTriple Γ₂ e₂)) :
    ellipticTwo Γ₁ e₁ = ellipticTwo Γ₂ e₂ := by
  rw [ellipticTwo_eq_count_one_fullCycleType, ellipticTwo_eq_count_one_fullCycleType,
    fullCycleType_def, fullCycleType_def, ← cycleData_σ1, ← cycleData_σ1,
    cycleData_eq_of_equivalent h]

/-- `ellipticTwo` does not depend on the coset enumeration. -/
theorem ellipticTwo_congr (Γ' : Subgroup PSL(2, ℤ)) (e₁ e₂ : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ellipticTwo Γ' e₁ = ellipticTwo Γ' e₂ :=
  ellipticTwo_eq_of_equivalent (equivalent_modularTriple Γ' e₁ e₂)

/-- Conjugate subgroups of `PSL(2, ℤ)` have the same number of order-`2` elliptic points. -/
theorem ellipticTwo_eq_of_conj {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : ∃ g : ConjAct PSL(2, ℤ), g • Γ₁ = Γ₂) :
    ellipticTwo Γ₁ e₁ = ellipticTwo Γ₂ e₂ :=
  ellipticTwo_eq_of_equivalent ((millington e₁ e₂).mpr h)

/-- The mirror subgroup `Γ'.map conjJAut` has the same number of order-`2` elliptic points as
`Γ'`. -/
theorem ellipticTwo_map_conjJAut (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (e' : PSL(2, ℤ) ⧸ Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ)) ≃ Fin n) :
    ellipticTwo (Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))) e' = ellipticTwo Γ' e := by
  rw [ellipticTwo_eq_count_one_fullCycleType, ellipticTwo_eq_count_one_fullCycleType,
    fullCycleType_def, fullCycleType_def, ← cycleData_σ1, ← cycleData_σ1,
    cycleData_eq_of_equivalent (equivalent_mirror_modularTriple Γ' e e'), cycleData_mirror]

/-- The full modular group `⊤` has `1` elliptic point of order `2`. -/
@[simp]
theorem ellipticTwo_top (e : PSL(2, ℤ) ⧸ (⊤ : Subgroup PSL(2, ℤ)) ≃ Fin 1) :
    ellipticTwo ⊤ e = 1 := by
  rw [ellipticTwo_eq_count_one_fullCycleType, permS, modularTriple_top, one_σ1,
    count_one_fullCycleType]
  simp

/-- Equivalent modular triples have the same number of order-`3` elliptic points. -/
theorem ellipticThree_eq_of_equivalent {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : (modularTriple Γ₁ e₁).Equivalent (modularTriple Γ₂ e₂)) :
    ellipticThree Γ₁ e₁ = ellipticThree Γ₂ e₂ := by
  rw [ellipticThree_eq_count_one_fullCycleType, ellipticThree_eq_count_one_fullCycleType,
    fullCycleType_def, fullCycleType_def, ← cycleData_σ0, ← cycleData_σ0,
    cycleData_eq_of_equivalent h]

/-- `ellipticThree` does not depend on the coset enumeration. -/
theorem ellipticThree_congr (Γ' : Subgroup PSL(2, ℤ))
    (e₁ e₂ : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ellipticThree Γ' e₁ = ellipticThree Γ' e₂ :=
  ellipticThree_eq_of_equivalent (equivalent_modularTriple Γ' e₁ e₂)

/-- Conjugate subgroups of `PSL(2, ℤ)` have the same number of order-`3` elliptic points. -/
theorem ellipticThree_eq_of_conj {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : ∃ g : ConjAct PSL(2, ℤ), g • Γ₁ = Γ₂) :
    ellipticThree Γ₁ e₁ = ellipticThree Γ₂ e₂ :=
  ellipticThree_eq_of_equivalent ((millington e₁ e₂).mpr h)

/-- The mirror subgroup `Γ'.map conjJAut` has the same number of order-`3` elliptic points as
`Γ'`. -/
theorem ellipticThree_map_conjJAut (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (e' : PSL(2, ℤ) ⧸ Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ)) ≃ Fin n) :
    ellipticThree (Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))) e' = ellipticThree Γ' e := by
  rw [ellipticThree_eq_count_one_fullCycleType, ellipticThree_eq_count_one_fullCycleType,
    fullCycleType_def, fullCycleType_def, ← cycleData_σ0, ← cycleData_σ0,
    cycleData_eq_of_equivalent (equivalent_mirror_modularTriple Γ' e e'), cycleData_mirror]

/-- The full modular group `⊤` has `1` elliptic point of order `3`. -/
@[simp]
theorem ellipticThree_top (e : PSL(2, ℤ) ⧸ (⊤ : Subgroup PSL(2, ℤ)) ≃ Fin 1) :
    ellipticThree ⊤ e = 1 := by
  rw [ellipticThree_eq_count_one_fullCycleType, modularTriple_top, one_σ0, count_one_fullCycleType]
  simp

/-! ### Genus and the integral genus formula -/

/-- The genus of a finite-index subgroup `Γ' ≤ PSL(2, ℤ)`, defined combinatorially as the genus
of its modular coset triple `modularTriple Γ' e`. -/
noncomputable def genus (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) : ℕ :=
  (modularTriple Γ' e).genus

/-- The defining formula for `genus`. -/
theorem genus_def (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    genus Γ' e = (modularTriple Γ' e).genus := (rfl)

/-- The Euler characteristic of `modularTriple Γ' e` is `2 - 2 g`. -/
theorem two_sub_two_mul_genus (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    2 - 2 * (genus Γ' e : ℤ) = (modularTriple Γ' e).eulerChar :=
  (isConnected_modularTriple Γ' e).two_sub_two_mul_genus

/-- Six times the Euler characteristic of `modularTriple Γ' e` equals
`6 c + 3 e₂ + 4 e₃ - n`. -/
theorem six_mul_eulerChar_modularTriple (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    6 * (modularTriple Γ' e).eulerChar =
      6 * (cuspCount Γ' e : ℤ) + 3 * (ellipticTwo Γ' e : ℤ) +
        4 * (ellipticThree Γ' e : ℤ) - n := by
  have h2 : (2 : ℤ) * (orbitCount (permS Γ' e) : ℤ) = (n : ℤ) + ellipticTwo Γ' e := by
    exact_mod_cast two_mul_orbitCount_permS Γ' e
  have h3 : (3 : ℤ) * (orbitCount (modularTriple Γ' e).σ0 : ℤ) =
      (n : ℤ) + 2 * ellipticThree Γ' e := by
    exact_mod_cast three_mul_orbitCount_σ0 Γ' e
  rw [eulerChar_def, ← cuspCount_def]
  change 6 * ((orbitCount (modularTriple Γ' e).σ0 : ℤ) + orbitCount (permS Γ' e) +
      cuspCount Γ' e - n) = _
  linarith

/-- **The integral genus formula** for a finite-index subgroup `Γ' ≤ PSL(2, ℤ)` of index `n`:
`12 g + 3 e₂ + 4 e₃ + 6 c = 12 + n`. -/
theorem genus_formula (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    12 * genus Γ' e + 3 * ellipticTwo Γ' e + 4 * ellipticThree Γ' e + 6 * cuspCount Γ' e =
      12 + n := by
  have hχ := two_sub_two_mul_genus Γ' e
  have h6 := six_mul_eulerChar_modularTriple Γ' e
  zify
  linarith

/-- Equivalent modular triples have the same genus. -/
theorem genus_eq_of_equivalent {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : (modularTriple Γ₁ e₁).Equivalent (modularTriple Γ₂ e₂)) :
    genus Γ₁ e₁ = genus Γ₂ e₂ :=
  PermutationTriple.genus_eq_of_equivalent h

/-- The genus does not depend on the coset enumeration. -/
theorem genus_congr (Γ' : Subgroup PSL(2, ℤ)) (e₁ e₂ : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    genus Γ' e₁ = genus Γ' e₂ :=
  genus_eq_of_equivalent (equivalent_modularTriple Γ' e₁ e₂)

/-- Conjugate subgroups of `PSL(2, ℤ)` have the same genus. -/
theorem genus_eq_of_conj {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : ∃ g : ConjAct PSL(2, ℤ), g • Γ₁ = Γ₂) :
    genus Γ₁ e₁ = genus Γ₂ e₂ :=
  genus_eq_of_equivalent ((millington e₁ e₂).mpr h)

/-- The mirror subgroup `Γ'.map conjJAut` has the same genus as `Γ'`. -/
theorem genus_map_conjJAut (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (e' : PSL(2, ℤ) ⧸ Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ)) ≃ Fin n) :
    genus (Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))) e' = genus Γ' e := by
  rw [genus_def, genus_def,
    PermutationTriple.genus_eq_of_equivalent (equivalent_mirror_modularTriple Γ' e e'),
    genus_mirror]

/-- The full modular group `⊤` has genus `0`. -/
@[simp]
theorem genus_top (e : PSL(2, ℤ) ⧸ (⊤ : Subgroup PSL(2, ℤ)) ≃ Fin 1) :
    genus ⊤ e = 0 :=
  genus_of_degree_one _

/-- For a torsion-free subgroup (`e₂ = e₃ = 0`), the genus formula simplifies to
`12 g + 6 c = 12 + n`. -/
theorem genus_formula_of_elliptic_eq_zero {Γ' : Subgroup PSL(2, ℤ)}
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (h2 : ellipticTwo Γ' e = 0) (h3 : ellipticThree Γ' e = 0) :
    12 * genus Γ' e + 6 * cuspCount Γ' e = 12 + n := by
  have h := genus_formula Γ' e
  omega

/-- Every torsion-free finite-index subgroup of `PSL(2, ℤ)` (`e₂ = e₃ = 0`) has index
divisible by `6`. -/
theorem six_dvd_of_elliptic_eq_zero {Γ' : Subgroup PSL(2, ℤ)} (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (h2 : ellipticTwo Γ' e = 0) (h3 : ellipticThree Γ' e = 0) :
    6 ∣ n := by
  have h := genus_formula_of_elliptic_eq_zero e h2 h3
  omega

/-- A subgroup has genus `0` if and only if `3 e₂ + 4 e₃ + 6 c = 12 + n`. -/
theorem genus_eq_zero_iff (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    genus Γ' e = 0 ↔
      3 * ellipticTwo Γ' e + 4 * ellipticThree Γ' e + 6 * cuspCount Γ' e = 12 + n := by
  have h := genus_formula Γ' e
  omega

/-- Every finite-index subgroup of `PSL(2, ℤ)` with positive genus has index at least `6`. -/
theorem six_le_of_genus_pos {Γ' : Subgroup PSL(2, ℤ)} {e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n}
    (hg : 0 < genus Γ' e) : 6 ≤ n := by
  have h := genus_formula Γ' e
  have hc := cuspCount_pos Γ' e
  omega

/-! ### Packaged invariant vector and opposite (right-coset) convention -/

/-- The classical combinatorial invariant vector `(index, genus, e₂, e₃, cuspWidths)` of a
finite-index subgroup of `PSL(2, ℤ)`. -/
@[ext]
structure Invariants where
  /-- The index `[PSL(2, ℤ) : Γ']`. -/
  index : ℕ
  /-- The genus of `X(Γ')`. -/
  genus : ℕ
  /-- The number of order-`2` elliptic points. -/
  ellipticTwo : ℕ
  /-- The number of order-`3` elliptic points. -/
  ellipticThree : ℕ
  /-- The multiset of cusp widths. -/
  cuspWidths : Multiset ℕ
  deriving DecidableEq

/-- The number of cusps recorded in an `Invariants` vector. -/
def Invariants.cuspCount (I : Invariants) : ℕ := I.cuspWidths.card

/-- The packaged invariant vector of `Γ' ≤ PSL(2, ℤ)` with coset enumeration `e`. -/
noncomputable def invariants (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Invariants where
  index := n
  genus := genus Γ' e
  ellipticTwo := ellipticTwo Γ' e
  ellipticThree := ellipticThree Γ' e
  cuspWidths := cuspWidths Γ' e

/-- The index field of `invariants Γ' e` is `n`. -/
@[simp]
theorem invariants_index (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (invariants Γ' e).index = n := (rfl)

/-- The genus field of `invariants Γ' e` is `genus Γ' e`. -/
@[simp]
theorem invariants_genus (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (invariants Γ' e).genus = genus Γ' e := (rfl)

/-- The order-`2` elliptic count field of `invariants Γ' e` is `ellipticTwo Γ' e`. -/
@[simp]
theorem invariants_ellipticTwo (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (invariants Γ' e).ellipticTwo = ellipticTwo Γ' e := (rfl)

/-- The order-`3` elliptic count field of `invariants Γ' e` is `ellipticThree Γ' e`. -/
@[simp]
theorem invariants_ellipticThree (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (invariants Γ' e).ellipticThree = ellipticThree Γ' e := (rfl)

/-- The cusp-width multiset field of `invariants Γ' e` is `cuspWidths Γ' e`. -/
@[simp]
theorem invariants_cuspWidths (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (invariants Γ' e).cuspWidths = cuspWidths Γ' e := (rfl)

/-- The cusp count of `invariants Γ' e` is `cuspCount Γ' e`. -/
@[simp]
theorem invariants_cuspCount (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (invariants Γ' e).cuspCount = cuspCount Γ' e :=
  (cuspCount_eq_card_cuspWidths Γ' e).symm

/-- Equivalent modular triples have identical invariant vectors. -/
theorem invariants_eq_of_equivalent {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : (modularTriple Γ₁ e₁).Equivalent (modularTriple Γ₂ e₂)) :
    invariants Γ₁ e₁ = invariants Γ₂ e₂ := by
  ext1
  · rfl
  · exact genus_eq_of_equivalent h
  · exact ellipticTwo_eq_of_equivalent h
  · exact ellipticThree_eq_of_equivalent h
  · exact cuspWidths_eq_of_equivalent h

/-- The invariant vector does not depend on the coset enumeration. -/
theorem invariants_congr (Γ' : Subgroup PSL(2, ℤ)) (e₁ e₂ : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    invariants Γ' e₁ = invariants Γ' e₂ :=
  invariants_eq_of_equivalent (equivalent_modularTriple Γ' e₁ e₂)

/-- Conjugate subgroups of `PSL(2, ℤ)` have identical invariant vectors. -/
theorem invariants_eq_of_conj {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : ∃ g : ConjAct PSL(2, ℤ), g • Γ₁ = Γ₂) :
    invariants Γ₁ e₁ = invariants Γ₂ e₂ :=
  invariants_eq_of_equivalent ((millington e₁ e₂).mpr h)

/-- The mirror subgroup `Γ'.map conjJAut` has the same invariant vector as `Γ'`. -/
theorem invariants_map_conjJAut (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (e' : PSL(2, ℤ) ⧸ Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ)) ≃ Fin n) :
    invariants (Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))) e' = invariants Γ' e := by
  ext1
  · rfl
  · exact genus_map_conjJAut Γ' e e'
  · exact ellipticTwo_map_conjJAut Γ' e e'
  · exact ellipticThree_map_conjJAut Γ' e e'
  · exact cuspWidths_map_conjJAut Γ' e e'

/-- The full modular group `⊤` has invariant vector `(1, 0, 1, 1, {1})`. -/
@[simp]
theorem invariants_top (e : PSL(2, ℤ) ⧸ (⊤ : Subgroup PSL(2, ℤ)) ≃ Fin 1) :
    invariants ⊤ e = ⟨1, 0, 1, 1, {1}⟩ := by
  ext1 <;> simp

/-! ### Opposite (right-coset / LMFDB) convention -/

/-- Under the opposite (right-coset) convention `r : Quotient (rightRel Γ') ≃ Fin n`,
`cuspWidths` agrees with the full cycle type of the right-coset permutation of `T`. -/
theorem cuspWidths_quotientRightRel (Γ' : Subgroup PSL(2, ℤ))
    (r : Quotient (QuotientGroup.rightRel Γ') ≃ Fin n) :
    cuspWidths Γ' ((QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ').symm.trans r) =
      (r.permCongr (Γ'.rightCosetPerm (T : PSL(2, ℤ)))).fullCycleType := by
  have h := (modularTriple_quotientRightRel Γ' r).2.2.2.1
  rw [cuspWidths_def, permT, h, fullCycleType_inv]

/-- Under the opposite convention, `cuspCount` equals the orbit count of the right-coset
permutation of `T`. -/
theorem cuspCount_quotientRightRel (Γ' : Subgroup PSL(2, ℤ))
    (r : Quotient (QuotientGroup.rightRel Γ') ≃ Fin n) :
    cuspCount Γ' ((QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ').symm.trans r) =
      orbitCount (r.permCongr (Γ'.rightCosetPerm (T : PSL(2, ℤ)))) := by
  have h := (modularTriple_quotientRightRel Γ' r).2.2.2.1
  rw [cuspCount_def, permT, h, orbitCount_inv]

/-- Under the opposite convention, `ellipticTwo` counts the fixed points of the right-coset
permutation of `S`. -/
theorem ellipticTwo_quotientRightRel (Γ' : Subgroup PSL(2, ℤ))
    (r : Quotient (QuotientGroup.rightRel Γ') ≃ Fin n) :
    ellipticTwo Γ' ((QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ').symm.trans r) =
      Fintype.card {x : Fin n // r.permCongr (Γ'.rightCosetPerm (S : PSL(2, ℤ))) x = x} := by
  have h := (modularTriple_quotientRightRel Γ' r).2.2.1
  rw [ellipticTwo_def, permS, h]

/-- Under the opposite convention, `ellipticThree` counts the fixed points of the right-coset
permutation of `R = S T`. -/
theorem ellipticThree_quotientRightRel (Γ' : Subgroup PSL(2, ℤ))
    (r : Quotient (QuotientGroup.rightRel Γ') ≃ Fin n) :
    ellipticThree Γ' ((QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ').symm.trans r) =
      Fintype.card {x : Fin n // r.permCongr (Γ'.rightCosetPerm (R : PSL(2, ℤ))) x = x} := by
  have h := (modularTriple_quotientRightRel Γ' r).2.2.2.2
  rw [ellipticThree_eq_card_fixed_permR, h, card_subtype_apply_eq, support_inv,
    ← card_subtype_apply_eq]

/-! ### Non-completeness of the invariant vector: an index-7 mirror pair -/

private def chiralS : Perm (Fin 7) :=
  Equiv.swap 1 2 * Equiv.swap 3 4 * Equiv.swap 5 6

private def chiralT : Perm (Fin 7) :=
  Equiv.swap 0 2 * Equiv.swap 2 1 * Equiv.swap 1 4 * Equiv.swap 4 6 * Equiv.swap 6 3

private def chiralTriple : PermutationTriple 7 where
  σ0 := (chiralT * chiralS)⁻¹
  σ1 := chiralS
  σinf := chiralT
  product_eq_one := mul_inv_cancel _

private theorem chiralTriple_isConnected : chiralTriple.IsConnected := by decide

private theorem not_equivalent_chiralTriple_mirror :
    ¬ chiralTriple.Equivalent chiralTriple.mirror := by
  intro heq
  obtain ⟨τ, hτ⟩ := equivalent_iff_exists_smul_eq.mp heq
  have h1 : τ * chiralTriple.σ1 * τ⁻¹ = chiralTriple.σ1 := by
    have hσ1 : (τ • chiralTriple).σ1 = chiralTriple.mirror.σ1 :=
      congrArg PermutationTriple.σ1 hτ
    have hinv : chiralTriple.σ1⁻¹ = chiralTriple.σ1 := by decide
    simpa [hinv] using hσ1
  have hinf : τ * chiralTriple.σinf * τ⁻¹ = chiralTriple.σinf⁻¹ := by
    simpa using congrArg PermutationTriple.σinf hτ
  have hcommS (x : Fin 7) : τ (chiralTriple.σ1 x) = chiralTriple.σ1 (τ x) := by
    have := congrFun (congrArg DFunLike.coe h1) (τ x)
    simpa using this
  have hcommT (x : Fin 7) : τ (chiralTriple.σinf x) = chiralTriple.σinf⁻¹ (τ x) := by
    have := congrFun (congrArg DFunLike.coe hinf) (τ x)
    simpa using this
  have hτ0 : τ 0 = 0 := by
    have hfix : chiralTriple.σ1 (τ 0) = τ 0 := by
      have h0 : chiralTriple.σ1 0 = 0 := by decide
      rw [← hcommS 0, h0]
    have huniq : ∀ x : Fin 7, chiralTriple.σ1 x = x → x = 0 := by decide
    exact huniq (τ 0) hfix
  have hτ2 : τ 2 = 3 := by
    have ht0 : chiralTriple.σinf 0 = 2 := by decide
    have ht0' : chiralTriple.σinf⁻¹ 0 = 3 := by decide
    rw [← ht0, hcommT 0, hτ0, ht0']
  have hτ1 : τ 1 = 6 := by
    have ht2 : chiralTriple.σinf 2 = 1 := by decide
    have ht3' : chiralTriple.σinf⁻¹ 3 = 6 := by decide
    rw [← ht2, hcommT 2, hτ2, ht3']
  have hs1 : chiralTriple.σ1 1 = 2 := by decide
  have hs6 : chiralTriple.σ1 6 = 5 := by decide
  have hcontra : (3 : Fin 7) = 5 := by
    calc (3 : Fin 7) = τ 2 := hτ2.symm
      _ = τ (chiralTriple.σ1 1) := by rw [hs1]
      _ = chiralTriple.σ1 (τ 1) := hcommS 1
      _ = 5 := by rw [hτ1, hs6]
  exact absurd hcontra (by decide)

/-- **Non-completeness of the classical invariant vector.** There exist two non-conjugate
index-`7` subgroups of `PSL(2, ℤ)` — a chiral subgroup and its mirror under `conjJAut` —
sharing the same invariant vector `(7, 0, 1, 1, {6, 1})`. -/
theorem exists_not_conj_invariants_eq :
    ∃ (Γ₁ Γ₂ : Subgroup PSL(2, ℤ)) (e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin 7)
      (e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin 7),
      invariants Γ₁ e₁ = ⟨7, 0, 1, 1, {6, 1}⟩ ∧
      invariants Γ₂ e₂ = ⟨7, 0, 1, 1, {6, 1}⟩ ∧
      ¬ ∃ g : ConjAct PSL(2, ℤ), g • Γ₁ = Γ₂ := by
  have h0 : chiralTriple.σ0 ^ 3 = 1 := by decide
  have h1 : chiralTriple.σ1 ^ 2 = 1 := by decide
  obtain ⟨Γ₁, _, e₁, -, heq₁⟩ :=
    exists_modularTriple_equivalent chiralTriple_isConnected h0 h1
  let Γ₂ : Subgroup PSL(2, ℤ) := Γ₁.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))
  let e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin 7 :=
    (TauCeti.QuotientGroup.congrOfMapEq conjJAut (rfl : Γ₁.map _ = Γ₂)).symm.trans e₁
  have hinv₁ : invariants Γ₁ e₁ = ⟨7, 0, 1, 1, {6, 1}⟩ := by
    have hg : genus Γ₁ e₁ = 0 := by
      rw [genus_def, PermutationTriple.genus_eq_of_equivalent heq₁, ← computedGenus_eq]
      decide
    have he2 : ellipticTwo Γ₁ e₁ = 1 := by
      rw [ellipticTwo_eq_count_one_fullCycleType, fullCycleType_def, ← cycleData_σ1,
        cycleData_eq_of_equivalent heq₁, cycleData_σ1, ← fullCycleType_def,
        ← computedCycleType_eq_fullCycleType]
      decide
    have he3 : ellipticThree Γ₁ e₁ = 1 := by
      rw [ellipticThree_eq_count_one_fullCycleType, fullCycleType_def, ← cycleData_σ0,
        cycleData_eq_of_equivalent heq₁, cycleData_σ0, ← fullCycleType_def,
        ← computedCycleType_eq_fullCycleType]
      decide
    have hcw : cuspWidths Γ₁ e₁ = {6, 1} := by
      rw [cuspWidths_eq_cycleData, cycleData_eq_of_equivalent heq₁, cycleData_σinf,
        ← fullCycleType_def, ← computedCycleType_eq_fullCycleType]
      decide
    ext1 <;> simp [hg, he2, he3, hcw]
  have hinv₂ : invariants Γ₂ e₂ = ⟨7, 0, 1, 1, {6, 1}⟩ := by
    rw [invariants_map_conjJAut Γ₁ e₁ e₂, hinv₁]
  refine ⟨Γ₁, Γ₂, e₁, e₂, hinv₁, hinv₂, fun hconj ↦ ?_⟩
  have h12 : (modularTriple Γ₁ e₁).Equivalent (modularTriple Γ₂ e₂) :=
    (millington e₁ e₂).mpr hconj
  have h2m : (modularTriple Γ₂ e₂).Equivalent (modularTriple Γ₁ e₁).mirror :=
    equivalent_mirror_modularTriple Γ₁ e₁ e₂
  have hm : chiralTriple.Equivalent chiralTriple.mirror := by
    rw [← IsoClass.mk_eq_mk_iff]
    calc IsoClass.mk chiralTriple
        = IsoClass.mk (modularTriple Γ₁ e₁) := (IsoClass.mk_eq_mk_iff.mpr heq₁).symm
      _ = IsoClass.mk (modularTriple Γ₂ e₂) := IsoClass.mk_eq_mk_iff.mpr h12
      _ = IsoClass.mk (modularTriple Γ₁ e₁).mirror := IsoClass.mk_eq_mk_iff.mpr h2m
      _ = IsoClass.mk chiralTriple.mirror := IsoClass.mk_eq_mk_iff.mpr heq₁.mirror
  exact not_equivalent_chiralTriple_mirror hm

end TauCeti.ModularGroup
