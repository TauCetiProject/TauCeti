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
public import TauCeti.NumberTheory.Modular.Invariants
import TauCeti.Combinatorics.PermutationTriple.ComputedInvariants
import TauCeti.Combinatorics.PermutationTriple.Decidable
import TauCeti.Combinatorics.PermutationTriple.Mirror

/-!
# Combinatorial invariants of the modular coset triple

Building on `TauCeti.NumberTheory.Modular.Invariants` (which defines `cuspWidths`, `cuspCount`,
`ellipticTwo`, `ellipticThree`, and proves the basic invariance and `genus_formula`), every
finite-index subgroup `Γ' ≤ PSL(2, ℤ)` with left-coset enumeration
`e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n` determines `modularTriple Γ' e = (σ0, σ1, σinf)`
(`permS = σ1`, `permT = σinf`, `σ0 = ρ U`), yielding the further combinatorial invariants of
`X(Γ')`:

* **Cusps (`cuspCycleWidth`, `permTCycleEquivDoubleCoset`)**: double-coset bijection onto
  `Γ' \ PSL(2, ℤ) / ⟨T⟩`, subgroup-inclusion divisibility, and fiber-sum formulas
  (`minimalPeriod_permT_dvd_of_le`, `sum_cuspCycleWidth_fiber_of_le`,
  `sum_widthRatio_permT_fiber_of_le`).
* **Elliptic points and `conjJAut` mirror invariance**: characterizations of fixed points of
  `permS`, `σ0`, and `permR`, and invariance of all invariants under the mirror `conjJAut`.
* **Genus (`genus`)**: `(modularTriple Γ' e).genus`, invariance under `conjJAut`, and torsion-free
  consequences.
* **Invariant vector (`Invariants`, `invariants`)**: invariant under triple equivalence,
  conjugacy, `conjJAut`, and the opposite right-coset convention, with an index-`7` chiral mirror
  pair proving non-completeness (`exists_not_conj_invariants_eq`).

## References

* M. H. Millington, *Subgroups of the classical modular group*, J. London Math. Soc. (2) 1 (1969),
  351–357.
* C. Kurth, L. Long, *Computations with finite index subgroups of `PSL₂(ℤ)` using Farey symbols*,
  in *Advances in Algebra and Combinatorics*, World Scientific (2008), 225–242, arXiv:0710.1835.
* F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228, Springer, 2005, §3.1.
-/

open Equiv Equiv.Perm Matrix
open scoped MatrixGroups Pointwise

public section

namespace TauCeti.ModularGroup

open _root_.ModularGroup PermutationTriple

variable {m n : ℕ}

/-! ### Additional cusp-width and cusp-count properties -/

/-- `cuspWidths Γ' e` is the `∞`-component of the cycle data of `modularTriple Γ' e`. -/
theorem cuspWidths_eq_cycleData (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspWidths Γ' e = (modularTriple Γ' e).cycleData.2.2 := by
  rw [cuspWidths_def, cycleData_σinf, fullCycleType_def, permT]

/-- Conjugate subgroups of `PSL(2, ℤ)` have the same multiset of cusp widths. -/
theorem cuspWidths_eq_of_conj {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : ∃ g : ConjAct PSL(2, ℤ), g • Γ₁ = Γ₂) :
    cuspWidths Γ₁ e₁ = cuspWidths Γ₂ e₂ := by
  rcases h with ⟨g, rfl⟩
  exact (cuspWidths_conjAct_smul Γ₁ e₁ g e₂).symm

/-- The mirror subgroup `Γ'.map conjJAut` has the same multiset of cusp widths as `Γ'`. -/
theorem cuspWidths_map_conjJAut (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (e' : PSL(2, ℤ) ⧸ Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ)) ≃ Fin n) :
    cuspWidths (Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))) e' = cuspWidths Γ' e := by
  rw [cuspWidths_eq_cycleData, cuspWidths_eq_cycleData,
    cycleData_eq_of_equivalent (equivalent_mirror_modularTriple Γ' e e'), cycleData_mirror]

/-- Every finite-index subgroup of `PSL(2, ℤ)` has at least one cusp. -/
theorem cuspCount_pos (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    0 < cuspCount Γ' e := by
  have : Nonempty (Fin n) := ⟨e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')⟩
  rw [cuspCount_def]
  exact (permT Γ' e).orbitCount_pos

/-- An index-`n` subgroup of `PSL(2, ℤ)` has at most `n` cusps. -/
theorem cuspCount_le (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspCount Γ' e ≤ n := by simpa [cuspCount_def] using (permT Γ' e).orbitCount_le_card

/-- Conjugate subgroups of `PSL(2, ℤ)` have the same cusp count. -/
theorem cuspCount_eq_of_conj {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : ∃ g : ConjAct PSL(2, ℤ), g • Γ₁ = Γ₂) :
    cuspCount Γ₁ e₁ = cuspCount Γ₂ e₂ := by
  rcases h with ⟨g, rfl⟩
  exact (cuspCount_conjAct_smul Γ₁ e₁ g e₂).symm

/-- The mirror subgroup `Γ'.map conjJAut` has the same cusp count as `Γ'`. -/
theorem cuspCount_map_conjJAut (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (e' : PSL(2, ℤ) ⧸ Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ)) ≃ Fin n) :
    cuspCount (Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))) e' = cuspCount Γ' e := by
  rw [← card_cuspWidths, ← card_cuspWidths, cuspWidths_map_conjJAut]

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

/-- The period of `permT Γ' e` at `e (g Γ')` divides `h` iff `g⁻¹ T ^ h g ∈ Γ'`. -/
theorem minimalPeriod_permT_dvd_iff (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (g : PSL(2, ℤ)) (h : ℕ) :
    Function.minimalPeriod (permT Γ' e) (e (g : PSL(2, ℤ) ⧸ Γ')) ∣ h ↔
      g⁻¹ * (T : PSL(2, ℤ)) ^ h * g ∈ Γ' := by
  rw [← Function.isPeriodicPt_iff_minimalPeriod_dvd, Function.IsPeriodicPt, Function.IsFixedPt,
    ← Equiv.Perm.coe_pow, permT_pow_apply, e.apply_eq_iff_eq, QuotientGroup.eq,
    show ((T : PSL(2, ℤ)) ^ h * g)⁻¹ * g = (g⁻¹ * (T : PSL(2, ℤ)) ^ h * g)⁻¹ by group,
    Subgroup.inv_mem_iff]

/-- Lifted to `SL(2, ℤ)`, the period of `permT Γ' e` at `e (σ Γ')` divides `h` iff
`σ⁻¹ T ^ h σ ∈ Γ'.liftSL`. -/
theorem minimalPeriod_permT_mk_dvd_iff (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (σ : SL(2, ℤ)) (h : ℕ) :
    Function.minimalPeriod (permT Γ' e) (e ((σ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) ∣ h ↔
      σ⁻¹ * _root_.ModularGroup.T ^ h * σ ∈ Γ'.liftSL := by
  rw [minimalPeriod_permT_dvd_iff, Subgroup.mem_liftSL, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]

/-- Every point has positive minimal period under `permT Γ' e`. -/
theorem minimalPeriod_permT_pos (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (x : Fin n) : 0 < Function.minimalPeriod (permT Γ' e) x :=
  Function.minimalPeriod_pos_of_mem_periodicPts ⟨orderOf (permT Γ' e), orderOf_pos _, by
    simp [Function.IsPeriodicPt, Function.IsFixedPt, ← Equiv.Perm.coe_pow]⟩

/-- The period of `permT Γ' e` at `e (g Γ')` is the least positive `h` with `g⁻¹ T ^ h g ∈ Γ'`. -/
theorem minimalPeriod_permT_eq_sInf (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (g : PSL(2, ℤ)) :
    Function.minimalPeriod (permT Γ' e) (e (g : PSL(2, ℤ) ⧸ Γ')) =
      sInf {h : ℕ | 0 < h ∧ g⁻¹ * (T : PSL(2, ℤ)) ^ h * g ∈ Γ'} := by
  have hmem : Function.minimalPeriod (permT Γ' e) (e (g : PSL(2, ℤ) ⧸ Γ')) ∈
      {h : ℕ | 0 < h ∧ g⁻¹ * (T : PSL(2, ℤ)) ^ h * g ∈ Γ'} :=
    ⟨minimalPeriod_permT_pos Γ' e _, (minimalPeriod_permT_dvd_iff Γ' e g _).mp dvd_rfl⟩
  exact le_antisymm
    (le_csInf ⟨_, hmem⟩ fun h ⟨hh, hmem'⟩ ↦
      Nat.le_of_dvd hh ((minimalPeriod_permT_dvd_iff Γ' e g h).mpr hmem'))
    (Nat.sInf_le hmem)

/-- For `σ : SL(2, ℤ)`, the period of `permT Γ' e` at `e (σ⁻¹ Γ')` (for the cusp `σ • ∞`) is the
least positive `h` with `σ T ^ h σ⁻¹ ∈ Γ'.liftSL`. -/
theorem minimalPeriod_permT_mk_inv_eq_sInf (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (σ : SL(2, ℤ)) :
    Function.minimalPeriod (permT Γ' e)
        (e (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) =
      sInf {h : ℕ | 0 < h ∧ σ * _root_.ModularGroup.T ^ h * σ⁻¹ ∈ Γ'.liftSL} := by
  rw [minimalPeriod_permT_eq_sInf]; congr 1; ext h
  simp [Subgroup.mem_liftSL, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]

/-- At the base coset `e 1` (the cusp `∞`), the period of `permT Γ' e` is the least positive `h`
with `T ^ h ∈ Γ'.liftSL`. -/
theorem minimalPeriod_permT_one (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Function.minimalPeriod (permT Γ' e) (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) =
      sInf {h : ℕ | 0 < h ∧ _root_.ModularGroup.T ^ h ∈ Γ'.liftSL} := by
  simpa using minimalPeriod_permT_mk_inv_eq_sInf Γ' e 1

/-- Two cosets `e (g₁ Γ')` and `e (g₂ Γ')` lie in the same cycle of `permT Γ' e` iff `g₁⁻¹` and
`g₂⁻¹` lie in the same double coset in `Γ' \ PSL(2, ℤ) / ⟨T⟩`. -/
theorem sameCycle_permT_iff_doubleCoset (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (g₁ g₂ : PSL(2, ℤ)) :
    (permT Γ' e).SameCycle (e (g₁ : PSL(2, ℤ) ⧸ Γ')) (e (g₂ : PSL(2, ℤ) ⧸ Γ')) ↔
      DoubleCoset.mk Γ' (Subgroup.zpowers (T : PSL(2, ℤ))) g₁⁻¹ =
        DoubleCoset.mk Γ' (Subgroup.zpowers (T : PSL(2, ℤ))) g₂⁻¹ := by
  rw [DoubleCoset.eq]
  constructor
  · rintro ⟨k, hk⟩
    rw [permT_zpow_apply, e.apply_eq_iff_eq, QuotientGroup.eq] at hk
    exact ⟨(((T : PSL(2, ℤ)) ^ k * g₁)⁻¹ * g₂)⁻¹, Γ'.inv_mem hk,
      (T : PSL(2, ℤ)) ^ (-k), Subgroup.zpow_mem_zpowers _ _, by rw [_root_.zpow_neg]; group⟩
  · rintro ⟨γ, hγ, t, ht, h⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    refine ⟨-k, ?_⟩
    rw [permT_zpow_apply, e.apply_eq_iff_eq, QuotientGroup.eq]
    have hinv : ((T : PSL(2, ℤ)) ^ (-k) * g₁)⁻¹ * g₂ = γ⁻¹ := by
      have := congrArg Inv.inv h
      simp only [_root_.mul_inv_rev, inv_inv] at this
      rw [this, _root_.zpow_neg]; group
    exact hinv ▸ Γ'.inv_mem hγ

private def doubleCosetOfCoset (Γ' : Subgroup PSL(2, ℤ)) :
    PSL(2, ℤ) ⧸ Γ' →
      DoubleCoset.Quotient (Γ' : Set PSL(2, ℤ)) (Subgroup.zpowers (T : PSL(2, ℤ))) :=
  Quotient.lift (fun g ↦ DoubleCoset.mk Γ' (Subgroup.zpowers (T : PSL(2, ℤ))) g⁻¹) fun g₁ g₂ h ↦
    DoubleCoset.eq.mpr
      ⟨(g₁⁻¹ * g₂)⁻¹, Γ'.inv_mem (QuotientGroup.leftRel_apply.mp h), 1, Subgroup.one_mem _, by
        group⟩

private theorem doubleCosetOfCoset_mk (Γ' : Subgroup PSL(2, ℤ)) (g : PSL(2, ℤ)) :
    doubleCosetOfCoset Γ' (g : PSL(2, ℤ) ⧸ Γ') =
      DoubleCoset.mk Γ' (Subgroup.zpowers (T : PSL(2, ℤ))) g⁻¹ := rfl

private noncomputable def permTDoubleCosetMap (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Quotient (SameCycle.setoid (permT Γ' e)) →
      DoubleCoset.Quotient (Γ' : Set PSL(2, ℤ)) (Subgroup.zpowers (T : PSL(2, ℤ))) :=
  Quotient.lift (fun x ↦ doubleCosetOfCoset Γ' (e.symm x)) fun x y h ↦ by
    obtain ⟨qx, rfl⟩ := e.surjective x; obtain ⟨qy, rfl⟩ := e.surjective y
    induction qx using QuotientGroup.induction_on with | H g₁ =>
    induction qy using QuotientGroup.induction_on with | H g₂ =>
    rw [e.symm_apply_apply, e.symm_apply_apply, doubleCosetOfCoset_mk, doubleCosetOfCoset_mk,
      ← sameCycle_permT_iff_doubleCoset]
    exact h

private theorem permTDoubleCosetMap_bijective (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) : Function.Bijective (permTDoubleCosetMap Γ' e) := by
  refine ⟨fun q₁ q₂ hq ↦ ?_, fun d ↦ ?_⟩
  · induction q₁ using Quotient.ind with | _ x =>
    induction q₂ using Quotient.ind with | _ y =>
    obtain ⟨qx, rfl⟩ := e.surjective x; obtain ⟨qy, rfl⟩ := e.surjective y
    induction qx using QuotientGroup.induction_on with | H g₁ =>
    induction qy using QuotientGroup.induction_on with | H g₂ =>
    rw [permTDoubleCosetMap, Quotient.lift_mk, Quotient.lift_mk, e.symm_apply_apply,
      e.symm_apply_apply, doubleCosetOfCoset_mk, doubleCosetOfCoset_mk,
      ← sameCycle_permT_iff_doubleCoset] at hq
    exact Quotient.sound hq
  · induction d using Quotient.ind' with | _ g =>
    refine ⟨Quotient.mk _ (e ((g⁻¹ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')), ?_⟩
    rw [permTDoubleCosetMap, Quotient.lift_mk, e.symm_apply_apply, doubleCosetOfCoset_mk, inv_inv]

/-- **Double-coset bijection for cusps.** The cycles of `permT Γ' e` are in canonical bijection
with the double cosets `Γ' \ PSL(2, ℤ) / ⟨T⟩`, sending the cycle of `e (g Γ')` to
`Γ' g⁻¹ ⟨T⟩`. -/
noncomputable def permTCycleEquivDoubleCoset (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Quotient (SameCycle.setoid (permT Γ' e)) ≃
      DoubleCoset.Quotient (Γ' : Set PSL(2, ℤ)) (Subgroup.zpowers (T : PSL(2, ℤ))) :=
  Equiv.ofBijective (permTDoubleCosetMap Γ' e) (permTDoubleCosetMap_bijective Γ' e)

/-- `permTCycleEquivDoubleCoset` sends the cycle of `e (g Γ')` to `Γ' g⁻¹ ⟨T⟩`. -/
@[simp] theorem permTCycleEquivDoubleCoset_mk (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (g : PSL(2, ℤ)) :
    permTCycleEquivDoubleCoset Γ' e (Quotient.mk _ (e (g : PSL(2, ℤ) ⧸ Γ'))) =
      DoubleCoset.mk Γ' (Subgroup.zpowers (T : PSL(2, ℤ))) g⁻¹ := by
  rw [permTCycleEquivDoubleCoset, Equiv.ofBijective_apply, permTDoubleCosetMap, Quotient.lift_mk,
    e.symm_apply_apply, doubleCosetOfCoset_mk]

/-- The cusp count equals the number of double cosets `Γ' \ PSL(2, ℤ) / ⟨T⟩`. -/
theorem cuspCount_eq_card_doubleCoset (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
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

/-- The canonical map on `permT`-cycles induced by `Γ'' ≤ Γ'`, sending the cycle of `e'' (g Γ'')`
to the cycle of `e' (g Γ')`. -/
noncomputable def cuspCycleMapOfLE {Γ'' Γ' : Subgroup PSL(2, ℤ)} (h : Γ'' ≤ Γ')
    (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m) (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Quotient (SameCycle.setoid (permT Γ'' e'')) → Quotient (SameCycle.setoid (permT Γ' e')) :=
  Quotient.map (fun y ↦ e' (Subgroup.quotientEquivProdOfLE h (e''.symm y)).1)
    fun y₁ y₂ ⟨k, hk⟩ ↦ by
      subst hk; obtain ⟨q₁, rfl⟩ := e''.surjective y₁
      induction q₁ using QuotientGroup.induction_on with | H g =>
      exact ⟨k, by rw [permT_zpow_apply, e''.symm_apply_apply, e''.symm_apply_apply]; exact
        permT_zpow_apply Γ' e' g k⟩

/-- `cuspCycleMapOfLE` sends the cycle of `e'' (g Γ'')` to the cycle of `e' (g Γ')`. -/
@[simp] theorem cuspCycleMapOfLE_mk {Γ'' Γ' : Subgroup PSL(2, ℤ)} (h : Γ'' ≤ Γ')
    (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m) (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (g : PSL(2, ℤ)) :
    cuspCycleMapOfLE h e'' e' (Quotient.mk _ (e'' (g : PSL(2, ℤ) ⧸ Γ''))) =
      Quotient.mk _ (e' (g : PSL(2, ℤ) ⧸ Γ')) := by
  rw [cuspCycleMapOfLE, Quotient.map_mk, e''.symm_apply_apply,
    Subgroup.quotientEquivProdOfLE_apply, Quotient.map'_mk'', id_eq]

/-- The width of a `permT`-cycle, well-defined on `Quotient (SameCycle.setoid (permT Γ' e))`. -/
noncomputable def cuspCycleWidth (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Quotient (SameCycle.setoid (permT Γ' e)) → ℕ :=
  Quotient.lift (Function.minimalPeriod (permT Γ' e)) fun _ _ h ↦ h.minimalPeriod_eq

/-- On the cycle of `x`, `cuspCycleWidth` is `Function.minimalPeriod (permT Γ' e) x`. -/
@[simp] theorem cuspCycleWidth_mk (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (x : Fin n) :
    cuspCycleWidth Γ' e (Quotient.mk _ x) = Function.minimalPeriod (permT Γ' e) x := (rfl)

/-- `cuspWidths Γ' e` is the multiset of `cuspCycleWidth Γ' e` over all `permT`-cycles. -/
theorem cuspWidths_eq_map_cuspCycleWidth (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    [Fintype (Quotient (SameCycle.setoid (permT Γ' e)))] :
    cuspWidths Γ' e = Finset.univ.val.map (cuspCycleWidth Γ' e) := by
  rw [cuspWidths_def]
  exact fullCycleType_eq_map_univ (permT Γ' e) (Equiv.refl _) fun _ ↦ rfl

/-- The period of `permT Γ' e` at any point `x` belongs to `cuspWidths Γ' e`. -/
theorem minimalPeriod_permT_mem_cuspWidths (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (x : Fin n) :
    Function.minimalPeriod (permT Γ' e) x ∈ cuspWidths Γ' e := by
  classical
  have := Fintype.ofFinite (Quotient (SameCycle.setoid (permT Γ' e)))
  rw [cuspWidths_eq_map_cuspCycleWidth]
  exact Multiset.mem_map.mpr ⟨Quotient.mk _ x, Finset.mem_univ _, rfl⟩

/-- For `Γ'' ≤ Γ'`, the width of the image cusp divides the width of each cusp above it. -/
theorem cuspCycleWidth_map_dvd {Γ'' Γ' : Subgroup PSL(2, ℤ)} (h : Γ'' ≤ Γ')
    (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m) (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (q : Quotient (SameCycle.setoid (permT Γ'' e''))) :
    cuspCycleWidth Γ' e' (cuspCycleMapOfLE h e'' e' q) ∣ cuspCycleWidth Γ'' e'' q := by
  induction q using Quotient.ind with | _ y =>
  obtain ⟨qy, rfl⟩ := e''.surjective y
  induction qy using QuotientGroup.induction_on with | H g =>
  rw [cuspCycleMapOfLE_mk, cuspCycleWidth_mk, cuspCycleWidth_mk]
  exact minimalPeriod_permT_dvd_of_le h e'' e' g

private theorem card_filter_cuspCycle_eq (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    [DecidableEq (Quotient (SameCycle.setoid (permT Γ' e)))]
    (q : Quotient (SameCycle.setoid (permT Γ' e))) :
    (Finset.univ.filter (fun y : Fin n ↦
        Quotient.mk (SameCycle.setoid (permT Γ' e)) y = q)).card = cuspCycleWidth Γ' e q := by
  induction q using Quotient.ind with | _ x =>
  rw [cuspCycleWidth_mk, ← Equiv.Perm.ncard_setOf_sameCycle, ← Set.ncard_coe_finset]
  congr 1; ext y
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
  have hSfin : ({q | cuspCycleMapOfLE h e'' e' q = c} : Set _).Finite := Set.toFinite _
  have hsum :
      ∑ᶠ q ∈ {q | cuspCycleMapOfLE h e'' e' q = c}, cuspCycleWidth Γ'' e'' q =
        (Finset.univ.filter (fun y : Fin m ↦
          Quotient.mk (SameCycle.setoid (permT Γ' e')) (proj y) = c)).card := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hSfin,
      show hSfin.toFinset = Finset.univ.filter (fun q ↦ cuspCycleMapOfLE h e'' e' q = c) by
        ext; simp,
      Finset.card_eq_sum_ones, ← Finset.sum_fiberwise_of_maps_to
        (g := Quotient.mk (SameCycle.setoid (permT Γ'' e'')))
        (t := Finset.univ.filter (fun q ↦ cuspCycleMapOfLE h e'' e' q = c))
        (fun y hy ↦ by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢; exact hy)]
    refine Finset.sum_congr rfl fun q hq ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    rw [← Finset.card_eq_sum_ones, ← card_filter_cuspCycle_eq Γ'' e'' q]
    congr 1; ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hy ↦ ⟨by rw [← hq, ← hy, cuspCycleMapOfLE, Quotient.map_mk], hy⟩, And.right⟩
  let eqv : {y : Fin m // Quotient.mk (SameCycle.setoid (permT Γ' e')) (proj y) = c} ≃
      {x : Fin n // Quotient.mk (SameCycle.setoid (permT Γ' e')) x = c} ×
        (Γ' ⧸ Γ''.subgroupOf Γ') :=
    { toFun := fun ⟨y, hy⟩ ↦ ⟨⟨proj y, hy⟩, (Subgroup.quotientEquivProdOfLE h (e''.symm y)).2⟩
      invFun := fun ⟨⟨x, hx⟩, r⟩ ↦
        ⟨e'' ((Subgroup.quotientEquivProdOfLE h).symm (e'.symm x, r)), by
          dsimp only [proj]; rw [e''.symm_apply_apply, Equiv.apply_symm_apply, e'.apply_symm_apply]
          exact hx⟩
      left_inv := fun ⟨y, _⟩ ↦ Subtype.ext <| by
        dsimp only [proj]
        rw [e'.symm_apply_apply, Prod.mk.eta, Equiv.symm_apply_apply, e''.apply_symm_apply]
      right_inv := fun ⟨⟨x, _⟩, r⟩ ↦ Prod.ext
        (Subtype.ext <| by
          dsimp only [proj]; rw [e''.symm_apply_apply, Equiv.apply_symm_apply, e'.apply_symm_apply])
        (by dsimp only; rw [e''.symm_apply_apply, Equiv.apply_symm_apply]) }
  have : Finite (PSL(2, ℤ) ⧸ Γ'') := .of_equiv _ e''.symm
  have : Finite ((PSL(2, ℤ) ⧸ Γ') × (Γ' ⧸ Γ''.subgroupOf Γ')) :=
    .of_equiv _ (Subgroup.quotientEquivProdOfLE h)
  have : Nonempty (PSL(2, ℤ) ⧸ Γ') := ⟨(1 : PSL(2, ℤ))⟩
  have : Finite (Γ' ⧸ Γ''.subgroupOf Γ') :=
    .of_surjective (Prod.snd : (PSL(2, ℤ) ⧸ Γ') × _ → _) Prod.snd_surjective
  have := Fintype.ofFinite (Γ' ⧸ Γ''.subgroupOf Γ')
  rw [hsum, ← Fintype.card_subtype, Fintype.card_congr eqv, Fintype.card_prod, mul_comm,
    ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, Fintype.card_subtype,
    card_filter_cuspCycle_eq Γ' e' c]; rfl

/-- **Sum of width ratios (ramification indices) over a cusp.** For `Γ'' ≤ Γ'`, the cusp width
ratios `width(c'') / width(c)` over all cusps `c''` of `Γ''` lying above `c` sum to
`[Γ' : Γ'']`. -/
theorem sum_widthRatio_permT_fiber_of_le {Γ'' Γ' : Subgroup PSL(2, ℤ)} (h : Γ'' ≤ Γ')
    (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m) (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (c : Quotient (SameCycle.setoid (permT Γ' e'))) :
    ∑ᶠ q ∈ {q | cuspCycleMapOfLE h e'' e' q = c},
        (cuspCycleWidth Γ'' e'' q / cuspCycleWidth Γ' e' c) = Γ''.relIndex Γ' := by
  classical
  have hpos : 0 < cuspCycleWidth Γ' e' c := by
    induction c using Quotient.ind with | _ x => exact minimalPeriod_permT_pos Γ' e' x
  have hSfin : ({q | cuspCycleMapOfLE h e'' e' q = c} : Set _).Finite := Set.toFinite _
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [← sum_cuspCycleWidth_fiber_of_le h e'' e' c, finsum_mem_eq_finite_toFinset_sum _ hSfin,
    finsum_mem_eq_finite_toFinset_sum _ hSfin, Finset.sum_mul]
  exact Finset.sum_congr rfl fun q hq ↦
    Nat.div_mul_cancel ((hSfin.mem_toFinset.mp hq) ▸ cuspCycleWidth_map_dvd h e'' e' q)

/-! ### Additional elliptic-point properties -/

/-- `ellipticThree Γ' e` equally counts the fixed points of `permR Γ' e`, since `permR` is
conjugate to `σ0⁻¹`. -/
theorem ellipticThree_eq_card_fixed_permR (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ellipticThree Γ' e = Fintype.card {x : Fin n // permR Γ' e x = x} := by
  have hconj : permR Γ' e = (permS Γ' e)⁻¹ * (modularTriple Γ' e).σ0⁻¹ * ((permS Γ' e)⁻¹)⁻¹ := by
    simpa only [inv_inv] using permR_eq_permS_inv_mul_σ0_inv_mul_permS Γ' e
  rw [ellipticThree_eq_count_fullCycleType, card_subtype_apply_eq, ← count_one_fullCycleType,
    hconj, fullCycleType_conj, fullCycleType_inv]

private theorem permRep_apply_eq_self_iff (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (a g : PSL(2, ℤ)) :
    e.permutationRepresentation a (e (g : PSL(2, ℤ) ⧸ Γ')) = e (g : PSL(2, ℤ) ⧸ Γ') ↔
      g⁻¹ * a * g ∈ Γ' := by
  rw [Equiv.permutationRepresentation_apply, Equiv.symm_apply_apply, MulAction.Quotient.smul_mk,
    smul_eq_mul, e.apply_eq_iff_eq, QuotientGroup.eq,
    show (a * g)⁻¹ * g = (g⁻¹ * a * g)⁻¹ by group, Subgroup.inv_mem_iff]

/-- `permS Γ' e` fixes `e (g Γ')` if and only if `g⁻¹ S g ∈ Γ'`. -/
theorem permS_apply_eq_self_iff (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (g : PSL(2, ℤ)) :
    permS Γ' e (e (g : PSL(2, ℤ) ⧸ Γ')) = e (g : PSL(2, ℤ) ⧸ Γ') ↔
      g⁻¹ * (S : PSL(2, ℤ)) * g ∈ Γ' := by
  rw [permS, modularTriple_σ1]; exact permRep_apply_eq_self_iff Γ' e S g

/-- `(modularTriple Γ' e).σ0` fixes `e (g Γ')` if and only if `g⁻¹ U g ∈ Γ'`. -/
theorem modularTriple_σ0_apply_eq_self_iff (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (g : PSL(2, ℤ)) :
    (modularTriple Γ' e).σ0 (e (g : PSL(2, ℤ) ⧸ Γ')) = e (g : PSL(2, ℤ) ⧸ Γ') ↔
      g⁻¹ * (U : PSL(2, ℤ)) * g ∈ Γ' := by
  rw [modularTriple_σ0]; exact permRep_apply_eq_self_iff Γ' e U g

/-- `permR Γ' e` fixes `e (g Γ')` if and only if `g⁻¹ R g ∈ Γ'`. -/
theorem permR_apply_eq_self_iff (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (g : PSL(2, ℤ)) :
    permR Γ' e (e (g : PSL(2, ℤ) ⧸ Γ')) = e (g : PSL(2, ℤ) ⧸ Γ') ↔
      g⁻¹ * (R : PSL(2, ℤ)) * g ∈ Γ' := by
  rw [permR_eq_permS_mul_permT, permS, permT, modularTriple_σ1, modularTriple_σinf, ← map_mul,
    ← QuotientGroup.mk_mul, ← R_def]
  exact permRep_apply_eq_self_iff Γ' e R g

/-- `ellipticTwo Γ' e ≤ n`. -/
theorem ellipticTwo_le (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ellipticTwo Γ' e ≤ n := by
  simpa [ellipticTwo_def, ← Fintype.card_subtype] using
    Fintype.card_subtype_le (fun x : Fin n ↦ permS Γ' e x = x)

/-- `ellipticThree Γ' e ≤ n`. -/
theorem ellipticThree_le (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    ellipticThree Γ' e ≤ n := by
  simpa [ellipticThree_def, ← Fintype.card_subtype] using
    Fintype.card_subtype_le (fun x : Fin n ↦ (modularTriple Γ' e).σ0 x = x)

/-- Conjugate subgroups of `PSL(2, ℤ)` have the same number of order-`2` elliptic points. -/
theorem ellipticTwo_eq_of_conj {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : ∃ g : ConjAct PSL(2, ℤ), g • Γ₁ = Γ₂) :
    ellipticTwo Γ₁ e₁ = ellipticTwo Γ₂ e₂ := by
  rcases h with ⟨g, rfl⟩
  exact (ellipticTwo_conjAct_smul Γ₁ e₁ g e₂).symm

/-- The mirror subgroup `Γ'.map conjJAut` has the same number of order-`2` elliptic points. -/
theorem ellipticTwo_map_conjJAut (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (e' : PSL(2, ℤ) ⧸ Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ)) ≃ Fin n) :
    ellipticTwo (Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))) e' = ellipticTwo Γ' e := by
  rw [ellipticTwo_eq_count_fullCycleType, ellipticTwo_eq_count_fullCycleType,
    fullCycleType_def, fullCycleType_def, ← cycleData_σ1, ← cycleData_σ1,
    cycleData_eq_of_equivalent (equivalent_mirror_modularTriple Γ' e e'), cycleData_mirror]

/-- Conjugate subgroups of `PSL(2, ℤ)` have the same number of order-`3` elliptic points. -/
theorem ellipticThree_eq_of_conj {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : ∃ g : ConjAct PSL(2, ℤ), g • Γ₁ = Γ₂) :
    ellipticThree Γ₁ e₁ = ellipticThree Γ₂ e₂ := by
  rcases h with ⟨g, rfl⟩
  exact (ellipticThree_conjAct_smul Γ₁ e₁ g e₂).symm

/-- The mirror subgroup `Γ'.map conjJAut` has the same number of order-`3` elliptic points. -/
theorem ellipticThree_map_conjJAut (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (e' : PSL(2, ℤ) ⧸ Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ)) ≃ Fin n) :
    ellipticThree (Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))) e' = ellipticThree Γ' e := by
  rw [ellipticThree_eq_count_fullCycleType, ellipticThree_eq_count_fullCycleType,
    fullCycleType_def, fullCycleType_def, ← cycleData_σ0, ← cycleData_σ0,
    cycleData_eq_of_equivalent (equivalent_mirror_modularTriple Γ' e e'), cycleData_mirror]

/-! ### Genus -/

/-- The genus of a finite-index `Γ' ≤ PSL(2, ℤ)`, defined as `(modularTriple Γ' e).genus`. -/
noncomputable def genus (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) : ℕ :=
  (modularTriple Γ' e).genus

/-- The defining formula for `genus`. -/
theorem genus_def (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    genus Γ' e = (modularTriple Γ' e).genus := (rfl)

/-- The Euler characteristic of `modularTriple Γ' e` is `2 - 2 g`. -/
theorem two_sub_two_mul_genus (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    2 - 2 * (genus Γ' e : ℤ) = (modularTriple Γ' e).eulerChar :=
  (isConnected_modularTriple Γ' e).two_sub_two_mul_genus

/-- Six times the Euler characteristic of `modularTriple Γ' e` is `6 c + 3 e₂ + 4 e₃ - n`. -/
theorem six_mul_eulerChar_modularTriple (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    6 * (modularTriple Γ' e).eulerChar =
      6 * (cuspCount Γ' e : ℤ) + 3 * (ellipticTwo Γ' e : ℤ) +
        4 * (ellipticThree Γ' e : ℤ) - n := by
  have h2 : (2 : ℤ) * orbitCount (permS Γ' e) = n + ellipticTwo Γ' e := by
    exact_mod_cast two_mul_orbitCount_permS Γ' e
  have h3 : (3 : ℤ) * orbitCount (modularTriple Γ' e).σ0 = n + 2 * ellipticThree Γ' e := by
    exact_mod_cast three_mul_orbitCount_σ0 Γ' e
  -- Unfold `permS` to `(modularTriple Γ' e).σ1` so `linarith` sees the same atom.
  dsimp only [permS] at h2
  rw [eulerChar_def, ← cuspCount_def]
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
@[simp] theorem genus_top (e : PSL(2, ℤ) ⧸ (⊤ : Subgroup PSL(2, ℤ)) ≃ Fin 1) : genus ⊤ e = 0 :=
  genus_of_degree_one _

/-- For a torsion-free subgroup (`e₂ = e₃ = 0`), the genus formula is `12 g + 6 c = 12 + n`. -/
theorem genus_formula_of_elliptic_eq_zero {Γ' : Subgroup PSL(2, ℤ)} (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (h2 : ellipticTwo Γ' e = 0) (h3 : ellipticThree Γ' e = 0) :
    12 * genus Γ' e + 6 * cuspCount Γ' e = 12 + n := by
  rw [genus_def]
  have := genus_formula Γ' e
  omega

/-- A subgroup has genus `0` if and only if `3 e₂ + 4 e₃ + 6 c = 12 + n`. -/
theorem genus_eq_zero_iff (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    genus Γ' e = 0 ↔
      3 * ellipticTwo Γ' e + 4 * ellipticThree Γ' e + 6 * cuspCount Γ' e = 12 + n :=
  genus_modularTriple_eq_zero_iff Γ' e

/-- Every finite-index subgroup of `PSL(2, ℤ)` with positive genus has index at least `6`. -/
theorem six_le_of_genus_pos {Γ' : Subgroup PSL(2, ℤ)} {e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n}
    (hg : 0 < genus Γ' e) : 6 ≤ n :=
  six_le_of_genus_modularTriple_pos Γ' e hg

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
@[simp] theorem invariants_index (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (invariants Γ' e).index = n := (rfl)

/-- The genus field of `invariants Γ' e` is `genus Γ' e`. -/
@[simp] theorem invariants_genus (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (invariants Γ' e).genus = genus Γ' e := (rfl)

/-- The order-`2` elliptic count field of `invariants Γ' e` is `ellipticTwo Γ' e`. -/
@[simp] theorem invariants_ellipticTwo (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (invariants Γ' e).ellipticTwo = ellipticTwo Γ' e := (rfl)

/-- The order-`3` elliptic count field of `invariants Γ' e` is `ellipticThree Γ' e`. -/
@[simp] theorem invariants_ellipticThree (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (invariants Γ' e).ellipticThree = ellipticThree Γ' e := (rfl)

/-- The cusp-width multiset field of `invariants Γ' e` is `cuspWidths Γ' e`. -/
@[simp] theorem invariants_cuspWidths (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (invariants Γ' e).cuspWidths = cuspWidths Γ' e := (rfl)

/-- The cusp count of `invariants Γ' e` is `cuspCount Γ' e`. -/
@[simp] theorem invariants_cuspCount (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (invariants Γ' e).cuspCount = cuspCount Γ' e :=
  card_cuspWidths Γ' e

/-- Equivalent modular triples have identical invariant vectors. -/
theorem invariants_eq_of_equivalent {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : (modularTriple Γ₁ e₁).Equivalent (modularTriple Γ₂ e₂)) :
    invariants Γ₁ e₁ = invariants Γ₂ e₂ :=
  Invariants.ext rfl (genus_eq_of_equivalent h) (ellipticTwo_eq_of_equivalent h)
    (ellipticThree_eq_of_equivalent h) (cuspWidths_eq_of_equivalent h)

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
    invariants (Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))) e' = invariants Γ' e :=
  Invariants.ext rfl (genus_map_conjJAut Γ' e e') (ellipticTwo_map_conjJAut Γ' e e')
    (ellipticThree_map_conjJAut Γ' e e') (cuspWidths_map_conjJAut Γ' e e')

/-- The full modular group `⊤` has invariant vector `(1, 0, 1, 1, {1})`. -/
@[simp] theorem invariants_top (e : PSL(2, ℤ) ⧸ (⊤ : Subgroup PSL(2, ℤ)) ≃ Fin 1) :
    invariants ⊤ e = ⟨1, 0, 1, 1, {1}⟩ := by ext1 <;> simp

/-! ### Opposite (right-coset / LMFDB) convention -/

/-- Under the opposite (right-coset) convention, `cuspWidths` agrees with the full cycle type of
the right-coset permutation of `T`. -/
theorem cuspWidths_quotientRightRel (Γ' : Subgroup PSL(2, ℤ))
    (r : Quotient (QuotientGroup.rightRel Γ') ≃ Fin n) :
    cuspWidths Γ' ((QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ').symm.trans r) =
      (r.permCongr (Γ'.rightCosetPerm (T : PSL(2, ℤ)))).fullCycleType := by
  rw [cuspWidths_def, permT, (modularTriple_quotientRightRel Γ' r).2.2.2.1, fullCycleType_inv]

/-- Under the opposite convention, `cuspCount` equals the orbit count of the right-coset
permutation of `T`. -/
theorem cuspCount_quotientRightRel (Γ' : Subgroup PSL(2, ℤ))
    (r : Quotient (QuotientGroup.rightRel Γ') ≃ Fin n) :
    cuspCount Γ' ((QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ').symm.trans r) =
      orbitCount (r.permCongr (Γ'.rightCosetPerm (T : PSL(2, ℤ)))) := by
  rw [cuspCount_def, permT, (modularTriple_quotientRightRel Γ' r).2.2.2.1, orbitCount_inv]

/-- Under the opposite convention, `ellipticTwo` counts the fixed points of the right-coset
permutation of `S`. -/
theorem ellipticTwo_quotientRightRel (Γ' : Subgroup PSL(2, ℤ))
    (r : Quotient (QuotientGroup.rightRel Γ') ≃ Fin n) :
    ellipticTwo Γ' ((QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ').symm.trans r) =
      Fintype.card {x : Fin n // r.permCongr (Γ'.rightCosetPerm (S : PSL(2, ℤ))) x = x} := by
  rw [ellipticTwo_def, ← Fintype.card_subtype, permS,
    (modularTriple_quotientRightRel Γ' r).2.2.1]

/-- Under the opposite convention, `ellipticThree` counts the fixed points of the right-coset
permutation of `R = S T`. -/
theorem ellipticThree_quotientRightRel (Γ' : Subgroup PSL(2, ℤ))
    (r : Quotient (QuotientGroup.rightRel Γ') ≃ Fin n) :
    ellipticThree Γ' ((QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ').symm.trans r) =
      Fintype.card {x : Fin n // r.permCongr (Γ'.rightCosetPerm (R : PSL(2, ℤ))) x = x} := by
  rw [ellipticThree_eq_card_fixed_permR, (modularTriple_quotientRightRel Γ' r).2.2.2.2,
    card_subtype_apply_eq, support_inv, ← card_subtype_apply_eq]

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
    have hinv : chiralTriple.σ1⁻¹ = chiralTriple.σ1 := by decide
    simpa [hinv] using congrArg PermutationTriple.σ1 hτ
  have hinf : τ * chiralTriple.σinf * τ⁻¹ = chiralTriple.σinf⁻¹ := by
    simpa using congrArg PermutationTriple.σinf hτ
  have hcommS (x : Fin 7) : τ (chiralTriple.σ1 x) = chiralTriple.σ1 (τ x) := by
    simpa using congrFun (congrArg DFunLike.coe h1) (τ x)
  have hcommT (x : Fin 7) : τ (chiralTriple.σinf x) = chiralTriple.σinf⁻¹ (τ x) := by
    simpa using congrFun (congrArg DFunLike.coe hinf) (τ x)
  have hτ0 : τ 0 = 0 :=
    (by decide : ∀ x : Fin 7, chiralTriple.σ1 x = x → x = 0) (τ 0)
      (by rw [← hcommS 0, (by decide : chiralTriple.σ1 0 = 0)])
  have hτ2 : τ 2 = 3 := by
    rw [← (by decide : chiralTriple.σinf 0 = 2), hcommT 0, hτ0]; decide
  have hτ1 : τ 1 = 6 := by
    rw [← (by decide : chiralTriple.σinf 2 = 1), hcommT 2, hτ2]; decide
  have h35 : (3 : Fin 7) = 5 := by
    rw [← hτ2, ← (by decide : chiralTriple.σ1 1 = 2), hcommS 1, hτ1]; decide
  exact absurd h35 (by decide)

/-- **Non-completeness of the classical invariant vector.** There exist two non-conjugate
index-`7` subgroups of `PSL(2, ℤ)` — a chiral subgroup and its mirror under `conjJAut` —
sharing the same invariant vector `(7, 0, 1, 1, {6, 1})`. -/
theorem exists_not_conj_invariants_eq :
    ∃ (Γ₁ Γ₂ : Subgroup PSL(2, ℤ)) (e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin 7)
      (e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin 7),
      invariants Γ₁ e₁ = ⟨7, 0, 1, 1, {6, 1}⟩ ∧
      invariants Γ₂ e₂ = ⟨7, 0, 1, 1, {6, 1}⟩ ∧
      ¬ ∃ g : ConjAct PSL(2, ℤ), g • Γ₁ = Γ₂ := by
  obtain ⟨Γ₁, _, e₁, -, heq₁⟩ :=
    exists_modularTriple_equivalent chiralTriple_isConnected (by decide) (by decide)
  let Γ₂ : Subgroup PSL(2, ℤ) := Γ₁.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))
  let e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin 7 :=
    (TauCeti.QuotientGroup.congrOfMapEq conjJAut (rfl : Γ₁.map _ = Γ₂)).symm.trans e₁
  have hinv₁ : invariants Γ₁ e₁ = ⟨7, 0, 1, 1, {6, 1}⟩ := by
    refine Invariants.ext rfl ?_ ?_ ?_ ?_
    · rw [invariants_genus, genus_def, PermutationTriple.genus_eq_of_equivalent heq₁,
        ← computedGenus_eq]; decide
    · rw [invariants_ellipticTwo, ellipticTwo_eq_count_fullCycleType, fullCycleType_def,
        ← cycleData_σ1, cycleData_eq_of_equivalent heq₁, cycleData_σ1, ← fullCycleType_def,
        ← computedCycleType_eq_fullCycleType]; decide
    · rw [invariants_ellipticThree, ellipticThree_eq_count_fullCycleType, fullCycleType_def,
        ← cycleData_σ0, cycleData_eq_of_equivalent heq₁, cycleData_σ0, ← fullCycleType_def,
        ← computedCycleType_eq_fullCycleType]; decide
    · rw [invariants_cuspWidths, cuspWidths_eq_cycleData, cycleData_eq_of_equivalent heq₁,
        cycleData_σinf, ← fullCycleType_def, ← computedCycleType_eq_fullCycleType]; decide
  refine ⟨Γ₁, Γ₂, e₁, e₂, hinv₁, by rw [invariants_map_conjJAut Γ₁ e₁ e₂, hinv₁], fun hconj ↦ ?_⟩
  refine not_equivalent_chiralTriple_mirror (IsoClass.mk_eq_mk_iff.mp ?_)
  exact (IsoClass.mk_eq_mk_iff.mpr heq₁).symm.trans <|
    (IsoClass.mk_eq_mk_iff.mpr ((millington e₁ e₂).mpr hconj)).trans <|
    (IsoClass.mk_eq_mk_iff.mpr (equivalent_mirror_modularTriple Γ₁ e₁ e₂)).trans
    (IsoClass.mk_eq_mk_iff.mpr heq₁.mirror)

end TauCeti.ModularGroup
