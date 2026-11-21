/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import TauCeti.Combinatorics.PermutationTriple.EulerCharacteristic
public import TauCeti.GroupTheory.DoubleCoset.Orbits
public import TauCeti.GroupTheory.GroupAction.Orbit.CycleType
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Projective
public import TauCeti.NumberTheory.Modular.CosetTriple
import TauCeti.Combinatorics.PermutationTriple.Mirror
import TauCeti.GroupTheory.Coset.Basic

/-!
# Combinatorial invariants of the modular coset triple

Every finite-index subgroup `Γ' ≤ PSL(2, ℤ)` with left-coset enumeration
`e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n` determines `modularTriple Γ' e = (σ0, σ1, σinf)`
(`permS = σ1`, `permT = σinf`, `σ0 = ρ U`), yielding the combinatorial invariants of `X(Γ')`:

* **Cusp widths and count (`cuspWidths`, `cuspCount`, `cuspCycleWidth`)**: the cycle lengths of
  `permT` (fixed points included, summing to `n`), the number of cycles of `permT`, the
  double-coset bijection `permTCycleEquivDoubleCoset` onto `Γ' \ PSL(2, ℤ) / ⟨T⟩`, subgroup
  inclusion maps `cuspCycleMapOfLE`, and fiber-sum formulas `sum_cuspCycleWidth_fiber_of_le` and
  `sum_widthRatio_permT_fiber_of_le`.
* **Elliptic points (`ellipticTwo`, `ellipticThree`)**: the fixed-point counts of `permS` and
  `σ0` (or `permR`), satisfying `ε₂ ≡ n (mod 2)` and `ε₃ ≡ n (mod 3)`.
* **Genus (`genus`) and the genus formula (`genus_formula`)**:
  `12 g + 3 ε₂ + 4 ε₃ + 6 ε∞ = 12 + n`, together with torsion-free divisibility `6 ∣ n` and
  `6 ≤ n` when `0 < g`.
* **Invariance and right-coset convention (`Invariants`, `invariants`)**: independence of the
  coset numbering, conjugacy class, and `conjJAut` mirror, and explicit formulas under the
  right-coset convention (`invariants_quotientRightRel`).

## References

* M. H. Millington, *Subgroups of the classical modular group*, J. London Math. Soc. (2) 1 (1969),
  351–357.
* C. Kurth, L. Long, *Computations with finite index subgroups of `PSL₂(ℤ)` using Farey symbols*,
  in *Advances in Algebra and Combinatorics*, World Scientific (2008), 225–242, arXiv:0710.1835.
* F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228, Springer, 2005,
  Theorem 3.1.1 and §§3.7–3.8.
* G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §1.6 and Proposition 1.40.
-/

open Equiv Equiv.Perm Matrix
open scoped MatrixGroups Pointwise Finset

public section

namespace TauCeti.ModularGroup

open _root_.ModularGroup PermutationTriple

variable {m n : ℕ}

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

/-- The genus of a finite-index `Γ' ≤ PSL(2, ℤ)`, defined as `(modularTriple Γ' e).genus`. -/
noncomputable def genus (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) : ℕ :=
  (modularTriple Γ' e).genus

variable (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)

theorem cuspWidths_def : cuspWidths Γ' e = (permT Γ' e).fullCycleType := (rfl)

theorem cuspCount_def : cuspCount Γ' e = orbitCount (permT Γ' e) := (rfl)

theorem ellipticTwo_def : ellipticTwo Γ' e = #{i | permS Γ' e i = i} := (rfl)

theorem ellipticThree_def : ellipticThree Γ' e = #{i | (modularTriple Γ' e).σ0 i = i} := (rfl)

theorem genus_def : genus Γ' e = (modularTriple Γ' e).genus := (rfl)

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

/-- `cuspWidths Γ' e` is the `∞`-component of the cycle data of `modularTriple Γ' e`. -/
theorem cuspWidths_eq_cycleData :
    cuspWidths Γ' e = (modularTriple Γ' e).cycleData.2.2 := by
  rw [cuspWidths_def, cycleData_σinf, fullCycleType_def, permT]

/-- Every finite-index subgroup of `PSL(2, ℤ)` has at least one cusp. -/
theorem cuspCount_pos : 0 < cuspCount Γ' e := by
  have : Nonempty (Fin n) := ⟨e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')⟩
  rw [cuspCount_def]
  exact (permT Γ' e).orbitCount_pos

/-- An index-`n` subgroup of `PSL(2, ℤ)` has at most `n` cusps. -/
theorem cuspCount_le : cuspCount Γ' e ≤ n := by
  simpa [cuspCount_def] using (permT Γ' e).orbitCount_le_card

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

/-- `ellipticThree Γ' e` equally counts the fixed points of `permR Γ' e`, since `permR` is
conjugate to `σ0⁻¹`. -/
theorem ellipticThree_eq_card_fixed_permR :
    ellipticThree Γ' e = Fintype.card {x : Fin n // permR Γ' e x = x} := by
  have hconj : permR Γ' e = (permS Γ' e)⁻¹ * (modularTriple Γ' e).σ0⁻¹ * ((permS Γ' e)⁻¹)⁻¹ := by
    simpa only [inv_inv] using permR_eq_permS_inv_mul_σ0_inv_mul_permS Γ' e
  rw [ellipticThree_eq_count_fullCycleType, card_subtype_apply_eq, ← count_one_fullCycleType,
    hconj, fullCycleType_conj, fullCycleType_inv]

/-- `ellipticTwo Γ' e ≤ n`. -/
theorem ellipticTwo_le : ellipticTwo Γ' e ≤ n := by
  simpa [ellipticTwo_def, ← Fintype.card_subtype] using
    Fintype.card_subtype_le (fun x : Fin n ↦ permS Γ' e x = x)

/-- `ellipticThree Γ' e ≤ n`. -/
theorem ellipticThree_le : ellipticThree Γ' e ≤ n := by
  simpa [ellipticThree_def, ← Fintype.card_subtype] using
    Fintype.card_subtype_le (fun x : Fin n ↦ (modularTriple Γ' e).σ0 x = x)

/-! ### Cycle periods of `permT`, double cosets, and width ratios -/

/-- The period of `permT Γ' e` at `e (g Γ')` divides `h` iff `g⁻¹ T ^ h g ∈ Γ'`. -/
theorem minimalPeriod_permT_dvd_iff (g : PSL(2, ℤ)) (h : ℕ) :
    Function.minimalPeriod (permT Γ' e) (e (g : PSL(2, ℤ) ⧸ Γ')) ∣ h ↔
      g⁻¹ * (T : PSL(2, ℤ)) ^ h * g ∈ Γ' := by
  rw [← Function.isPeriodicPt_iff_minimalPeriod_dvd, Function.IsPeriodicPt, Function.IsFixedPt,
    Perm.iterate_eq_pow, permT_pow_apply_eq_iff]

/-- Lifted to `SL(2, ℤ)`, the period of `permT Γ' e` at `e (σ Γ')` divides `h` iff
`σ⁻¹ T ^ h σ ∈ Γ'.liftSL`. -/
theorem minimalPeriod_permT_mk_dvd_iff (σ : SL(2, ℤ)) (h : ℕ) :
    Function.minimalPeriod (permT Γ' e) (e ((σ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) ∣ h ↔
      σ⁻¹ * _root_.ModularGroup.T ^ h * σ ∈ Γ'.liftSL := by
  rw [minimalPeriod_permT_dvd_iff, Subgroup.mem_liftSL, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]

/-- Every point has positive minimal period under `permT Γ' e`. -/
theorem minimalPeriod_permT_pos (x : Fin n) : 0 < Function.minimalPeriod (permT Γ' e) x :=
  Function.minimalPeriod_pos_of_mem_periodicPts ⟨orderOf (permT Γ' e), orderOf_pos _, by
    simp [Function.IsPeriodicPt, Function.IsFixedPt, ← Equiv.Perm.coe_pow]⟩

/-- The period of `permT Γ' e` at `e (g Γ')` is the least positive `h` with `g⁻¹ T ^ h g ∈ Γ'`. -/
theorem minimalPeriod_permT_eq_sInf (g : PSL(2, ℤ)) :
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
theorem minimalPeriod_permT_mk_inv_eq_sInf (σ : SL(2, ℤ)) :
    Function.minimalPeriod (permT Γ' e)
        (e (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) =
      sInf {h : ℕ | 0 < h ∧ σ * _root_.ModularGroup.T ^ h * σ⁻¹ ∈ Γ'.liftSL} := by
  rw [minimalPeriod_permT_eq_sInf]; congr 1; ext h
  simp [Subgroup.mem_liftSL, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]

/-- At the base coset `e 1` (the cusp `∞`), the period of `permT Γ' e` is the least positive `h`
with `T ^ h ∈ Γ'.liftSL`. -/
theorem minimalPeriod_permT_one :
    Function.minimalPeriod (permT Γ' e) (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) =
      sInf {h : ℕ | 0 < h ∧ _root_.ModularGroup.T ^ h ∈ Γ'.liftSL} := by
  simpa using minimalPeriod_permT_mk_inv_eq_sInf Γ' e 1

/-- **Double-coset bijection for cusps.** The cycles of `permT Γ' e` are in canonical bijection
with the double cosets `Γ' \ PSL(2, ℤ) / ⟨T⟩`, sending the cycle of `e (g Γ')` to
`Γ' g⁻¹ ⟨T⟩`. -/
noncomputable def permTCycleEquivDoubleCoset :
    Quotient (SameCycle.setoid (permT Γ' e)) ≃
      DoubleCoset.Quotient (Γ' : Set PSL(2, ℤ)) (Subgroup.zpowers (T : PSL(2, ℤ))) :=
  (Quotient.congr (Equiv.refl _)
    (fun _ _ ↦ by rw [permT, modularTriple_σinf]; exact Iff.rfl)).trans
    ((e.sameCycleQuotientEquivOrbitQuotient (T : PSL(2, ℤ))).trans
      (TauCeti.orbitQuotientEquivDoubleCoset Γ' (Subgroup.zpowers (T : PSL(2, ℤ)))))

/-- `permTCycleEquivDoubleCoset` sends the cycle of `e (g Γ')` to `Γ' g⁻¹ ⟨T⟩`. -/
@[simp] theorem permTCycleEquivDoubleCoset_mk (g : PSL(2, ℤ)) :
    permTCycleEquivDoubleCoset Γ' e (Quotient.mk _ (e (g : PSL(2, ℤ) ⧸ Γ'))) =
      DoubleCoset.mk Γ' (Subgroup.zpowers (T : PSL(2, ℤ))) g⁻¹ := by
  rw [permTCycleEquivDoubleCoset, Equiv.trans_apply, Equiv.trans_apply]
  exact (congrArg _ (e.sameCycleQuotientEquivOrbitQuotient_mk (T : PSL(2, ℤ)) _)).trans
    (TauCeti.orbitQuotientEquivDoubleCoset_mk Γ' (Subgroup.zpowers (T : PSL(2, ℤ))) g)

/-- The inverse of `permTCycleEquivDoubleCoset` sends the double coset `Γ' g⁻¹ ⟨T⟩` to the cycle
of `e (g Γ')`. -/
@[simp] theorem permTCycleEquivDoubleCoset_symm_mk (g : PSL(2, ℤ)) :
    (permTCycleEquivDoubleCoset Γ' e).symm
        (DoubleCoset.mk Γ' (Subgroup.zpowers (T : PSL(2, ℤ))) g⁻¹) =
      Quotient.mk _ (e (g : PSL(2, ℤ) ⧸ Γ')) :=
  (permTCycleEquivDoubleCoset Γ' e).symm_apply_eq.mpr (permTCycleEquivDoubleCoset_mk Γ' e g).symm

/-- Two cosets `e (g₁ Γ')` and `e (g₂ Γ')` lie in the same cycle of `permT Γ' e` iff `g₁⁻¹` and
`g₂⁻¹` lie in the same double coset in `Γ' \ PSL(2, ℤ) / ⟨T⟩`. -/
theorem sameCycle_permT_iff_doubleCoset (g₁ g₂ : PSL(2, ℤ)) :
    (permT Γ' e).SameCycle (e (g₁ : PSL(2, ℤ) ⧸ Γ')) (e (g₂ : PSL(2, ℤ) ⧸ Γ')) ↔
      DoubleCoset.mk Γ' (Subgroup.zpowers (T : PSL(2, ℤ))) g₁⁻¹ =
        DoubleCoset.mk Γ' (Subgroup.zpowers (T : PSL(2, ℤ))) g₂⁻¹ := by
  rw [← permTCycleEquivDoubleCoset_mk Γ' e g₁, ← permTCycleEquivDoubleCoset_mk Γ' e g₂,
    (permTCycleEquivDoubleCoset Γ' e).injective.eq_iff, Quotient.eq]
  exact Iff.rfl

/-- The cusp count equals the number of double cosets `Γ' \ PSL(2, ℤ) / ⟨T⟩`. -/
theorem cuspCount_eq_card_doubleCoset :
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
  Quotient.map (fun y ↦ e' (Subgroup.quotientMapOfLE h (e''.symm y)))
    fun y₁ y₂ ⟨k, hk⟩ ↦ by
      subst hk; obtain ⟨q₁, rfl⟩ := e''.surjective y₁
      induction q₁ using QuotientGroup.induction_on with | H g =>
      exact ⟨k, by
        rw [permT_zpow_apply, e''.symm_apply_apply, e''.symm_apply_apply]
        exact permT_zpow_apply Γ' e' g k⟩

/-- Explicit evaluation of `cuspCycleMapOfLE` on the cycle of an arbitrary point `y : Fin m`.
Not `@[simp]` so it does not clash with `cuspCycleMapOfLE_mk`. -/
theorem cuspCycleMapOfLE_mk_apply {Γ'' Γ' : Subgroup PSL(2, ℤ)} (h : Γ'' ≤ Γ')
    (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m) (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (y : Fin m) :
    cuspCycleMapOfLE h e'' e' (Quotient.mk _ y) =
      Quotient.mk _ (e' (Subgroup.quotientMapOfLE h (e''.symm y))) :=
  (rfl)

/-- `cuspCycleMapOfLE` sends the cycle of `e'' (g Γ'')` to the cycle of `e' (g Γ')`. -/
@[simp] theorem cuspCycleMapOfLE_mk {Γ'' Γ' : Subgroup PSL(2, ℤ)} (h : Γ'' ≤ Γ')
    (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m) (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (g : PSL(2, ℤ)) :
    cuspCycleMapOfLE h e'' e' (Quotient.mk _ (e'' (g : PSL(2, ℤ) ⧸ Γ''))) =
      Quotient.mk _ (e' (g : PSL(2, ℤ) ⧸ Γ')) := by
  rw [cuspCycleMapOfLE_mk_apply, e''.symm_apply_apply]
  rfl

/-- `cuspCycleMapOfLE` for the trivial inclusion `Γ' ≤ Γ'` is the identity. -/
@[simp] theorem cuspCycleMapOfLE_self (q : Quotient (SameCycle.setoid (permT Γ' e))) :
    cuspCycleMapOfLE (le_refl Γ') e e q = q := by
  induction q using Quotient.ind with | _ y =>
  obtain ⟨qy, rfl⟩ := e.surjective y
  induction qy using QuotientGroup.induction_on with | H g =>
  exact cuspCycleMapOfLE_mk (le_refl Γ') e e g

/-- `cuspCycleMapOfLE` respects composition of subgroup inclusions. -/
@[simp] theorem cuspCycleMapOfLE_cuspCycleMapOfLE {Γ''' Γ'' Γ' : Subgroup PSL(2, ℤ)}
    {k : ℕ} (h₁ : Γ''' ≤ Γ'') (h₂ : Γ'' ≤ Γ')
    (e''' : PSL(2, ℤ) ⧸ Γ''' ≃ Fin k) (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m)
    (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (q : Quotient (SameCycle.setoid (permT Γ''' e'''))) :
    cuspCycleMapOfLE h₂ e'' e' (cuspCycleMapOfLE h₁ e''' e'' q) =
      cuspCycleMapOfLE (h₁.trans h₂) e''' e' q := by
  induction q using Quotient.ind with | _ y =>
  obtain ⟨qy, rfl⟩ := e'''.surjective y
  induction qy using QuotientGroup.induction_on with | H g =>
  rw [cuspCycleMapOfLE_mk, cuspCycleMapOfLE_mk, cuspCycleMapOfLE_mk]

/-- Function-composition form of `cuspCycleMapOfLE_cuspCycleMapOfLE`. -/
theorem cuspCycleMapOfLE_comp {Γ''' Γ'' Γ' : Subgroup PSL(2, ℤ)}
    {k : ℕ} (h₁ : Γ''' ≤ Γ'') (h₂ : Γ'' ≤ Γ')
    (e''' : PSL(2, ℤ) ⧸ Γ''' ≃ Fin k) (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m)
    (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspCycleMapOfLE h₂ e'' e' ∘ cuspCycleMapOfLE h₁ e''' e'' =
      cuspCycleMapOfLE (h₁.trans h₂) e''' e' :=
  funext (cuspCycleMapOfLE_cuspCycleMapOfLE h₁ h₂ e''' e'' e')

/-- The width of a `permT`-cycle, well-defined on `Quotient (SameCycle.setoid (permT Γ' e))`. -/
noncomputable def cuspCycleWidth :
    Quotient (SameCycle.setoid (permT Γ' e)) → ℕ :=
  Quotient.lift (Function.minimalPeriod (permT Γ' e)) fun _ _ h ↦ h.minimalPeriod_eq

/-- On the cycle of `x`, `cuspCycleWidth` is `Function.minimalPeriod (permT Γ' e) x`. -/
@[simp] theorem cuspCycleWidth_mk (x : Fin n) :
    cuspCycleWidth Γ' e (Quotient.mk _ x) = Function.minimalPeriod (permT Γ' e) x := (rfl)

/-- `cuspWidths Γ' e` is the multiset of `cuspCycleWidth Γ' e` over all `permT`-cycles. -/
theorem cuspWidths_eq_map_cuspCycleWidth
    [Fintype (Quotient (SameCycle.setoid (permT Γ' e)))] :
    cuspWidths Γ' e = Finset.univ.val.map (cuspCycleWidth Γ' e) := by
  rw [cuspWidths_def]
  exact fullCycleType_eq_map_univ (permT Γ' e) (Equiv.refl _) fun _ ↦ rfl

/-- The period of `permT Γ' e` at any point `x` belongs to `cuspWidths Γ' e`. -/
theorem minimalPeriod_permT_mem_cuspWidths (x : Fin n) :
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

/-- The cardinality of the fibre of `Quotient.mk (SameCycle.setoid (permT Γ' e))` over a cusp
cycle `q` is `cuspCycleWidth Γ' e q`. -/
theorem natCard_fiber_cuspCycle (q : Quotient (SameCycle.setoid (permT Γ' e))) :
    Nat.card {y : Fin n // Quotient.mk (SameCycle.setoid (permT Γ' e)) y = q} =
      cuspCycleWidth Γ' e q := by
  induction q using Quotient.ind with | _ x =>
  exact Perm.natCard_fiber_quotientMk_sameCycle (permT Γ' e) x

/-- The cardinality of the fibre of `permTCycleEquivDoubleCoset Γ' e ∘ Quotient.mk _` over a
double coset `d` is `cuspCycleWidth Γ' e ((permTCycleEquivDoubleCoset Γ' e).symm d)`. -/
theorem natCard_fiber_permTCycleEquivDoubleCoset
    (d : DoubleCoset.Quotient (Γ' : Set PSL(2, ℤ)) (Subgroup.zpowers (T : PSL(2, ℤ)))) :
    Nat.card {y : Fin n // permTCycleEquivDoubleCoset Γ' e (Quotient.mk _ y) = d} =
      cuspCycleWidth Γ' e ((permTCycleEquivDoubleCoset Γ' e).symm d) := by
  rw [← natCard_fiber_cuspCycle Γ' e ((permTCycleEquivDoubleCoset Γ' e).symm d)]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ (Equiv.eq_symm_apply _).symm)

private theorem sum_cuspCycleWidth_fiber_eq_natCard {Γ'' Γ' : Subgroup PSL(2, ℤ)} (h : Γ'' ≤ Γ')
    (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m) (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (c : Quotient (SameCycle.setoid (permT Γ' e'))) :
    ∑ᶠ q ∈ {q | cuspCycleMapOfLE h e'' e' q = c}, cuspCycleWidth Γ'' e'' q =
      Nat.card {y : Fin m // cuspCycleMapOfLE h e'' e' (Quotient.mk _ y) = c} := by
  classical
  have : Fintype (Quotient (SameCycle.setoid (permT Γ'' e''))) := Fintype.ofFinite _
  have hSfin : ({q | cuspCycleMapOfLE h e'' e' q = c} : Set _).Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hSfin,
    show hSfin.toFinset = Finset.univ.filter (fun q ↦ cuspCycleMapOfLE h e'' e' q = c) by
      ext; simp]
  calc
    ∑ q ∈ Finset.univ.filter (fun q ↦ cuspCycleMapOfLE h e'' e' q = c), cuspCycleWidth Γ'' e'' q
      = ∑ q ∈ Finset.univ.filter (fun q ↦ cuspCycleMapOfLE h e'' e' q = c),
          (Finset.univ.filter (fun y : Fin m ↦
            Quotient.mk (SameCycle.setoid (permT Γ'' e'')) y = q)).card := by
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        rw [← natCard_fiber_cuspCycle Γ'' e'' q, Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = ∑ q ∈ Finset.univ.filter (fun q ↦ cuspCycleMapOfLE h e'' e' q = c),
          ∑ _y ∈ (Finset.univ.filter (fun y : Fin m ↦
            cuspCycleMapOfLE h e'' e' (Quotient.mk _ y) = c)).filter
              (fun y ↦ Quotient.mk (SameCycle.setoid (permT Γ'' e'')) y = q), (1 : ℕ) := by
        refine Finset.sum_congr rfl fun q hq ↦ ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
        rw [← Finset.card_eq_sum_ones]
        congr 1; ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun hy ↦ ⟨by rw [hy, hq], hy⟩, And.right⟩
    _ = (Finset.univ.filter (fun y : Fin m ↦
          cuspCycleMapOfLE h e'' e' (Quotient.mk _ y) = c)).card := by
        rw [Finset.card_eq_sum_ones]
        exact Finset.sum_fiberwise_of_maps_to
          (fun y hy ↦ by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢; exact hy) _
    _ = Nat.card {y : Fin m // cuspCycleMapOfLE h e'' e' (Quotient.mk _ y) = c} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **Sum of cusp widths over a cusp under subgroup inclusion.** For `Γ'' ≤ Γ'`, the widths of
the cusps of `Γ''` lying over a cusp `c` of `Γ'` sum to `[Γ' : Γ''] · width(c)`. -/
theorem sum_cuspCycleWidth_fiber_of_le {Γ'' Γ' : Subgroup PSL(2, ℤ)} (h : Γ'' ≤ Γ')
    (e'' : PSL(2, ℤ) ⧸ Γ'' ≃ Fin m) (e' : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (c : Quotient (SameCycle.setoid (permT Γ' e'))) :
    ∑ᶠ q ∈ {q | cuspCycleMapOfLE h e'' e' q = c}, cuspCycleWidth Γ'' e'' q =
      Γ''.relIndex Γ' * cuspCycleWidth Γ' e' c := by
  classical
  let proj : Fin m → Fin n := fun y ↦ e' (Subgroup.quotientMapOfLE h (e''.symm y))
  have hfiber (x : Fin n) : Nat.card {y : Fin m // proj y = x} = Γ''.relIndex Γ' := by
    rw [← Subgroup.card_fiber_quotientMapOfLE h (e'.symm x)]
    refine Nat.card_congr (Equiv.subtypeEquiv e''.symm fun y ↦ ?_)
    dsimp only [proj]
    exact (Equiv.eq_symm_apply e').symm
  let equivSigma :
      {y : Fin m // cuspCycleMapOfLE h e'' e' (Quotient.mk _ y) = c} ≃
        Σ x : {x : Fin n // Quotient.mk (SameCycle.setoid (permT Γ' e')) x = c},
          {y : Fin m // proj y = x.val} :=
    { toFun := fun ⟨y, hy⟩ ↦ ⟨⟨proj y, by rwa [← cuspCycleMapOfLE_mk_apply]⟩, ⟨y, rfl⟩⟩
      invFun := fun ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ↦
        ⟨y, by rw [cuspCycleMapOfLE_mk_apply]; change Quotient.mk _ (proj y) = c; rwa [hy]⟩
      left_inv := fun ⟨_, _⟩ ↦ rfl
      right_inv := fun ⟨⟨_, _⟩, ⟨_, rfl⟩⟩ ↦ rfl }
  calc
    ∑ᶠ q ∈ {q | cuspCycleMapOfLE h e'' e' q = c}, cuspCycleWidth Γ'' e'' q
      = Nat.card {y : Fin m // cuspCycleMapOfLE h e'' e' (Quotient.mk _ y) = c} :=
        sum_cuspCycleWidth_fiber_eq_natCard h e'' e' c
    _ = ∑ x : {x : Fin n // Quotient.mk (SameCycle.setoid (permT Γ' e')) x = c},
          Nat.card {y : Fin m // proj y = x.val} := by
        rw [Nat.card_congr equivSigma, Nat.card_eq_fintype_card, Fintype.card_sigma]
        simp_rw [Nat.card_eq_fintype_card]
    _ = Nat.card {x : Fin n // Quotient.mk (SameCycle.setoid (permT Γ' e')) x = c} *
          Γ''.relIndex Γ' := by
        simp_rw [hfiber, Finset.sum_const, Finset.card_univ, smul_eq_mul,
          ← Nat.card_eq_fintype_card]
    _ = Γ''.relIndex Γ' * cuspCycleWidth Γ' e' c := by
        rw [mul_comm, natCard_fiber_cuspCycle]

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

/-! ### The full modular group -/

section Top

variable (eTop : PSL(2, ℤ) ⧸ (⊤ : Subgroup PSL(2, ℤ)) ≃ Fin 1)

/-- The full modular group has a single cusp, of width one. -/
@[simp]
theorem cuspWidths_top : cuspWidths ⊤ eTop = {1} := by
  rw [cuspWidths, permT, modularTriple_top]
  simp

/-- The full modular group has one cusp. -/
@[simp]
theorem cuspCount_top : cuspCount ⊤ eTop = 1 := by
  rw [← card_cuspWidths, cuspWidths_top, Multiset.card_singleton]

/-- The full modular group has one elliptic point of period two, the orbit of `i`. -/
@[simp]
theorem ellipticTwo_top : ellipticTwo ⊤ eTop = 1 := by
  simp [ellipticTwo]

/-- The full modular group has one elliptic point of period three, the orbit of `e^{πi/3}`. -/
@[simp]
theorem ellipticThree_top : ellipticThree ⊤ eTop = 1 := by
  simp [ellipticThree]

/-- The full modular group `⊤` has genus `0`. -/
@[simp] theorem genus_top : genus ⊤ eTop = 0 :=
  genus_of_degree_one _

end Top

/-! ### Invariance under equivalence, numbering, conjugation, and `conjJAut` -/

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

/-- Equivalent modular triples have the same genus. -/
theorem genus_eq_of_equivalent
    (h : (modularTriple Γ₁ e₁).Equivalent (modularTriple Γ₂ e₂)) :
    genus Γ₁ e₁ = genus Γ₂ e₂ :=
  PermutationTriple.genus_eq_of_equivalent h

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

/-- The genus does not depend on the coset enumeration. -/
theorem genus_congr (e₁ e₂ : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    genus Γ' e₁ = genus Γ' e₂ :=
  genus_eq_of_equivalent (equivalent_modularTriple Γ' e₁ e₂)

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

/-- Conjugate subgroups of `PSL(2, ℤ)` have the same cusp widths. -/
theorem cuspWidths_eq_of_conj {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : ∃ g : ConjAct PSL(2, ℤ), g • Γ₁ = Γ₂) :
    cuspWidths Γ₁ e₁ = cuspWidths Γ₂ e₂ := by
  rcases h with ⟨g, rfl⟩
  exact (cuspWidths_conjAct_smul Γ₁ e₁ g e₂).symm

/-- Conjugate subgroups of `PSL(2, ℤ)` have the same cusp count. -/
theorem cuspCount_eq_of_conj {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : ∃ g : ConjAct PSL(2, ℤ), g • Γ₁ = Γ₂) :
    cuspCount Γ₁ e₁ = cuspCount Γ₂ e₂ := by
  rcases h with ⟨g, rfl⟩
  exact (cuspCount_conjAct_smul Γ₁ e₁ g e₂).symm

/-- Conjugate subgroups of `PSL(2, ℤ)` have the same number of order-`2` elliptic points. -/
theorem ellipticTwo_eq_of_conj {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : ∃ g : ConjAct PSL(2, ℤ), g • Γ₁ = Γ₂) :
    ellipticTwo Γ₁ e₁ = ellipticTwo Γ₂ e₂ := by
  rcases h with ⟨g, rfl⟩
  exact (ellipticTwo_conjAct_smul Γ₁ e₁ g e₂).symm

/-- Conjugate subgroups of `PSL(2, ℤ)` have the same number of order-`3` elliptic points. -/
theorem ellipticThree_eq_of_conj {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : ∃ g : ConjAct PSL(2, ℤ), g • Γ₁ = Γ₂) :
    ellipticThree Γ₁ e₁ = ellipticThree Γ₂ e₂ := by
  rcases h with ⟨g, rfl⟩
  exact (ellipticThree_conjAct_smul Γ₁ e₁ g e₂).symm

/-- Conjugate subgroups of `PSL(2, ℤ)` have the same genus. -/
theorem genus_eq_of_conj {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : ∃ g : ConjAct PSL(2, ℤ), g • Γ₁ = Γ₂) :
    genus Γ₁ e₁ = genus Γ₂ e₂ :=
  genus_eq_of_equivalent ((millington e₁ e₂).mpr h)

end Conjugation

section Mirror

variable (e' : PSL(2, ℤ) ⧸ Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ)) ≃ Fin n)

/-- The mirror subgroup `Γ'.map conjJAut` has the same multiset of cusp widths as `Γ'`. -/
theorem cuspWidths_map_conjJAut :
    cuspWidths (Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))) e' = cuspWidths Γ' e := by
  rw [cuspWidths_eq_cycleData, cuspWidths_eq_cycleData,
    cycleData_eq_of_equivalent (equivalent_mirror_modularTriple Γ' e e'), cycleData_mirror]

/-- The mirror subgroup `Γ'.map conjJAut` has the same cusp count as `Γ'`. -/
theorem cuspCount_map_conjJAut :
    cuspCount (Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))) e' = cuspCount Γ' e := by
  rw [← card_cuspWidths, ← card_cuspWidths, cuspWidths_map_conjJAut]

/-- The mirror subgroup `Γ'.map conjJAut` has the same number of order-`2` elliptic points. -/
theorem ellipticTwo_map_conjJAut :
    ellipticTwo (Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))) e' = ellipticTwo Γ' e := by
  rw [ellipticTwo_eq_count_fullCycleType, ellipticTwo_eq_count_fullCycleType,
    fullCycleType_def, fullCycleType_def, ← cycleData_σ1, ← cycleData_σ1,
    cycleData_eq_of_equivalent (equivalent_mirror_modularTriple Γ' e e'), cycleData_mirror]

/-- The mirror subgroup `Γ'.map conjJAut` has the same number of order-`3` elliptic points. -/
theorem ellipticThree_map_conjJAut :
    ellipticThree (Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))) e' = ellipticThree Γ' e := by
  rw [ellipticThree_eq_count_fullCycleType, ellipticThree_eq_count_fullCycleType,
    fullCycleType_def, fullCycleType_def, ← cycleData_σ0, ← cycleData_σ0,
    cycleData_eq_of_equivalent (equivalent_mirror_modularTriple Γ' e e'), cycleData_mirror]

/-- The mirror subgroup `Γ'.map conjJAut` has the same genus as `Γ'`. -/
theorem genus_map_conjJAut :
    genus (Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))) e' = genus Γ' e := by
  rw [genus_def, genus_def,
    PermutationTriple.genus_eq_of_equivalent (equivalent_mirror_modularTriple Γ' e e'),
    genus_mirror]

end Mirror

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

/-- The Euler characteristic of `modularTriple Γ' e` is `2 - 2 g`. -/
theorem two_sub_two_mul_genus :
    2 - 2 * (genus Γ' e : ℤ) = (modularTriple Γ' e).eulerChar :=
  (isConnected_modularTriple Γ' e).two_sub_two_mul_genus

/-- Six times the Euler characteristic of `modularTriple Γ' e` is `6 c + 3 e₂ + 4 e₃ - n`. -/
theorem six_mul_eulerChar_modularTriple :
    6 * (modularTriple Γ' e).eulerChar =
      6 * (cuspCount Γ' e : ℤ) + 3 * (ellipticTwo Γ' e : ℤ) +
        4 * (ellipticThree Γ' e : ℤ) - n := by
  have h2 : (2 : ℤ) * orbitCount (permS Γ' e) = n + ellipticTwo Γ' e := by
    exact_mod_cast two_mul_orbitCount_permS Γ' e
  have h3 : (3 : ℤ) * orbitCount (modularTriple Γ' e).σ0 = n + 2 * ellipticThree Γ' e := by
    exact_mod_cast three_mul_orbitCount_σ0 Γ' e
  dsimp only [permS] at h2
  rw [eulerChar_def, ← cuspCount_def]
  linarith

/-- **The genus formula.** The genus `g` of `Γ'`, its numbers `ε₂`, `ε₃` of elliptic points of
periods two and three, and its number `ε∞` of cusps satisfy
`12 g + 3 ε₂ + 4 ε₃ + 6 ε∞ = 12 + n`, where `n` is the index. -/
theorem genus_formula :
    12 * genus Γ' e + 3 * ellipticTwo Γ' e + 4 * ellipticThree Γ' e +
      6 * cuspCount Γ' e = 12 + n := by
  have hg := two_sub_two_mul_genus Γ' e
  have h2 := two_mul_orbitCount_permS Γ' e
  have h3 := three_mul_orbitCount_σ0 Γ' e
  rw [eulerChar_def] at hg
  rw [permS] at h2
  rw [cuspCount_def, permT]
  omega

/-- For a torsion-free subgroup (`e₂ = e₃ = 0`), the genus formula is `12 g + 6 c = 12 + n`. -/
theorem genus_formula_of_elliptic_eq_zero {Γ' : Subgroup PSL(2, ℤ)} (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (h2 : ellipticTwo Γ' e = 0) (h3 : ellipticThree Γ' e = 0) :
    12 * genus Γ' e + 6 * cuspCount Γ' e = 12 + n := by
  have := genus_formula Γ' e
  omega

/-- A subgroup has genus `0` if and only if `3 e₂ + 4 e₃ + 6 c = 12 + n`. -/
theorem genus_eq_zero_iff :
    genus Γ' e = 0 ↔
      3 * ellipticTwo Γ' e + 4 * ellipticThree Γ' e + 6 * cuspCount Γ' e = 12 + n := by
  have := genus_formula Γ' e
  omega

/-- Without elliptic points, as for a torsion-free `Γ'`, the index is divisible by `6`. -/
theorem six_dvd_of_ellipticTwo_eq_zero_of_ellipticThree_eq_zero (h2 : ellipticTwo Γ' e = 0)
    (h3 : ellipticThree Γ' e = 0) : 6 ∣ n := by
  have := genus_formula Γ' e
  omega

/-- Every finite-index subgroup of `PSL(2, ℤ)` with positive genus has index at least `6`. -/
theorem six_le_of_genus_pos {Γ' : Subgroup PSL(2, ℤ)} {e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n}
    (hg : 0 < genus Γ' e) : 6 ≤ n := by
  have hf := genus_formula Γ' e
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
noncomputable def invariants : Invariants where
  index := n
  genus := genus Γ' e
  ellipticTwo := ellipticTwo Γ' e
  ellipticThree := ellipticThree Γ' e
  cuspWidths := cuspWidths Γ' e

/-- The index field of `invariants Γ' e` is `n`. -/
@[simp] theorem invariants_index : (invariants Γ' e).index = n := (rfl)

/-- The genus field of `invariants Γ' e` is `genus Γ' e`. -/
@[simp] theorem invariants_genus : (invariants Γ' e).genus = genus Γ' e := (rfl)

/-- The order-`2` elliptic count field of `invariants Γ' e` is `ellipticTwo Γ' e`. -/
@[simp] theorem invariants_ellipticTwo :
    (invariants Γ' e).ellipticTwo = ellipticTwo Γ' e := (rfl)

/-- The order-`3` elliptic count field of `invariants Γ' e` is `ellipticThree Γ' e`. -/
@[simp] theorem invariants_ellipticThree :
    (invariants Γ' e).ellipticThree = ellipticThree Γ' e := (rfl)

/-- The cusp-width multiset field of `invariants Γ' e` is `cuspWidths Γ' e`. -/
@[simp] theorem invariants_cuspWidths : (invariants Γ' e).cuspWidths = cuspWidths Γ' e := (rfl)

/-- The cusp count of `invariants Γ' e` is `cuspCount Γ' e`. -/
@[simp] theorem invariants_cuspCount : (invariants Γ' e).cuspCount = cuspCount Γ' e :=
  card_cuspWidths Γ' e

/-- Equivalent modular triples have identical invariant vectors. -/
theorem invariants_eq_of_equivalent {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : (modularTriple Γ₁ e₁).Equivalent (modularTriple Γ₂ e₂)) :
    invariants Γ₁ e₁ = invariants Γ₂ e₂ :=
  Invariants.ext rfl (genus_eq_of_equivalent h) (ellipticTwo_eq_of_equivalent h)
    (ellipticThree_eq_of_equivalent h) (cuspWidths_eq_of_equivalent h)

/-- The invariant vector does not depend on the coset enumeration. -/
theorem invariants_congr (e₁ e₂ : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    invariants Γ' e₁ = invariants Γ' e₂ :=
  invariants_eq_of_equivalent (equivalent_modularTriple Γ' e₁ e₂)

/-- Conjugate subgroups of `PSL(2, ℤ)` have identical invariant vectors. -/
theorem invariants_eq_of_conj {Γ₁ Γ₂ : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁ ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂ ≃ Fin n}
    (h : ∃ g : ConjAct PSL(2, ℤ), g • Γ₁ = Γ₂) :
    invariants Γ₁ e₁ = invariants Γ₂ e₂ :=
  invariants_eq_of_equivalent ((millington e₁ e₂).mpr h)

/-- The mirror subgroup `Γ'.map conjJAut` has the same invariant vector as `Γ'`. -/
theorem invariants_map_conjJAut
    (e' : PSL(2, ℤ) ⧸ Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ)) ≃ Fin n) :
    invariants (Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))) e' = invariants Γ' e :=
  Invariants.ext rfl (genus_map_conjJAut Γ' e e') (ellipticTwo_map_conjJAut Γ' e e')
    (ellipticThree_map_conjJAut Γ' e e') (cuspWidths_map_conjJAut Γ' e e')

/-- The full modular group `⊤` has invariant vector `(1, 0, 1, 1, {1})`. -/
@[simp] theorem invariants_top (eTop : PSL(2, ℤ) ⧸ (⊤ : Subgroup PSL(2, ℤ)) ≃ Fin 1) :
    invariants ⊤ eTop = ⟨1, 0, 1, 1, {1}⟩ := by ext1 <;> simp

/-! ### Opposite (right-coset / LMFDB) convention -/

/-- The right-coset permutation of `S` squares to `1`. -/
theorem rightCosetPerm_S_sq (r : Quotient (QuotientGroup.rightRel Γ') ≃ Fin n) :
    (r.permCongr (Γ'.rightCosetPerm (S : PSL(2, ℤ)))) ^ 2 = 1 := by
  rw [sq, ← r.permCongr_mul, ← Γ'.rightCosetPerm_mul, ← sq, coe_S_sq, Γ'.rightCosetPerm_one]
  exact Equiv.ext fun _ ↦ by simp

/-- Under the opposite (right-coset) convention, `cuspWidths` agrees with the full cycle type of
the right-coset permutation of `T`. -/
theorem cuspWidths_quotientRightRel (r : Quotient (QuotientGroup.rightRel Γ') ≃ Fin n) :
    cuspWidths Γ' ((QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ').symm.trans r) =
      (r.permCongr (Γ'.rightCosetPerm (T : PSL(2, ℤ)))).fullCycleType := by
  rw [cuspWidths_def, permT, (modularTriple_quotientRightRel Γ' r).2.2.2.1, fullCycleType_inv]

/-- Under the opposite convention, `cuspCount` equals the orbit count of the right-coset
permutation of `T`. -/
theorem cuspCount_quotientRightRel (r : Quotient (QuotientGroup.rightRel Γ') ≃ Fin n) :
    cuspCount Γ' ((QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ').symm.trans r) =
      orbitCount (r.permCongr (Γ'.rightCosetPerm (T : PSL(2, ℤ)))) := by
  rw [cuspCount_def, permT, (modularTriple_quotientRightRel Γ' r).2.2.2.1, orbitCount_inv]

/-- Under the opposite convention, `ellipticTwo` counts the fixed points of the right-coset
permutation of `S`. -/
theorem ellipticTwo_quotientRightRel (r : Quotient (QuotientGroup.rightRel Γ') ≃ Fin n) :
    ellipticTwo Γ' ((QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ').symm.trans r) =
      Fintype.card {x : Fin n // r.permCongr (Γ'.rightCosetPerm (S : PSL(2, ℤ))) x = x} := by
  rw [ellipticTwo_def, ← Fintype.card_subtype, permS,
    (modularTriple_quotientRightRel Γ' r).2.2.1]

/-- Under the opposite convention, `ellipticThree` counts the fixed points of the right-coset
permutation of `R = S T`. -/
theorem ellipticThree_quotientRightRel (r : Quotient (QuotientGroup.rightRel Γ') ≃ Fin n) :
    ellipticThree Γ' ((QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ').symm.trans r) =
      Fintype.card {x : Fin n // r.permCongr (Γ'.rightCosetPerm (R : PSL(2, ℤ))) x = x} := by
  rw [ellipticThree_eq_card_fixed_permR, (modularTriple_quotientRightRel Γ' r).2.2.2.2,
    card_subtype_apply_eq, support_inv, ← card_subtype_apply_eq]

/-- Under the opposite convention, `genus` agrees with the genus of `ofRightCosetPerms`. -/
theorem genus_quotientRightRel (r : Quotient (QuotientGroup.rightRel Γ') ≃ Fin n) :
    genus Γ' ((QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ').symm.trans r) =
      (ofRightCosetPerms
        (r.permCongr (Γ'.rightCosetPerm (S : PSL(2, ℤ))))
        (r.permCongr (Γ'.rightCosetPerm (T : PSL(2, ℤ))))
        (rightCosetPerm_S_sq Γ' r)).genus := by
  rw [genus_def, modularTriple_quotientRightRel_eq_ofRightCosetPerms]

/-- **Packaged invariant vector from right-coset permutations.** Under the opposite convention
`g Γ' ↦ Γ' g⁻¹`, the invariant vector `invariants` is read directly off the right-coset
permutations of `S`, `T`, and `R = S T`. -/
theorem invariants_quotientRightRel (r : Quotient (QuotientGroup.rightRel Γ') ≃ Fin n) :
    invariants Γ' ((QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ').symm.trans r) =
      let sRow := r.permCongr (Γ'.rightCosetPerm (S : PSL(2, ℤ)))
      let tRow := r.permCongr (Γ'.rightCosetPerm (T : PSL(2, ℤ)))
      { index := n
        genus := (ofRightCosetPerms sRow tRow (rightCosetPerm_S_sq Γ' r)).genus
        ellipticTwo := Fintype.card {x : Fin n // sRow x = x}
        ellipticThree :=
          Fintype.card {x : Fin n // r.permCongr (Γ'.rightCosetPerm (R : PSL(2, ℤ))) x = x}
        cuspWidths := tRow.fullCycleType } :=
  Invariants.ext rfl (genus_quotientRightRel Γ' r) (ellipticTwo_quotientRightRel Γ' r)
    (ellipticThree_quotientRightRel Γ' r) (cuspWidths_quotientRightRel Γ' r)

end TauCeti.ModularGroup
