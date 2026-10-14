/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# A fundamental annulus for the quotient by powers of a contracting unit

If `q` is a unit of a normed field with `‖q‖ < 1`, every multiplicative coset modulo
`Subgroup.zpowers q` has exactly one representative in `‖q‖ < ‖u‖ ≤ 1`.
`unitsQuotientZPowersEquivAnnulus` gives this set-level equivalence. The half-open annulus is
essential: replacing the upper weak inequality by a strict inequality loses every coset
whose representatives have norms in `‖q‖^ℤ`.

The proof uses Mathlib's Archimedean fundamental-interval theorem
`existsUnique_sub_zpow_mem_Ioc` on positive norms. Neither completeness, nontriviality of the
norm nor discreteness of the value group is required. This is the multiplicative parameter
normalisation used for Tate uniformisation.
-/

public section

namespace TauCeti

variable {K : Type*} [NormedField K]

/-- There is a unique power of a contracting unit that moves a given unit into the
half-open fundamental annulus. -/
theorem existsUnique_norm_zpow_mul_mem_Ioc (q u : Kˣ) (hq : ‖(q : K)‖ < 1) :
    ∃! n : ℤ, ‖(q : K)‖ < ‖((q ^ n * u : Kˣ) : K)‖ ∧
      ‖((q ^ n * u : Kˣ) : K)‖ ≤ 1 := by
  let Q : NNRealˣ := Units.map nnnormHom.toMonoidHom q
  let U : NNRealˣ := Units.map nnnormHom.toMonoidHom u
  have hQ : Q < 1 := by
    rw [← Units.val_lt_val, ← NNReal.coe_lt_coe]
    simpa [Q] using hq
  have hnorm (n : ℤ) : (Q < U * Q ^ n ∧ U * Q ^ n ≤ 1) ↔
      ‖(q : K)‖ < ‖((q ^ n * u : Kˣ) : K)‖ ∧
        ‖((q ^ n * u : Kˣ) : K)‖ ≤ 1 := by
    rw [← Units.val_lt_val, ← Units.val_le_val,
      ← NNReal.coe_lt_coe, ← NNReal.coe_le_coe]
    simp [Q, U, norm_mul, norm_zpow, mul_comm]
  have h := existsUnique_sub_zpow_mem_Ioc (inv_lt_inv_iff.mpr hQ) U Q
  simpa only [Set.mem_Ioc, div_eq_mul_inv, inv_zpow, inv_inv, mul_inv_cancel,
    hnorm] using h

/-- Two units in the fundamental annulus representing the same coset modulo `q^ℤ` are equal. -/
theorem eq_of_norm_mem_Ioc_of_quotient_zpowers_eq (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    {u v : Kˣ} (hu : ‖(q : K)‖ < ‖(u : K)‖ ∧ ‖(u : K)‖ ≤ 1)
    (hv : ‖(q : K)‖ < ‖(v : K)‖ ∧ ‖(v : K)‖ ≤ 1)
    (huv : (u : Kˣ ⧸ Subgroup.zpowers q) = (v : Kˣ ⧸ Subgroup.zpowers q)) : u = v := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (QuotientGroup.eq_iff_div_mem.mp huv)
  have hnu : q ^ n * v = u := by
    rw [hn, div_mul_cancel]
  obtain ⟨m, hm, hm_unique⟩ := existsUnique_norm_zpow_mul_mem_Ioc q v hq
  have hn0 : n = 0 := (hm_unique n (by simpa [hnu] using hu)).trans
    (hm_unique 0 (by simpa using hv)).symm
  simpa [hn0] using hnu.symm

/-- The quotient of the units by the powers of `q`, identified with its unique representatives
in `‖q‖ < ‖u‖ ≤ 1`. This is an equivalence of sets, not of topological spaces or groups. -/
noncomputable def unitsQuotientZPowersEquivAnnulus (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    (Kˣ ⧸ Subgroup.zpowers q) ≃
      {u : Kˣ // ‖(q : K)‖ < ‖(u : K)‖ ∧ ‖(u : K)‖ ≤ 1} :=
  (Equiv.ofBijective (fun u : {u : Kˣ // ‖(q : K)‖ < ‖(u : K)‖ ∧ ‖(u : K)‖ ≤ 1} ↦
    (u.val : Kˣ ⧸ Subgroup.zpowers q)) ⟨by
      intro u v h
      exact Subtype.ext (eq_of_norm_mem_Ioc_of_quotient_zpowers_eq q hq u.prop v.prop h), by
      intro x
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨n, hn, _⟩ := existsUnique_norm_zpow_mul_mem_Ioc q u hq
      refine ⟨⟨q ^ n * u, hn⟩, ?_⟩
      dsimp only
      apply QuotientGroup.eq_iff_div_mem.mpr
      simpa only [mul_div_cancel_right] using Subgroup.zpow_mem_zpowers q n⟩).symm

/-- The inverse equivalence is the ordinary quotient projection. -/
@[simp]
theorem unitsQuotientZPowersEquivAnnulus_symm_apply (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (u : {u : Kˣ // ‖(q : K)‖ < ‖(u : K)‖ ∧ ‖(u : K)‖ ≤ 1}) :
    (unitsQuotientZPowersEquivAnnulus q hq).symm u =
      (u.val : Kˣ ⧸ Subgroup.zpowers q) :=
  (rfl)

/-- The normalised representative belongs to the original coset. -/
@[simp]
theorem mk_unitsQuotientZPowersEquivAnnulus (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Kˣ ⧸ Subgroup.zpowers q) :
    ((unitsQuotientZPowersEquivAnnulus q hq x).val : Kˣ ⧸ Subgroup.zpowers q) = x :=
  (unitsQuotientZPowersEquivAnnulus q hq).symm_apply_apply x

/-- A representative already in the fundamental annulus is unchanged by normalisation. -/
@[simp]
theorem unitsQuotientZPowersEquivAnnulus_apply_mk (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (u : Kˣ) (hu : ‖(q : K)‖ < ‖(u : K)‖ ∧ ‖(u : K)‖ ≤ 1) :
    unitsQuotientZPowersEquivAnnulus q hq (u : Kˣ ⧸ Subgroup.zpowers q) = ⟨u, hu⟩ :=
  (unitsQuotientZPowersEquivAnnulus q hq).apply_symm_apply ⟨u, hu⟩

end TauCeti
