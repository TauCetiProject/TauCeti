/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import TauCeti.Analysis.Normed.Ring.Ultra

/-!
# A fundamental annulus for the quotient by powers of a contracting unit

If `q` is a unit of a normed field with `‖q‖ < 1`, every multiplicative coset modulo
`Subgroup.zpowers q` has exactly one representative in `‖q‖ < ‖u‖ ≤ 1`.
`exists_mk_eq_and_norm_mem_Ioc` states the existence of such a representative, and
`unitsQuotientZPowersEquivAnnulus` gives the resulting set-level equivalence. The half-open
annulus is essential: replacing the upper weak inequality by a strict inequality loses every
coset whose representatives have norms in `‖q‖^ℤ`.

The proof uses Mathlib's Archimedean fundamental-interval theorem
`existsUnique_sub_zpow_mem_Ioc` on positive norms. Neither completeness, nontriviality of the
norm nor discreteness of the value group is required. This is the multiplicative parameter
normalisation used for Tate uniformisation.

A nonzero integer power of an element of norm less than one has norm different from one; in
particular `1 - qᵏ ≠ 0`. Neither a unit of norm one other than `1`, nor a unit in the open annulus
`‖q‖ < ‖u‖ < 1`, nor a square root of `q` is a power of `q`.

Over an ultrametric field the quotient `Kˣ ⧸ q^ℤ` has infinitely many squares
(`infinite_range_sq_quotient_zpowers`), as the classes of the norm-one units `1 - qᵏ` show. This
is the room needed to move a triple of points of the Tate curve into general position.
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
theorem eq_of_norm_mem_Ioc_of_quotient_zpowers_eq (q : Kˣ)
    {u v : Kˣ} (hu : ‖(q : K)‖ < ‖(u : K)‖ ∧ ‖(u : K)‖ ≤ 1)
    (hv : ‖(q : K)‖ < ‖(v : K)‖ ∧ ‖(v : K)‖ ≤ 1)
    (huv : (u : Kˣ ⧸ Subgroup.zpowers q) = (v : Kˣ ⧸ Subgroup.zpowers q)) : u = v := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (QuotientGroup.eq_iff_div_mem.mp huv)
  have hnu : q ^ n * v = u := by
    rw [hn, div_mul_cancel]
  obtain ⟨m, hm, hm_unique⟩ :=
    existsUnique_norm_zpow_mul_mem_Ioc q v (hu.1.trans_le hu.2)
  have hn0 : n = 0 := (hm_unique n (by simpa [hnu] using hu)).trans
    (hm_unique 0 (by simpa using hv)).symm
  simpa [hn0] using hnu.symm

/-- A unit in the open annulus `‖q‖ < ‖u‖ < 1` is not a power of `q`. -/
theorem notMem_zpowers_of_norm_lt_of_norm_lt_one {q u : Kˣ} (hqu : ‖(q : K)‖ < ‖(u : K)‖)
    (hu : ‖(u : K)‖ < 1) : u ∉ Subgroup.zpowers q := by
  intro hmem
  have hq := hqu.trans hu
  have h := eq_of_norm_mem_Ioc_of_quotient_zpowers_eq q (v := 1) ⟨hqu, hu.le⟩
    (by simpa using hq) (by rw [(QuotientGroup.eq_one_iff u).mpr hmem, QuotientGroup.mk_one])
  simp [h] at hu

/-- A nonzero power of an element of norm less than one does not have norm one. -/
theorem norm_zpow_ne_one {q : K} (hq : ‖q‖ < 1) {k : ℤ} (hk : k ≠ 0) : ‖q ^ k‖ ≠ 1 := by
  rw [norm_zpow, Ne, zpow_eq_one_iff_right₀ (norm_nonneg _) hq.ne]
  exact hk

/-- A nonzero power of an element of norm less than one is not one. -/
theorem one_sub_zpow_ne_zero {q : K} (hq : ‖q‖ < 1) {k : ℤ} (hk : k ≠ 0) : 1 - q ^ k ≠ 0 := by
  intro h
  apply norm_zpow_ne_one hq hk
  rw [← sub_eq_zero.mp h, norm_one]

/-- A unit of norm one other than `1` is not a power of a unit `q` with `‖q‖ < 1`. -/
theorem notMem_zpowers_of_norm_eq_one {q u : Kˣ} (hq : ‖(q : K)‖ < 1) (hu : ‖(u : K)‖ = 1)
    (hu₁ : u ≠ 1) : u ∉ Subgroup.zpowers q := by
  rintro ⟨n, rfl⟩
  have hq₀ : 0 < ‖(q : K)‖ := norm_pos_iff.mpr q.ne_zero
  rw [Units.val_zpow_eq_zpow_val, norm_zpow, zpow_eq_one_iff_right₀ hq₀.le hq.ne] at hu
  exact hu₁ (by simp [hu])

/-- A square root of a unit `q` with `‖q‖ < 1` is not a power of `q`. -/
theorem notMem_zpowers_of_sq_eq {q s : Kˣ} (hq : ‖(q : K)‖ < 1) (hs : s ^ 2 = q) :
    s ∉ Subgroup.zpowers q := by
  rintro ⟨n, rfl⟩
  have h : q ^ (2 * n - 1) = 1 := by
    rw [zpow_sub_one, two_mul, zpow_add, ← sq, hs, mul_inv_cancel]
  refine norm_zpow_ne_one hq (show 2 * n - 1 ≠ 0 by omega) ?_
  rw [← Units.val_zpow_eq_zpow_val, h, Units.val_one, norm_one]

/-- The quotient of the units by the powers of `q`, identified with its unique representatives
in `‖q‖ < ‖u‖ ≤ 1`. This is an equivalence of sets, not of topological spaces or groups. -/
noncomputable def unitsQuotientZPowersEquivAnnulus (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    (Kˣ ⧸ Subgroup.zpowers q) ≃
      {u : Kˣ // ‖(q : K)‖ < ‖(u : K)‖ ∧ ‖(u : K)‖ ≤ 1} :=
  (Equiv.ofBijective (fun u : {u : Kˣ // ‖(q : K)‖ < ‖(u : K)‖ ∧ ‖(u : K)‖ ≤ 1} ↦
    (u.val : Kˣ ⧸ Subgroup.zpowers q)) ⟨by
      intro u v h
      exact Subtype.ext (eq_of_norm_mem_Ioc_of_quotient_zpowers_eq q u.prop v.prop h), by
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

/-- Every class in `Kˣ ⧸ q^ℤ` has a representative in the fundamental annulus. -/
theorem exists_mk_eq_and_norm_mem_Ioc (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Kˣ ⧸ Subgroup.zpowers q) :
    ∃ r : Kˣ, (r : Kˣ ⧸ Subgroup.zpowers q) = x ∧ ‖(q : K)‖ < ‖(r : K)‖ ∧ ‖(r : K)‖ ≤ 1 :=
  ⟨_, mk_unitsQuotientZPowersEquivAnnulus q hq x, (unitsQuotientZPowersEquivAnnulus q hq x).prop⟩

/-- A representative already in the fundamental annulus is unchanged by normalisation. -/
@[simp]
theorem unitsQuotientZPowersEquivAnnulus_apply_mk (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (u : Kˣ) (hu : ‖(q : K)‖ < ‖(u : K)‖ ∧ ‖(u : K)‖ ≤ 1) :
    unitsQuotientZPowersEquivAnnulus q hq (u : Kˣ ⧸ Subgroup.zpowers q) = ⟨u, hu⟩ :=
  (unitsQuotientZPowersEquivAnnulus q hq).apply_symm_apply ⟨u, hu⟩

/-- Over an ultrametric field, the quotient `Kˣ ⧸ q^ℤ` by the powers of a unit with `‖q‖ < 1` has
infinitely many squares. -/
theorem infinite_range_sq_quotient_zpowers [IsUltrametricDist K] (q : Kˣ)
    (hq : ‖(q : K)‖ < 1) : (Set.range fun x : Kˣ ⧸ Subgroup.zpowers q ↦ x ^ 2).Infinite := by
  -- The units `u k = 1 - qᵏ⁺¹` have norm one, so their classes and those of their squares are
  -- represented in the fundamental annulus.
  have hq₀ : 0 < ‖(q : K)‖ := norm_pos_iff.mpr q.ne_zero
  have hpow (k : ℕ) : ‖(q : K) ^ (k + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ hq₀.le hq k.succ_ne_zero
  have hnorm (k : ℕ) : ‖1 - (q : K) ^ (k + 1)‖ = 1 := norm_one_sub_of_norm_lt_one (hpow k)
  let u (k : ℕ) : Kˣ := Units.mk0 (1 - (q : K) ^ (k + 1)) (norm_ne_zero_iff.mp (by simp [hnorm]))
  have hu : Function.Injective u := fun j k h ↦ by
    have h' : ‖(q : K)‖ ^ (j + 1) = ‖(q : K)‖ ^ (k + 1) := by
      rw [← norm_pow, ← norm_pow, sub_right_injective (congrArg Units.val h)]
    exact Nat.succ_injective (pow_right_injective₀ hq₀ hq.ne h')
  have hmem (k : ℕ) : ‖(q : K)‖ < ‖((u k ^ 2 : Kˣ) : K)‖ ∧ ‖((u k ^ 2 : Kˣ) : K)‖ ≤ 1 := by
    simp [u, hnorm, hq]
  refine Set.Infinite.mono (Set.range_comp_subset_range (fun k ↦ (u k : Kˣ ⧸ Subgroup.zpowers q))
    (· ^ 2)) fun hfin ↦ Set.infinite_univ (α := ℕ) ?_
  refine (hfin.preimage' fun y ⟨j, hj⟩ ↦ ?_).subset fun k _ ↦ Set.mem_range_self k
  subst hj
  -- The squares of `u k` and `u j` agree, so `u k = ± u j`.
  refine ((Set.toFinite {u j, -u j}).preimage hu.injOn).subset fun k hk ↦ ?_
  have h : u k ^ 2 = u j ^ 2 := eq_of_norm_mem_Ioc_of_quotient_zpowers_eq q (hmem k) (hmem j)
    (by simpa only [QuotientGroup.mk_pow, Set.mem_preimage, Set.mem_singleton_iff,
      Function.comp_apply] using hk)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (congrArg Units.val h) with h' | h'
  · exact Or.inl (Units.ext h')
  · exact Or.inr (Units.ext h')

end TauCeti
