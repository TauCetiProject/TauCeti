/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
public import TauCeti.RingTheory.PowerSeries.Dvd

/-!
# Weierstrass preparation with a uniformiser power over a discrete valuation ring

Let `O` be a discrete valuation ring with normalised additive valuation `v = addVal O`, and let
`f = ∑ aₙ Xⁿ` be a power series over `O`. Its *μ-invariant* is the least valuation of a
coefficient,

```text
μ(f) = min_n v(aₙ),
```

which is `⊤` exactly for `f = 0`, and its *λ-invariant* is the first index attaining it,

```text
λ(f) = min {n | v(aₙ) = μ(f)}.
```

Dividing out `π ^ μ(f)` for a uniformiser `π` leaves a series with a unit coefficient, whose
image in `k⟦X⟧` over the residue field `k` is nonzero of order `λ(f)`. When `O` is complete for
its maximal ideal, Mathlib's Weierstrass preparation theorem applies to that series, giving the
factorisation

```text
f = C (π ^ μ(f)) * u * P,    u a unit of O⟦X⟧,    P distinguished of degree λ(f),
```

which underlies the structure theory of the Iwasawa algebra `O⟦T⟧`. The exponent, the unit and the
polynomial are unique. No finiteness of the residue field is needed, and `O` need not be the
valuation ring of a normed field; the valuation ring of a complete discretely valued field is the
special case `O = Valuation.integer v`.

Both invariants are additive on products of nonzero series: after dividing out the uniformiser
powers, this is additivity of the order on the domain `k⟦X⟧`.

## Main definitions

* `PowerSeries.muInvariant`: `μ(f) = ⨅ n, addVal O (coeff n f)`, in `ℕ∞`.
* `PowerSeries.lambdaInvariant`: the least `n` with `addVal O (coeff n f) = μ(f)`.

## Main results

* `PowerSeries.C_dvd_iff_addVal_le_muInvariant`: `C a ∣ f ↔ v(a) ≤ μ(f)`; in particular
  `PowerSeries.C_pow_dvd_iff_le_muInvariant`: `C (π ^ k) ∣ f ↔ k ≤ μ(f)` for a uniformiser `π`.
* `PowerSeries.order_map_residue_eq_lambdaInvariant`: if `μ(f) = 0`, the reduction of `f` modulo
  the maximal ideal has order `λ(f)`.
* `PowerSeries.exists_pow_mul_distinguished_mul_unit`: Weierstrass preparation with a uniformiser
  power, with exponent `μ(f)` and polynomial degree `λ(f)`.
* `PowerSeries.C_pow_mul_unit_mul_inj`: uniqueness of the exponent, the unit and the distinguished
  polynomial.
* `PowerSeries.muInvariant_mul`, `PowerSeries.lambdaInvariant_mul`: additivity on products.

## References

* L. Washington, *Introduction to Cyclotomic Fields*, second edition, GTM 83, §7.1,
  Theorem 7.3 and the discussion of `μ` and `λ` following it.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, second edition,
  (5.3.1)–(5.3.4).
-/

public section

namespace PowerSeries

open IsDiscreteValuationRing IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The *μ-invariant* of a power series over a discrete valuation ring: the least normalised
valuation of a coefficient. It is `⊤` exactly for the zero series. -/
noncomputable def muInvariant (f : O⟦X⟧) : ℕ∞ :=
  ⨅ n, addVal O (coeff n f)

/-- The *λ-invariant* of a power series over a discrete valuation ring: the least index of a
coefficient whose valuation is the μ-invariant. It is `0` for the zero series. -/
noncomputable def lambdaInvariant (f : O⟦X⟧) : ℕ :=
  sInf {n | addVal O (coeff n f) = f.muInvariant}

theorem muInvariant_def (f : O⟦X⟧) : f.muInvariant = ⨅ n, addVal O (coeff n f) := (rfl)

theorem lambdaInvariant_def (f : O⟦X⟧) :
    f.lambdaInvariant = sInf {n | addVal O (coeff n f) = f.muInvariant} := (rfl)

theorem muInvariant_le_addVal_coeff (f : O⟦X⟧) (n : ℕ) : f.muInvariant ≤ addVal O (coeff n f) :=
  iInf_le _ n

theorem le_muInvariant_iff {f : O⟦X⟧} {k : ℕ∞} :
    k ≤ f.muInvariant ↔ ∀ n, k ≤ addVal O (coeff n f) :=
  le_iInf_iff

@[simp]
theorem muInvariant_eq_top_iff {f : O⟦X⟧} : f.muInvariant = ⊤ ↔ f = 0 := by
  simp only [muInvariant_def, iInf_eq_top, addVal_eq_top_iff]
  exact ⟨fun h ↦ ext fun n ↦ by rw [h, map_zero], fun h n ↦ by rw [h, map_zero]⟩

@[simp]
theorem muInvariant_zero : (0 : O⟦X⟧).muInvariant = ⊤ :=
  muInvariant_eq_top_iff.2 rfl

/-- The μ-invariant is attained, in degree `λ(f)`. -/
theorem addVal_coeff_lambdaInvariant (f : O⟦X⟧) :
    addVal O (coeff f.lambdaInvariant f) = f.muInvariant := by
  obtain ⟨n, hn⟩ := ciInf_mem fun n ↦ addVal O (coeff n f)
  exact Nat.sInf_mem (s := {n | addVal O (coeff n f) = f.muInvariant}) ⟨n, hn⟩

theorem lambdaInvariant_le {f : O⟦X⟧} {n : ℕ} (h : addVal O (coeff n f) = f.muInvariant) :
    f.lambdaInvariant ≤ n :=
  Nat.sInf_le h

/-- Every coefficient before degree `λ(f)` has valuation strictly larger than `μ(f)`. -/
theorem muInvariant_lt_addVal_coeff {f : O⟦X⟧} {n : ℕ} (h : n < f.lambdaInvariant) :
    f.muInvariant < addVal O (coeff n f) :=
  (f.muInvariant_le_addVal_coeff n).lt_of_ne fun h' ↦ Nat.notMem_of_lt_sInf h h'.symm

/-- `λ(f)` is the index of the first coefficient whose valuation is `μ(f)`. -/
theorem lambdaInvariant_eq_iff {f : O⟦X⟧} {n : ℕ} :
    f.lambdaInvariant = n ↔
      addVal O (coeff n f) = f.muInvariant ∧ ∀ i < n, f.muInvariant < addVal O (coeff i f) := by
  refine ⟨?_, fun ⟨hn, hlt⟩ ↦ (lambdaInvariant_le hn).antisymm (not_lt.1 fun h ↦ ?_)⟩
  · rintro rfl
    exact ⟨f.addVal_coeff_lambdaInvariant, fun i hi ↦ muInvariant_lt_addVal_coeff hi⟩
  · exact (hlt _ h).ne' f.addVal_coeff_lambdaInvariant

theorem muInvariant_C_mul (a : O) (f : O⟦X⟧) :
    (C a * f).muInvariant = addVal O a + f.muInvariant := by
  simp only [muInvariant_def, coeff_C_mul, addVal_mul, ENat.add_iInf]

@[simp]
theorem lambdaInvariant_C_mul {a : O} (ha : a ≠ 0) (f : O⟦X⟧) :
    (C a * f).lambdaInvariant = f.lambdaInvariant := by
  have hv : addVal O a ≠ ⊤ := addVal_eq_top_iff.not.2 ha
  rw [lambdaInvariant_def, lambdaInvariant_def, muInvariant_C_mul]
  congr 1
  ext n
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, coeff_C_mul, addVal_mul]
  exact (ENat.add_right_injective_of_ne_top hv).eq_iff

@[simp]
theorem muInvariant_C (a : O) : (C a).muInvariant = addVal O a := by
  refine le_antisymm (by simpa using (C a).muInvariant_le_addVal_coeff 0)
    (le_muInvariant_iff.2 fun n ↦ ?_)
  rw [coeff_C]
  split_ifs <;> simp

@[simp]
theorem lambdaInvariant_C (a : O) : (C a).lambdaInvariant = 0 :=
  lambdaInvariant_eq_iff.2
    ⟨by rw [coeff_zero_C, muInvariant_C], fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩

@[simp]
theorem lambdaInvariant_zero : (0 : O⟦X⟧).lambdaInvariant = 0 := by
  simpa using lambdaInvariant_C (0 : O)

/-- The μ-invariant vanishes exactly when the reduction modulo the maximal ideal is nonzero. -/
theorem muInvariant_eq_zero_iff {f : O⟦X⟧} : f.muInvariant = 0 ↔ f.map (residue O) ≠ 0 := by
  have : f.muInvariant = 0 ↔ ∃ n, addVal O (coeff n f) = 0 :=
    ⟨fun h ↦ ⟨_, f.addVal_coeff_lambdaInvariant.trans h⟩,
      fun ⟨n, hn⟩ ↦ nonpos_iff_eq_zero.1 (hn ▸ f.muInvariant_le_addVal_coeff n)⟩
  simp [this, PowerSeries.ext_iff, addVal_eq_zero_iff]

/-- A unit has μ-invariant zero. -/
@[simp]
theorem muInvariant_eq_zero_of_isUnit {f : O⟦X⟧} (hf : IsUnit f) : f.muInvariant = 0 :=
  muInvariant_eq_zero_iff.2 (hf.map (map (residue O))).ne_zero

/-- A unit has λ-invariant zero. -/
@[simp]
theorem lambdaInvariant_eq_zero_of_isUnit {f : O⟦X⟧} (hf : IsUnit f) : f.lambdaInvariant = 0 := by
  refine lambdaInvariant_eq_iff.2 ⟨?_, fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩
  rw [muInvariant_eq_zero_of_isUnit hf, addVal_eq_zero_iff, coeff_zero_eq_constantCoeff_apply]
  exact isUnit_iff_constantCoeff.1 hf

/-- If `μ(f) = 0`, the reduction of `f` modulo the maximal ideal has order `λ(f)`. -/
theorem order_map_residue_eq_lambdaInvariant {f : O⟦X⟧} (hf : f.muInvariant = 0) :
    (f.map (residue O)).order = f.lambdaInvariant := by
  refine order_eq_nat.2 ⟨?_, fun i hi ↦ ?_⟩
  · rw [coeff_map, residue_ne_zero_iff_isUnit, ← addVal_eq_zero_iff,
      addVal_coeff_lambdaInvariant, hf]
  · rw [coeff_map, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
      ← addVal_eq_zero_iff]
    exact (hf ▸ muInvariant_lt_addVal_coeff hi).ne'

/-- The constant `a` divides `f` exactly when `v(a) ≤ μ(f)`. -/
theorem C_dvd_iff_addVal_le_muInvariant (a : O) {f : O⟦X⟧} :
    C a ∣ f ↔ addVal O a ≤ f.muInvariant := by
  simp only [C_dvd_iff_dvd_coeff, le_muInvariant_iff, ← addVal_le_iff_dvd]

/-- For a uniformiser `π`, the constant `π ^ k` divides `f` exactly when `k ≤ μ(f)`. -/
theorem C_pow_dvd_iff_le_muInvariant {π : O} (hπ : Irreducible π) {f : O⟦X⟧} {k : ℕ} :
    C (π ^ k) ∣ f ↔ (k : ℕ∞) ≤ f.muInvariant := by
  rw [C_dvd_iff_addVal_le_muInvariant, hπ.addVal_pow]

/-- A nonzero power series is `π ^ μ(f)` times a series of μ-invariant zero. -/
theorem exists_eq_C_pow_mul {π : O} (hπ : Irreducible π) {f : O⟦X⟧} (hf : f ≠ 0) :
    ∃ (m : ℕ) (g : O⟦X⟧), f.muInvariant = m ∧ g.muInvariant = 0 ∧ f = C (π ^ m) * g := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (muInvariant_eq_top_iff.not.2 hf)
  obtain ⟨g, rfl⟩ := (C_pow_dvd_iff_le_muInvariant hπ).2 hm.le
  refine ⟨m, g, hm.symm, ?_, rfl⟩
  rw [muInvariant_C_mul, hπ.addVal_pow] at hm
  exact ENat.add_right_injective_of_ne_top (ENat.natCast_ne_top m) (hm.symm.trans (add_zero _).symm)

namespace IsWeierstrassFactorization

variable {g : O⟦X⟧} {P : Polynomial O} {h : O⟦X⟧}

/-- A series admitting a Weierstrass factorisation has μ-invariant zero. -/
theorem muInvariant_eq_zero (H : g.IsWeierstrassFactorization P h) : g.muInvariant = 0 :=
  muInvariant_eq_zero_iff.2 H.map_ne_zero

/-- The distinguished polynomial of a Weierstrass factorisation has degree `λ(g)`. -/
theorem natDegree_eq_lambdaInvariant (H : g.IsWeierstrassFactorization P h) :
    P.natDegree = g.lambdaInvariant := by
  rw [H.natDegree_eq_toNat_order_map,
    order_map_residue_eq_lambdaInvariant H.muInvariant_eq_zero, ENat.toNat_natCast]

end IsWeierstrassFactorization

/-- **Weierstrass preparation with a uniformiser power.** Over a discrete valuation ring complete
for its maximal ideal, a nonzero power series `f` factors as `C (π ^ μ(f)) * u * P` with `u` a
unit and `P` a distinguished polynomial of degree `λ(f)`. -/
theorem exists_pow_mul_distinguished_mul_unit [IsAdicComplete (maximalIdeal O) O]
    {π : O} (hπ : Irreducible π) {f : O⟦X⟧} (hf : f ≠ 0) :
    ∃ (m : ℕ) (P : Polynomial O) (u : O⟦X⟧ˣ), f.muInvariant = m ∧ P.natDegree = f.lambdaInvariant ∧
      P.IsDistinguishedAt (maximalIdeal O) ∧ f = C (π ^ m) * u * P := by
  obtain ⟨m, g, hm, hg, rfl⟩ := exists_eq_C_pow_mul hπ hf
  obtain ⟨P, h, H⟩ := exists_isWeierstrassFactorization (muInvariant_eq_zero_iff.1 hg)
  refine ⟨m, P, H.isUnit.unit, hm, ?_, H.isDistinguishedAt, ?_⟩
  · rw [lambdaInvariant_C_mul (pow_ne_zero _ hπ.ne_zero), H.natDegree_eq_lambdaInvariant]
  · rw [IsUnit.unit_spec, mul_assoc, H.eq_mul, mul_comm (P : O⟦X⟧)]

/-- **Uniqueness in Weierstrass preparation with a uniformiser power.** For a fixed uniformiser
`π`, the exponent, the unit and the distinguished polynomial of a factorisation
`C (π ^ m) * u * P` are determined by the product. -/
theorem C_pow_mul_unit_mul_inj [IsHausdorff (maximalIdeal O) O] {π : O} (hπ : Irreducible π)
    {m m' : ℕ} {u u' : O⟦X⟧ˣ} {P P' : Polynomial O} (hP : P.IsDistinguishedAt (maximalIdeal O))
    (hP' : P'.IsDistinguishedAt (maximalIdeal O)) :
    C (π ^ m) * u * P = C (π ^ m') * u' * P' ↔ m = m' ∧ u = u' ∧ P = P' := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl, rfl⟩; rfl⟩
  have H : (P * u : O⟦X⟧).IsWeierstrassFactorization P u := ⟨hP, u.isUnit, rfl⟩
  have H' : (P' * u' : O⟦X⟧).IsWeierstrassFactorization P' u' := ⟨hP', u'.isUnit, rfl⟩
  rw [mul_assoc, mul_assoc, mul_comm (u : O⟦X⟧), mul_comm (u' : O⟦X⟧)] at h
  obtain rfl : m = m' := by
    have hμ := congrArg muInvariant h
    rw [muInvariant_C_mul, muInvariant_C_mul, H.muInvariant_eq_zero, H'.muInvariant_eq_zero,
      hπ.addVal_pow, hπ.addVal_pow, add_zero, add_zero] at hμ
    exact_mod_cast hμ
  rw [mul_right_inj' ((map_ne_zero_iff C C_injective).2 (pow_ne_zero m hπ.ne_zero))] at h
  obtain ⟨rfl, huu'⟩ := H.elim (by rw [h]; exact H')
  exact ⟨rfl, Units.ext huu', rfl⟩

/-- The μ-invariant is additive on products. -/
@[simp]
theorem muInvariant_mul (f g : O⟦X⟧) : (f * g).muInvariant = f.muInvariant + g.muInvariant := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  obtain ⟨π, hπ⟩ := exists_irreducible O
  obtain ⟨m, f₀, -, hf₀, rfl⟩ := exists_eq_C_pow_mul hπ hf
  obtain ⟨n, g₀, -, hg₀, rfl⟩ := exists_eq_C_pow_mul hπ hg
  have hfg₀ : (f₀ * g₀).muInvariant = 0 := muInvariant_eq_zero_iff.2 <| by
    rw [map_mul]
    exact mul_ne_zero (muInvariant_eq_zero_iff.1 hf₀) (muInvariant_eq_zero_iff.1 hg₀)
  rw [mul_mul_mul_comm, ← map_mul, muInvariant_C_mul, muInvariant_C_mul, muInvariant_C_mul, hf₀,
    hg₀, hfg₀, addVal_mul]
  simp only [add_zero]

/-- The λ-invariant is additive on products of nonzero series. -/
@[simp]
theorem lambdaInvariant_mul {f g : O⟦X⟧} (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g).lambdaInvariant = f.lambdaInvariant + g.lambdaInvariant := by
  obtain ⟨π, hπ⟩ := exists_irreducible O
  obtain ⟨m, f₀, -, hf₀, rfl⟩ := exists_eq_C_pow_mul hπ hf
  obtain ⟨n, g₀, -, hg₀, rfl⟩ := exists_eq_C_pow_mul hπ hg
  have hfg₀ : (f₀ * g₀).muInvariant = 0 := by rw [muInvariant_mul, hf₀, hg₀, add_zero]
  have hπm := pow_ne_zero m hπ.ne_zero
  have hπn := pow_ne_zero n hπ.ne_zero
  rw [mul_mul_mul_comm, ← map_mul, lambdaInvariant_C_mul (mul_ne_zero hπm hπn),
    lambdaInvariant_C_mul hπm, lambdaInvariant_C_mul hπn]
  have key : ((f₀ * g₀).lambdaInvariant : ℕ∞) = f₀.lambdaInvariant + g₀.lambdaInvariant := by
    rw [← order_map_residue_eq_lambdaInvariant hfg₀, ← order_map_residue_eq_lambdaInvariant hf₀,
      ← order_map_residue_eq_lambdaInvariant hg₀, map_mul, order_mul]
  exact_mod_cast key

end PowerSeries
