/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Every
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Eigenvalues of Coxeter elements and exponents of Dynkin types

For every irreducible crystallographic Dynkin type `t` (`TauCeti.DynkinType.Valid`), the complex
eigenvalues of the matrix of any Coxeter element on the simple roots, counted with multiplicity, are

`exp (2πi e / h)`

as `e` runs over the **exponents** `t.exponents` of `t`, where `h = t.coxeterNumber`:

| type | `h` | exponents `m₁, …, mᵣ` |
|---|---|---|
| `Aₙ` | `n + 1` | `1, 2, …, n` |
| `Bₙ`, `Cₙ` | `2 n` | `1, 3, 5, …, 2 n - 1` |
| `Dₙ` | `2 (n - 1)` | `1, 3, …, 2 n - 3, n - 1` |
| `E₆` | `12` | `1, 4, 5, 7, 8, 11` |
| `E₇` | `18` | `1, 5, 7, 9, 11, 13, 17` |
| `E₈` | `30` | `1, 7, 11, 13, 17, 19, 23, 29` |
| `F₄` | `12` | `1, 5, 7, 11` |
| `G₂` | `6` | `1, 5` |

In even-rank type `D_{2k}`, the exponent `2 k - 1 = n - 1` appears twice, corresponding to the
double eigenvalue `-1` of `(X^{2k - 1} + 1)(X + 1)`. Stating the uniform theorem
`TauCeti.Coxeter.roots_charpoly_of_hasCartanType_of_actsBy` as an equality of multisets records
every multiplicity faithfully across all types.

This file also defines the fundamental invariant degrees `dᵢ = mᵢ + 1`
(`TauCeti.DynkinType.degrees`) and proves the classical identities `2 * ∑ mᵢ = |Φ|`,
`∑ dᵢ = |Φ| / 2 + r`, `0 < mᵢ < h`, and containment of every residue `< h` coprime to `h` among
the exponents.

## Main definitions

* `TauCeti.Coxeter.e6Exponents` (and `e7`, `e8`, `f4`, `g2`): the exponents of the exceptional
  types.
* `TauCeti.DynkinType.exponents`: the list of `r` exponents of any Dynkin type.
* `TauCeti.DynkinType.degrees`: the list of fundamental degrees `mᵢ + 1` of any Dynkin type.

## Main results

* `TauCeti.DynkinType.two_mul_sum_exponents`, `TauCeti.DynkinType.sum_exponents`, and
  `TauCeti.DynkinType.sum_degrees`: `2 * t.exponents.sum = t.numRoots` and
  `t.degrees.sum = t.numRoots / 2 + t.rank`.
* `TauCeti.DynkinType.mem_exponents_of_coprime`: every natural number `< t.coxeterNumber` coprime
  to `t.coxeterNumber` is an exponent of `t`.
* `TauCeti.Coxeter.eigenvalues_of_hasCartanType_E8` (and `E7`, `E6`, `F4`, `G2`): the eigenvalues
  of the matrix of every Coxeter element of an exceptional type on the simple roots, each simple.
* `TauCeti.Coxeter.roots_charpoly_of_hasCartanType_A_of_actsBy` (and `B`, `C`, `D`) and
  `TauCeti.Coxeter.roots_charpoly_of_hasCartanType_of_actsBy`: the complex eigenvalue multiset of
  every Coxeter element of a base of valid Cartan type `t` is `(Multiset.ofList t.exponents).map
  (fun e => exp (2πi e / h))`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Plates I--IX.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.7, 3.16–3.20.
-/

public section

open Matrix Polynomial RootPairing TauCeti

namespace TauCeti.Coxeter

/-- The exponents of `E₆`. -/
@[expose] def e6Exponents : List ℕ := [1, 4, 5, 7, 8, 11]

/-- The exponents of `E₇`. -/
@[expose] def e7Exponents : List ℕ := [1, 5, 7, 9, 11, 13, 17]

/-- The exponents of `E₈`. -/
@[expose] def e8Exponents : List ℕ := [1, 7, 11, 13, 17, 19, 23, 29]

/-- The exponents of `F₄`. -/
@[expose] def f4Exponents : List ℕ := [1, 5, 7, 11]

/-- The exponents of `G₂`. -/
@[expose] def g2Exponents : List ℕ := [1, 5]

/-- The exponents of `E₈` are the residues modulo `30` coprime to `30`. -/
theorem e8Exponents_eq_filter : e8Exponents = (List.range 30).filter (Nat.Coprime · 30) := by
  decide

/-- The exponents of `F₄` are the residues modulo `12` coprime to `12`. -/
theorem f4Exponents_eq_filter : f4Exponents = (List.range 12).filter (Nat.Coprime · 12) := by
  decide

/-- The exponents of `G₂` are the residues modulo `6` coprime to `6`. -/
theorem g2Exponents_eq_filter : g2Exponents = (List.range 6).filter (Nat.Coprime · 6) := by
  decide

end TauCeti.Coxeter

namespace TauCeti.DynkinType

/-- The **exponents** `m₁, …, mᵣ` of a Dynkin type: for a valid Dynkin type, the complex eigenvalues
of every Coxeter element on the root space, counted with multiplicity, are `exp (2πi e / h)` as `e`
runs over `t.exponents` (`TauCeti.Coxeter.roots_charpoly_of_hasCartanType_of_actsBy`). -/
def exponents : DynkinType → List ℕ
  | .A n => (List.range n).map (· + 1)
  | .B n | .C n => (List.range n).map (2 * · + 1)
  | .D n => if n = 0 then [] else (List.range (n - 1)).map (2 * · + 1) ++ [n - 1]
  | .E6 => Coxeter.e6Exponents
  | .E7 => Coxeter.e7Exponents
  | .E8 => Coxeter.e8Exponents
  | .F4 => Coxeter.f4Exponents
  | .G2 => Coxeter.g2Exponents

@[simp] lemma exponents_A (n : ℕ) : (A n).exponents = (List.range n).map (· + 1) := (rfl)
@[simp] lemma exponents_B (n : ℕ) : (B n).exponents = (List.range n).map (2 * · + 1) := (rfl)
@[simp] lemma exponents_C (n : ℕ) : (C n).exponents = (List.range n).map (2 * · + 1) := (rfl)
@[simp] lemma exponents_D_zero : (D 0).exponents = [] := (rfl)
@[simp] lemma exponents_D_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (D n).exponents = (List.range (n - 1)).map (2 * · + 1) ++ [n - 1] := by
  simp [exponents, hn]
@[simp] lemma exponents_E6 : E6.exponents = Coxeter.e6Exponents := (rfl)
@[simp] lemma exponents_E7 : E7.exponents = Coxeter.e7Exponents := (rfl)
@[simp] lemma exponents_E8 : E8.exponents = Coxeter.e8Exponents := (rfl)
@[simp] lemma exponents_F4 : F4.exponents = Coxeter.f4Exponents := (rfl)
@[simp] lemma exponents_G2 : G2.exponents = Coxeter.g2Exponents := (rfl)

/-- The **fundamental invariant degrees** `dᵢ = mᵢ + 1` of a Dynkin type. -/
def degrees (t : DynkinType) : List ℕ :=
  t.exponents.map (· + 1)

/-- Unfolded characterization of `TauCeti.DynkinType.degrees` as `t.exponents.map (· + 1)`. -/
lemma degrees_def (t : DynkinType) : t.degrees = t.exponents.map (· + 1) := (rfl)

/-- Membership in `t.degrees` in terms of `t.exponents`. -/
@[simp] lemma mem_degrees_iff {t : DynkinType} {d : ℕ} :
    d ∈ t.degrees ↔ ∃ e ∈ t.exponents, e + 1 = d := by
  rw [degrees_def, List.mem_map]

@[simp] lemma length_exponents (t : DynkinType) : t.exponents.length = t.rank := by
  cases t with
  | A n | B n | C n => simp
  | D n =>
    rcases eq_or_ne n 0 with rfl | hn
    · rfl
    · simp [exponents, hn]; omega
  | E6 | E7 | E8 | F4 | G2 => rfl

@[simp] lemma length_degrees (t : DynkinType) : t.degrees.length = t.rank := by
  simp [degrees_def]

private lemma sum_map_range_eq_finset_sum (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.coe_range, Finset.sum_eq_multiset_sum,
    Finset.range_val]

/-- **Twice the sum of the exponents of any Dynkin type equals its number of roots**:
`2 ∑ mᵢ = |Φ|`. -/
theorem two_mul_sum_exponents (t : DynkinType) : 2 * t.exponents.sum = t.numRoots := by
  have hodd : ∀ m : ℕ, ∑ k ∈ Finset.range m, (2 * k + 1) = m ^ 2 := fun m => by
    have h2 := Finset.sum_range_id_mul_two m
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      smul_eq_mul, mul_one]
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at h2
      nlinarith
  cases t with
  | A n =>
    have h2 := Finset.sum_range_id_mul_two n
    rw [exponents_A, sum_map_range_eq_finset_sum, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, smul_eq_mul, mul_one, numRoots_A]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at h2
      nlinarith
  | B n | C n =>
    simp only [exponents_B, exponents_C, sum_map_range_eq_finset_sum, hodd, numRoots_B, numRoots_C]
  | D n =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp only [exponents_D_of_ne_zero hn, List.sum_append, sum_map_range_eq_finset_sum, hodd,
        List.sum_singleton, numRoots_D]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
  | E6 | E7 | E8 | F4 | G2 => decide

/-- The sum of the exponents of any Dynkin type is half its number of roots (`|Φ| / 2`, equal to
`|Φ⁺|` for valid types). -/
@[simp] theorem sum_exponents (t : DynkinType) : t.exponents.sum = t.numRoots / 2 := by
  rw [← two_mul_sum_exponents, Nat.mul_div_right _ (by norm_num)]

/-- The sum of the fundamental degrees of any Dynkin type is `|Φ| / 2 + r` (`|Φ⁺| + r` for valid
types). -/
@[simp] theorem sum_degrees (t : DynkinType) : t.degrees.sum = t.numRoots / 2 + t.rank := by
  simp [degrees_def, List.sum_map_add]

/-- Every exponent of a valid Dynkin type is strictly positive. -/
lemma pos_of_mem_exponents {t : DynkinType} (ht : t.Valid) {e : ℕ} (he : e ∈ t.exponents) :
    0 < e := by
  cases t with
  | A n | B n | C n =>
    simp only [exponents_A, exponents_B, exponents_C, List.mem_map, List.mem_range] at he
    obtain ⟨k, _, rfl⟩ := he
    omega
  | D n =>
    have hn : 4 ≤ n := valid_D.mp ht
    rw [exponents_D_of_ne_zero (by omega), List.mem_append, List.mem_map, List.mem_singleton] at he
    rcases he with ⟨k, _, rfl⟩ | rfl <;> omega
  | E6 | E7 | E8 | F4 | G2 =>
    revert e he
    decide

/-- Every exponent of a valid Dynkin type is strictly less than its Coxeter number. -/
lemma lt_coxeterNumber_of_mem_exponents {t : DynkinType} (ht : t.Valid) {e : ℕ}
    (he : e ∈ t.exponents) : e < t.coxeterNumber := by
  cases t with
  | A n | B n | C n =>
    simp only [exponents_A, exponents_B, exponents_C, coxeterNumber_A, coxeterNumber_B,
      coxeterNumber_C, List.mem_map, List.mem_range] at he ⊢
    obtain ⟨k, hk, rfl⟩ := he
    omega
  | D n =>
    have hn : 4 ≤ n := valid_D.mp ht
    rw [exponents_D_of_ne_zero (by omega), List.mem_append, List.mem_map, List.mem_singleton] at he
    simp only [coxeterNumber_D]
    rcases he with ⟨k, hk, rfl⟩ | rfl
    · rw [List.mem_range] at hk; omega
    · omega
  | E6 | E7 | E8 | F4 | G2 =>
    simp only [coxeterNumber_E6, coxeterNumber_E7, coxeterNumber_E8, coxeterNumber_F4,
      coxeterNumber_G2]
    revert e he
    decide

private lemma mod_two_eq_one_of_coprime_two_mul {e k : ℕ} (h : e.Coprime (2 * k)) : e % 2 = 1 := by
  have hcop2 : e.Coprime 2 := h.coprime_mul_right_right
  rcases Nat.mod_two_eq_zero_or_one e with h0 | h1
  · exfalso
    have hdvd : 2 ∣ Nat.gcd e 2 := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h0) dvd_rfl
    rw [hcop2.gcd_eq_one] at hdvd
    omega
  · exact h1

/-- **Every residue `< h` coprime to the Coxeter number `h` is an exponent of `t`.** -/
theorem mem_exponents_of_coprime {t : DynkinType} (ht : t.Valid) {e : ℕ}
    (he : e < t.coxeterNumber) (hcop : e.Coprime t.coxeterNumber) : e ∈ t.exponents := by
  cases t with
  | A n =>
    have hn : 1 ≤ n := valid_A.mp ht
    simp only [coxeterNumber_A] at he hcop
    have he0 : e ≠ 0 := fun h0 => by rw [h0, Nat.coprime_zero_left] at hcop; omega
    simp only [exponents_A, List.mem_map, List.mem_range]
    exact ⟨e - 1, by omega, by omega⟩
  | B n | C n =>
    simp only [coxeterNumber_B, coxeterNumber_C] at he hcop
    have hmod := mod_two_eq_one_of_coprime_two_mul hcop
    simp only [exponents_B, exponents_C, List.mem_map, List.mem_range]
    exact ⟨e / 2, by omega, by omega⟩
  | D n =>
    have hn : 4 ≤ n := valid_D.mp ht
    simp only [coxeterNumber_D] at he hcop
    have hmod := mod_two_eq_one_of_coprime_two_mul hcop
    rw [exponents_D_of_ne_zero (by omega), List.mem_append, List.mem_map]
    exact Or.inl ⟨e / 2, List.mem_range.mpr (by omega), by omega⟩
  | E6 =>
    simp only [coxeterNumber_E6] at he hcop
    have hsub : ∀ x ∈ (List.range 12).filter (Nat.Coprime · 12), x ∈ E6.exponents := by decide
    exact hsub e (List.mem_filter.mpr ⟨List.mem_range.mpr he, decide_eq_true hcop⟩)
  | E7 =>
    simp only [coxeterNumber_E7] at he hcop
    have hsub : ∀ x ∈ (List.range 18).filter (Nat.Coprime · 18), x ∈ E7.exponents := by decide
    exact hsub e (List.mem_filter.mpr ⟨List.mem_range.mpr he, decide_eq_true hcop⟩)
  | E8 =>
    simp only [coxeterNumber_E8] at he hcop
    simp only [exponents_E8, Coxeter.e8Exponents_eq_filter, List.mem_filter, List.mem_range,
      decide_eq_true_eq]
    exact ⟨he, hcop⟩
  | F4 =>
    simp only [coxeterNumber_F4] at he hcop
    simp only [exponents_F4, Coxeter.f4Exponents_eq_filter, List.mem_filter, List.mem_range,
      decide_eq_true_eq]
    exact ⟨he, hcop⟩
  | G2 =>
    simp only [coxeterNumber_G2] at he hcop
    simp only [exponents_G2, Coxeter.g2Exponents_eq_filter, List.mem_filter, List.mem_range,
      decide_eq_true_eq]
    exact ⟨he, hcop⟩

/-- `1` is always an exponent of a valid Dynkin type. -/
lemma one_mem_exponents {t : DynkinType} (ht : t.Valid) : 1 ∈ t.exponents :=
  mem_exponents_of_coprime ht (two_le_coxeterNumber ht) (Nat.coprime_one_left _)

/-- `h - 1` is always an exponent of a valid Dynkin type. -/
lemma coxeterNumber_sub_one_mem_exponents {t : DynkinType} (ht : t.Valid) :
    t.coxeterNumber - 1 ∈ t.exponents := by
  have h2 := two_le_coxeterNumber ht
  refine mem_exponents_of_coprime ht (by omega) ?_
  have hcop : (t.coxeterNumber - 1).Coprime (t.coxeterNumber - 1 + 1) := by simp
  rwa [Nat.sub_add_cancel (by omega)] at hcop

/-- Every fundamental degree of a valid Dynkin type is at least `2`. -/
lemma two_le_of_mem_degrees {t : DynkinType} (ht : t.Valid) {d : ℕ} (hd : d ∈ t.degrees) :
    2 ≤ d := by
  obtain ⟨e, he, rfl⟩ := mem_degrees_iff.mp hd
  have := pos_of_mem_exponents ht he
  omega

/-- Every fundamental degree of a valid Dynkin type is at most its Coxeter number. -/
lemma le_coxeterNumber_of_mem_degrees {t : DynkinType} (ht : t.Valid) {d : ℕ}
    (hd : d ∈ t.degrees) : d ≤ t.coxeterNumber := by
  obtain ⟨e, he, rfl⟩ := mem_degrees_iff.mp hd
  exact lt_coxeterNumber_of_mem_exponents ht he

/-- `2` is always a fundamental degree of a valid Dynkin type (corresponding to the invariant
quadratic form). -/
lemma two_mem_degrees {t : DynkinType} (ht : t.Valid) : 2 ∈ t.degrees :=
  mem_degrees_iff.mpr ⟨1, one_mem_exponents ht, rfl⟩

/-- The Coxeter number `h` is always a fundamental degree of a valid Dynkin type. -/
lemma coxeterNumber_mem_degrees {t : DynkinType} (ht : t.Valid) :
    t.coxeterNumber ∈ t.degrees := by
  have h2 := two_le_coxeterNumber ht
  exact mem_degrees_iff.mpr ⟨t.coxeterNumber - 1, coxeterNumber_sub_one_mem_exponents ht, by omega⟩

end TauCeti.DynkinType

namespace TauCeti.Coxeter

variable {ι R M N : Type*} [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic] [IsDomain R]
  [CharZero R]

/-- **Eigenvalues of the matrix of every Coxeter element of type `E₆` on the simple roots**:
`exp (2πi e / 12)` for the exponents `e = 1, 4, 5, 7, 8, 11`, each once. -/
theorem eigenvalues_of_hasCartanType_E6 {b : P.Base} (h : HasCartanType P b .E6)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ e6Exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 12)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_of_hasCartanType_E6_of_actsBy h hnd hall hW
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic_mul (by norm_num) hc⟩
  have h4 : (4 : ℂ) / 12 = 1 / 3 := by norm_num
  have h8 : (8 : ℂ) / 12 = 2 / 3 := by norm_num
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic_mul hc,
    show (List.range 12).filter (Nat.Coprime · 12) = [1, 5, 7, 11] by decide,
    show (List.range 3).filter (Nat.Coprime · 3) = [1, 2] by decide]
  simp only [e6Exponents, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, Nat.cast_one, Nat.cast_ofNat, h4, h8]
  tauto

/-- **Eigenvalues of the matrix of every Coxeter element of type `E₇` on the simple roots**:
`exp (2πi e / 18)` for the exponents `e = 1, 5, 7, 9, 11, 13, 17`, each once. -/
theorem eigenvalues_of_hasCartanType_E7 {b : P.Base} (h : HasCartanType P b .E7)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ e7Exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 18)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_of_hasCartanType_E7_of_actsBy h hnd hall hW
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic_mul (by norm_num) hc⟩
  have h9 : (9 : ℂ) / 18 = 1 / 2 := by norm_num
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic_mul hc,
    show (List.range 18).filter (Nat.Coprime · 18) = [1, 5, 7, 11, 13, 17] by decide,
    show (List.range 2).filter (Nat.Coprime · 2) = [1] by decide]
  simp only [e7Exponents, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, Nat.cast_one, Nat.cast_ofNat, h9]
  tauto

/-- **Eigenvalues of the matrix of every Coxeter element of type `E₈` on the simple roots**:
`exp (2πi e / 30)` for the exponents `e = 1, 7, 11, 13, 17, 19, 23, 29`, each once. -/
theorem eigenvalues_of_hasCartanType_E8 {b : P.Base} (h : HasCartanType P b .E8)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ e8Exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 30)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_of_hasCartanType_E8_of_actsBy h hnd hall hW
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic hc⟩
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic hc, ← e8Exponents_eq_filter]
  norm_num

/-- **Eigenvalues of the matrix of every Coxeter element of type `F₄` on the simple roots**:
`exp (2πi e / 12)` for the exponents `e = 1, 5, 7, 11`, each once. -/
theorem eigenvalues_of_hasCartanType_F4 {b : P.Base} (h : HasCartanType P b .F4)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ f4Exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 12)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_of_hasCartanType_F4_of_actsBy h hnd hall hW
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic hc⟩
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic hc, ← f4Exponents_eq_filter]
  norm_num

/-- **Eigenvalues of the matrix of every Coxeter element of type `G₂` on the simple roots**:
`exp (2πi e / 6)` for the exponents `e = 1, 5`, each once. -/
theorem eigenvalues_of_hasCartanType_G2 {b : P.Base} (h : HasCartanType P b .G2)
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (∀ ζ : ℂ, ζ ∈ (W.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ g2Exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 6)) = ζ) ∧
      (W.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have hc := charpoly_of_hasCartanType_G2_of_actsBy h hnd hall hW
  refine ⟨fun ζ => ?_, nodup_roots_charpoly_of_charpoly_eq_cyclotomic hc⟩
  rw [mem_roots_charpoly_of_charpoly_eq_cyclotomic hc, ← g2Exponents_eq_filter]
  norm_num

/-! ### Complex root multisets of the classical characteristic polynomials -/

private lemma roots_geom_sum_complex (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (X : ℂ[X]) ^ k).roots =
      (Multiset.ofList ((List.range n).map (· + 1))).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (n + 1 : ℕ))) := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n + 1 : ℕ))
  have hζ : IsPrimitiveRoot ζ (n + 1) :=
    Complex.isPrimitiveRoot_exp (n + 1) (Nat.succ_ne_zero n)
  have hnth : nthRoots (n + 1) (1 : ℂ) = (Multiset.range (n + 1)).map (ζ ^ · * 1) :=
    hζ.nthRoots_eq (one_pow (n + 1))
  have hlhs : nthRoots (n + 1) (1 : ℂ) =
      (∑ k ∈ Finset.range (n + 1), (X : ℂ[X]) ^ k).roots + {1} := by
    rw [nthRoots, map_one, ← geom_sum_mul (X : ℂ[X]) (n + 1),
      roots_mul (by rw [geom_sum_mul]; simpa using X_pow_sub_C_ne_zero (Nat.succ_pos n) (1 : ℂ))]
    congr 1
    simpa using roots_X_sub_C (1 : ℂ)
  have hrhs : (Multiset.range (n + 1)).map (ζ ^ · * 1) =
      ((Multiset.ofList ((List.range n).map (· + 1))).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (n + 1 : ℕ)))) + {1} := by
    rw [← Multiset.coe_range, List.range_succ_eq_map, ← Multiset.cons_coe, Multiset.map_cons,
      pow_zero, one_mul, ← Multiset.singleton_add, add_comm]
    congr 1
    refine Multiset.map_congr rfl fun e _ => ?_
    rw [mul_one, ← Complex.exp_nat_mul]
    congr 1
    ring
  exact add_right_cancel (hlhs.symm.trans (hnth.trans hrhs))

private lemma roots_X_pow_add_one_complex {m : ℕ} (hm : 1 ≤ m) :
    ((X : ℂ[X]) ^ m + 1).roots =
      (Multiset.ofList ((List.range m).map (2 * · + 1))).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (2 * m : ℕ))) := by
  have hm0 : m ≠ 0 := by omega
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)
  let α : ℂ := Complex.exp (Real.pi * Complex.I / m)
  have hα : α ^ m = -1 := by
    rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ hmC, Complex.exp_pi_mul_I]
  have hnth : nthRoots m (-1 : ℂ) = (Multiset.range m).map (ζ ^ · * α) :=
    (Complex.isPrimitiveRoot_exp m hm0).nthRoots_eq hα
  have hlhs : ((X : ℂ[X]) ^ m + 1).roots = nthRoots m (-1 : ℂ) := by
    simp [nthRoots, sub_neg_eq_add]
  have hcoe : ∀ l : List ℕ, Multiset.ofList l = (l : Multiset ℕ) := fun _ => rfl
  rw [hlhs, hnth, ← Multiset.coe_range, hcoe, Multiset.map_coe, Multiset.map_coe, List.map_map]
  refine congrArg Multiset.ofList (List.map_congr_left fun k _ => ?_)
  simp only [Function.comp_apply]
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp

private lemma roots_eq_map_of_mem_iff_of_nodup {s : Multiset ℂ} {es : List ℕ} {h : ℕ}
    (hh : 0 < h) (hes_nd : es.Nodup) (hes_lt : ∀ e ∈ es, e < h) (hs_nd : s.Nodup)
    (hmem : ∀ ζ : ℂ, ζ ∈ s ↔
      ∃ e ∈ es, Complex.exp (2 * Real.pi * Complex.I * (e / (h : ℕ))) = ζ) :
    s = (Multiset.ofList es).map fun e : ℕ =>
      Complex.exp (2 * Real.pi * Complex.I * (e / (h : ℕ))) := by
  let f : ℕ → ℂ := fun e => Complex.exp (2 * Real.pi * Complex.I * (e / (h : ℕ)))
  have hf_pow : ∀ e : ℕ, f e = (Complex.exp (2 * Real.pi * Complex.I / h)) ^ e := by
    intro e
    dsimp [f]
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / h)) h :=
    Complex.isPrimitiveRoot_exp h hh.ne'
  have hmap_nd : ((Multiset.ofList es).map f).Nodup := by
    refine Multiset.Nodup.map_on (fun x hx y hy hxy => ?_) (Multiset.coe_nodup.mpr hes_nd)
    rw [Multiset.mem_coe] at hx hy
    rw [hf_pow, hf_pow] at hxy
    exact hζ.pow_inj (hes_lt x hx) (hes_lt y hy) hxy
  refine (Multiset.Nodup.ext hs_nd hmap_nd).mpr fun ζ => ?_
  rw [hmem]
  simp [f]

/-! ### Eigenvalue multisets for the classical types and for arbitrary valid Dynkin types -/

/-- **Complex eigenvalue multiset of every Coxeter element of type `Aₙ` on the simple roots**:
`exp (2πi e / (n + 1))` for `e = 1, …, n`, each with multiplicity one. -/
theorem roots_charpoly_of_hasCartanType_A_of_actsBy {n : ℕ} {b : P.Base}
    (h : HasCartanType P b (.A n)) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      (Multiset.ofList (DynkinType.A n).exponents).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (DynkinType.A n).coxeterNumber)) := by
  rw [charpoly_map, charpoly_of_hasCartanType_A_of_actsBy h hnd hall hW]
  simp [Polynomial.map_sum, roots_geom_sum_complex]

/-- **Complex eigenvalue multiset of every Coxeter element of type `Bₙ` (`1 ≤ n`) on the simple
roots**: `exp (2πi e / (2 n))` for `e = 1, 3, …, 2 n - 1`, each with multiplicity one. -/
theorem roots_charpoly_of_hasCartanType_B_of_actsBy {n : ℕ} (hn : 1 ≤ n) {b : P.Base}
    (h : HasCartanType P b (.B n)) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      (Multiset.ofList (DynkinType.B n).exponents).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (DynkinType.B n).coxeterNumber)) := by
  rw [charpoly_map, charpoly_of_hasCartanType_B_of_actsBy hn h hnd hall hW]
  simpa using roots_X_pow_add_one_complex hn

/-- **Complex eigenvalue multiset of every Coxeter element of type `Cₙ` (`1 ≤ n`) on the simple
roots**: `exp (2πi e / (2 n))` for `e = 1, 3, …, 2 n - 1`, each with multiplicity one. -/
theorem roots_charpoly_of_hasCartanType_C_of_actsBy {n : ℕ} (hn : 1 ≤ n) {b : P.Base}
    (h : HasCartanType P b (.C n)) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      (Multiset.ofList (DynkinType.C n).exponents).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (DynkinType.C n).coxeterNumber)) := by
  rw [charpoly_map, charpoly_of_hasCartanType_C_of_actsBy hn h hnd hall hW]
  simpa using roots_X_pow_add_one_complex hn

/-- **Complex eigenvalue multiset of every Coxeter element of type `Dₙ` (`2 ≤ n`) on the simple
roots**: `exp (2πi e / (2 (n - 1)))` for `e = 1, 3, …, 2 n - 3, n - 1` (with `-1` of multiplicity
two when `n` is even). -/
theorem roots_charpoly_of_hasCartanType_D_of_actsBy {n : ℕ} (hn : 2 ≤ n) {b : P.Base}
    (h : HasCartanType P b (.D n)) {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l)
    {W : Matrix b.support b.support ℤ} (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      (Multiset.ofList (DynkinType.D n).exponents).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / (DynkinType.D n).coxeterNumber)) := by
  have hm : 1 ≤ n - 1 := by omega
  have hmC : ((n - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hp1 : ((X : ℂ[X]) ^ (n - 1) + 1) ≠ 0 := by
    simpa [sub_neg_eq_add] using X_pow_sub_C_ne_zero (by omega : 0 < n - 1) (-1 : ℂ)
  have hp2 : ((X : ℂ[X]) + 1) ≠ 0 := by
    simpa using X_sub_C_ne_zero (-1 : ℂ)
  rw [charpoly_map, charpoly_of_hasCartanType_D_of_actsBy hn h hnd hall hW]
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_one,
    DynkinType.exponents_D_of_ne_zero (by omega : n ≠ 0), DynkinType.coxeterNumber_D,
    ← Multiset.coe_add, Multiset.map_add, Multiset.coe_singleton, Multiset.map_singleton]
  rw [roots_mul (mul_ne_zero hp1 hp2), roots_X_pow_add_one_complex hm]
  congr 1
  have hlin : ((X : ℂ[X]) + 1).roots = {-1} := by simpa using roots_X_add_C (1 : ℂ)
  rw [hlin]
  congr 1
  have hexp : 2 * (Real.pi : ℂ) * Complex.I * (((n - 1 : ℕ) : ℂ) / (2 * ((n - 1 : ℕ) : ℂ))) =
      Real.pi * Complex.I := by
    field_simp
  push_cast
  rw [hexp, Complex.exp_pi_mul_I]

/-- **Complex eigenvalue multiset of every Coxeter element of a base of valid Cartan type `t`** on
the simple roots: counted with multiplicity, the eigenvalues are `exp (2πi e / h)` as `e` runs over
`t.exponents`, where `h = t.coxeterNumber`. -/
theorem roots_charpoly_of_hasCartanType_of_actsBy {t : DynkinType} (ht : t.Valid)
    {b : P.Base} (h : HasCartanType P b t) {l : List b.support} (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      (Multiset.ofList t.exponents).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / t.coxeterNumber)) := by
  cases t with
  | A n => exact roots_charpoly_of_hasCartanType_A_of_actsBy h hnd hall hW
  | B n =>
    exact roots_charpoly_of_hasCartanType_B_of_actsBy
      (by have := DynkinType.valid_B.mp ht; omega) h hnd hall hW
  | C n =>
    exact roots_charpoly_of_hasCartanType_C_of_actsBy
      (by have := DynkinType.valid_C.mp ht; omega) h hnd hall hW
  | D n =>
    exact roots_charpoly_of_hasCartanType_D_of_actsBy
      (by have := DynkinType.valid_D.mp ht; omega) h hnd hall hW
  | E6 =>
    obtain ⟨hmem, hnd_r⟩ := eigenvalues_of_hasCartanType_E6 h hnd hall hW
    rw [DynkinType.coxeterNumber_E6, DynkinType.exponents_E6]
    exact roots_eq_map_of_mem_iff_of_nodup (h := 12) (by norm_num) (by decide) (by decide)
      hnd_r (by simpa using hmem)
  | E7 =>
    obtain ⟨hmem, hnd_r⟩ := eigenvalues_of_hasCartanType_E7 h hnd hall hW
    rw [DynkinType.coxeterNumber_E7, DynkinType.exponents_E7]
    exact roots_eq_map_of_mem_iff_of_nodup (h := 18) (by norm_num) (by decide) (by decide)
      hnd_r (by simpa using hmem)
  | E8 =>
    obtain ⟨hmem, hnd_r⟩ := eigenvalues_of_hasCartanType_E8 h hnd hall hW
    rw [DynkinType.coxeterNumber_E8, DynkinType.exponents_E8]
    exact roots_eq_map_of_mem_iff_of_nodup (h := 30) (by norm_num) (by decide) (by decide)
      hnd_r (by simpa using hmem)
  | F4 =>
    obtain ⟨hmem, hnd_r⟩ := eigenvalues_of_hasCartanType_F4 h hnd hall hW
    rw [DynkinType.coxeterNumber_F4, DynkinType.exponents_F4]
    exact roots_eq_map_of_mem_iff_of_nodup (h := 12) (by norm_num) (by decide) (by decide)
      hnd_r (by simpa using hmem)
  | G2 =>
    obtain ⟨hmem, hnd_r⟩ := eigenvalues_of_hasCartanType_G2 h hnd hall hW
    rw [DynkinType.coxeterNumber_G2, DynkinType.exponents_G2]
    exact roots_eq_map_of_mem_iff_of_nodup (h := 6) (by norm_num) (by decide) (by decide)
      hnd_r (by simpa using hmem)

/-- **Every primitive `h`-th root of unity `exp (2πi e / h)` (`e < h`, `gcd(e, h) = 1`) is an
eigenvalue of every Coxeter element of a base of valid Cartan type `t`.** -/
theorem mem_roots_charpoly_of_hasCartanType_of_actsBy_of_coprime {t : DynkinType}
    (ht : t.Valid) {b : P.Base} (h : HasCartanType P b t) {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) {e : ℕ} (he : e < t.coxeterNumber)
    (hcop : e.Coprime t.coxeterNumber) :
    Complex.exp (2 * Real.pi * Complex.I * (e / t.coxeterNumber)) ∈
      (W.map (Int.castRingHom ℂ)).charpoly.roots := by
  rw [roots_charpoly_of_hasCartanType_of_actsBy ht h hnd hall hW, Multiset.mem_map]
  exact ⟨e, Multiset.mem_coe.mpr (t.mem_exponents_of_coprime ht he hcop), rfl⟩

end TauCeti.Coxeter

end
