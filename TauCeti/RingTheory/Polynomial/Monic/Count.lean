/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.RingTheory.Polynomial.DegreeLT

/-!
# Counting monic polynomials of a given degree

Over a nontrivial semiring with `q` elements there are `q ^ d` monic polynomials of degree `d`
(`Polynomial.ncard_setOf_monic_natDegree_eq`). Two crude upper bounds follow over a finite
field: at most `q ^ (r - 1)` monic polynomials of degree `r`
vanish at a given point, and at most `r * q ^ (r - 1)` of them are not squarefree.

## Main results

* `Polynomial.ncard_monic_isRoot_le`: at most `Nat.card R ^ (r - 1)` monic polynomials of
  degree `r` over a finite commutative ring vanish at a given point.
* `Polynomial.Monic.exists_eq_mul_self_mul_of_not_squarefree`: a monic polynomial of degree `r`
  over a field that is not squarefree is `g * g * h` with `g`, `h` monic and `1 ≤ deg g ≤ r / 2`.
* `Polynomial.ncard_monic_not_squarefree_le`: at most `r * Nat.card K ^ (r - 1)` monic
  polynomials of degree `r` over a finite field are not squarefree.

## References

* R. Lidl and H. Niederreiter, *Finite Fields* (1983), ch. 3, for the counts of squarefree
  polynomials over a finite field.
-/

public section

namespace Polynomial

/-- At most `q ^ (r - 1)` monic polynomials of degree `r` over a finite commutative ring with `q`
elements vanish at a given point `a`: each is `X - C a` times a monic polynomial of degree
`r - 1`. -/
theorem ncard_monic_isRoot_le {R : Type*} [CommRing R] [Finite R] (a : R) (r : ℕ) :
    {f : R[X] | f.Monic ∧ f.natDegree = r ∧ f.IsRoot a}.ncard ≤ Nat.card R ^ (r - 1) := by
  cases subsingleton_or_nontrivial R
  · rw [Nat.card_unique, one_pow]
    exact Set.ncard_le_one_of_subsingleton _
  have hsub : {f : R[X] | f.Monic ∧ f.natDegree = r ∧ f.IsRoot a} ⊆
      ((X - C a) * ·) '' {g : R[X] | g.Monic ∧ g.natDegree = r - 1} := by
    rintro f ⟨hf, hr, ha⟩
    obtain ⟨g, rfl⟩ := dvd_iff_isRoot.mpr ha
    have hg : g.Monic := (monic_X_sub_C a).of_mul_monic_left hf
    rw [(monic_X_sub_C a).natDegree_mul hg, natDegree_X_sub_C] at hr
    exact ⟨g, ⟨hg, by omega⟩, rfl⟩
  calc _ ≤ _ := Set.ncard_le_ncard hsub ((finite_setOf_monic_natDegree_eq _ _).image _)
    _ ≤ _ := Set.ncard_image_le (finite_setOf_monic_natDegree_eq _ _)
    _ = _ := ncard_setOf_monic_natDegree_eq _ _

section Field

variable {K : Type*} [Field K]

/-- A monic polynomial of degree `r` over a field that is not squarefree is `g * g * h` with `g`,
`h` monic, `1 ≤ deg g = d ≤ r / 2` and `deg h = r - 2 * d`. -/
theorem Monic.exists_eq_mul_self_mul_of_not_squarefree {r : ℕ} {f : K[X]} (hf : f.Monic)
    (hr : f.natDegree = r) (hsq : ¬Squarefree f) : ∃ d ∈ Finset.Icc 1 (r / 2), ∃ g h : K[X],
      (g.Monic ∧ g.natDegree = d) ∧ (h.Monic ∧ h.natDegree = r - 2 * d) ∧ g * g * h = f := by
  classical
  simp only [Squarefree, not_forall] at hsq
  obtain ⟨x, hxx, hx⟩ := hsq
  have hpos := natDegree_pos_of_not_isUnit_of_dvd_monic hf hx ((dvd_mul_right x x).trans hxx)
  have hg : (normalize x).Monic := monic_normalize (by rintro rfl; simp at hpos)
  obtain ⟨h, hfh⟩ := (mul_dvd_mul (normalize_dvd_iff.mpr dvd_rfl)
    (normalize_dvd_iff.mpr dvd_rfl)).trans hxx
  have hh : h.Monic := (hg.mul hg).of_mul_monic_left (hfh ▸ hf)
  rw [hfh, (hg.mul hg).natDegree_mul hh, hg.natDegree_mul hg, natDegree_normalize] at hr
  exact ⟨x.natDegree, Finset.mem_Icc.mpr ⟨hpos, by omega⟩, normalize x, h,
    ⟨hg, natDegree_normalize⟩, ⟨hh, by omega⟩, hfh.symm⟩

/-- At most `r * q ^ (r - 1)` monic polynomials of degree `r` over a finite field with `q`
elements are not squarefree. (The proof gives `⌊r / 2⌋ * q ^ (r - 1)`.) -/
theorem ncard_monic_not_squarefree_le [Finite K] (r : ℕ) :
    {f : K[X] | f.Monic ∧ f.natDegree = r ∧ ¬Squarefree f}.ncard ≤ r * Nat.card K ^ (r - 1) := by
  set S : ℕ → Set K[X] := fun d ↦ {g : K[X] | g.Monic ∧ g.natDegree = d}
  set T : Finset.Icc 1 (r / 2) → Set K[X] :=
    fun d ↦ Set.image2 (fun g h ↦ g * g * h) (S d) (S (r - 2 * d))
  have hsub : {f : K[X] | f.Monic ∧ f.natDegree = r ∧ ¬Squarefree f} ⊆ ⋃ d, T d := by
    rintro f ⟨hf, hr, hsq⟩
    obtain ⟨d, hd, g, h, hg, hh, rfl⟩ := hf.exists_eq_mul_self_mul_of_not_squarefree hr hsq
    exact Set.mem_iUnion.mpr ⟨⟨d, hd⟩, g, hg, h, hh, rfl⟩
  have hT (d : Finset.Icc 1 (r / 2)) : (T d).ncard ≤ Nat.card K ^ (r - 1) := by
    have hd := Finset.mem_Icc.mp d.property
    calc (T d).ncard ≤ (S d).ncard * (S (r - 2 * d)).ncard :=
          Set.ncard_image2_le (finite_setOf_monic_natDegree_eq _ _)
            (finite_setOf_monic_natDegree_eq _ _)
      _ = Nat.card K ^ ((d : ℕ) + (r - 2 * d)) := by
          rw [ncard_setOf_monic_natDegree_eq, ncard_setOf_monic_natDegree_eq, pow_add]
      _ ≤ Nat.card K ^ (r - 1) := Nat.pow_le_pow_right Nat.card_pos (by omega)
  calc _ ≤ (⋃ d, T d).ncard := Set.ncard_le_ncard hsub
          (Set.finite_iUnion fun d ↦ (finite_setOf_monic_natDegree_eq _ _).image2 _
            (finite_setOf_monic_natDegree_eq _ _))
    _ ≤ ∑ d, (T d).ncard := Set.ncard_iUnion_le_of_fintype T
    _ ≤ ∑ _d : Finset.Icc 1 (r / 2), Nat.card K ^ (r - 1) := Finset.sum_le_sum fun d _ ↦ hT d
    _ ≤ r * Nat.card K ^ (r - 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, Nat.card_Icc, smul_eq_mul]
          exact Nat.mul_le_mul_right _ (by omega)

end Field

end Polynomial
