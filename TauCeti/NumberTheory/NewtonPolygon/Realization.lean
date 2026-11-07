/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Roots

/-!
# Realizing prescribed Newton slopes

For an additive valuation whose only infinite value is at zero, a finite multiset of real
slopes is realized by a split polynomial with nonzero constant coefficient precisely when
the negative of each slope is the valuation of a nonzero element of the coefficient ring.
The construction is a product of linear factors, with repeated slopes retaining their
multiplicities. It gives a monic polynomial of degree equal to the cardinality of the multiset.
Over a field one can instead normalize the constant coefficient to one, without changing
the slopes.

These statements are converses to `Polynomial.newtonSlopes_eq_map_roots`. They require
neither completeness nor algebraic closedness: the necessary root valuations are specified
explicitly. In an algebraically closed field, the splitting condition on a realizing
polynomial is automatic. The empty slope multiset is realized by the constant polynomial one,
not by the zero polynomial.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
-/

public section

namespace Polynomial

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]
variable (v : AddValuation R (WithTop ℝ))

/-- Prescribed finite slopes with attainable negative valuations are realized by a monic
split polynomial with no zero root. Each slope contributes one linear factor. -/
theorem exists_monic_splits_newtonSlopes (s : Multiset ℝ)
    (hs : ∀ m ∈ s, ∃ x : R, x ≠ 0 ∧ v x = ((-m : ℝ) : WithTop ℝ)) :
    ∃ f : R[X], f.Monic ∧ f.Splits ∧ f.coeff 0 ≠ 0 ∧
      f.natDegree = s.card ∧ f.newtonSlopes v = s := by
  classical
  induction s using Multiset.induction_on with
  | empty =>
    exact ⟨1, monic_one, Splits.one, by simp, by simp,
      by simpa using newtonSlopes_C v (1 : R)⟩
  | cons m s ih =>
    obtain ⟨x, hx, hvm⟩ := hs m (Multiset.mem_cons_self m s)
    obtain ⟨f, hmonic, hsplit, hf0, hdeg, hslopes⟩ :=
      ih (fun n hn => hs n (Multiset.mem_cons_of_mem hn))
    refine ⟨(X - C x) * f, (monic_X_sub_C x).mul hmonic,
      (Splits.X_sub_C x).mul hsplit, ?_, ?_, ?_⟩
    · simpa using mul_ne_zero (neg_ne_zero.mpr hx) hf0
    · simp [natDegree_mul (X_sub_C_ne_zero x) hmonic.ne_zero, hdeg, Nat.add_comm]
    · rw [newtonSlopes_mul _ _ v ((monic_X_sub_C x).newtonPolygon_ne_top v)
        (hmonic.newtonPolygon_ne_top v), newtonSlopes_X_sub_C v (hvm ▸ WithTop.coe_ne_top),
        hvm, WithTop.untop₀_coe, neg_neg, hslopes]
      exact Multiset.singleton_add _ _

/-- A multiset is the finite slope multiset of a monic split polynomial with nonzero
constant coefficient if and only if all its negative slopes are attained by the valuation
on nonzero elements. The realizing polynomial has exactly the prescribed degree. -/
theorem exists_monic_splits_newtonSlopes_iff (hv : ∀ x, v x = ⊤ → x = 0)
    (s : Multiset ℝ) :
    (∃ f : R[X], f.Monic ∧ f.Splits ∧ f.coeff 0 ≠ 0 ∧
      f.natDegree = s.card ∧ f.newtonSlopes v = s) ↔
    ∀ m ∈ s, ∃ x : R, x ≠ 0 ∧ v x = ((-m : ℝ) : WithTop ℝ) := by
  classical
  refine ⟨?_, exists_monic_splits_newtonSlopes v s⟩
  rintro ⟨f, -, hsplit, -, -, rfl⟩ m hm
  rw [newtonSlopes_eq_map_roots hv hsplit] at hm
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hm
  have hx0 := (Multiset.mem_filter.mp hx).2
  exact ⟨x, hx0, by simp [WithTop.coe_untop₀_of_ne_top (mt (hv x) hx0)]⟩

end Domain

section Field

variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℝ))

/-- Prescribed finite slopes with attainable negative valuations are realized over a field
by a split polynomial with constant coefficient one. Scalar normalization preserves both
the degree and the slope multiplicities. -/
theorem exists_splits_coeff_zero_eq_one_newtonSlopes (s : Multiset ℝ)
    (hs : ∀ m ∈ s, ∃ x : K, x ≠ 0 ∧ v x = ((-m : ℝ) : WithTop ℝ)) :
    ∃ f : K[X], f.Splits ∧ f.coeff 0 = 1 ∧
      f.natDegree = s.card ∧ f.newtonSlopes v = s := by
  obtain ⟨f, -, hsplit, hf0, hdeg, hslopes⟩ := exists_monic_splits_newtonSlopes v s hs
  refine ⟨C (f.coeff 0)⁻¹ * f, hsplit.C_mul _, ?_, ?_, ?_⟩
  · simp [hf0]
  · rw [natDegree_C_mul (inv_ne_zero hf0), hdeg]
  · rw [newtonSlopes_C_mul f v (v.ne_top_iff.mpr (inv_ne_zero hf0)), hslopes]

end Field

end Polynomial
