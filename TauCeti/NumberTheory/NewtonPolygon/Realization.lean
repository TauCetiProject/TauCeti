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

section CommRing

variable {R : Type*} [CommRing R]
variable (v : AddValuation R (WithTop ℝ))

/-- A finite multiset `s` of slopes such that, for every `m ∈ s`, `-m` is a value of `v`
is realized by a monic split polynomial with nonzero constant coefficient and degree `s.card`. -/
theorem exists_monic_splits_newtonSlopes (s : Multiset ℝ)
    (hs : ∀ m ∈ s, ∃ x : R, v x = ((-m : ℝ) : WithTop ℝ)) :
    ∃ f : R[X], f.Monic ∧ f.Splits ∧ f.coeff 0 ≠ 0 ∧
      f.natDegree = s.card ∧ f.newtonSlopes v = s := by
  classical
  have : Nontrivial R := nontrivial_of_ne (0 : R) 1 (fun h => by
    have := congrArg v h
    simp at this)
  let root (m : {m // m ∈ s}) : R := Classical.choose (hs m m.property)
  have hroot (m : {m // m ∈ s}) : v (root m) = ((-m.val : ℝ) : WithTop ℝ) :=
    Classical.choose_spec (hs m m.property)
  let t := s.attach.map root
  have ht : ∀ x ∈ t, v x ≠ ⊤ := by
    intro x hx
    obtain ⟨m, -, rfl⟩ := Multiset.mem_map.mp hx
    rw [hroot]
    exact WithTop.coe_ne_top
  have ht0 : ∀ x ∈ t, x ≠ 0 := by
    intro x hx h
    simpa [h] using ht x hx
  refine ⟨(t.map (X - C ·)).prod, monic_multisetProd_X_sub_C t,
    Splits.multisetProd (by simp), ?_, ?_, ?_⟩
  · have hfinite : v ((t.map (X - C ·)).prod.coeff 0) ≠ ⊤ := by
      refine Multiset.prod_induction (fun f : R[X] => v (f.coeff 0) ≠ ⊤) _ ?_
        (by simp) ?_
      · intro f g hf hg
        simpa [mul_coeff_zero, v.map_mul] using WithTop.add_ne_top.mpr ⟨hf, hg⟩
      · intro f hf
        obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hf
        simpa using ht x hx
    intro h
    exact hfinite (by rw [h, v.map_zero])
  · rw [natDegree_multiset_prod_X_sub_C_eq_card]
    simp [t]
  · rw [newtonSlopes_multiset_prod_X_sub_C t (fun x hx _ => ht x hx),
      Multiset.filter_eq_self.mpr ht0]
    simp only [t, Multiset.map_map]
    simpa only [Function.comp_apply, hroot, WithTop.untop₀_coe, neg_neg]
      using s.attach_map_val

/-- Over an integral domain, assuming only zero has infinite valuation, a multiset `s` is the
finite slope multiset of a monic split polynomial with nonzero constant coefficient and degree
`s.card` if and only if, for every `m ∈ s`, `-m` is a value of `v`. -/
theorem exists_monic_splits_newtonSlopes_iff [IsDomain R] (hv : ∀ x, v x = ⊤ → x = 0)
    (s : Multiset ℝ) :
    (∃ f : R[X], f.Monic ∧ f.Splits ∧ f.coeff 0 ≠ 0 ∧
      f.natDegree = s.card ∧ f.newtonSlopes v = s) ↔
    ∀ m ∈ s, ∃ x : R, v x = ((-m : ℝ) : WithTop ℝ) := by
  classical
  refine ⟨?_, exists_monic_splits_newtonSlopes v s⟩
  rintro ⟨f, -, hsplit, -, -, rfl⟩ m hm
  rw [newtonSlopes_eq_map_roots hv hsplit] at hm
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hm
  have hx0 := (Multiset.mem_filter.mp hx).2
  exact ⟨x, by simp [WithTop.coe_untop₀_of_ne_top (mt (hv x) hx0)]⟩

end CommRing

section Field

variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℝ))

/-- Over a field, a finite multiset `s` of slopes such that, for every `m ∈ s`, `-m` is a value
of `v` is realized by a split polynomial with constant coefficient one and degree `s.card`. -/
theorem exists_splits_coeff_zero_eq_one_newtonSlopes (s : Multiset ℝ)
    (hs : ∀ m ∈ s, ∃ x : K, v x = ((-m : ℝ) : WithTop ℝ)) :
    ∃ f : K[X], f.Splits ∧ f.coeff 0 = 1 ∧
      f.natDegree = s.card ∧ f.newtonSlopes v = s := by
  obtain ⟨f, -, hsplit, hf0, hdeg, hslopes⟩ := exists_monic_splits_newtonSlopes v s hs
  refine ⟨C (f.coeff 0)⁻¹ * f, hsplit.C_mul _, ?_, ?_, ?_⟩
  · simp [hf0]
  · rw [natDegree_C_mul (inv_ne_zero hf0), hdeg]
  · rw [newtonSlopes_C_mul f v (v.ne_top_iff.mpr (inv_ne_zero hf0)), hslopes]

end Field

end Polynomial
