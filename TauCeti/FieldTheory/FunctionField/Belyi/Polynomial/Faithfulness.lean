/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Lenstra.Belyi
public import TauCeti.FieldTheory.FunctionField.Belyi.Polynomial.GaloisAction

/-!
# Faithfulness of the Galois action on Belyi pairs

Over a field algebraic over `ℚ`, every nontrivial coefficient automorphism moves the
isomorphism class of some polynomial Belyi pair. In particular, the absolute Galois group of
`ℚ` acts faithfully on isomorphism classes of algebraic Belyi pairs over `AlgebraicClosure ℚ`.
The witnesses already have rational function field, so genus-zero pairs suffice.

The polynomial input is Lenstra's construction
`TauCeti.exists_polynomial_criticalValues_subset_comp_ne_map`. The passage to isomorphism
classes uses `TauCeti.AlgebraicBelyiPair.IsoClass.smul_mk_ofPolynomial_eq_iff`: an isomorphism
between polynomial pairs must be an affine change of variable. Thus the polynomial
inequivalence detects inequivalence of the actual pairs, not just of their presentations.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, LMS Student Texts 79, Cambridge University Press, 2012, Theorem 4.49
  (the proof attributed there to Lenstra).
-/

public section

namespace TauCeti.AlgebraicBelyiPair.IsoClass

universe u

variable {k : Type u} [Field k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
  {G : Type*} [Group G] [MulSemiringAction G k]

/-- If `g` moves a coefficient in a field algebraic over `ℚ`, it moves the isomorphism class
of a polynomial Belyi pair. The polynomial has positive degree and all its critical values,
in every field extension, lie in `{0, 1}`. -/
theorem exists_smul_mk_ofPolynomial_ne (g : G) (hg : ∃ x : k, g • x ≠ x) :
    ∃ (q : Polynomial k) (hq : 0 < q.natDegree)
      (hcrit : ∀ (L : Type u) [Field L] [Algebra k L], q.criticalValues L ⊆ {0, 1}),
      g • mk (ofPolynomial q hq hcrit) ≠ mk (ofPolynomial q hq hcrit) := by
  have hσ : MulSemiringAction.toRingHom G k g ≠ RingHom.id k := by
    intro h
    obtain ⟨x, hx⟩ := hg
    exact hx (RingHom.congr_fun h x)
  obtain ⟨q, hq, hcrit, hqσ⟩ := exists_polynomial_criticalValues_subset_comp_ne_map hσ
  refine ⟨q, hq, hcrit, ?_⟩
  intro h
  obtain ⟨a, b, ha, hab⟩ := (smul_mk_ofPolynomial_eq_iff hq hcrit g).mp h
  exact hqσ a b ha hab

/-- A faithful action by field automorphisms on an algebraic extension of `ℚ` remains faithful
on isomorphism classes of algebraic Belyi pairs. In particular this applies to
`Gal(AlgebraicClosure ℚ/ℚ)`. -/
instance instFaithfulSMul [FaithfulSMul G k] : FaithfulSMul G (IsoClass k) := by
  apply faithfulSMul_iff.mpr
  intro g hg
  apply eq_of_smul_eq_smul (α := k)
  intro x
  rw [one_smul]
  by_contra hx
  obtain ⟨q, hq, hcrit, hmove⟩ := exists_smul_mk_ofPolynomial_ne g ⟨x, hx⟩
  exact hmove (hg (mk (ofPolynomial q hq hcrit)))

end TauCeti.AlgebraicBelyiPair.IsoClass
