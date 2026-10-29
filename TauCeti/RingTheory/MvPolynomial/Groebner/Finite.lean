/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Groebner.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Finite Gröbner bases

Every ideal in a polynomial ring with finitely many variables over a Noetherian ring has a
finite Gröbner basis. More generally, any Gröbner basis contains a finite Gröbner basis whenever
its leading-term ideal is finitely generated. Over a field, rescaling the nonzero members gives
a finite monic Gröbner basis.

The extraction uses Mathlib's `Submodule.fg_span_iff_fg_span_finset_subset` and the Hilbert
basis theorem. These are existence results, without a choice of completion algorithm or a
claim that the resulting basis is reduced.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 2, §5:
  existence of finite Gröbner bases.
-/

public section

namespace MonomialOrder

open MvPolynomial

variable {σ R : Type*} (m : MonomialOrder σ)

section CommSemiring

variable [CommSemiring R] {m} {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}

/-- A Gröbner basis contains a finite Gröbner basis if its leading-term ideal is finitely
generated. No finiteness assumption on the variable type or coefficient ring is needed here. -/
theorem IsGroebnerBasis.exists_finset_subset (h : m.IsGroebnerBasis G I)
    (hfg : (Ideal.span (m.leadingTerm '' (I : Set (MvPolynomial σ R)))).FG) :
    ∃ B : Finset (MvPolynomial σ R), (B : Set _) ⊆ G ∧ m.IsGroebnerBasis B I := by
  classical
  rw [h.span_leadingTerm_image] at hfg
  obtain ⟨T, hTG, hT⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (m.leadingTerm '' G)).1 hfg
  obtain ⟨B, hBG, hBT⟩ := Finset.subset_set_image_iff.1 hTG
  refine ⟨B, hBG, .mk (hBG.trans h.subset) ?_⟩
  rw [h.span_leadingTerm_image]
  simpa only [← hBT, Finset.coe_image] using hT

end CommSemiring

section Noetherian

variable [CommRing R] [IsNoetherianRing R] [Finite σ]

/-- Every ideal over a Noetherian coefficient ring in finitely many variables has a finite
Gröbner basis, for any monomial order. -/
theorem exists_finset_isGroebnerBasis (I : Ideal (MvPolynomial σ R)) :
    ∃ G : Finset (MvPolynomial σ R), m.IsGroebnerBasis G I := by
  obtain ⟨G, -, hG⟩ := (m.isGroebnerBasis_self I).exists_finset_subset
    (IsNoetherian.noetherian _)
  exact ⟨G, hG⟩

end Noetherian

section Field

variable {k : Type*} [Field k] [Finite σ]

/-- Every ideal in finitely many variables over a field has a finite monic Gröbner basis.
All members are nonzero; for the zero ideal the empty basis is allowed. -/
theorem exists_finset_monic_isGroebnerBasis (I : Ideal (MvPolynomial σ k)) :
    ∃ G : Finset (MvPolynomial σ k), (∀ g ∈ G, m.Monic g) ∧ m.IsGroebnerBasis G I := by
  classical
  obtain ⟨B, hB⟩ := m.exists_finset_isGroebnerBasis I
  let normalize (p : MvPolynomial σ k) := C (m.leadingCoeff p)⁻¹ * p
  have hdegree (p : MvPolynomial σ k) (hp : p ≠ 0) :
      m.degree (normalize p) = m.degree p := by
    dsimp only [normalize]
    rw [m.degree_mul (C_ne_zero.2 (inv_ne_zero (m.leadingCoeff_ne_zero_iff.2 hp))) hp,
      m.degree_C, zero_add]
  have hmonic (p : MvPolynomial σ k) (hp : p ≠ 0) : m.Monic (normalize p) := by
    simp [normalize, Monic, m.leadingCoeff_ne_zero_iff.2 hp]
  have hGmonic : ∀ g ∈ (B.erase 0).image normalize, m.Monic g := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hg
    exact hmonic p (Finset.mem_erase.1 hp).1
  refine ⟨(B.erase 0).image normalize, hGmonic, ?_⟩
  apply (m.isGroebnerBasis_iff_forall_exists_degree_le_degree
    (fun g hg _ ↦ (hGmonic g hg).leadingCoeff_eq_one.symm ▸ isUnit_one)).2
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hg
    exact I.mul_mem_left _ (hB.subset (Finset.mem_erase.1 hp).2)
  · intro p hp hp0
    obtain ⟨b, hb, hb0, hbp⟩ := hB.exists_degree_le_degree hp hp0
    exact ⟨normalize b, Finset.mem_image.2 ⟨b, Finset.mem_erase.2 ⟨hb0, hb⟩, rfl⟩,
      (hmonic b hb0).ne_zero, (hdegree b hb0) ▸ hbp⟩

end Field

end MonomialOrder
