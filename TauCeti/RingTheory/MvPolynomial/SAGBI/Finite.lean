/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteType
public import TauCeti.RingTheory.MvPolynomial.SAGBI.Monic
import TauCeti.RingTheory.Adjoin.FG

/-!
# Finite SAGBI bases and finite generation of initial algebras

Unlike ideals in a polynomial ring in finitely many variables over a field, which always admit a
finite Gröbner basis by the Hilbert basis theorem (`MonomialOrder.exists_finset_isGroebnerBasis`),
a finitely generated subalgebra `A` of `MvPolynomial σ k` need not possess a finite SAGBI basis.
Instead, existence of a finite SAGBI basis of `A` is equivalent to finite generation of its initial
algebra `m.initialAlgebra A`, and over a field to finite generation of its monoid of leading
exponents `m.leadingExponents A`.

## Main results

* `MonomialOrder.IsSAGBIBasis.exists_finset_subset`: any SAGBI basis contains a finite SAGBI basis
  whenever the initial algebra is finitely generated.
* `MonomialOrder.exists_finset_isSAGBIBasis_iff_fg_initialAlgebra`: over any commutative semiring,
  `A` admits a finite SAGBI basis if and only if `m.initialAlgebra A` is finitely generated.
* `MonomialOrder.finiteType_initialAlgebra_iff_fg_leadingExponents` and
  `MonomialOrder.fg_initialAlgebra_iff_fg_leadingExponents`: over a field, the initial algebra of
  `A` is finitely generated as a `k`-algebra if and only if `m.leadingExponents A` is finitely
  generated as an additive submonoid.
* `MonomialOrder.exists_finset_monic_isSAGBIBasis_iff`: over a field, `A` admits a finite monic
  SAGBI basis if and only if `m.leadingExponents A` is finitely generated.

## References

* L. Robbiano, M. Sweedler, *Subalgebra bases*, in *Commutative Algebra (Salvador, 1988)*,
  Lecture Notes in Mathematics 1430, Springer, 1990, 61–87.
* D. Kapur, K. Madlener, *A completion procedure for computing a canonical basis for a
  k-subalgebra*, in *Computers and Mathematics*, Springer, 1989, 1–11.
* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, University Lecture Series 8, AMS, 1996,
  Chapter 11.
-/

public section

open MvPolynomial

namespace MonomialOrder

variable {σ R : Type*} (m : MonomialOrder σ)

section CommSemiring

variable [CommSemiring R] {m} {G : Set (MvPolynomial σ R)} {A : Subalgebra R (MvPolynomial σ R)}

/-- A SAGBI basis contains a finite SAGBI basis whenever the initial algebra is finitely generated.
No finiteness assumption on the variable type or field hypothesis on the coefficients is needed. -/
theorem IsSAGBIBasis.exists_finset_subset (h : m.IsSAGBIBasis G A)
    (hfg : (m.initialAlgebra A).FG) :
    ∃ B : Finset (MvPolynomial σ R), (B : Set (MvPolynomial σ R)) ⊆ G ∧
      m.IsSAGBIBasis (B : Set (MvPolynomial σ R)) A := by
  classical
  rw [← h.adjoin_leadingTerm] at hfg
  obtain ⟨T, hTG, hT⟩ := TauCeti.fg_adjoin_iff_exists_finset_subset_adjoin_eq.1 hfg
  obtain ⟨B, hBG, hBT⟩ := Finset.subset_set_image_iff.1 hTG
  refine ⟨B, hBG, .mk (hBG.trans h.subset) ?_⟩
  rw [← h.adjoin_leadingTerm]
  simpa only [← hBT, Finset.coe_image] using hT

/-- A finite SAGBI basis witnesses that the initial algebra is finitely generated. -/
theorem IsSAGBIBasis.fg_initialAlgebra (h : m.IsSAGBIBasis G A) (hG : G.Finite) :
    (m.initialAlgebra A).FG :=
  Subalgebra.fg_def.2 ⟨m.leadingTerm '' G, hG.image _, h.adjoin_leadingTerm⟩

/-- Over a commutative semiring, `A` admits a finite SAGBI basis if and only if its initial algebra
is finitely generated. -/
theorem exists_finset_isSAGBIBasis_iff_fg_initialAlgebra :
    (∃ B : Finset (MvPolynomial σ R), m.IsSAGBIBasis (B : Set (MvPolynomial σ R)) A) ↔
      (m.initialAlgebra A).FG := by
  refine ⟨fun ⟨B, hB⟩ ↦ hB.fg_initialAlgebra B.finite_toSet, fun hfg ↦ ?_⟩
  obtain ⟨B, -, hB⟩ := (isSAGBIBasis_self A).exists_finset_subset hfg
  exact ⟨B, hB⟩

end CommSemiring

section Field

variable {k : Type*} [Field k] {m} {G : Set (MvPolynomial σ k)}
  {A : Subalgebra k (MvPolynomial σ k)}

/-- Over a field, the initial algebra of `A` is of finite type over `k` if and only if the additive
submonoid of leading exponents of `A` is finitely generated. -/
theorem finiteType_initialAlgebra_iff_fg_leadingExponents :
    Algebra.FiniteType k (m.initialAlgebra A) ↔ (m.leadingExponents A).FG :=
  ⟨fun h ↦ AddMonoidAlgebra.finiteType_iff_fg.1 (h.equiv (m.initialAlgebraEquiv A).symm),
    fun h ↦ (AddMonoidAlgebra.finiteType_iff_fg.2 h).equiv (m.initialAlgebraEquiv A)⟩

/-- Over a field, the initial algebra of `A` is finitely generated as a subalgebra if and only if
the additive submonoid of leading exponents of `A` is finitely generated. -/
theorem fg_initialAlgebra_iff_fg_leadingExponents :
    (m.initialAlgebra A).FG ↔ (m.leadingExponents A).FG :=
  (Subalgebra.fg_iff_finiteType (m.initialAlgebra A)).trans
    finiteType_initialAlgebra_iff_fg_leadingExponents

/-- A finite SAGBI basis over a field witnesses finite generation of the leading exponents. -/
theorem IsSAGBIBasis.fg_leadingExponents (h : m.IsSAGBIBasis G A) (hG : G.Finite) :
    (m.leadingExponents A).FG :=
  fg_initialAlgebra_iff_fg_leadingExponents.1 (h.fg_initialAlgebra hG)

/-- Over a field, `A` has a finite monic SAGBI basis if and only if its monoid of leading exponents
is finitely generated. All members of a monic basis are nonzero; for the base-field subalgebra `⊥`
the empty basis `∅` is valid. -/
theorem exists_finset_monic_isSAGBIBasis_iff :
    (∃ B : Finset (MvPolynomial σ k), (∀ b ∈ B, m.Monic b) ∧
      m.IsSAGBIBasis (B : Set (MvPolynomial σ k)) A) ↔ (m.leadingExponents A).FG := by
  classical
  rw [← exists_finite_isSAGBIBasis_iff_fg]
  refine ⟨fun ⟨B, _, hB⟩ ↦ ⟨B, B.finite_toSet, hB⟩, fun ⟨B, hBfin, hB⟩ ↦ ?_⟩
  refine ⟨(hBfin.toFinset.erase 0).image m.monicNormalize, ?_, ?_⟩
  · intro g hg
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hg
    exact monic_monicNormalize (Finset.mem_erase.1 hp).1
  · rw [Finset.coe_image, Finset.coe_erase, hBfin.coe_toFinset,
      isSAGBIBasis_image_monicNormalize_iff]
    exact isSAGBIBasis_sdiff_singleton_zero.2 hB

end Field

end MonomialOrder
