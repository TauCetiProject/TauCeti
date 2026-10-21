/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Basic
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra.Corestrict
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra.LinearlyReductive

/-!
# Invariant rings of linearly reductive closed subgroups

The functions on an affine group invariant under a closed subgroup are the coinvariants
of its regular comodule algebra corestricted to the subgroup. This identifies the two
existing notions of coinvariants and applies Hilbert--Nagata finite generation and ideal
contraction to closed subgroups. Ideal contraction implies surjectivity on prime spectra,
without finite-type or reducedness assumptions.

The central inputs are `ComoduleAlgebra.finiteType_coinvariants` and
`ComoduleAlgebra.comap_map_coinvariants`, which use exactness of invariants.

## References

* S. Mukai, *An Introduction to Invariants and Moduli* (2003), §4.3.
* J. S. Milne, *Algebraic Groups* (2017), §12.
-/

public section

namespace TauCeti.HopfIdeal

universe u v

section Ring

variable {R : Type u} [CommRing R] {H : _root_.CommHopfAlgCat.{v} R}
  (I : HopfIdeal R H)

/-- Right-translation invariants are the coinvariants of the regular comodule algebra
corestricted to the quotient Hopf algebra of the subgroup. -/
theorem coinvariants_corestrict_regular :
    letI := ComoduleAlgebra.Corestrict (R := R) (A := H)
      (Bialgebra.Quotient.mkBialgHom (R := R) I.toIdeal)
    ComoduleAlgebra.coinvariants R (H ⧸ I.toIdeal) H = I.coinvariants := by
  let := ComoduleAlgebra.Corestrict (R := R) (A := H)
    (Bialgebra.Quotient.mkBialgHom (R := R) I.toIdeal)
  ext x
  simp only [ComoduleAlgebra.mem_coinvariants, ← ComoduleAlgebra.coactAlgHom_apply,
    ComoduleAlgebra.corestrict_coactAlgHom, ComoduleAlgebra.coactAlgHom_self,
    AlgHom.comp_apply, Bialgebra.Quotient.mkBialgHom_toAlgHom,
    Bialgebra.comulAlgHom_apply, mem_coinvariants_iff]

end Ring

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{v} k}
  (I : HopfIdeal k H)

/-- Invariants of a linearly reductive closed subgroup are finitely generated when the
ambient affine group is of finite type. -/
theorem finiteType_coinvariants_of_isLinearlyReductive [Algebra.FiniteType k H]
    (hI : Coalgebra.IsLinearlyReductive.{u, v, u} k (H ⧸ I.toIdeal)) :
    Algebra.FiniteType k I.coinvariants := by
  let := ComoduleAlgebra.Corestrict (R := k) (A := H)
    (Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal)
  have heq := I.coinvariants_corestrict_regular
  rw [← heq]
  exact ComoduleAlgebra.finiteType_coinvariants hI

/-- Every ideal of the functions invariant under a linearly reductive closed subgroup is
recovered by extending it to the ambient coordinate algebra and contracting it again. -/
theorem comap_map_coinvariants_of_isLinearlyReductive
    (hI : Coalgebra.IsLinearlyReductive.{u, v, u} k (H ⧸ I.toIdeal)) (J : Ideal I.coinvariants) :
    (J.map I.coinvariants.val.toRingHom).comap I.coinvariants.val.toRingHom = J := by
  let := ComoduleAlgebra.Corestrict (R := k) (A := H)
    (Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal)
  have heq := I.coinvariants_corestrict_regular
  have h := ComoduleAlgebra.comap_map_coinvariants (A := H) hI
  rw [heq] at h
  exact h J

/-- Every point of the invariant spectrum lifts to the ambient spectrum for a linearly
reductive subgroup. This does not require reducedness or finite type. -/
theorem surjective_comap_coinvariants_of_isLinearlyReductive
    (hI : Coalgebra.IsLinearlyReductive.{u, v, u} k (H ⧸ I.toIdeal)) :
    Function.Surjective (PrimeSpectrum.comap I.coinvariants.val.toRingHom) := by
  intro p
  have hc := I.comap_map_coinvariants_of_isLinearlyReductive hI p.asIdeal
  obtain ⟨Q, hQ, hprime, hle⟩ := p.asIdeal.exists_ideal_comap_le_prime
    (p.asIdeal.map I.coinvariants.val.toRingHom) hc.le
  refine ⟨⟨Q, hprime⟩, PrimeSpectrum.ext (le_antisymm hle ?_)⟩
  exact Ideal.map_le_iff_le_comap.mp hQ

end TauCeti.HopfIdeal
