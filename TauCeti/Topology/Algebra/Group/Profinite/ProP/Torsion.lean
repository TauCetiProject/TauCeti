/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Cyclic.ElementaryDivisors
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.StructureTheorem
public import TauCeti.Topology.Algebra.Group.Torsion
import TauCeti.NumberTheory.Padics.Module
import TauCeti.Topology.Algebra.ContinuousMulEquiv

/-!
# The torsion subgroup of a topologically finitely generated abelian pro-`p` group

The structure theorem identifies a topologically finitely generated abelian pro-`p` group `A`
with `ℤ_p ^ r × T` for a finite abelian `p`-group `T`. This file describes the two factors of
that decomposition and proves uniqueness of the rank and elementary divisors.

* The finite factor `T` is the torsion subgroup of `A`. Consequently the torsion subgroup is
  finite and closed, and it is open exactly when `A` is finite.
* The quotient `A ⧸ torsion A` is topologically isomorphic to `ℤ_p ^ r`; in particular a
  torsion-free topologically finitely generated abelian pro-`p` group is `ℤ_p ^ r`.
* The rank is unique: in any two decompositions `A ≅ ℤ_p ^ r × T ≅ ℤ_p ^ r' × T'` with `T` and
  `T'` torsion, `r = r'`, because both `ℤ_p ^ r` and `ℤ_p ^ r'` are the quotient by the torsion
  subgroup and a continuous additive isomorphism `ℤ_p ^ r ≃ ℤ_p ^ r'` is `ℤ_p`-linear. The
  uniqueness of the torsion factor, `T ≅ T'`, needs no pro-`p` hypothesis and is
  `TauCeti.torsionFactorAddEquiv` in `TauCeti.GroupTheory.Torsion`.
* When the finite factors are products of `ZMod (p ^ e i)` with positive exponents, that
  torsion-factor equivalence determines the exponents up to a bijection of the index types.

Finiteness of the torsion subgroup is what makes the torsion subgroup of the abelianisation of a
topologically finitely generated pro-`p` group a finite invariant; the `q`-invariant of a Demushkin
group is read off from it.

## Main results

* `TauCeti.IsProP.finite_torsion`, `TauCeti.IsProP.isClosed_torsion`,
  `TauCeti.IsProP.isOpen_torsion_iff_finite`: the torsion subgroup is finite, closed, and open
  exactly when the group is finite.
* `TauCeti.IsProP.exists_continuousMulEquiv_pi_padicInt`: a torsion-free topologically finitely
  generated abelian pro-`p` group is topologically isomorphic to `ℤ_p ^ r`.
* `TauCeti.IsProP.exists_continuousMulEquiv_quotient_torsion_pi_padicInt`: the quotient by the
  torsion subgroup is topologically isomorphic to `ℤ_p ^ r`.
* `TauCeti.eq_of_continuousMulEquiv_pi_padicInt_prod`: uniqueness of the rank `r`.
* `TauCeti.exists_equiv_exponents_of_continuousMulEquiv_pi_padicInt_prod_pi_zmod`:
  uniqueness of the positive elementary-divisor exponents up to reindexing.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 4.3.
-/

public section

namespace TauCeti

open CommGroup (torsion)
open Multiplicative

variable {p : ℕ} [Fact p.Prime]

section Uniqueness

variable {A : Type*} [CommGroup A] [TopologicalSpace A]

/-- **Uniqueness of the rank in the structure theorem.** Two decompositions of a topological
abelian group as `ℤ_p ^ r × T` and `ℤ_p ^ r' × T'`, with `T` and `T'` torsion, have `r = r'`:
both `ℤ_p ^ r` and `ℤ_p ^ r'` are the quotient by the torsion subgroup. -/
theorem eq_of_continuousMulEquiv_pi_padicInt_prod {r r' : ℕ} {T T' : Type*} [AddCommGroup T]
    [TopologicalSpace T] [AddCommGroup T'] [TopologicalSpace T'] (hT : IsAddTorsion T)
    (hT' : IsAddTorsion T') (e : A ≃ₜ* Multiplicative ((Fin r → ℤ_[p]) × T))
    (e' : A ≃ₜ* Multiplicative ((Fin r' → ℤ_[p]) × T')) : r = r' :=
  eq_of_continuousMulEquiv_pi_padicInt
    ((quotientTorsionContinuousMulEquiv hT e).symm.trans (quotientTorsionContinuousMulEquiv hT' e'))

/-- Two decompositions into a finite power of `ℤ_p` and a finite product of nontrivial cyclic
`p`-groups have the same elementary-divisor exponents up to reindexing. The decompositions
themselves suffice; no compactness, finite-generation, or pro-`p` assumption on `A` is needed. -/
theorem exists_equiv_exponents_of_continuousMulEquiv_pi_padicInt_prod_pi_zmod
    {r r' : ℕ} {ι κ : Type*} [Finite ι] [Finite κ] (e : ι → ℕ) (e' : κ → ℕ)
    (he : ∀ i, 0 < e i) (he' : ∀ j, 0 < e' j)
    (f : A ≃ₜ* Multiplicative ((Fin r → ℤ_[p]) × ((i : ι) → ZMod (p ^ e i))))
    (f' : A ≃ₜ* Multiplicative ((Fin r' → ℤ_[p]) × ((j : κ) → ZMod (p ^ e' j)))) :
    ∃ σ : ι ≃ κ, ∀ i, e i = e' (σ i) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact ZMod.exists_equiv_exponents_of_pi_pow_addEquiv (Fact.out : p.Prime).one_lt e e' he he'
    (torsionFactorAddEquiv isAddTorsion_of_finite isAddTorsion_of_finite
      f.toMulEquiv f'.toMulEquiv)

end Uniqueness

namespace IsProP

variable {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A]
  [TotallyDisconnectedSpace A]

/-- **The torsion subgroup of a topologically finitely generated abelian pro-`p` group is
finite**: it is the finite factor of the structure theorem. -/
theorem finite_torsion (hA : IsProP p A) (hfg : IsTopologicallyFinitelyGenerated A) :
    Finite (torsion A) := by
  obtain ⟨r, m, e, -, ⟨f⟩⟩ := hA.exists_continuousMulEquiv_pi_padicInt_prod_pi_zmod hfg
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact Finite.of_equiv _ (torsionMulEquiv isAddTorsion_of_finite f.toMulEquiv).symm.toEquiv

/-- The torsion subgroup of a topologically finitely generated abelian pro-`p` group is closed. -/
theorem isClosed_torsion (hA : IsProP p A) (hfg : IsTopologicallyFinitelyGenerated A) :
    IsClosed ((torsion A : Subgroup A) : Set A) :=
  haveI := hA.finite_torsion hfg
  (Set.toFinite _).isClosed

/-- The torsion subgroup of a topologically finitely generated abelian pro-`p` group is open
exactly when the group is finite, that is when the free rank of the structure theorem is `0`. -/
theorem isOpen_torsion_iff_finite (hA : IsProP p A) (hfg : IsTopologicallyFinitelyGenerated A) :
    IsOpen ((torsion A : Subgroup A) : Set A) ↔ Finite A := by
  refine ⟨fun h ↦ ?_, fun _ ↦ isOpen_discrete _⟩
  have := hA.finite_torsion hfg
  have := (torsion A).quotient_finite_of_isOpen h
  exact Finite.of_subgroup_quotient (torsion A)

/-- **Structure theorem for torsion-free topologically finitely generated abelian pro-`p`
groups.** Such a group is topologically isomorphic to `ℤ_p ^ r`. -/
theorem exists_continuousMulEquiv_pi_padicInt [IsMulTorsionFree A] (hA : IsProP p A)
    (hfg : IsTopologicallyFinitelyGenerated A) :
    ∃ r : ℕ, Nonempty (A ≃ₜ* Multiplicative (Fin r → ℤ_[p])) := by
  obtain ⟨r, m, e, -, ⟨f⟩⟩ := hA.exists_continuousMulEquiv_pi_padicInt_prod_pi_zmod hfg
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- The finite factor is the torsion subgroup of `A`, hence trivial.
  have := subsingleton_of_mulEquiv isAddTorsion_of_finite f.toMulEquiv
  let _ : Unique ((i : Fin m) → ZMod (p ^ e i)) := uniqueOfSubsingleton 0
  exact ⟨r, ⟨f.trans (ContinuousMulEquiv.multiplicativeProdUnique _ _)⟩⟩

/-- **The torsion-free quotient of a topologically finitely generated abelian pro-`p` group is
`ℤ_p ^ r`.** The quotient by the torsion subgroup is topologically isomorphic to the free factor of
the structure theorem. -/
theorem exists_continuousMulEquiv_quotient_torsion_pi_padicInt (hA : IsProP p A)
    (hfg : IsTopologicallyFinitelyGenerated A) :
    ∃ r : ℕ, Nonempty (A ⧸ torsion A ≃ₜ* Multiplicative (Fin r → ℤ_[p])) := by
  obtain ⟨r, m, e, -, ⟨f⟩⟩ := hA.exists_continuousMulEquiv_pi_padicInt_prod_pi_zmod hfg
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact ⟨r, ⟨quotientTorsionContinuousMulEquiv isAddTorsion_of_finite f⟩⟩

end IsProP

end TauCeti
