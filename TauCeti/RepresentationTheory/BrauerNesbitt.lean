/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.RepresentationTheory.BaseChange.Charpoly
public import TauCeti.RepresentationTheory.Semisimplification
public import TauCeti.RingTheory.Semisimple.Charpoly

/-!
# The Brauer–Nesbitt theorem for representations

Let `k` be an arbitrary field and `G` a monoid. Two finite-dimensional representations of `G` over
`k` with the same characteristic polynomial at every `g ∈ G` have equivalent semisimplifications
(`Representation.nonempty_equiv_semisimplification_iff_charpoly_eq`), and two such semisimple
representations are equivalent
(`Representation.nonempty_equiv_of_charpoly_eq_of_isSemisimpleRepresentation`). Equivalence of
semisimplifications can be tested after any extension of scalars
(`Representation.nonempty_equiv_semisimplification_baseChange_iff`). The continuous version is in
`TauCeti.RepresentationTheory.Continuous.BrauerNesbitt`.

The hypothesis concerns the elements of `G` only, not all of `k[G]`. Over an algebraic closure
`L` of `k` the semisimplifications of the scalar extensions are semisimple with the same
characteristic polynomials at the elements of `G`, so they are equivalent by the algebraically
closed case (`IsSemisimpleModule.nonempty_linearEquiv_of_charpoly_eq`). Hence every element of
`L[G]`, in particular every element of `k[G]` read in `L[G]`, acts on `L ⊗ V` and on `L ⊗ W` with
the same characteristic polynomial, and so every element of `k[G]` acts on `V` and on `W` with the
same characteristic polynomial (`Representation.charpoly_asAlgebraHom_eq_of_charpoly_eq`). Over
any field the characteristic polynomials of all elements of `k[G]` determine the
semisimplification (`TauCeti.nonempty_linearEquiv_semisimplification_iff_charpoly_eq`). No
perfectness of `k` is needed, although over an imperfect field a semisimple representation can
have a non-semisimple scalar extension: only semisimplifications are compared after the
extension.

In characteristic zero the characters already determine semisimple representations
(`Representation.nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation`). In characteristic
`p` they do not: over `𝔽₃` three copies of the trivial representation of `ℤ/2` and three copies of
its sign representation have equal characters, but the characteristic polynomials `(X - 1) ^ 3`
and `(X + 1) ^ 3` of the generator differ. Semisimplicity cannot be dropped: over `𝔽₂`, `ℤ/2`
acting trivially on `𝔽₂²` and by `!![1, 1; 0, 1]` has characteristic polynomial `(X - 1) ^ 2` at
every element, but only the first is semisimple.

## Main results

* `Representation.charpoly_asAlgebraHom_eq_of_charpoly_eq`: the characteristic polynomials at the
  elements of `G` determine those at all elements of `k[G]`.
* `Representation.nonempty_equiv_semisimplification_iff_charpoly_eq`: **Brauer–Nesbitt.** Over any
  field, `V^ss ≅ W^ss` if and only if every `g ∈ G` has the same characteristic polynomial on `V`
  and on `W`.
* `Representation.nonempty_equiv_of_charpoly_eq_of_isSemisimpleRepresentation` and
  `Representation.nonempty_equiv_iff_charpoly_eq_of_isSemisimpleRepresentation`: over any field,
  semisimple representations are equivalent if and only if they have the same characteristic
  polynomials.
* `Representation.nonempty_equiv_semisimplification_baseChange_iff`: for any field extension
  `L / k`, `(L ⊗ V)^ss ≅ (L ⊗ W)^ss` if and only if `V^ss ≅ W^ss`.

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, Proposition 2.6 and its proof.
* C. W. Curtis and I. Reiner, *Representation theory of finite groups and associative algebras*,
  Theorem 30.16.
* G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, arXiv:0809.0415v2, end of the proof of
  Theorem 2.12, for the descent of semisimplifications along a field extension.
-/

public section

open scoped MonoidAlgebra

namespace Representation

variable {k G V W : Type*} [Field k] [Monoid G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- **The characteristic polynomials at the elements of `G` determine those on `k[G]`.** If two
finite-dimensional representations of a monoid `G` over any field `k` have the same characteristic
polynomial at every `g ∈ G`, then every element of the monoid algebra `k[G]` acts on them with
the same characteristic polynomial. -/
theorem charpoly_asAlgebraHom_eq_of_charpoly_eq (ρ : Representation k G V)
    (σ : Representation k G W) (h : ∀ g, (ρ g).charpoly = (σ g).charpoly) (a : k[G]) :
    (ρ.asAlgebraHom a).charpoly = (σ.asAlgebraHom a).charpoly := by
  let L := AlgebraicClosure k
  have hspan : Submodule.span L (Set.range (MonoidAlgebra.of L G)) = ⊤ := by
    have hrange : Set.range (MonoidAlgebra.of L G) = Set.range (MonoidAlgebra.basis G L) := by
      ext
      simp [MonoidAlgebra.basis_apply]
    rw [hrange, Module.Basis.span_eq]
  -- Over `L` the semisimplifications of the scalar extensions are isomorphic.
  obtain ⟨e⟩ := IsSemisimpleModule.nonempty_linearEquiv_of_charpoly_eq (k := L)
    (M := TauCeti.semisimplification L[G] (ρ.baseChange L).asModule)
    (N := TauCeti.semisimplification L[G] (σ.baseChange L).asModule) hspan fun g => by
      rw [TauCeti.charpoly_lsmul_semisimplification, TauCeti.charpoly_lsmul_semisimplification,
        charpoly_lsmul_asModule_of, charpoly_lsmul_asModule_of, charpoly_baseChange_apply,
        charpoly_baseChange_apply, h]
  -- So `a`, read in `L[G]`, acts on `L ⊗ V` and on `L ⊗ W` with the same characteristic polynomial.
  have hL := e.charpoly_lsmul_eq (k := L) (MonoidAlgebra.mapAlgHom G (Algebra.ofId k L) a)
  rw [TauCeti.charpoly_lsmul_semisimplification, TauCeti.charpoly_lsmul_semisimplification,
    charpoly_lsmul_asModule, charpoly_lsmul_asModule, asAlgebraHom_baseChange_mapAlgHom,
    asAlgebraHom_baseChange_mapAlgHom, LinearMap.charpoly_baseChange,
    LinearMap.charpoly_baseChange] at hL
  exact Polynomial.map_injective _ (algebraMap k L).injective hL

/-- **Brauer–Nesbitt.** Over an arbitrary field, two finite-dimensional representations of a
monoid have equivalent semisimplifications if and only if every element of the monoid acts on them
with the same characteristic polynomial. -/
theorem nonempty_equiv_semisimplification_iff_charpoly_eq (ρ : Representation k G V)
    (σ : Representation k G W) :
    Nonempty (ρ.semisimplification.Equiv σ.semisimplification) ↔
      ∀ g, (ρ g).charpoly = (σ g).charpoly := by
  refine ⟨fun ⟨e⟩ g => ?_, fun h => ?_⟩
  · rw [← charpoly_semisimplification_apply, e.charpoly_apply_eq,
      charpoly_semisimplification_apply]
  · obtain ⟨e⟩ := (TauCeti.nonempty_linearEquiv_semisimplification_iff_charpoly_eq (k := k)
      (M := ρ.asModule) (N := σ.asModule)).mpr fun a => by
      rw [charpoly_lsmul_asModule, charpoly_lsmul_asModule,
        charpoly_asAlgebraHom_eq_of_charpoly_eq ρ σ h]
    exact TauCeti.Representation.nonempty_equiv_iff.mpr
      ⟨ρ.semisimplificationAsModuleEquiv ≪≫ₗ e ≪≫ₗ σ.semisimplificationAsModuleEquiv.symm⟩

/-- **Brauer–Nesbitt for semisimple representations.** Over an arbitrary field, two
finite-dimensional semisimple representations of a monoid with the same characteristic polynomial
at every element are equivalent. -/
theorem nonempty_equiv_of_charpoly_eq_of_isSemisimpleRepresentation (ρ : Representation k G V)
    (σ : Representation k G W) [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation]
    (h : ∀ g, (ρ g).charpoly = (σ g).charpoly) : Nonempty (ρ.Equiv σ) := by
  obtain ⟨e⟩ := (nonempty_equiv_semisimplification_iff_charpoly_eq ρ σ).mpr h
  obtain ⟨eρ⟩ := ρ.nonempty_equiv_semisimplification_iff.mpr ‹_›
  obtain ⟨eσ⟩ := σ.nonempty_equiv_semisimplification_iff.mpr ‹_›
  exact ⟨(eρ.symm.trans e).trans eσ⟩

/-- Over an arbitrary field, two finite-dimensional semisimple representations of a monoid are
equivalent if and only if they have the same characteristic polynomial at every element. -/
theorem nonempty_equiv_iff_charpoly_eq_of_isSemisimpleRepresentation (ρ : Representation k G V)
    (σ : Representation k G W) [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation] :
    Nonempty (ρ.Equiv σ) ↔ ∀ g, (ρ g).charpoly = (σ g).charpoly :=
  ⟨fun ⟨e⟩ => e.charpoly_apply_eq, nonempty_equiv_of_charpoly_eq_of_isSemisimpleRepresentation ρ σ⟩

/-- **Semisimplifications descend along field extensions.** For any field extension `L / k`, two
finite-dimensional representations over `k` have equivalent semisimplifications if and only if
their scalar extensions to `L` do. -/
theorem nonempty_equiv_semisimplification_baseChange_iff (L : Type*) [Field L] [Algebra k L]
    (ρ : Representation k G V) (σ : Representation k G W) :
    Nonempty ((ρ.baseChange L).semisimplification.Equiv (σ.baseChange L).semisimplification) ↔
      Nonempty (ρ.semisimplification.Equiv σ.semisimplification) := by
  simp_rw [nonempty_equiv_semisimplification_iff_charpoly_eq, charpoly_baseChange_apply,
    (Polynomial.map_injective _ (algebraMap k L).injective).eq_iff]

end Representation
