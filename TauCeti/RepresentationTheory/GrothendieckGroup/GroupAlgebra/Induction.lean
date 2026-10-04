/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.FiniteIndex
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.CoextendScalars
public import TauCeti.Algebra.MonoidAlgebra.CosetBasis
public import TauCeti.Algebra.MonoidAlgebra.Finite
public import TauCeti.RepresentationTheory.Coinduced
public import TauCeti.RepresentationTheory.Induction.FiniteDimensional.Basic
public import TauCeti.RepresentationTheory.Induction.Permutation

/-!
# Induction between Grothendieck groups of group algebras

Let `S` be a subgroup of a finite group `G` and `k` a commutative ring. The group algebra `k[G]`
is a free `k[S]`-module of finite rank, with a basis indexed by the cosets of `S`
(`TauCeti.MonoidAlgebra.basisCosets`). Hence coextension of scalars
`M ↦ Hom_{k[S]}(k[G], M)` is exact and preserves finite generation, and it descends to the
exact Grothendieck groups of finitely generated modules:

```text
ind S : G₀(k[S]) →+ G₀(k[G]),   [M] ↦ [Hom_{k[S]}(k[G], M)].
```

The module `Hom_{k[S]}(k[G], M)` is the coinduced module, and since `S` has finite index it is
isomorphic to the induced module. So on the class of a representation `ρ` of `S`, `ind S` is the
class of the induced representation `Ind_S^G ρ` (`TauCeti.indK0_of_asModule_of_equiv`), in
particular of Tau Ceti's finite-dimensional induction `TauCeti.indFDRep` over a field
(`TauCeti.indK0_of_indFDRep`), and the class of the trivial line goes to the class of the
permutation module `k[G ⧸ S]` (`TauCeti.indK0_of_trivial`).

The exactness of induction is what makes `ind S` well defined on the exact Grothendieck group,
whose relations come from all short exact sequences, including the non-split ones that occur when
the characteristic of `k` divides the order of `G`.

## Main definitions

* `TauCeti.indK0`: induction from a subgroup as a homomorphism of exact Grothendieck groups of
  finitely generated group-algebra modules.

## Main results

* `TauCeti.indK0_of`: the class of a module goes to the class of its coinduced module.
* `TauCeti.indK0_of_asModule_of_equiv`: the class of a representation goes to the class of any
  representation equivalent to its induced representation.
* `TauCeti.indK0_of_trivial`: the class of the trivial line goes to the class of the permutation
  module on the cosets.
* `TauCeti.indK0_of_ofMulAction_quotient`: for `D ≤ S`, the class of the permutation module
  `k[S ⧸ (D ⊓ S)]` goes to the class of the permutation module `k[G ⧸ D]`.
* `TauCeti.indK0_of_indFDRep`: over a field, the class of a finite-dimensional representation goes
  to the class of `TauCeti.indFDRep` of it.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.1, for the induction
  homomorphism `R_k(H) → R_k(G)`.
-/

public section

open CategoryTheory
open scoped MonoidAlgebra

namespace TauCeti

universe u

section CommRing

variable (k : Type u) [CommRing k] {G : Type u} [Group G] [Finite G] (S : Subgroup G)

/-- **Induction on the Grothendieck group of a group algebra.** For a subgroup `S` of a finite
group `G`, coinduction `M ↦ Hom_{k[S]}(k[G], M)` of finitely generated `k[S]`-modules is exact,
so it induces `G₀(k[S]) →+ G₀(k[G])`. Since `S` has finite index, the coinduced module is the
induced one (`TauCeti.indK0_of_asModule_of_equiv`). -/
noncomputable def indK0 :
    ExactK0 (finiteModulesExactStructure k[S]) →+ ExactK0 (finiteModulesExactStructure k[G]) :=
  (MonoidAlgebra.mapDomainAlgHom k k S.subtype).finiteModulesK0Coextend
    (letI := (MonoidAlgebra.mapDomainRingHom k S.subtype).toModule;
      .of_basis (MonoidAlgebra.basisCosets k S.subtype S.subtype_injective))
    (MonoidAlgebra.mapDomainRingHom_moduleFinite_of_finite S.subtype)

/-- Induction sends the class of a module `M` to the class of its coinduced module
`Hom_{k[S]}(k[G], M)`. -/
@[simp]
theorem indK0_of (M : FGModuleCat.{u} k[S]) :
    indK0 k S (ExactK0.of M) =
      ExactK0.of (((MonoidAlgebra.mapDomainAlgHom k k S.subtype).finiteModulesCoextendScalars
        (letI := (MonoidAlgebra.mapDomainRingHom k S.subtype).toModule;
          .of_basis (MonoidAlgebra.basisCosets k S.subtype S.subtype_injective))
        (MonoidAlgebra.mapDomainRingHom_moduleFinite_of_finite S.subtype)).obj M) :=
  AlgHom.finiteModulesK0Coextend_of _ _ _ M

/-- **Induction of the class of a representation.** If `σ` is a representation of `G`
equivalent to the representation induced from a representation `ρ` of `S`, then induction sends
the class of the `k[S]`-module of `ρ` to the class of the `k[G]`-module of `σ`. The space of `σ`
is finite over `k` because the induced space is. -/
theorem indK0_of_asModule_of_equiv {V W : Type u} [AddCommGroup V] [Module k V]
    [Module.Finite k V] [AddCommGroup W] [Module k W]
    (ρ : Representation k S V) (σ : Representation k G W) (e : (ρ.ind S.subtype).Equiv σ) :
    letI : Module.Finite k[S] ρ.asModule := Module.Finite.of_restrictScalars_finite k k[S] _
    letI : Module.Finite k W := Module.Finite.equiv e.toLinearEquiv
    letI : Module.Finite k[G] σ.asModule := Module.Finite.of_restrictScalars_finite k k[G] _
    indK0 k S (ExactK0.of (FGModuleCat.of k[S] ρ.asModule)) =
      ExactK0.of (FGModuleCat.of k[G] σ.asModule) := by
  classical
  let : Module.Finite k[S] ρ.asModule := Module.Finite.of_restrictScalars_finite k k[S] _
  let : Module.Finite k W := Module.Finite.equiv e.toLinearEquiv
  let : Module.Finite k[G] σ.asModule := Module.Finite.of_restrictScalars_finite k k[G] _
  rw [indK0_of]
  -- The coinduced module is the module of `coind`, which is equivalent to `ind` and so to `σ`.
  refine ExactK0.of_congr (ObjectProperty.isoMk _
    ((AlgHom.finiteModulesCoextendScalarsCompιIso _ _ _).app _ ≪≫ LinearEquiv.toModuleIso
      ((Representation.coextendScalarsEquivCoind S.subtype ρ).trans
        ((Representation.asModuleLinearEquivOfEquiv
          (Representation.equivOfIso (Rep.indCoindIso (Rep.of ρ)))).symm.trans
            (Representation.asModuleLinearEquivOfEquiv e)))))

/-- **Induction of the trivial line.** Induction from `S` sends the class of the trivial
one-dimensional representation to the class of the permutation module `k[G ⧸ S]`. -/
@[simp high + 1]
theorem indK0_of_trivial :
    letI : Module.Finite k[S] (Representation.trivial k S k).asModule :=
      Module.Finite.of_restrictScalars_finite k k[S] _
    letI : Module.Finite k[G] (Representation.ofMulAction k G (G ⧸ S)).asModule :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    indK0 k S (ExactK0.of (FGModuleCat.of k[S] (Representation.trivial k S k).asModule)) =
      ExactK0.of (FGModuleCat.of k[G] (Representation.ofMulAction k G (G ⧸ S)).asModule) :=
  indK0_of_asModule_of_equiv k S _ _ (indTrivialEquiv k S)

/-- **Induction of a coset permutation module.** For a subgroup `D ≤ S`, induction from `S` sends
the class of the permutation module `k[S ⧸ (D ⊓ S)]` to the class of the permutation module
`k[G ⧸ D]`. -/
@[simp high]
theorem indK0_of_ofMulAction_quotient {D : Subgroup G} (h : D ≤ S) :
    letI : Module.Finite k[S] (Representation.ofMulAction k S (S ⧸ D.subgroupOf S)).asModule :=
      Module.Finite.of_restrictScalars_finite k k[S] _
    letI : Module.Finite k[G] (Representation.ofMulAction k G (G ⧸ D)).asModule :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    indK0 k S (ExactK0.of (FGModuleCat.of k[S]
        (Representation.ofMulAction k S (S ⧸ D.subgroupOf S)).asModule)) =
      ExactK0.of (FGModuleCat.of k[G] (Representation.ofMulAction k G (G ⧸ D)).asModule) :=
  indK0_of_asModule_of_equiv k S _ _ (indOfMulActionQuotientEquiv k h)

end CommRing

/-- **Induction of a finite-dimensional representation.** Over a field, induction from `S` sends
the class of a finite-dimensional representation `A` of `S` to the class of the induced
representation `TauCeti.indFDRep A`. -/
@[simp high]
theorem indK0_of_indFDRep (k : Type u) [Field k] {G : Type u} [Group G] [Finite G]
    {S : Subgroup G} (A : FDRep k S) :
    letI : Module.Finite k[S] (Representation.asModule A.ρ) :=
      Module.Finite.of_restrictScalars_finite k k[S] _
    letI : Module.Finite k[G] (Representation.asModule (indFDRep A).ρ) :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    indK0 k S (ExactK0.of (FGModuleCat.of k[S] (Representation.asModule A.ρ))) =
      ExactK0.of (FGModuleCat.of k[G] (Representation.asModule (indFDRep A).ρ)) :=
  indK0_of_asModule_of_equiv k S A.ρ (indFDRep A).ρ (indFDRepForgetEquiv A).symm

end TauCeti
