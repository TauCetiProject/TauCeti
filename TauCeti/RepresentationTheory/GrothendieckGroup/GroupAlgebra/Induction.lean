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
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Permutation.Basic
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Restriction
public import TauCeti.RepresentationTheory.Induction.FiniteDimensional.Basic
public import TauCeti.RepresentationTheory.Induction.Permutation
public import TauCeti.RepresentationTheory.OfModule

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
permutation module `k[G ⧸ S]`, that is, to the permutation class `TauCeti.permK0 k G (G ⧸ S)`
(`TauCeti.indK0_of_trivial`).

The exactness of induction is what makes `ind S` well defined on the exact Grothendieck group,
whose relations come from all short exact sequences, including the non-split ones that occur when
the characteristic of `k` divides the order of `G`.

Induction is transitive: for subgroups `S ≤ T` of `G`, inducing from `S` to `T` and then to `G`
is inducing from `S` to `G` (`TauCeti.indK0_indK0`). Since `G₀` of a subgroup of `T` is indexed by
`S.subgroupOf T` rather than by `S`, the statement transports classes between the two along the
isomorphism `Subgroup.subgroupOfEquivOfLe`, by restriction (`TauCeti.resK0`).

## Main definitions

* `TauCeti.indK0`: induction from a subgroup as a homomorphism of exact Grothendieck groups of
  finitely generated group-algebra modules.

## Main results

* `TauCeti.indK0_of`: the class of a module goes to the class of its coinduced module.
* `TauCeti.indK0_of_asModule_of_equiv`: the class of a representation goes to the class of any
  representation equivalent to its induced representation.
* `TauCeti.indK0_of_trivial`: the class of the trivial line goes to the permutation class of the
  cosets.
* `TauCeti.indK0_of_ofMulAction_quotient`: for `D ≤ S`, the class of the permutation module
  `k[S ⧸ (D ⊓ S)]` goes to the class of the permutation module `k[G ⧸ D]`.
* `TauCeti.indK0_of_indFDRep`: over a field, the class of a finite-dimensional representation goes
  to the class of `TauCeti.indFDRep` of it.
* `TauCeti.indK0_comp_indK0` and `TauCeti.indK0_indK0`: induction is transitive along a chain of
  subgroups `S ≤ T ≤ G`.

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
one-dimensional representation to the permutation class of `G ⧸ S`, the class of the permutation
module `k[G ⧸ S]`. -/
@[simp high + 1]
theorem indK0_of_trivial :
    letI : Module.Finite k[S] (Representation.trivial k S k).asModule :=
      Module.Finite.of_restrictScalars_finite k k[S] _
    indK0 k S (ExactK0.of (FGModuleCat.of k[S] (Representation.trivial k S k).asModule)) =
      permK0 k G (G ⧸ S) :=
  (indK0_of_asModule_of_equiv k S _ _ (indTrivialEquiv k S)).trans (permK0_def k (G ⧸ S)).symm

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

/-- **Induction is transitive.** For subgroups `S ≤ T` of `G`, inducing from `S.subgroupOf T` to
`T` and then from `T` to `G` is inducing from `S` to `G`, after transporting classes from
`S.subgroupOf T` to `S` by restriction along `Subgroup.subgroupOfEquivOfLe`. -/
theorem indK0_comp_indK0 {T : Subgroup G} (h : S ≤ T) :
    (indK0 k T).comp (indK0 k (S.subgroupOf T)) =
      (indK0 k S).comp (resK0 k (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom) := by
  ext M
  -- Write `M` as the module of the representation `ρ` it defines.
  let := Module.restrictScalars k k[S.subgroupOf T] M.obj
  have := IsScalarTower.restrictScalars k k[S.subgroupOf T] M.obj
  have : Module.Finite k[S.subgroupOf T] M.obj := M.2
  have : Module.Finite k M.obj := Module.Finite.trans k[S.subgroupOf T] M.obj
  let ρ := Representation.ofModule' (k := k) (G := S.subgroupOf T) M.obj
  have : Module.Finite k[S.subgroupOf T] ρ.asModule :=
    Module.Finite.of_restrictScalars_finite k _ ρ.asModule
  have hM : (ExactK0.of M : ExactK0 (finiteModulesExactStructure k[S.subgroupOf T])) =
      ExactK0.of (FGModuleCat.of _ ρ.asModule) :=
    ExactK0.of_congr (Representation.ofModule'AsModuleEquiv M.obj).symm.toFGModuleCatIso
  -- Both sides are the class of `Ind_T (Ind_{S.subgroupOf T} ρ)`; on the right this is
  -- induction in stages, `TauCeti.Rep.indFunctorSubgroupOfIso`.
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, hM]
  rw [resK0_of_asModule, indK0_of_asModule_of_equiv k S _ _
      (Representation.equivOfIso ((Rep.indFunctorSubgroupOfIso h).app (Rep.of ρ)).symm),
    indK0_of_asModule_of_equiv k (S.subgroupOf T) ρ _ (Representation.Equiv.refl _),
    indK0_of_asModule_of_equiv k T _ _ (Representation.Equiv.refl _)]
  -- `Rep.indFunctor_obj` unfolds the functor-composite form to the representation-level form.
  simp only [Functor.comp_obj, Rep.indFunctor_obj]

/-- **Induction is transitive**, on classes: `TauCeti.indK0_comp_indK0` evaluated at `x`. -/
theorem indK0_indK0 {T : Subgroup G} (h : S ≤ T)
    (x : ExactK0 (finiteModulesExactStructure k[S.subgroupOf T])) :
    indK0 k T (indK0 k (S.subgroupOf T) x) =
      indK0 k S (resK0 k (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom x) :=
  DFunLike.congr_fun (indK0_comp_indK0 k S h) x

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
