/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.Coproduct
public import TauCeti.Algebra.Homology.DerivedCategory.HomologyIn
public import TauCeti.Algebra.Homology.ModelCategory.KInjective.Resolution
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.WeakSerre

/-!
# The derived category of complexes with quasi-coherent cohomology

Let `X` be a scheme. This file defines `TauCeti.AlgebraicGeometry.Coherent.DQCoh X`, the full
subcategory `D_QCoh(𝒪_X)` of the derived category `D(𝒪_X)` of all `𝒪_X`-modules consisting of the
complexes all of whose cohomology sheaves are quasi-coherent. It is the property
`DerivedCategory.homologyIn` for quasi-coherence, and works for any model of the derived category
(`HasDerivedCategory`).

* `DQCoh.mem_iff`: membership is quasi-coherence of all cohomology sheaves.
* `DQCoh.isTriangulated`: `D_QCoh(𝒪_X)` is a triangulated subcategory, closed under shifts and
  cones. Quasi-coherent sheaves are closed under kernels, cokernels and extensions in all
  `𝒪_X`-modules.
* `DQCoh.isClosedUnderCoproducts` and `DQCoh.hasCoproducts`: `D(𝒪_X)` has coproducts indexed by
  `u`-small types, computed by degreewise direct sums of complexes, and `D_QCoh(𝒪_X)` is closed
  under them. Hence `D_QCoh(𝒪_X)` has these coproducts, computed in `D(𝒪_X)`.
* `DQCoh.singleFunctor_obj_mem_iff`: a module sheaf placed in one degree lies in `D_QCoh(𝒪_X)` if
  and only if it is quasi-coherent; for instance `𝒪_X[0] ∈ D_QCoh(𝒪_X)`.
* `DQCoh.restrict`: derived restriction along an open immersion preserves `D_QCoh`, and
  `DQCoh.mem_iff_of_iSup_eq_top`: membership in `D_QCoh(𝒪_X)` is local on `X`.
* `DQCoh.mapDerivedCategory_tildeFunctor_obj`: for a commutative ring `A`, the derived functor of
  `M ↦ M~` sends `D(A)` into `D_QCoh(𝒪_{Spec A})`, the easy half of the equivalence
  `D(A) ≌ D_QCoh(𝒪_{Spec A})` of [Stacks, Lemma 36.3.5](https://stacks.math.columbia.edu/tag/06Z0).

The category of `𝒪_X`-modules is a Grothendieck abelian category, so it has K-injective
resolutions and exact coproducts; these give the coproducts in `D(𝒪_X)` and their homology.

## References

* [Stacks: Section 36.3](https://stacks.math.columbia.edu/tag/06YZ), the definition of `D_QCoh`.
* [Stacks: Lemma 36.3.1](https://stacks.math.columbia.edu/tag/08DT), direct sums in `D_QCoh`.
-/

public section

open CategoryTheory Limits DerivedCategory

namespace TauCeti.AlgebraicGeometry.Coherent

open _root_.AlgebraicGeometry

universe w w' u

section

variable (X : Scheme.{u}) [HasDerivedCategory.{w} X.Modules]

/-- `D_QCoh(𝒪_X)`: the objects of the derived category of `𝒪_X`-modules all of whose cohomology
sheaves are quasi-coherent. -/
def DQCoh : ObjectProperty (DerivedCategory X.Modules) :=
  homologyIn (Scheme.Modules.isQuasicoherent X)

variable {X} in
/-- An object of `D(𝒪_X)` lies in `D_QCoh(𝒪_X)` if and only if all its cohomology sheaves are
quasi-coherent. -/
theorem DQCoh.mem_iff {K : DerivedCategory X.Modules} :
    DQCoh X K ↔ ∀ n : ℤ, ((homologyFunctor X.Modules n).obj K).IsQuasicoherent :=
  homologyIn_iff K

/-- Membership in `D_QCoh(𝒪_X)` is invariant under isomorphism in `D(𝒪_X)`. -/
instance : (DQCoh X).IsClosedUnderIsomorphisms :=
  inferInstanceAs (homologyIn (Scheme.Modules.isQuasicoherent X)).IsClosedUnderIsomorphisms

/-- `D_QCoh(𝒪_X)` is a triangulated subcategory of `D(𝒪_X)`: it contains zero and is closed under
shifts and extensions, hence under cones. -/
instance DQCoh.isTriangulated : (DQCoh X).IsTriangulated :=
  inferInstanceAs (homologyIn (Scheme.Modules.isQuasicoherent X)).IsTriangulated

/-- `D_QCoh(𝒪_X)` is closed under the coproducts of `D(𝒪_X)` indexed by `u`-small types. -/
instance DQCoh.isClosedUnderCoproducts (J : Type u) :
    (DQCoh X).IsClosedUnderColimitsOfShape (Discrete J) :=
  inferInstanceAs
    ((homologyIn (Scheme.Modules.isQuasicoherent X)).IsClosedUnderColimitsOfShape (Discrete J))

/-- `D_QCoh(𝒪_X)` has coproducts indexed by `u`-small types, computed in `D(𝒪_X)`. -/
instance DQCoh.hasCoproducts : HasCoproducts.{u} (DQCoh X).FullSubcategory :=
  ⟨fun _ ↦ hasColimitsOfShape_of_closedUnderColimits _ _⟩

variable {X} in
/-- A sheaf of modules placed in one degree lies in `D_QCoh(𝒪_X)` if and only if it is
quasi-coherent. -/
@[simp]
theorem DQCoh.singleFunctor_obj_mem_iff (F : X.Modules) (n : ℤ) :
    DQCoh X ((singleFunctor X.Modules n).obj F) ↔ F.IsQuasicoherent :=
  homologyIn_singleFunctor_obj_iff (P := Scheme.Modules.isQuasicoherent X) F n

end

section Restriction

variable {X U : Scheme.{u}} [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w'} U.Modules]

/-- Derived restriction along an open immersion `f : U ⟶ X`, the functor `D(𝒪_X) ⥤ D(𝒪_U)` induced
by the exact restriction functor, sends `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_U)`. -/
theorem DQCoh.restrict (f : U ⟶ X) [IsOpenImmersion f] {K : DerivedCategory X.Modules}
    (hK : DQCoh X K) : DQCoh U ((Scheme.Modules.restrictFunctor f).mapDerivedCategory.obj K) :=
  homologyIn_mapDerivedCategory_obj (P := Scheme.Modules.isQuasicoherent X)
    (P' := Scheme.Modules.isQuasicoherent U) _
    (fun F (_ : F.IsQuasicoherent) ↦
      inferInstanceAs ((Scheme.Modules.restrictFunctor f).obj F).IsQuasicoherent) hK

end Restriction

/-- Membership in `D_QCoh(𝒪_X)` is local on `X`: for opens `U i` covering `X`, an object of
`D(𝒪_X)` lies in `D_QCoh(𝒪_X)` if and only if each of its restrictions to the `U i` lies in
`D_QCoh(𝒪_{U i})`. -/
theorem DQCoh.mem_iff_of_iSup_eq_top {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]
    {ι : Type*} (U : ι → X.Opens) (hU : iSup U = ⊤)
    [∀ i, HasDerivedCategory.{w'} (U i).toScheme.Modules] (K : DerivedCategory X.Modules) :
    DQCoh X K ↔ ∀ i,
      DQCoh (U i) ((Scheme.Modules.restrictFunctor (U i).ι).mapDerivedCategory.obj K) := by
  refine ⟨fun hK i ↦ DQCoh.restrict _ hK, fun hK ↦ DQCoh.mem_iff.2 fun n ↦ ?_⟩
  refine (((homologyFunctor X.Modules n).obj K).isQuasicoherent_iff_of_iSup_eq_top U hU).2
    fun i ↦ ?_
  exact (Scheme.Modules.isQuasicoherent _).prop_of_iso
    (((Scheme.Modules.restrictFunctor (U i).ι).mapDerivedCategoryCompHomologyFunctorIso n).app K)
    (DQCoh.mem_iff.1 (hK i) n)

/-- For a commutative ring `A`, the functor `D(A) ⥤ D(𝒪_{Spec A})` induced by the exact functor
`M ↦ M~` takes values in `D_QCoh(𝒪_{Spec A})`: the cohomology sheaves of `M~` are the sheaves
associated with the cohomology modules of `M`. -/
theorem DQCoh.mapDerivedCategory_tildeFunctor_obj (A : CommRingCat.{u})
    [HasDerivedCategory.{w} (Spec A).Modules] [HasDerivedCategory.{w'} (ModuleCat.{u} A)]
    (M : DerivedCategory (ModuleCat.{u} A)) :
    DQCoh (Spec A) ((tilde.functor A).mapDerivedCategory.obj M) :=
  homologyIn_mapDerivedCategory_obj (P := ⊤) (P' := Scheme.Modules.isQuasicoherent (Spec A)) _
    (fun N _ ↦ inferInstanceAs ((tilde.functor A).obj N).IsQuasicoherent)
    ((homologyIn_iff M).2 fun _ ↦ trivial)

end TauCeti.AlgebraicGeometry.Coherent
