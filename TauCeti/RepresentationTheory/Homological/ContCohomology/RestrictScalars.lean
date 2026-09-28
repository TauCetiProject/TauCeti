/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ShortComplex.PreservesHomology
public import TauCeti.RepresentationTheory.Continuous.TopRep.RestrictScalars
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete

/-!
# Continuous cohomology does not see the scalars

Mathlib's `continuousCohomology n X`, for `X : TopRep k G`, is the homology of the complex of
homogeneous cochains, a complex of topological `k`-modules built from the iterated coinduction
`C(G, C(G, …, X.V))` and its invariants. Forgetting the scalars, that is reading `X` as a
continuous representation on the underlying topological abelian group `X.V`, gives an object
`TopRep.restrictScalarsInt.obj X` of `TopRep ℤ G`, and this file proves that its continuous
cohomology is the underlying topological abelian group of the continuous cohomology of `X`:

```text
continuousCohomology n (TopRep.restrictScalarsInt.obj X)
  ≅ TopModuleCat.restrictScalarsInt.obj (continuousCohomology n X).
```

The identification is available at every level of the construction, not only on cohomology: the
coinduced resolution of the underlying additive representation is the underlying additive
resolution (`TopRep.resolutionXRestrictScalarsIntIso`, compatible with the differentials), the
complex of homogeneous cochains of the underlying additive representation is the image of the
complex of homogeneous cochains under the functor forgetting the scalars
(`TopRep.homogeneousCochainsRestrictScalarsIntIso`), and the cocycles are identified by
`TauCeti.ContCohomology.cocyclesRestrictScalarsIntIso`. A consumer holding a cocycle of `X` can
read it as a cocycle of the underlying additive representation and compare the two classes through
`TauCeti.ContCohomology.π_comp_restrictScalarsIntIso_hom`.

The point of the statement is that the calculus of continuous cohomology, with its explicit low
degree cocycles, its long exact sequences and its comparison with discrete group cohomology, is
developed for coefficients in `TopRep ℤ G`, in particular for the discrete modules
`TauCeti.ofDiscreteModule ℤ G M`, while the coefficient objects of the pro-`p` theory, such as the
trivial representation on `𝔽_p`, are objects of `TopRep (ZMod p) G` so that their cohomology is a
vector space over `𝔽_p`. The isomorphism here, together with
`TauCeti.ContCohomology.ofDiscreteModule_eq_restrictScalarsInt_obj`, which identifies the
underlying additive representation of a discrete `X` with `TauCeti.ofDiscreteModule ℤ G X.V`, is
what lets every result of the first kind be applied to coefficients of the second kind.

## Main definitions

* `TopRep.resolutionXRestrictScalarsIntIso`: the coinduced resolution of the underlying additive
  representation is the underlying additive resolution.
* `TopRep.homogeneousCochainsRestrictScalarsIntIso`: the homogeneous cochains of the underlying
  additive representation are the image of the homogeneous cochains under forgetting the scalars.
* `TauCeti.ContCohomology.restrictScalarsIntIso`: continuous cohomology commutes with forgetting
  the scalars, as an isomorphism in `TopModuleCat ℤ`;
  `TauCeti.ContCohomology.cocyclesRestrictScalarsIntIso` is the corresponding identification of
  the cocycles.
* `TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntIso`: for a discrete `X`, the
  continuous cohomology of `ofDiscreteModule ℤ G X.V` is the underlying topological abelian group
  of the continuous cohomology of `X`; `subsingleton_continuousCohomology_ofDiscreteModule_iff`
  and `nontrivial_continuousCohomology_ofDiscreteModule_iff` read it on vanishing, and
  `TauCeti.ContCohomology.ofDiscreteModuleCocyclesRestrictScalarsIntIso` is the corresponding
  identification of the cocycles.

## Main results

* `TopRep.d_comp_resolutionXRestrictScalarsIntIso_hom`: the identification of the resolutions
  commutes with the differentials.
* `TauCeti.ContCohomology.π_comp_restrictScalarsIntIso_hom`: the isomorphism carries the class of
  a cocycle to the class of the corresponding cocycle, and
  `TauCeti.ContCohomology.cocyclesRestrictScalarsIntIso_hom_comp_map_iCycles` identifies the
  corresponding cocycle as the same homogeneous cochain;
  `TauCeti.ContCohomology.π_comp_ofDiscreteModuleRestrictScalarsIntIso_hom` and
  `TauCeti.ContCohomology.iCycles_ofDiscreteModuleCocyclesRestrictScalarsIntIso_hom_apply` are
  the corresponding statements for a discrete `X`.
* `TauCeti.ContCohomology.coeffMap_comp_restrictScalarsIntIso_hom`: the isomorphism is natural in
  the representation, with respect to the coefficient maps
  `TauCeti.ContinuousCohomology.coeffMap`;
  `TopRep.cochainsMap_comp_homogeneousCochainsRestrictScalarsIntIso_hom` and
  `TauCeti.ContCohomology.cocyclesMap_comp_cocyclesRestrictScalarsIntIso_hom` are the
  corresponding statements for the cochains and the cocycles.
* `TauCeti.ContCohomology.ofDiscreteModule_eq_restrictScalarsInt_obj`: for a discrete `X`, the
  underlying additive representation is `TauCeti.ofDiscreteModule ℤ G X.V`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2: the
  cohomology of a profinite group with coefficients in a discrete module is computed by continuous
  cochains valued in the underlying abelian group; no scalars enter the construction.
-/

public section

open CategoryTheory ContRepresentation

namespace TopRep

variable {k : Type*} [Ring k] [TopologicalSpace k] {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-! ### The resolution -/

/-- The coinduced resolution of the underlying additive representation of `X` is the underlying
additive resolution of `X`, degree by degree: in degree `n` both sides are the representation on
the iterated function space `C(G, C(G, …, X.V))`. -/
noncomputable def resolutionXRestrictScalarsIntIso (X : TopRep k G) :
    ∀ n : ℕ, resolutionX (restrictScalarsInt.obj X) n ≅ restrictScalarsInt.obj (resolutionX X n)
  | 0 => Iso.refl _
  | n + 1 =>
    (coind₁Functor ℤ G).mapIso (resolutionXRestrictScalarsIntIso X n) ≪≫
      coind₁RestrictScalarsIntIso (resolutionX X n)

/-- In degree zero the identification of the resolutions is the identity. -/
@[simp]
theorem resolutionXRestrictScalarsIntIso_zero (X : TopRep k G) :
    resolutionXRestrictScalarsIntIso X 0 = Iso.refl _ :=
  (rfl)

/-- In degree `n + 1` the identification of the resolutions is the coinduction of the
identification in degree `n`, followed by the identification of the coinduced representations. -/
theorem resolutionXRestrictScalarsIntIso_succ (X : TopRep k G) (n : ℕ) :
    resolutionXRestrictScalarsIntIso X (n + 1) =
      (coind₁Functor ℤ G).mapIso (resolutionXRestrictScalarsIntIso X n) ≪≫
        coind₁RestrictScalarsIntIso (resolutionX X n) :=
  (rfl)

/-- The identification of the resolutions commutes with the differentials of the resolution. -/
@[reassoc]
theorem d_comp_resolutionXRestrictScalarsIntIso_hom (X : TopRep k G) (n : ℕ) :
    d (restrictScalarsInt.obj X) n ≫ (resolutionXRestrictScalarsIntIso X (n + 1)).hom =
      (resolutionXRestrictScalarsIntIso X n).hom ≫ restrictScalarsInt.map (d X n) := by
  -- `simp` cannot drive the inductive step: `coind₁Functor` is an abbreviation, which `simp`
  -- unfolds to `ofHom (coind₁Map _)` before the naturality lemmas, stated for
  -- `(coind₁Functor ℤ G).map`, can apply. The rewrites below unfold the two recursions,
  -- reassociate, and apply those lemmas.
  induction n with
  | zero =>
    simp only [resolutionXRestrictScalarsIntIso_succ, resolutionXRestrictScalarsIntIso_zero,
      d_zero, Iso.trans_hom, Functor.mapIso_hom, Iso.refl_hom, Category.id_comp]
    exact coind₁ι_comp_coind₁RestrictScalarsIntIso_hom X
  | succ n ih =>
    rw [d_succ, d_succ, resolutionXRestrictScalarsIntIso_succ X (n + 1), Iso.trans_hom,
      Functor.mapIso_hom, Preadditive.sub_comp, Functor.map_sub, Preadditive.comp_sub]
    congr 1
    · -- the unit `coind₁ι` is natural, and compatible with forgetting the scalars
      rw [← coind₁ι_app, ← coind₁ι_app, ← NatTrans.naturality_assoc, Functor.id_map, coind₁ι_app,
        coind₁ι_app, coind₁ι_comp_coind₁RestrictScalarsIntIso_hom]
    · -- the coinduction of the differential, by the induction hypothesis
      rw [← Functor.map_comp_assoc, ih, Functor.map_comp_assoc,
        coind₁Functor_map_comp_coind₁RestrictScalarsIntIso_hom,
        resolutionXRestrictScalarsIntIso_succ X n, Iso.trans_hom, Functor.mapIso_hom,
        Category.assoc]

/-! ### The homogeneous cochains -/

/-- The complex of homogeneous cochains of the underlying additive representation of `X` is the
image of the complex of homogeneous cochains of `X` under the functor forgetting the scalars. -/
noncomputable def homogeneousCochainsRestrictScalarsIntIso (X : TopRep k G) :
    homogeneousCochains (restrictScalarsInt.obj X) ≅
      (TopModuleCat.restrictScalarsInt.mapHomologicalComplex _).obj (homogeneousCochains X) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (invariantsFunctor ℤ G).mapIso (resolutionXRestrictScalarsIntIso X (n + 1)) ≪≫
      invariantsRestrictScalarsIntIso (resolutionX X (n + 1)))
    (by
      rintro i j (rfl : i + 1 = j)
      rw [Functor.mapHomologicalComplex_obj_d, homogeneousCochains.d_eq,
        homogeneousCochains.d_eq, Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom,
        Functor.mapIso_hom, Category.assoc, invariantsRestrictScalarsIntIso_hom_comp_map,
        ← Functor.map_comp_assoc, ← d_comp_resolutionXRestrictScalarsIntIso_hom,
        Functor.map_comp_assoc])

/-- The component in degree `n` of `homogeneousCochainsRestrictScalarsIntIso` is the identification
of the invariants of the identified resolutions. -/
theorem homogeneousCochainsRestrictScalarsIntIso_hom_f (X : TopRep k G) (n : ℕ) :
    (homogeneousCochainsRestrictScalarsIntIso X).hom.f n =
      ((invariantsFunctor ℤ G).mapIso (resolutionXRestrictScalarsIntIso X (n + 1)) ≪≫
        invariantsRestrictScalarsIntIso (resolutionX X (n + 1))).hom :=
  (rfl)

/-! ### Naturality -/

section Naturality

open ContinuousCohomology

variable {X Y : TopRep k G} (f : X ⟶ Y)

/-- The identification of the resolutions is natural in the representation: on the elements of
the resolutions, the map induced by the underlying additive map of `f` is the map induced by
`f`. -/
theorem resolutionXRestrictScalarsIntIso_hom_resolutionMap_apply (i : ℕ)
    (v : (resolutionX (restrictScalarsInt.obj X) i).V) :
    (resolutionXRestrictScalarsIntIso Y i).hom.hom
        ((resolutionMap (ContinuousMonoidHom.id G) (restrictScalarsInt.map f) i).hom v) =
      (resolutionMap (ContinuousMonoidHom.id G) f i).hom
        ((resolutionXRestrictScalarsIntIso X i).hom.hom v) := by
  -- `resolutionMap` at the identity homomorphism is, in degree `i + 1`, the coinduction of the
  -- map in degree `i`; this is definitional, so the induction step is the induction hypothesis at
  -- the value `v x`.
  induction i with
  | zero => exact restrictScalarsInt_map_hom_apply f v
  | succ i ih =>
    refine ContinuousMap.ext fun x ↦ ?_
    simp only [resolutionXRestrictScalarsIntIso_succ, Iso.trans_hom, CategoryTheory.comp_apply,
      Functor.mapIso_hom, hom_ofHom]
    rw [coind₁RestrictScalarsIntIso_hom_apply, coind₁RestrictScalarsIntIso_hom_apply]
    exact ih (v x)

/-- The identification of the complexes of homogeneous cochains is natural in the
representation. -/
theorem cochainsMap_comp_homogeneousCochainsRestrictScalarsIntIso_hom :
    cochainsMap (ContinuousMonoidHom.id G) (restrictScalarsInt.map f) ≫
        (homogeneousCochainsRestrictScalarsIntIso Y).hom =
      (homogeneousCochainsRestrictScalarsIntIso X).hom ≫
        (TopModuleCat.restrictScalarsInt.mapHomologicalComplex _).map
          (cochainsMap (ContinuousMonoidHom.id G) f) := by
  ext i x
  -- In degree `i` the cochain map is the map induced on the invariants by the map on the
  -- resolutions in degree `i + 1`; this is definitional but not visible to `rw`, so the square is
  -- checked on elements.
  have h := congr($(invariantsRestrictScalarsIntIso_hom_comp_map
    (resolutionMap (ContinuousMonoidHom.id G) f (i + 1)))
      ((invariantsFunctor ℤ G).map (resolutionXRestrictScalarsIntIso X (i + 1)).hom x))
  simp only [CategoryTheory.comp_apply, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, homogeneousCochainsRestrictScalarsIntIso_hom_f,
    Iso.trans_hom] at h ⊢
  refine Eq.trans ?_ h.symm
  exact congrArg (fun w ↦ (invariantsRestrictScalarsIntIso (resolutionX Y (i + 1))).hom w)
    (Subtype.ext ((resolutionXRestrictScalarsIntIso_hom_resolutionMap_apply f (i + 1) x.1).trans
      (restrictScalarsInt_map_hom_apply _ _).symm))

end Naturality

end TopRep

namespace TauCeti.ContCohomology

open TopRep _root_.ContinuousCohomology
open TauCeti.ContinuousCohomology (coeffMap coeffMap_def)

variable {k : Type*} [Ring k] [TopologicalSpace k] {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (X : TopRep k G) (n : ℕ)

/-! ### Continuous cohomology -/

/-- **Continuous cohomology does not see the scalars.** The continuous cohomology of the
underlying additive representation of `X` is the underlying topological abelian group of the
continuous cohomology of `X`. -/
noncomputable def restrictScalarsIntIso :
    continuousCohomology n (restrictScalarsInt.obj X) ≅
      TopModuleCat.restrictScalarsInt.obj (continuousCohomology n X) :=
  HomologicalComplex.homologyMapIso (homogeneousCochainsRestrictScalarsIntIso X) n ≪≫
    ((homogeneousCochains X).sc n).mapHomologyIso TopModuleCat.restrictScalarsInt

/-- The cocycles of the underlying additive representation of `X` are the underlying topological
abelian group of the cocycles of `X`. -/
noncomputable def cocyclesRestrictScalarsIntIso :
    cocycles (restrictScalarsInt.obj X) n ≅ TopModuleCat.restrictScalarsInt.obj (cocycles X n) :=
  HomologicalComplex.cyclesMapIso (homogeneousCochainsRestrictScalarsIntIso X) n ≪≫
    ((homogeneousCochains X).sc n).mapCyclesIso TopModuleCat.restrictScalarsInt

/-- Under `cocyclesRestrictScalarsIntIso`, a cocycle corresponds to the same homogeneous cochain,
read through `homogeneousCochainsRestrictScalarsIntIso`. -/
@[reassoc (attr := simp)]
theorem cocyclesRestrictScalarsIntIso_hom_comp_map_iCycles :
    (cocyclesRestrictScalarsIntIso X n).hom ≫
        TopModuleCat.restrictScalarsInt.map ((homogeneousCochains X).iCycles n) =
      (homogeneousCochains (restrictScalarsInt.obj X)).iCycles n ≫
        (homogeneousCochainsRestrictScalarsIntIso X).hom.f n :=
  -- The middle object of `cocyclesRestrictScalarsIntIso` is the cycles of the image complex only
  -- after unfolding `HomologicalComplex.cycles`, so `rw` cannot split the composite and the
  -- squares are pasted as terms.
  (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (((homogeneousCochains X).sc n).mapCyclesIso_hom_iCycles
      TopModuleCat.restrictScalarsInt)).trans
    (HomologicalComplex.cyclesMap_i (homogeneousCochainsRestrictScalarsIntIso X).hom n)

/-- `restrictScalarsIntIso` carries the class of a cocycle of the underlying additive
representation to the class of the corresponding cocycle of `X`. -/
@[reassoc (attr := simp)]
theorem π_comp_restrictScalarsIntIso_hom :
    π (restrictScalarsInt.obj X) n ≫ (restrictScalarsIntIso X n).hom =
      (cocyclesRestrictScalarsIntIso X n).hom ≫ TopModuleCat.restrictScalarsInt.map (π X n) :=
  -- As in `cocyclesRestrictScalarsIntIso_hom_comp_map_iCycles`, the composites only split after
  -- unfolding, so the squares are pasted as terms.
  (HomologicalComplex.homologyπ_naturality_assoc
    (homogeneousCochainsRestrictScalarsIntIso X).hom n _).trans <|
    (congrArg (_ ≫ ·) (((homogeneousCochains X).sc n).homologyπ_comp_mapHomologyIso_hom
      TopModuleCat.restrictScalarsInt)).trans (Category.assoc _ _ _).symm

/-- In degree one, `cocyclesRestrictScalarsIntIso` does not change the values of a homogeneous
cocycle: both sides are the function `C(G, C(G, X.V))` underlying the cocycle. -/
-- Not a `simp` lemma: the carriers of the cocycles sit in the implicit arguments of `Subtype.val`,
-- where `simp` unfolds `(homogeneousCochains _).X 1` before matching; use it with `rw`.
theorem iCycles_cocyclesRestrictScalarsIntIso_hom_apply
    (v : cocycles (restrictScalarsInt.obj X) 1) (g₀ g₁ : G) :
    ((homogeneousCochains X).iCycles 1 ((cocyclesRestrictScalarsIntIso X 1).hom v)).val g₀ g₁ =
      ((homogeneousCochains (restrictScalarsInt.obj X)).iCycles 1 v).val g₀ g₁ := by
  -- The inclusion of the compared cocycle is the degree-one component of
  -- `homogeneousCochainsRestrictScalarsIntIso`, which is the identity on invariant functions.
  have h : (homogeneousCochains X).iCycles 1 ((cocyclesRestrictScalarsIntIso X 1).hom v) =
      (homogeneousCochainsRestrictScalarsIntIso X).hom.f 1
        ((homogeneousCochains (restrictScalarsInt.obj X)).iCycles 1 v) :=
    congr($(cocyclesRestrictScalarsIntIso_hom_comp_map_iCycles X 1) v)
  set u := (homogeneousCochains (restrictScalarsInt.obj X)).iCycles 1 v
  have hres : ((resolutionXRestrictScalarsIntIso X (1 + 1)).hom.hom u.val : C(G, C(G, X.V))) =
      u.val := by
    simp only [resolutionXRestrictScalarsIntIso_succ, resolutionXRestrictScalarsIntIso_zero,
      Iso.trans_hom, Functor.mapIso_hom, Iso.refl_hom, CategoryTheory.comp_apply, hom_ofHom]
    rw [coind₁RestrictScalarsIntIso_hom_apply]
    -- What remains is the coinduction of the degree-zero identification, the identity on
    -- `C(G, X.V)`, applied pointwise.
    refine ContinuousMap.ext fun x ↦ ContinuousMap.ext fun y ↦ ?_
    exact congrArg (fun F : C(G, X.V) ↦ F y)
      (coind₁RestrictScalarsIntIso_hom_apply (resolutionX X 0) (u.val x))
  rw [h, homogeneousCochainsRestrictScalarsIntIso_hom_f, Iso.trans_hom, CategoryTheory.comp_apply]
  exact congrArg (fun w : C(G, C(G, X.V)) ↦ w g₀ g₁)
    ((coe_invariantsRestrictScalarsIntIso_hom_apply _ _).trans hres)

variable {X} {Y : TopRep k G} (f : X ⟶ Y)

/-- The identification of the cocycles is natural in the representation: on cocycles, the map
induced by the underlying additive map of `f` is the underlying additive map of the map induced
by `f`. -/
@[reassoc (attr := simp)]
theorem cocyclesMap_comp_cocyclesRestrictScalarsIntIso_hom :
    cocyclesMap (ContinuousMonoidHom.id G) (restrictScalarsInt.map f) n ≫
        (cocyclesRestrictScalarsIntIso Y n).hom =
      (cocyclesRestrictScalarsIntIso X n).hom ≫
        TopModuleCat.restrictScalarsInt.map (cocyclesMap (ContinuousMonoidHom.id G) f n) := by
  -- The first square is the naturality of the identification of the cochains, the second is
  -- `ShortComplex.mapCyclesIso_hom_naturality`; as in
  -- `cocyclesRestrictScalarsIntIso_hom_comp_map_iCycles`, the composites only split after
  -- unfolding, so the squares are pasted as terms.
  have h : HomologicalComplex.cyclesMap
        (cochainsMap (ContinuousMonoidHom.id G) (restrictScalarsInt.map f)) n ≫
        HomologicalComplex.cyclesMap (homogeneousCochainsRestrictScalarsIntIso Y).hom n =
      HomologicalComplex.cyclesMap (homogeneousCochainsRestrictScalarsIntIso X).hom n ≫
        HomologicalComplex.cyclesMap
          ((TopModuleCat.restrictScalarsInt.mapHomologicalComplex _).map
            (cochainsMap (ContinuousMonoidHom.id G) f)) n := by
    rw [← HomologicalComplex.cyclesMap_comp, ← HomologicalComplex.cyclesMap_comp,
      cochainsMap_comp_homogeneousCochainsRestrictScalarsIntIso_hom]
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) h).trans <|
    (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (ShortComplex.mapCyclesIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor _ _ n).map
          (cochainsMap (ContinuousMonoidHom.id G) f)) TopModuleCat.restrictScalarsInt)).trans
        (Category.assoc _ _ _).symm

/-- **Continuous cohomology does not see the scalars, naturally.** The identification
`restrictScalarsIntIso` is natural in the representation: it carries the coefficient map of the
underlying additive map of `f` to the underlying additive map of the coefficient map of `f`. -/
@[reassoc (attr := simp)]
theorem coeffMap_comp_restrictScalarsIntIso_hom :
    coeffMap (restrictScalarsInt.map f) n ≫ (restrictScalarsIntIso Y n).hom =
      (restrictScalarsIntIso X n).hom ≫ TopModuleCat.restrictScalarsInt.map (coeffMap f n) := by
  -- As in `cocyclesMap_comp_cocyclesRestrictScalarsIntIso_hom`, with
  -- `ShortComplex.mapHomologyIso_hom_naturality` for the second square.
  have h : HomologicalComplex.homologyMap
        (cochainsMap (ContinuousMonoidHom.id G) (restrictScalarsInt.map f)) n ≫
        HomologicalComplex.homologyMap (homogeneousCochainsRestrictScalarsIntIso Y).hom n =
      HomologicalComplex.homologyMap (homogeneousCochainsRestrictScalarsIntIso X).hom n ≫
        HomologicalComplex.homologyMap
          ((TopModuleCat.restrictScalarsInt.mapHomologicalComplex _).map
            (cochainsMap (ContinuousMonoidHom.id G) f)) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      cochainsMap_comp_homogeneousCochainsRestrictScalarsIntIso_hom]
  rw [coeffMap_def, coeffMap_def]
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) h).trans <|
    (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor _ _ n).map
          (cochainsMap (ContinuousMonoidHom.id G) f)) TopModuleCat.restrictScalarsInt)).trans
        (Category.assoc _ _ _).symm

end TauCeti.ContCohomology

/-! ### Discrete coefficients -/

namespace TauCeti.ContCohomology

open TopRep

variable {k : Type*} [Ring k] [TopologicalSpace k] {G : Type*} [Monoid G]

attribute [local instance] TopRep.distribMulAction

/-- For a discrete `X`, the operators of the underlying additive representation of `X` are those
of the object attached by the discrete coefficient dictionary to `X.V` with the action read off
from `X`. -/
theorem ofDiscreteModule_ρ_eq_restrictScalarsInt_obj_ρ (X : TopRep k G) [DiscreteTopology X.V] :
    (ofDiscreteModule ℤ G X.V).ρ = (restrictScalarsInt.obj X).ρ :=
  DFunLike.ext _ _ fun g ↦ ContinuousLinearMap.ext fun (x : X.V) ↦
    ((ofDiscreteModule_ρ_apply_apply (R := ℤ) g x).trans
      (TopRep.distribMulAction_smul X g x)).trans (restrictScalarsInt_obj_ρ_apply X g x).symm

/-- For a discrete `X`, the underlying additive representation of `X` is the object attached by
the discrete coefficient dictionary to `X.V` with the action read off from `X`. Together with
`restrictScalarsIntIso`, this applies every statement about the coefficients
`TauCeti.ofDiscreteModule ℤ G M` to the continuous cohomology of `X`. -/
theorem ofDiscreteModule_eq_restrictScalarsInt_obj (X : TopRep k G) [DiscreteTopology X.V] :
    ofDiscreteModule ℤ G X.V = restrictScalarsInt.obj X :=
  -- This is not `ofDiscreteModule_eq_self (restrictScalarsInt.obj X)`: that statement carries the
  -- module structure and the derived action of `restrictScalarsInt.obj X`, whereas a consumer
  -- holds `X.V` with its canonical `ℤ`-module structure and the action derived from `X`.
  -- Both sides are `TopRep.of` of their operators, so they agree as soon as the operators do.
  congrArg (TopRep.of (X := X.V)) (ofDiscreteModule_ρ_eq_restrictScalarsInt_obj_ρ X)

end TauCeti.ContCohomology

namespace TauCeti.ContCohomology

open TopRep _root_.ContinuousCohomology

attribute [local instance] TopRep.distribMulAction

variable {k : Type*} [Ring k] [TopologicalSpace k] {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (X : TopRep k G) [DiscreteTopology X.V] (n : ℕ)

/-- **The continuous cohomology of a discrete representation over any scalars is that of its
carrier as a discrete `ℤ`-module**, with the action read off from `X`: the composite of
`ofDiscreteModule_eq_restrictScalarsInt_obj` and `restrictScalarsIntIso`. -/
noncomputable def ofDiscreteModuleRestrictScalarsIntIso :
    continuousCohomology n (ofDiscreteModule ℤ G X.V) ≅
      TopModuleCat.restrictScalarsInt.obj (continuousCohomology n X) :=
  eqToIso (congrArg (continuousCohomology n) (ofDiscreteModule_eq_restrictScalarsInt_obj X)) ≪≫
    restrictScalarsIntIso X n

/-- The cocycles of the carrier of a discrete `X` as a discrete `ℤ`-module are the underlying
topological abelian group of the cocycles of `X`: the composite of
`ofDiscreteModule_eq_restrictScalarsInt_obj` and `cocyclesRestrictScalarsIntIso`. -/
noncomputable def ofDiscreteModuleCocyclesRestrictScalarsIntIso :
    cocycles (ofDiscreteModule ℤ G X.V) n ≅ TopModuleCat.restrictScalarsInt.obj (cocycles X n) :=
  eqToIso (congrArg (cocycles · n) (ofDiscreteModule_eq_restrictScalarsInt_obj X)) ≪≫
    cocyclesRestrictScalarsIntIso X n

/-- `ofDiscreteModuleRestrictScalarsIntIso` carries the class of a cocycle of the carrier to the
class of the corresponding cocycle of `X`. -/
@[reassoc (attr := simp)]
theorem π_comp_ofDiscreteModuleRestrictScalarsIntIso_hom :
    π (ofDiscreteModule ℤ G X.V) n ≫ (ofDiscreteModuleRestrictScalarsIntIso X n).hom =
      (ofDiscreteModuleCocyclesRestrictScalarsIntIso X n).hom ≫
        TopModuleCat.restrictScalarsInt.map (π X n) := by
  -- Transport along the equality of representations commutes with `π` once the equality has a
  -- variable side.
  have key : ∀ {B : TopRep ℤ G} (h : ofDiscreteModule ℤ G X.V = B),
      π (ofDiscreteModule ℤ G X.V) n ≫ eqToHom (congrArg (continuousCohomology n) h) =
        eqToHom (congrArg (cocycles · n) h) ≫ π B n := by
    rintro B rfl
    simp
  rw [ofDiscreteModuleRestrictScalarsIntIso, ofDiscreteModuleCocyclesRestrictScalarsIntIso,
    Iso.trans_hom, Iso.trans_hom, eqToIso.hom, eqToIso.hom, ← Category.assoc,
    key (ofDiscreteModule_eq_restrictScalarsInt_obj X), Category.assoc,
    π_comp_restrictScalarsIntIso_hom, Category.assoc]

/-- In degree one, `ofDiscreteModuleCocyclesRestrictScalarsIntIso` does not change the values of
a homogeneous cocycle. -/
-- Not a `simp` lemma, for the same reason as `iCycles_cocyclesRestrictScalarsIntIso_hom_apply`.
theorem iCycles_ofDiscreteModuleCocyclesRestrictScalarsIntIso_hom_apply
    (w : cocycles (ofDiscreteModule ℤ G X.V) 1) (g₀ g₁ : G) :
    ((homogeneousCochains X).iCycles 1
        ((ofDiscreteModuleCocyclesRestrictScalarsIntIso X 1).hom w)).val g₀ g₁ =
      ((homogeneousCochains (ofDiscreteModule ℤ G X.V)).iCycles 1 w).val g₀ g₁ := by
  rw [ofDiscreteModuleCocyclesRestrictScalarsIntIso, Iso.trans_hom, eqToIso.hom,
    CategoryTheory.comp_apply, iCycles_cocyclesRestrictScalarsIntIso_hom_apply]
  -- Both representations are `TopRep.of` an operator on `X.V`, so the transport along the
  -- equality of operators is the identity on values once that equality has a variable side.
  have key : ∀ (ρ : ContRepresentation ℤ G X.V) (h : (ofDiscreteModule ℤ G X.V).ρ = ρ),
      ((homogeneousCochains (TopRep.of ρ)).iCycles 1
        (eqToHom (congrArg (fun ρ ↦ cocycles (TopRep.of ρ) 1) h) w)).val g₀ g₁ =
      ((homogeneousCochains (ofDiscreteModule ℤ G X.V)).iCycles 1 w).val g₀ g₁ := by
    rintro ρ rfl
    simp only [eqToHom_refl, CategoryTheory.id_apply]
    rfl
  exact key X.ρ.restrictScalarsInt (ofDiscreteModule_ρ_eq_restrictScalarsInt_obj_ρ X)

/-- `Hⁿ(G, X)` vanishes exactly when the `ℤ`-cohomology of the carrier of the discrete `X`
vanishes. -/
theorem subsingleton_continuousCohomology_ofDiscreteModule_iff :
    Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G X.V)) ↔
      Subsingleton (continuousCohomology n X) :=
  (ofDiscreteModuleRestrictScalarsIntIso X n).toContinuousLinearEquiv.toEquiv.subsingleton_congr

/-- `Hⁿ(G, X)` is nontrivial exactly when the `ℤ`-cohomology of the carrier of the discrete `X`
is nontrivial. -/
theorem nontrivial_continuousCohomology_ofDiscreteModule_iff :
    Nontrivial (continuousCohomology n (ofDiscreteModule ℤ G X.V)) ↔
      Nontrivial (continuousCohomology n X) :=
  (ofDiscreteModuleRestrictScalarsIntIso X n).toContinuousLinearEquiv.toEquiv.nontrivial_congr

end TauCeti.ContCohomology
