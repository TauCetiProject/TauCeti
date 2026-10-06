/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ShortComplex.PreservesHomology
public import TauCeti.RepresentationTheory.Continuous.TopRep.EqToHom
public import TauCeti.RepresentationTheory.Continuous.TopRep.RestrictScalars
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic

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
  the corresponding statements for a discrete `X`. The additive equivalences
  `TauCeti.ContCohomology.restrictScalarsIntEquiv`,
  `TauCeti.ContCohomology.cocyclesRestrictScalarsIntEquiv` and
  `TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv` between the carriers are the
  isomorphisms on elements; they act through the values of the iterated function spaces
  (`TopRep.resolutionXRestrictScalarsIntIso_succ_hom_apply`,
  `TauCeti.ContCohomology.iCycles_cocyclesRestrictScalarsIntEquiv_zero_apply` and its analogues
  in degrees one and two,
  `TauCeti.ContCohomology.restrictScalarsIntEquiv_π`).
* `TauCeti.ContCohomology.coeffMap_comp_restrictScalarsIntIso_hom`: the isomorphism is natural in
  the representation, with respect to the coefficient maps
  `TauCeti.ContinuousCohomology.coeffMap`;
  `TopRep.cochainsMap_comp_homogeneousCochainsRestrictScalarsIntIso_hom` and
  `TauCeti.ContCohomology.cocyclesMap_comp_cocyclesRestrictScalarsIntIso_hom` are the
  corresponding statements for the cochains and the cocycles.
* `TauCeti.ContCohomology.map_comp_restrictScalarsIntIso_hom_of_hom`: the isomorphism is also
  natural with respect to the simultaneous change of group and coefficients
  `ContinuousCohomology.map phi f` along a continuous homomorphism `phi : H →ₜ* G`, with the
  scalar-restricted coefficient map `TopRep.resRestrictScalarsIntMap phi f`. This is what
  transfers statements about change-of-group maps, such as Shapiro's lemma, from discrete
  `ℤ`-modules to coefficients over an arbitrary ring.
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

open _root_.ContinuousCohomology

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

/-- In degree zero the identification of the resolutions does not change elements. -/
-- Not a `simp` lemma: `simp` already rewrites the left-hand side through
-- `resolutionXRestrictScalarsIntIso_zero`, `Iso.refl_hom` and `TopRep.hom_id`, so the simpNF
-- linter rejects it; it is the explicit degree-zero step of the value computations below.
theorem resolutionXRestrictScalarsIntIso_zero_hom_apply (X : TopRep k G)
    (x : (resolutionX (restrictScalarsInt.obj X) 0).V) :
    (resolutionXRestrictScalarsIntIso X 0).hom.hom x = x :=
  (rfl)

/-- In degree `n + 1` the identification of the resolutions is the coinduction of the
identification in degree `n`, followed by the identification of the coinduced representations. -/
theorem resolutionXRestrictScalarsIntIso_succ (X : TopRep k G) (n : ℕ) :
    resolutionXRestrictScalarsIntIso X (n + 1) =
      (coind₁Functor ℤ G).mapIso (resolutionXRestrictScalarsIntIso X n) ≪≫
        coind₁RestrictScalarsIntIso (resolutionX X n) :=
  (rfl)

/-- In degree `n + 1` the identification of the resolutions acts on an element of the iterated
function space `C(G, C(G, …, X.V))` by applying the identification in degree `n` to its values. -/
-- The value of the identification lies in the carrier of `restrictScalarsInt.obj _`, which is the
-- function space `C(G, (resolutionX X n).V)` only after unfolding the functor, so the coercion to
-- a function is spelled out.
@[simp]
theorem resolutionXRestrictScalarsIntIso_succ_hom_apply (X : TopRep k G) (n : ℕ)
    (f : (resolutionX (restrictScalarsInt.obj X) (n + 1)).V) (g : G) :
    DFunLike.coe (F := C(G, (resolutionX X n).V))
        ((resolutionXRestrictScalarsIntIso X (n + 1)).hom.hom f) g =
      (resolutionXRestrictScalarsIntIso X n).hom.hom (f g) := by
  simp only [resolutionXRestrictScalarsIntIso_succ, Iso.trans_hom, CategoryTheory.comp_apply,
    Functor.mapIso_hom, hom_ofHom]
  rw [coind₁RestrictScalarsIntIso_hom_apply]
  -- `coind₁Map φ` is postcomposition with `φ`, `ContRepresentation.coind₁Map_toFun`; the rewrite
  -- is not available because the `ℤ`-module instance on the carrier of `restrictScalarsInt.obj _`
  -- is the field of the object, which the lemma's synthesized instance does not match, so the
  -- evaluation of the composite is checked by unification instead
  exact ContinuousMap.comp_apply _ _ _

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

/-- On elements, the identification of the homogeneous cochains in degree `n` is the identification
of the resolutions in degree `n + 1` on the underlying invariant elements. -/
theorem coe_homogeneousCochainsRestrictScalarsIntIso_hom_f (X : TopRep k G) (n : ℕ)
    (u : (homogeneousCochains (restrictScalarsInt.obj X)).X n) :
    ((homogeneousCochainsRestrictScalarsIntIso X).hom.f n u).val =
      (resolutionXRestrictScalarsIntIso X (n + 1)).hom.hom u.val := by
  rw [homogeneousCochainsRestrictScalarsIntIso_hom_f, Iso.trans_hom, CategoryTheory.comp_apply]
  exact coe_invariantsRestrictScalarsIntIso_hom_apply _ _

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

/-- The cocycles of the underlying additive representation of `X` are the cocycles of `X`, as an
additive equivalence between the carriers. -/
noncomputable def cocyclesRestrictScalarsIntEquiv :
    cocycles (restrictScalarsInt.obj X) n ≃+ cocycles X n :=
  (cocyclesRestrictScalarsIntIso X n).toContinuousLinearEquiv.toAddEquiv

/-- The additive equivalence `cocyclesRestrictScalarsIntEquiv` is `cocyclesRestrictScalarsIntIso`
on elements. -/
theorem cocyclesRestrictScalarsIntEquiv_apply (v : cocycles (restrictScalarsInt.obj X) n) :
    cocyclesRestrictScalarsIntEquiv X n v = (cocyclesRestrictScalarsIntIso X n).hom v :=
  (rfl)

/-- The continuous cohomology of the underlying additive representation of `X` is the continuous
cohomology of `X`, as an additive equivalence between the carriers. -/
noncomputable def restrictScalarsIntEquiv :
    continuousCohomology n (restrictScalarsInt.obj X) ≃+ continuousCohomology n X :=
  (restrictScalarsIntIso X n).toContinuousLinearEquiv.toAddEquiv

/-- The additive equivalence `restrictScalarsIntEquiv` is `restrictScalarsIntIso` on elements. -/
theorem restrictScalarsIntEquiv_apply (a : continuousCohomology n (restrictScalarsInt.obj X)) :
    restrictScalarsIntEquiv X n a = (restrictScalarsIntIso X n).hom a :=
  (rfl)

/-- `restrictScalarsIntEquiv` carries the class of a cocycle of the underlying additive
representation to the class of the corresponding cocycle of `X`. -/
@[simp]
theorem restrictScalarsIntEquiv_π (v : cocycles (restrictScalarsInt.obj X) n) :
    restrictScalarsIntEquiv X n (π (restrictScalarsInt.obj X) n v) =
      π X n (cocyclesRestrictScalarsIntEquiv X n v) :=
  congr($(π_comp_restrictScalarsIntIso_hom X n) v)

/-- Under `cocyclesRestrictScalarsIntEquiv`, the underlying homogeneous cochain of a cocycle is
carried by the identification of the resolutions. -/
theorem coe_iCycles_cocyclesRestrictScalarsIntEquiv (v : cocycles (restrictScalarsInt.obj X) n) :
    ((homogeneousCochains X).iCycles n (cocyclesRestrictScalarsIntEquiv X n v)).val =
      (resolutionXRestrictScalarsIntIso X (n + 1)).hom.hom
        ((homogeneousCochains (restrictScalarsInt.obj X)).iCycles n v).val := by
  have h : (homogeneousCochains X).iCycles n (cocyclesRestrictScalarsIntEquiv X n v) =
      (homogeneousCochainsRestrictScalarsIntIso X).hom.f n
        ((homogeneousCochains (restrictScalarsInt.obj X)).iCycles n v) :=
    congr($(cocyclesRestrictScalarsIntIso_hom_comp_map_iCycles X n) v)
  rw [h, coe_homogeneousCochainsRestrictScalarsIntIso_hom_f]

/-- In degree zero, `cocyclesRestrictScalarsIntEquiv` does not change the values of a homogeneous
cocycle: both sides are the function `C(G, X.V)` underlying the cocycle. -/
theorem iCycles_cocyclesRestrictScalarsIntEquiv_zero_apply
    (v : cocycles (restrictScalarsInt.obj X) 0) (g₀ : G) :
    ((homogeneousCochains X).iCycles 0 (cocyclesRestrictScalarsIntEquiv X 0 v)).val g₀ =
      ((homogeneousCochains (restrictScalarsInt.obj X)).iCycles 0 v).val g₀ :=
  (congrArg (fun w : C(G, X.V) ↦ w g₀)
    (coe_iCycles_cocyclesRestrictScalarsIntEquiv X 0 v)).trans
    ((resolutionXRestrictScalarsIntIso_succ_hom_apply X 0 _ g₀).trans
      (resolutionXRestrictScalarsIntIso_zero_hom_apply X _))

/-- In degree one, `cocyclesRestrictScalarsIntEquiv` does not change the values of a homogeneous
cocycle: both sides are the function `C(G, C(G, X.V))` underlying the cocycle. -/
-- Not a `simp` lemma: the carriers of the cocycles sit in the implicit arguments of `Subtype.val`,
-- where `simp` unfolds `(homogeneousCochains _).X 1` before matching; use it with `rw`.
theorem iCycles_cocyclesRestrictScalarsIntEquiv_one_apply
    (v : cocycles (restrictScalarsInt.obj X) 1) (g₀ g₁ : G) :
    ((homogeneousCochains X).iCycles 1 (cocyclesRestrictScalarsIntEquiv X 1 v)).val g₀ g₁ =
      ((homogeneousCochains (restrictScalarsInt.obj X)).iCycles 1 v).val g₀ g₁ :=
  -- The identification of the resolutions is the identity on values, one function-space level at
  -- a time; the composite is assembled as a term because the intermediate values live in the
  -- carriers of `restrictScalarsInt.obj _`, which `rw` does not see as function spaces.
  (congrArg (fun w : C(G, C(G, X.V)) ↦ w g₀ g₁)
    (coe_iCycles_cocyclesRestrictScalarsIntEquiv X 1 v)).trans
    ((congrArg (fun w : C(G, X.V) ↦ w g₁)
      (resolutionXRestrictScalarsIntIso_succ_hom_apply X 1 _ g₀)).trans
      ((resolutionXRestrictScalarsIntIso_succ_hom_apply X 0 _ g₁).trans
        (resolutionXRestrictScalarsIntIso_zero_hom_apply X _)))

/-- In degree two, `cocyclesRestrictScalarsIntEquiv` does not change the values of a homogeneous
cocycle. -/
theorem iCycles_cocyclesRestrictScalarsIntEquiv_two_apply
    (v : cocycles (restrictScalarsInt.obj X) 2) (g₀ g₁ g₂ : G) :
    ((homogeneousCochains X).iCycles 2 (cocyclesRestrictScalarsIntEquiv X 2 v)).val g₀ g₁ g₂ =
      ((homogeneousCochains (restrictScalarsInt.obj X)).iCycles 2 v).val g₀ g₁ g₂ :=
  -- The identification of the resolutions is the identity on values, one function-space level at
  -- a time; the composite is assembled as a term because the intermediate values live in the
  -- carriers of `restrictScalarsInt.obj _`, which `rw` does not see as function spaces.
  (congrArg (fun w : C(G, C(G, C(G, X.V))) ↦ w g₀ g₁ g₂)
    (coe_iCycles_cocyclesRestrictScalarsIntEquiv X 2 v)).trans
    ((congrArg (fun w : C(G, C(G, X.V)) ↦ w g₁ g₂)
      (resolutionXRestrictScalarsIntIso_succ_hom_apply X (1 + 1) _ g₀)).trans
      ((congrArg (fun w : C(G, X.V) ↦ w g₂)
        (resolutionXRestrictScalarsIntIso_succ_hom_apply X 1 _ g₁)).trans
        ((resolutionXRestrictScalarsIntIso_succ_hom_apply X 0 _ g₂).trans
          (resolutionXRestrictScalarsIntIso_zero_hom_apply X _))))

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

namespace TopRep

open _root_.ContinuousCohomology

universe u v

variable {R : Type v} [Ring R] [TopologicalSpace R]
  {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {X : TopRep.{u} R G} {Y : TopRep.{u} R H}
  (phi : H →ₜ* G) (f : TopRep.res (phi : H →* G) X ⟶ Y)

private theorem resolutionXRestrictScalarsIntIso_hom_resolutionMap_apply_of_hom (i : ℕ)
    (x : (resolutionX (restrictScalarsInt.obj X) i).V) :
    (resolutionXRestrictScalarsIntIso Y i).hom.hom
        ((resolutionMap phi (resRestrictScalarsIntMap (phi : H →* G) f) i).hom x) =
      (resolutionMap phi f i).hom
        ((resolutionXRestrictScalarsIntIso X i).hom.hom x) := by
  induction i with
  | zero => exact resRestrictScalarsIntMap_hom_apply (phi : H →* G) f x
  | succ i ih =>
    refine ContinuousMap.ext fun h => ?_
    simp only [resolutionXRestrictScalarsIntIso_succ, Iso.trans_hom,
      CategoryTheory.comp_apply, Functor.mapIso_hom, hom_ofHom]
    rw [coind₁RestrictScalarsIntIso_hom_apply, coind₁RestrictScalarsIntIso_hom_apply]
    exact ih (x (phi h))

private theorem cochainsMap_comp_homogeneousCochainsRestrictScalarsIntIso_hom_of_hom :
    cochainsMap phi (resRestrictScalarsIntMap (phi : H →* G) f) ≫
        (homogeneousCochainsRestrictScalarsIntIso Y).hom =
      (homogeneousCochainsRestrictScalarsIntIso X).hom ≫
        (TopModuleCat.restrictScalarsInt.mapHomologicalComplex _).map
          (cochainsMap phi f) := by
  ext i x
  apply Subtype.ext
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    CategoryTheory.comp_apply]
  rw [coe_homogeneousCochainsRestrictScalarsIntIso_hom_f]
  -- A homogeneous cochain is a subtype of `resolutionX _ (i + 1)`, and `cochainsMap` acts on its
  -- underlying element as `resolutionMap`; this unfolds the complex-map wrappers to that action.
  change (resolutionXRestrictScalarsIntIso Y (i + 1)).hom.hom
      ((resolutionMap phi (resRestrictScalarsIntMap (phi : H →* G) f) (i + 1)).hom x.1) =
    (resolutionMap phi f (i + 1)).hom
      ((homogeneousCochainsRestrictScalarsIntIso X).hom.f i x).1
  exact (resolutionXRestrictScalarsIntIso_hom_resolutionMap_apply_of_hom
    phi f (i + 1) x.1).trans (congrArg
      (fun z : (resolutionX X (i + 1)).V ↦ (resolutionMap phi f (i + 1)).hom z)
      (coe_homogeneousCochainsRestrictScalarsIntIso_hom_f X i x).symm)

end TopRep

namespace TauCeti.ContCohomology

universe u v

variable {R : Type v} [Ring R] [TopologicalSpace R]
  {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {X : TopRep.{u} R G} {Y : TopRep.{u} R H}
  (phi : H →ₜ* G) (f : TopRep.res (phi : H →* G) X ⟶ Y) (n : ℕ)

/-- Scalar restriction commutes with the simultaneous group-and-coefficient map on continuous
cohomology. -/
theorem map_comp_restrictScalarsIntIso_hom_of_hom :
    _root_.ContinuousCohomology.map phi
        (TopRep.resRestrictScalarsIntMap (phi : H →* G) f) n ≫
        (restrictScalarsIntIso Y n).hom =
      (restrictScalarsIntIso X n).hom ≫
        TopModuleCat.restrictScalarsInt.map
          (_root_.ContinuousCohomology.map phi f n) := by
  have h : HomologicalComplex.homologyMap
        (_root_.ContinuousCohomology.cochainsMap phi
          (TopRep.resRestrictScalarsIntMap (phi : H →* G) f)) n ≫
        HomologicalComplex.homologyMap (TopRep.homogeneousCochainsRestrictScalarsIntIso Y).hom n =
      HomologicalComplex.homologyMap (TopRep.homogeneousCochainsRestrictScalarsIntIso X).hom n ≫
        HomologicalComplex.homologyMap
          ((TopModuleCat.restrictScalarsInt.mapHomologicalComplex _).map
            (_root_.ContinuousCohomology.cochainsMap phi f)) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      TopRep.cochainsMap_comp_homogeneousCochainsRestrictScalarsIntIso_hom_of_hom]
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) h).trans <|
    (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor _ _ n).map
          (_root_.ContinuousCohomology.cochainsMap phi f))
          TopModuleCat.restrictScalarsInt)).trans
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

/-- The carrier cast identifying discrete coefficients with their underlying additive
representation is the identity. -/
theorem cast_ofDiscreteModule_eq_restrictScalarsInt_obj
    (X : TopRep k G) [DiscreteTopology X.V]
    (x : (ofDiscreteModule ℤ G X.V).V) :
    cast (congrArg TopRep.V (ofDiscreteModule_eq_restrictScalarsInt_obj X)) x =
      (show X.V from x) := by
  exact cast_eq _ _

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

/-- The morphism of `ofDiscreteModuleRestrictScalarsIntIso` is the coefficient transport followed
by the scalar-restriction isomorphism. -/
theorem ofDiscreteModuleRestrictScalarsIntIso_hom :
    (ofDiscreteModuleRestrictScalarsIntIso X n).hom =
      eqToHom (congrArg (continuousCohomology n)
        (ofDiscreteModule_eq_restrictScalarsInt_obj X)) ≫
        (restrictScalarsIntIso X n).hom := by
  rw [ofDiscreteModuleRestrictScalarsIntIso, Iso.trans_hom, eqToIso.hom]

/-- The continuous cohomology of the carrier of a discrete `X` as a discrete `ℤ`-module is the
continuous cohomology of `X`, as an additive equivalence between the carriers. -/
noncomputable def ofDiscreteModuleRestrictScalarsIntEquiv :
    continuousCohomology n (ofDiscreteModule ℤ G X.V) ≃+ continuousCohomology n X :=
  (ofDiscreteModuleRestrictScalarsIntIso X n).toContinuousLinearEquiv.toAddEquiv

/-- `ofDiscreteModuleRestrictScalarsIntEquiv` is the transport along the equality of objects
followed by `restrictScalarsIntEquiv`. -/
theorem ofDiscreteModuleRestrictScalarsIntEquiv_apply
    (a : continuousCohomology n (ofDiscreteModule ℤ G X.V)) :
    ofDiscreteModuleRestrictScalarsIntEquiv X n a =
      restrictScalarsIntEquiv X n (eqToHom (congrArg (continuousCohomology n)
        (ofDiscreteModule_eq_restrictScalarsInt_obj X)) a) :=
  (rfl)

/-- The cocycles of the carrier of a discrete `X` as a discrete `ℤ`-module are the underlying
topological abelian group of the cocycles of `X`: the composite of
`ofDiscreteModule_eq_restrictScalarsInt_obj` and `cocyclesRestrictScalarsIntIso`. -/
noncomputable def ofDiscreteModuleCocyclesRestrictScalarsIntIso :
    cocycles (ofDiscreteModule ℤ G X.V) n ≅ TopModuleCat.restrictScalarsInt.obj (cocycles X n) :=
  eqToIso (congrArg (cocycles · n) (ofDiscreteModule_eq_restrictScalarsInt_obj X)) ≪≫
    cocyclesRestrictScalarsIntIso X n

/-- `ofDiscreteModuleCocyclesRestrictScalarsIntIso` is the transport along the equality of objects
followed by `cocyclesRestrictScalarsIntEquiv`. -/
theorem ofDiscreteModuleCocyclesRestrictScalarsIntIso_hom_apply
    (w : cocycles (ofDiscreteModule ℤ G X.V) n) :
    (ofDiscreteModuleCocyclesRestrictScalarsIntIso X n).hom w =
      cocyclesRestrictScalarsIntEquiv X n (eqToHom (congrArg (cocycles · n)
        (ofDiscreteModule_eq_restrictScalarsInt_obj X)) w) :=
  (rfl)

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

/-- `ofDiscreteModuleRestrictScalarsIntEquiv` carries the class of a cocycle of the carrier to the
class of the corresponding cocycle of `X`. -/
@[simp]
theorem ofDiscreteModuleRestrictScalarsIntEquiv_π (w : cocycles (ofDiscreteModule ℤ G X.V) n) :
    ofDiscreteModuleRestrictScalarsIntEquiv X n (π (ofDiscreteModule ℤ G X.V) n w) =
      π X n ((ofDiscreteModuleCocyclesRestrictScalarsIntIso X n).hom w) :=
  congr($(π_comp_ofDiscreteModuleRestrictScalarsIntIso_hom X n) w)

/-- In degree one, `ofDiscreteModuleCocyclesRestrictScalarsIntIso` does not change the values of
a homogeneous cocycle. -/
-- Not a `simp` lemma, for the same reason as `iCycles_cocyclesRestrictScalarsIntEquiv_one_apply`.
theorem iCycles_ofDiscreteModuleCocyclesRestrictScalarsIntIso_hom_apply
    (w : cocycles (ofDiscreteModule ℤ G X.V) 1) (g₀ g₁ : G) :
    ((homogeneousCochains X).iCycles 1
        ((ofDiscreteModuleCocyclesRestrictScalarsIntIso X 1).hom w)).val g₀ g₁ =
      ((homogeneousCochains (ofDiscreteModule ℤ G X.V)).iCycles 1 w).val g₀ g₁ := by
  rw [ofDiscreteModuleCocyclesRestrictScalarsIntIso, Iso.trans_hom, eqToIso.hom,
    CategoryTheory.comp_apply, ← cocyclesRestrictScalarsIntEquiv_apply,
    iCycles_cocyclesRestrictScalarsIntEquiv_one_apply]
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
