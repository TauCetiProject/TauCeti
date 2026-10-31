/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
public import TauCeti.AlgebraicGeometry.Morphisms.StalkMap
public import TauCeti.Topology.Sets.Opens

/-!
# The ramification, non-étale and branch loci of a morphism of schemes

For a morphism of schemes `f : X ⟶ Y` this file defines three sets:

* `Scheme.Hom.ramificationLocus f : Set X`, the points `x` at which `f` is not unramified, that is,
  at which the stalk map `𝒪_{Y, f x} → 𝒪_{X, x}` is not formally unramified;
* `Scheme.Hom.nonEtaleLocus f : Set X`, the points with no open neighbourhood on which `f` is
  étale, the complement of the points at which `f` is étale in the sense of Stacks, Definition
  29.37.1 (02GI);
* `Scheme.Hom.branchLocus f : Set Y`, the image of the ramification locus.

This API reserves `ramificationLocus` for failure of formal unramifiedness and
`nonEtaleLocus` for failure of étaleness. The Stacks Project uses ramification-locus terminology
in both settings; the definitions here fix the distinction used in Stacks, Section 58.21 and
SGA 1, Exposé X, Théorème 3.1.

On `Spec S ⟶ Spec R` the ramification locus is the complement of Mathlib's
`Algebra.unramifiedLocus R S`, and for `S` of finite presentation the non-étale locus is the
complement of `Algebra.etaleLocus R S`. For `f` locally of finite type, the complement of the
ramification locus is the union of the opens on which `f` is unramified
(`unramifiedAt_iff_stalkMap`), so the ramification locus is closed, and so is the branch locus of
a universally closed morphism. The non-étale locus is closed directly from its definition.

The two loci in `X` differ in general (a closed immersion is unramified but rarely flat), but they
agree for a dominant morphism of integral schemes, locally of finite type, onto a locally
Noetherian normal scheme (`ramificationLocus_eq_nonEtaleLocus`, SGA 1, Exposé I, 9.5 (ii)). At an
unramified point `x` the morphism is quasi-finite, so `dim 𝒪_{X, x} = dim 𝒪_{Y, f x}`
(`Scheme.Hom.ringKrullDim_stalk_eq_of_quasiFiniteAt`), and an unramified point over a normal
local ring of the same dimension is étale
(`Scheme.Hom.exists_etale_of_formallyUnramified_stalkMap_of_ringKrullDim_le`).

## Main results

* `AlgebraicGeometry.Scheme.Hom.ramificationLocus_eq_setOf_not_exists`: for `f` locally of finite
  type, the ramification locus is the complement of the points with an open neighbourhood on
  which `f` is unramified in Stacks' sense (Definition 29.36.1 (02G4)).
* `AlgebraicGeometry.Scheme.Hom.mem_nonEtaleLocus_iff_stalkMap`: for `f` locally of finite
  presentation, `f` is not étale at `x` iff its stalk map at `x` is not both flat and formally
  unramified (Stacks 02GU).
* `AlgebraicGeometry.Scheme.Hom.isClosed_ramificationLocus`,
  `AlgebraicGeometry.Scheme.Hom.isClosed_nonEtaleLocus`,
  `AlgebraicGeometry.Scheme.Hom.isClosed_branchLocus` (for `f` universally closed and locally of
  finite type, in particular finite, Stacks 01WM).
* `AlgebraicGeometry.Scheme.Hom.ramificationLocus_subset_nonEtaleLocus`.
* `AlgebraicGeometry.Scheme.Hom.ramificationLocus_eq_nonEtaleLocus`: for a dominant morphism of
  integral schemes, locally of finite type, onto a locally Noetherian normal (for instance,
  regular) scheme, the ramification locus is the non-étale locus.
* `AlgebraicGeometry.Scheme.Hom.ramificationLocus_specMap`,
  `AlgebraicGeometry.Scheme.Hom.nonEtaleLocus_specMap`,
  `AlgebraicGeometry.Scheme.Hom.branchLocus_specMap`: the affine comparisons with
  `Algebra.unramifiedLocus` and `Algebra.etaleLocus`.

## References

* [Stacks Project, Definition 29.36.1](https://stacks.math.columbia.edu/tag/02G4),
  [Definition 29.37.1](https://stacks.math.columbia.edu/tag/02GI),
  [Lemma 29.45.7](https://stacks.math.columbia.edu/tag/01WM), and Section 58.21.
* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé X, Théorème 3.1,
  and Exposé I, Théorème 9.5.
* The affine non-étale locus `(Algebra.etaleLocus R S)ᶜ` and its closedness appear in
  T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0), `lean/Pcf/NonEtaleLocus.lean`
  (`Pcf.nonEtaleLocus`, `Pcf.isClosed_nonEtaleLocus`). Here the affine locus corresponds to
  `nonEtaleLocus_specMap`, and its closedness follows from `isClosed_nonEtaleLocus` and
  `nonEtaleLocus_specMap`.
-/

public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The **ramification locus** of `f`: the points of `X` at which `f` is not unramified, with
"unramified at `x`" meaning that the stalk map `𝒪_{Y, f x} → 𝒪_{X, x}` is formally unramified.
For `f` locally of finite type it is the complement of the set of points at which `f` is
unramified in the sense of Stacks, Definition 29.36.1 (02G4); see
`ramificationLocus_eq_setOf_not_exists`. -/
def ramificationLocus : Set X :=
  {x | ¬ (f.stalkMap x).hom.FormallyUnramified}

/-- The **non-étale locus** of `f`: the points of `X` with no open neighbourhood on which `f` is
étale, the complement of the points at which `f` is étale in the sense of Stacks, Definition
29.37.1 (02GI). Stacks, Sections 58.28 and 58.29, calls this set the ramification locus; here that
name is reserved for `ramificationLocus`. -/
def nonEtaleLocus : Set X :=
  {x | ¬ ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f)}

/-- The **branch locus** of `f`: the image of the ramification locus, the points of `Y` over which
`f` is ramified at some point. -/
def branchLocus : Set Y :=
  f '' f.ramificationLocus

/-- Unfolding of `ramificationLocus`. -/
lemma ramificationLocus_def :
    f.ramificationLocus = {x | ¬ (f.stalkMap x).hom.FormallyUnramified} := by
  unfold ramificationLocus
  rfl

/-- Unfolding of `nonEtaleLocus`. -/
lemma nonEtaleLocus_def :
    f.nonEtaleLocus = {x | ¬ ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f)} := by
  unfold nonEtaleLocus
  rfl

/-- Unfolding of `branchLocus`. -/
lemma branchLocus_def : f.branchLocus = f '' f.ramificationLocus := by
  unfold branchLocus
  rfl

variable {f}

/-- `f` is ramified at `x` iff its stalk map at `x` is not formally unramified. -/
@[simp]
lemma mem_ramificationLocus_iff {x : X} :
    x ∈ f.ramificationLocus ↔ ¬ (f.stalkMap x).hom.FormallyUnramified :=
  Iff.rfl

/-- `x` lies in the non-étale locus iff no open neighbourhood of `x` makes `f` étale. -/
@[simp]
lemma mem_nonEtaleLocus_iff {x : X} :
    x ∈ f.nonEtaleLocus ↔ ¬ ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) :=
  Iff.rfl

/-- `y` lies in the branch locus iff `f` is ramified at some point over `y`. -/
@[simp]
lemma mem_branchLocus_iff {y : Y} : y ∈ f.branchLocus ↔ ∃ x ∈ f.ramificationLocus, f x = y :=
  Iff.rfl

variable (f)

/-- **The non-étale locus in stalk form.** For `f` locally of finite presentation, `f` is not étale
at `x` iff its stalk map at `x` is not both flat and formally unramified (Stacks, Lemma 29.37.15
(02GU), conditions (1) and (4)). -/
@[stacks 02GU "(1) ⇔ (4)"]
theorem mem_nonEtaleLocus_iff_stalkMap [LocallyOfFinitePresentation f] {x : X} :
    x ∈ f.nonEtaleLocus ↔
      ¬ ((f.stalkMap x).hom.Flat ∧ (f.stalkMap x).hom.FormallyUnramified) :=
  not_congr (etaleAt_iff_stalkMap f x)

/-- **The ramification locus in the form of Stacks, Definition 29.36.1 (02G4).** For `f` locally
of finite type, `f` is ramified at `x` iff no open neighbourhood `U` of `x` makes `U.ι ≫ f`
locally of finite type and formally unramified. -/
@[stacks 02G4 "complement of the unramified points"]
theorem ramificationLocus_eq_setOf_not_exists [LocallyOfFiniteType f] :
    f.ramificationLocus = {x | ¬ ∃ U : X.Opens, x ∈ U ∧ LocallyOfFiniteType (U.ι ≫ f) ∧
      FormallyUnramified (U.ι ≫ f)} := by
  ext x
  exact not_congr (unramifiedAt_iff_stalkMap f x).symm

/-- The ramification locus of a morphism locally of finite type is closed: its complement, the
set of points where `f` is unramified, is open (Stacks, Section 29.36 (02G3), the remark after
Definition 29.36.1). -/
theorem isClosed_ramificationLocus [LocallyOfFiniteType f] : IsClosed f.ramificationLocus := by
  rw [ramificationLocus_eq_setOf_not_exists]
  exact TopologicalSpace.Opens.isClosed_setOf_not_exists _

/-- The non-étale locus is closed, with no hypothesis on `f`: the étale points form an open set
by Stacks, Definition 29.37.1 (02GI). -/
theorem isClosed_nonEtaleLocus : IsClosed f.nonEtaleLocus :=
  TopologicalSpace.Opens.isClosed_setOf_not_exists _

/-- An étale point is unramified: the ramification locus is contained in the non-étale locus. -/
theorem ramificationLocus_subset_nonEtaleLocus : f.ramificationLocus ⊆ f.nonEtaleLocus := by
  rintro x hx ⟨U, hxU, hU⟩
  exact hx <| formallyUnramified_stalkMap_of_isOpenImmersion_comp f U.ι ⟨x, hxU⟩

/-- **Unramified points are étale over a normal base** (SGA 1, Exposé I, 9.5 (ii)). For a
dominant morphism `f : X ⟶ Y` of integral schemes, locally of finite type, with `Y` locally
Noetherian and normal (for instance, regular), the ramification locus of `f` is its non-étale
locus. Normality of `X` is not needed. -/
theorem ramificationLocus_eq_nonEtaleLocus [IsLocallyNoetherian Y] [IsIntegral X] [IsIntegral Y]
    [IsDominant f] [LocallyOfFiniteType f] [TauCeti.AlgebraicGeometry.IsNormalScheme Y] :
    f.ramificationLocus = f.nonEtaleLocus := by
  refine (ramificationLocus_subset_nonEtaleLocus f).antisymm fun x hx hfu ↦ hx ?_
  -- `f` is unramified, hence quasi-finite, near `x`, so the local rings have equal dimension.
  obtain ⟨U, hxU, _, _⟩ := (unramifiedAt_iff_stalkMap f x).mpr hfu
  have hqf : f.QuasiFiniteAt x :=
    (quasiFiniteAt_comp_iff_of_isOpenImmersion (f := U.ι) (x := ⟨x, hxU⟩)).mp
      ((U.ι ≫ f).quasiFiniteAt ⟨x, hxU⟩)
  exact f.exists_etale_of_formallyUnramified_stalkMap_of_ringKrullDim_le hfu
    (f.ringKrullDim_stalk_eq_of_quasiFiniteAt hqf).ge

/-- The image of the closed ramification locus under a closed map is closed, for `f` locally of
finite type. -/
theorem isClosed_branchLocus_of_isClosedMap [LocallyOfFiniteType f] (hf : IsClosedMap f) :
    IsClosed f.branchLocus :=
  hf _ (isClosed_ramificationLocus f)

/-- The branch locus of a universally closed morphism locally of finite type, in particular a
finite morphism (Stacks, Lemma 29.45.7 (01WM)), is closed. -/
theorem isClosed_branchLocus [UniversallyClosed f] [LocallyOfFiniteType f] :
    IsClosed f.branchLocus :=
  isClosed_branchLocus_of_isClosedMap f f.isClosedMap

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- On `Spec S ⟶ Spec R` the ramification locus is the complement of Mathlib's
`Algebra.unramifiedLocus`. No finiteness is needed. -/
theorem ramificationLocus_specMap :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).ramificationLocus =
      (Algebra.unramifiedLocus R S)ᶜ := by
  ext q
  exact not_congr (formallyUnramified_stalkMap_specMap_iff q)

/-- On `Spec S ⟶ Spec R` the branch locus is the image under `PrimeSpectrum.comap` of the
complement of `Algebra.unramifiedLocus`. -/
theorem branchLocus_specMap :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).branchLocus =
      PrimeSpectrum.comap (algebraMap R S) '' (Algebra.unramifiedLocus R S)ᶜ := by
  rw [branchLocus_def, ramificationLocus_specMap]
  exact Set.image_congr fun q _ ↦ Spec.map_apply _ q

/-- On `Spec S ⟶ Spec R`, for `S` of finite presentation, the non-étale locus is the complement of
Mathlib's `Algebra.etaleLocus`. -/
theorem nonEtaleLocus_specMap [Algebra.FinitePresentation R S] :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).nonEtaleLocus =
      (Algebra.etaleLocus R S)ᶜ := by
  ext q
  exact not_congr (etaleAt_spec_iff q)

end Scheme.Hom

end AlgebraicGeometry
