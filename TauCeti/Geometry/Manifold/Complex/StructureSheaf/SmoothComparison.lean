/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Basic
public import TauCeti.Geometry.Manifold.Sheaf.LocallyRingedSpace

/-!
# Holomorphic and complex-smooth structure sheaves

On a finite-dimensional boundaryless complex manifold, complex `C^∞` functions are
holomorphic and hence complex analytic. Thus the `C^ω` holomorphic structure sheaf agrees
with Mathlib's `C^∞` structure sheaf over **ℂ**, not the sheaf of real-smooth functions.

We identify sections and sheaves, preserve evaluation on stalks, and compare pullback by
holomorphic maps. Conversely, every morphism of the native locally ringed spaces which induces
the identity on the residue fields `ℂ` is the pullback along a unique holomorphic map
(`TauCeti.holomorphicMapLocalRingedEquiv`). This allows the holomorphic sheaf to use Mathlib's
existing native manifold locally ringed space and its morphisms, rather than a parallel
construction.
No compactness, Hausdorffness or second-countability assumption is needed.

The comparison uses the native holomorphic regularity theorem
`MDifferentiable.contMDiff`. The locally ringed-space construction being compared is
Heather Macbeth's `ChartedSpace.locallyRingedSpace` in Mathlib.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §§1 and 6, for holomorphic functions
  and their local rings.
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H) [I.Boundaryless]
  (X : Type) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- Holomorphic sections are exactly the complex-smooth sections, with the same values. -/
def smoothSectionsEquiv (U : Opens X) :
    (holomorphicStructureSheaf I X).obj.obj (op U) ≃+*
      (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op U) where
  toFun s := ⟨s, (contMDiff s).of_le (by simp)⟩
  invFun s := ofContMDiff s
    ((ContMDiffMap.contMDiff (I := I) (I' := 𝓘(ℂ)) (n := ∞) s).mdifferentiable
      (by simp)).contMDiff
  left_inv s := ext fun x ↦ ofContMDiff_apply (I := I) (X := X) _ _ x
  right_inv s := ContMDiffMap.ext fun x ↦ ofContMDiff_apply (I := I) (X := X) _ _ x
  map_mul' s t := ContMDiffMap.ext fun x ↦ mul_apply s t x
  map_add' s t := ContMDiffMap.ext fun x ↦ add_apply s t x

variable {I X}

-- Avoid indexing on section carriers that reduce differently after import.
/-- The section comparison preserves values. -/
@[simp]
theorem smoothSectionsEquiv_apply (U : Opens X)
    (s : (holomorphicStructureSheaf I X).obj.obj (op U)) (x : U) :
    (no_index (smoothSectionsEquiv I X U s)) x = s x := (by
  rw [smoothSectionsEquiv]
  rfl)

/-- The inverse section comparison preserves values. -/
@[simp]
theorem smoothSectionsEquiv_symm_apply (U : Opens X)
    (s : (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op U)) (x : U) :
    (no_index ((smoothSectionsEquiv I X U).symm s)) x = s x := (by
  rw [smoothSectionsEquiv]
  exact ofContMDiff_apply (I := I) (X := X) (U := U) _ _ x)

variable (I X)

/-- The holomorphic structure sheaf is the complex-smooth structure sheaf used by
Mathlib's native manifold locally ringed space. -/
def smoothSheafIso :
    holomorphicStructureSheaf I X ≅ (ChartedSpace.locallyRingedSpace I X).sheaf :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun U ↦ (smoothSectionsEquiv I X U.unop).toCommRingCatIso) (by
      intro U V h
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro s
      apply ContMDiffMap.ext
      intro x
      exact (smoothSectionsEquiv_apply _ _ _).trans ((map_apply h s x).trans
        (smoothSectionsEquiv_apply U.unop s _).symm)))

variable {I X}

/-- On each open subset the sheaf comparison is the section comparison. -/
@[simp]
theorem smoothSheafIso_hom_app (U : Opens X) :
    (smoothSheafIso I X).hom.hom.app (op U) =
      CommRingCat.ofHom (smoothSectionsEquiv I X U).toRingHom := (rfl)

/-- On each open subset the inverse comparison is the inverse section comparison. -/
@[simp]
theorem smoothSheafIso_inv_app (U : Opens X) :
    (smoothSheafIso I X).inv.hom.app (op U) =
      CommRingCat.ofHom (smoothSectionsEquiv I X U).symm.toRingHom := (rfl)

variable (I X)

/-- The induced isomorphism between holomorphic germs and complex-smooth germs. -/
def smoothStalkIso (x : X) :
    (holomorphicStructureSheaf I X).presheaf.stalk x ≅
      (smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor (X := TopCat.of X) CommRingCat x).mapIso
    ((sheafToPresheaf _ _).mapIso (smoothSheafIso I X))

variable {I X}

-- Stalk carriers involve colimits; keep their projections out of the simp index.
/-- The stalk comparison sends the germ of a section to the germ of its comparison. -/
@[simp]
theorem smoothStalkIso_hom_germ (x : X) (U : Opens X) (hx : x ∈ U)
    (s : (holomorphicStructureSheaf I X).obj.obj (op U)) :
    (no_index (smoothStalkIso I X x).hom)
        (no_index ((holomorphicStructureSheaf I X).presheaf.germ U x hx s)) =
      (smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.germ U x hx
        (smoothSectionsEquiv I X U s) := by
  have h := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx (smoothSheafIso I X).hom.hom s
  rw [smoothSheafIso_hom_app] at h
  exact h

/-- The inverse stalk comparison takes the germ of a complex-smooth section to its
holomorphic germ. -/
@[simp]
theorem smoothStalkIso_inv_germ (x : X) (U : Opens X) (hx : x ∈ U)
    (s : (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op U)) :
    (no_index (smoothStalkIso I X x).inv)
        (no_index ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.germ U x hx s)) =
      (holomorphicStructureSheaf I X).presheaf.germ U x hx
        ((smoothSectionsEquiv I X U).symm s) := by
  have h := congrArg (fun a ↦ (smoothStalkIso I X x).inv a)
    (smoothStalkIso_hom_germ x U hx ((smoothSectionsEquiv I X U).symm s))
  simpa only [Iso.hom_inv_id_apply, RingEquiv.apply_symm_apply] using h.symm

/-- The stalk comparison preserves the value of a germ at its base point. -/
@[simp]
theorem eval_smoothStalkIso_hom (x : X)
    (s : (holomorphicStructureSheaf I X).presheaf.stalk x) :
    smoothSheafCommRing.eval I 𝓘(ℂ) X ℂ x ((smoothStalkIso I X x).hom s) = eval I X x s := by
  obtain ⟨U, hx, s, rfl⟩ := (holomorphicStructureSheaf I X).presheaf.exists_germ_eq s
  rw [smoothStalkIso_hom_germ]
  exact (smoothSheafCommRing.eval_germ U x hx _).trans
    ((smoothSectionsEquiv_apply U s ⟨x, hx⟩).trans (eval_germ I X U x hx s).symm)

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℂ E' H'} [J.Boundaryless]
  {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold J 1 Y]

/-- The sheaf comparison intertwines holomorphic pullback with Mathlib's complex-smooth
pullback. Thus both give the same morphisms on the native manifold carrier. -/
theorem smoothSheafIso_hom_naturality (f : X → Y) (hf : ContMDiff I J ω f) :
    homOfContMDiff I X f hf ≫
        (TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom ⟨f, hf.continuous⟩)).map
          (smoothSheafIso I X).hom =
      (smoothSheafIso J Y).hom ≫
        (hf.of_le (by simp)).smoothSheafCommRingHom J Y f := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  simp only [TopCat.Sheaf.comp_app, TopCat.Sheaf.pushforward_map,
    TopCat.Presheaf.pushforward_map_app, homOfContMDiff_app]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  apply ContMDiffMap.ext
  intro x
  -- Expose the categorical composites, whose sections have different bundled orders.
  change smoothSectionsEquiv I X _ (precomp I X f hf U s) x =
    smoothSectionsEquiv J Y U.unop s ⟨f x, x.property⟩
  exact (smoothSectionsEquiv_apply _ _ _).trans
    ((precomp_apply I X f hf U s x).trans (smoothSectionsEquiv_apply U.unop s _).symm)

end TauCeti.holomorphicStructureSheaf

namespace TauCeti

open AlgebraicGeometry CategoryTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℂ E' H'} [J.Boundaryless]
  {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold J 1 Y]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E''] [FiniteDimensional ℂ E'']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℂ E'' H''} [K.Boundaryless]
  {Z : Type} [TopologicalSpace Z] [ChartedSpace H'' Z] [IsManifold K 1 Z]

/-- A complex manifold of class `C^1` is of class `C^∞`, as the general equivalence
`ChartedSpace.locallyRingedSpaceMapEquiv` and its lemmas require. -/
private theorem isManifold_infty : IsManifold J ∞ Y :=
  IsManifold.of_ne_zero ∞ one_ne_zero ‹_›

attribute [local instance] isManifold_infty

/-- **Holomorphic maps are the morphisms of locally `ℂ`-ringed spaces.** Holomorphic maps
between finite-dimensional complex manifolds without boundary correspond to the morphisms of
their native locally ringed spaces that preserve values at points, that is, induce the identity
on the residue fields `ℂ`. A holomorphic map gives the pullback of functions
(`ChartedSpace.locallyRingedSpaceMap`), and such a morphism gives its underlying map, which is
holomorphic. -/
def holomorphicMapLocalRingedEquiv :
    C^ω⟮I, X; J, Y⟯ ≃ {φ : ChartedSpace.locallyRingedSpace I X ⟶
        ChartedSpace.locallyRingedSpace J Y // ChartedSpace.PreservesValues φ} :=
  haveI := FiniteDimensional.completeSpace ℂ E'
  Equiv.trans (β := C^∞⟮I, X; J, Y⟯)
    { toFun f := ⟨f, f.contMDiff.of_le (by simp)⟩
      invFun f := ⟨f, (f.contMDiff.mdifferentiable (by simp)).contMDiff⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    ChartedSpace.locallyRingedSpaceMapEquiv

/-- The morphism attached to a holomorphic map is its pullback of functions. -/
@[simp]
theorem holomorphicMapLocalRingedEquiv_apply_coe (f : C^ω⟮I, X; J, Y⟯) :
    (holomorphicMapLocalRingedEquiv f).1 =
      ChartedSpace.locallyRingedSpaceMap f (f.contMDiff.of_le (by simp)) :=
  ChartedSpace.locallyRingedSpaceMapEquiv_apply_coe _

/-- The holomorphic map attached to a value-preserving morphism is its underlying map. -/
@[simp]
theorem coe_holomorphicMapLocalRingedEquiv_symm_apply
    (φ : {φ : ChartedSpace.locallyRingedSpace I X ⟶ ChartedSpace.locallyRingedSpace J Y //
      ChartedSpace.PreservesValues φ}) :
    ⇑(holomorphicMapLocalRingedEquiv.symm φ) = φ.1.base :=
  ChartedSpace.coe_locallyRingedSpaceMapEquiv_symm_apply φ

/-- The identity holomorphic map corresponds to the identity morphism. -/
theorem holomorphicMapLocalRingedEquiv_id :
    (holomorphicMapLocalRingedEquiv (ContMDiffMap.id : C^ω⟮I, X; I, X⟯)).1 =
      𝟙 (ChartedSpace.locallyRingedSpace I X) :=
  (holomorphicMapLocalRingedEquiv_apply_coe _).trans (ChartedSpace.locallyRingedSpace_id I X)

/-- A composition of holomorphic maps corresponds to the composition of morphisms. -/
theorem holomorphicMapLocalRingedEquiv_comp (g : C^ω⟮J, Y; K, Z⟯) (f : C^ω⟮I, X; J, Y⟯) :
    (holomorphicMapLocalRingedEquiv (g.comp f)).1 =
      (holomorphicMapLocalRingedEquiv f).1 ≫ (holomorphicMapLocalRingedEquiv g).1 := by
  simp only [holomorphicMapLocalRingedEquiv_apply_coe]
  exact ChartedSpace.locallyRingedSpace_comp K (f.contMDiff.of_le (by simp))
    (g.contMDiff.of_le (by simp))

end TauCeti
