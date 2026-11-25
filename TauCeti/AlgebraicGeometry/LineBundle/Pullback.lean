/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Endomorphisms
public import TauCeti.AlgebraicGeometry.LineBundle.TensorProduct

/-!
# Pullback of line bundles

Let `f : X ⟶ Y` be a morphism of schemes. The inverse image `f^* L` of a line bundle `L` on `Y`
is a line bundle on `X`, giving a pullback functor on line bundles.
The generic restriction compatibility used to establish this result is provided by
`TauCeti.AlgebraicGeometry.Modules.Pullback.Basic`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.unitIsoRestrictImage`: transport a local trivialization
  to its image along an open immersion;
* `AlgebraicGeometry.Scheme.Modules.unitIsoRestrictPullback`: pull back a local trivialization
  to an open contained in the preimage of its domain;
* `AlgebraicGeometry.Scheme.Modules.nonempty_unitIsoRestrict_of_le`: a sheaf trivial over an
  open is trivial over every smaller open;
* `AlgebraicGeometry.Scheme.Modules.exists_isAffineOpen_mem_trivialization_le`: every point of an
  open `W` has an affine neighbourhood inside `W` trivializing a given invertible sheaf;
* `AlgebraicGeometry.Scheme.Modules.restrictFunctor_map_pullback_map_eq_iff`: through
  trivializations, two morphisms of invertible sheaves have equal pullbacks over the preimage of
  the trivializing open exactly when the pullback identifies the corresponding functions;
* `TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_pullback`: the pullback of an invertible
  sheaf is invertible;
* `TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_iff_forall_restrict`: a sheaf of modules
  is invertible exactly when its restrictions to the members of an open cover are invertible;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.pullback`: the pullback functor on line bundles;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.pullback_map_eq_pullback_map_iff`: two morphisms of
  line bundles have equal pullbacks exactly when their underlying module morphisms do;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.pullbackTrivialObjIso`: the pullback of the structure
  sheaf is the structure sheaf.

## References

* R. Hartshorne, *Algebraic Geometry*, Section II.5 and Section II.6 (the Picard group).
* The Stacks Project, *Sheaves of Modules*, section *Invertible modules*.
-/

public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {X Y : Scheme.{u}}

/-- Transport a trivialization on an open of the source of an open immersion to its image. -/
def unitIsoRestrictImage (g : X ⟶ Y) [IsOpenImmersion g] (V : X.Opens) {M : Y.Modules}
    (e : SheafOfModules.unit V.toScheme.ringCatSheaf ≅ (M.restrict g).restrict V.ι) :
    SheafOfModules.unit (g ''ᵁ V).toScheme.ringCatSheaf ≅ M.restrict (g ''ᵁ V).ι :=
  (restrictUnitIso (g.isoImage V).inv).symm ≪≫
    (restrictFunctor (g.isoImage V).inv).mapIso
      (e ≪≫ ((restrictFunctorComp V.ι g).app M).symm) ≪≫
    ((restrictFunctorComp (g.isoImage V).inv (V.ι ≫ g)).app M).symm ≪≫
    (restrictFunctorCongr (g.isoImage_inv_ι V)).app M

/-- Pull back a local trivialization to any open contained in the preimage of its domain. -/
def unitIsoRestrictPullback (f : X ⟶ Y) {V : Y.Opens} {W : X.Opens}
    (hW : W ≤ f ⁻¹ᵁ V) {M : Y.Modules}
    (e : SheafOfModules.unit V.toScheme.ringCatSheaf ≅ M.restrict V.ι) :
    SheafOfModules.unit W.toScheme.ringCatSheaf ≅ ((pullback f).obj M).restrict W.ι :=
  (pullbackObjUnitIso (f.resLE V W hW)).symm ≪≫
    (pullback (f.resLE V W hW)).mapIso e ≪≫
    ((restrictPullbackIso f V W hW).app M).symm

/-- A sheaf of modules trivial over an open `V` is trivial over every smaller open `U`. -/
theorem nonempty_unitIsoRestrict_of_le {U V : X.Opens} (hUV : U ≤ V) {M : X.Modules}
    (h : Nonempty (SheafOfModules.unit V.toScheme.ringCatSheaf ≅ M.restrict V.ι)) :
    Nonempty (SheafOfModules.unit U.toScheme.ringCatSheaf ≅ M.restrict U.ι) :=
  ⟨unitIsoRestrictPullback (𝟙 X) hUV h.some ≪≫
    (restrictFunctor U.ι).mapIso ((pullbackId X).app M)⟩

/-- Every point `x` of an open `W` has an affine open neighbourhood contained in `W` over which a
given invertible sheaf is trivial. -/
theorem exists_isAffineOpen_mem_trivialization_le (M : X.Modules)
    [hM : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M] {W : X.Opens} {x : X}
    (hx : x ∈ W) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ W ∧
      Nonempty (SheafOfModules.unit U.toScheme.ringCatSheaf ≅ M.restrict U.ι) := by
  obtain ⟨ι, V, hV, e⟩ :=
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_iff_exists_isOpenCover.mp hM
  obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (hV.iSup_eq_top.ge (Set.mem_univ x))
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ V k ⊓ W from ⟨hk, hx⟩) (V k ⊓ W).isOpen
  exact ⟨U, hU, hxU, fun _ hy ↦ (hUle hy).2,
    nonempty_unitIsoRestrict_of_le (fun _ hy ↦ (hUle hy).1) (e k)⟩

/-- Every point has an affine open neighbourhood over which two invertible sheaves are both
trivial. -/
theorem exists_isAffineOpen_mem_trivializations (M N : X.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M]
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X N] (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      Nonempty (SheafOfModules.unit U.toScheme.ringCatSheaf ≅ M.restrict U.ι) ∧
      Nonempty (SheafOfModules.unit U.toScheme.ringCatSheaf ≅ N.restrict U.ι) := by
  obtain ⟨V, -, hxV, -, ⟨eM⟩⟩ := exists_isAffineOpen_mem_trivialization_le M (Opens.mem_top x)
  obtain ⟨U, hU, hxU, hUV, ⟨eN⟩⟩ := exists_isAffineOpen_mem_trivialization_le N hxV
  exact ⟨U, hU, hxU, nonempty_unitIsoRestrict_of_le hUV ⟨eM⟩, ⟨eN⟩⟩

end

end AlgebraicGeometry.Scheme.Modules

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace SheafOfModules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pullback of an invertible sheaf along a morphism of schemes is invertible. -/
instance isInvertible_pullback (M : Y.Modules) [hM : isInvertible Y M] :
    isInvertible X ((Scheme.Modules.pullback f).obj M) := by
  obtain ⟨ι, V, hV, e⟩ :=
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_iff_exists_isOpenCover.mp hM
  refine TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_iff_exists_isOpenCover.mpr
    ⟨ι, fun i ↦ f ⁻¹ᵁ V i, ?_, fun i ↦
      ⟨Scheme.Modules.unitIsoRestrictPullback f le_rfl (e i).some⟩⟩
  rw [IsOpenCover, ← Scheme.Hom.preimage_iSup, hV.iSup_eq_top, Scheme.Hom.preimage_top]

/-- Restriction of an invertible sheaf along an open immersion is invertible. -/
instance isInvertible_restrict [IsOpenImmersion f] (M : Y.Modules) [isInvertible Y M] :
    isInvertible X (M.restrict f) :=
  (isInvertible X).prop_of_iso ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm
    inferInstance

/-- **Invertibility is local**: a sheaf of modules on a scheme is invertible exactly when its
restriction to every member of an open cover is invertible. -/
theorem isInvertible_iff_forall_restrict (𝒰 : X.OpenCover) (M : X.Modules) :
    isInvertible X M ↔ ∀ i, isInvertible (𝒰.X i) (M.restrict (𝒰.f i)) := by
  refine ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · have := h
    infer_instance
  -- Trivialize the restriction to each member `𝒰.X i` on an open cover `W i` of `𝒰.X i`, and
  -- pick for every point of `X` a trivializing open `W i k` whose image contains it.
  choose ι W hW e using fun i ↦ isInvertible_iff_exists_isOpenCover.mp (h i)
  have hx (x : X) : ∃ i k, x ∈ 𝒰.f i ''ᵁ W i k := by
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp ((hW i).iSup_eq_top.ge (Set.mem_univ y))
    exact ⟨i, k, y, hk, rfl⟩
  choose i k hk using hx
  refine isInvertible_iff_exists_isOpenCover.mpr ⟨X, fun x ↦ 𝒰.f (i x) ''ᵁ W (i x) (k x),
    IsOpenCover.mk (top_unique fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hk x⟩), fun x ↦ ⟨?_⟩⟩
  -- Transport the trivialization over `W i k` to its image along the isomorphism
  -- `(𝒰.f i).isoImage (W i k)` of open subschemes.
  exact Scheme.Modules.unitIsoRestrictImage (𝒰.f (i x)) (W (i x) (k x))
    (e (i x) (k x)).some

end SheafOfModules

namespace InvertibleSheaf

variable {X Y : Scheme.{u}}

/-- The pullback of line bundles along a morphism of schemes `f : X ⟶ Y`, as a functor from line
bundles on `Y` to line bundles on `X`. -/
-- Expose the underlying module so rigidified pullbacks can use this functor directly.
@[expose]
def pullback (f : X ⟶ Y) : InvertibleSheaf Y ⥤ InvertibleSheaf X :=
  (SheafOfModules.isInvertible X).lift
    ((SheafOfModules.isInvertible Y).ι ⋙ Scheme.Modules.pullback f)
    fun L ↦ SheafOfModules.isInvertible_pullback f L.obj

/-- The underlying sheaf of the pullback of a line bundle is its pullback as a sheaf of
modules. -/
@[simp]
lemma pullback_obj_obj (f : X ⟶ Y) (L : InvertibleSheaf Y) :
    ((pullback f).obj L).obj = (Scheme.Modules.pullback f).obj L.obj :=
  (rfl)

/-- Pullback acts on a morphism of line bundles by the underlying module pullback. -/
@[simp]
lemma pullback_map (f : X ⟶ Y) {L K : InvertibleSheaf Y} (φ : L ⟶ K) :
    ((pullback f).map φ).hom =
      eqToHom (pullback_obj_obj f L) ≫ (Scheme.Modules.pullback f).map φ.hom ≫
        eqToHom (pullback_obj_obj f K).symm := by
  cases pullback_obj_obj f L
  cases pullback_obj_obj f K
  unfold pullback
  simp

/-- Two morphisms of line bundles have equal pullbacks exactly when the underlying morphisms of
sheaves of modules do. -/
lemma pullback_map_eq_pullback_map_iff (f : X ⟶ Y) {L K : InvertibleSheaf Y} {φ ψ : L ⟶ K} :
    (pullback f).map φ = (pullback f).map ψ ↔
      (Scheme.Modules.pullback f).map φ.hom = (Scheme.Modules.pullback f).map ψ.hom :=
  ⟨fun h ↦ by simpa [cancel_epi, cancel_mono] using congrArg (·.hom) h,
    fun h ↦ ObjectProperty.hom_ext _ (by simp [h])⟩

/-- The pullback of the structure sheaf is the structure sheaf: `f^* 𝒪_Y ≅ 𝒪_X`, both
represented by trivial line bundles. -/
def pullbackTrivialObjIso (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (trivial Y).obj ≅ (trivial X).obj :=
  (Scheme.Modules.pullback f).mapIso (trivialObjIsoUnit Y) ≪≫
    Scheme.Modules.pullbackObjUnitIso f ≪≫ (trivialObjIsoUnit X).symm

end InvertibleSheaf

end

end AlgebraicGeometry

end TauCeti

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory MonoidalCategory

universe u

variable {X Z : Scheme.{u}}

/-- If trivializations over `U` identify `a` and `b` with multiplication by `ra` and `rb`, then the
pullbacks of `a` and `b` along `g` agree over `g⁻¹ U` exactly when `g` identifies `ra` and `rb`. -/
theorem restrictFunctor_map_pullback_map_eq_iff (g : Z ⟶ X) {M N : X.Modules}
    {U : X.Opens} (eM : (𝟙_ U.toScheme.Modules) ≅ M.restrict U.ι)
    (eN : (𝟙_ U.toScheme.Modules) ≅ N.restrict U.ι) {a b : M ⟶ N} {ra rb : Γ(U, ⊤)}
    (ha : (restrictFunctor U.ι).map a = eM.inv ≫ globalSectionsSmul _ ra ≫ eN.hom)
    (hb : (restrictFunctor U.ι).map b = eM.inv ≫ globalSectionsSmul _ rb ≫ eN.hom) :
    (restrictFunctor (g ⁻¹ᵁ U).ι).map ((pullback g).map a) =
        (restrictFunctor (g ⁻¹ᵁ U).ι).map ((pullback g).map b) ↔
      g.app U (U.topIso.hom ra) = g.app U (U.topIso.hom rb) := by
  let α := restrictPullbackIso g U (g ⁻¹ᵁ U) le_rfl
  have key (φ : M ⟶ N) : (restrictFunctor (g ⁻¹ᵁ U).ι).map ((pullback g).map φ) =
      α.hom.app M ≫ (pullback (g.resLE U (g ⁻¹ᵁ U) le_rfl)).map
        ((restrictFunctor U.ι).map φ) ≫ α.inv.app N :=
    (NatIso.naturality_2 α φ).symm
  rw [key, key, ha, hb]
  simp only [Functor.map_comp, cancel_epi, cancel_mono, pullback_map_globalSectionsSmul]
  rw [(globalSectionsSmul_injective _).eq_iff]
  -- On global sections, `g.resLE U (g ⁻¹ᵁ U)` is `g.app U` up to the identifications
  -- `topIso` of the global sections of an open subscheme with the sections over that open.
  have happTop (r : Γ(U, ⊤)) : (g.resLE U (g ⁻¹ᵁ U) le_rfl).appTop r =
      (g ⁻¹ᵁ U).topIso.inv (g.app U (U.topIso.hom r)) := by
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, ← Scheme.Hom.app_eq_appLE]
    simp only [CommRingCat.comp_apply]
  rw [happTop, happTop]
  exact (ConcreteCategory.bijective_of_isIso (g ⁻¹ᵁ U).topIso.inv).injective.eq_iff

end AlgebraicGeometry.Scheme.Modules
