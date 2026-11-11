/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import TauCeti.AlgebraicGeometry.Descent.QuasicoherentSheaf.Affine
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.BaseChange

/-!
# Descent of morphisms of quasi-coherent modules along faithfully flat maps of affine schemes

Let `f : X ⟶ S` be a morphism of schemes, with projections `p₁, p₂ : X ×_S X ⟶ X`, and let `A`, `B`
be modules on `S`. A morphism `g : f^* A ⟶ f^* B` satisfies the descent condition if it is
compatible with the canonical identifications `p₂^* f^* M ≅ p₁^* f^* M` for `M = A, B`; every
morphism of descent data for `Descent.qcohPseudofunctor` along `f` does
(`Descent.qcohPseudofunctor_descentData_hom_comm`). When `f` is flat, quasi-compact and
quasi-separated and `B` is quasi-coherent, flat base change identifies `f^* f_* f^* B` with
`p₂_* p₁^* f^* B`, and under this identification the pullback of the unit `B ⟶ f_* f^* B` becomes
the adjunct of the canonical identification. So `g` satisfies the descent condition if and only if
it is a morphism of coalgebras for the comonad `f^* f_*`
(`Scheme.Modules.comp_pullback_map_unit_app_eq_iff`).

For a faithfully flat ring map `φ : R ⟶ S`, pullback of quasi-coherent modules along `Spec φ` is
comonadic, so the coalgebra morphisms between pullbacks are exactly the pullbacks of morphisms.
Hence morphisms of quasi-coherent modules descend along `Spec φ`: the functor from quasi-coherent
modules on `Spec R` to descent data along `Spec φ` for `Descent.qcohPseudofunctor` is fully faithful
(`Descent.qcohPseudofunctor_isPrestackFor_singleton_specMap`). This is the descent of morphisms
in fpqc descent of quasi-coherent modules, for a single faithfully flat map of affine schemes;
effectivity of descent data is not treated here.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.comp_pullback_map_unit_app_eq_iff`: for `f` flat,
  quasi-compact and quasi-separated, a morphism `f^* A ⟶ f^* B` with `B` quasi-coherent is a
  coalgebra morphism for `f^* f_*` iff it satisfies the descent condition.
* `TauCeti.AlgebraicGeometry.Descent.qcohPseudofunctor_descentData_hom_comm`: morphisms of descent
  data along a single morphism satisfy the descent condition on underlying modules.
* `TauCeti.AlgebraicGeometry.Descent.qcohPseudofunctor_isPrestackFor_singleton_specMap`: for a
  faithfully flat ring map `φ`, `qcohPseudofunctor` is a prestack for the covering `{Spec φ}`.

## References

* The Stacks Project, Section 35.3 (descent for modules along faithfully flat ring maps) and
  Proposition 35.5.2 (023T), descent of quasi-coherent modules along fpqc coverings.
* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII,
  Théorème 1.1.
* J. Bénabou, J. Roubaud, *Monades et descente*, C. R. Acad. Sci. Paris Sér. A-B 270 (1970),
  A96–A98: with base change, descent data are coalgebras for the comonad `f^* f_*`.
* G. Janelidze, W. Tholen, *Facets of descent, I*, Appl. Categ. Structures 2 (1994), 245–281.
-/

public section

open CategoryTheory Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Descent of morphisms as coalgebra morphisms.** For `f : X ⟶ S` flat, quasi-compact and
quasi-separated, and modules `A`, `B` on `S` with `B` quasi-coherent, a morphism
`g : f^* A ⟶ f^* B` is a morphism of coalgebras for the comonad `f^* f_*` if and only if it is
compatible with the canonical isomorphisms `p₂^* f^* M ≅ (p₂ ≫ f)^* M = (p₁ ≫ f)^* M ≅ p₁^* f^* M`
on `X ×_S X`, for `M = A, B`. This is the morphism-level case of the Bénabou–Roubaud theorem:
when base change holds, descent data along `f` are coalgebras for `f^* f_*`. -/
theorem comp_pullback_map_unit_app_eq_iff [QuasiCompact f] [QuasiSeparated f] [Flat f]
    {A B : S.Modules} [B.IsQuasicoherent] (g : (pullback f).obj A ⟶ (pullback f).obj B) :
    g ≫ (pullback f).map ((pullbackPushforwardAdjunction f).unit.app B) =
        (pullback f).map ((pullbackPushforwardAdjunction f).unit.app A) ≫
          (pullback f).map ((pushforward f).map g) ↔
      (pullback (pullback.snd f f)).map g ≫
          (pullbackComp (pullback.snd f f) f).hom.app B ≫
            (pullbackCongr pullback.condition.symm).hom.app B ≫
              (pullbackComp (pullback.fst f f) f).inv.app B =
        ((pullbackComp (pullback.snd f f) f).hom.app A ≫
            (pullbackCongr pullback.condition.symm).hom.app A ≫
              (pullbackComp (pullback.fst f f) f).inv.app A) ≫
          (pullback (pullback.fst f f)).map g := by
  have H := IsPullback.of_hasPullback f f
  have := isIso_pushforwardBaseChange_app H ((pullback f).obj B)
  -- Followed by the base change isomorphism `f^* f_* f^* B ≅ p₂_* p₁^* f^* B`, both sides of the
  -- coalgebra condition are the adjuncts under `p₂^* ⊣ p₂_*` of the two sides of the descent
  -- condition.
  have hB := pullback_map_unit_comp_pushforwardBaseChange_app H.toCommSq B
  have hA := pullback_map_unit_comp_pushforwardBaseChange_app H.toCommSq A
  have hn := (pushforwardBaseChange H.toCommSq).naturality g
  dsimp only [Functor.comp_map] at hn
  rw [← cancel_mono ((pushforwardBaseChange H.toCommSq).app ((pullback f).obj B)),
    Category.assoc, hB, Category.assoc, hn, reassoc_of% hA,
    ← ((pullbackPushforwardAdjunction (pullback.snd f f)).homEquiv _ _).apply_eq_iff_eq]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc,
    Adjunction.unit_naturality_assoc]

end AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry.Descent

open _root_.AlgebraicGeometry

/-- A morphism `ψ` of descent data for `qcohPseudofunctor` along a single morphism `f : X ⟶ Y`,
between the descent data of quasi-coherent modules `A` and `B` on `Y`, is compatible, on underlying
modules, with the canonical isomorphisms `p₂^* f^* M ≅ (p₂ ≫ f)^* M = (p₁ ≫ f)^* M ≅ p₁^* f^* M`
on `X ×_Y X`, for `M = A, B`. -/
theorem qcohPseudofunctor_descentData_hom_comm {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : QuasicoherentSheaf Y}
    (ψ : Pseudofunctor.DescentData.ofObj (F := qcohPseudofunctor) (f := fun _ : PUnit ↦ f) A ⟶
      Pseudofunctor.DescentData.ofObj B) :
    (Scheme.Modules.pullback (pullback.snd f f)).map (ψ.hom PUnit.unit).hom ≫
        (Scheme.Modules.pullbackComp (pullback.snd f f) f).hom.app B.obj ≫
          (Scheme.Modules.pullbackCongr pullback.condition.symm).hom.app B.obj ≫
            (Scheme.Modules.pullbackComp (pullback.fst f f) f).inv.app B.obj =
      ((Scheme.Modules.pullbackComp (pullback.snd f f) f).hom.app A.obj ≫
          (Scheme.Modules.pullbackCongr pullback.condition.symm).hom.app A.obj ≫
            (Scheme.Modules.pullbackComp (pullback.fst f f) f).inv.app A.obj) ≫
        (Scheme.Modules.pullback (pullback.fst f f)).map (ψ.hom PUnit.unit).hom := by
  let g : (qcohPseudofunctor.map f.op.toLoc).toFunctor.obj A ⟶
      (qcohPseudofunctor.map f.op.toLoc).toFunctor.obj B := ψ.hom PUnit.unit
  -- The descent condition on `X ×_S X`, with the objects of the descent data unfolded.
  have hq : f.op.toLoc ≫ (pullback.fst f f).op.toLoc = (pullback.snd f f ≫ f).op.toLoc := by
    rw [← pullback.condition]; rfl
  have hψ : (qcohPseudofunctor.map (pullback.snd f f).op.toLoc).toFunctor.map g ≫
      (qcohPseudofunctor.mapComp' f.op.toLoc (pullback.snd f f).op.toLoc
          (pullback.snd f f ≫ f).op.toLoc rfl).inv.toNatTrans.app B ≫
        (qcohPseudofunctor.mapComp' f.op.toLoc (pullback.fst f f).op.toLoc
          (pullback.snd f f ≫ f).op.toLoc hq).hom.toNatTrans.app B =
      ((qcohPseudofunctor.mapComp' f.op.toLoc (pullback.snd f f).op.toLoc
          (pullback.snd f f ≫ f).op.toLoc rfl).inv.toNatTrans.app A ≫
        (qcohPseudofunctor.mapComp' f.op.toLoc (pullback.fst f f).op.toLoc
          (pullback.snd f f ≫ f).op.toLoc hq).hom.toNatTrans.app A) ≫
        (qcohPseudofunctor.map (pullback.fst f f).op.toLoc).toFunctor.map g :=
    ψ.comm (pullback.snd f f ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (pullback.snd f f)
      (pullback.fst f f) rfl pullback.condition
  -- Read it on underlying modules through the inclusion of quasi-coherent modules. The category
  -- `qcohPseudofunctor.obj T` is `QuasicoherentSheaf T` only up to unfolding, so Mathlib's
  -- `ObjectProperty.ι_map` and `ObjectProperty.FullSubcategory.comp_hom` do not apply to `hψ`;
  -- `hι` states `ι_map` for this category.
  let ι : qcohPseudofunctor.obj ⟨op (pullback f f)⟩ ⥤ (pullback f f).Modules :=
    (isQuasicoherent.prop _).ι
  have hι {E F} (a : E ⟶ F) : ι.map a = a.hom := rfl
  replace hψ := congrArg ι.map hψ
  simp only [CategoryTheory.Functor.map_comp] at hψ
  simp only [hι, qcohPseudofunctor_mapComp'_inv_toNatTrans_app_hom,
    qcohPseudofunctor_mapComp'_hom_toNatTrans_app_hom f (pullback.fst f f) _ pullback.condition]
    at hψ
  -- Merge the two identifications of `(p₂ ≫ f)^*` and `(p₁ ≫ f)^*` into one.
  have key (M : Y.Modules) :
      (Scheme.Modules.pullbackComp (pullback.snd f f) f).hom.app M ≫
        (Scheme.Modules.pullbackCongr pullback.condition.symm).hom.app M ≫
          (Scheme.Modules.pullbackComp (pullback.fst f f) f).inv.app M =
      ((Scheme.Modules.pullbackComp (pullback.snd f f) f).hom.app M ≫
          (Scheme.Modules.pullbackCongr (rfl : pullback.snd f f ≫ f = _)).hom.app M) ≫
        (Scheme.Modules.pullbackCongr pullback.condition).inv.app M ≫
          (Scheme.Modules.pullbackComp (pullback.fst f f) f).inv.app M := by
    simp [Scheme.Modules.pullbackCongr]
  exact (congrArg (_ ≫ ·) (key B.obj)).trans (hψ.trans (congrArg (· ≫ _) (key A.obj).symm))

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- **Descent of morphisms of quasi-coherent modules along a faithfully flat map of affine
schemes.** For a faithfully flat ring map `φ : R ⟶ S`, `qcohPseudofunctor` is a prestack for the
covering `{Spec φ : Spec S ⟶ Spec R}`: a morphism `f^* A ⟶ f^* B` of quasi-coherent modules on
`Spec S`, for `f = Spec φ`, that is compatible with the canonical descent data comes from a unique
morphism `A ⟶ B`. -/
theorem qcohPseudofunctor_isPrestackFor_singleton_specMap (hφ : φ.hom.FaithfullyFlat) :
    qcohPseudofunctor.IsPrestackFor (Presieve.singleton (Spec.map φ)) := by
  rw [← Presieve.ofArrows_pUnit.{0}, Pseudofunctor.isPrestackFor_ofArrows_iff,
    Functor.FullyFaithful.nonempty_iff_map_bijective]
  rintro (A : QuasicoherentSheaf (Spec R)) (B : QuasicoherentSheaf (Spec R))
  have := isEquivalence_comparison_qcohPseudofunctorMapSpecMapAdjunction φ hφ
  have : Flat (Spec.map φ) := Flat.SpecMap_iff.2 hφ.flat
  let K := Comonad.comparison (qcohPseudofunctorMapSpecMapAdjunction φ)
  refine ⟨fun h₁ h₂ e ↦ K.map_injective (Comonad.Coalgebra.Hom.ext ?_), fun ψ ↦ ?_⟩
  · exact congr(Pseudofunctor.DescentData.Hom.hom $e PUnit.unit)
  -- `ψ` satisfies the descent condition, so it is a morphism of coalgebras for `f^* f_*`, and
  -- comonadicity lifts it to a morphism `A ⟶ B`.
  have : B.obj.IsQuasicoherent := B.property
  have hc := (Scheme.Modules.comp_pullback_map_unit_app_eq_iff (Spec.map φ) (A := A.obj)
    (B := B.obj) (ψ.hom PUnit.unit).hom).2 (qcohPseudofunctor_descentData_hom_comm (Spec.map φ) ψ)
  -- The coalgebra structure of `K.obj M` is `f^*` of the unit (`Comonad.comparison_obj_a`), whose
  -- underlying morphism is `f^*` of the unit for modules
  -- (`qcohPseudofunctorMapSpecMapAdjunction_unit_app_hom`).
  have hu (M : QuasicoherentSheaf (Spec R)) : (K.obj M).a.hom =
      (Scheme.Modules.pullback (Spec.map φ)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M.obj) :=
    congrArg (Scheme.Modules.pullback (Spec.map φ)).map
      (qcohPseudofunctorMapSpecMapAdjunction_unit_app_hom φ M)
  obtain ⟨h, hh⟩ := K.map_surjective
    { f := ψ.hom PUnit.unit
      h := ObjectProperty.hom_ext _
        ((congrArg (· ≫ _) (hu A)).trans (hc.symm.trans (congrArg (_ ≫ ·) (hu B).symm))) }
  exact ⟨h, Pseudofunctor.DescentData.hom_ext fun _ ↦ congrArg Comonad.Coalgebra.Hom.f hh⟩

end TauCeti.AlgebraicGeometry.Descent
