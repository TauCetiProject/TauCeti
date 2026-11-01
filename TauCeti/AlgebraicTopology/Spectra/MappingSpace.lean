/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.AddBasepoint
public import TauCeti.AlgebraicTopology.Spectra.Free
public import TauCeti.CategoryTheory.Limits.Shapes.Products

/-!
# Smashing symmetric spectra with pointed simplicial sets, and mapping spaces

For a symmetric spectrum `X` and a pointed simplicial set `K`, the symmetric spectrum `X ∧ K` has
levels `X_n ∧ K`, with `Σ_n` acting on `X_n` and the sphere acting through `X`. Its right adjoint
in the spectrum variable `Y` is the pointed mapping simplicial set `Map(X, Y)`, whose `m`-simplices
are the spectrum maps `X ∧ Δ[m]₊ ⟶ Y` and whose vertices are the spectrum maps `X ⟶ Y`. These
are the tensors and mapping spaces of the simplicial structure of symmetric spectra of Hovey,
Shipley and Smith; the mapping spaces enter the definition of stable equivalences through maps into
Ω-spectra.

Both are obtained from the native module structure, without reconstructing a sphere action by
hand. Write `G₀ K` for the free symmetric sequence `(SymmetricSequence.free 0).obj K`, which is
`K` in level zero and the point elsewhere. Then `X ∧ K` is the module `X ⊗ G₀ K` given by
`Mod.tensorLeft`, and `Map(X, Y)` is level zero of the object `Hom_S(X, Y)` of `S`-linear maps of
`Mod.ihom`. The adjunction is the composite of `G₀ ⊣ ev₀` with `Mod.ihomAdjunction`.

The level formula `X_n ∧ K ≅ (X ∧ K)_n` holds for the Day convolution `X ⊗ G₀ K` of any symmetric
sequence `X`, and is an instance of the wedge formula for Day convolution: in the wedge over the
subsets `S` of `Fin n` of `X_{#S} ∧ (G₀ K)_{#Sᶜ}`, every summand with `S ≠ Fin n` is the point.

## Main definitions

* `SymmetricSequence.tensorFreeZeroι X K n`: the isomorphism `X_n ∧ K ⟶ (X ⊗ G₀ K)_n`, natural in
  `X` and `K` and `Σ_n`-equivariant.
* `SymmetricSpectrum.levelSmash X`: the functor `K ↦ X ∧ K`.
* `SymmetricSpectrum.mappingSpace X`: the functor `Y ↦ Map(X, Y)`.
* `SymmetricSpectrum.levelSmashMappingSpaceAdjunction X`: the adjunction `X ∧ - ⊣ Map(X, -)`.
* `SymmetricSpectrum.levelSmashUnitIso X`: the unit isomorphism `X ∧ S⁰ ≅ X`.
* `SymmetricSpectrum.mappingSpaceSimplexEquiv`: the `m`-simplices of `Map(X, Y)` are the maps
  `X ∧ Δ[m]₊ ⟶ Y`.
* `SymmetricSpectrum.unitHomMappingSpaceEquiv`: the vertices of `Map(X, Y)`, the based maps
  `S⁰ ⟶ Map(X, Y)`, are the maps `X ⟶ Y`.

These are point-set constructions; deriving them requires the stable model structure.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Sections 1 and 2.
-/

public section

open CategoryTheory MonoidalCategory Limits

namespace TauCeti

open scoped DayFunctor

/-! ### Day convolution with a symmetric sequence concentrated in level zero -/

namespace SymmetricSequence

/-- The inclusion `X_n ∧ K ⟶ (X ⊗ G₀ K)_n` of the summand of the identity shuffle in the wedge
formula for the Day convolution of a symmetric sequence `X` with the free symmetric sequence
`G₀ K` on `K` in level zero. It is an isomorphism (`isIso_tensorFreeZeroι`). -/
noncomputable def tensorFreeZeroι (X : SymmetricSequence.{0}) (K : PointedSSet.{0}) (n : ℕ) :
    X.functor.obj (FiniteBijection.mk n) ⊗ K ⟶
      (X ⊗ (free 0).obj K).functor.obj (FiniteBijection.mk n) :=
  X.functor.obj (FiniteBijection.mk n) ◁ freeι 0 K ≫
    (DayFunctor.η X ((free 0).obj K)).app (FiniteBijection.mk n, FiniteBijection.mk 0) ≫
      (X ⊗ (free 0).obj K).functor.map (ρ_ (FiniteBijection.mk n)).hom

/-- **The level formula** `X_n ∧ K ≅ (X ⊗ G₀ K)_n`: in the wedge formula for `(X ⊗ G₀ K)_n`, every
summand other than `X_n ∧ (G₀ K)₀ ≅ X_n ∧ K` is the point. -/
instance isIso_tensorFreeZeroι (X : SymmetricSequence.{0}) (K : PointedSSet.{0}) (n : ℕ) :
    IsIso (tensorFreeZeroι X K n) := by
  have : IsIso ((DayFunctor.η X ((free 0).obj K)).app
      (FiniteBijection.mk n, FiniteBijection.mk 0) ≫
      (X ⊗ (free 0).obj K).functor.map (ρ_ (FiniteBijection.mk n)).hom) := by
    rw [DayFunctor.η_app_comp_map_eq_tensorHom_comp_shuffleCofan_inj]
    -- The block image of the unitor is all of `Fin n`; every other subset has a nonempty
    -- complement, on which `G₀ K` is the point.
    have hb : FiniteBijection.blockImage (ρ_ (FiniteBijection.mk n)).hom = Finset.univ := by
      rw [← Finset.compl_eq_empty_iff, ← Finset.card_eq_zero,
        FiniteBijection.card_compl_blockImage]
      rfl
    have : IsIso ((DayFunctor.shuffleCofan X ((free 0).obj K) (FiniteBijection.mk n)).inj
        (FiniteBijection.blockImage (ρ_ (FiniteBijection.mk n)).hom)) :=
      Cofan.IsColimit.isIso_inj_of_isInitial (DayFunctor.isColimitShuffleCofan _ _ _) _
        fun S hS ↦ IsInitial.isInitialObj (tensorLeft _) _ (isInitialFreeObj K (by
          rw [hb] at hS
          simpa [Finset.card_eq_zero, Finset.compl_eq_empty_iff] using hS))
    exact IsIso.comp_isIso' inferInstance this
  exact IsIso.comp_isIso' inferInstance this

/-- The level isomorphism `X_n ∧ K ⟶ (X ⊗ G₀ K)_n` is natural in the symmetric sequence `X`. -/
@[reassoc (attr := simp)]
lemma tensorFreeZeroι_naturality_left {X Y : SymmetricSequence.{0}} (f : X ⟶ Y)
    (K : PointedSSet.{0}) (n : ℕ) :
    f.natTrans.app (FiniteBijection.mk n) ▷ K ≫ tensorFreeZeroι Y K n =
      tensorFreeZeroι X K n ≫ (f ▷ (free 0).obj K).natTrans.app (FiniteBijection.mk n) := by
  simp only [tensorFreeZeroι, Category.assoc]
  rw [NatTrans.naturality]
  simp only [tensor_obj]
  rw [DayFunctor.η_app_comp_whiskerRight_natTrans_app_assoc, whisker_exchange_assoc]

/-- The level isomorphism `X_n ∧ K ⟶ (X ⊗ G₀ K)_n` is natural in the pointed simplicial set `K`. -/
@[reassoc (attr := simp)]
lemma tensorFreeZeroι_naturality_right (X : SymmetricSequence.{0}) {K L : PointedSSet.{0}}
    (f : K ⟶ L) (n : ℕ) :
    X.functor.obj (FiniteBijection.mk n) ◁ f ≫ tensorFreeZeroι X L n =
      tensorFreeZeroι X K n ≫ (X ◁ (free 0).map f).natTrans.app (FiniteBijection.mk n) := by
  simp only [tensorFreeZeroι, Category.assoc]
  rw [NatTrans.naturality]
  simp only [tensor_obj]
  rw [DayFunctor.η_app_comp_whiskerLeft_natTrans_app_assoc, ← whiskerLeft_comp_assoc,
    freeι_naturality, whiskerLeft_comp_assoc]

/-- The level isomorphism `X_n ∧ K ⟶ (X ⊗ G₀ K)_n` is `Σ_n`-equivariant, for the action on
`X_n`. -/
@[reassoc (attr := simp)]
lemma map_whiskerRight_comp_tensorFreeZeroι (X : SymmetricSequence.{0}) (K : PointedSSet.{0})
    {n m : ℕ} (σ : FiniteBijection.mk n ⟶ FiniteBijection.mk m) :
    X.functor.map σ ▷ K ≫ tensorFreeZeroι X K m =
      tensorFreeZeroι X K n ≫ (X ⊗ (free 0).obj K).functor.map σ := by
  simp only [tensorFreeZeroι, Category.assoc]
  have e : X.functor.map σ ▷ ((free 0).obj K).functor.obj (FiniteBijection.mk 0) ≫
      (DayFunctor.η X ((free 0).obj K)).app (FiniteBijection.mk m, FiniteBijection.mk 0) =
      (DayFunctor.η X ((free 0).obj K)).app (FiniteBijection.mk n, FiniteBijection.mk 0) ≫
        (X ⊗ (free 0).obj K).functor.map (σ ▷ FiniteBijection.mk 0) := by
    simpa using (DayFunctor.η X ((free 0).obj K)).naturality
      ((σ, 𝟙 _) : (FiniteBijection.mk n, FiniteBijection.mk 0) ⟶
        (FiniteBijection.mk m, FiniteBijection.mk 0))
  rw [← whisker_exchange_assoc]
  slice_lhs 2 3 => rw [e]
  simp only [Category.assoc, ← Functor.map_comp]
  exact congrArg (fun g ↦ _ ≫ _ ≫ (X ⊗ (free 0).obj K).functor.map g) (rightUnitor_naturality σ)

/-- In level `n`, `X ⊗ G₀ S⁰ ≅ X ⊗ 𝟙 ≅ X` is the right unitor `X_n ∧ S⁰ ≅ X_n`. -/
@[reassoc]
lemma tensorFreeZeroι_comp_whiskerLeft_freeZeroUnitIso_hom (X : SymmetricSequence.{0}) (n : ℕ) :
    tensorFreeZeroι X (𝟙_ _) n ≫
      (X ◁ freeZeroUnitIso.hom ≫ (ρ_ X).hom).natTrans.app (FiniteBijection.mk n) =
        (ρ_ _).hom := by
  simp only [tensorFreeZeroι, Category.assoc]
  rw [NatTrans.naturality, DayFunctor.comp_natTrans, NatTrans.comp_app]
  simp only [tensor_obj, Category.assoc]
  rw [DayFunctor.η_app_comp_whiskerLeft_natTrans_app_assoc, ← whiskerLeft_comp_assoc,
    freeι_comp_freeZeroUnitIso_hom]
  have h := DayFunctor.whiskerLeft_ν_comp_η_app_comp_rightUnitor_hom_natTrans_app X
    (FiniteBijection.mk n) =≫ X.functor.map (ρ_ (FiniteBijection.mk n)).hom
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id] at h
  refine h.trans ?_
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

end SymmetricSequence

namespace SymmetricSpectrum

/-- The symmetric spectrum `X ∧ K` of a symmetric spectrum `X` and a pointed simplicial set `K`,
as a functor of `K`: the Day convolution `X ⊗ G₀ K` with the free symmetric sequence on `K` in
level zero, with the sphere acting on `X`. Its levels are `X_n ∧ K`
(`SymmetricSequence.tensorFreeZeroι`). -/
-- An abbreviation, so that the levels of `X ∧ K` are those of the Day convolution `X ⊗ G₀ K`
-- without transports.
noncomputable abbrev levelSmash (X : SymmetricSpectrum) : PointedSSet.{0} ⥤ SymmetricSpectrum where
  obj K := (Mod.tensorLeft X).obj ((SymmetricSequence.free 0).obj K)
  map f := (Mod.tensorLeft X).map ((SymmetricSequence.free 0).map f)

/-- The pointed mapping simplicial set `Map(X, Y)` of symmetric spectra, as a functor of `Y`:
level zero of the object `Hom_S(X, Y)` of `S`-linear maps. Its `m`-simplices are the spectrum maps
`X ∧ Δ[m]₊ ⟶ Y` (`mappingSpaceSimplexEquiv`). -/
-- An abbreviation, so that maps into `Map(X, Y)` are maps into the level of `Hom_S(X, Y)`.
noncomputable abbrev mappingSpace (X : SymmetricSpectrum) :
    SymmetricSpectrum ⥤ PointedSSet.{0} where
  obj Y := ((Mod.ihom X).obj Y).functor.obj (FiniteBijection.mk 0)
  map g := ((Mod.ihom X).map g).natTrans.app (FiniteBijection.mk 0)

/-- Smashing a symmetric spectrum `X` with pointed simplicial sets is left adjoint to the mapping
space `Map(X, -)`: spectrum maps `X ∧ K ⟶ Y` are based maps `K ⟶ Map(X, Y)`. -/
noncomputable def levelSmashMappingSpaceAdjunction (X : SymmetricSpectrum) :
    levelSmash X ⊣ mappingSpace X :=
  (SymmetricSequence.freeEvaluationAdjunction 0).comp (Mod.ihomAdjunction X)

/-- The adjunction `X ∧ - ⊣ Map(X, -)` curries a spectrum map `X ∧ K ⟶ Y` into `Hom_S(X, Y)` and
restricts it to the generator `K ⟶ (G₀ K)₀`. -/
lemma levelSmashMappingSpaceAdjunction_homEquiv_apply (X : SymmetricSpectrum)
    {K : PointedSSet.{0}} {Y : SymmetricSpectrum} (f : (levelSmash X).obj K ⟶ Y) :
    (levelSmashMappingSpaceAdjunction X).homEquiv K Y f =
      SymmetricSequence.freeι 0 K ≫
        (Mod.ihomHomEquiv X _ Y f).natTrans.app (FiniteBijection.mk 0) := by
  have h := congrFun (congrFun ((SymmetricSequence.freeEvaluationAdjunction 0).comp_homEquiv
    (Mod.ihomAdjunction X)) K) Y
  refine (congrFun (congrArg DFunLike.coe h) f).trans ?_
  rw [Mod.ihomAdjunction_homEquiv]
  refine ((SymmetricSequence.freeEvaluationAdjunction 0).homEquiv_unit K _
    (Mod.ihomHomEquiv X _ Y f)).trans ?_
  rw [SymmetricSequence.freeEvaluationAdjunction_unit_app]
  -- The right adjoint evaluates a map of symmetric sequences at level zero.
  rfl

/-- The inverse of the adjunction `X ∧ - ⊣ Map(X, -)` extends a based map `K ⟶ Map(X, Y)` to a
map of symmetric sequences `G₀ K ⟶ Hom_S(X, Y)` and uncurries it. -/
lemma levelSmashMappingSpaceAdjunction_homEquiv_symm_apply (X : SymmetricSpectrum)
    {K : PointedSSet.{0}} {Y : SymmetricSpectrum} (g : K ⟶ (mappingSpace X).obj Y) :
    ((levelSmashMappingSpaceAdjunction X).homEquiv K Y).symm g =
      (Mod.ihomHomEquiv X _ Y).symm
        (((SymmetricSequence.freeEvaluationAdjunction 0).homEquiv K _).symm g) := by
  have h := congrFun (congrFun ((SymmetricSequence.freeEvaluationAdjunction 0).comp_homEquiv
    (Mod.ihomAdjunction X)) K) Y
  rw [Mod.ihomAdjunction_homEquiv] at h
  -- The inverse of a composite of bijections applies the inverses in turn.
  exact congrArg (fun e ↦ e.symm g) h

/-- The `m`-simplices of the mapping space `Map(X, Y)` are the spectrum maps `X ∧ Δ[m]₊ ⟶ Y`. -/
noncomputable def mappingSpaceSimplexEquiv (X Y : SymmetricSpectrum) (m : SimplexCategory) :
    ((mappingSpace X).obj Y).right.obj (Opposite.op m) ≃
      ((levelSmash X).obj (PointedSSet.addBasepoint.obj (SSet.stdSimplex.obj m)) ⟶ Y) :=
  SSet.yonedaEquiv.symm.trans ((PointedSSet.addBasepointHomEquiv _ _).symm.trans
    ((levelSmashMappingSpaceAdjunction X).homEquiv _ _).symm)

/-- An `m`-simplex of `Map(X, Y)` gives the spectrum map `X ∧ Δ[m]₊ ⟶ Y` adjoint to the based map
`Δ[m]₊ ⟶ Map(X, Y)` that it classifies. -/
lemma mappingSpaceSimplexEquiv_apply (X Y : SymmetricSpectrum) (m : SimplexCategory)
    (x : ((mappingSpace X).obj Y).right.obj (Opposite.op m)) :
    mappingSpaceSimplexEquiv X Y m x =
      ((levelSmashMappingSpaceAdjunction X).homEquiv _ _).symm
        ((PointedSSet.addBasepointHomEquiv _ _).symm (SSet.yonedaEquiv.symm x)) :=
  (rfl)

/-- A spectrum map `X ∧ Δ[m]₊ ⟶ Y` gives the `m`-simplex of `Map(X, Y)` classifying its adjoint
`Δ[m] ⟶ Map(X, Y)`. -/
lemma mappingSpaceSimplexEquiv_symm_apply (X Y : SymmetricSpectrum) (m : SimplexCategory)
    (f : (levelSmash X).obj (PointedSSet.addBasepoint.obj (SSet.stdSimplex.obj m)) ⟶ Y) :
    (mappingSpaceSimplexEquiv X Y m).symm f =
      SSet.yonedaEquiv (PointedSSet.addBasepointHomEquiv _ _
        ((levelSmashMappingSpaceAdjunction X).homEquiv _ _ f)) :=
  (rfl)

/-- The unit isomorphism `X ∧ S⁰ ≅ X`, through `G₀ S⁰ ≅ 𝟙` and the right unitor. In every level
it is the right unitor `X_n ∧ S⁰ ≅ X_n` (`tensorFreeZeroι_comp_levelSmashUnitIso_hom`). -/
noncomputable def levelSmashUnitIso (X : SymmetricSpectrum) : (levelSmash X).obj (𝟙_ _) ≅ X :=
  (Mod.tensorLeft X).mapIso SymmetricSequence.freeZeroUnitIso ≪≫ Mod.tensorLeftUnitIso X

/-- In level `n`, the unit isomorphism `X ∧ S⁰ ≅ X` is the right unitor `X_n ∧ S⁰ ≅ X_n`. -/
@[reassoc (attr := simp)]
lemma tensorFreeZeroι_comp_levelSmashUnitIso_hom (X : SymmetricSpectrum) (n : ℕ) :
    SymmetricSequence.tensorFreeZeroι X.X (𝟙_ _) n ≫
      (evaluation n).map (levelSmashUnitIso X).hom = (ρ_ _).hom := by
  have h := SymmetricSequence.tensorFreeZeroι_comp_whiskerLeft_freeZeroUnitIso_hom X.X n
  simp only [levelSmashUnitIso, Iso.trans_hom, Functor.mapIso_hom, Mod.comp_hom',
    Mod.tensorLeftUnitIso_hom_hom]
  exact h

/-- The vertices of the mapping space `Map(X, Y)`, the based maps `S⁰ ⟶ Map(X, Y)`, are the
spectrum maps `X ⟶ Y`. -/
noncomputable def unitHomMappingSpaceEquiv (X Y : SymmetricSpectrum) :
    (𝟙_ PointedSSet.{0} ⟶ (mappingSpace X).obj Y) ≃ (X ⟶ Y) :=
  ((levelSmashMappingSpaceAdjunction X).homEquiv _ _).symm.trans
    ((levelSmashUnitIso X).homCongr (Iso.refl Y))

/-- A vertex of `Map(X, Y)` gives the spectrum map `X ≅ X ∧ S⁰ ⟶ Y` adjoint to it. -/
lemma unitHomMappingSpaceEquiv_apply (X Y : SymmetricSpectrum)
    (g : 𝟙_ PointedSSet.{0} ⟶ (mappingSpace X).obj Y) :
    unitHomMappingSpaceEquiv X Y g =
      (levelSmashUnitIso X).inv ≫ ((levelSmashMappingSpaceAdjunction X).homEquiv _ _).symm g := by
  simp [unitHomMappingSpaceEquiv]

end SymmetricSpectrum

end TauCeti
