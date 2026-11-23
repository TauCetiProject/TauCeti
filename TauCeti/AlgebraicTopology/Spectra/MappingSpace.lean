/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Parametrized
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
`Mod.ihom`. The adjunction is the composite of `G₀ ⊣ ev₀` with `Mod.ihomAdjunction`, and the
two-variable adjunction `levelSmashBifunctor ⊣₂ mappingSpaceBifunctor` is obtained from
`Mod.ihomAdjunction₂` using Mathlib's `CategoryTheory.ParametrizedAdjunction` by Joël Riou.

The level formula `X_n ∧ K ≅ (X ∧ K)_n` holds for the Day convolution `X ⊗ G₀ K` of any symmetric
sequence `X`, and is an instance of the wedge formula for Day convolution: in the wedge over the
subsets `S` of `Fin n` of `X_{#S} ∧ (G₀ K)_{#Sᶜ}`, every summand with `S ≠ Fin n` is the point.

## Main definitions

* `SymmetricSequence.tensorFreeZeroι X K n`: the isomorphism `X_n ∧ K ⟶ (X ⊗ G₀ K)_n`, natural in
  `X` and `K` and `Σ_n`-equivariant.
* `SymmetricSpectrum.levelSmash X`, `SymmetricSpectrum.levelSmashRight K`, and
  `SymmetricSpectrum.levelSmashBifunctor`: the functor `(X, K) ↦ X ∧ K`.
* `SymmetricSpectrum.mappingSpace X` and `SymmetricSpectrum.mappingSpaceBifunctor`: the functor
  `(X, Y) ↦ Map(X, Y)`.
* `SymmetricSpectrum.levelSmashMappingSpaceAdjunction X` and
  `SymmetricSpectrum.levelSmashMappingSpaceAdjunction₂`: the one- and two-variable adjunctions
  `X ∧ - ⊣ Map(X, -)`.
* `SymmetricSpectrum.levelSmashUnitIso X`: the unit isomorphism `X ∧ S⁰ ≅ X`.
* `SymmetricSpectrum.mappingSpaceSimplexEquiv`: the `m`-simplices of `Map(X, Y)` are the maps
  `X ∧ Δ[m]₊ ⟶ Y`.
* `SymmetricSpectrum.unitHomMappingSpaceEquiv`: the vertices of `Map(X, Y)`, the based maps
  `S⁰ ⟶ Map(X, Y)`, are the maps `X ⟶ Y`.

These are point-set constructions; deriving them requires the stable model structure.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Sections 1, 2.2, and 3.1.
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

/-- The identity-shuffle inclusion inserts the level-zero generator and the right unitor. -/
lemma tensorFreeZeroι_def (X : SymmetricSequence.{0}) (K : PointedSSet.{0}) (n : ℕ) :
    tensorFreeZeroι X K n = X.functor.obj (FiniteBijection.mk n) ◁ freeι 0 K ≫
      (DayFunctor.η X ((free 0).obj K)).app (FiniteBijection.mk n, FiniteBijection.mk 0) ≫
        (X ⊗ (free 0).obj K).functor.map (ρ_ (FiniteBijection.mk n)).hom := (rfl)

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

open MonoidalClosed Opposite

/-- The symmetric spectrum `X ∧ K` of a symmetric spectrum `X` and a pointed simplicial set `K`,
as a functor of `K`: the Day convolution `X ⊗ G₀ K` with the free symmetric sequence on `K` in
level zero, with the sphere acting on `X`. Its levels are `X_n ∧ K`
(`SymmetricSequence.tensorFreeZeroι`). -/
-- An abbreviation, so that the levels of `X ∧ K` are those of the Day convolution `X ⊗ G₀ K`
-- without transports.
noncomputable abbrev levelSmash (X : SymmetricSpectrum) : PointedSSet.{0} ⥤ SymmetricSpectrum where
  obj K := (Mod.tensorLeft X).obj ((SymmetricSequence.free 0).obj K)
  map f := (Mod.tensorLeft X).map ((SymmetricSequence.free 0).map f)

/-- Smashing every level with a fixed pointed simplicial set, with the sphere acting on the
spectrum coordinate. On objects this is the existing `levelSmash` construction. -/
noncomputable abbrev levelSmashRight (K : PointedSSet.{0}) :
    SymmetricSpectrum ⥤ SymmetricSpectrum :=
  Mod.tensorRight ((SymmetricSequence.free 0).obj K)

/-- The pointed mapping simplicial set `Map(X, Y)` of symmetric spectra, as a functor of `Y`:
level zero of the object `Hom_S(X, Y)` of `S`-linear maps. Its `m`-simplices are the spectrum maps
`X ∧ Δ[m]₊ ⟶ Y` (`mappingSpaceSimplexEquiv`). -/
-- An abbreviation, so that maps into `Map(X, Y)` are maps into the level of `Hom_S(X, Y)`. It is
-- the composite that `levelSmashMappingSpaceAdjunction` produces: written out with its own `obj`
-- and `map`, the kernel needs far too long to match the two outside the module system, as it must
-- for the equation lemma `levelSmashMappingSpaceAdjunction.eq_1` (which doc-gen4 asks for).
noncomputable abbrev mappingSpace (X : SymmetricSpectrum) :
    SymmetricSpectrum ⥤ PointedSSet.{0} :=
  Mod.ihom X ⋙ (DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor ⋙
    (CategoryTheory.evaluation FiniteBijection PointedSSet.{0}).obj (FiniteBijection.mk 0)

/-- The bifunctor `(X, K) ↦ X ∧ K` smashing a symmetric spectrum levelwise with a pointed
simplicial set. Fixing `X` recovers `levelSmash X`, and fixing `K` recovers `levelSmashRight K`. -/
@[expose]
noncomputable def levelSmashBifunctor :
    SymmetricSpectrum ⥤ PointedSSet.{0} ⥤ SymmetricSpectrum :=
  Mod.curriedTensor ⋙ (Functor.whiskeringLeft _ _ _).obj (SymmetricSequence.free 0)

/-- Fixing `X` in `levelSmashBifunctor` gives `levelSmash X`. -/
@[simp]
lemma levelSmashBifunctor_obj (X : SymmetricSpectrum) :
    levelSmashBifunctor.obj X = levelSmash X :=
  (rfl)

/-- Fixing `K` in `levelSmashBifunctor` gives `levelSmashRight K`. -/
@[simp]
lemma levelSmashBifunctor_flip_obj (K : PointedSSet.{0}) :
    levelSmashBifunctor.flip.obj K = levelSmashRight K :=
  (rfl)

/-- On maps in the spectrum variable, `levelSmashBifunctor` applies `levelSmashRight K`. -/
@[simp]
lemma levelSmashBifunctor_map_app {X Y : SymmetricSpectrum} (f : X ⟶ Y) (K : PointedSSet.{0}) :
    (levelSmashBifunctor.map f).app K = (levelSmashRight K).map f :=
  (rfl)

/-- On maps in the simplicial variable, `levelSmashBifunctor.flip` applies `levelSmash X`. -/
lemma levelSmashBifunctor_flip_map_app {K L : PointedSSet.{0}} (g : K ⟶ L)
    (X : SymmetricSpectrum) :
    (levelSmashBifunctor.flip.map g).app X = (levelSmash X).map g :=
  (rfl)

/-- The pointed mapping-space bifunctor `(X, Y) ↦ Map(X, Y)` of symmetric spectra, contravariant
in the source spectrum `X` and covariant in the target spectrum `Y`. Fixing `X` recovers
`mappingSpace X`, while a map `f : X ⟶ X'` acts by level-zero internal-hom precomposition. -/
@[expose]
noncomputable def mappingSpaceBifunctor :
    SymmetricSpectrumᵒᵖ ⥤ SymmetricSpectrum ⥤ PointedSSet.{0} :=
  MonoidalClosed.internalHom ⋙
    (Functor.whiskeringRight SymmetricSpectrum SymmetricSpectrum PointedSSet.{0}).obj
      (evaluation 0)

/-- Fixing `X` in `mappingSpaceBifunctor` gives `mappingSpace X.unop`. -/
@[simp]
lemma mappingSpaceBifunctor_obj (X : SymmetricSpectrumᵒᵖ) :
    mappingSpaceBifunctor.obj X = mappingSpace X.unop :=
  (rfl)

/-- On maps in the source spectrum variable, `mappingSpaceBifunctor` applies level-zero
internal-hom precomposition. -/
@[simp]
lemma mappingSpaceBifunctor_map_app {X X' : SymmetricSpectrumᵒᵖ} (f : X ⟶ X')
    (Y : SymmetricSpectrum) :
    (mappingSpaceBifunctor.map f).app Y = (evaluation 0).map ((MonoidalClosed.pre f.unop).app Y) :=
  (rfl)

/-- Smashing a symmetric spectrum `X` with pointed simplicial sets is left adjoint to the mapping
space `Map(X, -)`: spectrum maps `X ∧ K ⟶ Y` are based maps `K ⟶ Map(X, Y)`. -/
noncomputable def levelSmashMappingSpaceAdjunction (X : SymmetricSpectrum) :
    levelSmash X ⊣ mappingSpace X :=
  (SymmetricSequence.freeEvaluationAdjunction 0).comp (Mod.ihomAdjunction X)

/-- Smashing a fixed symmetric spectrum `X` with pointed simplicial sets is a left adjoint, hence
preserves colimits of all sizes. -/
instance (X : SymmetricSpectrum) : (levelSmash X).IsLeftAdjoint :=
  (levelSmashMappingSpaceAdjunction X).isLeftAdjoint

/-- Taking the pointed mapping space out of a fixed symmetric spectrum `X` is a right adjoint, hence
preserves limits of all sizes. -/
instance (X : SymmetricSpectrum) : (mappingSpace X).IsRightAdjoint :=
  (levelSmashMappingSpaceAdjunction X).isRightAdjoint

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

/-- The parametrized adjunction `levelSmashBifunctor ⊣₂ mappingSpaceBifunctor`: spectrum maps
`X ∧ K ⟶ Y` correspond naturally in all three variables to based maps `K ⟶ Map(X, Y)`. -/
noncomputable def levelSmashMappingSpaceAdjunction₂ :
    levelSmashBifunctor ⊣₂ mappingSpaceBifunctor :=
  ParametrizedAdjunction.mk' levelSmashMappingSpaceAdjunction fun {X Y} f {K} {Z} g ↦ by
    -- Expose `levelSmash`, `mappingSpace`, and `Mod.internalHom` in the
    -- `ParametrizedAdjunction.mk'` goal.
    change (levelSmash Y).obj K ⟶ Z at g
    let p : (Mod.internalHom Y).obj Z ⟶ (Mod.internalHom X).obj Z := (MonoidalClosed.pre f).app Z
    change (levelSmashMappingSpaceAdjunction X).homEquiv K Z ((levelSmashRight K).map f ≫ g) =
      (levelSmashMappingSpaceAdjunction Y).homEquiv K Z g ≫ (evaluation 0).map p
    have hcur : Mod.ihomHomEquiv X ((SymmetricSequence.free 0).obj K) Z
        ((levelSmashRight K).map f ≫ g) =
        Mod.ihomHomEquiv Y ((SymmetricSequence.free 0).obj K) Z g ≫ p.hom := by
      let g' : (Mod.curriedTensor.obj Y).obj ((SymmetricSequence.free 0).obj K) ⟶ Z := g
      have h := Mod.ihomAdjunction₂.homEquiv_naturality_one f g'
      rw [Mod.ihomAdjunction₂_homEquiv_apply Y, Mod.ihomAdjunction₂_homEquiv_apply X] at h
      dsimp only [Mod.curriedTensor_map_app, Mod.ihomFunctor_map, unop_op] at h
      have h' : Mod.ihomHomEquiv X ((SymmetricSequence.free 0).obj K) Z
          ((levelSmashRight K).map f ≫ g) =
          Mod.ihomHomEquiv Y ((SymmetricSequence.free 0).obj K) Z g ≫ (Mod.ihomPre f).app Z := h
      exact h'.trans (by rw [← Mod.pre_app_hom_eq_ihomPre_app])
    rw [levelSmashMappingSpaceAdjunction_homEquiv_apply,
      levelSmashMappingSpaceAdjunction_homEquiv_apply, hcur, DayFunctor.comp_natTrans,
      NatTrans.comp_app]
    exact (Category.assoc _ _ _).symm

/-- At each spectrum `X`, `levelSmashMappingSpaceAdjunction₂` specializes to
`levelSmashMappingSpaceAdjunction X`. -/
@[simp]
lemma levelSmashMappingSpaceAdjunction₂_adj (X : SymmetricSpectrum) :
    levelSmashMappingSpaceAdjunction₂.adj X = levelSmashMappingSpaceAdjunction X :=
  (rfl)

/-- The bijection of `levelSmashMappingSpaceAdjunction₂` is that of
`levelSmashMappingSpaceAdjunction X`. -/
lemma levelSmashMappingSpaceAdjunction₂_homEquiv_apply (X : SymmetricSpectrum)
    {K : PointedSSet.{0}} {Y : SymmetricSpectrum}
    (f : (levelSmashBifunctor.obj X).obj K ⟶ Y) :
    levelSmashMappingSpaceAdjunction₂.homEquiv f =
      (levelSmashMappingSpaceAdjunction X).homEquiv K Y f :=
  (rfl)

instance (X : SymmetricSpectrum) : (levelSmashBifunctor.obj X).IsLeftAdjoint :=
  (levelSmashMappingSpaceAdjunction X).isLeftAdjoint

instance (X : SymmetricSpectrumᵒᵖ) : (mappingSpaceBifunctor.obj X).IsRightAdjoint :=
  (levelSmashMappingSpaceAdjunction X.unop).isRightAdjoint

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

/-- The underlying map of the unit isomorphism `X ∧ S⁰ ≅ X`. -/
lemma levelSmashUnitIso_hom_hom (X : SymmetricSpectrum) :
    (levelSmashUnitIso X).hom.hom =
      X.X ◁ SymmetricSequence.freeZeroUnitIso.hom ≫ (ρ_ X.X).hom := by
  simp only [levelSmashUnitIso, Iso.trans_hom, Functor.mapIso_hom, Mod.comp_hom',
    Mod.tensorLeftUnitIso_hom_hom]
  rfl

/-- In level `n`, the unit isomorphism `X ∧ S⁰ ≅ X` is the right unitor `X_n ∧ S⁰ ≅ X_n`. -/
@[reassoc (attr := simp)]
lemma tensorFreeZeroι_comp_levelSmashUnitIso_hom (X : SymmetricSpectrum) (n : ℕ) :
    SymmetricSequence.tensorFreeZeroι X.X (𝟙_ _) n ≫
      (evaluation n).map (levelSmashUnitIso X).hom = (ρ_ _).hom := by
  have h : (evaluation n).map (levelSmashUnitIso X).hom =
      (X.X ◁ SymmetricSequence.freeZeroUnitIso.hom ≫ (ρ_ X.X).hom).natTrans.app
        (FiniteBijection.mk n) :=
    congrArg (fun g ↦ g.natTrans.app (FiniteBijection.mk n)) (levelSmashUnitIso_hom_hom X)
  rw [h]
  exact SymmetricSequence.tensorFreeZeroι_comp_whiskerLeft_freeZeroUnitIso_hom X.X n

/-- The unit isomorphism `X ∧ S⁰ ≅ X` is natural in `X`. -/
@[simp↓, reassoc (attr := simp↓)]
lemma levelSmashBifunctor_map_app_comp_levelSmashUnitIso_hom {X X' : SymmetricSpectrum}
    (f : X ⟶ X') :
    (levelSmashBifunctor.map f).app (𝟙_ _) ≫ (levelSmashUnitIso X').hom =
      (levelSmashUnitIso X).hom ≫ f := by
  have h₁ : f.hom ▷ (SymmetricSequence.free 0).obj (𝟙_ _) ≫
      X'.X ◁ SymmetricSequence.freeZeroUnitIso.hom =
      X.X ◁ SymmetricSequence.freeZeroUnitIso.hom ≫ f.hom ▷ 𝟙_ SymmetricSequence := by
    have e := congrArg Mod.Hom.hom
      ((Mod.curriedTensor.map f).naturality SymmetricSequence.freeZeroUnitIso.hom).symm
    rw [Mod.comp_hom', Mod.comp_hom'] at e
    exact e
  have h₂ : f.hom ▷ 𝟙_ SymmetricSequence ≫ (ρ_ X'.X).hom = (ρ_ X.X).hom ≫ f.hom := by
    have e := congrArg Mod.Hom.hom
      ((Mod.tensorRightUnitIso (A := SymmetricSequence.sphere)).hom.naturality f)
    rw [Mod.comp_hom', Mod.comp_hom', Mod.tensorRightUnitIso_hom_app,
      Mod.tensorRightUnitIso_hom_app, Mod.tensorLeftUnitIso_hom_hom,
      Mod.tensorLeftUnitIso_hom_hom, Functor.id_map] at e
    exact e
  dsimp only [levelSmashBifunctor, Mod.curriedTensor, Functor.comp_map,
    Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app]
  apply Mod.Hom.ext
  rw [Mod.comp_hom', Mod.comp_hom', levelSmashUnitIso_hom_hom, levelSmashUnitIso_hom_hom]
  simp only [Mod.Hom.mk'_hom]
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

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

/-- A spectrum map `X ⟶ Y` gives the vertex of `Map(X, Y)` adjoint to `X ∧ S⁰ ≅ X ⟶ Y`. -/
lemma unitHomMappingSpaceEquiv_symm_apply (X Y : SymmetricSpectrum) (f : X ⟶ Y) :
    (unitHomMappingSpaceEquiv X Y).symm f =
      (levelSmashMappingSpaceAdjunction X).homEquiv _ _ ((levelSmashUnitIso X).hom ≫ f) := by
  simp [unitHomMappingSpaceEquiv]

/-- `Map(f, Y)` sends the vertex corresponding to `g : X' ⟶ Y` to the vertex corresponding to
`f ≫ g`. -/
@[simp↓, reassoc (attr := simp↓)]
lemma unitHomMappingSpaceEquiv_symm_comp_mappingSpaceBifunctor_map_app {X X' Y : SymmetricSpectrum}
    (f : X ⟶ X') (g : X' ⟶ Y) :
    (unitHomMappingSpaceEquiv X' Y).symm g ≫ (mappingSpaceBifunctor.map f.op).app Y =
      (unitHomMappingSpaceEquiv X Y).symm (f ≫ g) := by
  rw [unitHomMappingSpaceEquiv_symm_apply, unitHomMappingSpaceEquiv_symm_apply]
  have h1 := levelSmashMappingSpaceAdjunction₂.homEquiv_naturality_one f
    ((levelSmashUnitIso X').hom ≫ g)
  have h2 := congrArg ((levelSmashMappingSpaceAdjunction X).homEquiv _ Y)
    (levelSmashBifunctor_map_app_comp_levelSmashUnitIso_hom_assoc f g)
  exact h1.symm.trans h2

/-- Postcomposing a vertex `S⁰ ⟶ Map(X', Y)` with `Map(f, Y)` precomposes the corresponding
spectrum map `X' ⟶ Y` with `f : X ⟶ X'`. -/
@[simp↓]
lemma unitHomMappingSpaceEquiv_comp_mappingSpaceBifunctor_map_app {X X' Y : SymmetricSpectrum}
    (f : X ⟶ X') (g : 𝟙_ PointedSSet.{0} ⟶ (mappingSpace X').obj Y) :
    unitHomMappingSpaceEquiv X Y (g ≫ (mappingSpaceBifunctor.map f.op).app Y) =
      f ≫ unitHomMappingSpaceEquiv X' Y g := by
  apply (unitHomMappingSpaceEquiv X Y).symm.injective
  rw [Equiv.symm_apply_apply, ← unitHomMappingSpaceEquiv_symm_comp_mappingSpaceBifunctor_map_app,
    Equiv.symm_apply_apply]
  rfl

/-- `Map(X, k)` sends the vertex corresponding to `f : X ⟶ Y` to the vertex corresponding to
`f ≫ k`. -/
@[simp↓, reassoc (attr := simp↓)]
lemma unitHomMappingSpaceEquiv_symm_comp_mappingSpace_map {X Y Y' : SymmetricSpectrum}
    (f : X ⟶ Y) (k : Y ⟶ Y') :
    (unitHomMappingSpaceEquiv X Y).symm f ≫ (mappingSpace X).map k =
      (unitHomMappingSpaceEquiv X Y').symm (f ≫ k) := by
  rw [unitHomMappingSpaceEquiv_symm_apply, unitHomMappingSpaceEquiv_symm_apply,
    ← (levelSmashMappingSpaceAdjunction X).homEquiv_naturality_right, Category.assoc]

/-- Postcomposing a vertex `S⁰ ⟶ Map(X, Y)` with `Map(X, k)` postcomposes the corresponding
spectrum map `X ⟶ Y` with `k : Y ⟶ Y'`. -/
@[simp↓]
lemma unitHomMappingSpaceEquiv_comp_mappingSpace_map {X Y Y' : SymmetricSpectrum}
    (g : 𝟙_ PointedSSet.{0} ⟶ (mappingSpace X).obj Y) (k : Y ⟶ Y') :
    unitHomMappingSpaceEquiv X Y' (g ≫ (mappingSpace X).map k) =
      unitHomMappingSpaceEquiv X Y g ≫ k := by
  rw [unitHomMappingSpaceEquiv_apply, unitHomMappingSpaceEquiv_apply, Category.assoc,
    ← (levelSmashMappingSpaceAdjunction X).homEquiv_naturality_right_symm]

/-- Applying `Map(f, Y)` to an `m`-simplex of `Map(X', Y)` precomposes the corresponding
spectrum map `X' ∧ Δ[m]₊ ⟶ Y` with `f ∧ Δ[m]₊`. -/
@[simp↓]
lemma mappingSpaceSimplexEquiv_mappingSpaceBifunctor_map_app {X X' Y : SymmetricSpectrum}
    (f : X ⟶ X') (n : SimplexCategory)
    (x : ((mappingSpace X').obj Y).right.obj (Opposite.op n)) :
    mappingSpaceSimplexEquiv X Y n (((mappingSpaceBifunctor.map f.op).app Y).right.app _ x) =
      (levelSmashBifunctor.map f).app _ ≫ mappingSpaceSimplexEquiv X' Y n x := by
  -- Elaborate the domain of `Map(f, Y)` as `mappingSpace X'` so `rw` matches `x` at implicit
  -- transparency.
  let m : (mappingSpace X').obj Y ⟶ (mappingSpace X).obj Y :=
    (mappingSpaceBifunctor.map f.op).app Y
  change mappingSpaceSimplexEquiv X Y n (m.right.app _ x) = _
  rw [mappingSpaceSimplexEquiv_apply, mappingSpaceSimplexEquiv_apply,
    ← SSet.yonedaEquiv_symm_comp x m.right,
    ← PointedSSet.addBasepointForgetAdjunction_homEquiv,
    ← PointedSSet.addBasepointForgetAdjunction_homEquiv]
  have h1 := PointedSSet.addBasepointForgetAdjunction.homEquiv_naturality_right_symm
    (SSet.yonedaEquiv.symm x) m
  rw [Under.forget_map] at h1
  have h2 := levelSmashMappingSpaceAdjunction₂.homEquiv_symm_naturality_one f
    ((PointedSSet.addBasepointForgetAdjunction.homEquiv (SSet.stdSimplex.obj n)
      ((mappingSpace X').obj Y)).symm (SSet.yonedaEquiv.symm x))
  simpa only [levelSmashMappingSpaceAdjunction₂_adj] using h1.symm ▸ h2

/-- `Map(f, Y)` sends the `m`-simplex corresponding to `g : X' ∧ Δ[m]₊ ⟶ Y` to the `m`-simplex
corresponding to `(f ∧ Δ[m]₊) ≫ g`. -/
@[simp↓]
lemma mappingSpaceBifunctor_map_app_mappingSpaceSimplexEquiv_symm {X X' Y : SymmetricSpectrum}
    (f : X ⟶ X') (n : SimplexCategory)
    (g : (levelSmash X').obj (PointedSSet.addBasepoint.obj (SSet.stdSimplex.obj n)) ⟶ Y) :
    ((mappingSpaceBifunctor.map f.op).app Y).right.app _
        ((mappingSpaceSimplexEquiv X' Y n).symm g) =
      (mappingSpaceSimplexEquiv X Y n).symm ((levelSmashBifunctor.map f).app _ ≫ g) := by
  apply (mappingSpaceSimplexEquiv X Y n).injective
  rw [mappingSpaceSimplexEquiv_mappingSpaceBifunctor_map_app, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  rfl

/-- Applying `Map(X, k)` to an `m`-simplex of `Map(X, Y)` postcomposes the corresponding spectrum
map `X ∧ Δ[m]₊ ⟶ Y` with `k : Y ⟶ Y'`. -/
@[simp↓]
lemma mappingSpaceSimplexEquiv_mappingSpace_map_app {X Y Y' : SymmetricSpectrum}
    (k : Y ⟶ Y') (n : SimplexCategory)
    (x : ((mappingSpace X).obj Y).right.obj (Opposite.op n)) :
    mappingSpaceSimplexEquiv X Y' n (((mappingSpace X).map k).right.app _ x) =
      mappingSpaceSimplexEquiv X Y n x ≫ k := by
  rw [mappingSpaceSimplexEquiv_apply, mappingSpaceSimplexEquiv_apply,
    ← SSet.yonedaEquiv_symm_comp x ((mappingSpace X).map k).right,
    ← PointedSSet.addBasepointForgetAdjunction_homEquiv,
    ← PointedSSet.addBasepointForgetAdjunction_homEquiv]
  have h := PointedSSet.addBasepointForgetAdjunction.homEquiv_naturality_right_symm
    (SSet.yonedaEquiv.symm x) ((mappingSpace X).map k)
  rw [Under.forget_map] at h
  rw [h, (levelSmashMappingSpaceAdjunction X).homEquiv_naturality_right_symm]

/-- `Map(X, k)` sends the `m`-simplex corresponding to `g : X ∧ Δ[m]₊ ⟶ Y` to the `m`-simplex
corresponding to `g ≫ k`. -/
@[simp↓]
lemma mappingSpace_map_app_mappingSpaceSimplexEquiv_symm {X Y Y' : SymmetricSpectrum}
    (k : Y ⟶ Y') (n : SimplexCategory)
    (g : (levelSmash X).obj (PointedSSet.addBasepoint.obj (SSet.stdSimplex.obj n)) ⟶ Y) :
    ((mappingSpace X).map k).right.app _ ((mappingSpaceSimplexEquiv X Y n).symm g) =
      (mappingSpaceSimplexEquiv X Y' n).symm (g ≫ k) := by
  apply (mappingSpaceSimplexEquiv X Y' n).injective
  rw [mappingSpaceSimplexEquiv_mappingSpace_map_app, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

/-- Restricting an `n`-simplex of `Map(X, Y)` along `α : m ⟶ n` precomposes the corresponding
spectrum map `X ∧ Δ[n]₊ ⟶ Y` with `X ∧ (Δ[α])₊`. -/
@[simp↓]
lemma mappingSpaceSimplexEquiv_map (X Y : SymmetricSpectrum) {m n : SimplexCategory}
    (α : m ⟶ n) (x : ((mappingSpace X).obj Y).right.obj (Opposite.op n)) :
    mappingSpaceSimplexEquiv X Y m (((mappingSpace X).obj Y).right.map α.op x) =
      (levelSmash X).map (PointedSSet.addBasepoint.map (SSet.stdSimplex.map α)) ≫
        mappingSpaceSimplexEquiv X Y n x := by
  rw [mappingSpaceSimplexEquiv_apply, mappingSpaceSimplexEquiv_apply,
    ← SSet.yonedaEquiv_symm_naturality_left,
    ← PointedSSet.addBasepointForgetAdjunction_homEquiv,
    ← PointedSSet.addBasepointForgetAdjunction_homEquiv,
    PointedSSet.addBasepointForgetAdjunction.homEquiv_naturality_left_symm]
  exact (levelSmashMappingSpaceAdjunction X).homEquiv_naturality_left_symm _ _

/-- Restricting the `n`-simplex corresponding to `g : X ∧ Δ[n]₊ ⟶ Y` along `α : m ⟶ n`
gives the `m`-simplex corresponding to `(X ∧ (Δ[α])₊) ≫ g`. -/
@[simp↓]
lemma map_mappingSpaceSimplexEquiv_symm (X Y : SymmetricSpectrum) {m n : SimplexCategory}
    (α : m ⟶ n)
    (g : (levelSmash X).obj (PointedSSet.addBasepoint.obj (SSet.stdSimplex.obj n)) ⟶ Y) :
    ((mappingSpace X).obj Y).right.map α.op ((mappingSpaceSimplexEquiv X Y n).symm g) =
      (mappingSpaceSimplexEquiv X Y m).symm
        ((levelSmash X).map (PointedSSet.addBasepoint.map (SSet.stdSimplex.map α)) ≫ g) := by
  apply (mappingSpaceSimplexEquiv X Y m).injective
  rw [mappingSpaceSimplexEquiv_map, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end SymmetricSpectrum

end TauCeti
