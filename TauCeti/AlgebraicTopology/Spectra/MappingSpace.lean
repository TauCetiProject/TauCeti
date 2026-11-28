/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.AddBasepoint
public import TauCeti.AlgebraicTopology.Spectra.Free
public import TauCeti.AlgebraicTopology.Spectra.StructureMap
public import TauCeti.CategoryTheory.Limits.Shapes.Products
public import TauCeti.CategoryTheory.Monoidal.Mod.Free.Closed

import TauCeti.CategoryTheory.Adjunction.Unique
import TauCeti.CategoryTheory.Monoidal.Closed.InternalCurrying

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
Pairing this with uniqueness of right adjoints yields the free smash comparisons
`(F_n K) ∧ L ≅ F_n (K ∧ L)` and `F_n S⁰ ∧ L ≅ F_n L` and the free mapping-space identifications
`Map(F_n K, E) ≅ Map_*(K, E_n)` and `Map(F_n S⁰, E) ≅ E_n`.

## Main definitions

* `SymmetricSequence.tensorFreeZeroι X K n`: the isomorphism `X_n ∧ K ⟶ (X ⊗ G₀ K)_n`, natural in
  `X` and `K` and `Σ_n`-equivariant.
* `SymmetricSequence.freeTensorFreeZeroIso n K`: the isomorphism `G_n K ⊗ G₀ L ≅ G_n (K ∧ L)`,
  natural in `L`.
* `SymmetricSpectrum.levelSmash X`: the functor `K ↦ X ∧ K`.
* `SymmetricSpectrum.mappingSpace X`: the functor `Y ↦ Map(X, Y)`.
* `SymmetricSpectrum.levelSmashMappingSpaceAdjunction X`: the adjunction `X ∧ - ⊣ Map(X, -)`.
* `SymmetricSpectrum.levelSmashUnitIso X`: the unit isomorphism `X ∧ S⁰ ≅ X`.
* `SymmetricSpectrum.mappingSpaceSimplexEquiv`: the `m`-simplices of `Map(X, Y)` are the maps
  `X ∧ Δ[m]₊ ⟶ Y`.
* `SymmetricSpectrum.unitHomMappingSpaceEquiv`: the vertices of `Map(X, Y)`, the based maps
  `S⁰ ⟶ Map(X, Y)`, are the maps `X ⟶ Y`.
* `SymmetricSpectrum.levelSmashFreeIso n K`: the natural isomorphism `(F_n K) ∧ L ≅ F_n (K ∧ L)`.
* `SymmetricSpectrum.levelSmashFreeZeroIso n`: the natural isomorphism `F_n S⁰ ∧ L ≅ F_n L`.
* `SymmetricSpectrum.mappingSpaceFreeIso n K`: the natural isomorphism
  `Map(F_n K, E) ≅ Map_*(K, E_n)`.
* `SymmetricSpectrum.mappingSpaceFreeZeroIso n`: the natural isomorphism `Map(F_n S⁰, E) ≅ E_n`.

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

/-- The canonical comparison map `G_n (K ∧ L) ⟶ G_n K ⊗ G₀ L`, adjoint to the generator
inclusion `K ∧ L ⟶ (G_n K)_n ∧ L ≅ (G_n K ⊗ G₀ L)_n`. -/
private noncomputable def freeTensorFreeZeroHom (n : ℕ) (K L : PointedSSet.{0}) :
    (free n).obj (K ⊗ L) ⟶ (free n).obj K ⊗ (free 0).obj L :=
  ((freeEvaluationAdjunction n).homEquiv _ _).symm
    (freeι n K ▷ L ≫ tensorFreeZeroι ((free n).obj K) L n)

@[reassoc]
private lemma freeι_comp_freeTensorFreeZeroHom (n : ℕ) (K L : PointedSSet.{0}) :
    freeι n (K ⊗ L) ≫ (freeTensorFreeZeroHom n K L).natTrans.app (FiniteBijection.mk n) =
      freeι n K ▷ L ≫ tensorFreeZeroι ((free n).obj K) L n :=
  freeι_comp_homEquiv_symm n _

/-- Level `m` of `G_n (K ∧ L)` is isomorphic to `(G_n K)_m ∧ L`, since `tensorRight L`
preserves the defining coproduct. -/
private noncomputable def freeTensorLevelIso (n m : ℕ) (K L : PointedSSet.{0}) :
    ((free n).obj (K ⊗ L)).functor.obj (FiniteBijection.mk m) ≅
      ((free n).obj K).functor.obj (FiniteBijection.mk m) ⊗ L :=
  freeLevelIso n m (K ⊗ L) ≪≫
    (Limits.PreservesCoproduct.iso (tensorRight L)
      (fun _ : FiniteBijection.mk n ⟶ FiniteBijection.mk m ↦ K)).symm ≪≫
    (tensorRight L).mapIso (freeLevelIso n m K).symm

private lemma freeι_comp_map_comp_freeTensorLevelIso_hom (n m : ℕ) (K L : PointedSSet.{0})
    (σ : FiniteBijection.mk n ⟶ FiniteBijection.mk m) :
    freeι n (K ⊗ L) ≫ ((free n).obj (K ⊗ L)).functor.map σ ≫
        (freeTensorLevelIso n m K L).hom =
      (freeι n K ≫ ((free n).obj K).functor.map σ) ▷ L := by
  simp only [freeTensorLevelIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    PreservesCoproduct.iso_inv]
  slice_lhs 1 3 => rw [freeι_comp_map_comp_freeLevelIso_hom]
  have hσ := Limits.ι_comp_sigmaComparison (tensorRight L)
    (fun _ : FiniteBijection.mk n ⟶ FiniteBijection.mk m ↦ K) σ
  dsimp only [Functor.flip_obj_obj, curriedTensor_obj_obj,
    Functor.flip_obj_map, curriedTensor_map_app] at hσ ⊢
  rw [hσ, ← comp_whiskerRight, ι_comp_freeLevelIso_inv]

private lemma isIso_freeTensorFreeZeroHom_app (n m : ℕ) (K L : PointedSSet.{0}) :
    IsIso ((freeTensorFreeZeroHom n K L).natTrans.app (FiniteBijection.mk m)) := by
  have heq : (freeTensorFreeZeroHom n K L).natTrans.app (FiniteBijection.mk m) =
      (freeTensorLevelIso n m K L).hom ≫ tensorFreeZeroι ((free n).obj K) L m := by
    refine free_level_hom_ext fun σ ↦ ?_
    have hnat := map_whiskerRight_comp_tensorFreeZeroι ((free n).obj K) L σ
    have hstep := freeι_comp_map_comp_freeTensorLevelIso_hom n m K L σ
    rw [(freeTensorFreeZeroHom n K L).natTrans.naturality σ,
      freeι_comp_freeTensorFreeZeroHom_assoc]
    dsimp only [free, Functor.comp_obj] at hnat hstep ⊢
    rw [← hnat, ← comp_whiskerRight_assoc, ← hstep, Category.assoc, Category.assoc]
  rw [heq]
  infer_instance

private lemma isIso_freeTensorFreeZeroHom (n : ℕ) (K L : PointedSSet.{0}) :
    IsIso (freeTensorFreeZeroHom n K L) := by
  have : ∀ c : FiniteBijection,
      IsIso (((DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor.map
        (freeTensorFreeZeroHom n K L)).app c) := by
    rintro ⟨m⟩
    rw [DayFunctor.equiv_functor_map]
    exact isIso_freeTensorFreeZeroHom_app n m K L
  have : IsIso ((DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor.map
      (freeTensorFreeZeroHom n K L)) :=
    NatIso.isIso_of_isIso_app
      ((DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor.map
        (freeTensorFreeZeroHom n K L))
  exact isIso_of_reflects_iso _ (DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor

private lemma free_hom_ext_of_homEquiv {n : ℕ} {K : PointedSSet.{0}} {Y : SymmetricSequence}
    {f g : (free n).obj K ⟶ Y}
    (h : freeι n K ≫ f.natTrans.app (FiniteBijection.mk n) =
      freeι n K ≫ g.natTrans.app (FiniteBijection.mk n)) :
    f = g := by
  apply ((freeEvaluationAdjunction n).homEquiv K Y).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, freeEvaluationAdjunction_unit_app]
  exact h

private lemma freeTensorFreeZeroHom_naturality (n : ℕ) (K : PointedSSet.{0})
    {L L' : PointedSSet.{0}} (f : L ⟶ L') :
    (free n).map (K ◁ f) ≫ freeTensorFreeZeroHom n K L' =
      freeTensorFreeZeroHom n K L ≫ (free n).obj K ◁ (free 0).map f := by
  refine free_hom_ext_of_homEquiv ?_
  rw [DayFunctor.comp_natTrans, NatTrans.comp_app, DayFunctor.comp_natTrans,
    NatTrans.comp_app, ← Category.assoc, ← freeι_naturality, Category.assoc,
    freeι_comp_freeTensorFreeZeroHom, ← Category.assoc (freeι n (K ⊗ L)),
    freeι_comp_freeTensorFreeZeroHom, Category.assoc, whisker_exchange_assoc]
  exact congrArg (_ ≫ ·) (tensorFreeZeroι_naturality_right ((free n).obj K) f n)

private noncomputable def freeTensorFreeZeroNatTrans (n : ℕ) (K : PointedSSet.{0}) :
    tensorLeft K ⋙ free n ⟶ free 0 ⋙ tensorLeft ((free n).obj K) where
  app L := freeTensorFreeZeroHom n K L
  naturality {_ _} f := freeTensorFreeZeroHom_naturality n K f

private instance isIso_freeTensorFreeZeroNatTrans (n : ℕ) (K : PointedSSet.{0}) :
    IsIso (freeTensorFreeZeroNatTrans n K) := by
  have : ∀ L, IsIso ((freeTensorFreeZeroNatTrans n K).app L) :=
    fun L ↦ isIso_freeTensorFreeZeroHom n K L
  exact NatIso.isIso_of_isIso_app _

/-- Smashing a free symmetric sequence `G_n K` on the right with `G₀ L` is naturally isomorphic
in `L` to `G_n (K ∧ L)`. -/
noncomputable def freeTensorFreeZeroIso (n : ℕ) (K : PointedSSet.{0}) :
    free 0 ⋙ tensorLeft ((free n).obj K) ≅ tensorLeft K ⋙ free n :=
  (asIso (freeTensorFreeZeroNatTrans n K)).symm

/-- On the generating level `n`, `(freeTensorFreeZeroIso n K).inv.app L` sends the generator
`K ∧ L` to `(freeι n K ▷ L) ≫ tensorFreeZeroι ((free n).obj K) L n`. -/
@[reassoc (attr := simp)]
lemma freeι_comp_freeTensorFreeZeroIso_inv_app (n : ℕ) (K L : PointedSSet.{0}) :
    freeι n (K ⊗ L) ≫ ((freeTensorFreeZeroIso n K).inv.app L).natTrans.app (FiniteBijection.mk n) =
      freeι n K ▷ L ≫ tensorFreeZeroι ((free n).obj K) L n :=
  freeι_comp_freeTensorFreeZeroHom n K L

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
-- An abbreviation, so that maps into `Map(X, Y)` are maps into the level of `Hom_S(X, Y)`. It is
-- the composite that `levelSmashMappingSpaceAdjunction` produces: written out with its own `obj`
-- and `map`, the kernel needs far too long to match the two outside the module system, as it must
-- for the equation lemma `levelSmashMappingSpaceAdjunction.eq_1` (which doc-gen4 asks for).
noncomputable abbrev mappingSpace (X : SymmetricSpectrum) :
    SymmetricSpectrum ⥤ PointedSSet.{0} :=
  Mod.ihom X ⋙ (DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor ⋙
    (CategoryTheory.evaluation FiniteBijection PointedSSet.{0}).obj (FiniteBijection.mk 0)

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

/-- A spectrum map `X ⟶ Y` gives the vertex of `Map(X, Y)` adjoint to `X ∧ S⁰ ≅ X ⟶ Y`. -/
lemma unitHomMappingSpaceEquiv_symm_apply (X Y : SymmetricSpectrum) (f : X ⟶ Y) :
    (unitHomMappingSpaceEquiv X Y).symm f =
      (levelSmashMappingSpaceAdjunction X).homEquiv _ _ ((levelSmashUnitIso X).hom ≫ f) := by
  simp [unitHomMappingSpaceEquiv]

/-! ### Structure maps of levelwise smash -/

/-- Unfold `(α_ _ _ _).hom ≫ sphere_p ◁ tensorFreeZeroι ≫ (X ∧ L).dayStructureMap p q` into
`freeι 0 L` followed by the Day-convolution/associator composite. -/
private lemma whiskerLeft_tensorFreeZeroι_comp_levelSmash_dayStructureMap
    (X : SymmetricSpectrum) (L : PointedSSet.{0}) (n : ℕ) :
    (α_ (SymmetricSequence.sphere.functor.obj (FiniteBijection.mk 1))
          (X.X.functor.obj (FiniteBijection.mk n)) L).hom ≫
        SymmetricSequence.sphere.functor.obj (FiniteBijection.mk 1) ◁
          SymmetricSequence.tensorFreeZeroι X.X L n ≫
        ((levelSmash X).obj L).dayStructureMap (FiniteBijection.mk 1) (FiniteBijection.mk n) =
      (SymmetricSequence.sphere.functor.obj (FiniteBijection.mk 1) ⊗
          X.X.functor.obj (FiniteBijection.mk n)) ◁ SymmetricSequence.freeι 0 L ≫
        ((α_ (SymmetricSequence.sphere.functor.obj (FiniteBijection.mk 1))
            (X.X.functor.obj (FiniteBijection.mk n))
            (((SymmetricSequence.free 0).obj L).functor.obj (FiniteBijection.mk 0))).hom ≫
          SymmetricSequence.sphere.functor.obj (FiniteBijection.mk 1) ◁
            (DayFunctor.η X.X ((SymmetricSequence.free 0).obj L)).app
              (FiniteBijection.mk n, FiniteBijection.mk 0) ≫
          SymmetricSequence.sphere.functor.obj (FiniteBijection.mk 1) ◁
            (X.X ⊗ (SymmetricSequence.free 0).obj L).functor.map
              (ρ_ (FiniteBijection.mk n)).hom ≫
          (DayFunctor.η SymmetricSequence.sphere
              (X.X ⊗ (SymmetricSequence.free 0).obj L)).app
            (FiniteBijection.mk 1, FiniteBijection.mk n) ≫
          (α_ SymmetricSequence.sphere X.X
              ((SymmetricSequence.free 0).obj L)).inv.natTrans.app
            (FiniteBijection.mk 1 ⊗ FiniteBijection.mk n) ≫
          (ModObj.smul (M := SymmetricSequence.sphere) (X := X.X) ▷
            (SymmetricSequence.free 0).obj L).natTrans.app
            (FiniteBijection.mk 1 ⊗ FiniteBijection.mk n)) := by
  simp only [SymmetricSequence.tensorFreeZeroι_def, Mod.dayStructureMap_def,
    Mod.tensorLeft_smul, DayFunctor.comp_natTrans, NatTrans.comp_app,
    whiskerLeft_comp, Category.assoc]
  rw [← associator_naturality_right_assoc]

/-- Passing across `tensorFreeZeroι` intertwines the Day structure map of `X` with that of
`X ∧ L`. -/
private lemma tensorFreeZeroι_comp_levelSmash_dayStructureMap_aux
    (X : SymmetricSpectrum) (L : PointedSSet.{0}) (p q : FiniteBijection) :
    (α_ (SymmetricSequence.sphere.functor.obj p) (X.X.functor.obj q)
        (((SymmetricSequence.free 0).obj L).functor.obj (FiniteBijection.mk 0))).hom ≫
        SymmetricSequence.sphere.functor.obj p ◁
          (DayFunctor.η X.X ((SymmetricSequence.free 0).obj L)).app (q, FiniteBijection.mk 0) ≫
        SymmetricSequence.sphere.functor.obj p ◁
          (X.X ⊗ (SymmetricSequence.free 0).obj L).functor.map (ρ_ q).hom ≫
        (DayFunctor.η SymmetricSequence.sphere (X.X ⊗ (SymmetricSequence.free 0).obj L)).app
          (p, q) ≫
        (α_ SymmetricSequence.sphere X.X ((SymmetricSequence.free 0).obj L)).inv.natTrans.app
          (p ⊗ q) ≫
        (ModObj.smul (M := SymmetricSequence.sphere) (X := X.X) ▷
          (SymmetricSequence.free 0).obj L).natTrans.app (p ⊗ q) =
      (DayFunctor.η SymmetricSequence.sphere X.X).app (p, q) ▷
          ((SymmetricSequence.free 0).obj L).functor.obj (FiniteBijection.mk 0) ≫
        (ModObj.smul (M := SymmetricSequence.sphere) (X := X.X)).natTrans.app (p ⊗ q) ▷
          ((SymmetricSequence.free 0).obj L).functor.obj (FiniteBijection.mk 0) ≫
        (DayFunctor.η X.X ((SymmetricSequence.free 0).obj L)).app (p ⊗ q, FiniteBijection.mk 0) ≫
        (X.X ⊗ (SymmetricSequence.free 0).obj L).functor.map (ρ_ (p ⊗ q)).hom := by
  have hη : SymmetricSequence.sphere.functor.obj p ◁
        (X.X ⊗ (SymmetricSequence.free 0).obj L).functor.map (ρ_ q).hom ≫
      (DayFunctor.η SymmetricSequence.sphere (X.X ⊗ (SymmetricSequence.free 0).obj L)).app (p, q) =
      (DayFunctor.η SymmetricSequence.sphere (X.X ⊗ (SymmetricSequence.free 0).obj L)).app
          (p, q ⊗ FiniteBijection.mk 0) ≫
        (SymmetricSequence.sphere ⊗ (X.X ⊗ (SymmetricSequence.free 0).obj L)).functor.map
          (p ◁ (ρ_ q).hom) := by
    simpa using (DayFunctor.η SymmetricSequence.sphere
      (X.X ⊗ (SymmetricSequence.free 0).obj L)).naturality
      ((𝟙 p, (ρ_ q).hom) : (p, q ⊗ FiniteBijection.mk 0) ⟶ (p, q))
  have hγNat : ((SymmetricSequence.sphere ⊗ X.X) ⊗ (SymmetricSequence.free 0).obj L).functor.map
        (ρ_ (p ⊗ q)).hom ≫
      (ModObj.smul (M := SymmetricSequence.sphere) (X := X.X) ▷
        (SymmetricSequence.free 0).obj L).natTrans.app (p ⊗ q) =
      (ModObj.smul (M := SymmetricSequence.sphere) (X := X.X) ▷
          (SymmetricSequence.free 0).obj L).natTrans.app ((p ⊗ q) ⊗ FiniteBijection.mk 0) ≫
        (X.X ⊗ (SymmetricSequence.free 0).obj L).functor.map (ρ_ (p ⊗ q)).hom :=
    (ModObj.smul (M := SymmetricSequence.sphere) (X := X.X) ▷
      (SymmetricSequence.free 0).obj L).natTrans.naturality (ρ_ (p ⊗ q)).hom
  have hday := DayFunctor.whiskerLeft_η_app_comp_η_app_comp_associator_inv_natTrans_app_assoc
    SymmetricSequence.sphere X.X ((SymmetricSequence.free 0).obj L) p q (FiniteBijection.mk 0)
    (((SymmetricSequence.sphere ⊗ X.X) ⊗ (SymmetricSequence.free 0).obj L).functor.map
        (p ◁ (ρ_ q).hom) ≫
      (ModObj.smul (M := SymmetricSequence.sphere) (X := X.X) ▷
        (SymmetricSequence.free 0).obj L).natTrans.app (p ⊗ q))
  -- 1. Slide `(ρ_ q).hom` past the outer Day unit `η` and the associator `α⁻¹` by naturality.
  slice_lhs 3 4 => rw [hη]
  slice_lhs 4 5 =>
    rw [(α_ SymmetricSequence.sphere X.X ((SymmetricSequence.free 0).obj L)).inv.natTrans.naturality
      ((p ◁ (ρ_ q).hom : p ⊗ q ⊗ FiniteBijection.mk 0 ⟶ p ⊗ q))]
  -- 2. Regroup the two Day units `η` and associator into the left-associated Day unit composite.
  rw [Category.assoc
    ((α_ SymmetricSequence.sphere X.X ((SymmetricSequence.free 0).obj L)).inv.natTrans.app _)]
  rw [hday, Iso.hom_inv_id_assoc]
  congr 1
  -- 3. Apply monoidal unitor coherence `(α_ p q 𝟙_).hom ≫ p ◁ (ρ_ q).hom = (ρ_ (p ⊗ q)).hom`, then
  --    slide `(ρ_ (p ⊗ q)).hom` past `smul ▷ G₀ L` and `η` to the end.
  slice_lhs 2 3 =>
    rw [← Functor.map_comp,
      show (α_ p q (FiniteBijection.mk 0)).hom ≫ p ◁ (ρ_ q).hom = (ρ_ (p ⊗ q)).hom by
        -- Expose `FiniteBijection.mk 0` as `𝟙_ FiniteBijection` so `monoidal` applies.
        change (α_ p q (𝟙_ FiniteBijection)).hom ≫ p ◁ (ρ_ q).hom = (ρ_ (p ⊗ q)).hom
        monoidal]
  slice_lhs 2 3 => rw [hγNat]
  rw [DayFunctor.η_app_comp_whiskerRight_natTrans_app_assoc]

/-- Passing across `tensorFreeZeroι` intertwines the structure map of `X` with the structure map
of `X ∧ L`. -/
@[reassoc]
lemma tensorFreeZeroι_comp_levelSmash_smashPowStructureMap
    (X : SymmetricSpectrum) (L : PointedSSet.{0}) (n : ℕ) :
    X.smashPowStructureMap n ▷ L ≫
        SymmetricSequence.tensorFreeZeroι X.X L (1 + n) =
      (α_ PointedSSet.circle (X.X.functor.obj (FiniteBijection.mk n)) L).hom ≫
        PointedSSet.circle ◁ SymmetricSequence.tensorFreeZeroι X.X L n ≫
        ((levelSmash X).obj L).smashPowStructureMap n := by
  have hday : (α_ (SymmetricSequence.sphere.functor.obj (FiniteBijection.mk 1))
          (X.X.functor.obj (FiniteBijection.mk n)) L).hom ≫
        SymmetricSequence.sphere.functor.obj (FiniteBijection.mk 1) ◁
          SymmetricSequence.tensorFreeZeroι X.X L n ≫
        ((levelSmash X).obj L).dayStructureMap (FiniteBijection.mk 1) (FiniteBijection.mk n) =
      X.dayStructureMap (FiniteBijection.mk 1) (FiniteBijection.mk n) ▷ L ≫
        SymmetricSequence.tensorFreeZeroι X.X L (1 + n) := by
    rw [whiskerLeft_tensorFreeZeroι_comp_levelSmash_dayStructureMap,
      tensorFreeZeroι_comp_levelSmash_dayStructureMap_aux,
      ← comp_whiskerRight_assoc, ← Mod.dayStructureMap_def, whisker_exchange_assoc,
      ← SymmetricSequence.tensorFreeZeroι_def]
    -- `(FiniteBijection.mk 1 ⊗ FiniteBijection.mk n).len` is definitionally `1 + n`.
    rfl
  rw [Mod.smashPowStructureMap_def, Mod.smashPowStructureMap_def, comp_whiskerRight,
    Category.assoc, hday.symm, associator_naturality_left_assoc, whisker_exchange_assoc]

/-! ### Free smash comparisons and mapping spaces out of free spectra -/

/-- Smashing a free symmetric spectrum `F_n K` on the right with `L` is naturally isomorphic in
`L` to `F_n (K ∧ L)`. -/
noncomputable def levelSmashFreeIso (n : ℕ) (K : PointedSSet.{0}) :
    levelSmash ((free n).obj K) ≅ MonoidalCategory.tensorLeft K ⋙ free n :=
  Functor.isoWhiskerLeft (SymmetricSequence.free 0)
      (Mod.tensorLeftFreeIso (A := SymmetricSequence.sphere) ((SymmetricSequence.free n).obj K)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight (SymmetricSequence.freeTensorFreeZeroIso n K)
      (freeMod SymmetricSequence.sphere) ≪≫
    Functor.associator _ _ _

private lemma evaluation_map_eq (n : ℕ) {X Y : SymmetricSpectrum} (f : X ⟶ Y) :
    (evaluation n).map f = f.hom.natTrans.app (FiniteBijection.mk n) := rfl

/-- On the generating level `n`, `(levelSmashFreeIso n K).inv.app L` sends the generator
`K ∧ L` into `(F_n K)_n ∧ L ≅ (F_n K ∧ L)_n`. -/
@[reassoc (attr := simp)]
lemma freeι_comp_evaluation_map_levelSmashFreeIso_inv_app (n : ℕ) (K L : PointedSSet.{0}) :
    freeι n (K ⊗ L) ≫ (evaluation n).map ((levelSmashFreeIso n K).inv.app L) =
      freeι n K ▷ L ≫ SymmetricSequence.tensorFreeZeroι ((free n).obj K).X L n := by
  have hcomp : ((levelSmashFreeIso n K).inv.app L).hom =
      ((freeMod SymmetricSequence.sphere).map
        ((SymmetricSequence.freeTensorFreeZeroIso n K).inv.app L)).hom ≫
      ((Mod.tensorLeftFreeIso (A := SymmetricSequence.sphere)
        ((SymmetricSequence.free n).obj K)).inv.app ((SymmetricSequence.free 0).obj L)).hom := by
    simp [levelSmashFreeIso]
  rw [evaluation_map_eq, hcomp, freeι_eq, DayFunctor.comp_natTrans, NatTrans.comp_app,
    Category.assoc, Mod.tensorLeftFreeIso_inv_app_hom]
  have hmod : (freeModι SymmetricSequence.sphere ((SymmetricSequence.free n).obj (K ⊗ L))) ≫
      ((freeMod SymmetricSequence.sphere).map
        ((SymmetricSequence.freeTensorFreeZeroIso n K).inv.app L)).hom ≫
      (α_ SymmetricSequence.sphere ((SymmetricSequence.free n).obj K)
        ((SymmetricSequence.free 0).obj L)).inv =
      ((SymmetricSequence.freeTensorFreeZeroIso n K).inv.app L) ≫
        (freeModι SymmetricSequence.sphere ((SymmetricSequence.free n).obj K) ▷
          (SymmetricSequence.free 0).obj L) := by
    rw [← freeModι_naturality_assoc]
    dsimp only [Functor.comp_obj, MonoidalCategory.curriedTensor_obj_obj]
    rw [freeModι_tensor]
  have hmodApp := congrArg (fun g : (SymmetricSequence.free n).obj (K ⊗ L) ⟶ _ ↦
    g.natTrans.app (FiniteBijection.mk n)) hmod
  simp only [DayFunctor.comp_natTrans, NatTrans.comp_app] at hmodApp
  rw [hmodApp, ← Category.assoc, SymmetricSequence.freeι_comp_freeTensorFreeZeroIso_inv_app,
    Category.assoc, ← SymmetricSequence.tensorFreeZeroι_naturality_left, ← comp_whiskerRight_assoc,
    ← freeι_eq]
  -- `((free n).obj K).X` is `SymmetricSequence.sphere ⊗ (SymmetricSequence.free n).obj K`.
  rfl

/-- Smashing `F_n S⁰` with `L` is naturally isomorphic in `L` to `F_n L`. -/
noncomputable def levelSmashFreeZeroIso (n : ℕ) :
    levelSmash ((free n).obj (𝟙_ _)) ≅ free n :=
  levelSmashFreeIso n (𝟙_ _) ≪≫
    Functor.isoWhiskerRight (leftUnitorNatIso PointedSSet.{0}) (free n) ≪≫
    Functor.leftUnitor (free n)

/-- On the generating level `n`, `(levelSmashFreeZeroIso n).inv.app L` sends the generator
`L` through `(λ_ L).inv` into `(F_n S⁰)_n ∧ L ≅ (F_n S⁰ ∧ L)_n`. -/
@[reassoc (attr := simp)]
lemma freeι_comp_evaluation_map_levelSmashFreeZeroIso_inv_app (n : ℕ) (L : PointedSSet.{0}) :
    freeι n L ≫ (evaluation n).map ((levelSmashFreeZeroIso n).inv.app L) =
      (λ_ L).inv ≫ freeι n (𝟙_ _) ▷ L ≫
        SymmetricSequence.tensorFreeZeroι ((free n).obj (𝟙_ _)).X L n := by
  have hinv : (levelSmashFreeZeroIso n).inv.app L =
      (free n).map (λ_ L).inv ≫ (levelSmashFreeIso n (𝟙_ _)).inv.app L := by
    simp [levelSmashFreeZeroIso]
  rw [hinv, Functor.map_comp, ← Category.assoc, ← freeι_naturality, Category.assoc,
    freeι_comp_evaluation_map_levelSmashFreeIso_inv_app]

/-- Mapping out of the free symmetric spectrum `F_n K` into `E` is naturally isomorphic to the
pointed mapping space `Map_*(K, E_n)`. -/
noncomputable def mappingSpaceFreeIso (n : ℕ) (K : PointedSSet.{0}) :
    mappingSpace ((free n).obj K) ≅ evaluation n ⋙ CategoryTheory.ihom K :=
  (levelSmashMappingSpaceAdjunction ((free n).obj K)).rightAdjointUniq
    (((CategoryTheory.ihom.adjunction K).comp (freeEvaluationAdjunction n)).ofNatIsoLeft
      (levelSmashFreeIso n K).symm)

/-- Under `mappingSpaceFreeIso n K`, the adjunction bijection `F_n K ∧ L ⟶ E` corresponds to the
curried restriction of `K ∧ L ⟶ E_n` along the generator and `tensorFreeZeroι`. -/
@[reassoc]
lemma homEquiv_comp_mappingSpaceFreeIso_hom_app (n : ℕ) (K L : PointedSSet.{0})
    (E : SymmetricSpectrum) (f : (levelSmash ((free n).obj K)).obj L ⟶ E) :
    (levelSmashMappingSpaceAdjunction ((free n).obj K)).homEquiv L E f ≫
        (mappingSpaceFreeIso n K).hom.app E =
      MonoidalClosed.curry (freeι n K ▷ L ≫
        SymmetricSequence.tensorFreeZeroι ((free n).obj K).X L n ≫ (evaluation n).map f) := by
  let adj2 := ((CategoryTheory.ihom.adjunction K).comp (freeEvaluationAdjunction n)).ofNatIsoLeft
    (levelSmashFreeIso n K).symm
  rw [mappingSpaceFreeIso, Adjunction.homEquiv_comp_rightAdjointUniq_hom_app _ adj2]
  dsimp only [adj2]
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply, Iso.symm_hom]
  dsimp only [MonoidalCategory.curriedTensor_obj_obj]
  rw [Adjunction.homEquiv_unit (freeEvaluationAdjunction n), freeEvaluationAdjunction_unit_app,
    Functor.map_comp, ← Category.assoc, freeι_comp_evaluation_map_levelSmashFreeIso_inv_app,
    MonoidalClosed.homEquiv_apply_eq, Category.assoc]

/-- Uncurrying `(mappingSpaceFreeIso n K).hom.app E` yields restriction of the counit evaluation
along the generator `freeι n K` and `tensorFreeZeroι`. -/
@[reassoc]
lemma uncurry_mappingSpaceFreeIso_hom_app (n : ℕ) (K : PointedSSet.{0}) (E : SymmetricSpectrum) :
    MonoidalClosed.uncurry ((mappingSpaceFreeIso n K).hom.app E) =
      freeι n K ▷ (mappingSpace ((free n).obj K)).obj E ≫
        SymmetricSequence.tensorFreeZeroι ((free n).obj K).X
          ((mappingSpace ((free n).obj K)).obj E) n ≫
        (evaluation n).map ((levelSmashMappingSpaceAdjunction ((free n).obj K)).counit.app E) := by
  rw [← Category.id_comp ((mappingSpaceFreeIso n K).hom.app E),
    ← Adjunction.right_triangle_components (levelSmashMappingSpaceAdjunction ((free n).obj K)),
    ← Adjunction.homEquiv_unit, homEquiv_comp_mappingSpaceFreeIso_hom_app,
    MonoidalClosed.uncurry_curry]

/-- Mapping out of `F_n S⁰` into `E` is naturally isomorphic to level `E_n`. -/
noncomputable def mappingSpaceFreeZeroIso (n : ℕ) :
    mappingSpace ((free n).obj (𝟙_ _)) ≅ evaluation n :=
  mappingSpaceFreeIso n (𝟙_ _) ≪≫
    Functor.isoWhiskerLeft (evaluation n) MonoidalClosed.unitNatIso.symm

/-- On components, `(mappingSpaceFreeZeroIso n).hom.app E` factors through
`mappingSpaceFreeIso n S⁰` and `MonoidalClosed.unitNatIso.inv`. -/
@[reassoc]
lemma mappingSpaceFreeZeroIso_hom_app (n : ℕ) (E : SymmetricSpectrum) :
    (mappingSpaceFreeZeroIso n).hom.app E =
      (mappingSpaceFreeIso n (𝟙_ _)).hom.app E ≫
        MonoidalClosed.unitNatIso.inv.app ((evaluation n).obj E) := by
  simp [mappingSpaceFreeZeroIso]

/-- Under `mappingSpaceFreeZeroIso n`, the adjunction bijection `F_n S⁰ ∧ L ⟶ E` corresponds to
restriction along the generator and `tensorFreeZeroι`, precomposed with `(λ_ L).inv`. -/
@[reassoc]
lemma homEquiv_comp_mappingSpaceFreeZeroIso_hom_app (n : ℕ) (L : PointedSSet.{0})
    (E : SymmetricSpectrum) (f : (levelSmash ((free n).obj (𝟙_ _))).obj L ⟶ E) :
    (levelSmashMappingSpaceAdjunction ((free n).obj (𝟙_ _))).homEquiv L E f ≫
        (mappingSpaceFreeZeroIso n).hom.app E =
      (λ_ L).inv ≫ freeι n (𝟙_ _) ▷ L ≫
        SymmetricSequence.tensorFreeZeroι ((free n).obj (𝟙_ _)).X L n ≫
        (evaluation n).map f := by
  rw [mappingSpaceFreeZeroIso_hom_app, ← Category.assoc,
    homEquiv_comp_mappingSpaceFreeIso_hom_app]
  simp only [MonoidalClosed.unitNatIso_inv_app, ← Category.assoc (MonoidalClosed.curry _),
    leftUnitor_inv_naturality, Category.assoc, ← MonoidalClosed.uncurry_eq,
    MonoidalClosed.uncurry_curry]

end SymmetricSpectrum

end TauCeti
