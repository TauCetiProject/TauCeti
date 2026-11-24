/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.RingTheory.Flat.CategoryTheory
public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.Algebra.Homology.CartanEilenbergResolution
public import TauCeti.Algebra.Homology.Monoidal.Homology.Connecting
public import TauCeti.Algebra.Homology.TotalComplex.Basic

/-!
# The Künneth bicomplex

Let `K` and `L` be chain complexes of modules over a commutative ring `R`, indexed by `ℕ`, and let
`Q` be the Cartan–Eilenberg resolution of `L` (`ChainComplex.cartanEilenbergResolution`).
Tensoring each complex `Q.X p` (the row `p` in `ChainComplex.cartanEilenbergResolution`) with `K`
gives the first-quadrant bicomplex `HomologicalComplex.kunnethBicomplex K L` whose column `p` is
`K ⊗ Q.X p`, and whose row `n` is `p ↦ (K ⊗ Q.X p).X n`. The augmentation
`Q.X 0 ⟶ L` induces an augmentation of its total complex to `K ⊗ L`
(`HomologicalComplex.kunnethBicomplexAugmentation`). A chain map `f : K ⟶ K'` induces a morphism
of Künneth bicomplexes `HomologicalComplex.kunnethBicomplexMapLeft f L`, `f ▷ Q.X p` on column
`p`, compatible with the augmentations
(`HomologicalComplex.total_map_kunnethBicomplexMapLeft_kunnethBicomplexAugmentation`). A chain map
`g : L₁ ⟶ L₂` induces a morphism of Künneth bicomplexes
`HomologicalComplex.kunnethBicomplexMapRight K g`, `K ◁ Q(g).f p` on column `p` for the lift
`Q(g) = ChainComplex.cartanEilenbergResolutionMap g` of `g` to the Cartan–Eilenberg resolutions,
which depends on choices; it is compatible with the augmentations
(`HomologicalComplex.total_map_kunnethBicomplexMapRight_kunnethBicomplexAugmentation`). More
generally, any morphism `ψ` of the Cartan–Eilenberg resolutions induces a morphism of Künneth
bicomplexes `HomologicalComplex.kunnethBicomplexMapRightOfLift K ψ`, functorially in `ψ`.

When every term of `K` is flat, this augmentation is a quasi-isomorphism
(`HomologicalComplex.quasiIso_kunnethBicomplexAugmentation`). Indeed, the row `n` of the bicomplex,
augmented by `(K ⊗ L).X n`, is spliced from the degree `n` parts of the sequences
`0 ⟶ K ⊗ kernels (p + 1) ⟶ K ⊗ Q.X p ⟶ K ⊗ kernels p ⟶ 0`, which are short exact because
tensoring with a flat module is exact
(`HomologicalComplex.shortExact_tensorLeftShortComplex_of_preservesFiniteLimits`). Exact augmented
rows make the augmentation of the total complex a quasi-isomorphism
(`HomologicalComplex₂.quasiIso_totalAugmentation_of_rows`).

This bicomplex is the source of the Künneth spectral sequence. When every term of `K` is flat, the
spectral sequence of its column filtration therefore converges to the homology of `K ⊗ L`. Since
the complexes `Q.X p` have projective terms and projective homology, the Künneth formula for the
columns `K ⊗ Q.X p` identifies the page after the first (E² in Weibel's numbering, `page 3` in the
numbering of `HomologicalComplex₂.columnFiltrationSpectralSequence`) with `Tor`; see
`TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.SpectralSequence`.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Section 5.7 and Theorem 5.6.4.
* H. Cartan, S. Eilenberg, *Homological Algebra*, Princeton University Press, 1956,
  Chapter XVII, §5.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory ChainComplex cartanEilenbergResolution

universe u

variable {R : Type u} [CommRing R] (K L : ChainComplex (ModuleCat.{u} R) ℕ)

namespace ChainComplex.cartanEilenbergResolution

/-- Tensoring with a complex of flat modules keeps the sequences
`0 ⟶ kernels (p + 1) ⟶ Q.X p ⟶ kernels p ⟶ 0` of the Cartan–Eilenberg resolution short exact. -/
lemma shortExact_whiskerLeft_row [∀ p, Module.Flat R (K.X p)] (p : ℕ) :
    (HomologicalComplex.tensorLeftShortComplex K
      (ShortComplex.mk _ _ (rowι_rowπ L p))).ShortExact :=
  HomologicalComplex.shortExact_tensorLeftShortComplex_of_preservesFiniteLimits K
    (shortExact_row L p)

end ChainComplex.cartanEilenbergResolution

namespace HomologicalComplex

-- The body is exposed so that the statements of `kunnethBicomplex_d` and of the lemmas below,
-- whose types mention `K ⊗ Q.X p` where the bicomplex has `(kunnethBicomplex K L).X p`, elaborate.
/-- **The Künneth bicomplex.** Its column `p` is `K ⊗ Q.X p`, where `Q` is the Cartan–Eilenberg
resolution of `L`, and its horizontal differentials are induced by those of `Q`: it is `Q` with
`tensorLeft K` applied to every complex `Q.X p`. -/
@[expose]
def kunnethBicomplex : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ) :=
  ((tensorLeft K).mapHomologicalComplex _).obj (cartanEilenbergResolution L)

/-- The column `p` of the Künneth bicomplex is `K ⊗ Q.X p`. -/
@[simp]
lemma kunnethBicomplex_X (p : ℕ) :
    (kunnethBicomplex K L).X p = K ⊗ (cartanEilenbergResolution L).X p := (rfl)

-- Not `@[simp]`: together with the simp lemma `ChainComplex.cartanEilenbergResolution.d_succ` it
-- would rewrite the left-hand side of the simp lemma `kunnethBicomplex_d_comp_ε`.
/-- The horizontal differential of the Künneth bicomplex is `K` whiskered with that of `Q`. -/
lemma kunnethBicomplex_d (p p' : ℕ) :
    (kunnethBicomplex K L).d p p' = K ◁ (cartanEilenbergResolution L).d p p' := (rfl)

/-- The augmentation of the column `0` of the Künneth bicomplex to `K ⊗ L`. -/
def kunnethBicomplexε : (kunnethBicomplex K L).X 0 ⟶ K ⊗ L :=
  K ◁ cartanEilenbergResolutionπ L

/-- The augmentation `kunnethBicomplexε K L` is `K` whiskered with the augmentation `Q.X 0 ⟶ L`. -/
lemma kunnethBicomplexε_def : kunnethBicomplexε K L = K ◁ cartanEilenbergResolutionπ L := (rfl)

@[reassoc (attr := simp)]
lemma kunnethBicomplex_d_comp_ε : (kunnethBicomplex K L).d 1 0 ≫ kunnethBicomplexε K L = 0 := by
  -- `(kunnethBicomplex K L).X 0` is `K ⊗ Q.X 0` only by definition, so the two whiskerings
  -- compose syntactically only after this `change`; rewriting with `kunnethBicomplex_d` and
  -- `kunnethBicomplexε_def` would leave a composite that `rw` cannot match
  change K ◁ _ ≫ K ◁ _ = 0
  rw [← MonoidalCategory.whiskerLeft_comp, cartanEilenbergResolution.d_comp_π, whiskerLeft_zero]

/-- The augmentation of the total complex of the Künneth bicomplex to `K ⊗ L`. -/
def kunnethBicomplexAugmentation :
    (kunnethBicomplex K L).total (ComplexShape.down ℕ) ⟶ K ⊗ L :=
  HomologicalComplex₂.totalAugmentation _ (kunnethBicomplexε K L)
    (kunnethBicomplex_d_comp_ε K L)

/-- The augmentation of the total complex is induced by `kunnethBicomplexε K L`. -/
lemma kunnethBicomplexAugmentation_def :
    kunnethBicomplexAugmentation K L = HomologicalComplex₂.totalAugmentation _
      (kunnethBicomplexε K L) (kunnethBicomplex_d_comp_ε K L) := (rfl)

section MapLeft

variable {K₁ K₂ K₃ : ChainComplex (ModuleCat.{u} R) ℕ} (f : K₁ ⟶ K₂) (f' : K₂ ⟶ K₃)
  (M : ChainComplex (ModuleCat.{u} R) ℕ)

/-- The morphism of Künneth bicomplexes induced by a chain map `f : K₁ ⟶ K₂`: on column `p` it is
`f ▷ Q.X p`, for the Cartan–Eilenberg resolution `Q` of `M`. It is the natural transformation
`tensorLeft K₁ ⟶ tensorLeft K₂` induced by `f`, applied to the complexes of `Q`. -/
def kunnethBicomplexMapLeft : kunnethBicomplex K₁ M ⟶ kunnethBicomplex K₂ M :=
  (NatTrans.mapHomologicalComplex ((curriedTensor _).map f) _).app
    (ChainComplex.cartanEilenbergResolution M)

/-- The morphism `HomologicalComplex.kunnethBicomplexMapLeft f M` is `f ▷ Q.X p` on column `p`. -/
@[simp]
lemma kunnethBicomplexMapLeft_f (p : ℕ) :
    (kunnethBicomplexMapLeft f M).f p = f ▷ (ChainComplex.cartanEilenbergResolution M).X p :=
  (rfl)

@[simp]
lemma kunnethBicomplexMapLeft_id : kunnethBicomplexMapLeft (𝟙 K₁) M = 𝟙 _ := by
  rw [kunnethBicomplexMapLeft, CategoryTheory.Functor.map_id, NatTrans.mapHomologicalComplex_id,
    NatTrans.id_app]
  -- `(tensorLeft K₁).mapHomologicalComplex _` applied to `Q` is `kunnethBicomplex K₁ M` by
  -- definition
  rfl

@[simp]
lemma kunnethBicomplexMapLeft_comp :
    kunnethBicomplexMapLeft (f ≫ f') M =
      kunnethBicomplexMapLeft f M ≫ kunnethBicomplexMapLeft f' M := by
  rw [kunnethBicomplexMapLeft, CategoryTheory.Functor.map_comp,
    NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app]
  -- the composite is that of the morphisms of Künneth bicomplexes, which are morphisms out of
  -- `kunnethBicomplex K₁ M` only by definition
  rfl

/-- The morphism of Künneth bicomplexes induced by `f` is compatible with the augmentations of the
total complexes to `K₁ ⊗ M` and `K₂ ⊗ M`. -/
@[reassoc]
lemma total_map_kunnethBicomplexMapLeft_kunnethBicomplexAugmentation :
    HomologicalComplex₂.total.map (kunnethBicomplexMapLeft f M) (ComplexShape.down ℕ) ≫
        kunnethBicomplexAugmentation K₂ M =
      kunnethBicomplexAugmentation K₁ M ≫ f ▷ M := by
  have e : (kunnethBicomplexMapLeft f M).f 0 ≫ kunnethBicomplexε K₂ M =
      kunnethBicomplexε K₁ M ≫ f ▷ M := by
    rw [kunnethBicomplexε_def, kunnethBicomplexε_def, kunnethBicomplexMapLeft_f]
    -- the column `0` of the Künneth bicomplex is `K₁ ⊗ Q.X 0` only by definition
    change f ▷ _ ≫ K₂ ◁ _ = K₁ ◁ _ ≫ f ▷ _
    exact (whisker_exchange _ _).symm
  rw [kunnethBicomplexAugmentation_def, kunnethBicomplexAugmentation_def,
    HomologicalComplex₂.total_map_totalAugmentation, HomologicalComplex₂.totalAugmentation_comp]
  simp only [e]

end MapLeft

section MapRight

variable {L₁ L₂ : ChainComplex (ModuleCat.{u} R) ℕ} (g : L₁ ⟶ L₂)

/-- A morphism of Künneth bicomplexes over a chain map `g : L₁ ⟶ L₂`: on column `p` it is
`K ◁ Q(g).f p` for the lift `Q(g) = ChainComplex.cartanEilenbergResolutionMap g` of `g` to the
Cartan–Eilenberg resolutions. It depends on the choice of that lift. -/
def kunnethBicomplexMapRight : kunnethBicomplex K L₁ ⟶ kunnethBicomplex K L₂ :=
  ((tensorLeft K).mapHomologicalComplex _).map (ChainComplex.cartanEilenbergResolutionMap g)

/-- The morphism `HomologicalComplex.kunnethBicomplexMapRight K g` is `K ◁ Q(g).f p` on column
`p`. -/
@[simp]
lemma kunnethBicomplexMapRight_f (p : ℕ) :
    (kunnethBicomplexMapRight K g).f p = K ◁ (ChainComplex.cartanEilenbergResolutionMap g).f p :=
  (rfl)

/-- The morphism of Künneth bicomplexes over `g` is compatible with the augmentations of the total
complexes to `K ⊗ L₁` and `K ⊗ L₂`. -/
@[reassoc]
lemma total_map_kunnethBicomplexMapRight_kunnethBicomplexAugmentation :
    HomologicalComplex₂.total.map (kunnethBicomplexMapRight K g) (ComplexShape.down ℕ) ≫
        kunnethBicomplexAugmentation K L₂ =
      kunnethBicomplexAugmentation K L₁ ≫ K ◁ g := by
  have e : (kunnethBicomplexMapRight K g).f 0 ≫ kunnethBicomplexε K L₂ =
      kunnethBicomplexε K L₁ ≫ K ◁ g := by
    rw [kunnethBicomplexε_def, kunnethBicomplexε_def, kunnethBicomplexMapRight_f]
    -- the column `0` of the Künneth bicomplex is `K ⊗ Q.X 0` only by definition
    change K ◁ _ ≫ K ◁ _ = K ◁ _ ≫ K ◁ _
    rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp,
      ChainComplex.cartanEilenbergResolutionMap_π]
  rw [kunnethBicomplexAugmentation_def, kunnethBicomplexAugmentation_def,
    HomologicalComplex₂.total_map_totalAugmentation, HomologicalComplex₂.totalAugmentation_comp]
  simp only [e]

end MapRight

section MapRightOfLift

variable {L₁ L₂ L₃ : ChainComplex (ModuleCat.{u} R) ℕ}

/-- The morphism of Künneth bicomplexes induced by a morphism `ψ` of the Cartan–Eilenberg
resolutions of `L₁` and `L₂`: on column `p` it is `K ◁ ψ.f p`. For the lift
`ChainComplex.cartanEilenbergResolutionMap g` of a chain map `g`, it is
`HomologicalComplex.kunnethBicomplexMapRight K g`
(`HomologicalComplex.kunnethBicomplexMapRight_eq`). -/
def kunnethBicomplexMapRightOfLift
    (ψ : cartanEilenbergResolution L₁ ⟶ cartanEilenbergResolution L₂) :
    kunnethBicomplex K L₁ ⟶ kunnethBicomplex K L₂ :=
  ((tensorLeft K).mapHomologicalComplex _).map ψ

/-- The morphism `HomologicalComplex.kunnethBicomplexMapRightOfLift K ψ` is `K ◁ ψ.f p` on column
`p`. -/
@[simp]
lemma kunnethBicomplexMapRightOfLift_f
    (ψ : cartanEilenbergResolution L₁ ⟶ cartanEilenbergResolution L₂) (p : ℕ) :
    (kunnethBicomplexMapRightOfLift K ψ).f p = K ◁ ψ.f p :=
  (rfl)

/-- The identity of the Cartan–Eilenberg resolution induces the identity of the Künneth
bicomplex. -/
@[simp]
lemma kunnethBicomplexMapRightOfLift_id :
    kunnethBicomplexMapRightOfLift K (𝟙 (cartanEilenbergResolution L₁)) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

/-- `HomologicalComplex.kunnethBicomplexMapRightOfLift` is compatible with composition. -/
@[simp]
lemma kunnethBicomplexMapRightOfLift_comp
    (ψ : cartanEilenbergResolution L₁ ⟶ cartanEilenbergResolution L₂)
    (ψ' : cartanEilenbergResolution L₂ ⟶ cartanEilenbergResolution L₃) :
    kunnethBicomplexMapRightOfLift K (ψ ≫ ψ') =
      kunnethBicomplexMapRightOfLift K ψ ≫ kunnethBicomplexMapRightOfLift K ψ' :=
  CategoryTheory.Functor.map_comp _ _ _

/-- The morphism of Künneth bicomplexes over a chain map `g` is the one induced by the lift
`ChainComplex.cartanEilenbergResolutionMap g` of `g` to the Cartan–Eilenberg resolutions. -/
lemma kunnethBicomplexMapRight_eq (g : L₁ ⟶ L₂) :
    kunnethBicomplexMapRight K g =
      kunnethBicomplexMapRightOfLift K (ChainComplex.cartanEilenbergResolutionMap g) :=
  (rfl)

end MapRightOfLift

/-- In degree `n`, the map `K ⊗ Q.X 0 ⟶ K ⊗ L` vanishes on the image of the differential of the
row `n` of the Künneth bicomplex. -/
lemma kunnethBicomplex_row_d_comp_whiskerLeft_rowπ_f (n : ℕ) :
    (((HomologicalComplex.eval _ _ n).mapHomologicalComplex _).obj (kunnethBicomplex K L)).d 1 0 ≫
      (K ◁ rowπ L 0).f n = 0 := by
  have := congr_hom (kunnethBicomplex_d_comp_ε K L) n
  rw [comp_f, zero_f, kunnethBicomplexε_def, cartanEilenbergResolutionπ_eq] at this
  -- the row differential is by definition the degree `n` component of the bicomplex differential
  exact this

/-- In degree `n`, the augmentation of the Künneth bicomplex, followed by the identification of
the degree `n` part of the single complex on `K ⊗ L`, is the augmentation of the row `n`. -/
private lemma map_eval_toSingle₀Equiv_symm_kunnethBicomplexε (n : ℕ) :
    ((HomologicalComplex.eval _ _ n).mapHomologicalComplex _).map
        ((ChainComplex.toSingle₀Equiv (kunnethBicomplex K L) (K ⊗ L)).symm
          ⟨kunnethBicomplexε K L, kunnethBicomplex_d_comp_ε K L⟩) ≫
      (singleMapHomologicalComplex (HomologicalComplex.eval _ _ n) _ 0).hom.app (K ⊗ L) =
    (ChainComplex.toSingle₀Equiv _ ((K ⊗ kernels L 0).X n)).symm
      ⟨(K ◁ rowπ L 0).f n, kunnethBicomplex_row_d_comp_whiskerLeft_rowπ_f K L n⟩ := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [Functor.mapHomologicalComplex_obj_X, eval_obj, single₀_obj_zero,
    Functor.comp_obj, comp_f, Functor.mapHomologicalComplex_map_f,
    singleMapHomologicalComplex_hom_app_self, single₀ObjXSelf, Iso.refl_hom, eval_map, id_f,
    Iso.refl_inv, Category.comp_id, Functor.mapHomologicalComplex_obj_d]
  rw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero, kunnethBicomplexε_def,
    cartanEilenbergResolutionπ_eq]
  exact (ChainComplex.toSingle₀Equiv_symm_apply_f_zero
    (C := ((HomologicalComplex.eval _ _ n).mapHomologicalComplex _).obj (kunnethBicomplex K L))
    ((K ◁ rowπ L 0).f n) _).symm

variable [∀ p, Module.Flat R (K.X p)]

/-- The row `n` of the Künneth bicomplex is spliced from the degree `n` parts of the short exact
sequences `ChainComplex.cartanEilenbergResolution.shortExact_whiskerLeft_row`, so its augmentation
to `(K ⊗ L).X n` is a quasi-isomorphism. -/
lemma quasiIso_kunnethBicomplex_row (n : ℕ) :
    QuasiIso ((ChainComplex.toSingle₀Equiv
      (((HomologicalComplex.eval _ _ n).mapHomologicalComplex _).obj (kunnethBicomplex K L))
      ((K ⊗ kernels L 0).X n)).symm ⟨(K ◁ rowπ L 0).f n,
        kunnethBicomplex_row_d_comp_whiskerLeft_rowπ_f K L n⟩) := by
  let X := ((HomologicalComplex.eval _ _ n).mapHomologicalComplex _).obj (kunnethBicomplex K L)
  let S (p : ℕ) :=
    HomologicalComplex.tensorLeftShortComplex K (ShortComplex.mk _ _ (rowι_rowπ L p))
  let ι (p : ℕ) : (K ⊗ kernels L (p + 1)).X n ⟶ X.X p := (S p).f.f n
  let ε (p : ℕ) : X.X p ⟶ (K ⊗ kernels L p).X n := (S p).g.f n
  have w (p : ℕ) : ι p ≫ ε p = 0 := by
    have := congr_hom (S p).zero n
    rw [comp_f, zero_f] at this
    exact this
  -- the short complex `ι p, ε p` is by definition the degree `n` part of
  -- `shortExact_whiskerLeft_row K L p`
  have hS (p : ℕ) : (ShortComplex.mk _ _ (w p)).ShortExact :=
    (shortExact_iff_degreewise_shortExact _).1 (shortExact_whiskerLeft_row K L p) n
  have hd (p : ℕ) : X.d (p + 1) p = ε (p + 1) ≫ ι p := by
    dsimp only [X, ι, ε, S]
    rw [Functor.mapHomologicalComplex_obj_d, eval_map, kunnethBicomplex_d, d_succ,
      MonoidalCategory.whiskerLeft_comp, comp_f]
    -- the two sides differ only in how the middle object `X.X p` is written
    rfl
  exact ChainComplex.quasiIso_toSingle₀Equiv_symm_of_shortExact ι ε w hS hd

/-- **The Künneth bicomplex computes `K ⊗ L`.** If every term of `K` is flat, the augmentation
of the total complex of the Künneth bicomplex to `K ⊗ L` is a quasi-isomorphism. -/
theorem quasiIso_kunnethBicomplexAugmentation : QuasiIso (kunnethBicomplexAugmentation K L) := by
  let φ := (ChainComplex.toSingle₀Equiv (kunnethBicomplex K L) (K ⊗ L)).symm
    ⟨kunnethBicomplexε K L, kunnethBicomplex_d_comp_ε K L⟩
  have hφ (n : ℕ) : QuasiIso (((HomologicalComplex.eval _ _ n).mapHomologicalComplex _).map φ) := by
    rw [← quasiIso_iff_comp_right _
      ((singleMapHomologicalComplex (HomologicalComplex.eval _ _ n) _ 0).hom.app (K ⊗ L)),
      map_eval_toSingle₀Equiv_symm_kunnethBicomplexε]
    exact quasiIso_kunnethBicomplex_row K L n
  have := HomologicalComplex₂.quasiIso_totalAugmentation_of_rows φ hφ
  rw [kunnethBicomplexAugmentation_def]
  convert this using 2
  simp [φ]

end HomologicalComplex
