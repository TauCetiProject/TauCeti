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
(`HomologicalComplex.kunnethBicomplexAugmentation`).

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
columns `K ⊗ Q.X p` is expected to identify the page after the first (E² in Weibel's numbering,
`page 3` in the numbering of `HomologicalComplex₂.columnFiltrationSpectralSequence`) with `Tor`;
this file does not prove that identification.

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
