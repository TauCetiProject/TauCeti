/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Flat.CategoryTheory
public import TauCeti.Algebra.Homology.CartanEilenbergResolution
public import TauCeti.Algebra.Homology.Monoidal.Homology.Connecting
public import TauCeti.Algebra.Homology.TotalComplex.Basic

/-!
# The Künneth bicomplex

Let `K` and `L` be chain complexes of modules over a commutative ring `R`, indexed by `ℕ`, and let
`Q` be the Cartan–Eilenberg resolution of `L` (`ChainComplex.cartanEilenbergResolution`). Tensoring
each row of `Q` with `K` gives the first-quadrant bicomplex
`HomologicalComplex.kunnethBicomplex K L` whose column `p` is `K ⊗ Q.X p`. The augmentation
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

This bicomplex is the source of the Künneth spectral sequence: its columns satisfy the Künneth
formula, since the rows of a Cartan–Eilenberg resolution have projective terms and projective
homology, so the spectral sequence of its column filtration converges to the homology of `K ⊗ L`.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Section 5.7 and Theorem 5.6.4.
* H. Cartan, S. Eilenberg, *Homological Algebra*, Princeton University Press, 1956,
  Chapter XVII, §5.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory ChainComplex cartanEilenbergResolution

universe u

namespace HomologicalComplex

variable {R : Type u} [CommRing R] (K L : ChainComplex (ModuleCat.{u} R) ℕ)

/-- Whiskering a zero map of complexes of modules on the left gives zero. -/
private lemma whiskerLeft_zero {M N : ChainComplex (ModuleCat.{u} R) ℕ} :
    K ◁ (0 : M ⟶ N) = 0 := by
  ext n : 1
  refine mapBifunctor.hom_ext fun i j h ↦ ?_
  simp

/-- **The Künneth bicomplex.** Its column `p` is `K ⊗ Q.X p`, where `Q` is the Cartan–Eilenberg
resolution of `L`, and its horizontal differentials are induced by those of `Q`. -/
def kunnethBicomplex : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ) where
  X p := K ⊗ (cartanEilenbergResolution L).X p
  d p p' := K ◁ (cartanEilenbergResolution L).d p p'
  shape p p' h := by rw [(cartanEilenbergResolution L).shape _ _ h, whiskerLeft_zero]
  d_comp_d' p p' p'' _ _ := by
    rw [← MonoidalCategory.whiskerLeft_comp, HomologicalComplex.d_comp_d, whiskerLeft_zero]

/-- The augmentation of the column `0` of the Künneth bicomplex to `K ⊗ L`. -/
def kunnethBicomplexε : (kunnethBicomplex K L).X 0 ⟶ K ⊗ L :=
  K ◁ cartanEilenbergResolutionπ L

@[reassoc (attr := simp)]
lemma kunnethBicomplex_d_comp_ε : (kunnethBicomplex K L).d 1 0 ≫ kunnethBicomplexε K L = 0 := by
  change K ◁ _ ≫ K ◁ _ = 0
  rw [← MonoidalCategory.whiskerLeft_comp, cartanEilenbergResolution.d_comp_π, whiskerLeft_zero]

/-- The augmentation of the total complex of the Künneth bicomplex to `K ⊗ L`. -/
def kunnethBicomplexAugmentation :
    (kunnethBicomplex K L).total (ComplexShape.down ℕ) ⟶ K ⊗ L :=
  HomologicalComplex₂.totalAugmentation _ (kunnethBicomplexε K L)
    (kunnethBicomplex_d_comp_ε K L)

variable [∀ p, Module.Flat R (K.X p)]

/-- Tensoring with a complex of flat modules keeps the sequences
`0 ⟶ kernels (p + 1) ⟶ Q.X p ⟶ kernels p ⟶ 0` of the Cartan–Eilenberg resolution short exact. -/
lemma shortExact_whiskerLeft_row (p : ℕ) :
    (ShortComplex.mk (K ◁ rowι L p) (K ◁ rowπ L p)
      (by rw [← MonoidalCategory.whiskerLeft_comp, rowι_rowπ, whiskerLeft_zero])).ShortExact := by
  have := shortExact_tensorLeftShortComplex_of_preservesFiniteLimits K (shortExact_row L p)
    fun n ↦ (Finset.antidiagonal n).finite_toSet.subset fun x hx ↦ by simpa using hx
  convert this using 2

omit [∀ p, Module.Flat R (K.X p)] in
/-- The map `K ⊗ Q.X 0 ⟶ K ⊗ L` vanishes on the image of the differential of the Künneth
bicomplex. -/
lemma whiskerLeft_d_comp_rowπ :
    K ◁ (cartanEilenbergResolution L).d 1 0 ≫ K ◁ rowπ L 0 = 0 := by
  rw [← MonoidalCategory.whiskerLeft_comp, d_succ, Category.assoc, rowι_rowπ, comp_zero,
    whiskerLeft_zero]

omit [∀ p, Module.Flat R (K.X p)] in
/-- In degree `n`, the map `K ⊗ Q.X 0 ⟶ K ⊗ L` vanishes on the image of the differential of the
row `n` of the Künneth bicomplex. -/
lemma rowAugmentation_comp (n : ℕ) :
    (((HomologicalComplex.eval _ _ n).mapHomologicalComplex _).obj (kunnethBicomplex K L)).d 1 0 ≫
      (K ◁ rowπ L 0).f n = 0 :=
  (comp_f _ _ n).symm.trans
    ((congrArg (fun f : K ⊗ (cartanEilenbergResolution L).X 1 ⟶ K ⊗ kernels L 0 ↦ f.f n)
      (whiskerLeft_d_comp_rowπ K L)).trans (zero_f _ _ n))

/-- The row `n` of the Künneth bicomplex is spliced from the degree `n` parts of the short exact
sequences `shortExact_whiskerLeft_row`, so its augmentation to `(K ⊗ L).X n` is a
quasi-isomorphism. -/
lemma quasiIso_kunnethBicomplex_row (n : ℕ) :
    QuasiIso ((ChainComplex.toSingle₀Equiv
      (((HomologicalComplex.eval _ _ n).mapHomologicalComplex _).obj (kunnethBicomplex K L))
      ((K ⊗ kernels L 0).X n)).symm ⟨(K ◁ rowπ L 0).f n,
        rowAugmentation_comp K L n⟩) := by
  let X := ((HomologicalComplex.eval _ _ n).mapHomologicalComplex _).obj (kunnethBicomplex K L)
  let ι (p : ℕ) : (K ⊗ kernels L (p + 1)).X n ⟶ X.X p := (K ◁ rowι L p).f n
  let ε (p : ℕ) : X.X p ⟶ (K ⊗ kernels L p).X n := (K ◁ rowπ L p).f n
  have w (p : ℕ) : ι p ≫ ε p = 0 :=
    (comp_f (K ◁ rowι L p) (K ◁ rowπ L p) n).symm.trans (by
      rw [← MonoidalCategory.whiskerLeft_comp, rowι_rowπ, whiskerLeft_zero, zero_f])
  have hS (p : ℕ) : (ShortComplex.mk _ _ (w p)).ShortExact :=
    ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans (Category.comp_id _).symm)
        ((Category.id_comp _).trans (Category.comp_id _).symm))
      ((shortExact_iff_degreewise_shortExact _).1 (shortExact_whiskerLeft_row K L p) n)
  have hd (p : ℕ) : X.d (p + 1) p = ε (p + 1) ≫ ι p :=
    (congrArg (fun f ↦ (K ◁ f).f n) (d_succ L p)).trans
      ((congrArg (fun f ↦ f.f n)
        (MonoidalCategory.whiskerLeft_comp K (rowπ L (p + 1)) (rowι L p))).trans (comp_f _ _ n))
  exact ChainComplex.quasiIso_toSingle₀Equiv_symm_of_shortExact ι ε w hS hd

/-- **The Künneth bicomplex computes `K ⊗ L`.** If every term of `K` is flat, the augmentation
of the total complex of the Künneth bicomplex to `K ⊗ L` is a quasi-isomorphism. -/
theorem quasiIso_kunnethBicomplexAugmentation : QuasiIso (kunnethBicomplexAugmentation K L) := by
  let φ := (ChainComplex.toSingle₀Equiv (kunnethBicomplex K L) (K ⊗ L)).symm
    ⟨kunnethBicomplexε K L, kunnethBicomplex_d_comp_ε K L⟩
  have hφ (n : ℕ) : QuasiIso (((HomologicalComplex.eval _ _ n).mapHomologicalComplex _).map φ) := by
    rw [← quasiIso_iff_comp_right _
      ((singleMapHomologicalComplex (HomologicalComplex.eval _ _ n) _ 0).hom.app (K ⊗ L))]
    have heq : ((HomologicalComplex.eval _ _ n).mapHomologicalComplex _).map φ ≫
        (singleMapHomologicalComplex (HomologicalComplex.eval _ _ n) _ 0).hom.app (K ⊗ L) =
        (ChainComplex.toSingle₀Equiv _ ((K ⊗ kernels L 0).X n)).symm ⟨(K ◁ rowπ L 0).f n,
          rowAugmentation_comp K L n⟩ := by
      apply HomologicalComplex.to_single_hom_ext
      simp only [Functor.mapHomologicalComplex_obj_X, eval_obj, single₀_obj_zero,
        Functor.comp_obj, comp_f, Functor.mapHomologicalComplex_map_f,
        singleMapHomologicalComplex_hom_app_self, single₀ObjXSelf, Iso.refl_hom, eval_map, id_f,
        Iso.refl_inv, Category.comp_id, Functor.mapHomologicalComplex_obj_d]
      rw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero, eval_map, kunnethBicomplexε,
        cartanEilenbergResolutionπ_eq]
      exact (ChainComplex.toSingle₀Equiv_symm_apply_f_zero
        (C := ((HomologicalComplex.eval _ _ n).mapHomologicalComplex _).obj (kunnethBicomplex K L))
        ((K ◁ rowπ L 0).f n) _).symm
    rw [heq]
    exact quasiIso_kunnethBicomplex_row K L n
  have := HomologicalComplex₂.quasiIso_totalAugmentation_of_rows φ hφ
  unfold kunnethBicomplexAugmentation
  convert this using 2
  simp [φ]

end HomologicalComplex
