/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import TauCeti.Algebra.Homology.ShortComplex.Resolution

/-!
# Left derived functors on a projective presentation of length one

Let `S : 0 ⟶ P₁ ⟶ P₀ ⟶ M ⟶ 0` be a short exact sequence in an abelian category with `P₁` and
`P₀` projective. Then `⋯ ⟶ 0 ⟶ P₁ ⟶ P₀` is a projective resolution of `M`
(`CategoryTheory.ShortComplex.ShortExact.projectiveResolution`), and for every additive functor
`F` it computes the left derived functors of `F` at `M`:

* `L₁F(M)` is the kernel of `F(P₁) ⟶ F(P₀)`
  (`CategoryTheory.ShortComplex.ShortExact.leftDerivedOneIsoKernel`);
* `LₙF(M)` vanishes for `n ≥ 2`
  (`CategoryTheory.ShortComplex.ShortExact.isZero_leftDerived_add_two`).

The complex, its augmentation, and the chain maps induced by morphisms of short complexes are
constructed in `TauCeti.Algebra.Homology.ShortComplex.Resolution` for any category with zero
morphisms and a zero object.

The identification of `L₁F(M)` is natural in the functor `F` and in maps of such presentations.
For an arbitrary additive `F` the projectivity of `P₁` is needed even in degree `1`: the long exact
sequence only gives `L₁F(M) ≅ ker(L₀F(P₁) ⟶ F(P₀))`, and `L₀F(P₁) = F(P₁)` for projective `P₁`.
Over a principal ideal domain every module has such a presentation, by a free module and its
kernel, which is again free; applied to the tensor product, this computes `Tor₁` in the Künneth
and universal coefficient theorems.

The file also records two general facts. The natural transformation `LₙF ⟶ LₙG` induced by
`α : F ⟶ G` is additive in `α` (`CategoryTheory.NatTrans.leftDerived_add`), so that a derived
functor depending on a parameter through a natural transformation, such as `Tor` in its underived
variable, is an additive functor of that parameter. An exact additive functor has no positive left
derived functors (`CategoryTheory.Functor.isZero_leftDerived_succ`).

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 2.4, for left derived functors
  computed from a projective resolution.
-/

public section

noncomputable section

namespace CategoryTheory

open Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {S S' : ShortComplex C}

namespace ShortComplex

/-- For a short exact `S`, the augmentation of `S.resolutionComplex` is a quasi-isomorphism. -/
lemma quasiIso_resolutionπ (hS : S.ShortExact) : _root_.QuasiIso S.resolutionπ := by
  refine ⟨fun n => ?_⟩
  obtain _ | _ | n := n
  · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
    refine ⟨(ShortComplex.exact_iff_of_iso ?_).2 hS.exact, ?_⟩
    · refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
      · exact (Category.id_comp _).trans (Category.comp_id _).symm
      · simp only [HomologicalComplex.shortComplexFunctor'_map_τ₂, Iso.refl_hom,
          resolutionπ_f_zero]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
    · simp only [HomologicalComplex.shortComplexFunctor'_map_τ₂, resolutionπ_f_zero]
      exact hS.epi_g
  · rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _),
      HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
    exact ShortComplex.exact_of_f_is_kernel _ <|
      KernelFork.IsLimit.ofMonoOfIsZero _ hS.mono_f (isZero_zero C)
  · rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _),
      HomologicalComplex.exactAt_iff]
    exact ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C)

namespace ShortExact

variable (hS : S.ShortExact) [Projective S.X₁] [Projective S.X₂]

/-- A short exact sequence `0 ⟶ P₁ ⟶ P₀ ⟶ M ⟶ 0` with `P₁` and `P₀` projective gives the
projective resolution `⋯ ⟶ 0 ⟶ P₁ ⟶ P₀` of `M`, with `P₀` in degree `0`. -/
@[expose]
def projectiveResolution : ProjectiveResolution S.X₃ where
  complex := S.resolutionComplex
  projective n := by
    obtain _ | _ | n := n
    · exact inferInstanceAs (Projective S.X₂)
    · exact inferInstanceAs (Projective S.X₁)
    · exact inferInstanceAs (Projective (0 : C))
  π := S.resolutionπ
  quasiIso := quasiIso_resolutionπ hS

/-- The complex of the resolution is `S.resolutionComplex`. -/
@[simp]
lemma projectiveResolution_complex : hS.projectiveResolution.complex = S.resolutionComplex :=
  (rfl)

/-- The augmentation of the resolution is `S.resolutionπ`. -/
@[simp]
lemma projectiveResolution_π : hS.projectiveResolution.π = S.resolutionπ :=
  (rfl)

variable {D : Type*} [Category* D] [Abelian D] [HasProjectiveResolutions C]
  (F : C ⥤ D) [F.Additive]

include hS in
/-- The left derived functors of `F` vanish in degrees at least `2` on an object with a
projective presentation of length one. -/
lemma isZero_leftDerived_add_two (n : ℕ) : IsZero ((F.leftDerived (n + 2)).obj S.X₃) := by
  refine IsZero.of_iso ?_ (hS.projectiveResolution.isoLeftDerivedObj F (n + 2))
  rw [HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff]
  exact ShortComplex.exact_of_isZero_X₂ _ (F.map_isZero (S.isZero_resolutionComplex_X_add_two n))

omit [Projective S.X₁] [Projective S.X₂] [HasProjectiveResolutions C] in
/-- No differential enters degree `1` of the mapped presentation complex. -/
private lemma mapHomologicalComplex_d_two_one :
    ((F.mapHomologicalComplex _).obj S.resolutionComplex).d 2 1 = 0 :=
  (F.map_isZero (S.isZero_resolutionComplex_X_add_two 0)).eq_of_src _ _

/-- Homology in degree `1` of the mapped presentation consists of its cycles. -/
private abbrev resolutionHomologyOneIsoCycles :
    ((F.mapHomologicalComplex _).obj hS.projectiveResolution.complex).cycles 1 ≅
      ((F.mapHomologicalComplex _).obj hS.projectiveResolution.complex).homology 1 :=
  ((F.mapHomologicalComplex _).obj hS.projectiveResolution.complex).isoHomologyπ
    2 1 (by simp) (mapHomologicalComplex_d_two_one F)

/-- The map `L₁F(M) ⟶ F(P₁)` computed on `F` applied to the resolution: the class in degree `1`
of a cycle goes to that cycle, since no nonzero differential enters degree `1`. -/
private def leftDerivedOneι :
    (F.leftDerived 1).obj S.X₃ ⟶
      ((F.mapHomologicalComplex _).obj hS.projectiveResolution.complex).X 1 :=
  ((hS.projectiveResolution.isoLeftDerivedObj F 1).hom ≫
    (hS.resolutionHomologyOneIsoCycles F).inv) ≫
    ((F.mapHomologicalComplex _).obj hS.projectiveResolution.complex).iCycles 1

private lemma leftDerivedOneι_comp :
    hS.leftDerivedOneι F ≫
      ((F.mapHomologicalComplex _).obj hS.projectiveResolution.complex).d 1 0 = 0 := by
  rw [leftDerivedOneι, Category.assoc, HomologicalComplex.iCycles_d, Limits.comp_zero]

/-- `L₁F(M) ⟶ F(P₁)` is a kernel of `F(P₁) ⟶ F(P₀)`. -/
private def isLimitLeftDerivedOneι :
    IsLimit (KernelFork.ofι _ (hS.leftDerivedOneι_comp F)) :=
  IsKernel.isoKernel _ _
    (((F.mapHomologicalComplex _).obj hS.projectiveResolution.complex).cyclesIsKernel 1 0 (by simp))
    (hS.projectiveResolution.isoLeftDerivedObj F 1 ≪≫
      (hS.resolutionHomologyOneIsoCycles F).symm) rfl

/-- On an object with a projective presentation `0 ⟶ P₁ ⟶ P₀ ⟶ M ⟶ 0`, the first left derived
functor of `F` is the kernel of `F(P₁) ⟶ F(P₀)`. It sends the homology class of a cycle of `F`
applied to the resolution to that cycle
(`homologyπ_comp_isoLeftDerivedObj_inv_comp_leftDerivedOneIsoKernel_hom_comp_ι`). -/
def leftDerivedOneIsoKernel : (F.leftDerived 1).obj S.X₃ ≅ kernel (F.map S.f) :=
  (hS.isLimitLeftDerivedOneι F).conePointUniqueUpToIso (limit.isLimit _)

/-- The identification of `L₁F(M)` with a kernel, followed by the inclusion into `F(P₁)`. -/
@[reassoc]
private lemma leftDerivedOneIsoKernel_hom_comp_ι :
    (hS.leftDerivedOneIsoKernel F).hom ≫ kernel.ι (F.map S.f) =
      (hS.projectiveResolution.isoLeftDerivedObj F 1).hom ≫
        (hS.resolutionHomologyOneIsoCycles F).inv ≫
        ((F.mapHomologicalComplex _).obj hS.projectiveResolution.complex).iCycles 1 :=
  (IsLimit.conePointUniqueUpToIso_hom_comp (hS.isLimitLeftDerivedOneι F) (limit.isLimit _)
    WalkingParallelPair.zero).trans (Category.assoc _ _ _)

/-- The identification of `L₁F(M)` with the kernel of `F(P₁) ⟶ F(P₀)` sends the homology class
of a cycle of `F` applied to the resolution to that cycle. -/
@[reassoc (attr := simp)]
lemma homologyπ_comp_isoLeftDerivedObj_inv_comp_leftDerivedOneIsoKernel_hom_comp_ι :
    ((F.mapHomologicalComplex _).obj S.resolutionComplex).homologyπ 1 ≫
      (hS.projectiveResolution.isoLeftDerivedObj F 1).inv ≫
        (hS.leftDerivedOneIsoKernel F).hom ≫ kernel.ι (F.map S.f) =
      ((F.mapHomologicalComplex _).obj S.resolutionComplex).iCycles 1 := by
  rw [leftDerivedOneIsoKernel_hom_comp_ι]
  -- `homologyπ` lands in `homology`, while `isoLeftDerivedObj` lands in `homologyFunctor` applied
  -- to the complex. These agree only definitionally, so the cancellation needs `erw`, as in
  -- Mathlib's `ProjectiveResolution.isoLeftDerivedObj_hom_naturality`.
  erw [Iso.inv_hom_id_assoc]
  exact HomologicalComplex.isoHomologyπ_hom_inv_id_assoc _ 2 1 (by simp)
    (mapHomologicalComplex_d_two_one F) _

variable {hS} {G : C ⥤ D} [G.Additive] (hS' : S'.ShortExact) [Projective S'.X₁] [Projective S'.X₂]

include hS' in
/-- A morphism between first left derived functors which is computed on the resolutions by a
chain map `ψ` acts on the kernels by the degree `1` component of `ψ`. -/
private lemma comp_leftDerivedOneIsoKernel_hom_comp_ι
    (ψ : (F.mapHomologicalComplex _).obj hS.projectiveResolution.complex ⟶
      (G.mapHomologicalComplex _).obj hS'.projectiveResolution.complex)
    (m : (F.leftDerived 1).obj S.X₃ ⟶ (G.leftDerived 1).obj S'.X₃)
    (hm : m = (hS.projectiveResolution.isoLeftDerivedObj F 1).hom ≫
      (HomologicalComplex.homologyFunctor D _ 1).map ψ ≫
        (hS'.projectiveResolution.isoLeftDerivedObj G 1).inv) :
    m ≫ (hS'.leftDerivedOneIsoKernel G).hom ≫ kernel.ι (G.map S'.f) =
      ((hS.leftDerivedOneIsoKernel F).hom ≫ kernel.ι (F.map S.f)) ≫ ψ.f 1 := by
  subst hm
  rw [Category.assoc, Category.assoc, leftDerivedOneIsoKernel_hom_comp_ι,
    leftDerivedOneIsoKernel_hom_comp_ι]
  -- The cycle inclusions land in `F` applied to the resolution in degree `1` rather than in
  -- `F.obj S.X₁`, and `homologyFunctor` is only definitionally `homology`. The rewrites at these
  -- junctions therefore need `erw`, as in Mathlib's
  -- `ProjectiveResolution.isoLeftDerivedObj_hom_naturality`, and the final reassociation is
  -- composed as a term.
  erw [Iso.inv_hom_id_assoc,
    HomologicalComplex.isoHomologyπ_inv_naturality_assoc ψ 2 1 (by simp)
      (mapHomologicalComplex_d_two_one F)
      (mapHomologicalComplex_d_two_one G),
    HomologicalComplex.cyclesMap_i]
  exact ((Category.assoc _ _ _).trans (_ ≫= Category.assoc _ _ _)).symm

omit [G.Additive] [Projective S'.X₁] [Projective S'.X₂] in
/-- The identification of `L₁F(M)` with the kernel of `F(P₁) ⟶ F(P₀)` is natural in `F`. -/
@[reassoc]
lemma leftDerived_app_comp_leftDerivedOneIsoKernel_hom (hS : S.ShortExact) [G.Additive]
    (α : F ⟶ G) :
    (NatTrans.leftDerived α 1).app S.X₃ ≫ (hS.leftDerivedOneIsoKernel G).hom =
      (hS.leftDerivedOneIsoKernel F).hom ≫
        kernel.map (F.map S.f) (G.map S.f) (α.app S.X₁) (α.app S.X₂) (α.naturality S.f) := by
  rw [← cancel_mono (kernel.ι (G.map S.f)), Category.assoc, Category.assoc, kernel.lift_ι,
    ← Category.assoc (hS.leftDerivedOneIsoKernel F).hom]
  exact comp_leftDerivedOneIsoKernel_hom_comp_ι F hS _ _
    (ProjectiveResolution.leftDerived_app_eq α hS.projectiveResolution 1)

omit [G.Additive] in
/-- The identification of `L₁F(M)` with the kernel of `F(P₁) ⟶ F(P₀)` is natural in maps of
projective presentations. -/
@[reassoc]
lemma leftDerived_map_comp_leftDerivedOneIsoKernel_hom (φ : S ⟶ S') :
    (F.leftDerived 1).map φ.τ₃ ≫ (hS'.leftDerivedOneIsoKernel F).hom =
      (hS.leftDerivedOneIsoKernel F).hom ≫
        kernel.map (F.map S.f) (F.map S'.f) (F.map φ.τ₁) (F.map φ.τ₂)
          (by simp only [← F.map_comp, φ.comm₁₂]) := by
  rw [← cancel_mono (kernel.ι (F.map S'.f)), Category.assoc, Category.assoc, kernel.lift_ι,
    ← Category.assoc (hS.leftDerivedOneIsoKernel F).hom]
  rw [← resolutionComplexMap_f_one φ]
  exact comp_leftDerivedOneIsoKernel_hom_comp_ι F hS' _ _
    (F.leftDerived_map_eq 1 φ.τ₃ (P := hS.projectiveResolution) (Q := hS'.projectiveResolution)
      (resolutionComplexMap φ) (resolutionComplexMap_comp_resolutionπ φ))

end ShortExact

end ShortComplex

section Additive

variable [HasProjectiveResolutions C] {D : Type*} [Category* D] [Abelian D]

/-- The natural transformation between left derived functors induced by a natural transformation
is additive in it. -/
@[simp]
theorem NatTrans.leftDerived_add {F G : C ⥤ D} [F.Additive] [G.Additive] (α β : F ⟶ G) (n : ℕ) :
    NatTrans.leftDerived (α + β) n = NatTrans.leftDerived α n + NatTrans.leftDerived β n := by
  ext X
  have h : (NatTrans.mapHomologicalComplex (α + β) _).app (projectiveResolution X).complex =
      (NatTrans.mapHomologicalComplex α _).app _ + (NatTrans.mapHomologicalComplex β _).app _ := by
    ext
    simp
  simp only [NatTrans.app_add, (projectiveResolution X).leftDerived_app_eq, h, Functor.map_add,
    Preadditive.add_comp, Preadditive.comp_add]

/-- An exact additive functor has no positive left derived functors. -/
theorem Functor.isZero_leftDerived_succ (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (X : C) (q : ℕ) : IsZero ((F.leftDerived (q + 1)).obj X) := by
  let P := projectiveResolution X
  refine IsZero.of_iso ?_ (P.isoLeftDerivedObj F (q + 1))
  rw [HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (q + 2) (q + 1) q (by simp) (by simp)]
  exact (P.exact_succ q).map F

end Additive

end CategoryTheory
