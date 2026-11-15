/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Induction

/-!
# A relative CW complex is the colimit of its skeleta

The skeleta `skeletonLT C j` of a relative CW complex `C` in a Hausdorff space, with their
inclusions into each other, form a sequential diagram in `TopCat` (`TauCeti.skeletonFunctor`),
and their inclusions into `C` form a cocone over it (`TauCeti.skeletonCocone`).  This cocone is a
colimit (`TauCeti.isColimitSkeletonCocone`): this is the weak topology of the complex, and maps
out of `C` are built skeleton by skeleton with
`TauCeti.exists_continuousMap_prod_complex_of_skeletonLT`.

The mathematical source is Hatcher, *Algebraic Topology*, Appendix, Proposition A.2.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Topology.RelCWComplex

universe w

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]

/-- The skeleta `skeletonLT C j` of a relative CW complex and their inclusions, as a sequential
diagram of spaces. -/
abbrev skeletonFunctor : ℕ ⥤ TopCat.{w} where
  obj j := skeletonObj C j
  map f := TopCat.ofHom (ContinuousMap.inclusion (skeletonLT_mono (mod_cast f.le)))

/-- The inclusions of the skeleta into the whole complex. -/
@[expose] def skeletonCocone : Cocone (skeletonFunctor C) where
  pt := TopCat.of C
  ι := { app j := TopCat.ofHom (ContinuousMap.inclusion (skeletonLT C (j : ℕ∞)).subset_complex) }

lemma coe_skeletonCocone_ι_app_apply (j : ℕ) (x : skeletonObj C j) :
    ((skeletonCocone C).ι.app j x).1 = x.1 :=
  (rfl)

/-- A map out of a relative CW complex defined on each skeleton, compatibly with the inclusions
of skeleta, is continuous: it is the value of the cocone `s` on any skeleton containing the
point. -/
private lemma exists_desc_skeletonCocone (s : Cocone (skeletonFunctor C)) :
    ∃ G : C(C, s.pt), ∀ (j : ℕ) (x : X) (hx : x ∈ (skeletonLT C (j : ℕ∞) : Set X)),
      G ⟨x, (skeletonLT C _).subset_complex hx⟩ = s.ι.app j ⟨x, hx⟩ := by
  have hle (j : ℕ) : (skeletonLT C ((0 + j : ℕ) : ℕ∞) : Set X) ⊆ skeletonLT C (j : ℕ∞) :=
    skeletonLT_mono (by simp)
  let F (j : ℕ) : C(Unit × (skeletonLT C ((0 + j : ℕ) : ℕ∞) : Set X), s.pt) :=
    (s.ι.app j).hom.comp ((ContinuousMap.inclusion (hle j)).comp ContinuousMap.snd)
  obtain ⟨G, hG⟩ := exists_continuousMap_prod_complex_of_skeletonLT (k := 0) F
    fun j _ x hx ↦ ConcreteCategory.congr_hom (s.w (homOfLE j.le_succ)) ⟨x, hle j hx⟩
  refine ⟨G.comp ((ContinuousMap.const C ()).prodMk (ContinuousMap.id C)), fun j x hx ↦ ?_⟩
  exact hG j () x (skeletonLT_mono (by simp) hx)

/-- **A relative CW complex is the colimit of its skeleta** in `TopCat`.  This is the weak
topology of the complex. -/
def isColimitSkeletonCocone : IsColimit (skeletonCocone C) where
  desc s := TopCat.ofHom (exists_desc_skeletonCocone C s).choose
  fac s j := by
    ext x
    exact (exists_desc_skeletonCocone C s).choose_spec j x.1 x.2
  uniq s m hm := by
    ext x
    obtain ⟨j, hj⟩ := exists_mem_skeletonLT_add 0 x.2
    rw [zero_add] at hj
    exact (ConcreteCategory.congr_hom (hm j) ⟨x.1, hj⟩).trans
      ((exists_desc_skeletonCocone C s).choose_spec j x.1 hj).symm

end TauCeti
