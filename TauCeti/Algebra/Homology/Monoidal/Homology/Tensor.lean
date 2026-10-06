/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Preserves.BifunctorCokernel
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Homology objects tensored with an object

Let `K` be a homological complex in a preadditive monoidal category `C`.  The homology object
`K.homology p` is the cokernel of the map `K.toCycles (c.prev p) p` from the chains of degree
`c.prev p` to the cycles of degree `p`.  If tensoring with an object `T` preserves cokernels (for
instance for modules over a commutative ring), then `K.homology p ⊗ T` is the cokernel of
`K.toCycles (c.prev p) p ▷ T`, and symmetrically `T ⊗ K.homology p` is the cokernel of
`T ◁ K.toCycles (c.prev p) p`.  As a consequence, morphisms out of
`K.homology p ⊗ L.homology q` are determined on tensor products of classes of cycles.

## Main definitions and results

* `HomologicalComplex.homologyWhiskerRightIsCokernel` and
  `HomologicalComplex.homologyWhiskerLeftIsCokernel`: `K.homology p ⊗ T` and `T ⊗ K.homology p`
  are the cokernels of the boundaries tensored with `T`.
* `HomologicalComplex.homology_tensor_homology_hom_ext`: morphisms out of
  `K.homology p ⊗ L.homology q` are determined by their composites with
  `K.homologyπ p ⊗ₘ L.homologyπ q`.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  {I : Type*} {c : ComplexShape I} (K L : HomologicalComplex C c) (p q : I)
  [K.HasHomology p] [L.HasHomology q]

/-- If tensoring on the right with `T` preserves cokernels, then `K.homology p ⊗ T` is the
cokernel of the boundaries of `K` tensored with `T`. -/
def homologyWhiskerRightIsCokernel (T : C)
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight T)] :
    IsColimit (CokernelCofork.ofπ (K.homologyπ p ▷ T)
      (by rw [← comp_whiskerRight, toCycles_comp_homologyπ,
        MonoidalPreadditive.zero_whiskerRight]) :
        Cofork (K.toCycles (c.prev p) p ▷ T) 0) :=
  isColimitCoforkMapOfIsColimit' (tensorRight T) _ (K.homologyIsCokernel (c.prev p) p rfl)

/-- If tensoring on the left with `T` preserves cokernels, then `T ⊗ K.homology p` is the
cokernel of the boundaries of `K` tensored with `T`. -/
def homologyWhiskerLeftIsCokernel (T : C)
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft T)] :
    IsColimit (CokernelCofork.ofπ (T ◁ K.homologyπ p)
      (by rw [← whiskerLeft_comp, toCycles_comp_homologyπ,
        MonoidalPreadditive.whiskerLeft_zero]) :
        Cofork (T ◁ K.toCycles (c.prev p) p) 0) :=
  isColimitCoforkMapOfIsColimit' (tensorLeft T) _ (K.homologyIsCokernel (c.prev p) p rfl)

/-- Morphisms out of `K.homology p ⊗ L.homology q` are determined by their composites with the
tensor product of the projections from cycles.  This is
`CokernelCofork.isColimitMapBifunctor.hom_ext` for the tensor product bifunctor and the cokernel
presentations `homologyIsCokernel`, stated as an `@[ext]` lemma. -/
@[ext]
lemma homology_tensor_homology_hom_ext
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft (K.homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight (L.cycles q))]
    {T : C} {f g : K.homology p ⊗ L.homology q ⟶ T}
    (hfg : (K.homologyπ p ⊗ₘ L.homologyπ q) ≫ f = (K.homologyπ p ⊗ₘ L.homologyπ q) ≫ g) :
    f = g := by
  have : PreservesColimit (parallelPair (L.toCycles (c.prev q) q) 0)
      ((curriedTensor C).obj
        (CokernelCofork.ofπ (K.homologyπ p) (K.toCycles_comp_homologyπ (c.prev p) p)).pt) :=
    inferInstanceAs (PreservesColimit _ (tensorLeft (K.homology p)))
  have : PreservesColimit (parallelPair (K.toCycles (c.prev p) p) 0)
      ((curriedTensor C).flip.obj (L.cycles q)) :=
    inferInstanceAs (PreservesColimit _ (tensorRight (L.cycles q)))
  exact CokernelCofork.isColimitMapBifunctor.hom_ext (K.homologyIsCokernel (c.prev p) p rfl)
    (L.homologyIsCokernel (c.prev q) q rfl) (curriedTensor C) (by simpa [tensorHom_def] using hfg)

end HomologicalComplex
