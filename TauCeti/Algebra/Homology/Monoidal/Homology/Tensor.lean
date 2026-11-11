/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Homology objects tensored with an object

Let `K` be a homological complex in a preadditive monoidal category `C`.  The homology object
`K.homology p` is the cokernel of the map `K.toCycles (c.prev p) p` from the chains of degree
`c.prev p` to the cycles of degree `p`.  If tensoring with an object `T` preserves this cokernel
(for instance, if it preserves all cokernels, as for modules over a commutative ring), then
`K.homology p ⊗ T` is the cokernel of `K.toCycles (c.prev p) p ▷ T`, and symmetrically
`T ⊗ K.homology p` is the cokernel of `T ◁ K.toCycles (c.prev p) p`.  As a consequence,
morphisms out of `K.homology p ⊗ L.homology q` are determined on tensor products of classes of
cycles.

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

/-- If tensoring on the right with `T` preserves the cokernel of `K.toCycles (c.prev p) p`, then
`K.homology p ⊗ T` is the cokernel of the boundaries of `K` tensored with `T`. -/
def homologyWhiskerRightIsCokernel (T : C)
    [PreservesColimit (parallelPair (K.toCycles (c.prev p) p) 0) (tensorRight T)] :
    IsColimit (CokernelCofork.ofπ (K.homologyπ p ▷ T)
      (by simp [← comp_whiskerRight]) :
        Cofork (K.toCycles (c.prev p) p ▷ T) 0) :=
  isColimitCoforkMapOfIsColimit' (tensorRight T) _ (K.homologyIsCokernel (c.prev p) p rfl)

/-- If tensoring on the left with `T` preserves the cokernel of `K.toCycles (c.prev p) p`, then
`T ⊗ K.homology p` is the cokernel of the boundaries of `K` tensored with `T`. -/
def homologyWhiskerLeftIsCokernel (T : C)
    [PreservesColimit (parallelPair (K.toCycles (c.prev p) p) 0) (tensorLeft T)] :
    IsColimit (CokernelCofork.ofπ (T ◁ K.homologyπ p)
      (by simp [← whiskerLeft_comp]) :
        Cofork (T ◁ K.toCycles (c.prev p) p) 0) :=
  isColimitCoforkMapOfIsColimit' (tensorLeft T) _ (K.homologyIsCokernel (c.prev p) p rfl)

/-- Morphisms out of `K.homology p ⊗ L.homology q` are determined by their composites with the
tensor product of the projections from cycles, provided tensoring preserves the cokernels
presenting the two homology objects. -/
@[ext]
lemma homology_tensor_homology_hom_ext
    [PreservesColimit (parallelPair (L.toCycles (c.prev q) q) 0) (tensorLeft (K.homology p))]
    [PreservesColimit (parallelPair (K.toCycles (c.prev p) p) 0) (tensorRight (L.cycles q))]
    {T : C} {f g : K.homology p ⊗ L.homology q ⟶ T}
    (hfg : (K.homologyπ p ⊗ₘ L.homologyπ q) ≫ f = (K.homologyπ p ⊗ₘ L.homologyπ q) ≫ g) :
    f = g := by
  refine Cofork.IsColimit.hom_ext (L.homologyWhiskerLeftIsCokernel q (K.homology p)) ?_
  refine Cofork.IsColimit.hom_ext (K.homologyWhiskerRightIsCokernel p (L.cycles q)) ?_
  simpa [tensorHom_def] using hfg

end HomologicalComplex
