/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MappingTorus.FiberPair

/-!
# The Wang sequence of a mapping torus

The long exact sequence of the pair consisting of a mapping torus and one of its fibres gives
the Wang sequence.  The relative homology identification is the one in
`TauCeti.MappingTorus.singularHomologyFiberPairIso`.  The boundary morphism of the pair, under
this identification, is `id - φ_*` followed by the map induced by the fibre inclusion.  This file
records the exact portion around the homology of the mapping torus, with no restriction on the
coefficient object beyond those required for singular homology.

The construction is the mapping-torus sequence of Hatcher, *Algebraic Topology*, Section 2.2.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe w v u

namespace TauCeti.MappingTorus

variable {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F)
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- The map on singular homology induced by including the fibre of a mapping torus into its total
space, with the fibre represented by the subspace object of `fiberPair`. -/
noncomputable def wangInclusion (n : ℕ) :
    (TopPair.toSSetPair.obj (fiberPair φ)).left.homology R n ⟶
      (TopPair.toSSetPair.obj (fiberPair φ)).right.homology R n :=
  SSet.homologyMap (TopPair.toSSetPair.obj (fiberPair φ)).hom R n

/-- The connecting map in the Wang sequence, obtained from the pair sequence and the relative
homology identification `Hₙ₊₁(T, F) ≅ Hₙ(F)`. -/
noncomputable def wangConnecting (n : ℕ) :
    (TopPair.toSSetPair.obj (fiberPair φ)).right.homology R (n + 1) ⟶
      ((singularHomologyFunctor A n).obj R).obj (TopCat.of F) := by
  exact (TopPair.toSSetPair.obj (fiberPair φ)).homologyπ R (n + 1) ≫
    (singularHomologyFiberPairIso φ R n).hom

/-- The homology map induced by the fibre inclusion, followed by the map from ambient to relative
homology, is zero under the relative homology identification. -/
@[reassoc (attr := simp)]
theorem wangInclusion_comp_wangConnecting (n : ℕ) :
    wangInclusion φ R (n + 1) ≫ wangConnecting φ R n = 0 := by
  simp only [wangInclusion, wangConnecting]
  let Q := TopPair.toSSetPair.obj (fiberPair φ)
  let f := SSet.homologyMap Q.hom R (n + 1)
  let g := Q.homologyπ R (n + 1)
  calc
    f ≫ g ≫ (singularHomologyFiberPairIso φ R n).hom =
        (f ≫ g) ≫ (singularHomologyFiberPairIso φ R n).hom := by
          exact (Category.assoc f g _).symm
    _ = 0 := by rw [Q.homologyMap_hom_homologyπ, zero_comp]

/-- The exact portion `Hₙ₊₁(F) → Hₙ₊₁(T) → Hₙ(F)` of the Wang sequence. -/
theorem wang_exact_total (n : ℕ) :
    (ShortComplex.mk (wangInclusion φ R (n + 1)) (wangConnecting φ R n)
      (wangInclusion_comp_wangConnecting φ R n)).Exact := by
  let Q := TopPair.toSSetPair.obj (fiberPair φ)
  let S₁ := ShortComplex.mk (SSet.homologyMap Q.hom R (n + 1))
    (Q.homologyπ R (n + 1)) (Q.homologyMap_hom_homologyπ R (n + 1))
  have hS : S₁.Exact := Q.homology_exact₂ R (n + 1)
  let S₂ := ShortComplex.mk (wangInclusion φ R (n + 1)) (wangConnecting φ R n)
    (wangInclusion_comp_wangConnecting φ R n)
  let e : S₁ ≅ S₂ := ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (asIso (singularHomologyFiberPairIso φ R n).hom)
    (by
      simp [S₁, S₂, wangInclusion, Q, TopPair.toSSetPair_obj_hom,
        TopPair.toSSetPair_obj_left, TopPair.toSSetPair_obj_right])
    (by
      simp [S₁, S₂, wangConnecting, Q])
  exact ShortComplex.exact_of_iso e hS

end TauCeti.MappingTorus

end
