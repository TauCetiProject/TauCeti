/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver.Basic
public import TauCeti.AlgebraicGeometry.Limits.Coproduct

/-!
# Finite coproducts of projective schemes

A finite family of schemes projective over a commutative ring has a projective coproduct over
that ring. The ambient module is the finite product of the modules of homogeneous coordinates
of the summands. Projection onto a coordinate block induces a closed immersion of its projective
spectrum; different blocks have disjoint images. The coproduct of these embeddings is a closed
immersion, without any reducedness or flatness assumption on the coefficient ring.

The structure morphism of the coproduct is the descent of the structure morphisms of its
summands. In particular, the result concerns projectivity over the specified affine base.
The coordinate maps use `SymmetricAlgebra.gradedMap`, the graded lift of the linear
projections, together with `Proj.map` and `Proj.isClosedImmersion_map`.
-/

public section

universe u v

open CategoryTheory Limits AlgebraicGeometry
open TauCeti.SymmetricAlgebra

namespace AlgebraicGeometry.Scheme

variable (R : Type u) [CommRing R] {ι : Type v} [Finite ι]
  (X : ι → Scheme.{u}) [∀ i, (X i).Over (Spec (.of R))]

/-- A finite coproduct of schemes projective over `Spec R` is projective over `Spec R`, with
structure morphism the descent of the structure morphisms of its summands. -/
theorem IsProjectiveOver.sigma [∀ i, (X i).IsProjectiveOver R] :
    (∐ X).IsProjectiveOver R := by
  classical
  -- Reindex into the ring universe so the ambient product stays in that universe.
  let Y : Shrink.{u} ι → Scheme.{u} := X ∘ (equivShrink.{u} ι).symm
  have : Finite (Shrink.{u} ι) := Finite.of_equiv ι (equivShrink.{u} ι)
  let : ∀ i, (Y i).Over (Spec (.of R)) := by
    dsimp only [Y, Function.comp_apply]
    infer_instance
  have : ∀ i, (Y i).IsProjectiveOver R := by
    dsimp only [Y, Function.comp_apply]
    infer_instance
  have hY : (∐ Y).IsProjectiveOver R := by
    choose M _ _ _ f hf hfR using fun i ↦
      IsProjectiveOver.exists_isClosedImmersion (R := R) (X := Y i)
    let g (i : Shrink.{u} ι) := f i ≫ projPiι.{u, u} R M i
    have hdisj : Pairwise fun i j ↦ Disjoint (Set.range (g i)) (Set.range (g j)) := by
      intro i j hij
      simpa only [g, Function.comp_def, ← Scheme.Hom.comp_apply] using
        (pairwise_disjoint_range_projPiι.{u, u} R M hij).mono
          (Set.range_comp_subset_range (f i) (projPiι.{u, u} R M i))
          (Set.range_comp_subset_range (f j) (projPiι.{u, u} R M j))
    have : ∀ i, IsClosedImmersion (g i) := fun _ ↦ inferInstance
    have : IsClosedImmersion (Sigma.desc g) := isClosedImmersion_sigmaDesc g hdisj
      (locallyFinite_of_finite _)
    refine ⟨⟨(∀ i, M i), inferInstance, inferInstance, inferInstance, Sigma.desc g,
      inferInstance, ⟨?_⟩⟩⟩
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc_assoc, comp_over]
  let e : (∐ Y) ≅ ∐ X := Sigma.reindex (equivShrink.{u} ι).symm X
  have : e.hom.IsOver (Spec (.of R)) := by
    constructor
    apply Sigma.hom_ext
    intro i
    dsimp only [e]
    rw [Sigma.ι_reindex_hom_assoc, comp_over, comp_over]
  exact IsProjectiveOver.of_isClosedImmersion R e.inv

end AlgebraicGeometry.Scheme
