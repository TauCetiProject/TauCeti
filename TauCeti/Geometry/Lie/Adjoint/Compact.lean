/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.InvariantForm.Positive
public import TauCeti.Algebra.Lie.InvariantForm.RankOne
public import TauCeti.Geometry.Lie.Adjoint.InvariantForm

/-!
# The centre and derived algebra of a compact Lie group

The Lie algebra of a compact finite-dimensional real smooth Lie group is the direct sum
of its centre and derived ideal. The derived algebra is centreless and semisimple, and
its Killing form is negative definite. On the whole Lie algebra the Killing form is
nonpositive, with diagonal zero exactly on the centre. Unless it is abelian, the Lie algebra
contains a copy of `so(3) ≅ 𝔰𝔲(2)`. Connectedness is not required.

## Main results

* `TauCeti.Lie.exists_posDef_orthogonal_derivedSeries_one_eq_center_of_compactSpace`:
  a symmetric positive invariant form exhibits the centre as the orthogonal complement of the
  derived ideal.
* `TauCeti.Lie.isCompl_center_derivedSeries_one_of_compactSpace`: the centre and derived ideal
  complement one another.
* `TauCeti.Lie.derivedSeries_one_eq_top_iff_center_eq_bot`: the Lie algebra is perfect exactly
  when its centre is trivial.
* `TauCeti.Lie.isSemisimple_derivedSeries_one_of_compactSpace`: the derived algebra is semisimple.
* `TauCeti.Lie.hasCentralRadical_of_compactSpace`: the radical equals the centre.
* `LeftInvariantDerivation.killingForm_self_nonpos`: the Killing form is nonpositive.
* `LeftInvariantDerivation.killingForm_self_eq_zero_iff`: the diagonal of the Killing form
  vanishes exactly on the centre.
* `TauCeti.Lie.killingForm_derivedSeries_one_self_neg_of_compactSpace_of_ne_zero`:
  the derived algebra has negative-definite Killing form.
* `TauCeti.Lie.exists_injective_lieHom_soThree_of_compactSpace`: a non-abelian Lie algebra of a
  compact Lie group receives an injective homomorphism from `so(3) ≅ 𝔰𝔲(2)`.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer (2012),
  Definition 12.1.1, Lemma 12.1.2, Proposition 12.1.4, and Remark 12.2.14.
-/

public section

open scoped ContDiff Manifold
open LieAlgebra

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [CompactSpace G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

private instance : FiniteDimensional ℝ (LeftInvariantDerivation I G) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  exact finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint

/-- The Lie algebra of a compact finite-dimensional real smooth Lie group admits a symmetric
positive-definite invariant form for which the centre is the orthogonal complement of
the derived ideal. -/
theorem exists_posDef_orthogonal_derivedSeries_one_eq_center_of_compactSpace :
    ∃ (B : LinearMap.BilinForm ℝ (LeftInvariantDerivation I G))
      (hinv : B.lieInvariant (LeftInvariantDerivation I G)),
      LinearMap.BilinForm.IsSymm B ∧ B.toQuadraticMap.PosDef ∧
        LieAlgebra.InvariantForm.orthogonal B hinv
          (derivedSeries ℝ (LeftInvariantDerivation I G) 1) =
          center ℝ (LeftInvariantDerivation I G) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  obtain ⟨B, hsymm, hpos, hAd⟩ := exists_isSymm_bilinForm_Ad_invariant (I := I) (G := G)
  have hpos : B.toQuadraticMap.PosDef := B.posDef_toQuadraticMap_iff.mpr hpos
  have hinv := lieInvariant_of_isInvariantForm hAd
  exact ⟨B, hinv, hsymm, hpos,
    B.orthogonal_derivedSeries_one_eq_center (B.nondegenerate_of_anisotropic hpos.anisotropic).2
      hinv⟩

/-- The centre and derived ideal of the Lie algebra of a compact finite-dimensional real
smooth Lie group complement one another. -/
theorem isCompl_center_derivedSeries_one_of_compactSpace :
    IsCompl (center ℝ (LeftInvariantDerivation I G))
      (derivedSeries ℝ (LeftInvariantDerivation I G) 1) := by
  obtain ⟨B, hinv, hsymm, hpos, _⟩ :=
    exists_posDef_orthogonal_derivedSeries_one_eq_center_of_compactSpace (I := I) (G := G)
  exact B.isCompl_center_derivedSeries_one_of_anisotropic hsymm.isRefl hpos.anisotropic hinv

/-- The Lie algebra of a compact finite-dimensional real smooth Lie group is perfect exactly when
its centre is trivial. -/
theorem derivedSeries_one_eq_top_iff_center_eq_bot :
    derivedSeries ℝ (LeftInvariantDerivation I G) 1 = ⊤ ↔
      center ℝ (LeftInvariantDerivation I G) = ⊥ := by
  have h := isCompl_center_derivedSeries_one_of_compactSpace (I := I) (G := G)
  refine ⟨fun hd ↦ ?_, fun hc ↦ eq_top_of_bot_isCompl (hc ▸ h)⟩
  have hinf := h.inf_eq_bot
  rwa [hd, inf_top_eq] at hinf

/-- The derived algebra of the Lie algebra of a compact finite-dimensional real smooth
Lie group is semisimple. -/
theorem isSemisimple_derivedSeries_one_of_compactSpace :
    LieAlgebra.IsSemisimple ℝ (derivedSeries ℝ (LeftInvariantDerivation I G) 1) := by
  obtain ⟨B, hinv, hsymm, hpos, _⟩ :=
    exists_posDef_orthogonal_derivedSeries_one_eq_center_of_compactSpace (I := I) (G := G)
  exact B.isSemisimple_derivedSeries_one_of_anisotropic hsymm.isRefl hpos.anisotropic hinv

/-- The radical of the Lie algebra of a compact finite-dimensional real smooth Lie group
is its centre. -/
theorem hasCentralRadical_of_compactSpace :
    LieAlgebra.HasCentralRadical ℝ (LeftInvariantDerivation I G) := by
  obtain ⟨B, hinv, hsymm, hpos, _⟩ :=
    exists_posDef_orthogonal_derivedSeries_one_eq_center_of_compactSpace (I := I) (G := G)
  exact B.hasCentralRadical_of_anisotropic hsymm.isRefl hpos.anisotropic hinv

/-- The Killing form of the Lie algebra of a compact finite-dimensional real smooth Lie
group is nonpositive on the diagonal. -/
theorem _root_.LeftInvariantDerivation.killingForm_self_nonpos
    (X : LeftInvariantDerivation I G) :
    killingForm ℝ (LeftInvariantDerivation I G) X X ≤ 0 := by
  obtain ⟨B, hinv, hsymm, hpos, _⟩ :=
    exists_posDef_orthogonal_derivedSeries_one_eq_center_of_compactSpace (I := I) (G := G)
  exact B.killingForm_self_nonpos_of_posDef hsymm hpos hinv X

/-- The diagonal of the Killing form of the Lie algebra of a compact finite-dimensional
real smooth Lie group vanishes exactly on its centre. -/
@[simp]
theorem _root_.LeftInvariantDerivation.killingForm_self_eq_zero_iff
    (X : LeftInvariantDerivation I G) :
    killingForm ℝ (LeftInvariantDerivation I G) X X = 0 ↔
      X ∈ center ℝ (LeftInvariantDerivation I G) := by
  obtain ⟨B, hinv, hsymm, hpos, _⟩ :=
    exists_posDef_orthogonal_derivedSeries_one_eq_center_of_compactSpace (I := I) (G := G)
  exact B.killingForm_self_eq_zero_iff_of_posDef hsymm hpos hinv X

/-- The Killing form of the derived algebra of the Lie algebra of a compact
finite-dimensional real smooth Lie group is strictly negative at every nonzero vector. -/
theorem killingForm_derivedSeries_one_self_neg_of_compactSpace_of_ne_zero
    (X : derivedSeries ℝ (LeftInvariantDerivation I G) 1) (hX : X ≠ 0) :
    killingForm ℝ (derivedSeries ℝ (LeftInvariantDerivation I G) 1) X X < 0 := by
  obtain ⟨B, hinv, hsymm, hpos, _⟩ :=
    exists_posDef_orthogonal_derivedSeries_one_eq_center_of_compactSpace (I := I) (G := G)
  exact B.killingForm_derivedSeries_one_self_neg_of_posDef_of_ne_zero hsymm hpos hinv X hX

/-- **A non-abelian Lie algebra of a compact Lie group contains `so(3) ≅ 𝔰𝔲(2)`.** If the Lie
algebra of a compact finite-dimensional real smooth Lie group is not abelian, it receives an
injective Lie algebra homomorphism from `so(3)`. -/
theorem exists_injective_lieHom_soThree_of_compactSpace
    (hG : ¬IsLieAbelian (LeftInvariantDerivation I G)) :
    ∃ f : Orthogonal.so (Fin 3) ℝ →ₗ⁅ℝ⁆ LeftInvariantDerivation I G, Function.Injective f := by
  obtain ⟨B, hinv, hsymm, hpos, _⟩ :=
    exists_posDef_orthogonal_derivedSeries_one_eq_center_of_compactSpace (I := I) (G := G)
  exact B.exists_injective_lieHom_soThree hsymm hpos hinv hG

end TauCeti.Lie
