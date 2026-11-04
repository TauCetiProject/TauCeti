/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.Geometry.Manifold.Morse.Deformation

/-!
# Relative homology across a band without critical points

Let `f` be a smooth real function on a boundaryless finite-dimensional manifold `M`, and let
`a ≤ b` be such that the band `f⁻¹[a, b]` is compact and contains no critical point of `f`. The
sublevel `{f ≤ a}` is a strong deformation retract of `{f ≤ b}`
(`TauCeti.exists_sublevelDeformation`), so the relative singular homology of the sublevel pair
`({f ≤ b}, {f ≤ a})` vanishes in every degree, for coefficients in any preadditive category with
coproducts and homology (`TauCeti.isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.1.
-/

public section

noncomputable section

open CategoryTheory Limits Set
open scoped ContDiff Manifold

universe u v w

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ} {a b : ℝ}
  {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C]

/-- **A band without critical points carries no relative homology.** If the band `f⁻¹[a, b]` is
compact and contains no critical point of the smooth function `f`, the relative singular homology
of the sublevel pair `({f ≤ b}, {f ≤ a})` vanishes in every degree. -/
theorem isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) (R : C) (n : ℕ) :
    IsZero ((sublevelPair f hab).singularHomology R n) := by
  obtain ⟨r, -, ⟨G⟩⟩ := exists_sublevelDeformation hf hab hcompact hreg
  have e : sublevelInclusion f a b hab = .inclusion (sublevel_mono f hab) := by ext; simp
  rw [e] at G
  -- The identity of the pair is homotopic to the retraction, which factors through `{f ≤ a}`.
  refine TopPair.isZero_singularHomology_of_homotopy (f := TopPair.ofInclusionMap
      (X := TopCat.of M) (sublevel_mono f hab) (sublevel_mono f hab)
      ((ContinuousMap.inclusion (sublevel_mono f hab)).comp r) fun x _ ↦ (r x).2)
    ?_ (TopCat.ofHom r) (by ext x; exact (TopPair.ofInclusionMap_fst_apply
      (hst := sublevel_mono f hab) (hst' := sublevel_mono f hab) _ _ x).symm) R n
  rw [← TopPair.ofInclusionMap_id]
  refine TopPair.ofInclusionHomotopy G.symm.toHomotopy fun τ x hx ↦ ?_
  have h : G.symm.toHomotopy (τ, x) = x := G.symm.eq_fst τ hx
  rw [h]
  exact hx

end TauCeti
