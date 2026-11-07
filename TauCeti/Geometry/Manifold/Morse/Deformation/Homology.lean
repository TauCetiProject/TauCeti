/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.Triple
public import TauCeti.Geometry.Manifold.Morse.Deformation

/-!
# Relative homology across a band without critical points

Let `f` be a smooth real function on a boundaryless finite-dimensional manifold `M`, and let
`a ≤ b` be such that the band `f⁻¹[a, b]` is compact and contains no critical point of `f`. The
sublevel `{f ≤ a}` is a strong deformation retract of `{f ≤ b}`
(`TauCeti.exists_sublevelDeformation`), so the relative singular homology of the sublevel pair
`({f ≤ b}, {f ≤ a})` vanishes in every degree, for coefficients in any preadditive category with
coproducts and homology (`TauCeti.isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero`).

Consequently, regular collars can be cut off a band. If `a ≤ s ≤ t ≤ b` and the bands
`f⁻¹[a, s]` and `f⁻¹[t, b]` are compact and free of critical points, the long exact sequences of
the triples `{f ≤ a} ⊆ {f ≤ t} ⊆ {f ≤ b}` and `{f ≤ a} ⊆ {f ≤ s} ⊆ {f ≤ t}` identify the relative
homology of `({f ≤ b}, {f ≤ a})` with that of `({f ≤ t}, {f ≤ s})`, for coefficients in an
abelian category with coproducts (`TauCeti.singularHomologySublevelPairIsoOfCollars`). Both
identifications are induced by inclusions of pairs
(`TauCeti.singularHomologyMap_innerToTotal_comp_singularHomologySublevelPairIsoOfCollars_hom`).

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
  exact TopPair.isZero_singularHomology_ofInclusion_of_homotopyRel (X := TopCat.of M)
    (sublevel_mono f hab) r G R n

/-- **Removing regular collars from a band.** If the bands `f⁻¹[a, s]` and `f⁻¹[t, b]` are
compact and contain no critical points, then the relative homology of `({f ≤ b}, {f ≤ a})` is that
of `({f ≤ t}, {f ≤ s})`: both are identified with the relative homology of `({f ≤ t}, {f ≤ a})` by
the long exact sequences of the triples `{f ≤ a} ⊆ {f ≤ t} ⊆ {f ≤ b}` and
`{f ≤ a} ⊆ {f ≤ s} ⊆ {f ≤ t}`. -/
def singularHomologySublevelPairIsoOfCollars (hf : ContMDiff I 𝓘(ℝ) ∞ f) {s t : ℝ}
    (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) (hcompact₁ : IsCompact (f ⁻¹' Icc a s))
    (hcompact₂ : IsCompact (f ⁻¹' Icc t b))
    (hreg₁ : ∀ x, a ≤ f x → f x ≤ s → mfderiv I 𝓘(ℝ) f x ≠ 0)
    (hreg₂ : ∀ x, t ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0)
    {A : Type*} [Category A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ) :
    (sublevelPair f (has.trans (hst.trans htb))).singularHomology R n ≅
      (sublevelPair f hst).singularHomology R n :=
  have h₁ := isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero hf has hcompact₁ hreg₁ R
  have h₂ := isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero hf htb hcompact₂ hreg₂ R
  (@asIso _ _ _ _ _ ((TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f (has.trans hst))
      (sublevel_mono f htb)).isIso_singularHomologyMap_innerToTotal_of_isZero R n (h₂ n)
        (h₂ (n + 1)))).symm ≪≫
    @asIso _ _ _ _ _ ((TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f has)
      (sublevel_mono f hst)).isIso_singularHomologyMap_totalToOuter_of_isZero R n (h₁ n)
        fun m _ ↦ h₁ m)

/-- The identification `TauCeti.singularHomologySublevelPairIsoOfCollars` of
`Hₙ({f ≤ b}, {f ≤ a})` with `Hₙ({f ≤ t}, {f ≤ s})` is induced by inclusions of pairs: precomposed
with the map induced by `({f ≤ t}, {f ≤ a}) ⟶ ({f ≤ b}, {f ≤ a})`, it is the map induced by
`({f ≤ t}, {f ≤ a}) ⟶ ({f ≤ t}, {f ≤ s})`. -/
@[reassoc]
lemma singularHomologyMap_innerToTotal_comp_singularHomologySublevelPairIsoOfCollars_hom
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    (hcompact₁ : IsCompact (f ⁻¹' Icc a s)) (hcompact₂ : IsCompact (f ⁻¹' Icc t b))
    (hreg₁ : ∀ x, a ≤ f x → f x ≤ s → mfderiv I 𝓘(ℝ) f x ≠ 0)
    (hreg₂ : ∀ x, t ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0)
    {A : Type*} [Category A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ) :
    TopPair.singularHomologyMap (TopTriple.innerToTotal.app (TopTriple.ofInclusions
        (X := TopCat.of M) (sublevel_mono f (has.trans hst)) (sublevel_mono f htb))) R n ≫
      (singularHomologySublevelPairIsoOfCollars hf has hst htb hcompact₁ hcompact₂ hreg₁ hreg₂
        R n).hom =
      TopPair.singularHomologyMap (TopTriple.totalToOuter.app (TopTriple.ofInclusions
        (X := TopCat.of M) (sublevel_mono f has) (sublevel_mono f hst))) R n := by
  simp [singularHomologySublevelPairIsoOfCollars]

end TauCeti
