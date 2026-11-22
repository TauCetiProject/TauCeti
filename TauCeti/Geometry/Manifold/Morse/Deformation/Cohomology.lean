/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Cohomology.Triple
public import TauCeti.Geometry.Manifold.Morse.Deformation.Homology

/-!
# Relative cohomology of bands with regular collars

Let `f` be a smooth real function on a boundaryless finite-dimensional manifold `M`, and let
`a ≤ b` be such that the band `f⁻¹[a, b]` is compact and contains no critical point of `f`. The
sublevel `{f ≤ a}` is a strong deformation retract of `{f ≤ b}`
(`TauCeti.exists_sublevelDeformation`), so the relative singular cohomology of the sublevel pair
`({f ≤ b}, {f ≤ a})` vanishes in every degree, with arbitrary coefficients
(`TauCeti.isZero_singularCohomology_sublevelPair_of_mfderiv_ne_zero`).

Consequently, regular collars can be cut off a band. If `a ≤ s ≤ t ≤ b` and the bands
`f⁻¹[a, s]` and `f⁻¹[t, b]` are compact and free of critical points, the long exact sequences of
the triples `{f ≤ a} ⊆ {f ≤ t} ⊆ {f ≤ b}` and `{f ≤ a} ⊆ {f ≤ s} ⊆ {f ≤ t}` identify the relative
cohomology of `({f ≤ b}, {f ≤ a})` with that of `({f ≤ t}, {f ≤ s})`, both by restriction to
`({f ≤ t}, {f ≤ a})` (`TauCeti.singularCohomologySublevelPairIsoOfCollars`,
`TauCeti.singularCohomologySublevelPairIsoOfCollars_hom_comp_singularCohomologyMap_totalToOuter`).
In particular a compact band `f⁻¹[a, b]` around an isolated critical value `c` can be narrowed to
any `f⁻¹[c - ε, c + ε]` inside it (`TauCeti.singularCohomologySublevelPairIsoSymmetricBand`), which
is where the relative cohomology across a critical level is computed, for instance from the
attachment of the negative disc bundles of Morse–Bott critical submanifolds. These are the
cohomology forms of `TauCeti.isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero`,
`TauCeti.singularHomologySublevelPairIsoOfCollars` and
`TauCeti.singularHomologySublevelPairIsoSymmetricBand`.

## Main results

* `TauCeti.isZero_singularCohomology_sublevelPair_of_mfderiv_ne_zero`: a compact band without
  critical points carries no relative cohomology.
* `TauCeti.singularCohomologySublevelPairIsoOfCollars`: regular collars can be cut off a band
  without changing the relative cohomology of the sublevel pair.
* `TauCeti.singularCohomologySublevelPairIsoSymmetricBand`: in particular a compact band around an
  isolated critical value `c` can be narrowed to any `f⁻¹[c - ε, c + ε]` inside it.
-/

public section

noncomputable section

open CategoryTheory Limits Set
open scoped ContDiff Manifold

universe u v w

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ} {a b s t : ℝ}
  {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Abelian C] (R : C) (k : Type*) [Ring k]
  [Linear k C] (N : C)

/-- **A band without critical points carries no relative cohomology.** If the band `f⁻¹[a, b]` is
compact and contains no critical point of the smooth function `f`, the relative singular
cohomology of the sublevel pair `({f ≤ b}, {f ≤ a})` vanishes in every degree, with arbitrary
coefficients. This is the cohomology form of
`TauCeti.isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero`. -/
theorem isZero_singularCohomology_sublevelPair_of_mfderiv_ne_zero (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) (n : ℕ) :
    IsZero ((sublevelPair f hab).singularCohomology R k N n) := by
  obtain ⟨r, -, ⟨G⟩⟩ := exists_sublevelDeformation hf hab hcompact hreg
  have e : sublevelInclusion f a b hab = .inclusion (sublevel_mono f hab) := by ext; simp
  rw [e] at G
  exact TopPair.isZero_singularCohomology_ofInclusion_of_homotopyRel (X := TopCat.of M)
    (sublevel_mono f hab) r G R k N n

/-- **Removing regular collars from a band, in cohomology.** If the bands `f⁻¹[a, s]` and
`f⁻¹[t, b]` are compact and contain no critical points, then the relative cohomology of
`({f ≤ b}, {f ≤ a})` is that of `({f ≤ t}, {f ≤ s})`, with arbitrary coefficients: both are
identified with the relative cohomology of `({f ≤ t}, {f ≤ a})` by restriction, through the long
exact sequences of the triples `{f ≤ a} ⊆ {f ≤ t} ⊆ {f ≤ b}` and `{f ≤ a} ⊆ {f ≤ s} ⊆ {f ≤ t}`.
This is the cohomology form of `TauCeti.singularHomologySublevelPairIsoOfCollars`. -/
def singularCohomologySublevelPairIsoOfCollars (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) (hcompact₁ : IsCompact (f ⁻¹' Icc a s))
    (hcompact₂ : IsCompact (f ⁻¹' Icc t b))
    (hreg₁ : ∀ x, a ≤ f x → f x ≤ s → mfderiv I 𝓘(ℝ) f x ≠ 0)
    (hreg₂ : ∀ x, t ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) (n : ℕ) :
    (sublevelPair f (has.trans (hst.trans htb))).singularCohomology R k N n ≅
      (sublevelPair f hst).singularCohomology R k N n :=
  have h₁ :=
    isZero_singularCohomology_sublevelPair_of_mfderiv_ne_zero R k N hf has hcompact₁ hreg₁
  have h₂ :=
    isZero_singularCohomology_sublevelPair_of_mfderiv_ne_zero R k N hf htb hcompact₂ hreg₂
  @asIso _ _ _ _ _ ((TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f (has.trans hst))
      (sublevel_mono f htb)).isIso_singularCohomologyMap_innerToTotal_of_isZero R k N n (h₂ n)
        (h₂ (n + 1))) ≪≫
    (@asIso _ _ _ _ _ ((TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f has)
      (sublevel_mono f hst)).isIso_singularCohomologyMap_totalToOuter_of_isZero R k N n (h₁ n)
        fun m _ ↦ h₁ m)).symm

/-- The identification `TauCeti.singularCohomologySublevelPairIsoOfCollars` of
`Hⁿ({f ≤ b}, {f ≤ a})` with `Hⁿ({f ≤ t}, {f ≤ s})` is induced by inclusions of pairs: followed by
the restriction along `({f ≤ t}, {f ≤ a}) ⟶ ({f ≤ t}, {f ≤ s})`, it is the restriction along
`({f ≤ t}, {f ≤ a}) ⟶ ({f ≤ b}, {f ≤ a})`. -/
@[reassoc]
lemma singularCohomologySublevelPairIsoOfCollars_hom_comp_singularCohomologyMap_totalToOuter
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    (hcompact₁ : IsCompact (f ⁻¹' Icc a s)) (hcompact₂ : IsCompact (f ⁻¹' Icc t b))
    (hreg₁ : ∀ x, a ≤ f x → f x ≤ s → mfderiv I 𝓘(ℝ) f x ≠ 0)
    (hreg₂ : ∀ x, t ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) (n : ℕ) :
    (singularCohomologySublevelPairIsoOfCollars R k N hf has hst htb hcompact₁ hcompact₂ hreg₁
        hreg₂ n).hom ≫
      TopPair.singularCohomologyMap (R := R) (k := k) (M := N) (TopTriple.totalToOuter.app
        (TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f has) (sublevel_mono f hst)))
        n =
      TopPair.singularCohomologyMap (R := R) (k := k) (M := N) (TopTriple.innerToTotal.app
        (TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f (has.trans hst))
          (sublevel_mono f htb))) n := by
  simp [singularCohomologySublevelPairIsoOfCollars]

/-- **Narrowing a band around an isolated critical value, in cohomology.** Let `a < c < b`, with
the band `f⁻¹[a, b]` compact and every critical point of `f` in it on the level `c`. For
`0 < ε ≤ min (c - a) (b - c)`, `Hⁿ({f ≤ b}, {f ≤ a})` is identified with
`Hⁿ({f ≤ c + ε}, {f ≤ c - ε})` by cutting off the regular collars `f⁻¹[a, c - ε]` and
`f⁻¹[c + ε, b]` (`TauCeti.singularCohomologySublevelPairIsoSymmetricBand_def`). This is the
cohomology form of `TauCeti.singularHomologySublevelPairIsoSymmetricBand`. -/
def singularCohomologySublevelPairIsoSymmetricBand (hf : ContMDiff I 𝓘(ℝ) ∞ f) {c ε : ℝ}
    (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c)
    (hε : 0 < ε) (hεδ : ε ≤ min (c - a) (b - c)) (n : ℕ) :
    (sublevelPair f (hac.trans hcb).le).singularCohomology R k N n ≅
      (sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularCohomology R k N n :=
  have ha : a ≤ c - ε := by linarith [hεδ.trans (min_le_left _ _)]
  have hb : c + ε ≤ b := by linarith [hεδ.trans (min_le_right _ _)]
  -- The collars below `c - ε` and above `c + ε` are compact and hold no critical point.
  have hsub {a₁ b₁ : ℝ} (ha₁ : a ≤ a₁) (hb₁ : b₁ ≤ b) : IsCompact (f ⁻¹' Icc a₁ b₁) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.continuous)
      (preimage_mono (Icc_subset_Icc ha₁ hb₁))
  have hreg {a₁ b₁ : ℝ} (ha₁ : a ≤ a₁) (hb₁ : b₁ ≤ b) (hc : c ∉ Icc a₁ b₁) :
      ∀ x, a₁ ≤ f x → f x ≤ b₁ → mfderiv I 𝓘(ℝ) f x ≠ 0 := fun x h₁ h₂ h₀ ↦ hc <| by
    rw [← hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 h₀) ⟨ha₁.trans h₁, h₂.trans hb₁⟩]
    exact ⟨h₁, h₂⟩
  singularCohomologySublevelPairIsoOfCollars R k N hf ha (by linarith) hb
    (hsub le_rfl (by linarith)) (hsub (by linarith) le_rfl)
    (hreg le_rfl (by linarith) fun h ↦ by linarith [h.2])
    (hreg (by linarith) le_rfl fun h ↦ by linarith [h.1]) n

/-- The narrowed-band identification `TauCeti.singularCohomologySublevelPairIsoSymmetricBand`
cuts off the regular collars `f⁻¹[a, c - ε]` and `f⁻¹[c + ε, b]` by
`TauCeti.singularCohomologySublevelPairIsoOfCollars`, so its compatibility lemma
`TauCeti.singularCohomologySublevelPairIsoOfCollars_hom_comp_singularCohomologyMap_totalToOuter`
applies. -/
lemma singularCohomologySublevelPairIsoSymmetricBand_def (hf : ContMDiff I 𝓘(ℝ) ∞ f) {c ε : ℝ}
    (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c)
    (hε : 0 < ε) (hεδ : ε ≤ min (c - a) (b - c)) (n : ℕ)
    (ha : a ≤ c - ε) (hb : c + ε ≤ b) (hcompact₁ : IsCompact (f ⁻¹' Icc a (c - ε)))
    (hcompact₂ : IsCompact (f ⁻¹' Icc (c + ε) b))
    (hreg₁ : ∀ x, a ≤ f x → f x ≤ c - ε → mfderiv I 𝓘(ℝ) f x ≠ 0)
    (hreg₂ : ∀ x, c + ε ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) :
    singularCohomologySublevelPairIsoSymmetricBand R k N hf hac hcb hcompact hcrit hε hεδ n =
      singularCohomologySublevelPairIsoOfCollars R k N hf ha (by linarith) hb hcompact₁ hcompact₂
        hreg₁ hreg₂ n :=
  (rfl)

end TauCeti
