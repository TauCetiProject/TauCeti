/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Excision
public import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Cohomology.Triple
public import TauCeti.Geometry.Manifold.Morse.Deformation.Homology

/-!
# Relative cohomology of bands: without critical points, and above a regular level

Let `f` be a smooth real function on a boundaryless finite-dimensional manifold `M`, and let
`a ≤ b` be such that the band `f⁻¹[a, b]` is compact and contains no critical point of `f`. The
sublevel `{f ≤ a}` is a strong deformation retract of `{f ≤ b}`
(`TauCeti.exists_sublevelDeformation`), so the relative singular cohomology of the sublevel pair
`({f ≤ b}, {f ≤ a})` vanishes in every degree, with arbitrary coefficients
(`TauCeti.isZero_singularCohomology_sublevelPair_of_mfderiv_ne_zero`), and the inclusion
`{f ≤ a} ⊆ {f ≤ b}` induces isomorphisms on singular cohomology
(`TauCeti.isIso_singularCohomologyMap_map_sublevelPair_of_mfderiv_ne_zero`).

Above a regular value `a`, the inclusion of pairs `(f⁻¹[a, b], f⁻¹(a)) ⟶ ({f ≤ b}, {f ≤ a})`
induces isomorphisms on relative singular cohomology in every degree
(`TauCeti.isIso_singularCohomologyMap_bandPairInclusion`).

Consequently, regular collars can be cut off a band. If `a ≤ s ≤ t ≤ b` and the bands
`f⁻¹[a, s]` and `f⁻¹[t, b]` are compact and free of critical points, the long exact sequences of
the triples `{f ≤ a} ⊆ {f ≤ t} ⊆ {f ≤ b}` and `{f ≤ a} ⊆ {f ≤ s} ⊆ {f ≤ t}` identify the relative
cohomology of `({f ≤ b}, {f ≤ a})` with that of `({f ≤ t}, {f ≤ s})`, both by restriction to
`({f ≤ t}, {f ≤ a})` (`TauCeti.singularCohomologySublevelPairIsoOfCollars`,
`TauCeti.singularCohomologySublevelPairIsoOfCollars_hom_comp_singularCohomologyMap_totalToOuter`,
`TauCeti.singularCohomologySublevelPairIsoOfCollars_hom_comp_singularCohomologyMap`).
In particular a compact band `f⁻¹[a, b]` around an isolated critical value `c` can be narrowed to
any `f⁻¹[c - ε, c + ε]` inside it (`TauCeti.singularCohomologySublevelPairIsoSymmetricBand`), and
the relative cohomology of a compact band around an isolated critical value depends only on the
critical value (`TauCeti.singularCohomologySublevelPairIsoOfCriticalValue`). These are the
cohomology forms of `TauCeti.isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero`,
`TauCeti.singularHomologySublevelPairIsoOfCollars`,
`TauCeti.singularHomologySublevelPairIsoOfCriticalValue`, and
`TauCeti.singularHomologySublevelPairIsoSymmetricBand`.

## Main results

* `TauCeti.isZero_singularCohomology_sublevelPair_of_mfderiv_ne_zero`: a compact band without
  critical points carries no relative cohomology.
* `TauCeti.isZero_singularCohomology_sublevelPair_of_isEmpty`: in particular, if all critical
  points in a compact band lie in the image of an empty type, the relative cohomology vanishes.
* `TauCeti.isIso_singularCohomologyMap_map_sublevelPair_of_mfderiv_ne_zero`: so the inclusion of
  the lower sublevel into the upper one induces isomorphisms on cohomology.
* `TauCeti.isIso_singularCohomologyMap_bandPairInclusion`: above a regular value, a compact band
  relative to its lower level has the relative cohomology of the sublevel pair.
* `TauCeti.singularCohomologySublevelPairIsoOfCollars`: regular collars can be cut off a band
  without changing the relative cohomology of the sublevel pair, and the inclusion across regular
  collars induces an isomorphism
  (`TauCeti.isIso_singularCohomologyMap_sublevelPair_of_collar`).
* `TauCeti.singularCohomologySublevelPairIsoOfCriticalValue`: the relative cohomology of a compact
  band around an isolated critical value does not depend on the band; the identification is
  induced by inclusions of pairs
  (`TauCeti.singularCohomologySublevelPairIsoOfCriticalValue_hom_comp_singularCohomologyMap`) and
  satisfies identity, symmetry, and composition coherence laws
  (`TauCeti.singularCohomologySublevelPairIsoOfCriticalValue_self`,
  `TauCeti.singularCohomologySublevelPairIsoOfCriticalValue_symm`,
  `TauCeti.singularCohomologySublevelPairIsoOfCriticalValue_trans`).
* `TauCeti.isIso_singularCohomologyMap_ofInclusionMap_sublevelPair_iff`: an inclusion of pairs
  `(K, L) ⟶ ({f ≤ b}, {f ≤ a})` is an isomorphism on relative cohomology exactly when it is one
  after cutting off regular collars of the band.
* `TauCeti.singularCohomologySublevelPairIsoSymmetricBand`: in particular a compact band around an
  isolated critical value `c` can be narrowed to any `f⁻¹[c - ε, c + ε]` inside it.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.1.
* J. Milnor, *Lectures on the h-cobordism theorem*, Princeton University Press, 1965, §3.
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
  {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Abelian C]

section

variable {s t : ℝ} (R : C) (k : Type*) [Ring k] [Linear k C] (N : C)

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

/-- **A band whose critical points lie in the image of an empty type carries no relative
cohomology.** If `a ≤ b`, the band `f⁻¹[a, b]` of a smooth function `f` is compact and all its
critical points lie in the range of a map `i : S → M` from an empty type `S`, then the band has no
critical points, so `Hⁿ({f ≤ b}, {f ≤ a})` vanishes in every degree, with arbitrary coefficients. -/
theorem isZero_singularCohomology_sublevelPair_of_isEmpty {S : Type*} [IsEmpty S] {i : S → M}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i) (n : ℕ) :
    IsZero ((sublevelPair f hab).singularCohomology R k N n) :=
  isZero_singularCohomology_sublevelPair_of_mfderiv_ne_zero R k N hf hab hcompact
    (mfderiv_ne_zero_of_isEmpty hcrit) n

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
  singularCohomologySublevelPairIsoOfCollars R k N hf ha (by linarith) hb
    (isCompact_preimage_Icc_of_subset hf.continuous hcompact le_rfl (by linarith))
    (isCompact_preimage_Icc_of_subset hf.continuous hcompact (by linarith) le_rfl)
    (mfderiv_ne_zero_of_notMem_Icc hcrit le_rfl (by linarith) fun h ↦ by linarith [h.2])
    (mfderiv_ne_zero_of_notMem_Icc hcrit (by linarith) le_rfl fun h ↦ by linarith [h.1]) n

/-- The narrowed-band identification `TauCeti.singularCohomologySublevelPairIsoSymmetricBand`
cuts off the regular collars `f⁻¹[a, c - ε]` and `f⁻¹[c + ε, b]` by
`TauCeti.singularCohomologySublevelPairIsoOfCollars`, so its compatibility lemma
`TauCeti.singularCohomologySublevelPairIsoOfCollars_hom_comp_singularCohomologyMap_totalToOuter`
applies. -/
lemma singularCohomologySublevelPairIsoSymmetricBand_def (hf : ContMDiff I 𝓘(ℝ) ∞ f) {c ε : ℝ}
    (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c)
    (hε : 0 < ε) (hεδ : ε ≤ min (c - a) (b - c)) (n : ℕ) :
    singularCohomologySublevelPairIsoSymmetricBand R k N hf hac hcb hcompact hcrit hε hεδ n =
      singularCohomologySublevelPairIsoOfCollars R k N hf (le_sub_comm.1 (hεδ.trans
          (min_le_left _ _))) (by linarith) (le_sub_iff_add_le'.1 (hεδ.trans (min_le_right _ _)))
        (isCompact_preimage_Icc_of_subset hf.continuous hcompact le_rfl (by linarith))
        (isCompact_preimage_Icc_of_subset hf.continuous hcompact (by linarith) le_rfl)
        (mfderiv_ne_zero_of_notMem_Icc hcrit le_rfl (by linarith) fun h ↦ by linarith [h.2])
        (mfderiv_ne_zero_of_notMem_Icc hcrit (by linarith) le_rfl fun h ↦ by linarith [h.1]) n :=
  (rfl)

end

/-- **Crossing a band without critical points does not change cohomology.** If the band
`f⁻¹[a, b]` is compact and contains no critical point of the smooth function `f`, the inclusion of
`{f ≤ a}` into `{f ≤ b}` induces isomorphisms on singular cohomology in every degree. -/
theorem isIso_singularCohomologyMap_map_sublevelPair_of_mfderiv_ne_zero
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) (R : C)
    (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ) :
    IsIso (TopCat.singularCohomologyMap (R := R) (k := k) (M := N) (sublevelPair f hab).map n) := by
  obtain ⟨e, he⟩ := exists_sublevelHomotopyEquiv hf hab hcompact hreg
  have h : (sublevelPair f hab).map = TopCat.ofHom e.toFun := by
    ext x
    exact Subtype.ext (he x).symm
  rw [h]
  exact e.isIso_singularCohomologyMap R k N n

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- A collar `f⁻¹[a, a']` which the flow `φ` crosses at unit speed carries no cohomology relative
to its lower level `f⁻¹(a)`: following the flow down to the level `a` is a strong deformation
retraction. -/
private theorem isZero_singularCohomology_collar {a' : ℝ} (hf : Continuous f) (φ : Flow ℝ M)
    (hφf : ∀ x t, 0 ≤ t → a ≤ f x - t → f x ≤ a' → f (φ t x) = f x - t)
    (hLN : f ⁻¹' {a} ⊆ f ⁻¹' Icc a a') (R : C) (k : Type*) [Ring k] [Linear k C] (N : C)
    (n : ℕ) :
    IsZero ((TopPair.ofInclusion (X := TopCat.of M) hLN).singularCohomology R k N n) := by
  obtain ⟨r, ⟨G⟩⟩ := exists_collarDeformation hf φ hφf hLN
  exact TopPair.isZero_singularCohomology_ofInclusion_of_homotopyRel hLN r G R k N n

/-- **The relative cohomology of a band over a regular level** (Milnor, *Lectures on the
h-cobordism theorem*, §3). If `a ≤ b`, the band `f⁻¹[a, b]` is compact and `a` is a regular value
of the smooth function `f`, then the inclusion of pairs `(f⁻¹[a, b], f⁻¹(a)) ⟶ ({f ≤ b}, {f ≤ a})`
induces isomorphisms on relative singular cohomology in every degree. The band may contain critical
points, and `b` need not be a regular value. -/
theorem isIso_singularCohomologyMap_bandPairInclusion (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a) (R : C)
    (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := N)
      (bandPairInclusion f hab) n) := by
  have hfc : Continuous f := hf.continuous
  -- A collar `f⁻¹[a, a']` without critical points, with `a < a'` unless the band is a level.
  obtain ⟨a', ⟨haa', ha'b⟩, hlt, hcollar, hreg⟩ :=
    exists_mem_Icc_isCompact_forall_mfderiv_ne_zero (hf.of_le (by simp)) hab hcompact ha
  -- Enlarge `{f ≤ a}` to `{f ≤ a'}` in the sublevel pair.
  let T₁ :=
    TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f haa') (sublevel_mono f ha'b)
  let ψ₁ : sublevelPair f hab ⟶ TopPair.ofInclusion (X := TopCat.of M) (sublevel_mono f ha'b) :=
    TopTriple.totalToOuter.app T₁
  have h₁ : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := N) ψ₁ n) :=
    T₁.isIso_singularCohomologyMap_totalToOuter_of_isZero R k N n
      (isZero_singularCohomology_sublevelPair_of_mfderiv_ne_zero R k N hf haa' hcollar hreg n)
      fun m _ ↦
        isZero_singularCohomology_sublevelPair_of_mfderiv_ne_zero R k N hf haa' hcollar hreg m
  -- Enlarge `f⁻¹(a)` to the collar `f⁻¹[a, a']` in the band pair.
  have hLN : f ⁻¹' {a} ⊆ f ⁻¹' Icc a a' :=
    preimage_mono (singleton_subset_iff.2 ⟨le_rfl, haa'⟩)
  have hNW : f ⁻¹' Icc a a' ⊆ f ⁻¹' Icc a b := preimage_mono (Icc_subset_Icc_right ha'b)
  obtain ⟨φ, -, -, -, hφf⟩ := exists_flow_apply_eq_sub hf hcollar hreg
  let T₂ := TopTriple.ofInclusions (X := TopCat.of M) hLN hNW
  let ψ₂ : bandPair f hab ⟶ TopPair.ofInclusion (X := TopCat.of M) hNW :=
    TopTriple.totalToOuter.app T₂
  have h₂ : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := N) ψ₂ n) :=
    T₂.isIso_singularCohomologyMap_totalToOuter_of_isZero R k N n
      (isZero_singularCohomology_collar hfc φ hφf hLN R k N n)
      fun m _ ↦ isZero_singularCohomology_collar hfc φ hφf hLN R k N m
  -- Excise `{f < a}` from `({f ≤ b}, {f ≤ a'})`.
  have h₃ : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := N)
      (bandCollarPairInclusion f a ha'b) n) :=
    TopPair.isIso_singularCohomologyMap_bandCollarPairInclusion (R := R) (k := k) (M := N)
      hfc ha'b hlt n
  -- The two composites `(f⁻¹[a, b], f⁻¹(a)) ⟶ ({f ≤ b}, {f ≤ a'})` agree.
  have hsq : bandPairInclusion f hab ≫ ψ₁ = ψ₂ ≫ bandCollarPairInclusion f a ha'b :=
    bandPairInclusion_comp_totalToOuter f haa' ha'b
  have h₁₂ : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := N) ψ₁ n ≫
      TopPair.singularCohomologyMap (R := R) (k := k) (M := N) (bandPairInclusion f hab) n) := by
    rw [← TopPair.singularCohomologyMap_comp, hsq, TopPair.singularCohomologyMap_comp]
    exact IsIso.comp_isIso' h₃ h₂
  exact IsIso.of_isIso_comp_left
    (TopPair.singularCohomologyMap (R := R) (k := k) (M := N) ψ₁ n) _

/-- Restrict a compact band `[s, t]` around an isolated critical value `c` to a subband `[u, v]`
around `c`. -/
private def singularCohomologySublevelPairIsoSubBand (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {c s t u v : ℝ} (hsc : s < c) (hct : c < t) (hsu : s ≤ u) (huc : u < c) (hcv : c < v)
    (hvt : v ≤ t) (hcompact : IsCompact (f ⁻¹' Icc s t))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc s t → f x = c)
    (R : C) (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ) :
    (sublevelPair f (hsc.trans hct).le).singularCohomology R k N n ≅
      (sublevelPair f (huc.trans hcv).le).singularCohomology R k N n :=
  have hfc := hf.continuous
  singularCohomologySublevelPairIsoOfCollars R k N hf hsu (huc.trans hcv).le hvt
    (isCompact_preimage_Icc_of_subset hfc hcompact le_rfl (huc.trans hct).le)
    (isCompact_preimage_Icc_of_subset hfc hcompact (hsc.trans hcv).le le_rfl)
    (mfderiv_ne_zero_of_notMem_Icc hcrit le_rfl (huc.trans hct).le fun h ↦ huc.not_ge h.2)
    (mfderiv_ne_zero_of_notMem_Icc hcrit (hsc.trans hcv).le le_rfl fun h ↦ hcv.not_ge h.1) n

/-- **The relative cohomology of an isolated critical value.** Let `f⁻¹[s, t]` and `f⁻¹[s', t']` be
compact bands with `s, s' < c < t, t'`, in each of which every critical point of `f` lies on the
level `c`. Then `Hⁿ({f ≤ t}, {f ≤ s})` and `Hⁿ({f ≤ t'}, {f ≤ s'})` are isomorphic: cutting off
the regular collars identifies both with `Hⁿ({f ≤ min t t'}, {f ≤ max s s'})`
(`TauCeti.singularCohomologySublevelPairIsoOfCollars`). So the relative cohomology of a band
around an isolated critical value depends only on the value; for a symmetric subband this agrees
with `TauCeti.singularCohomologySublevelPairIsoSymmetricBand`
(`TauCeti.singularCohomologySublevelPairIsoSymmetricBand_eq_ofCriticalValue`). -/
def singularCohomologySublevelPairIsoOfCriticalValue (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {c s t s' t' : ℝ} (hsc : s < c) (hct : c < t) (hs'c : s' < c) (hct' : c < t')
    (hcompact : IsCompact (f ⁻¹' Icc s t)) (hcompact' : IsCompact (f ⁻¹' Icc s' t'))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc s t → f x = c)
    (hcrit' : ∀ x ∈ criticalPoints I f, f x ∈ Icc s' t' → f x = c)
    (R : C) (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ) :
    (sublevelPair f (hsc.trans hct).le).singularCohomology R k N n ≅
      (sublevelPair f (hs'c.trans hct').le).singularCohomology R k N n :=
  have hu : max s s' < c := max_lt hsc hs'c
  have hv : c < min t t' := lt_min hct hct'
  singularCohomologySublevelPairIsoSubBand hf hsc hct (le_max_left s s') hu hv (min_le_left t t')
      hcompact hcrit R k N n ≪≫
    (singularCohomologySublevelPairIsoSubBand hf hs'c hct' (le_max_right s s') hu hv
      (min_le_right t t') hcompact' hcrit' R k N n).symm

/-- When the inner band coincides with the outer band, `singularCohomologySublevelPairIsoSubBand`
is the identity isomorphism. -/
private lemma singularCohomologySublevelPairIsoSubBand_refl (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {c s t u v : ℝ} (hsc : s < c) (hct : c < t) (hsu : s ≤ u) (huc : u < c) (hcv : c < v)
    (hvt : v ≤ t) (hus : u = s) (hvt' : v = t) (hcompact : IsCompact (f ⁻¹' Icc s t))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc s t → f x = c)
    (R : C) (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ) :
    (singularCohomologySublevelPairIsoSubBand hf hsc hct hsu huc hcv hvt hcompact hcrit
      R k N n).hom = eqToHom (by subst hus hvt'; rfl) := by
  subst hus hvt'
  have hfc := hf.continuous
  have h := singularCohomologySublevelPairIsoOfCollars_hom_comp_singularCohomologyMap_totalToOuter
    R k N hf hsu (huc.trans hcv).le hvt
    (isCompact_preimage_Icc_of_subset hfc hcompact le_rfl (huc.trans hct).le)
    (isCompact_preimage_Icc_of_subset hfc hcompact (hsc.trans hcv).le le_rfl)
    (mfderiv_ne_zero_of_notMem_Icc hcrit le_rfl (huc.trans hct).le fun h ↦ huc.not_ge h.2)
    (mfderiv_ne_zero_of_notMem_Icc hcrit (hsc.trans hcv).le le_rfl fun h ↦ hcv.not_ge h.1) n
  have h1 : TopTriple.totalToOuter.app (TopTriple.ofInclusions (X := TopCat.of M)
      (sublevel_mono f hsu) (sublevel_mono f (huc.trans hcv).le)) = 𝟙 _ := by
    refine TopPair.hom_ext_of_fst _ ?_
    rw [TopTriple.totalToOuter_app_fst, TopPair.Hom.fst_id]
  have h2 : TopTriple.innerToTotal.app (TopTriple.ofInclusions (X := TopCat.of M)
      (sublevel_mono f (hsu.trans (huc.trans hcv).le)) (sublevel_mono f hvt)) = 𝟙 _ := by
    refine TopPair.hom_ext_of_fst _ ?_
    rw [TopTriple.innerToTotal_app_fst, TopPair.Hom.fst_id]
    rfl
  have hT₁ : TopPair.singularCohomologyMap (R := R) (k := k) (M := N)
      (TopTriple.totalToOuter.app (TopTriple.ofInclusions (X := TopCat.of M)
        (sublevel_mono f hsu) (sublevel_mono f (huc.trans hcv).le))) n = 𝟙 _ := by
    rw [h1]
    exact TopPair.singularCohomologyMap_id _ _
  have hT₂ : TopPair.singularCohomologyMap (R := R) (k := k) (M := N)
      (TopTriple.innerToTotal.app (TopTriple.ofInclusions (X := TopCat.of M)
        (sublevel_mono f (hsu.trans (huc.trans hcv).le)) (sublevel_mono f hvt))) n = 𝟙 _ := by
    rw [h2]
    exact TopPair.singularCohomologyMap_id _ _
  rw [hT₁, hT₂] at h
  exact (Category.comp_id _).symm.trans h

/-- Replacing the inner endpoints of `singularCohomologySublevelPairIsoSubBand` by equal reals
conjugates the isomorphism by `eqToHom`. -/
private lemma singularCohomologySublevelPairIsoSubBand_hom_eq (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {c s t u v u' v' : ℝ} (hsc : s < c) (hct : c < t)
    (hsu : s ≤ u) (huc : u < c) (hcv : c < v) (hvt : v ≤ t)
    (hsu' : s ≤ u') (hu'c : u' < c) (hcv' : c < v') (hv't : v' ≤ t)
    (hu : u = u') (hv : v = v') (hcompact : IsCompact (f ⁻¹' Icc s t))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc s t → f x = c)
    (R : C) (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ) :
    (singularCohomologySublevelPairIsoSubBand hf hsc hct hsu huc hcv hvt hcompact hcrit
        R k N n).hom ≫
      eqToHom (by subst hu hv; rfl) =
      (singularCohomologySublevelPairIsoSubBand hf hsc hct hsu' hu'c hcv' hv't hcompact hcrit
        R k N n).hom := by
  subst hu hv
  simp

/-- The narrowed-band identification `TauCeti.singularCohomologySublevelPairIsoSymmetricBand`
agrees with `TauCeti.singularCohomologySublevelPairIsoOfCriticalValue` for the bands `f⁻¹[a, b]`
and `f⁻¹[c - ε, c + ε]`, so the naturality lemma
`TauCeti.singularCohomologySublevelPairIsoOfCriticalValue_hom_comp_singularCohomologyMap`
applies to it. -/
lemma singularCohomologySublevelPairIsoSymmetricBand_eq_ofCriticalValue
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {c ε : ℝ} (hac : a < c) (hcb : c < b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c)
    (hε : 0 < ε) (hεδ : ε ≤ min (c - a) (b - c)) (R : C) (k : Type*) [Ring k] [Linear k C]
    (N : C) (n : ℕ) :
    singularCohomologySublevelPairIsoSymmetricBand R k N hf hac hcb hcompact hcrit hε hεδ n =
      singularCohomologySublevelPairIsoOfCriticalValue hf hac hcb (by linarith : c - ε < c)
        (by linarith : c < c + ε) hcompact
        (Icc_subset_and_isCompact_preimage_Icc hf.continuous hcompact hεδ).2 hcrit
        (fun x hx hfx ↦ hcrit x hx
          ((Icc_subset_and_isCompact_preimage_Icc hf.continuous hcompact hεδ).1 hfx))
        R k N n := by
  have ha : a ≤ c - ε := by linarith [hεδ.trans (min_le_left _ _)]
  have hb : c + ε ≤ b := by linarith [hεδ.trans (min_le_right _ _)]
  have hu : max a (c - ε) = c - ε := max_eq_right ha
  have hv : min b (c + ε) = c + ε := min_eq_right hb
  apply Iso.ext
  simp only [singularCohomologySublevelPairIsoSymmetricBand_def,
    singularCohomologySublevelPairIsoOfCriticalValue, Iso.trans_hom, Iso.symm_hom]
  have hR_hom := singularCohomologySublevelPairIsoSubBand_refl hf (by linarith : c - ε < c)
    (by linarith : c < c + ε) (le_max_right a (c - ε)) (max_lt hac (by linarith : c - ε < c))
    (lt_min hcb (by linarith : c < c + ε)) (min_le_right b (c + ε)) hu hv
    (Icc_subset_and_isCompact_preimage_Icc hf.continuous hcompact hεδ).2
    (fun x hx hfx ↦ hcrit x hx
      ((Icc_subset_and_isCompact_preimage_Icc hf.continuous hcompact hεδ).1 hfx)) R k N n
  symm
  rw [Iso.comp_inv_eq, hR_hom]
  exact (singularCohomologySublevelPairIsoSubBand_hom_eq hf hac hcb ha (by linarith : c - ε < c)
    (by linarith : c < c + ε) hb (le_max_left a (c - ε)) (max_lt hac (by linarith : c - ε < c))
    (lt_min hcb (by linarith : c < c + ε)) (min_le_left b (c + ε)) hu.symm hv.symm
    hcompact hcrit R k N n).symm

/-- The identification `TauCeti.singularCohomologySublevelPairIsoOfCollars` of
`Hⁿ({f ≤ b}, {f ≤ a})` with `Hⁿ({f ≤ t}, {f ≤ s})` is compatible with inclusions of pairs: for
subsets `L ⊆ K` of `M` with `K ⊆ {f ≤ t}` and `L ⊆ {f ≤ a}`, followed by the map induced by the
inclusion `(K, L) ⟶ ({f ≤ t}, {f ≤ s})`, it is the map induced by the inclusion
`(K, L) ⟶ ({f ≤ b}, {f ≤ a})`. -/
@[reassoc]
lemma singularCohomologySublevelPairIsoOfCollars_hom_comp_singularCohomologyMap
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    (hcompact₁ : IsCompact (f ⁻¹' Icc a s)) (hcompact₂ : IsCompact (f ⁻¹' Icc t b))
    (hreg₁ : ∀ x, a ≤ f x → f x ≤ s → mfderiv I 𝓘(ℝ) f x ≠ 0)
    (hreg₂ : ∀ x, t ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) {K L : Set M} (hLK : L ⊆ K)
    (hK : K ⊆ {x | f x ≤ t}) (hL : L ⊆ {x | f x ≤ a})
    (R : C) (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ) :
    (singularCohomologySublevelPairIsoOfCollars R k N hf has hst htb hcompact₁ hcompact₂ hreg₁
        hreg₂ n).hom ≫
      TopPair.singularCohomologyMap (R := R) (k := k) (M := N) (TopPair.ofInclusionMap
        (X := TopCat.of M) (Y := TopCat.of M) hLK (sublevel_mono f hst)
        (ContinuousMap.inclusion hK) fun _ hx ↦ sublevel_mono f has (hL hx)) n =
      TopPair.singularCohomologyMap (R := R) (k := k) (M := N) (TopPair.ofInclusionMap
        (X := TopCat.of M) (Y := TopCat.of M) hLK (sublevel_mono f (has.trans (hst.trans htb)))
        (ContinuousMap.inclusion (hK.trans (sublevel_mono f htb))) fun _ hx ↦ hL hx) n := by
  let T := TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f (has.trans hst))
    (sublevel_mono f htb)
  let T' := TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f has) (sublevel_mono f hst)
  let m := TopPair.ofInclusionMap (X := TopCat.of M) (Y := TopCat.of M) hLK
    (sublevel_mono f (has.trans hst)) (ContinuousMap.inclusion hK) fun _ hx ↦ hL hx
  have hι : TopPair.ofInclusionMap (X := TopCat.of M) (Y := TopCat.of M) hLK
      (sublevel_mono f (has.trans (hst.trans htb)))
      (ContinuousMap.inclusion (hK.trans (sublevel_mono f htb))) (fun _ hx ↦ hL hx) =
      m ≫ TopTriple.innerToTotal.app T :=
    TopPair.hom_ext_of_fst _ <| by
      ext x
      exact (TopPair.ofInclusionMap_fst_apply _ _ x).trans (congrArg
        (fun y ↦ TopPair.Hom.fst (TopTriple.innerToTotal.app T) y)
        (TopPair.ofInclusionMap_fst_apply (ContinuousMap.inclusion hK) _ x)).symm
  have hj : m ≫ TopTriple.totalToOuter.app T' = TopPair.ofInclusionMap (X := TopCat.of M)
      (Y := TopCat.of M) hLK (sublevel_mono f hst) (ContinuousMap.inclusion hK)
      (fun _ hx ↦ sublevel_mono f has (hL hx)) :=
    TopPair.hom_ext_of_fst _ <| by
      ext x
      exact (congrArg (fun y ↦ TopPair.Hom.fst (TopTriple.totalToOuter.app T') y)
        (TopPair.ofInclusionMap_fst_apply _ _ x)).trans
          (TopPair.ofInclusionMap_fst_apply (ContinuousMap.inclusion hK) _ x).symm
  rw [hι, ← hj]
  exact ((singularCohomologySublevelPairIsoOfCollars R k N hf has hst htb hcompact₁ hcompact₂ hreg₁
      hreg₂ n).hom ≫= TopPair.singularCohomologyMap_comp m _ n).trans <|
    (Category.assoc _ _ _).symm.trans <|
      (singularCohomologySublevelPairIsoOfCollars_hom_comp_singularCohomologyMap_totalToOuter R k N
        hf has hst htb hcompact₁ hcompact₂ hreg₁ hreg₂ n =≫ TopPair.singularCohomologyMap m n).trans
        (TopPair.singularCohomologyMap_comp m _ n).symm

/-- Compatibility of `singularCohomologySublevelPairIsoSubBand` with inclusions from
`({f ≤ v}, {f ≤ l})` for `l ≤ s`. -/
private lemma singularCohomologySublevelPairIsoSubBand_hom_comp (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {c s t u v l : ℝ} (hsc : s < c) (hct : c < t) (hsu : s ≤ u) (huc : u < c) (hcv : c < v)
    (hvt : v ≤ t) (hls : l ≤ s) (hcompact : IsCompact (f ⁻¹' Icc s t))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc s t → f x = c)
    (R : C) (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ) :
    (singularCohomologySublevelPairIsoSubBand hf hsc hct hsu huc hcv hvt hcompact hcrit
      R k N n).hom ≫
      TopPair.singularCohomologyMap (R := R) (k := k) (M := N) (TopPair.ofInclusionMap
        (X := TopCat.of M) (Y := TopCat.of M)
        (sublevel_mono f (hls.trans (hsc.trans hcv).le))
        (sublevel_mono f (huc.trans hcv).le)
        (ContinuousMap.inclusion subset_rfl)
        (fun _ hx ↦ (sublevel_mono f hsu) (sublevel_mono f hls hx))) n =
      TopPair.singularCohomologyMap (R := R) (k := k) (M := N) (TopPair.ofInclusionMap
        (X := TopCat.of M) (Y := TopCat.of M)
        (sublevel_mono f (hls.trans (hsc.trans hcv).le))
        (sublevel_mono f (hsc.trans hct).le)
        (ContinuousMap.inclusion (sublevel_mono f hvt))
        (fun _ hx ↦ sublevel_mono f hls hx)) n :=
  have hfc := hf.continuous
  singularCohomologySublevelPairIsoOfCollars_hom_comp_singularCohomologyMap hf hsu
    (huc.trans hcv).le hvt
    (isCompact_preimage_Icc_of_subset hfc hcompact le_rfl (huc.trans hct).le)
    (isCompact_preimage_Icc_of_subset hfc hcompact (hsc.trans hcv).le le_rfl)
    (mfderiv_ne_zero_of_notMem_Icc hcrit le_rfl (huc.trans hct).le fun h ↦ huc.not_ge h.2)
    (mfderiv_ne_zero_of_notMem_Icc hcrit (hsc.trans hcv).le le_rfl fun h ↦ hcv.not_ge h.1)
    (sublevel_mono f (hls.trans (hsc.trans hcv).le))
    (hK := subset_rfl) (hL := sublevel_mono f hls) R k N n

/-- The identification `TauCeti.singularCohomologySublevelPairIsoOfCriticalValue` of
`Hⁿ({f ≤ t}, {f ≤ s})` with `Hⁿ({f ≤ t'}, {f ≤ s'})` is induced by inclusions of pairs: followed
by the map induced by `({f ≤ min t t'}, {f ≤ min s s'}) ⟶ ({f ≤ t'}, {f ≤ s'})`, it is the map
induced by `({f ≤ min t t'}, {f ≤ min s s'}) ⟶ ({f ≤ t}, {f ≤ s})`. -/
@[reassoc]
lemma singularCohomologySublevelPairIsoOfCriticalValue_hom_comp_singularCohomologyMap
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {c s t s' t' : ℝ} (hsc : s < c) (hct : c < t) (hs'c : s' < c)
    (hct' : c < t') (hcompact : IsCompact (f ⁻¹' Icc s t))
    (hcompact' : IsCompact (f ⁻¹' Icc s' t'))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc s t → f x = c)
    (hcrit' : ∀ x ∈ criticalPoints I f, f x ∈ Icc s' t' → f x = c)
    (R : C) (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ) :
    (singularCohomologySublevelPairIsoOfCriticalValue hf hsc hct hs'c hct' hcompact hcompact'
        hcrit hcrit' R k N n).hom ≫
      TopPair.singularCohomologyMap (R := R) (k := k) (M := N) (TopPair.ofInclusionMap
        (X := TopCat.of M) (Y := TopCat.of M)
        (sublevel_mono f ((min_le_left s s').trans (hsc.trans (lt_min hct hct')).le))
        (sublevel_mono f (hs'c.trans hct').le)
        (ContinuousMap.inclusion (sublevel_mono f (min_le_right t t')))
        fun _ hx ↦ (hx : f _ ≤ min s s').trans (min_le_right s s')) n =
      TopPair.singularCohomologyMap (R := R) (k := k) (M := N) (TopPair.ofInclusionMap
        (X := TopCat.of M) (Y := TopCat.of M)
        (sublevel_mono f ((min_le_left s s').trans (hsc.trans (lt_min hct hct')).le))
        (sublevel_mono f (hsc.trans hct).le)
        (ContinuousMap.inclusion (sublevel_mono f (min_le_left t t')))
        fun _ hx ↦ (hx : f _ ≤ min s s').trans (min_le_left s s')) n := by
  have h1 := singularCohomologySublevelPairIsoSubBand_hom_comp hf hsc hct (le_max_left s s')
    (max_lt hsc hs'c) (lt_min hct hct') (min_le_left t t') (min_le_left s s') hcompact hcrit
    R k N n
  have h2 := singularCohomologySublevelPairIsoSubBand_hom_comp hf hs'c hct' (le_max_right s s')
    (max_lt hsc hs'c) (lt_min hct hct') (min_le_right t t') (min_le_right s s') hcompact' hcrit'
    R k N n
  simp only [singularCohomologySublevelPairIsoOfCriticalValue, Iso.trans_hom, Iso.symm_hom,
    Category.assoc]
  rw [← h2, Iso.inv_hom_id_assoc, h1]

/-- Transporting the relative cohomology of a band around an isolated critical value to itself via
`TauCeti.singularCohomologySublevelPairIsoOfCriticalValue` is the identity isomorphism. -/
@[simp]
lemma singularCohomologySublevelPairIsoOfCriticalValue_self (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {c s t : ℝ} (hsc : s < c) (hct : c < t)
    (hcompact : IsCompact (f ⁻¹' Icc s t)) (hcompact' : IsCompact (f ⁻¹' Icc s t))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc s t → f x = c)
    (hcrit' : ∀ x ∈ criticalPoints I f, f x ∈ Icc s t → f x = c)
    (R : C) (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ) :
    singularCohomologySublevelPairIsoOfCriticalValue hf hsc hct hsc hct hcompact hcompact'
        hcrit hcrit' R k N n = Iso.refl _ :=
  Iso.ext (by simp [singularCohomologySublevelPairIsoOfCriticalValue])

/-- **The inclusion across regular collars induces an isomorphism on relative cohomology.** If
`l ≤ s ≤ v ≤ t` and the bands `f⁻¹[l, s]` and `f⁻¹[v, t]` are compact and contain no critical
point of the smooth function `f`, then the inclusion of pairs
`({f ≤ v}, {f ≤ l}) ⟶ ({f ≤ t}, {f ≤ s})` induces isomorphisms on relative singular cohomology in
every degree. This is the cohomology form of
`TauCeti.isIso_singularHomologyMap_sublevelPair_of_collar`. -/
theorem isIso_singularCohomologyMap_sublevelPair_of_collar (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {l s v t : ℝ} (hls : l ≤ s) (hsv : s ≤ v) (hvt : v ≤ t)
    (hcompact₁ : IsCompact (f ⁻¹' Icc l s)) (hcompact₂ : IsCompact (f ⁻¹' Icc v t))
    (hreg₁ : ∀ x, l ≤ f x → f x ≤ s → mfderiv I 𝓘(ℝ) f x ≠ 0)
    (hreg₂ : ∀ x, v ≤ f x → f x ≤ t → mfderiv I 𝓘(ℝ) f x ≠ 0)
    (R : C) (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := N) (TopPair.ofInclusionMap
      (X := TopCat.of M) (Y := TopCat.of M)
      (sublevel_mono f (hls.trans hsv)) (sublevel_mono f (hsv.trans hvt))
      (ContinuousMap.inclusion (sublevel_mono f hvt))
      (fun _ hx ↦ sublevel_mono f hls hx)) n) := by
  let T₁ := TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f (hls.trans hsv))
    (sublevel_mono f hvt)
  let T₂ := TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f hls)
    (sublevel_mono f (hsv.trans hvt))
  let m₁ : TopPair.ofInclusion (X := TopCat.of M) (sublevel_mono f (hls.trans hsv)) ⟶
      TopPair.ofInclusion (X := TopCat.of M) (sublevel_mono f (hls.trans (hsv.trans hvt))) :=
    TopTriple.innerToTotal.app T₁
  let m₂ : TopPair.ofInclusion (X := TopCat.of M)
      (sublevel_mono f (hls.trans (hsv.trans hvt))) ⟶
      TopPair.ofInclusion (X := TopCat.of M) (sublevel_mono f (hsv.trans hvt)) :=
    TopTriple.totalToOuter.app T₂
  have h₁ : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := N) m₁ n) :=
    T₁.isIso_singularCohomologyMap_innerToTotal_of_isZero R k N n
      (isZero_singularCohomology_sublevelPair_of_mfderiv_ne_zero R k N hf hvt hcompact₂ hreg₂ n)
      (isZero_singularCohomology_sublevelPair_of_mfderiv_ne_zero R k N hf hvt hcompact₂ hreg₂
        (n + 1))
  have h₂ : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := N) m₂ n) :=
    T₂.isIso_singularCohomologyMap_totalToOuter_of_isZero R k N n
      (isZero_singularCohomology_sublevelPair_of_mfderiv_ne_zero R k N hf hls hcompact₁ hreg₁ n)
      fun m _ ↦
        isZero_singularCohomology_sublevelPair_of_mfderiv_ne_zero R k N hf hls hcompact₁ hreg₁ m
  have hfac : TopPair.ofInclusionMap (X := TopCat.of M) (Y := TopCat.of M)
      (sublevel_mono f (hls.trans hsv)) (sublevel_mono f (hsv.trans hvt))
      (ContinuousMap.inclusion (sublevel_mono f hvt)) (fun _ hx ↦ sublevel_mono f hls hx) =
      m₁ ≫ m₂ := by
    refine TopPair.hom_ext_of_fst _ <| by
      ext x
      apply Subtype.ext
      refine (congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply
        (ContinuousMap.inclusion (sublevel_mono f hvt)) _ x)).trans ?_
      refine (congrArg (fun g ↦ (g x).val)
        (TopTriple.innerToTotal_app_fst (T := T₁))).symm.trans ?_
      exact (congrArg (fun g ↦ (g (TopPair.Hom.fst m₁ x)).val)
        (TopTriple.totalToOuter_app_fst (T := T₂))).symm
  rw [hfac, TopPair.singularCohomologyMap_comp]
  exact IsIso.comp_isIso' h₂ h₁

private lemma singularCohomologySublevelPairIsoOfCriticalValue_hom_comp_inclusion
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {c s t s' t' l v : ℝ} (hsc : s < c) (hct : c < t)
    (hs'c : s' < c) (hct' : c < t') (hls : l ≤ min s s') (hvt : v ≤ min t t') (hlv : l ≤ v)
    (hcompact : IsCompact (f ⁻¹' Icc s t)) (hcompact' : IsCompact (f ⁻¹' Icc s' t'))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc s t → f x = c)
    (hcrit' : ∀ x ∈ criticalPoints I f, f x ∈ Icc s' t' → f x = c)
    (R : C) (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ) :
    (singularCohomologySublevelPairIsoOfCriticalValue hf hsc hct hs'c hct' hcompact hcompact'
        hcrit hcrit' R k N n).hom ≫
      TopPair.singularCohomologyMap (R := R) (k := k) (M := N) (TopPair.ofInclusionMap
        (X := TopCat.of M) (Y := TopCat.of M)
        (sublevel_mono f hlv) (sublevel_mono f (hs'c.trans hct').le)
        (ContinuousMap.inclusion (sublevel_mono f (hvt.trans (min_le_right t t'))))
        fun _ hx ↦ (hx : f _ ≤ l).trans (hls.trans (min_le_right s s'))) n =
      TopPair.singularCohomologyMap (R := R) (k := k) (M := N) (TopPair.ofInclusionMap
        (X := TopCat.of M) (Y := TopCat.of M)
        (sublevel_mono f hlv) (sublevel_mono f (hsc.trans hct).le)
        (ContinuousMap.inclusion (sublevel_mono f (hvt.trans (min_le_left t t'))))
        fun _ hx ↦ (hx : f _ ≤ l).trans (hls.trans (min_le_left s s'))) n := by
  let κ := TopPair.ofInclusionMap (X := TopCat.of M) (Y := TopCat.of M)
    (sublevel_mono f hlv)
    (sublevel_mono f ((min_le_left s s').trans (hsc.trans (lt_min hct hct')).le))
    (ContinuousMap.inclusion (sublevel_mono f hvt))
    fun _ hx ↦ sublevel_mono f hls hx
  have hR : TopPair.ofInclusionMap (X := TopCat.of M) (Y := TopCat.of M)
      (sublevel_mono f hlv) (sublevel_mono f (hs'c.trans hct').le)
      (ContinuousMap.inclusion (sublevel_mono f (hvt.trans (min_le_right t t'))))
      (fun _ hx ↦ (hx : f _ ≤ l).trans (hls.trans (min_le_right s s'))) =
      κ ≫ TopPair.ofInclusionMap (X := TopCat.of M) (Y := TopCat.of M)
        (sublevel_mono f ((min_le_left s s').trans (hsc.trans (lt_min hct hct')).le))
        (sublevel_mono f (hs'c.trans hct').le)
        (ContinuousMap.inclusion (sublevel_mono f (min_le_right t t')))
        fun _ hx ↦ (hx : f _ ≤ min s s').trans (min_le_right s s') := by
    refine Eq.trans ?_ (TopPair.ofInclusionMap_comp (X := TopCat.of M) (Y := TopCat.of M)
      (Z := TopCat.of M) (sublevel_mono f (hs'c.trans hct').le)
      (ContinuousMap.inclusion (sublevel_mono f hvt))
      (ContinuousMap.inclusion (sublevel_mono f (min_le_right t t')))
      (fun _ hx ↦ sublevel_mono f hls hx)
      (fun _ hx ↦ (hx : f _ ≤ min s s').trans (min_le_right s s')))
    congr 1
  have hL : TopPair.ofInclusionMap (X := TopCat.of M) (Y := TopCat.of M)
      (sublevel_mono f hlv) (sublevel_mono f (hsc.trans hct).le)
      (ContinuousMap.inclusion (sublevel_mono f (hvt.trans (min_le_left t t'))))
      (fun _ hx ↦ (hx : f _ ≤ l).trans (hls.trans (min_le_left s s'))) =
      κ ≫ TopPair.ofInclusionMap (X := TopCat.of M) (Y := TopCat.of M)
        (sublevel_mono f ((min_le_left s s').trans (hsc.trans (lt_min hct hct')).le))
        (sublevel_mono f (hsc.trans hct).le)
        (ContinuousMap.inclusion (sublevel_mono f (min_le_left t t')))
        fun _ hx ↦ (hx : f _ ≤ min s s').trans (min_le_left s s') := by
    refine Eq.trans ?_ (TopPair.ofInclusionMap_comp (X := TopCat.of M) (Y := TopCat.of M)
      (Z := TopCat.of M) (sublevel_mono f (hsc.trans hct).le)
      (ContinuousMap.inclusion (sublevel_mono f hvt))
      (ContinuousMap.inclusion (sublevel_mono f (min_le_left t t')))
      (fun _ hx ↦ sublevel_mono f hls hx)
      (fun _ hx ↦ (hx : f _ ≤ min s s').trans (min_le_left s s')))
    congr 1
  rw [hR, hL, TopPair.singularCohomologyMap_comp, TopPair.singularCohomologyMap_comp,
    singularCohomologySublevelPairIsoOfCriticalValue_hom_comp_singularCohomologyMap_assoc]

/-- Transporting the relative cohomology of a band around an isolated critical value through an
intermediate band via `TauCeti.singularCohomologySublevelPairIsoOfCriticalValue` agrees with
direct transport between the outer bands. -/
lemma singularCohomologySublevelPairIsoOfCriticalValue_trans (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {c s₁ t₁ s₂ t₂ s₃ t₃ : ℝ} (hs₁c : s₁ < c) (hct₁ : c < t₁) (hs₂c : s₂ < c) (hct₂ : c < t₂)
    (hs₃c : s₃ < c) (hct₃ : c < t₃)
    (hcompact₁ : IsCompact (f ⁻¹' Icc s₁ t₁)) (hcompact₂ : IsCompact (f ⁻¹' Icc s₂ t₂))
    (hcompact₃ : IsCompact (f ⁻¹' Icc s₃ t₃))
    (hcrit₁ : ∀ x ∈ criticalPoints I f, f x ∈ Icc s₁ t₁ → f x = c)
    (hcrit₂ : ∀ x ∈ criticalPoints I f, f x ∈ Icc s₂ t₂ → f x = c)
    (hcrit₃ : ∀ x ∈ criticalPoints I f, f x ∈ Icc s₃ t₃ → f x = c)
    (R : C) (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ) :
    singularCohomologySublevelPairIsoOfCriticalValue hf hs₁c hct₁ hs₂c hct₂ hcompact₁ hcompact₂
        hcrit₁ hcrit₂ R k N n ≪≫
      singularCohomologySublevelPairIsoOfCriticalValue hf hs₂c hct₂ hs₃c hct₃ hcompact₂ hcompact₃
        hcrit₂ hcrit₃ R k N n =
      singularCohomologySublevelPairIsoOfCriticalValue hf hs₁c hct₁ hs₃c hct₃ hcompact₁ hcompact₃
        hcrit₁ hcrit₃ R k N n := by
  let l := min (min s₁ s₂) s₃
  let v := min (min t₁ t₂) t₃
  have hlc : l < c := min_lt_of_right_lt hs₃c
  have hcv : c < v := lt_min (lt_min hct₁ hct₂) hct₃
  have hlv : l ≤ v := (hlc.trans hcv).le
  have hls₃ : l ≤ s₃ := min_le_right _ _
  have hvt₃ : v ≤ t₃ := min_le_right _ _
  have hcollar := isCompact_and_mfderiv_ne_zero_lowerCollar hf.continuous hct₁ hct₂ hct₃ hs₃c
    hcompact₁ hcompact₂ hcompact₃ hcrit₁ hcrit₂ hcrit₃
  have hcompact_vt₃ : IsCompact (f ⁻¹' Icc v t₃) :=
    isCompact_preimage_Icc_of_subset hf.continuous hcompact₃ (hs₃c.trans hcv).le le_rfl
  have hreg_vt₃ : ∀ x, v ≤ f x → f x ≤ t₃ → mfderiv I 𝓘(ℝ) f x ≠ 0 :=
    mfderiv_ne_zero_of_notMem_Icc hcrit₃ (hs₃c.trans hcv).le le_rfl fun hx ↦ hcv.not_ge hx.1
  let ι : sublevelPair f hlv ⟶ sublevelPair f (hs₃c.trans hct₃).le :=
    TopPair.ofInclusionMap (X := TopCat.of M) (Y := TopCat.of M) (sublevel_mono f hlv)
      (sublevel_mono f (hs₃c.trans hct₃).le) (ContinuousMap.inclusion (sublevel_mono f hvt₃))
      fun _ hx ↦ sublevel_mono f hls₃ hx
  -- Both collars `[l, s₃]` and `[v, t₃]` are compact and critical-free, so restricting from
  -- `[l, v]` to `[s₃, t₃]` induces an isomorphism on relative cohomology.
  have : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := N) ι n) :=
    isIso_singularCohomologyMap_sublevelPair_of_collar hf hls₃ (hs₃c.trans hcv).le hvt₃
      hcollar.1 hcompact_vt₃ hcollar.2 hreg_vt₃ R k N n
  have h12 := singularCohomologySublevelPairIsoOfCriticalValue_hom_comp_inclusion hf
    hs₁c hct₁ hs₂c hct₂ (le_min ((min_le_left s₁ s₂).trans' (min_le_left _ _))
      ((min_le_right s₁ s₂).trans' (min_le_left _ _)))
    (le_min ((min_le_left t₁ t₂).trans' (min_le_left _ _))
      ((min_le_right t₁ t₂).trans' (min_le_left _ _)))
    hlv hcompact₁ hcompact₂ hcrit₁ hcrit₂ R k N n
  have h23 := singularCohomologySublevelPairIsoOfCriticalValue_hom_comp_inclusion hf
    hs₂c hct₂ hs₃c hct₃ (le_min ((min_le_right s₁ s₂).trans' (min_le_left _ _))
      (min_le_right _ _))
    (le_min ((min_le_right t₁ t₂).trans' (min_le_left _ _)) (min_le_right _ _))
    hlv hcompact₂ hcompact₃ hcrit₂ hcrit₃ R k N n
  have h13 := singularCohomologySublevelPairIsoOfCriticalValue_hom_comp_inclusion hf
    hs₁c hct₁ hs₃c hct₃ (le_min ((min_le_left s₁ s₂).trans' (min_le_left _ _))
      (min_le_right _ _))
    (le_min ((min_le_left t₁ t₂).trans' (min_le_left _ _)) (min_le_right _ _))
    hlv hcompact₁ hcompact₃ hcrit₁ hcrit₃ R k N n
  -- Composition follows by right-cancellation after restricting each isomorphism to the common
  -- band `({f ≤ v}, {f ≤ l})` along `ι`.
  apply Iso.ext
  rw [Iso.trans_hom, ← cancel_mono (TopPair.singularCohomologyMap (R := R) (k := k) (M := N) ι n)]
  rw [Category.assoc, h23, h12, h13]

/-- Morphism-level composition of `TauCeti.singularCohomologySublevelPairIsoOfCriticalValue`. -/
@[reassoc]
lemma singularCohomologySublevelPairIsoOfCriticalValue_hom_comp (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {c s₁ t₁ s₂ t₂ s₃ t₃ : ℝ} (hs₁c : s₁ < c) (hct₁ : c < t₁) (hs₂c : s₂ < c) (hct₂ : c < t₂)
    (hs₃c : s₃ < c) (hct₃ : c < t₃)
    (hcompact₁ : IsCompact (f ⁻¹' Icc s₁ t₁)) (hcompact₂ : IsCompact (f ⁻¹' Icc s₂ t₂))
    (hcompact₃ : IsCompact (f ⁻¹' Icc s₃ t₃))
    (hcrit₁ : ∀ x ∈ criticalPoints I f, f x ∈ Icc s₁ t₁ → f x = c)
    (hcrit₂ : ∀ x ∈ criticalPoints I f, f x ∈ Icc s₂ t₂ → f x = c)
    (hcrit₃ : ∀ x ∈ criticalPoints I f, f x ∈ Icc s₃ t₃ → f x = c)
    (R : C) (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ) :
    (singularCohomologySublevelPairIsoOfCriticalValue hf hs₁c hct₁ hs₂c hct₂ hcompact₁ hcompact₂
        hcrit₁ hcrit₂ R k N n).hom ≫
      (singularCohomologySublevelPairIsoOfCriticalValue hf hs₂c hct₂ hs₃c hct₃ hcompact₂ hcompact₃
        hcrit₂ hcrit₃ R k N n).hom =
      (singularCohomologySublevelPairIsoOfCriticalValue hf hs₁c hct₁ hs₃c hct₃ hcompact₁ hcompact₃
        hcrit₁ hcrit₃ R k N n).hom :=
  congrArg Iso.hom (singularCohomologySublevelPairIsoOfCriticalValue_trans hf hs₁c hct₁ hs₂c hct₂
    hs₃c hct₃ hcompact₁ hcompact₂ hcompact₃ hcrit₁ hcrit₂ hcrit₃ R k N n)

/-- Inverting `TauCeti.singularCohomologySublevelPairIsoOfCriticalValue` swaps the two bands. -/
lemma singularCohomologySublevelPairIsoOfCriticalValue_symm (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {c s t s' t' : ℝ} (hsc : s < c) (hct : c < t) (hs'c : s' < c) (hct' : c < t')
    (hcompact : IsCompact (f ⁻¹' Icc s t)) (hcompact' : IsCompact (f ⁻¹' Icc s' t'))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc s t → f x = c)
    (hcrit' : ∀ x ∈ criticalPoints I f, f x ∈ Icc s' t' → f x = c)
    (R : C) (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ) :
    (singularCohomologySublevelPairIsoOfCriticalValue hf hsc hct hs'c hct' hcompact hcompact'
        hcrit hcrit' R k N n).symm =
      singularCohomologySublevelPairIsoOfCriticalValue hf hs'c hct' hsc hct hcompact' hcompact
        hcrit' hcrit R k N n := by
  have h := (singularCohomologySublevelPairIsoOfCriticalValue_trans hf hsc hct hs'c hct' hsc hct
    hcompact hcompact' hcompact hcrit hcrit' hcrit R k N n).trans
    (singularCohomologySublevelPairIsoOfCriticalValue_self hf hsc hct hcompact hcompact hcrit hcrit
      R k N n)
  apply Iso.ext
  rw [Iso.symm_hom, ← Category.comp_id (singularCohomologySublevelPairIsoOfCriticalValue hf hsc
      hct hs'c hct' hcompact hcompact' hcrit hcrit' R k N n).inv,
    ← Iso.refl_hom (X := (sublevelPair f (hsc.trans hct).le).singularCohomology R k N n),
    ← congrArg Iso.hom h, Iso.trans_hom, Iso.inv_hom_id_assoc]

/-- **Regular collars around the target of an inclusion of pairs, in cohomology.** Let
`a ≤ s ≤ t ≤ b` be such that the bands `f⁻¹[a, s]` and `f⁻¹[t, b]` are compact and contain no
critical point of the smooth function `f`, and let `L ⊆ K` be subsets of `M` with `K ⊆ {f ≤ t}`
and `L ⊆ {f ≤ a}`. Then the inclusion `(K, L) ⟶ ({f ≤ b}, {f ≤ a})` induces an isomorphism on
relative singular cohomology in degree `n` exactly when the inclusion
`(K, L) ⟶ ({f ≤ t}, {f ≤ s})` does. -/
theorem isIso_singularCohomologyMap_ofInclusionMap_sublevelPair_iff (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) (hcompact₁ : IsCompact (f ⁻¹' Icc a s))
    (hcompact₂ : IsCompact (f ⁻¹' Icc t b))
    (hreg₁ : ∀ x, a ≤ f x → f x ≤ s → mfderiv I 𝓘(ℝ) f x ≠ 0)
    (hreg₂ : ∀ x, t ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) {K L : Set M} (hLK : L ⊆ K)
    (hK : K ⊆ {x | f x ≤ t}) (hL : L ⊆ {x | f x ≤ a})
    (R : C) (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := N) (TopPair.ofInclusionMap
      (X := TopCat.of M) (Y := TopCat.of M) hLK (sublevel_mono f (has.trans (hst.trans htb)))
      (ContinuousMap.inclusion (hK.trans (sublevel_mono f htb))) fun _ hx ↦ hL hx) n) ↔
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := N) (TopPair.ofInclusionMap
      (X := TopCat.of M) (Y := TopCat.of M) hLK (sublevel_mono f hst) (ContinuousMap.inclusion hK)
      fun _ hx ↦ sublevel_mono f has (hL hx)) n) := by
  rw [← singularCohomologySublevelPairIsoOfCollars_hom_comp_singularCohomologyMap hf has hst htb
    hcompact₁ hcompact₂ hreg₁ hreg₂ hLK hK hL R k N n, isIso_comp_left_iff]

end TauCeti
