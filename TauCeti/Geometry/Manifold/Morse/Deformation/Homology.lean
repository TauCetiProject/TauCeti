/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.Triple
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints.Band
public import TauCeti.Geometry.Manifold.Morse.Deformation

/-!
# Relative homology of bands: without critical points, and above a regular level

Let `f` be a smooth real function on a boundaryless finite-dimensional manifold `M`, and let
`a ≤ b` be such that the band `f⁻¹[a, b]` is compact and contains no critical point of `f`. The
sublevel `{f ≤ a}` is a strong deformation retract of `{f ≤ b}`
(`TauCeti.exists_sublevelDeformation`), so the relative singular homology of the sublevel pair
`({f ≤ b}, {f ≤ a})` vanishes in every degree, for coefficients in any preadditive category with
coproducts and homology (`TauCeti.isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero`), and
the inclusion `{f ≤ a} ⊆ {f ≤ b}` induces isomorphisms on singular homology
(`TauCeti.isIso_homologyMap_map_sublevelPair_of_mfderiv_ne_zero`).

The band `f⁻¹[a, b]` itself, relative to its lower level `f⁻¹(a)`, has the same relative homology
as the sublevel pair, whatever the critical points inside the band, as soon as `a` is a regular
value and the band is compact: the inclusion of pairs `(f⁻¹[a, b], f⁻¹(a)) ⟶ ({f ≤ b}, {f ≤ a})`
induces isomorphisms (`TauCeti.isIso_singularHomologyMap_bandPairInclusion`). When `b` is regular
as well, the band is a compact cobordism between the levels `f⁻¹(a)` and `f⁻¹(b)`, so statements
about sublevel pairs, such as the Morse inequalities, apply to the cobordism relative to its
incoming boundary. The proof uses a collar `f⁻¹[a, a']` without critical points above the
regular level: the flow lowering `f` at unit speed through it retracts the collar onto `f⁻¹(a)`
and `{f ≤ a'}` onto `{f ≤ a}`, so both subspaces may be enlarged by the collar, and then excision
of `{f < a}` from `({f ≤ b}, {f ≤ a'})` leaves `(f⁻¹[a, b], f⁻¹[a, a'])`.

Consequently, regular collars can be cut off a band. If `a ≤ s ≤ t ≤ b` and the bands
`f⁻¹[a, s]` and `f⁻¹[t, b]` are compact and free of critical points, the long exact sequences of
the triples `{f ≤ a} ⊆ {f ≤ t} ⊆ {f ≤ b}` and `{f ≤ a} ⊆ {f ≤ s} ⊆ {f ≤ t}` identify the relative
homology of `({f ≤ b}, {f ≤ a})` with that of `({f ≤ t}, {f ≤ s})`, for coefficients in an
abelian category with coproducts (`TauCeti.singularHomologySublevelPairIsoOfCollars`). Both
identifications are induced by inclusions of pairs
(`TauCeti.singularHomologyMap_innerToTotal_comp_singularHomologySublevelPairIsoOfCollars_hom`), and
the resulting isomorphism is compatible with the inclusion of any pair `(K, L)` with `K ⊆ {f ≤ t}`
and `L ⊆ {f ≤ a}` (`TauCeti.singularHomologyMap_comp_singularHomologySublevelPairIsoOfCollars_hom`).

In particular the relative homology of a band around an isolated critical value `c` depends only on
`c`: if `c` is the only critical value of `f` in the compact bands `f⁻¹[s, t]` and `f⁻¹[s', t']`,
with `s, s' < c < t, t'`, then `Hₙ({f ≤ t}, {f ≤ s})` and `Hₙ({f ≤ t'}, {f ≤ s'})` are both
identified with `Hₙ({f ≤ min t t'}, {f ≤ max s s'})`
(`TauCeti.singularHomologySublevelPairIsoOfCriticalValue`), compatibly with the maps induced by
the inclusions of `({f ≤ min t t'}, {f ≤ min s s'})` into both pairs
(`TauCeti.singularHomologyMap_comp_singularHomologySublevelPairIsoOfCriticalValue_hom`). This is
the contribution of the critical level `c` to the Morse inequalities of a filtration of `M` by
sublevels cut between the critical values
(`TauCeti.sum_range_neg_one_pow_mul_finrank_singularHomology_le_sum_sublevelPair`), whatever the
cut.

## Main results

* `TauCeti.isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero`: a compact band without
  critical points carries no relative homology.
* `TauCeti.isIso_homologyMap_map_sublevelPair_of_mfderiv_ne_zero`: so the inclusion of the lower
  sublevel into the upper one induces isomorphisms on homology.
* `TauCeti.isIso_singularHomologyMap_bandPairInclusion`: above a regular value, a compact band
  relative to its lower level has the relative homology of the sublevel pair.
* `TauCeti.singularHomologySublevelPairIsoOfCollars`: regular collars can be cut off a band
  without changing the relative homology of the sublevel pair.
* `TauCeti.singularHomologySublevelPairIsoOfCriticalValue`: the relative homology of a compact
  band around an isolated critical value does not depend on the band; the identification is
  induced by inclusions of pairs
  (`TauCeti.singularHomologyMap_comp_singularHomologySublevelPairIsoOfCriticalValue_hom`).
* `TauCeti.isIso_singularHomologyMap_ofInclusionMap_sublevelPair_iff`: an inclusion of pairs
  `(K, L) ⟶ ({f ≤ b}, {f ≤ a})` is an isomorphism on relative homology exactly when it is one
  after cutting off regular collars of the band.
* `TauCeti.singularHomologySublevelPairIsoSymmetricBand`: in particular a compact band around an
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

/-- **Crossing a band without critical points does not change homology.** If the band `f⁻¹[a, b]`
is compact and contains no critical point of the smooth function `f`, the inclusion of
`{f ≤ a}` into `{f ≤ b}` induces isomorphisms on singular homology in every degree. -/
theorem isIso_homologyMap_map_sublevelPair_of_mfderiv_ne_zero (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) (R : C) (n : ℕ) :
    IsIso (SSet.homologyMap (TopCat.toSSet.map (sublevelPair f hab).map) R n) := by
  obtain ⟨e, he⟩ := exists_sublevelHomotopyEquiv hf hab hcompact hreg
  have h : (sublevelPair f hab).map = TopCat.ofHom e.toFun := by
    ext x
    exact Subtype.ext (he x).symm
  have := (e.singularHomologyIso R n).isIso_hom
  rw [ContinuousMap.HomotopyEquiv.singularHomologyIso_hom, singularHomologyFunctor_obj_map] at this
  rwa [h]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- A collar `f⁻¹[a, a']` which the flow `φ` crosses at unit speed carries no homology relative to
its lower level `f⁻¹(a)`: following the flow down to the level `a` is a strong deformation
retraction. -/
private theorem isZero_singularHomology_collar {a' : ℝ} (hf : Continuous f) (φ : Flow ℝ M)
    (hφf : ∀ x t, 0 ≤ t → a ≤ f x - t → f x ≤ a' → f (φ t x) = f x - t)
    (hLN : f ⁻¹' {a} ⊆ f ⁻¹' Icc a a') (R : C) (n : ℕ) :
    IsZero ((TopPair.ofInclusion (X := TopCat.of M) hLN).singularHomology R n) := by
  obtain ⟨r, ⟨G⟩⟩ := exists_collarDeformation hf φ hφf hLN
  exact TopPair.isZero_singularHomology_ofInclusion_of_homotopyRel hLN r G R n

variable {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A]

/-- **The relative homology of a band over a regular level** (Milnor, *Lectures on the h-cobordism
theorem*, §3). If `a ≤ b`, the band `f⁻¹[a, b]` is compact and `a` is a regular value of the
smooth function `f`, then the inclusion of pairs `(f⁻¹[a, b], f⁻¹(a)) ⟶ ({f ≤ b}, {f ≤ a})`
induces isomorphisms on relative singular homology in every degree. The band may contain critical
points, and `b` need not be a regular value. -/
theorem isIso_singularHomologyMap_bandPairInclusion (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a) (R : A) (n : ℕ) :
    IsIso (TopPair.singularHomologyMap (bandPairInclusion f hab) R n) := by
  have hfc : Continuous f := hf.continuous
  -- A collar `f⁻¹[a, a']` without critical points, with `a < a'` unless the band is a level.
  obtain ⟨a', ⟨haa', ha'b⟩, hlt, hcollar, hreg⟩ :=
    exists_mem_Icc_isCompact_forall_mfderiv_ne_zero (hf.of_le (by simp)) hab hcompact ha
  -- Enlarge `{f ≤ a}` to `{f ≤ a'}` in the sublevel pair.
  let T₁ :=
    TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f haa') (sublevel_mono f ha'b)
  let ψ₁ : sublevelPair f hab ⟶ TopPair.ofInclusion (X := TopCat.of M) (sublevel_mono f ha'b) :=
    TopTriple.totalToOuter.app T₁
  have h₁ : IsIso (TopPair.singularHomologyMap ψ₁ R n) :=
    T₁.isIso_singularHomologyMap_totalToOuter_of_isZero R n
      (isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero hf haa' hcollar hreg R n)
      fun m _ ↦ isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero hf haa' hcollar hreg R m
  -- Enlarge `f⁻¹(a)` to the collar `f⁻¹[a, a']` in the band pair.
  have hLN : f ⁻¹' {a} ⊆ f ⁻¹' Icc a a' :=
    preimage_mono (singleton_subset_iff.2 ⟨le_rfl, haa'⟩)
  have hNW : f ⁻¹' Icc a a' ⊆ f ⁻¹' Icc a b := preimage_mono (Icc_subset_Icc_right ha'b)
  obtain ⟨φ, -, -, -, hφf⟩ := exists_flow_apply_eq_sub hf hcollar hreg
  let T₂ := TopTriple.ofInclusions (X := TopCat.of M) hLN hNW
  let ψ₂ : bandPair f hab ⟶ TopPair.ofInclusion (X := TopCat.of M) hNW :=
    TopTriple.totalToOuter.app T₂
  have h₂ : IsIso (TopPair.singularHomologyMap ψ₂ R n) :=
    T₂.isIso_singularHomologyMap_totalToOuter_of_isZero R n
      (isZero_singularHomology_collar hfc φ hφf hLN R n)
      fun m _ ↦ isZero_singularHomology_collar hfc φ hφf hLN R m
  -- Excise `{f < a}` from `({f ≤ b}, {f ≤ a'})`.
  have h₃ : IsIso (TopPair.singularHomologyMap (bandCollarPairInclusion f a ha'b) R n) :=
    TopPair.isIso_singularHomologyMap_bandCollarPairInclusion R hfc ha'b hlt n
  -- The two composites `(f⁻¹[a, b], f⁻¹(a)) ⟶ ({f ≤ b}, {f ≤ a'})` agree.
  have hsq : bandPairInclusion f hab ≫ ψ₁ = ψ₂ ≫ bandCollarPairInclusion f a ha'b := by
    refine TopPair.hom_ext_of_fst _ ?_
    rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, bandPairInclusion_fst,
      bandCollarPairInclusion_fst]
    ext x
    rfl
  have h₁₂ : IsIso (TopPair.singularHomologyMap (bandPairInclusion f hab) R n ≫
      TopPair.singularHomologyMap ψ₁ R n) := by
    rw [← TopPair.singularHomologyMap_comp, hsq, TopPair.singularHomologyMap_comp]
    exact IsIso.comp_isIso' h₂ h₃
  exact IsIso.of_isIso_comp_right _ (TopPair.singularHomologyMap ψ₁ R n)

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
    (R : A) (n : ℕ) :
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
    (R : A) (n : ℕ) :
    TopPair.singularHomologyMap (TopTriple.innerToTotal.app (TopTriple.ofInclusions
        (X := TopCat.of M) (sublevel_mono f (has.trans hst)) (sublevel_mono f htb))) R n ≫
      (singularHomologySublevelPairIsoOfCollars hf has hst htb hcompact₁ hcompact₂ hreg₁ hreg₂
        R n).hom =
      TopPair.singularHomologyMap (TopTriple.totalToOuter.app (TopTriple.ofInclusions
        (X := TopCat.of M) (sublevel_mono f has) (sublevel_mono f hst))) R n := by
  simp [singularHomologySublevelPairIsoOfCollars]

omit [T2Space M] in
/-- A sub-band `f⁻¹[a₁, b₁]` of a compact band `f⁻¹[a, b]` of a continuous function is compact. -/
theorem isCompact_preimage_Icc_of_subset (hf : Continuous f)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) {a₁ b₁ : ℝ} (ha₁ : a ≤ a₁) (hb₁ : b₁ ≤ b) :
    IsCompact (f ⁻¹' Icc a₁ b₁) :=
  hcompact.of_isClosed_subset (isClosed_Icc.preimage hf) (preimage_mono (Icc_subset_Icc ha₁ hb₁))

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- If every critical point of `f` in the band `f⁻¹[a, b]` lies on the level `c`, then a sub-band
`f⁻¹[a₁, b₁]` missing the level `c` contains no critical point. -/
theorem mfderiv_ne_zero_of_notMem_Icc {c : ℝ}
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c) {a₁ b₁ : ℝ} (ha₁ : a ≤ a₁)
    (hb₁ : b₁ ≤ b) (hc : c ∉ Icc a₁ b₁) (x : M) (h₁ : a₁ ≤ f x) (h₂ : f x ≤ b₁) :
    mfderiv I 𝓘(ℝ) f x ≠ 0 := fun h₀ ↦ hc <| by
  rw [← hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 h₀) ⟨ha₁.trans h₁, h₂.trans hb₁⟩]
  exact ⟨h₁, h₂⟩

/-- **The relative homology of an isolated critical value.** Let `f⁻¹[s, t]` and `f⁻¹[s', t']` be
compact bands with `s, s' < c < t, t'`, in each of which every critical point of `f` lies on the
level `c`. Then `Hₙ({f ≤ t}, {f ≤ s})` and `Hₙ({f ≤ t'}, {f ≤ s'})` are isomorphic: cutting off
the regular collars identifies both with `Hₙ({f ≤ min t t'}, {f ≤ max s s'})`
(`TauCeti.singularHomologySublevelPairIsoOfCollars`). So the relative homology of a band around an
isolated critical value depends only on the value. -/
def singularHomologySublevelPairIsoOfCriticalValue (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {c s t s' t' : ℝ} (hsc : s < c) (hct : c < t) (hs'c : s' < c) (hct' : c < t')
    (hcompact : IsCompact (f ⁻¹' Icc s t)) (hcompact' : IsCompact (f ⁻¹' Icc s' t'))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc s t → f x = c)
    (hcrit' : ∀ x ∈ criticalPoints I f, f x ∈ Icc s' t' → f x = c) (R : A) (n : ℕ) :
    (sublevelPair f (hsc.trans hct).le).singularHomology R n ≅
      (sublevelPair f (hs'c.trans hct').le).singularHomology R n :=
  have hu : max s s' < c := max_lt hsc hs'c
  have hv : c < min t t' := lt_min hct hct'
  have hfc := hf.continuous
  -- Below `max s s'` and above `min t t'` the bands are compact and hold no critical point.
  singularHomologySublevelPairIsoOfCollars hf (le_max_left s s') (hu.trans hv).le
      (min_le_left t t') (isCompact_preimage_Icc_of_subset hfc hcompact le_rfl (hu.trans hct).le)
      (isCompact_preimage_Icc_of_subset hfc hcompact (hsc.trans hv).le le_rfl)
      (mfderiv_ne_zero_of_notMem_Icc hcrit le_rfl (hu.trans hct).le fun h ↦ hu.not_ge h.2)
      (mfderiv_ne_zero_of_notMem_Icc hcrit (hsc.trans hv).le le_rfl fun h ↦ hv.not_ge h.1)
      R n ≪≫
    (singularHomologySublevelPairIsoOfCollars hf (le_max_right s s') (hu.trans hv).le
      (min_le_right t t') (isCompact_preimage_Icc_of_subset hfc hcompact' le_rfl (hu.trans hct').le)
      (isCompact_preimage_Icc_of_subset hfc hcompact' (hs'c.trans hv).le le_rfl)
      (mfderiv_ne_zero_of_notMem_Icc hcrit' le_rfl (hu.trans hct').le fun h ↦ hu.not_ge h.2)
      (mfderiv_ne_zero_of_notMem_Icc hcrit' (hs'c.trans hv).le le_rfl fun h ↦ hv.not_ge h.1)
      R n).symm

omit [T2Space M] in
/-- **Narrowing a band.** If the band `f⁻¹[a, b]` of a continuous function is compact and
`ε ≤ min (c - a) (b - c)`, then `[c - ε, c + ε] ⊆ [a, b]` and the band `f⁻¹[c - ε, c + ε]` is
compact. -/
theorem Icc_subset_and_isCompact_preimage_Icc (hf : Continuous f)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) {c ε : ℝ} (hεδ : ε ≤ min (c - a) (b - c)) :
    Icc (c - ε) (c + ε) ⊆ Icc a b ∧ IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) := by
  have hε' : Icc (c - ε) (c + ε) ⊆ Icc a b :=
    Icc_subset_Icc (by linarith [hεδ.trans (min_le_left _ _)])
      (by linarith [hεδ.trans (min_le_right _ _)])
  exact ⟨hε', hcompact.of_isClosed_subset (isClosed_Icc.preimage hf) (preimage_mono hε')⟩

/-- **Narrowing a band around an isolated critical value.** Let `a < c < b`, with the band
`f⁻¹[a, b]` compact and every critical point of `f` in it on the level `c`. For
`0 < ε ≤ min (c - a) (b - c)`, `Hₙ({f ≤ b}, {f ≤ a})` is identified with
`Hₙ({f ≤ c + ε}, {f ≤ c - ε})` by `TauCeti.singularHomologySublevelPairIsoOfCriticalValue`
(`TauCeti.singularHomologySublevelPairIsoSymmetricBand_def`). -/
def singularHomologySublevelPairIsoSymmetricBand (hf : ContMDiff I 𝓘(ℝ) ∞ f) {c ε : ℝ}
    (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c)
    (hε : 0 < ε) (hεδ : ε ≤ min (c - a) (b - c)) (R : A) (n : ℕ) :
    (sublevelPair f (hac.trans hcb).le).singularHomology R n ≅
      (sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology R n :=
  have hband := Icc_subset_and_isCompact_preimage_Icc hf.continuous hcompact hεδ
  singularHomologySublevelPairIsoOfCriticalValue hf hac hcb (by linarith : c - ε < c)
    (by linarith : c < c + ε) hcompact hband.2 hcrit (fun x hx hfx ↦ hcrit x hx (hband.1 hfx)) R n

/-- The narrowed-band identification `TauCeti.singularHomologySublevelPairIsoSymmetricBand` is
`TauCeti.singularHomologySublevelPairIsoOfCriticalValue` for the bands `f⁻¹[a, b]` and
`f⁻¹[c - ε, c + ε]`, so its naturality lemma
`TauCeti.singularHomologyMap_comp_singularHomologySublevelPairIsoOfCriticalValue_hom` applies. -/
lemma singularHomologySublevelPairIsoSymmetricBand_def (hf : ContMDiff I 𝓘(ℝ) ∞ f) {c ε : ℝ}
    (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c)
    (hε : 0 < ε) (hεδ : ε ≤ min (c - a) (b - c)) (R : A) (n : ℕ) :
    singularHomologySublevelPairIsoSymmetricBand hf hac hcb hcompact hcrit hε hεδ R n =
      singularHomologySublevelPairIsoOfCriticalValue hf hac hcb (by linarith : c - ε < c)
        (by linarith : c < c + ε) hcompact
        (Icc_subset_and_isCompact_preimage_Icc hf.continuous hcompact hεδ).2 hcrit
        (fun x hx hfx ↦ hcrit x hx
          ((Icc_subset_and_isCompact_preimage_Icc hf.continuous hcompact hεδ).1 hfx)) R n :=
  (rfl)

/-- The identification `TauCeti.singularHomologySublevelPairIsoOfCollars` of
`Hₙ({f ≤ b}, {f ≤ a})` with `Hₙ({f ≤ t}, {f ≤ s})` is compatible with inclusions of pairs: for
subsets `L ⊆ K` of `M` with `K ⊆ {f ≤ t}` and `L ⊆ {f ≤ a}`, precomposed with the map induced by
the inclusion `(K, L) ⟶ ({f ≤ b}, {f ≤ a})`, it is the map induced by the inclusion
`(K, L) ⟶ ({f ≤ t}, {f ≤ s})`. -/
@[reassoc]
lemma singularHomologyMap_comp_singularHomologySublevelPairIsoOfCollars_hom
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    (hcompact₁ : IsCompact (f ⁻¹' Icc a s)) (hcompact₂ : IsCompact (f ⁻¹' Icc t b))
    (hreg₁ : ∀ x, a ≤ f x → f x ≤ s → mfderiv I 𝓘(ℝ) f x ≠ 0)
    (hreg₂ : ∀ x, t ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) {K L : Set M} (hLK : L ⊆ K)
    (hK : K ⊆ {x | f x ≤ t}) (hL : L ⊆ {x | f x ≤ a}) (R : A) (n : ℕ) :
    TopPair.singularHomologyMap (TopPair.ofInclusionMap (X := TopCat.of M) (Y := TopCat.of M)
        hLK (sublevel_mono f (has.trans (hst.trans htb)))
        (ContinuousMap.inclusion (hK.trans (sublevel_mono f htb))) fun _ hx ↦ hL hx) R n ≫
      (singularHomologySublevelPairIsoOfCollars hf has hst htb hcompact₁ hcompact₂ hreg₁ hreg₂
        R n).hom =
      TopPair.singularHomologyMap (TopPair.ofInclusionMap (X := TopCat.of M) (Y := TopCat.of M)
        hLK (sublevel_mono f hst) (ContinuousMap.inclusion hK)
        fun _ hx ↦ sublevel_mono f has (hL hx)) R n := by
  -- Factor the inclusion through `({f ≤ t}, {f ≤ a})`.
  let T := TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f (has.trans hst))
    (sublevel_mono f htb)
  let T' := TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f has) (sublevel_mono f hst)
  let k := TopPair.ofInclusionMap (X := TopCat.of M) (Y := TopCat.of M) hLK
    (sublevel_mono f (has.trans hst)) (ContinuousMap.inclusion hK) fun _ hx ↦ hL hx
  have hι : TopPair.ofInclusionMap (X := TopCat.of M) (Y := TopCat.of M) hLK
      (sublevel_mono f (has.trans (hst.trans htb)))
      (ContinuousMap.inclusion (hK.trans (sublevel_mono f htb))) (fun _ hx ↦ hL hx) =
      k ≫ TopTriple.innerToTotal.app T :=
    TopPair.hom_ext_of_fst _ <| by
      ext x
      exact (TopPair.ofInclusionMap_fst_apply _ _ x).trans (congrArg
        (fun y ↦ TopPair.Hom.fst (TopTriple.innerToTotal.app T) y)
        (TopPair.ofInclusionMap_fst_apply (ContinuousMap.inclusion hK) _ x)).symm
  have hj : k ≫ TopTriple.totalToOuter.app T' = TopPair.ofInclusionMap (X := TopCat.of M)
      (Y := TopCat.of M) hLK (sublevel_mono f hst) (ContinuousMap.inclusion hK)
      (fun _ hx ↦ sublevel_mono f has (hL hx)) :=
    TopPair.hom_ext_of_fst _ <| by
      ext x
      exact (congrArg (fun y ↦ TopPair.Hom.fst (TopTriple.totalToOuter.app T') y)
        (TopPair.ofInclusionMap_fst_apply _ _ x)).trans
          (TopPair.ofInclusionMap_fst_apply (ContinuousMap.inclusion hK) _ x).symm
  rw [hι, ← hj]
  exact (TopPair.singularHomologyMap_comp_assoc k R _ n _).trans <|
    (TopPair.singularHomologyMap k R n ≫=
      singularHomologyMap_innerToTotal_comp_singularHomologySublevelPairIsoOfCollars_hom hf has hst
        htb hcompact₁ hcompact₂ hreg₁ hreg₂ R n).trans
      (TopPair.singularHomologyMap_comp k R _ n).symm

/-- The identification `TauCeti.singularHomologySublevelPairIsoOfCriticalValue` of
`Hₙ({f ≤ t}, {f ≤ s})` with `Hₙ({f ≤ t'}, {f ≤ s'})` is induced by inclusions of pairs:
precomposed with the map induced by `({f ≤ min t t'}, {f ≤ min s s'}) ⟶ ({f ≤ t}, {f ≤ s})`, it is
the map induced by `({f ≤ min t t'}, {f ≤ min s s'}) ⟶ ({f ≤ t'}, {f ≤ s'})`. -/
@[reassoc]
lemma singularHomologyMap_comp_singularHomologySublevelPairIsoOfCriticalValue_hom
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {c s t s' t' : ℝ} (hsc : s < c) (hct : c < t) (hs'c : s' < c)
    (hct' : c < t') (hcompact : IsCompact (f ⁻¹' Icc s t))
    (hcompact' : IsCompact (f ⁻¹' Icc s' t'))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc s t → f x = c)
    (hcrit' : ∀ x ∈ criticalPoints I f, f x ∈ Icc s' t' → f x = c) (R : A) (n : ℕ) :
    TopPair.singularHomologyMap (TopPair.ofInclusionMap (X := TopCat.of M) (Y := TopCat.of M)
        (sublevel_mono f ((min_le_left s s').trans (hsc.trans (lt_min hct hct')).le))
        (sublevel_mono f (hsc.trans hct).le)
        (ContinuousMap.inclusion (sublevel_mono f (min_le_left t t')))
        fun _ hx ↦ (hx : f _ ≤ min s s').trans (min_le_left s s')) R n ≫
      (singularHomologySublevelPairIsoOfCriticalValue hf hsc hct hs'c hct' hcompact hcompact'
        hcrit hcrit' R n).hom =
      TopPair.singularHomologyMap (TopPair.ofInclusionMap (X := TopCat.of M) (Y := TopCat.of M)
        (sublevel_mono f ((min_le_left s s').trans (hsc.trans (lt_min hct hct')).le))
        (sublevel_mono f (hs'c.trans hct').le)
        (ContinuousMap.inclusion (sublevel_mono f (min_le_right t t')))
        fun _ hx ↦ (hx : f _ ≤ min s s').trans (min_le_right s s')) R n := by
  simp only [singularHomologySublevelPairIsoOfCriticalValue, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, Iso.comp_inv_eq,
    singularHomologyMap_comp_singularHomologySublevelPairIsoOfCollars_hom (hK := subset_rfl)
      (hL := sublevel_mono f (min_le_left s s')),
    singularHomologyMap_comp_singularHomologySublevelPairIsoOfCollars_hom (hK := subset_rfl)
      (hL := sublevel_mono f (min_le_right s s'))]

/-- **Regular collars around the target of an inclusion of pairs.** Let `a ≤ s ≤ t ≤ b` be such
that the bands `f⁻¹[a, s]` and `f⁻¹[t, b]` are compact and contain no critical point of the smooth
function `f`, and let `L ⊆ K` be subsets of `M` with `K ⊆ {f ≤ t}` and `L ⊆ {f ≤ a}`. Then the
inclusion `(K, L) ⟶ ({f ≤ b}, {f ≤ a})` induces an isomorphism on relative singular homology in
degree `n` exactly when the inclusion `(K, L) ⟶ ({f ≤ t}, {f ≤ s})` does: followed by the
isomorphism `TauCeti.singularHomologySublevelPairIsoOfCollars`, the first becomes the second
(`TauCeti.singularHomologyMap_comp_singularHomologySublevelPairIsoOfCollars_hom`). -/
theorem isIso_singularHomologyMap_ofInclusionMap_sublevelPair_iff (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) (hcompact₁ : IsCompact (f ⁻¹' Icc a s))
    (hcompact₂ : IsCompact (f ⁻¹' Icc t b))
    (hreg₁ : ∀ x, a ≤ f x → f x ≤ s → mfderiv I 𝓘(ℝ) f x ≠ 0)
    (hreg₂ : ∀ x, t ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) {K L : Set M} (hLK : L ⊆ K)
    (hK : K ⊆ {x | f x ≤ t}) (hL : L ⊆ {x | f x ≤ a}) (R : A) (n : ℕ) :
    IsIso (TopPair.singularHomologyMap (TopPair.ofInclusionMap (X := TopCat.of M)
      (Y := TopCat.of M) hLK (sublevel_mono f (has.trans (hst.trans htb)))
      (ContinuousMap.inclusion (hK.trans (sublevel_mono f htb))) fun _ hx ↦ hL hx) R n) ↔
    IsIso (TopPair.singularHomologyMap (TopPair.ofInclusionMap (X := TopCat.of M)
      (Y := TopCat.of M) hLK (sublevel_mono f hst) (ContinuousMap.inclusion hK)
      fun _ hx ↦ sublevel_mono f has (hL hx)) R n) := by
  rw [← singularHomologyMap_comp_singularHomologySublevelPairIsoOfCollars_hom hf has hst htb
    hcompact₁ hcompact₂ hreg₁ hreg₂ hLK hK hL R n, isIso_comp_right_iff]

end TauCeti
