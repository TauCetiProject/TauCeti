/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Excision
public import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Cohomology.Triple
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Deformation

/-!
# Relative cohomology of bands: without critical points, and above a regular level

This is the cohomological counterpart of
`TauCeti/Geometry/Manifold/Morse/Deformation/Homology.lean`.

Let `f` be a smooth real function on a boundaryless finite-dimensional manifold `M`, and let
`a ≤ b` be such that the band `f⁻¹[a, b]` is compact and contains no critical point of `f`. The
sublevel `{f ≤ a}` is a strong deformation retract of `{f ≤ b}`
(`TauCeti.exists_sublevelDeformation`), so the relative singular cohomology of the sublevel pair
`({f ≤ b}, {f ≤ a})` vanishes in every degree
(`TauCeti.isZero_singularCohomology_sublevelPair_of_mfderiv_ne_zero`), and the inclusion
`{f ≤ a} ⊆ {f ≤ b}` induces isomorphisms on singular cohomology
(`TauCeti.isIso_singularCohomologyMap_map_sublevelPair_of_mfderiv_ne_zero`).

Above a regular value `a`, the inclusion of pairs `(f⁻¹[a, b], f⁻¹(a)) ⟶ ({f ≤ b}, {f ≤ a})`
induces isomorphisms on relative singular cohomology in every degree
(`TauCeti.isIso_singularCohomologyMap_bandPairInclusion`). Regular collars can be cut off a band
without changing its relative singular cohomology
(`TauCeti.singularCohomologySublevelPairIsoOfCollars`), so the relative singular cohomology of a
compact band around an isolated critical value depends only on the critical value
(`TauCeti.singularCohomologySublevelPairIsoOfCriticalValue`).

## Main results

* `TauCeti.isZero_singularCohomology_sublevelPair_of_mfderiv_ne_zero`: a compact band without
  critical points carries no relative cohomology.
* `TauCeti.isIso_singularCohomologyMap_map_sublevelPair_of_mfderiv_ne_zero`: so the inclusion of
  the lower sublevel into the upper one induces isomorphisms on cohomology.
* `TauCeti.isIso_singularCohomologyMap_bandPairInclusion`: above a regular value, a compact band
  relative to its lower level has the relative cohomology of the sublevel pair.
* `TauCeti.singularCohomologySublevelPairIsoOfCollars`: regular collars can be cut off a band
  without changing the relative cohomology of the sublevel pair.
* `TauCeti.singularCohomologySublevelPairIsoOfCriticalValue`: the relative cohomology of a compact
  band around an isolated critical value does not depend on the band; the identification is
  induced by inclusions of pairs
  (`TauCeti.singularCohomologySublevelPairIsoOfCriticalValue_hom_comp_singularCohomologyMap`).
* `TauCeti.isIso_singularCohomologyMap_ofInclusionMap_sublevelPair_iff`: an inclusion of pairs
  `(K, L) ⟶ ({f ≤ b}, {f ≤ a})` is an isomorphism on relative cohomology exactly when it is one
  after cutting off regular collars of the band.

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

/-- **A band without critical points carries no relative cohomology.** If the band `f⁻¹[a, b]` is
compact and contains no critical point of the smooth function `f`, the relative singular cohomology
of the sublevel pair `({f ≤ b}, {f ≤ a})` vanishes in every degree. -/
theorem isZero_singularCohomology_sublevelPair_of_mfderiv_ne_zero (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) (R : C)
    (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ) :
    IsZero ((sublevelPair f hab).singularCohomology R k N n) := by
  obtain ⟨r, -, ⟨G⟩⟩ := exists_sublevelDeformation hf hab hcompact hreg
  have e : sublevelInclusion f a b hab = .inclusion (sublevel_mono f hab) := by ext; simp
  rw [e] at G
  exact TopPair.isZero_singularCohomology_ofInclusion_of_homotopyRel (X := TopCat.of M)
    (sublevel_mono f hab) r G R k N n

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
  have hval (x : f ⁻¹' Icc a a') (s : ℝ) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
      f (φ (s * (f x - a)) x) = f x - s * (f x - a) := by
    have hx : a ≤ f x ∧ f x ≤ a' := x.property
    exact hφf x _ (mul_nonneg hs₀ (by linarith)) (by nlinarith) hx.2
  have hmem (x : f ⁻¹' Icc a a') (s : ℝ) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
      φ (s * (f x - a)) x ∈ f ⁻¹' Icc a a' := by
    have hx : a ≤ f x ∧ f x ≤ a' := x.property
    rw [mem_preimage, hval x s hs₀ hs₁, mem_Icc]
    constructor <;> nlinarith
  let r : C(f ⁻¹' Icc a a', f ⁻¹' {a}) :=
    { toFun := fun x ↦ ⟨φ (1 * (f x - a)) x, by
        rw [mem_preimage, hval x 1 zero_le_one le_rfl, mem_singleton_iff]
        ring⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact φ.continuous (by fun_prop) (by fun_prop) }
  refine TopPair.isZero_singularCohomology_ofInclusion_of_homotopyRel hLN r
    { toFun := fun p ↦ ⟨φ ((1 - (p.1 : ℝ)) * (f p.2 - a)) p.2,
        hmem p.2 _ (by linarith [p.1.property.2]) (by linarith [p.1.property.1])⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact φ.continuous (by fun_prop) (by fun_prop)
      map_zero_left := fun x ↦ Subtype.ext (by simp [r])
      map_one_left := fun x ↦ Subtype.ext (by simp [Flow.map_zero_apply])
      prop' := fun t x hx ↦ by
        have hxa : f x = a := hx
        ext
        simp [r, hxa] } R k N n

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- The excision step: for a collar `f⁻¹[a, a']` with `a < a'`, or with `a' = b`, excising
`{f < a}` from `({f ≤ b}, {f ≤ a'})` leaves `(f⁻¹[a, b], f⁻¹[a, a'])`. -/
private theorem isIso_singularCohomologyMap_excision_collar {a' : ℝ} (hf : Continuous f)
    (ha'b : a' ≤ b) (hlt : a < a' ∨ a' = b) (R : C) (k : Type*) [Ring k] [Linear k C] (N : C)
    (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := N)
      (TopPair.ofInclusionMap (X := TopCat.of M) (Y := TopCat.of M)
        (preimage_mono (Icc_subset_Icc_right ha'b) : f ⁻¹' Icc a a' ⊆ f ⁻¹' Icc a b)
        (sublevel_mono f ha'b) (ContinuousMap.inclusion fun _ hx ↦ (hx : f _ ∈ Icc a b).2)
        fun _ hx ↦ (hx : f _ ∈ Icc a a').2) n) := by
  have hWb : f ⁻¹' Icc a b ⊆ {x | f x ≤ b} := fun _ hx ↦ hx.2
  set ι := TopPair.ofInclusionMap (X := TopCat.of M) (Y := TopCat.of M)
    (preimage_mono (Icc_subset_Icc_right ha'b) : f ⁻¹' Icc a a' ⊆ f ⁻¹' Icc a b)
    (sublevel_mono f ha'b) (ContinuousMap.inclusion hWb) fun _ hx ↦ (hx : f _ ∈ Icc a a').2
  have hι : ⇑(TopPair.Hom.fst ι) = ContinuousMap.inclusion hWb :=
    funext fun _ ↦ TopPair.ofInclusionMap_fst_apply _ _ _
  refine TopPair.isIso_singularCohomologyMap_of_open_cover (R := R) (k := k) (M := N) ι
    (hι ▸ Topology.IsEmbedding.inclusion hWb) ?_
    (fun i : Bool ↦ bif i then ({x | f x.val < a' ∨ b ≤ a'} : Set {x | f x ≤ b})
      else ({x | a < f x.val} : Set {x | f x ≤ b})) (fun i ↦ ?_) ?_ (fun i ↦ ?_) n
  · rintro x ⟨y, hy⟩
    have hy' : f x.val ≤ a' := by
      have h := congrArg Subtype.val (hy.trans (congrFun hι x))
      exact h ▸ y.property
    exact ⟨⟨x.val, x.property.1, hy'⟩, rfl⟩
  · cases i
    · exact isOpen_lt continuous_const (hf.comp continuous_subtypeVal)
    · exact (isOpen_lt (hf.comp continuous_subtypeVal) continuous_const).union isOpen_const
  · refine eq_univ_of_forall fun x ↦ mem_iUnion.2 ?_
    by_cases hx : f x.val < a'
    · exact ⟨true, Or.inl hx⟩
    rcases hlt with hlt | rfl
    · exact ⟨false, show a < f x.val by linarith⟩
    · exact ⟨true, Or.inr le_rfl⟩
  · cases i
    · refine Or.inr fun x (hx : a < f x.val) ↦ ⟨⟨x.val, hx.le, x.property⟩, ?_⟩
      rw [hι]
      rfl
    · refine Or.inl fun x (hx : f x.val < a' ∨ b ≤ a') ↦ ⟨⟨x.val, ?_⟩, rfl⟩
      rcases hx with hx | hx
      · exact hx.le
      · exact (x.property : f x.val ≤ b).trans hx

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
  obtain ⟨a', haa', ha'b, hlt, hreg⟩ : ∃ a', a ≤ a' ∧ a' ≤ b ∧ (a < a' ∨ a' = b) ∧
      ∀ x, a ≤ f x → f x ≤ a' → mfderiv I 𝓘(ℝ) f x ≠ 0 := by
    rcases hab.eq_or_lt with rfl | hlt
    · refine ⟨a, le_rfl, le_rfl, Or.inr rfl, fun x h₁ h₂ hx ↦ ?_⟩
      exact isRegularPoint_iff_notMem_criticalPoints.1 (ha.isRegularPoint (le_antisymm h₂ h₁))
        (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx)
    · obtain ⟨a', ⟨h₁, h₂⟩, -, h⟩ :=
        exists_mem_Ioc_isCompact_forall_mfderiv_ne_zero (hf.of_le (by simp)) hlt hcompact ha
      exact ⟨a', h₁.le, h₂, Or.inl h₁, h⟩
  have hcollar : IsCompact (f ⁻¹' Icc a a') :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hfc)
      (preimage_mono (Icc_subset_Icc_right ha'b))
  let T₁ :=
    TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f haa') (sublevel_mono f ha'b)
  let ψ₁ : sublevelPair f hab ⟶ TopPair.ofInclusion (X := TopCat.of M) (sublevel_mono f ha'b) :=
    TopTriple.totalToOuter.app T₁
  have h₁ : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := N) ψ₁ n) :=
    T₁.isIso_singularCohomologyMap_totalToOuter_of_isZero R k N n
      (isZero_singularCohomology_sublevelPair_of_mfderiv_ne_zero hf haa' hcollar hreg R k N n)
      fun m _ ↦ isZero_singularCohomology_sublevelPair_of_mfderiv_ne_zero hf haa' hcollar hreg
        R k N m
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
  let ι : TopPair.ofInclusion (X := TopCat.of M) hNW ⟶
      TopPair.ofInclusion (X := TopCat.of M) (sublevel_mono f ha'b) :=
    TopPair.ofInclusionMap _ _ (ContinuousMap.inclusion fun _ hx ↦ (hx : f _ ∈ Icc a b).2)
      fun _ hx ↦ (hx : f _ ∈ Icc a a').2
  have h₃ : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := N) ι n) :=
    isIso_singularCohomologyMap_excision_collar hfc ha'b hlt R k N n
  have hsq : bandPairInclusion f hab ≫ ψ₁ = ψ₂ ≫ ι := by
    refine TopPair.hom_ext_of_fst _ ?_
    rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, bandPairInclusion_fst]
    ext x
    exact (TopPair.ofInclusionMap_fst_apply _ _ x).symm
  have h₁₂ : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := N) ψ₁ n ≫
      TopPair.singularCohomologyMap (R := R) (k := k) (M := N) (bandPairInclusion f hab) n) := by
    rw [← TopPair.singularCohomologyMap_comp, hsq, TopPair.singularCohomologyMap_comp]
    exact IsIso.comp_isIso' h₃ h₂
  exact IsIso.of_isIso_comp_left
    (TopPair.singularCohomologyMap (R := R) (k := k) (M := N) ψ₁ n) _

/-- **Removing regular collars from a band in cohomology.** If the bands `f⁻¹[a, s]` and
`f⁻¹[t, b]` are compact and contain no critical points, then the relative cohomology of
`({f ≤ b}, {f ≤ a})` is that of `({f ≤ t}, {f ≤ s})`: both are identified with the relative
cohomology of `({f ≤ t}, {f ≤ a})` by the long exact sequences of the triples
`{f ≤ a} ⊆ {f ≤ t} ⊆ {f ≤ b}` and `{f ≤ a} ⊆ {f ≤ s} ⊆ {f ≤ t}`. -/
def singularCohomologySublevelPairIsoOfCollars (hf : ContMDiff I 𝓘(ℝ) ∞ f) {s t : ℝ}
    (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) (hcompact₁ : IsCompact (f ⁻¹' Icc a s))
    (hcompact₂ : IsCompact (f ⁻¹' Icc t b))
    (hreg₁ : ∀ x, a ≤ f x → f x ≤ s → mfderiv I 𝓘(ℝ) f x ≠ 0)
    (hreg₂ : ∀ x, t ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0)
    (R : C) (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ) :
    (sublevelPair f (has.trans (hst.trans htb))).singularCohomology R k N n ≅
      (sublevelPair f hst).singularCohomology R k N n :=
  have h₁ := isZero_singularCohomology_sublevelPair_of_mfderiv_ne_zero hf has hcompact₁ hreg₁ R k N
  have h₂ := isZero_singularCohomology_sublevelPair_of_mfderiv_ne_zero hf htb hcompact₂ hreg₂ R k N
  @asIso _ _ _ _ _ ((TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f (has.trans hst))
      (sublevel_mono f htb)).isIso_singularCohomologyMap_innerToTotal_of_isZero R k N n (h₂ n)
        (h₂ (n + 1))) ≪≫
    (@asIso _ _ _ _ _ ((TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f has)
      (sublevel_mono f hst)).isIso_singularCohomologyMap_totalToOuter_of_isZero R k N n (h₁ n)
        fun m _ ↦ h₁ m)).symm

/-- The identification `TauCeti.singularCohomologySublevelPairIsoOfCollars` of
`Hⁿ({f ≤ b}, {f ≤ a})` with `Hⁿ({f ≤ t}, {f ≤ s})` is induced by inclusions of pairs: followed by
the map induced by `({f ≤ t}, {f ≤ a}) ⟶ ({f ≤ t}, {f ≤ s})`, it is the map induced by
`({f ≤ t}, {f ≤ a}) ⟶ ({f ≤ b}, {f ≤ a})`. -/
@[reassoc]
lemma singularCohomologySublevelPairIsoOfCollars_hom_comp_totalToOuter
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    (hcompact₁ : IsCompact (f ⁻¹' Icc a s)) (hcompact₂ : IsCompact (f ⁻¹' Icc t b))
    (hreg₁ : ∀ x, a ≤ f x → f x ≤ s → mfderiv I 𝓘(ℝ) f x ≠ 0)
    (hreg₂ : ∀ x, t ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0)
    (R : C) (k : Type*) [Ring k] [Linear k C] (N : C) (n : ℕ) :
    (singularCohomologySublevelPairIsoOfCollars hf has hst htb hcompact₁ hcompact₂ hreg₁ hreg₂
        R k N n).hom ≫
      TopPair.singularCohomologyMap (R := R) (k := k) (M := N)
        (TopTriple.totalToOuter.app (TopTriple.ofInclusions (X := TopCat.of M)
          (sublevel_mono f has) (sublevel_mono f hst))) n =
      TopPair.singularCohomologyMap (R := R) (k := k) (M := N)
        (TopTriple.innerToTotal.app (TopTriple.ofInclusions (X := TopCat.of M)
          (sublevel_mono f (has.trans hst)) (sublevel_mono f htb))) n := by
  simp [singularCohomologySublevelPairIsoOfCollars]

/-- **The relative cohomology of an isolated critical value.** Let `f⁻¹[s, t]` and `f⁻¹[s', t']` be
compact bands with `s, s' < c < t, t'`, in each of which every critical point of `f` lies on the
level `c`. Then `Hⁿ({f ≤ t}, {f ≤ s})` and `Hⁿ({f ≤ t'}, {f ≤ s'})` are isomorphic: cutting off
the regular collars identifies both with `Hⁿ({f ≤ min t t'}, {f ≤ max s s'})`
(`TauCeti.singularCohomologySublevelPairIsoOfCollars`). So the relative cohomology of a band
around an isolated critical value depends only on the value. -/
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
  have hfc := hf.continuous
  have hreg {a b : ℝ} (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c)
      {a₁ b₁ : ℝ} (ha₁ : a ≤ a₁) (hb₁ : b₁ ≤ b) (hc : c ∉ Icc a₁ b₁) :
      ∀ x, a₁ ≤ f x → f x ≤ b₁ → mfderiv I 𝓘(ℝ) f x ≠ 0 := fun x h₁ h₂ h₀ ↦ hc <| by
    rw [← hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 h₀) ⟨ha₁.trans h₁, h₂.trans hb₁⟩]
    exact ⟨h₁, h₂⟩
  have hsub {a b a₁ b₁ : ℝ} (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha₁ : a ≤ a₁)
      (hb₁ : b₁ ≤ b) : IsCompact (f ⁻¹' Icc a₁ b₁) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hfc) (preimage_mono (Icc_subset_Icc ha₁ hb₁))
  singularCohomologySublevelPairIsoOfCollars hf (le_max_left s s') (hu.trans hv).le
      (min_le_left t t') (hsub hcompact le_rfl (hu.trans hct).le)
      (hsub hcompact (hsc.trans hv).le le_rfl)
      (hreg hcrit le_rfl (hu.trans hct).le fun h ↦ hu.not_ge h.2)
      (hreg hcrit (hsc.trans hv).le le_rfl fun h ↦ hv.not_ge h.1) R k N n ≪≫
    (singularCohomologySublevelPairIsoOfCollars hf (le_max_right s s') (hu.trans hv).le
      (min_le_right t t') (hsub hcompact' le_rfl (hu.trans hct').le)
      (hsub hcompact' (hs'c.trans hv).le le_rfl)
      (hreg hcrit' le_rfl (hu.trans hct').le fun h ↦ hu.not_ge h.2)
      (hreg hcrit' (hs'c.trans hv).le le_rfl fun h ↦ hv.not_ge h.1) R k N n).symm

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
    (singularCohomologySublevelPairIsoOfCollars hf has hst htb hcompact₁ hcompact₂ hreg₁ hreg₂
        R k N n).hom ≫
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
  exact ((singularCohomologySublevelPairIsoOfCollars hf has hst htb hcompact₁ hcompact₂ hreg₁
      hreg₂ R k N n).hom ≫= TopPair.singularCohomologyMap_comp m _ n).trans <|
    (Category.assoc _ _ _).symm.trans <|
      (singularCohomologySublevelPairIsoOfCollars_hom_comp_totalToOuter hf has hst htb
        hcompact₁ hcompact₂ hreg₁ hreg₂ R k N n =≫ TopPair.singularCohomologyMap m n).trans
        (TopPair.singularCohomologyMap_comp m _ n).symm

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
  have h1 := singularCohomologySublevelPairIsoOfCollars_hom_comp_singularCohomologyMap hf
    (le_max_left s s') ((max_lt hsc hs'c).trans (lt_min hct hct')).le (min_le_left t t')
    (hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.continuous)
      (preimage_mono (Icc_subset_Icc le_rfl ((max_lt hsc hs'c).trans hct).le)))
    (hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.continuous)
      (preimage_mono (Icc_subset_Icc (hsc.trans (lt_min hct hct')).le le_rfl)))
    (fun x h₁ h₂ h₀ ↦ (max_lt hsc hs'c).not_ge <| by
      rw [← hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 h₀)
        ⟨h₁, h₂.trans ((max_lt hsc hs'c).trans hct).le⟩]
      exact h₂)
    (fun x h₁ h₂ h₀ ↦ (lt_min hct hct').not_ge <| by
      rw [← hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 h₀)
        ⟨(hsc.trans (lt_min hct hct')).le.trans h₁, h₂⟩]
      exact h₁)
    (sublevel_mono f ((min_le_left s s').trans (hsc.trans (lt_min hct hct')).le))
    (hK := subset_rfl) (hL := sublevel_mono f (min_le_left s s')) R k N n
  have h2 := singularCohomologySublevelPairIsoOfCollars_hom_comp_singularCohomologyMap hf
    (le_max_right s s') ((max_lt hsc hs'c).trans (lt_min hct hct')).le (min_le_right t t')
    (hcompact'.of_isClosed_subset (isClosed_Icc.preimage hf.continuous)
      (preimage_mono (Icc_subset_Icc le_rfl ((max_lt hsc hs'c).trans hct').le)))
    (hcompact'.of_isClosed_subset (isClosed_Icc.preimage hf.continuous)
      (preimage_mono (Icc_subset_Icc (hs'c.trans (lt_min hct hct')).le le_rfl)))
    (fun x h₁ h₂ h₀ ↦ (max_lt hsc hs'c).not_ge <| by
      rw [← hcrit' x (mem_criticalPoints_iff_mfderiv_eq_zero.2 h₀)
        ⟨h₁, h₂.trans ((max_lt hsc hs'c).trans hct').le⟩]
      exact h₂)
    (fun x h₁ h₂ h₀ ↦ (lt_min hct hct').not_ge <| by
      rw [← hcrit' x (mem_criticalPoints_iff_mfderiv_eq_zero.2 h₀)
        ⟨(hs'c.trans (lt_min hct hct')).le.trans h₁, h₂⟩]
      exact h₁)
    (sublevel_mono f ((min_le_left s s').trans (hsc.trans (lt_min hct hct')).le))
    (hK := subset_rfl) (hL := sublevel_mono f (min_le_right s s')) R k N n
  simp only [singularCohomologySublevelPairIsoOfCriticalValue, Iso.trans_hom, Iso.symm_hom,
    Category.assoc]
  rw [← h2, Iso.inv_hom_id_assoc, h1]

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
