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
public import TauCeti.Geometry.Manifold.Morse.Deformation

/-!
# Relative homology of bands: without critical points, and above a regular level

Let `f` be a smooth real function on a boundaryless finite-dimensional manifold `M`, and let
`a ≤ b` be such that the band `f⁻¹[a, b]` is compact and contains no critical point of `f`. The
sublevel `{f ≤ a}` is a strong deformation retract of `{f ≤ b}`
(`TauCeti.exists_sublevelDeformation`), so the relative singular homology of the sublevel pair
`({f ≤ b}, {f ≤ a})` vanishes in every degree, for coefficients in any preadditive category with
coproducts and homology (`TauCeti.isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero`).

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
(`TauCeti.singularHomologyMap_innerToTotal_comp_singularHomologySublevelPairIsoOfCollars_hom`).

## Main results

* `TauCeti.isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero`: a compact band without
  critical points carries no relative homology.
* `TauCeti.isIso_singularHomologyMap_bandPairInclusion`: above a regular value, a compact band
  relative to its lower level has the relative homology of the sublevel pair.
* `TauCeti.singularHomologySublevelPairIsoOfCollars`: regular collars can be cut off a band
  without changing the relative homology of the sublevel pair.

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

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- A collar `f⁻¹[a, a']` which the flow `φ` crosses at unit speed carries no homology relative to
its lower level `f⁻¹(a)`: following the flow down to the level `a` is a strong deformation
retraction. -/
private theorem isZero_singularHomology_collar {a' : ℝ} (hf : Continuous f) (φ : Flow ℝ M)
    (hφf : ∀ x t, 0 ≤ t → a ≤ f x - t → f x ≤ a' → f (φ t x) = f x - t)
    (hLN : f ⁻¹' {a} ⊆ f ⁻¹' Icc a a') (R : C) (n : ℕ) :
    IsZero ((TopPair.ofInclusion (X := TopCat.of M) hLN).singularHomology R n) := by
  -- Along the flow line of `x` in the collar, `f` takes the value `f x - s * (f x - a)` at time
  -- `s * (f x - a)`, for `0 ≤ s ≤ 1`.
  have hval (x : f ⁻¹' Icc a a') (s : ℝ) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
      f (φ (s * (f x - a)) x) = f x - s * (f x - a) := by
    have hx : a ≤ f x ∧ f x ≤ a' := x.2
    exact hφf x _ (mul_nonneg hs₀ (by linarith)) (by nlinarith) hx.2
  have hmem (x : f ⁻¹' Icc a a') (s : ℝ) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
      φ (s * (f x - a)) x ∈ f ⁻¹' Icc a a' := by
    have hx : a ≤ f x ∧ f x ≤ a' := x.2
    rw [mem_preimage, hval x s hs₀ hs₁, mem_Icc]
    constructor <;> nlinarith
  let r : C(f ⁻¹' Icc a a', f ⁻¹' {a}) :=
    { toFun := fun x ↦ ⟨φ (1 * (f x - a)) x, by
        rw [mem_preimage, hval x 1 zero_le_one le_rfl, mem_singleton_iff]
        ring⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact φ.continuous (by fun_prop) (by fun_prop) }
  refine TopPair.isZero_singularHomology_ofInclusion_of_homotopyRel hLN r
    { toFun := fun p ↦ ⟨φ ((1 - (p.1 : ℝ)) * (f p.2 - a)) p.2,
        hmem p.2 _ (by linarith [p.1.2.2]) (by linarith [p.1.2.1])⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact φ.continuous (by fun_prop) (by fun_prop)
      map_zero_left := fun x ↦ Subtype.ext (by simp [r])
      map_one_left := fun x ↦ Subtype.ext (by simp [Flow.map_zero_apply])
      prop' := fun t x hx ↦ by
        have hxa : f x = a := hx
        ext
        simp [r, hxa] } R n

variable {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- The excision step: for a collar `f⁻¹[a, a']` with `a < a'`, or with `a' = b`, excising
`{f < a}` from `({f ≤ b}, {f ≤ a'})` leaves `(f⁻¹[a, b], f⁻¹[a, a'])`. -/
private theorem isIso_singularHomologyMap_excision_collar {a' : ℝ} (hf : Continuous f)
    (ha'b : a' ≤ b) (hlt : a < a' ∨ a' = b) (R : A) (n : ℕ) :
    IsIso (TopPair.singularHomologyMap
      (TopPair.ofInclusionMap (X := TopCat.of M) (Y := TopCat.of M)
        (preimage_mono (Icc_subset_Icc_right ha'b) : f ⁻¹' Icc a a' ⊆ f ⁻¹' Icc a b)
        (sublevel_mono f ha'b) (ContinuousMap.inclusion fun _ hx ↦ (hx : f _ ∈ Icc a b).2)
        fun _ hx ↦ (hx : f _ ∈ Icc a a').2) R n) := by
  have hWb : f ⁻¹' Icc a b ⊆ {x | f x ≤ b} := fun _ hx ↦ hx.2
  set ι := TopPair.ofInclusionMap (X := TopCat.of M) (Y := TopCat.of M)
    (preimage_mono (Icc_subset_Icc_right ha'b) : f ⁻¹' Icc a a' ⊆ f ⁻¹' Icc a b)
    (sublevel_mono f ha'b) (ContinuousMap.inclusion hWb) fun _ hx ↦ (hx : f _ ∈ Icc a a').2
  have hι : ⇑(TopPair.Hom.fst ι) = ContinuousMap.inclusion hWb :=
    funext fun _ ↦ TopPair.ofInclusionMap_fst_apply _ _ _
  -- The cover of `{f ≤ b}` by `{f < a'}` (all of it if `a' = b`), inside the subspace, and by
  -- `{a < f}`, inside the band.
  refine TopPair.isIso_singularHomologyMap_of_open_cover R ι
    (hι ▸ Topology.IsEmbedding.inclusion hWb) ?_
    (fun i : Bool ↦ bif i then ({x | f x.1 < a' ∨ b ≤ a'} : Set {x | f x ≤ b})
      else ({x | a < f x.1} : Set {x | f x ≤ b})) (fun i ↦ ?_) ?_ (fun i ↦ ?_) n
  · rintro x ⟨y, hy⟩
    have hy' : f x.1 ≤ a' := by
      have h := congrArg Subtype.val (hy.trans (congrFun hι x))
      exact h ▸ y.2
    exact ⟨⟨x.1, x.2.1, hy'⟩, rfl⟩
  · cases i
    · exact isOpen_lt continuous_const (hf.comp continuous_subtype_val)
    · exact (isOpen_lt (hf.comp continuous_subtype_val) continuous_const).union isOpen_const
  · refine eq_univ_of_forall fun x ↦ mem_iUnion.2 ?_
    by_cases hx : f x.1 < a'
    · exact ⟨true, Or.inl hx⟩
    rcases hlt with hlt | rfl
    · exact ⟨false, show a < f x.1 by linarith⟩
    · exact ⟨true, Or.inr le_rfl⟩
  · cases i
    · refine Or.inr fun x (hx : a < f x.1) ↦ ⟨⟨x.1, hx.le, x.2⟩, ?_⟩
      rw [hι]
      rfl
    · refine Or.inl fun x (hx : f x.1 < a' ∨ b ≤ a') ↦ ⟨⟨x.1, ?_⟩, rfl⟩
      rcases hx with hx | hx
      · exact hx.le
      · exact (x.2 : f x.1 ≤ b).trans hx

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
  obtain ⟨a', haa', ha'b, hlt, hreg⟩ : ∃ a', a ≤ a' ∧ a' ≤ b ∧ (a < a' ∨ a' = b) ∧
      ∀ x, a ≤ f x → f x ≤ a' → mfderiv I 𝓘(ℝ) f x ≠ 0 := by
    rcases hab.eq_or_lt with rfl | hlt
    · refine ⟨a, le_rfl, le_rfl, Or.inr rfl, fun x h₁ h₂ hx ↦ ?_⟩
      exact isRegularPoint_iff_notMem_criticalPoints.1 (ha.isRegularPoint (le_antisymm h₂ h₁))
        (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx)
    · obtain ⟨a', ⟨h₁, h₂⟩, h⟩ :=
        exists_mem_Ioc_forall_notMem_criticalPoints (hf.of_le (by simp)) hlt hcompact ha
      exact ⟨a', h₁.le, h₂, Or.inl h₁, fun x hx₁ hx₂ hx ↦
        h x (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) ⟨hx₁, hx₂⟩⟩
  have hcollar : IsCompact (f ⁻¹' Icc a a') :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hfc)
      (preimage_mono (Icc_subset_Icc_right ha'b))
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
  let ι : TopPair.ofInclusion (X := TopCat.of M) hNW ⟶
      TopPair.ofInclusion (X := TopCat.of M) (sublevel_mono f ha'b) :=
    TopPair.ofInclusionMap _ _ (ContinuousMap.inclusion fun _ hx ↦ (hx : f _ ∈ Icc a b).2)
      fun _ hx ↦ (hx : f _ ∈ Icc a a').2
  have h₃ : IsIso (TopPair.singularHomologyMap ι R n) :=
    isIso_singularHomologyMap_excision_collar hfc ha'b hlt R n
  -- The two composites `(f⁻¹[a, b], f⁻¹(a)) ⟶ ({f ≤ b}, {f ≤ a'})` agree.
  have hsq : bandPairInclusion f hab ≫ ψ₁ = ψ₂ ≫ ι := by
    refine TopPair.hom_ext_of_fst _ ?_
    rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, bandPairInclusion_fst]
    ext x
    exact (TopPair.ofInclusionMap_fst_apply _ _ x).symm
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

end TauCeti
