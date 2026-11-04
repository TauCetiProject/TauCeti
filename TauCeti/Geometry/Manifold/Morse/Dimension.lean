/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Dimension
public import TauCeti.Geometry.Manifold.Morse.Cell.Band

/-!
# Morse index bounds, free top homology, and cohomology vanishing

Let `f` be a Morse function on a boundaryless finite-dimensional manifold `M`, write
`M_b = {f ≤ b}`, and suppose every critical point in a compact band `f⁻¹[a, b]` between regular
values `a ≤ b` has Morse index at most `d`. Cutting the band at its critical values into elementary
cobordisms (`TauCeti.IsMorse.band_induction`), each homotopy-equivalent as a pair to a finite
relative CW complex with cells only in dimensions at most `d`
(`TauCeti.IsMorse.exists_relCWComplex_isIso_singularHomologyMap_sublevelPair`), and gluing along
the long exact sequence of each sublevel triple `M_a ⊆ M_m ⊆ M_b` complements the homology
vanishing above `d` in `TauCeti.Geometry.Manifold.Morse.Cell.Band` with:

* **Projectivity and freeness of top homology in degree `d`**
  (`TauCeti.IsMorse.projective_singularHomology_sublevelPair_of_manifoldMorseIndex_le`,
  `TauCeti.IsMorse.free_singularHomology_sublevelPair_of_manifoldMorseIndex_le`):
  `H_d(M_b, M_a; R)` is projective over any hereditary abelian category with coproducts when `R` is
  projective, and `H_d(M_b, M_a; P)` is a free `k`-module over any principal ideal ring `k` without
  zero divisors (in any universe, including `ℤ`) for any projective `k`-module `P`.
* **Cohomology vanishing above `d`**
  (`TauCeti.IsMorse.isZero_singularCohomology_sublevelPair_of_manifoldMorseIndex_le`):
  `Hⁿ(M_b, M_a; R, N) = 0` for every `n > d` over any hereditary commutative ring `k` (in any
  universe, including `ℤ`), for any projective `R` and any `k`-module `N`, by the universal
  coefficient theorem. Degree-`d` integral cohomology `H^d(M_b, M_a; ℤ)` need not be torsion-free,
  as `Ext¹_ℤ(H_{d-1}(M_b, M_a; ℤ), ℤ)` can contribute torsion.

Specializing `M_a = ∅` below the minimum of `f` on `M_b` gives the corresponding absolute theorems
for any **compact regular sublevel set** `M_b` (requiring no compactness of the ambient manifold
`M`, as for pseudoconvex or Morse exhaustions on noncompact manifolds), and specializing further to
`b > sup f` gives the theorems for a **compact manifold** `M` (including homology vanishing above
`d` without exact sequential colimit assumptions,
`TauCeti.IsMorse.isZero_singularHomology_of_compactSpace_of_manifoldMorseIndex_le`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Sections 3 and 5.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2 (Theorem 2.35) and Section 3.1 (Theorem 3.2).
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology Topology.RelCWComplex
open scoped ContDiff Manifold

universe u v w

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ}

section Band

/-- Across a single critical level `c` whose critical points all have index at most `d`, there is a
collar `[c - ε, c + ε]` and a finite relative CW complex over `{f ≤ c - ε}` with no cells above
dimension `d` whose inclusion into `({f ≤ c + ε}, {f ≤ c - ε})` induces isomorphisms on relative
singular homology. -/
private theorem IsMorse.exists_level_relCWComplex_of_manifoldMorseIndex_le (hf : IsMorse I f)
    {c δ : ℝ} {d : ℕ} (hδ : 0 < δ) (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ)))
    (hd : ∀ x ∈ criticalPoints I f ∩ f ⁻¹' {c}, manifoldMorseIndex I f x ≤ d) :
    ∃ (ε : ℝ) (_ : 0 < ε), ε ≤ δ ∧
      ∃ (C : Set M) (_ : RelCWComplex C {x | f x ≤ c - ε}) (_ : RelCWComplex.Finite C),
        (∀ m, d < m → IsEmpty (cell C m)) ∧
        ∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Preadditive A]
          [CategoryWithHomology A] (R : A) (n : ℕ),
          Nonempty ((complexBasePair C).singularHomology R n ≅
            (sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology R n) := by
  obtain ⟨ε, hε, hεδ, C, _, _, _, hcell, hiso⟩ :=
    hf.exists_relCWComplex_isIso_singularHomologyMap_sublevelPair.{u, v, w} hδ hcompact
  refine ⟨ε, hε, hεδ, C, inferInstance, inferInstance, fun m hm ↦ ?_, fun R n ↦ ?_⟩
  · exact (hcell m).some.isEmpty_congr.2 ⟨fun ⟨q, hq⟩ ↦ by have := hd q q.2; omega⟩
  · rw [complexBasePair_eq_ofInclusion]
    exact ⟨@asIso _ _ _ _ _ (hiso R n)⟩

/-- **Projectivity of top relative homology at a Morse index bound** over a hereditary abelian
category: if `a ≤ b` are regular values with compact band `f⁻¹[a, b]` and every critical point in
`f⁻¹(a, b]` has Morse index at most `d`, then `H_d({f ≤ b}, {f ≤ a}; R)` is projective whenever `R`
is projective. -/
theorem IsMorse.projective_singularHomology_sublevelPair_of_manifoldMorseIndex_le
    (hf : IsMorse I f) {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A]
    [∀ V : A, HasProjectiveDimensionLE V 1] (R : A) [Projective R]
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) {d : ℕ}
    (hd : ∀ x ∈ criticalPoints I f, f x ∈ Ioc a b → manifoldMorseIndex I f x ≤ d) :
    Projective ((sublevelPair f hab).singularHomology R d) := by
  refine (hf.band_induction
    (P := fun s t hst ↦ Projective ((sublevelPair f hst).singularHomology R d) ∧
      IsZero ((sublevelPair f hst).singularHomology R (d + 1)))
    hab hcompact ha hb
    (fun _ _ hst hc hcrit ↦ ?_) (fun p _ hap hpb _ hδ hc ↦ ?_) (fun _ _ _ hrs hst _ h₁ h₂ ↦ ?_)).1
  · have hzero (k : ℕ) := isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero hf.contMDiff
      hst hc (fun x hsx hxt hx ↦
        hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) ⟨hsx, hxt⟩) R k
    exact ⟨(hzero d).projective, hzero (d + 1)⟩
  · obtain ⟨ε, hε, hεδ, C, _, _, hempty, hiso⟩ :=
      hf.exists_level_relCWComplex_of_manifoldMorseIndex_le.{u, v, w} hδ hc
        fun x hx ↦ hd x hx.1 (mem_preimage.1 hx.2 ▸ ⟨hap, hpb.le⟩)
    have : ∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A := fun m ↦
      have : _root_.Finite (cell C m) := FiniteType.finite_cell m
      @hasExactColimitsOfShape_discrete_finite A _ _ Abelian.hasFiniteBiproducts _ _
    have : IsEmpty (cell C (d + 1)) := hempty (d + 1) (Nat.lt_succ_self d)
    refine ⟨ε, hε, hεδ,
      Projective.of_iso (hiso R d).some
        (projective_singularHomology_complexBasePair_of_isEmpty_cell_succ C R d),
      (isZero_singularHomology_complexBasePair_of_isEmpty_cell C R (d + 1)).of_iso
        (hiso R (d + 1)).some.symm⟩
  · let T := TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f hrs) (sublevel_mono f hst)
    have : Projective ((TopTriple.innerPair.obj T).singularHomology R d) := h₁.1
    have : Projective ((TopTriple.outerPair.obj T).singularHomology R d) := h₂.1
    exact ⟨T.projective_singularHomology_totalPair R d h₂.2,
      T.isZero_singularHomology_totalPair R (d + 1) h₁.2 h₂.2⟩

/-- **Freeness of top relative homology at a Morse index bound** over a principal ideal ring
without zero divisors (in any universe, including `ℤ`): if `a ≤ b` are regular values with compact
band `f⁻¹[a, b]` and every critical point in `f⁻¹(a, b]` has Morse index at most `d`, then
`H_d({f ≤ b}, {f ≤ a}; P)` is a free `k`-module for any projective `k`-module `P`. -/
theorem IsMorse.free_singularHomology_sublevelPair_of_manifoldMorseIndex_le
    (hf : IsMorse I f) {k : Type v} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k]
    (P : ModuleCat.{u} k) [Module.Projective k P]
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) {d : ℕ}
    (hd : ∀ x ∈ criticalPoints I f, f x ∈ Ioc a b → manifoldMorseIndex I f x ≤ d) :
    Module.Free k ((sublevelPair f hab).singularHomology P d : ModuleCat k) := by
  by_cases! hP : Subsingleton P
  · have hP₀ : IsZero P := ModuleCat.isZero_iff_subsingleton.2 hP
    have hX : IsZero ((TopPair.toSSetPair.obj (sublevelPair f hab)).right.chainComplex P) :=
      (Functor.isZero_iff _).1 ((SSet.chainComplexFunctor (ModuleCat.{u} k)).map_isZero hP₀) _
    have hQ : IsZero ((sublevelPair f hab).singularChainComplex P) :=
      hX.of_epi ((sublevelPair f hab).singularChainComplexπ P)
    have : Subsingleton ((sublevelPair f hab).singularHomology P d : ModuleCat k) :=
      ModuleCat.isZero_iff_subsingleton.1
        ((HomologicalComplex.homologyFunctor _ _ d).map_isZero hQ)
    exact Module.Free.of_subsingleton k _
  · -- A nontrivial projective module over a PID is free on a nonempty basis, so `k` embeds in `P`
    -- and `Small.{u} k` holds, making `ModuleCat.{u} k` hereditary.
    have : Module.Free k P :=
      .of_injective_of_projective_of_isPrincipalIdealRing .id Function.injective_id
    let b := Module.Free.chooseBasis k P
    let i := b.index_nonempty.some
    have : Small.{u} k := small_of_injective (f := (· • b i)) fun r s hrs ↦ by
      simpa using congr(b.coord i $hrs)
    have : Projective ((sublevelPair f hab).singularHomology P d) :=
      hf.projective_singularHomology_sublevelPair_of_manifoldMorseIndex_le P hab hcompact ha hb hd
    exact .of_injective_of_projective_of_isPrincipalIdealRing .id Function.injective_id

/-- **Vanishing of relative singular cohomology above a Morse index bound** over any hereditary
commutative ring `k` (in any universe, including `ℤ`): if `a ≤ b` are regular values with compact
band `f⁻¹[a, b]` and every critical point in `f⁻¹(a, b]` has Morse index at most `d`, then
`Hⁿ({f ≤ b}, {f ≤ a}; R, N) = 0` for every `n > d`, every projective `R`, and every `k`-module
`N`. -/
theorem IsMorse.isZero_singularCohomology_sublevelPair_of_manifoldMorseIndex_le
    (hf : IsMorse I f) {k : Type v} [CommRing k]
    [∀ V : ModuleCat.{u} k, HasProjectiveDimensionLE V 1] (R N : ModuleCat.{u} k)
    [Module.Projective k R] {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) {d n : ℕ}
    (hd : ∀ x ∈ criticalPoints I f, f x ∈ Ioc a b → manifoldMorseIndex I f x ≤ d) (hn : d < n) :
    IsZero ((sublevelPair f hab).singularCohomology R k N n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.zero_le d |>.trans_lt hn)).symm⟩
  have hdm : d ≤ m := Nat.le_of_lt_succ hn
  have : Projective ((sublevelPair f hab).singularHomology R m) :=
    hf.projective_singularHomology_sublevelPair_of_manifoldMorseIndex_le R hab hcompact ha hb
      fun x hx hxI ↦ (hd x hx hxI).trans hdm
  exact (sublevelPair f hab).isZero_singularCohomology_succ_of_projective_homology R N m
    (hf.isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le hab hcompact ha hb
      (fun p hp ↦ hd p hp.1 ⟨hp.2.1.lt_of_ne fun h ↦
        (isRegularValue_iff_notMem_image_criticalPoints.1 ha) ⟨p, hp.1, h.symm⟩, hp.2.2⟩) R hn)

end Band

section Sublevel

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- If a sublevel `{f ≤ b}` is compact, choosing `a` strictly below `b` and strictly below the
minimum of `f` on `{f ≤ b}` realizes `({f ≤ b}, ∅)` as a compact band `f⁻¹[a, b]` with regular lower
endpoint `a`. -/
private theorem IsMorse.exists_sublevelPair_empty_of_isCompact_sublevel
    (hf : IsMorse I f) {b : ℝ} (hcompact : IsCompact {x : M | f x ≤ b}) :
    ∃ a : ℝ, ∃ hab : a ≤ b, IsEmpty (sublevelPair f hab).snd ∧
      IsCompact (f ⁻¹' Icc a b) ∧ IsRegularValue I 𝓘(ℝ) f a ∧
      ∀ x, f x ≤ b → f x ∈ Ioc a b := by
  have hfc : Continuous f := hf.contMDiff.continuous
  obtain ⟨l, hl⟩ := (hcompact.image hfc).bddBelow
  let a := min (l - 1) (b - 1)
  have hab : a ≤ b := (min_le_right _ _).trans (by linarith)
  have hgt {x : M} (hx : f x ≤ b) : a < f x :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith [hl ⟨x, hx, rfl⟩])
  have hempty : ∀ x : M, ¬ f x ≤ a := fun x hxa ↦ (hgt (hxa.trans hab)).not_ge hxa
  have heq : f ⁻¹' Icc a b = {x : M | f x ≤ b} :=
    Set.ext fun x ↦ ⟨fun hx ↦ hx.2, fun hx ↦ ⟨(hgt hx).le, hx⟩⟩
  refine ⟨a, hab, ⟨fun x ↦ hempty x.1 x.2⟩, heq ▸ hcompact,
    isRegularValue_iff_notMem_image_criticalPoints.2 fun ⟨x, _, hxa⟩ ↦ hempty x hxa.le,
    fun x hx ↦ ⟨hgt hx, hx⟩⟩

/-- **Top singular homology of a compact regular sublevel set is projective** over a hereditary
abelian category when `R` is projective and all critical points in `{f ≤ b}` have index at most
`d`. -/
theorem IsMorse.projective_singularHomology_sublevel_of_manifoldMorseIndex_le
    (hf : IsMorse I f) {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A]
    [∀ V : A, HasProjectiveDimensionLE V 1] (R : A) [Projective R]
    {b : ℝ} (hcompact : IsCompact {x : M | f x ≤ b}) (hb : IsRegularValue I 𝓘(ℝ) f b) {d : ℕ}
    (hd : ∀ x ∈ criticalPoints I f, f x ≤ b → manifoldMorseIndex I f x ≤ d) :
    Projective (((AlgebraicTopology.singularHomologyFunctor.{u} A d).obj R).obj
      (TopCat.of {x : M | f x ≤ b})) := by
  obtain ⟨a, hab, _, hc, ha, _⟩ := hf.exists_sublevelPair_empty_of_isCompact_sublevel hcompact
  exact Projective.of_iso (asIso ((sublevelPair f hab).singularHomologyπ R d)).symm
    (hf.projective_singularHomology_sublevelPair_of_manifoldMorseIndex_le R hab hc ha hb
      fun x hx hxab ↦ hd x hx hxab.2)

/-- **Top singular homology of a compact regular sublevel set is free over a PID.** Over any
principal ideal ring `k` without zero divisors (in any universe, including `ℤ`), if `{f ≤ b}` is
compact with regular value `b` and every critical point in `{f ≤ b}` has Morse index at most `d`,
then `H_d({f ≤ b}; P)` is a free `k`-module for any projective `k`-module `P`, with no compactness
assumption on `M`. -/
theorem IsMorse.free_singularHomology_sublevel_of_manifoldMorseIndex_le
    (hf : IsMorse I f) {k : Type v} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k]
    (P : ModuleCat.{u} k) [Module.Projective k P]
    {b : ℝ} (hcompact : IsCompact {x : M | f x ≤ b}) (hb : IsRegularValue I 𝓘(ℝ) f b) {d : ℕ}
    (hd : ∀ x ∈ criticalPoints I f, f x ≤ b → manifoldMorseIndex I f x ≤ d) :
    Module.Free k (((AlgebraicTopology.singularHomologyFunctor.{u} (ModuleCat.{u} k) d).obj P).obj
      (TopCat.of {x : M | f x ≤ b})) := by
  obtain ⟨a, hab, _, hc, ha, _⟩ := hf.exists_sublevelPair_empty_of_isCompact_sublevel hcompact
  have hfree := hf.free_singularHomology_sublevelPair_of_manifoldMorseIndex_le P hab hc ha hb
    fun x hx hxab ↦ hd x hx hxab.2
  exact Module.Free.of_equiv' hfree
    (asIso ((sublevelPair f hab).singularHomologyπ (C := ModuleCat.{u} k) P d)).symm.toLinearEquiv

/-- **Singular cohomology of a compact regular sublevel set vanishes above a Morse index bound**
over any hereditary commutative ring `k` (in any universe, including `ℤ`), without assuming `M` is
compact. -/
theorem IsMorse.isZero_singularCohomology_sublevel_of_manifoldMorseIndex_le
    (hf : IsMorse I f) {k : Type v} [CommRing k]
    [∀ V : ModuleCat.{u} k, HasProjectiveDimensionLE V 1] (R N : ModuleCat.{u} k)
    [Module.Projective k R] {b : ℝ} (hcompact : IsCompact {x : M | f x ≤ b})
    (hb : IsRegularValue I 𝓘(ℝ) f b) {d n : ℕ}
    (hd : ∀ x ∈ criticalPoints I f, f x ≤ b → manifoldMorseIndex I f x ≤ d) (hn : d < n) :
    IsZero ((TopCat.of {x : M | f x ≤ b}).singularCohomology R k N n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.zero_le d |>.trans_lt hn)).symm⟩
  have hdm : d ≤ m := Nat.le_of_lt_succ hn
  have : Projective (((AlgebraicTopology.singularHomologyFunctor.{u} (ModuleCat.{u} k) m).obj R).obj
      (TopCat.of {x : M | f x ≤ b})) :=
    hf.projective_singularHomology_sublevel_of_manifoldMorseIndex_le R hcompact hb
      fun x hx hxb ↦ (hd x hx hxb).trans hdm
  exact (TopCat.of {x : M | f x ≤ b}).isZero_singularCohomology_succ_of_projective_homology R N m
    (hf.isZero_singularHomology_sublevel_of_manifoldMorseIndex_le hcompact hb hd R hn)

end Sublevel

section Compact

variable [CompactSpace M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- On a compact manifold `M`, choosing `b` strictly above `range f` identifies `{f ≤ b}` with `M`
by a homeomorphism, with `b` a regular value and `{f ≤ b}` compact. -/
private theorem IsMorse.exists_sublevel_homeomorph_of_compactSpace (hf : IsMorse I f) :
    ∃ b : ℝ, IsCompact {x : M | f x ≤ b} ∧ IsRegularValue I 𝓘(ℝ) f b ∧
      Nonempty ({x : M | f x ≤ b} ≃ₜ M) := by
  obtain ⟨t, ht⟩ := (isCompact_range hf.contMDiff.continuous).bddAbove
  have hb (x : M) : f x < t + 1 := by linarith [ht (mem_range_self x)]
  have heq : {x : M | f x ≤ t + 1} = univ := eq_univ_of_forall fun x ↦ (hb x).le
  exact ⟨t + 1, heq ▸ isCompact_univ,
    isRegularValue_iff_notMem_image_criticalPoints.2 fun ⟨x, _, hxb⟩ ↦ (hb x).ne hxb,
    ⟨(Homeomorph.setCongr heq).trans (Homeomorph.Set.univ M)⟩⟩

/-- **Singular homology of a compact manifold vanishes above a Morse index bound**, for any
coefficient object `R` in an abelian category with coproducts (without the exact sequential colimit
hypothesis of `TauCeti.IsMorse.isZero_singularHomology_of_manifoldMorseIndex_le`). -/
theorem IsMorse.isZero_singularHomology_of_compactSpace_of_manifoldMorseIndex_le
    (hf : IsMorse I f) {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A)
    {d n : ℕ} (hd : ∀ x ∈ criticalPoints I f, manifoldMorseIndex I f x ≤ d) (hn : d < n) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor.{u} A n).obj R).obj (TopCat.of M)) := by
  obtain ⟨b, hc, hb, ⟨e⟩⟩ := hf.exists_sublevel_homeomorph_of_compactSpace
  exact (hf.isZero_singularHomology_sublevel_of_manifoldMorseIndex_le hc hb
    (fun x hx _ ↦ hd x hx) R hn).of_iso (e.toHomotopyEquiv.singularHomologyIso R n).symm

/-- **Top singular homology of a compact manifold is projective** over a hereditary abelian
category when `R` is projective and every critical point of `f` has Morse index at most `d`. -/
theorem IsMorse.projective_singularHomology_of_manifoldMorseIndex_le
    (hf : IsMorse I f) {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A]
    [∀ V : A, HasProjectiveDimensionLE V 1] (R : A) [Projective R]
    {d : ℕ} (hd : ∀ x ∈ criticalPoints I f, manifoldMorseIndex I f x ≤ d) :
    Projective (((AlgebraicTopology.singularHomologyFunctor.{u} A d).obj R).obj (TopCat.of M)) := by
  obtain ⟨b, hc, hb, ⟨e⟩⟩ := hf.exists_sublevel_homeomorph_of_compactSpace
  exact Projective.of_iso (e.toHomotopyEquiv.singularHomologyIso R d)
    (hf.projective_singularHomology_sublevel_of_manifoldMorseIndex_le R hc hb fun x hx _ ↦ hd x hx)

/-- **Top singular homology of a compact manifold is free over a PID.** Over any principal ideal
ring `k` without zero divisors (in any universe, including `ℤ`), if `M` is compact and every
critical point of `f` has Morse index at most `d`, then `H_d(M; P)` is a free `k`-module for any
projective `k`-module `P`. -/
theorem IsMorse.free_singularHomology_of_manifoldMorseIndex_le
    (hf : IsMorse I f) {k : Type v} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k]
    (P : ModuleCat.{u} k) [Module.Projective k P]
    {d : ℕ} (hd : ∀ x ∈ criticalPoints I f, manifoldMorseIndex I f x ≤ d) :
    Module.Free k (((AlgebraicTopology.singularHomologyFunctor.{u} (ModuleCat.{u} k) d).obj P).obj
      (TopCat.of M)) := by
  obtain ⟨b, hc, hb, ⟨e⟩⟩ := hf.exists_sublevel_homeomorph_of_compactSpace
  have hfree :=
    hf.free_singularHomology_sublevel_of_manifoldMorseIndex_le P hc hb fun x hx _ ↦ hd x hx
  exact Module.Free.of_equiv' hfree (e.toHomotopyEquiv.singularHomologyIso P d).toLinearEquiv

/-- **Singular cohomology of a compact manifold vanishes above a Morse index bound** over any
hereditary commutative ring `k` (in any universe, including `ℤ`). -/
theorem IsMorse.isZero_singularCohomology_of_manifoldMorseIndex_le
    (hf : IsMorse I f) {k : Type v} [CommRing k]
    [∀ V : ModuleCat.{u} k, HasProjectiveDimensionLE V 1] (R N : ModuleCat.{u} k)
    [Module.Projective k R] {d n : ℕ}
    (hd : ∀ x ∈ criticalPoints I f, manifoldMorseIndex I f x ≤ d) (hn : d < n) :
    IsZero ((TopCat.of M).singularCohomology R k N n) := by
  obtain ⟨b, hc, hb, ⟨e⟩⟩ := hf.exists_sublevel_homeomorph_of_compactSpace
  exact (hf.isZero_singularCohomology_sublevel_of_manifoldMorseIndex_le R N hc hb
    (fun x hx _ ↦ hd x hx) hn).of_iso (e.toHomotopyEquiv.singularCohomologyIso R k N n)

end Compact

end TauCeti
