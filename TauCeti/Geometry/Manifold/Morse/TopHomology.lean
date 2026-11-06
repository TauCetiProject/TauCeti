/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Free
public import TauCeti.AlgebraicTopology.Cellular.TopHomology
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
public import TauCeti.AlgebraicTopology.Singular.Triple.Free
public import TauCeti.Geometry.Manifold.Morse.Cell.Band

/-!
# Homology in the degree of the largest Morse index, and cohomology above it

Let `f` be a Morse function on a boundaryless finite-dimensional manifold `M`, and let `a ≤ b` be
regular values with compact band `f⁻¹[a, b]`. If every critical point of `f` in the band has index
at most `d`, then the sublevel `M_b = {f ≤ b}` is obtained from `M_a = {f ≤ a}`, up to homotopy, by
attaching cells of dimension at most `d`. The relative singular homology `Hₙ(M_b, M_a)` then
vanishes for `n > d`
(`TauCeti.IsMorse.isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le`), and this file
adds that `H_d(M_b, M_a; V)` is free for every free module `V` over a principal ideal ring without
zero divisors; for instance `H_d(M_b, M_a; ℤ)` is free abelian
(`TauCeti.IsMorse.free_singularHomology_sublevelPair_of_manifoldMorseIndex_le`).

The same holds for a compact regular sublevel `M_b`, which is such a band over the empty sublevel
(`TauCeti.IsMorse.free_singularHomology_sublevel_of_manifoldMorseIndex_le`), and on a compact
manifold, which is itself one
(`TauCeti.IsMorse.free_singularHomology_of_compactSpace_of_manifoldMorseIndex_le`).
If `f` is proper and bounded below and all its critical points have index at most `d`, then
`H_d(M; V)` is free with no compactness assumption on `M`
(`TauCeti.IsMorse.free_singularHomology_of_manifoldMorseIndex_le`). Along an exhaustion of `M` by
regular sublevels `M_{a₀} ⊆ M_{a₁} ⊆ ⋯`, the homology `H_d(M; V)` is the colimit of the
`H_d(M_{aⱼ}; V)`. Since `H_{d+1}(M_{aⱼ₊₁}, M_{aⱼ}; V)` vanishes, the long exact sequence of the pair
makes each map `H_d(M_{aⱼ}; V) ⟶ H_d(M_{aⱼ₊₁}; V)` injective with cokernel embedded in the free
module `H_d(M_{aⱼ₊₁}, M_{aⱼ}; V)`, and such a sequential colimit is free
(`ModuleCat.free_of_isColimit_of_exact`). The rank may be infinite.

Together with the vanishing of homology above `d`, the universal coefficient theorem over the
hereditary ring `k` then shows that cohomology vanishes above degree `d`: for every `k`-module
`N`, `Hⁿ(M_b, M_a; V, N) = 0` and, on a compact manifold, `Hⁿ(M; V, N) = 0` for `n > d`
(`TauCeti.IsMorse.isZero_singularCohomology_sublevelPair_of_manifoldMorseIndex_le` and
`TauCeti.IsMorse.isZero_singularCohomology_of_compactSpace_of_manifoldMorseIndex_le`). In degree
`d + 1` this uses the freeness of `H_d`, which kills the term `Ext¹(H_d, N)`. None of these
statements says that the degree-`d` integral cohomology is torsion-free: it contains
`Ext¹(H_{d-1}, ℤ)`, which can be nonzero.

Freeness is proved along Milnor's induction over the critical levels,
`TauCeti.IsMorse.band_induction`, together with the vanishing of `H_{d+1}`. Across one critical
level the pair has the relative homology of a finite CW pair with one `i`-cell for each critical
point of index `i` (`TauCeti.IsMorse.exists_relCWComplex_isIso_singularHomologyMap_sublevelPair`),
which has no `(d + 1)`-cells; there vanishing is
`TauCeti.isZero_singularHomology_complexBasePair_of_isEmpty_cell` and freeness is
`TauCeti.free_singularHomology_complexBasePair_of_isEmpty_cell`. Along a triple of sublevels
`M_a ⊆ M_m ⊆ M_b` the long exact sequence propagates vanishing
(`TauCeti.TopTriple.isZero_singularHomology_totalPair`) and, since `H_{d+1}(M_b, M_m)` vanishes,
freeness (`TauCeti.TopTriple.free_singularHomology_totalPair`).

## Main results

* `TauCeti.IsMorse.free_singularHomology_sublevelPair_of_manifoldMorseIndex_le`,
  `TauCeti.IsMorse.free_singularHomology_sublevel_of_manifoldMorseIndex_le` and
  `TauCeti.IsMorse.free_singularHomology_of_compactSpace_of_manifoldMorseIndex_le`: freeness of
  homology in the degree of the largest index, for compact bands, compact regular sublevels and
  compact manifolds.
* `TauCeti.IsMorse.free_singularHomology_of_manifoldMorseIndex_le`: the same for a manifold with a
  proper Morse function bounded below.
* `TauCeti.IsMorse.isZero_singularCohomology_sublevelPair_of_manifoldMorseIndex_le` and
  `TauCeti.IsMorse.isZero_singularCohomology_of_compactSpace_of_manifoldMorseIndex_le`: vanishing
  of cohomology above the largest index.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 and Section 7.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Lemma 2.34, and Section 3.1, Theorem 3.2.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology Topology.RelCWComplex
open scoped ContDiff Manifold

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ}

/-- **Homology is free in the degree of the largest index.** Let `f` be a Morse function, `a ≤ b`
regular values with compact band `f⁻¹[a, b]`, and suppose that every critical point in the band has
index at most `d`. Then `H_d({f ≤ b}, {f ≤ a}; V)` is free for every free module `V` over a
principal ideal ring without zero divisors. With integral coefficients it is free abelian. -/
theorem IsMorse.free_singularHomology_sublevelPair_of_manifoldMorseIndex_le (hf : IsMorse I f)
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) {d : ℕ}
    (hd : ∀ p ∈ criticalPoints I f ∩ f ⁻¹' Icc a b, manifoldMorseIndex I f p ≤ d)
    {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k] (V : ModuleCat.{u} k)
    [Module.Free k V] :
    Module.Free k ((sublevelPair f hab).singularHomology V d : ModuleCat k) := by
  -- The vanishing of `H_{d+1}` is carried along, since the step along a triple needs it.
  refine (hf.band_induction (P := fun s t hst ↦
      IsZero ((sublevelPair f hst).singularHomology V (d + 1)) ∧
        Module.Free k ((sublevelPair f hst).singularHomology V d : ModuleCat k))
    hab hcompact ha hb ?_ ?_ ?_).2
  · -- A band without critical points has no relative homology.
    intro s t hst hcompact' hcrit
    have h := isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero hf.contMDiff hst hcompact'
      (fun x hsx hxt hx ↦ hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) ⟨hsx, hxt⟩) V
    have := ModuleCat.isZero_iff_subsingleton.1 (h d)
    exact ⟨h (d + 1), inferInstance⟩
  · -- One critical level: the cell pair has no `(d + 1)`-cells.
    intro p _ hap hpb δ hδ hcompact'
    obtain ⟨ε, hε, hεδ, C, _, _, hC, hcell, hiso⟩ :=
      hf.exists_relCWComplex_isIso_singularHomologyMap_sublevelPair hδ hcompact'
    refine ⟨ε, hε, hεδ, ?_⟩
    have : IsEmpty (cell C (d + 1)) := (hcell (d + 1)).some.isEmpty_congr.2
      ⟨fun q ↦ by
        have hq : f q.1.1 = f p := q.1.2.2
        have := hd q.1.1 ⟨q.1.2.1, by rw [mem_preimage, hq]; exact ⟨hap.le, hpb.le⟩⟩
        have := q.2
        lia⟩
    have hzero := isZero_singularHomology_complexBasePair_of_isEmpty_cell C V (d + 1)
    have hfree := free_singularHomology_complexBasePair_of_isEmpty_cell C V d
    rw [complexBasePair_eq_ofInclusion] at hzero hfree
    exact ⟨hzero.of_iso (@asIso _ _ _ _ _ (hiso V (d + 1))).symm,
      .of_equiv (@asIso _ _ _ _ _ (hiso V d)).toLinearEquiv⟩
  · -- Along a triple of sublevels, where `H_{d+1}` of the upper pair vanishes.
    intro s m t hsm hmt _ h₁ h₂
    let T := TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f hsm) (sublevel_mono f hmt)
    have : Module.Free k ((TopTriple.innerPair.obj T).singularHomology V d : ModuleCat k) := h₁.2
    have : Module.Free k ((TopTriple.outerPair.obj T).singularHomology V d : ModuleCat k) := h₂.2
    exact ⟨T.isZero_singularHomology_totalPair V (d + 1) h₁.1 h₂.1,
      T.free_singularHomology_totalPair V d h₂.1⟩

/-- **Homology of a compact regular sublevel is free in the degree of the largest index.** Let `f`
be a Morse function, let `b` be a regular value of `f` with compact sublevel `{f ≤ b}`, and suppose
every critical point in this sublevel has index at most `d`. Then `H_d({f ≤ b}; V)` is free for
every free module `V` over a principal ideal ring without zero divisors. -/
theorem IsMorse.free_singularHomology_sublevel_of_manifoldMorseIndex_le (hf : IsMorse I f)
    {b : ℝ} (hcompact : IsCompact {x | f x ≤ b}) (hb : IsRegularValue I 𝓘(ℝ) f b) {d : ℕ}
    (hd : ∀ p ∈ criticalPoints I f, f p ≤ b → manifoldMorseIndex I f p ≤ d)
    {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k] (V : ModuleCat.{u} k)
    [Module.Free k V] :
    Module.Free k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) d).obj V).obj
      (TopCat.of {x | f x ≤ b})) := by
  obtain ⟨a, hab, _, hband, ha⟩ :=
    exists_isEmpty_sublevelPair_of_isCompact_sublevel (I := I) hf.contMDiff.continuous hcompact
  have := hf.free_singularHomology_sublevelPair_of_manifoldMorseIndex_le hab hband ha hb
    (fun p hp ↦ hd p hp.1 hp.2.2) V
  -- Relative homology modulo the empty sublevel is the homology of `{f ≤ b}`.
  exact .of_equiv (asIso ((sublevelPair f hab).singularHomologyπ V d)).toLinearEquiv.symm

/-- **Homology of a compact manifold is free in the degree of the largest index.** If every
critical point of a Morse function on a compact boundaryless manifold `M` has index at most `d`,
then `H_d(M; V)` is free for every free module `V` over a principal ideal ring without zero
divisors. With integral coefficients it is free abelian. -/
theorem IsMorse.free_singularHomology_of_compactSpace_of_manifoldMorseIndex_le [CompactSpace M]
    (hf : IsMorse I f) {d : ℕ} (hd : ∀ x ∈ criticalPoints I f, manifoldMorseIndex I f x ≤ d)
    {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k] (V : ModuleCat.{u} k)
    [Module.Free k V] :
    Module.Free k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) d).obj V).obj
      (TopCat.of M)) := by
  obtain ⟨a, b, hab, hcompact, ha, hb, hf'⟩ :=
    exists_isRegularValue_forall_mem_Ioc (I := I) hf.contMDiff.continuous
  have := hf.free_singularHomology_sublevelPair_of_manifoldMorseIndex_le hab hcompact ha hb
    (fun x hx ↦ hd x hx.1) V
  exact .of_equiv (singularHomologyIsoSublevelPair hab (fun x ↦ (hf' x).1)
    (fun x ↦ (hf' x).2) V d).symm.toLinearEquiv

/-- **Homology is free in the degree of the largest index.** Let `f` be a proper Morse function,
bounded below, all of whose critical points have index at most `d`. Then `H_d(M; V)` is free for
every free module `V` over a principal ideal ring without zero divisors; in particular
`H_d(M; ℤ)` is free abelian. The manifold need not be compact, and `H_d(M; V)` may have infinite
rank. -/
theorem IsMorse.free_singularHomology_of_manifoldMorseIndex_le (hf : IsMorse I f)
    (hp : IsProperMap f) (hbdd : BddBelow (range f)) {d : ℕ}
    (hd : ∀ x ∈ criticalPoints I f, manifoldMorseIndex I f x ≤ d)
    {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k] (V : ModuleCat.{u} k)
    [Module.Free k V] :
    Module.Free k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) d).obj V).obj
      (TopCat.of M)) := by
  have hcont : Continuous f := hf.contMDiff.continuous
  -- `H_d(M)` is the colimit of the homology of the regular sublevels `{f ≤ a j}`.
  obtain ⟨a, ha, hreg, hcompact, hc⟩ :=
    hf.exists_regular_sublevel_isColimit_singularHomology hp hbdd
  -- Each step `({f ≤ a (j + 1)}, {f ≤ a j})` is a compact band between regular values.
  have hband (j : ℕ) : IsCompact (f ⁻¹' Icc (a j) (a (j + 1))) :=
    (hcompact (j + 1)).of_isClosed_subset (isClosed_Icc.preimage hcont) fun x hx ↦ hx.2
  have hstep (j : ℕ) := ha (Nat.le_succ j)
  have hfree (j : ℕ) := hf.free_singularHomology_sublevelPair_of_manifoldMorseIndex_le (hstep j)
    (hband j) (hreg j) (hreg (j + 1)) (fun x hx ↦ hd x hx.1) V
  have hzero (j : ℕ) := hf.isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le (hstep j)
    (hband j) (hreg j) (hreg (j + 1)) (fun x hx ↦ hd x hx.1) V (lt_add_one d)
  have : Module.Free k (((ha.functor ⋙ sublevelFunctor f) ⋙
      (AlgebraicTopology.singularHomologyFunctor _ d).obj V).obj 0) :=
    hf.free_singularHomology_sublevel_of_manifoldMorseIndex_le (hcompact 0) (hreg 0)
      (fun x hx _ ↦ hd x hx) V
  -- In the long exact sequence of the pair `({f ≤ a (j + 1)}, {f ≤ a j})`, the map
  -- `H_d({f ≤ a j}) ⟶ H_d({f ≤ a (j + 1)})`, induced by the embedding
  -- `(sublevelFunctor f).map _ = (sublevelPair f _).map`, is injective since `H_{d+1}` of the pair
  -- vanishes, and is followed by the map into the free module `H_d({f ≤ a (j + 1)}, {f ≤ a j})`.
  exact ModuleCat.free_of_isColimit_of_exact (hc V d).some
    (fun j ↦ (ModuleCat.mono_iff_injective _).1
      ((sublevelPair f (hstep j)).mono_homologyMap_map_of_isZero V (hzero j)))
    (fun j ↦ ((sublevelPair f (hstep j)).singularHomologyπ V d).hom) fun j ↦
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        ((sublevelPair f (hstep j)).singularHomology_exact_space V d)

/-- **Cohomology of a compact band vanishes above the largest index.** Let `f` be a Morse function,
`a ≤ b` regular values with compact band `f⁻¹[a, b]`, and suppose that every critical point in the
band has index at most `d`. Then `Hⁿ({f ≤ b}, {f ≤ a}; V, N) = 0` for every `n > d`, every free
module `V` over a principal ideal ring `k` without zero divisors and every `k`-module `N`. For
instance the integral cohomology of the pair vanishes above degree `d`. -/
theorem IsMorse.isZero_singularCohomology_sublevelPair_of_manifoldMorseIndex_le (hf : IsMorse I f)
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) {d : ℕ}
    (hd : ∀ p ∈ criticalPoints I f ∩ f ⁻¹' Icc a b, manifoldMorseIndex I f p ≤ d)
    {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k] (V N : ModuleCat.{u} k)
    [Module.Free k V] {n : ℕ} (hn : d < n) :
    IsZero ((sublevelPair f hab).singularCohomology V k N n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
  -- `Hₘ` is free if `m = d` and zero if `m > d`, so projective either way.
  have : Projective ((sublevelPair f hab).singularHomology V m) := by
    rcases (Nat.lt_succ_iff.1 hn).eq_or_lt with rfl | hdm
    · have := hf.free_singularHomology_sublevelPair_of_manifoldMorseIndex_le hab hcompact ha hb hd V
      infer_instance
    · exact (hf.isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le hab hcompact ha hb hd
        V hdm).projective
  exact TopPair.isZero_singularCohomology_succ_of_projective_homology _ V N m
    (hf.isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le hab hcompact ha hb hd V hn)

/-- **Cohomology of a compact manifold vanishes above the largest index.** If every critical point
of a Morse function on a compact boundaryless manifold `M` has index at most `d`, then
`Hⁿ(M; V, N) = 0` for every `n > d`, every free module `V` over a principal ideal ring `k` without
zero divisors and every `k`-module `N`. For instance the integral cohomology of `M` vanishes above
degree `d`. -/
theorem IsMorse.isZero_singularCohomology_of_compactSpace_of_manifoldMorseIndex_le [CompactSpace M]
    (hf : IsMorse I f) {d : ℕ} (hd : ∀ x ∈ criticalPoints I f, manifoldMorseIndex I f x ≤ d)
    {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k] (V N : ModuleCat.{u} k)
    [Module.Free k V] {n : ℕ} (hn : d < n) :
    IsZero ((TopCat.of M).singularCohomology V k N n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
  -- `Hₘ(M)` is free if `m = d` and zero if `m > d`, so projective either way.
  have : Projective (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) m).obj V).obj
      (TopCat.of M)) := by
    rcases (Nat.lt_succ_iff.1 hn).eq_or_lt with rfl | hdm
    · have := hf.free_singularHomology_of_compactSpace_of_manifoldMorseIndex_le hd V
      infer_instance
    · exact (hf.isZero_singularHomology_of_compactSpace_of_manifoldMorseIndex_le hd V
        hdm).projective
  exact TopCat.isZero_singularCohomology_succ_of_projective_homology _ V N m
    (hf.isZero_singularHomology_of_compactSpace_of_manifoldMorseIndex_le hd V hn)

end TauCeti
