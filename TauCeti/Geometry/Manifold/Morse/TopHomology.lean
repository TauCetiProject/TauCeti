/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Colimits
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

On a compact manifold `M` itself is such a band, over the empty sublevel, so `H_d(M; V)` is free
(`TauCeti.IsMorse.free_singularHomology_of_compactSpace_of_manifoldMorseIndex_le`). The same holds
for a proper Morse function bounded below on a possibly noncompact `M`, all of whose critical
points have index at most `d` (`TauCeti.IsMorse.free_singularHomology_of_manifoldMorseIndex_le`).
Then `H_d(M; V)` is the colimit of the homology of a regular sublevel exhaustion
`M_{a₁} ⊆ M_{a₂} ⊆ ⋯`; the vanishing of `H_{d+1}(M_{a_{j+1}}, M_{a_j})` makes the maps
`H_d(M_{a_j}) → H_d(M_{a_{j+1}})` injective, with cokernels embedded in the free modules
`H_d(M_{a_{j+1}}, M_{a_j})`, and such a colimit is free (`ModuleCat.free_of_isColimit`).

Together with the vanishing of homology above `d`, the universal coefficient theorem over the
hereditary ring `k` then shows that cohomology vanishes above degree `d`: for every `k`-module
`N`, `Hⁿ(M_b, M_a; V, N) = 0` and, for a proper Morse function bounded below or on a compact
manifold, `Hⁿ(M; V, N) = 0` for `n > d`
(`TauCeti.IsMorse.isZero_singularCohomology_sublevelPair_of_manifoldMorseIndex_le`,
`TauCeti.IsMorse.isZero_singularCohomology_of_manifoldMorseIndex_le` and
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
  `TauCeti.IsMorse.free_singularHomology_of_compactSpace_of_manifoldMorseIndex_le` and
  `TauCeti.IsMorse.free_singularHomology_of_manifoldMorseIndex_le`: freeness of homology in the
  degree of the largest index.
* `TauCeti.IsMorse.isZero_singularCohomology_sublevelPair_of_manifoldMorseIndex_le`,
  `TauCeti.IsMorse.isZero_singularCohomology_of_compactSpace_of_manifoldMorseIndex_le` and
  `TauCeti.IsMorse.isZero_singularCohomology_of_manifoldMorseIndex_le`: vanishing of cohomology
  above the largest index.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 and Section 7.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Lemma 2.34, and Section 3.1, Theorem 3.2.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits Module Set Topology Topology.RelCWComplex
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

/-- **Homology of a compact manifold is free in the degree of the largest index.** If every
critical point of a Morse function on a compact boundaryless manifold `M` has index at most `d`,
then `H_d(M; V)` is free for every free module `V` over a principal ideal ring without zero
divisors. With integral coefficients it is free abelian. -/
theorem IsMorse.free_singularHomology_of_compactSpace_of_manifoldMorseIndex_le [CompactSpace M]
    (hf : IsMorse I f) {d : ℕ} (hd : ∀ x ∈ criticalPoints I f, manifoldMorseIndex I f x ≤ d)
    {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k] (V : ModuleCat.{u} k)
    [Module.Free k V] :
    Module.Free k (((singularHomologyFunctor (ModuleCat.{u} k) d).obj V).obj
      (TopCat.of M)) := by
  obtain ⟨a, b, hab, hcompact, ha, hb, hf'⟩ :=
    exists_isRegularValue_forall_mem_Ioc (I := I) hf.contMDiff.continuous
  have := hf.free_singularHomology_sublevelPair_of_manifoldMorseIndex_le hab hcompact ha hb
    (fun x hx ↦ hd x hx.1) V
  exact .of_equiv (singularHomologyIsoSublevelPair hab (fun x ↦ (hf' x).1)
    (fun x ↦ (hf' x).2) V d).symm.toLinearEquiv

/-- **Homology of a manifold with a proper Morse function is free in the degree of the largest
index.** Let `f` be a proper Morse function, bounded below, all of whose critical points have index
at most `d`. Then `H_d(M; V)` is free for every free module `V` over a principal ideal ring without
zero divisors. With integral coefficients it is free abelian. `M` need not be compact, and the
homology need not be finitely generated. -/
theorem IsMorse.free_singularHomology_of_manifoldMorseIndex_le (hf : IsMorse I f)
    (hp : IsProperMap f) (hbdd : BddBelow (range f)) {d : ℕ}
    (hd : ∀ x ∈ criticalPoints I f, manifoldMorseIndex I f x ≤ d)
    {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k] (V : ModuleCat.{u} k)
    [Module.Free k V] :
    Module.Free k (((singularHomologyFunctor (ModuleCat.{u} k) d).obj V).obj (TopCat.of M)) := by
  obtain ⟨a, K, hmono, -, hreg, hK, hK0, -⟩ := hf.exists_regular_sublevel_exhaustion hp hbdd
  have hKa (j : ℕ) : K j = {x | f x ≤ a j} := hK j
  have hband {i j : ℕ} (hij : i ≤ j) : IsCompact (f ⁻¹' Icc (a i) (a j)) :=
    (K.isCompact j).of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous)
      fun x hx ↦ by simpa [hKa j] using hx.2
  have hpair {i j : ℕ} (hij : i ≤ j) :=
    hf.free_singularHomology_sublevelPair_of_manifoldMorseIndex_le (hmono.monotone hij)
      (hband hij) (hreg i) (hreg j) (fun x hx ↦ hd x hx.1) V
  -- The nonempty regular sublevels `{f ≤ a (j + 1)}` and their inclusions into `M` form a cocone
  -- of embeddings, and every compact subset of `M` lies in one of them.
  let F : ℕ ⥤ TopCat.{u} :=
    { obj j := TopCat.of {x | f x ≤ a (j + 1)}
      map h := TopCat.ofHom (ContinuousMap.inclusion
        (sublevel_mono f (hmono.monotone (Nat.succ_le_succ h.le)))) }
  let c : Cocone F :=
    { pt := TopCat.of M
      ι := { app j := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ } }
  have hc : IsColimit (((singularHomologyFunctor (ModuleCat.{u} k) d).obj V).mapCocone c) :=
    isColimitMapCoconeSingularHomology V d c (fun _ ↦ IsEmbedding.subtypeVal) fun L hL ↦ by
      obtain ⟨j, hj⟩ := K.exists_superset_of_isCompact hL
      refine ⟨j, fun x hx ↦ ⟨⟨x, ?_⟩, rfl⟩⟩
      exact sublevel_mono f (hmono.monotone j.le_succ) (by simpa [hKa j] using hj hx)
  refine ModuleCat.free_of_isColimit _ hc ?_ (fun j ↦ ?_) fun j ↦ ?_
  · -- The first sublevel is a band over the empty sublevel `{f ≤ a 0}`.
    have : IsEmpty (sublevelPair f (hmono.monotone (Nat.zero_le 1))).snd :=
      ⟨fun x ↦ by simpa [← hKa 0, hK0] using x.2⟩
    have hπ : IsIso ((sublevelPair f (hmono.monotone (Nat.zero_le 1))).singularHomologyπ V d) :=
      inferInstance
    have := hpair (Nat.zero_le 1)
    exact .of_equiv (@asIso _ _ _ _ _ hπ).symm.toLinearEquiv
  · -- `H_{d+1}` of the band between consecutive sublevels vanishes.
    have h := hmono.monotone (Nat.le_succ (j + 1))
    have := (sublevelPair f h).mono_homologyMap_map_of_isZero V
      (hf.isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le h (hband (j + 1).le_succ)
        (hreg _) (hreg _) (fun x hx ↦ hd x hx.1) V d.lt_succ_self)
    exact (ModuleCat.mono_iff_injective _).1 this
  · -- The cokernel embeds in the free module `H_d` of the band between consecutive sublevels.
    have h := hmono.monotone (Nat.le_succ (j + 1))
    have hex := ((sublevelPair f h).singularHomology_exact_space V d).moduleCat_range_eq_ker
    have := hpair (j + 1).le_succ
    let e := (Submodule.quotEquivOfEq _ _ hex).trans (LinearMap.quotKerEquivRange _)
    have : Module.Free k (LinearMap.range (ShortComplex.mk _ _
        ((sublevelPair f h).homologyMap_comp_singularHomologyπ V d)).g.hom) :=
      Submodule.free_of_isPrincipalIdealRing _
    exact .of_equiv e.symm

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

/-- **Cohomology of a manifold with a proper Morse function vanishes above the largest index.** Let
`f` be a proper Morse function, bounded below, all of whose critical points have index at most `d`.
Then the singular cohomology `Hⁿ(M; V, N)` vanishes for every `n > d`, every free module `V` over a
principal ideal ring `k` without zero divisors and every `k`-module `N`; for instance
`Hⁿ(M; ℤ) = 0` for `n > d`. -/
theorem IsMorse.isZero_singularCohomology_of_manifoldMorseIndex_le (hf : IsMorse I f)
    (hp : IsProperMap f) (hbdd : BddBelow (range f)) {d : ℕ}
    (hd : ∀ x ∈ criticalPoints I f, manifoldMorseIndex I f x ≤ d)
    {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k] (V N : ModuleCat.{u} k)
    [Module.Free k V] {n : ℕ} (hn : d < n) :
    IsZero ((TopCat.of M).singularCohomology V k N n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
  have hzero {j : ℕ} (hj : d < j) :=
    hf.isZero_singularHomology_of_manifoldMorseIndex_le hp hbdd hd V hj
  -- `Hₘ` is free for `m = d` and zero for `m > d`, hence projective, and `Hₘ₊₁` is zero.
  have : Projective (((singularHomologyFunctor (ModuleCat.{u} k) m).obj V).obj (TopCat.of M)) := by
    rcases (show d ≤ m by lia).eq_or_lt with rfl | hlt
    · have := hf.free_singularHomology_of_manifoldMorseIndex_le hp hbdd hd V
      infer_instance
    · exact (hzero hlt).projective
  exact TopCat.isZero_singularCohomology_succ_of_projective_homology _ V N m (hzero hn)

/-- **Cohomology of a compact manifold vanishes above the largest index.** If every critical point
of a Morse function on a compact boundaryless manifold `M` has index at most `d`, then
`Hⁿ(M; V, N) = 0` for every `n > d`, every free module `V` over a principal ideal ring `k` without
zero divisors and every `k`-module `N`. For instance the integral cohomology of `M` vanishes above
degree `d`. -/
theorem IsMorse.isZero_singularCohomology_of_compactSpace_of_manifoldMorseIndex_le [CompactSpace M]
    (hf : IsMorse I f) {d : ℕ} (hd : ∀ x ∈ criticalPoints I f, manifoldMorseIndex I f x ≤ d)
    {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k] (V N : ModuleCat.{u} k)
    [Module.Free k V] {n : ℕ} (hn : d < n) :
    IsZero ((TopCat.of M).singularCohomology V k N n) :=
  hf.isZero_singularCohomology_of_manifoldMorseIndex_le hf.contMDiff.continuous.isProperMap
    (isCompact_range hf.contMDiff.continuous).bddBelow hd V N hn

end TauCeti
