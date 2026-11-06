/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Free
public import TauCeti.AlgebraicTopology.Cellular.TopHomology
public import TauCeti.AlgebraicTopology.Singular.Triple.Free
public import TauCeti.Geometry.Manifold.Morse.Cell.Band

/-!
# Homology in the degree of the largest Morse index

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
None of these statements says that the degree-`d` integral cohomology is torsion-free.

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

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 and Section 7.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Lemma 2.34.
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
  have hcont : Continuous f := hf.contMDiff.continuous
  -- Below the minimum of `f` on the compact sublevel, the sublevel `{f ≤ a}` is empty.
  obtain ⟨a, hab, ha⟩ := exists_le_forall_lt_of_isCompact_sublevel hcompact hcont.continuousOn
  have : IsEmpty (sublevelPair f hab).snd := ⟨fun x ↦ (ha x.1).not_ge x.2⟩
  have := hf.free_singularHomology_sublevelPair_of_manifoldMorseIndex_le hab
    (hcompact.of_isClosed_subset (isClosed_Icc.preimage hcont) fun x hx ↦ hx.2)
    (isRegularValue_iff_notMem_image_criticalPoints.2 fun ⟨p, _, hp⟩ ↦ (ha p).ne' hp)
    hb (fun p hp ↦ hd p hp.1 hp.2.2) V
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
  obtain ⟨a, K, hmono, -, hreg, hK, -, -⟩ := hf.exists_regular_sublevel_exhaustion hp hbdd
  have hKa (j : ℕ) : K j = {x | f x ≤ a j} := hK j
  -- The regular sublevels `{f ≤ a j}` and their inclusions into `M` form a cocone of embeddings,
  -- and every compact subset of `M` lies in one of them, so `H_d(M)` is the colimit of their
  -- homology.
  let F : ℕ ⥤ TopCat.{u} :=
    { obj j := TopCat.of {x | f x ≤ a j}
      map h := TopCat.ofHom (ContinuousMap.inclusion (sublevel_mono f (hmono.monotone h.le))) }
  let c : Cocone F :=
    { pt := TopCat.of M
      ι := { app j := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ } }
  have hc : IsColimit (((AlgebraicTopology.singularHomologyFunctor _ d).obj V).mapCocone c) :=
    isColimitMapCoconeSingularHomology V d c (fun _ ↦ IsEmbedding.subtypeVal) fun L hL ↦ by
      obtain ⟨j, hj⟩ := K.exists_superset_of_isCompact hL
      exact ⟨j, fun x hx ↦ ⟨⟨x, by simpa [hKa j] using hj hx⟩, rfl⟩⟩
  -- Each step `({f ≤ a (j + 1)}, {f ≤ a j})` is a compact band between regular values.
  have hband (j : ℕ) : IsCompact (f ⁻¹' Icc (a j) (a (j + 1))) :=
    (K.isCompact (j + 1)).of_isClosed_subset (isClosed_Icc.preimage hcont)
      fun x hx ↦ by simpa [hKa] using hx.2
  have hstep (j : ℕ) := hmono.monotone (Nat.le_succ j)
  have hfree (j : ℕ) := hf.free_singularHomology_sublevelPair_of_manifoldMorseIndex_le (hstep j)
    (hband j) (hreg j) (hreg (j + 1)) (fun x hx ↦ hd x hx.1) V
  have hzero (j : ℕ) := hf.isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le (hstep j)
    (hband j) (hreg j) (hreg (j + 1)) (fun x hx ↦ hd x hx.1) V (lt_add_one d)
  have : Module.Free k ((F ⋙ (AlgebraicTopology.singularHomologyFunctor _ d).obj V).obj 0) :=
    hf.free_singularHomology_sublevel_of_manifoldMorseIndex_le (by simpa [hKa] using K.isCompact 0)
      (hreg 0) (fun x hx _ ↦ hd x hx) V
  -- In the long exact sequence of the pair `({f ≤ a (j + 1)}, {f ≤ a j})`, the map
  -- `H_d({f ≤ a j}) ⟶ H_d({f ≤ a (j + 1)})` is injective, since `H_{d+1}` of the pair vanishes,
  -- and is followed by the map into the free module `H_d({f ≤ a (j + 1)}, {f ≤ a j})`.
  exact ModuleCat.free_of_isColimit_of_exact hc
    (fun j ↦ (ModuleCat.mono_iff_injective _).1
      ((sublevelPair f (hstep j)).mono_homologyMap_map_of_isZero V (hzero j)))
    (fun j ↦ ((sublevelPair f (hstep j)).singularHomologyπ V d).hom) fun j ↦
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        ((sublevelPair f (hstep j)).singularHomology_exact_space V d)

end TauCeti
