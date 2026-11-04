/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.TopHomology
public import TauCeti.AlgebraicTopology.Singular.Sublevel
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

On a compact manifold `M` itself is such a band, over the empty sublevel, so the singular homology
of `M` vanishes above `d` with coefficients in any abelian category with coproducts
(`TauCeti.IsMorse.isZero_singularHomology_of_compactSpace_of_manifoldMorseIndex_le`), without the
exactness of sequential colimits needed for a proper function on a noncompact manifold, and
`H_d(M; V)` is free (`TauCeti.IsMorse.free_singularHomology_of_manifoldMorseIndex_le`).
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

* `TauCeti.IsMorse.free_singularHomology_sublevelPair_of_manifoldMorseIndex_le` and
  `TauCeti.IsMorse.free_singularHomology_of_manifoldMorseIndex_le`: freeness of homology in the
  degree of the largest index.
* `TauCeti.IsMorse.isZero_singularHomology_of_compactSpace_of_manifoldMorseIndex_le`: vanishing of
  the homology of a compact manifold above the largest index.

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

universe u v w

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

section Compact

variable [CompactSpace M]

/-- **Homology of a compact manifold vanishes above the largest index.** If every critical point
of a Morse function on a compact boundaryless manifold `M` has index at most `d`, then the singular
homology `Hₙ(M; R)` vanishes for every `n > d` and every coefficient object `R` of an abelian
category with coproducts. -/
theorem IsMorse.isZero_singularHomology_of_compactSpace_of_manifoldMorseIndex_le
    (hf : IsMorse I f) {d : ℕ}
    (hd : ∀ x ∈ criticalPoints I f, manifoldMorseIndex I f x ≤ d)
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) {n : ℕ}
    (hn : d < n) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor A n).obj R).obj (TopCat.of M)) := by
  obtain ⟨a, b, hab, hcompact, ha, hb, hf'⟩ :=
    exists_isRegularValue_forall_mem_Ioc (I := I) hf.contMDiff.continuous
  exact (hf.isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le hab hcompact ha hb
    (fun x hx ↦ hd x hx.1) R hn).of_iso (nonempty_singularHomology_iso_sublevelPair hab
      (fun x ↦ (hf' x).1) (fun x ↦ (hf' x).2) R n).some

/-- **Homology of a compact manifold is free in the degree of the largest index.** If every
critical point of a Morse function on a compact boundaryless manifold `M` has index at most `d`,
then `H_d(M; V)` is free for every free module `V` over a principal ideal ring without zero
divisors. With integral coefficients it is free abelian. -/
theorem IsMorse.free_singularHomology_of_manifoldMorseIndex_le (hf : IsMorse I f) {d : ℕ}
    (hd : ∀ x ∈ criticalPoints I f, manifoldMorseIndex I f x ≤ d)
    {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k] (V : ModuleCat.{u} k)
    [Module.Free k V] :
    Module.Free k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) d).obj V).obj
      (TopCat.of M)) := by
  obtain ⟨a, b, hab, hcompact, ha, hb, hf'⟩ :=
    exists_isRegularValue_forall_mem_Ioc (I := I) hf.contMDiff.continuous
  have := hf.free_singularHomology_sublevelPair_of_manifoldMorseIndex_le hab hcompact ha hb
    (fun x hx ↦ hd x hx.1) V
  exact .of_equiv (nonempty_singularHomology_iso_sublevelPair hab (fun x ↦ (hf' x).1)
    (fun x ↦ (hf' x).2) V d).some.symm.toLinearEquiv

end Compact

end TauCeti
