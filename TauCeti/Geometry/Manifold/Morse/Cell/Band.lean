/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.DirectedUnion
public import TauCeti.AlgebraicTopology.Singular.Empty
public import TauCeti.AlgebraicTopology.Singular.Sublevel
public import TauCeti.AlgebraicTopology.Singular.Triple
public import TauCeti.Geometry.Manifold.Morse.Cell.Homology
public import TauCeti.Geometry.Manifold.Morse.Deformation.Homology
public import TauCeti.Geometry.Manifold.Morse.Exhaustion

/-!
# Homology of a Morse function with bounded indices

Let `f` be a Morse function on a boundaryless manifold `M`, and write `M_b = {f ≤ b}`. Crossing a
single critical level attaches one cell for each critical point of the level, of dimension its
index (`TauCeti.IsMorse.exists_isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le`),
while across a compact band without critical points the relative homology of `(M_b, M_a)` vanishes
(`TauCeti.isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero`).
This file assembles these steps along finitely many critical levels, and then along an exhaustion.

* If `a` and `b` are regular values, the band `f⁻¹[a, b]` is compact, and every critical point in
  it has index at most `d`, then `Hₙ(M_b, M_a)` vanishes for `n > d`
  (`TauCeti.IsMorse.isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le`). The band
  contains only finitely many critical values, and the relative homology of `(M_b, M_a)` is
  assembled from the pieces between them by the long exact sequence of a triple, along the
  induction over critical levels `TauCeti.IsMorse.band_induction`.
* If `b` is a regular value with compact sublevel `M_b`, and every critical point in `M_b` has
  index at most `d`, then `Hₙ(M_b)` vanishes for `n > d`
  (`TauCeti.IsMorse.isZero_singularHomology_sublevel_of_manifoldMorseIndex_le`).
* If `M` is compact and all critical points of `f` have index at most `d`, then `Hₙ(M)` vanishes
  for `n > d`, with coefficients in any abelian category with coproducts
  (`TauCeti.IsMorse.isZero_singularHomology_of_compactSpace_of_manifoldMorseIndex_le`). Here `M`
  is itself a band over the empty sublevel, so no exactness of sequential colimits is needed.
* If `f` is proper and bounded below and all its critical points have index at most `d`, then
  `Hₙ(M)` vanishes for `n > d`, with coefficients in an abelian category in which colimits of
  sequences are exact (`TauCeti.IsMorse.isZero_singularHomology_of_manifoldMorseIndex_le`). Every
  singular simplex lies in some regular sublevel, so the homology of `M` is the colimit of the
  homology of the sublevels of a regular exhaustion.

The last statement is the homological shadow of the CW model of `M` with one cell of dimension
`λ` for each critical point of index `λ`: a CW complex of dimension at most `d` has no homology
above degree `d`. It is the form in which index bounds, such as those for strongly
`q`-pseudoconvex functions on complex manifolds, bound the homology of a manifold.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorems 3.1, 3.2 and 3.5.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.1, Proposition 2.6, and Section 2.2, Lemma 2.34.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology AlgebraicTopology
open scoped ContDiff Manifold

universe u v w

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ} {a b : ℝ}
  {C : Type v} [Category.{w} C]

/-- **A compact band whose critical points have index at most `d` has no relative homology above
degree `d`.** Let `f` be a Morse function, let `a ≤ b` be regular values of `f` with compact band
`f⁻¹[a, b]`, and suppose every critical point in the band has Morse index at most `d`. Then the
relative singular homology `Hₙ({f ≤ b}, {f ≤ a}; R)` vanishes for every `n > d` and every
coefficient object `R` of an abelian category with coproducts. -/
theorem IsMorse.isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le [HasCoproducts.{u} C]
    [Abelian C] (hf : IsMorse I f) {d : ℕ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hd : ∀ p ∈ criticalPoints I f ∩ f ⁻¹' Icc a b, manifoldMorseIndex I f p ≤ d) (R : C) {n : ℕ}
    (hn : d < n) : IsZero ((sublevelPair f hab).singularHomology R n) :=
  hf.band_induction (P := fun s t hst ↦ IsZero ((sublevelPair f hst).singularHomology R n)) hab
    hcompact ha hb
    (fun _ _ hst hcompact hcrit ↦ isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero
      hf.contMDiff hst hcompact
        (fun x hx₁ hx₂ hx ↦ hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) ⟨hx₁, hx₂⟩) R n)
    (fun p hp hap hpb _ hδ hcompact ↦ by
      obtain ⟨ε, hε, hεδ, hzero⟩ :=
        hf.exists_isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le
          (fun q hq ↦ hd q ⟨hq.1, by
            have : f q = f p := hq.2
            constructor <;> linarith⟩) hδ hcompact
      exact ⟨ε, hε, hεδ, hzero R n hn⟩)
    -- The long exact sequence of the triple `(M_t, M_m, M_s)` joins the pieces.
    fun _ _ _ hsm hmt _ h₁ h₂ ↦ (TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f hsm)
      (sublevel_mono f hmt)).isZero_singularHomology_totalPair R n h₁ h₂

/-- **A compact regular sublevel whose critical points have index at most `d` has no homology
above degree `d`.** Let `f` be a Morse function, let `b` be a regular value of `f` with compact
sublevel `{f ≤ b}`, and suppose every critical point in this sublevel has Morse index at most `d`.
Then the singular homology `Hₙ({f ≤ b}; R)` vanishes for every `n > d` and every coefficient object
`R` of an abelian category with coproducts. -/
theorem IsMorse.isZero_singularHomology_sublevel_of_manifoldMorseIndex_le [HasCoproducts.{u} C]
    [Abelian C] (hf : IsMorse I f) {d : ℕ} (hcompact : IsCompact {x | f x ≤ b})
    (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hd : ∀ p ∈ criticalPoints I f, f p ≤ b → manifoldMorseIndex I f p ≤ d) (R : C) {n : ℕ}
    (hn : d < n) :
    IsZero (((singularHomologyFunctor C n).obj R).obj (TopCat.of {x | f x ≤ b})) := by
  have hcont : Continuous f := hf.contMDiff.continuous
  -- Below the minimum of `f` on the compact sublevel, the sublevel `{f ≤ a}` is empty.
  obtain ⟨m, hm⟩ := hcompact.bddBelow_image hcont.continuousOn
  have hab : min m b - 1 ≤ b := by linarith [min_le_right m b]
  have hempty (x : M) : ¬f x ≤ min m b - 1 := fun hx ↦ by
    have hxb : x ∈ {x | f x ≤ b} := hx.trans hab
    have := hm (mem_image_of_mem f hxb)
    linarith [min_le_left m b]
  have : IsEmpty (sublevelPair f hab).snd := ⟨fun x ↦ hempty x.1 x.2⟩
  have hzero := hf.isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le hab
    (hcompact.of_isClosed_subset (isClosed_Icc.preimage hcont) fun x hx ↦ hx.2)
    (isRegularValue_iff_notMem_image_criticalPoints.2 fun ⟨p, _, hp⟩ ↦ hempty p hp.le)
    hb (fun p hp ↦ hd p hp.1 hp.2.2) R hn
  -- Relative homology modulo the empty sublevel is the homology of `{f ≤ b}`.
  have hπ : IsIso ((sublevelPair f hab).singularHomologyπ R n) := inferInstance
  exact hzero.of_iso (@asIso _ _ _ _ _ hπ)

/-- **Homology of a compact manifold vanishes above the largest index.** If every critical point
of a Morse function on a compact boundaryless manifold `M` has index at most `d`, then the singular
homology `Hₙ(M; R)` vanishes for every `n > d` and every coefficient object `R` of an abelian
category with coproducts. -/
theorem IsMorse.isZero_singularHomology_of_compactSpace_of_manifoldMorseIndex_le [CompactSpace M]
    [HasCoproducts.{u} C] [Abelian C] (hf : IsMorse I f) {d : ℕ}
    (hd : ∀ p ∈ criticalPoints I f, manifoldMorseIndex I f p ≤ d) (R : C) {n : ℕ} (hn : d < n) :
    IsZero (((singularHomologyFunctor C n).obj R).obj (TopCat.of M)) := by
  obtain ⟨a, b, hab, hcompact, ha, hb, hf'⟩ :=
    exists_isRegularValue_forall_mem_Ioc (I := I) hf.contMDiff.continuous
  exact (hf.isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le hab hcompact ha hb
    (fun p hp ↦ hd p hp.1) R hn).of_iso (singularHomologyIsoSublevelPair hab
      (fun x ↦ (hf' x).1) (fun x ↦ (hf' x).2) R n)

/-- **A manifold with a proper Morse function whose indices are at most `d` has no homology above
degree `d`.** Let `f` be a proper Morse function, bounded below, all of whose critical points have
Morse index at most `d`. Then the singular homology `Hₙ(M; R)` vanishes for every `n > d` and every
coefficient object `R` of an abelian category with coproducts in which colimits of sequences are
exact, such as a category of modules. -/
theorem IsMorse.isZero_singularHomology_of_manifoldMorseIndex_le [HasCoproducts.{u} C] [Abelian C]
    [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C] (hf : IsMorse I f)
    (hp : IsProperMap f) (hbdd : BddBelow (range f)) {d : ℕ}
    (hd : ∀ p ∈ criticalPoints I f, manifoldMorseIndex I f p ≤ d) (R : C) {n : ℕ} (hn : d < n) :
    IsZero (((singularHomologyFunctor C n).obj R).obj (TopCat.of M)) := by
  obtain ⟨a, K, hmono, -, hreg, hK, -, -⟩ := hf.exists_regular_sublevel_exhaustion hp hbdd
  have hKa (j : ℕ) : K j = {x | f x ≤ a j} := hK j
  -- The regular sublevels `{f ≤ a j}` and their inclusions into `M` form a cocone of embeddings,
  -- and every compact subset of `M` lies in one of them.
  let F : ℕ ⥤ TopCat.{u} :=
    { obj j := TopCat.of {x | f x ≤ a j}
      map h := TopCat.ofHom (ContinuousMap.inclusion (sublevel_mono f (hmono.monotone h.le))) }
  let c : Cocone F :=
    { pt := TopCat.of M
      ι := { app j := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ } }
  have hc : IsColimit (((singularHomologyFunctor C n).obj R).mapCocone c) :=
    isColimitMapCoconeSingularHomology R n c (fun _ ↦ IsEmbedding.subtypeVal) fun L hL ↦ by
      obtain ⟨j, hj⟩ := K.exists_superset_of_isCompact hL
      exact ⟨j, fun x hx ↦ ⟨⟨x, by simpa [hKa j] using hj hx⟩, rfl⟩⟩
  refine hc.isZero_pt (Functor.isZero _ fun j ↦ ?_)
  exact hf.isZero_singularHomology_sublevel_of_manifoldMorseIndex_le
    (by simpa [hKa j] using K.isCompact j) (hreg j) (fun p hp _ ↦ hd p hp) R hn

end TauCeti
