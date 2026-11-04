/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.TopHomology
public import TauCeti.AlgebraicTopology.Singular.DirectedUnion
public import TauCeti.AlgebraicTopology.Singular.Sublevel
public import TauCeti.AlgebraicTopology.Singular.Triple.Free
public import TauCeti.Geometry.Manifold.Morse.Cell.Homology
public import TauCeti.Geometry.Manifold.Morse.Deformation.Homology
public import TauCeti.Geometry.Manifold.Morse.Exhaustion

/-!
# Homology above the largest Morse index

Let `f` be a Morse function on a boundaryless finite-dimensional manifold `M`, and let `a ≤ b` be
regular values with compact band `f⁻¹[a, b]`. If every critical point of `f` in the band has index
at most `d`, then the sublevel `M_b = {f ≤ b}` is obtained from `M_a = {f ≤ a}`, up to homotopy, by
attaching cells of dimension at most `d`. Consequently, writing `Hᵢ` for relative singular
homology of the pair `(M_b, M_a)`:

* `Hₙ(M_b, M_a; R)` vanishes for every `n > d`, with coefficients in any abelian category with
  coproducts, in particular with integral coefficients
  (`TauCeti.IsMorse.isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le`);
* `H_d(M_b, M_a; V)` is free for every free module `V` over a principal ideal ring without zero
  divisors, for instance `H_d(M_b, M_a; ℤ)` is free abelian
  (`TauCeti.IsMorse.free_singularHomology_sublevelPair_of_manifoldMorseIndex_le`).

On a compact manifold `M` itself is such a band, over the empty sublevel, so the same holds for the
singular homology of `M` (`TauCeti.IsMorse.isZero_singularHomology_of_manifoldMorseIndex_le` and
`TauCeti.IsMorse.free_singularHomology_of_manifoldMorseIndex_le`). For a proper Morse function
bounded below, `M` is the increasing union of compact regular sublevels, and since singular homology
has compact supports the vanishing above `d` holds on `M`, for coefficients with exact sequential
colimits (`TauCeti.IsMorse.isZero_singularHomology_of_isProperMap_of_manifoldMorseIndex_le`).
None of these statements says that the degree-`d` integral cohomology is torsion-free.

The statements about bands are proved by Milnor's induction over the critical levels, isolated as
`TauCeti.IsMorse.sublevelPair_induction`: a property of sublevel pairs that holds across bands
without critical points and across one critical level, and is preserved by composing adjacent
bands, holds across every compact band between regular values. Across one critical level the pair
has the relative homology of a finite CW pair with one `i`-cell for each critical point of index
`i` (`TauCeti.IsMorse.exists_relCWComplex_isIso_singularHomologyMap_sublevelPair`), which has no
cells above dimension `d`; there vanishing is
`TauCeti.isZero_singularHomology_complexBasePair_of_isEmpty_cell` and freeness is
`TauCeti.free_singularHomology_complexBasePair_of_isEmpty_cell`. Along a triple of sublevels
`M_a ⊆ M_m ⊆ M_b` the long exact sequence propagates vanishing
(`TauCeti.TopTriple.isZero_singularHomology_totalPair`) and, since `H_{d+1}(M_b, M_m)` vanishes,
freeness (`TauCeti.TopTriple.free_singularHomology_totalPair`).

## Main results

* `TauCeti.IsMorse.isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le`,
  `TauCeti.IsMorse.isZero_singularHomology_of_manifoldMorseIndex_le` and
  `TauCeti.IsMorse.isZero_singularHomology_of_isProperMap_of_manifoldMorseIndex_le`: vanishing of
  homology above the largest index.
* `TauCeti.IsMorse.free_singularHomology_sublevelPair_of_manifoldMorseIndex_le` and
  `TauCeti.IsMorse.free_singularHomology_of_manifoldMorseIndex_le`: freeness of homology in the
  degree of the largest index.

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

/-- **Homology vanishes above the largest index.** Let `f` be a Morse function, `a ≤ b` regular
values with compact band `f⁻¹[a, b]`, and suppose that every critical point in the band has index
at most `d`. Then the relative singular homology `Hₙ({f ≤ b}, {f ≤ a}; R)` vanishes for every
`n > d` and every coefficient object `R` of an abelian category with coproducts. -/
theorem IsMorse.isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le (hf : IsMorse I f)
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) {d : ℕ}
    (hd : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → manifoldMorseIndex I f x ≤ d)
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) {n : ℕ}
    (hn : d < n) : IsZero ((sublevelPair f hab).singularHomology R n) := by
  revert A
  refine hf.sublevelPair_induction (fun s t hst ↦ ∀ {A : Type v} [Category.{w} A] [Abelian A]
      [HasCoproducts.{u} A] (R : A), IsZero ((sublevelPair f hst).singularHomology R n))
    ?_ ?_ ?_ hab hcompact ha hb
  · -- A band without critical points.
    intro s t hst _ _ hst' hcrit A _ _ _ R
    exact isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero hf.contMDiff hst hst'
      (fun x hsx hxt hx ↦ hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) ⟨hsx, hxt⟩) R n
  · -- One critical level: no critical point on it has index `n`.
    intro c δ hδ hcδ hcδ' hcompact' _
    obtain ⟨ε, hε, hεδ, hzero, -⟩ :=
      hf.exists_isZero_and_finrank_le_singularHomology_sublevelPair hδ hcompact'
    refine ⟨ε, hε, hεδ, fun R ↦ hzero R n fun p hp ↦ ?_⟩
    have hpc : f p = c := hp.2
    have := hd p hp.1 ⟨by linarith, by linarith⟩
    lia
  · -- Along a triple of sublevels.
    intro s m t hsm hmt _ _ _ _ _ _ h₁ h₂ A _ _ _ R
    exact (TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f hsm)
      (sublevel_mono f hmt)).isZero_singularHomology_totalPair R n (h₁ R) (h₂ R)

/-- **Homology is free in the degree of the largest index.** Let `f` be a Morse function, `a ≤ b`
regular values with compact band `f⁻¹[a, b]`, and suppose that every critical point in the band has
index at most `d`. Then `H_d({f ≤ b}, {f ≤ a}; V)` is free for every free module `V` over a
principal ideal ring without zero divisors. With integral coefficients it is free abelian. -/
theorem IsMorse.free_singularHomology_sublevelPair_of_manifoldMorseIndex_le (hf : IsMorse I f)
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) {d : ℕ}
    (hd : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → manifoldMorseIndex I f x ≤ d)
    {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k] (V : ModuleCat.{u} k)
    [Module.Free k V] :
    Module.Free k ((sublevelPair f hab).singularHomology V d : ModuleCat k) := by
  refine hf.sublevelPair_induction (fun s t hst ↦
      Module.Free k ((sublevelPair f hst).singularHomology V d : ModuleCat k))
    ?_ ?_ ?_ hab hcompact ha hb
  · -- A band without critical points has no relative homology.
    intro s t hst _ _ hst' hcrit
    have := ModuleCat.isZero_iff_subsingleton.1 <|
      isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero hf.contMDiff hst hst'
        (fun x hsx hxt hx ↦ hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) ⟨hsx, hxt⟩) V d
    infer_instance
  · -- One critical level: the cell pair has no `(d + 1)`-cells.
    intro c δ hδ hcδ hcδ' hcompact' _
    obtain ⟨ε, hε, hεδ, C, _, _, hC, hcell, hiso⟩ :=
      hf.exists_relCWComplex_isIso_singularHomologyMap_sublevelPair hδ hcompact'
    refine ⟨ε, hε, hεδ, ?_⟩
    have : IsEmpty (cell C (d + 1)) := (hcell (d + 1)).some.isEmpty_congr.2
      ⟨fun p ↦ by
        have hpc : f p.1.1 = c := p.1.2.2
        have := hd p.1.1 p.1.2.1 ⟨by linarith, by linarith⟩
        have := p.2
        lia⟩
    have h := free_singularHomology_complexBasePair_of_isEmpty_cell C V d
    rw [complexBasePair_eq_ofInclusion] at h
    exact .of_equiv (@asIso _ _ _ _ _ (hiso V d)).toLinearEquiv
  · -- Along a triple of sublevels, where `H_{d+1}` of the upper pair vanishes.
    intro s m t hsm hmt hs ht hcompact' _ hm' ht' h₁ h₂
    have hzero := hf.isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le hmt
      (hcompact'.of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous)
        (preimage_mono (Icc_subset_Icc hsm le_rfl))) hm' ht'
      (fun x hx hxI ↦ hd x hx ⟨by linarith [hxI.1], by linarith [hxI.2]⟩) V (lt_add_one d)
    let T := TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f hsm) (sublevel_mono f hmt)
    have : Module.Free k ((TopTriple.innerPair.obj T).singularHomology V d : ModuleCat k) := h₁
    have : Module.Free k ((TopTriple.outerPair.obj T).singularHomology V d : ModuleCat k) := h₂
    exact T.free_singularHomology_totalPair V d hzero

/-- **Homology vanishes above the largest index, for a proper function.** If every critical point
of a proper Morse function `f` bounded below has index at most `d`, then the singular homology
`Hₙ(M; R)` vanishes for every `n > d` and every coefficient object `R` of an abelian category with
coproducts and exact sequential colimits, such as modules over a ring. -/
theorem IsMorse.isZero_singularHomology_of_isProperMap_of_manifoldMorseIndex_le
    (hf : IsMorse I f) (hp : IsProperMap f) (hbdd : BddBelow (range f)) {d : ℕ}
    (hd : ∀ x ∈ criticalPoints I f, manifoldMorseIndex I f x ≤ d)
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] [HasColimitsOfShape ℕ A]
    [HasExactColimitsOfShape ℕ A] (R : A) {n : ℕ} (hn : d < n) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor A n).obj R).obj (TopCat.of M)) := by
  obtain ⟨a, K, hmono, htop, hreg, hK, hK0, -⟩ := hf.exists_regular_sublevel_exhaustion hp hbdd
  have hU : Monotone fun k ↦ {x : M | f x ≤ a k} := fun _ _ h ↦ sublevel_mono f (hmono.monotone h)
  -- The sublevels `{f ≤ a k}` exhaust `M`, and every compact subset of `M` lies in one of them.
  let c : Cocone ({ obj k := TopCat.of {x : M | f x ≤ a k}
                    map h := TopCat.ofHom (ContinuousMap.inclusion (hU h.le)) } : ℕ ⥤ TopCat.{u}) :=
    { pt := TopCat.of M, ι := { app k := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ } }
  have hL (L : Set c.pt) (hL : IsCompact L) : ∃ k, L ⊆ Set.range (c.ι.app k) := by
    obtain ⟨t, ht⟩ := (hL.image hf.contMDiff.continuous).bddAbove
    obtain ⟨k, hk⟩ := (htop.eventually_ge_atTop t).exists
    exact ⟨k, fun x hx ↦ ⟨⟨x, (ht ⟨x, hx, rfl⟩).trans hk⟩, rfl⟩⟩
  refine (isColimitMapCoconeSingularHomology R n c (fun _ ↦ IsEmbedding.subtypeVal) hL).isZero_pt
    (Functor.isZero_iff _ |>.2 fun k ↦ ?_)
  -- Each sublevel is the band `f⁻¹[a 0, a k]` over the empty sublevel `{f ≤ a 0}`.
  have ha0 (x : M) : a 0 < f x := by
    by_contra h
    have : x ∈ K 0 := by rw [hK]; exact not_lt.1 h
    rw [hK0] at this
    exact this
  have h0k : a 0 ≤ a k := hmono.monotone (Nat.zero_le k)
  have : IsEmpty (sublevelPair f h0k).snd := ⟨fun (x : {x : M | f x ≤ a 0}) ↦ (ha0 x).not_ge x.2⟩
  have hπ : IsIso ((sublevelPair f h0k).singularHomologyπ R n) := inferInstance
  refine (hf.isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le h0k
    ((K.isCompact k).of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous)
      (fun x hx ↦ by rw [hK]; exact hx.2)) (hreg 0) (hreg k) (fun x hx _ ↦ hd x hx) R hn).of_iso
    (@asIso _ _ _ _ _ hπ)

section Compact

variable [CompactSpace M]

/-- **Homology of a compact manifold vanishes above the largest index.** If every critical point
of a Morse function on a compact boundaryless manifold `M` has index at most `d`, then the singular
homology `Hₙ(M; R)` vanishes for every `n > d` and every coefficient object `R` of an abelian
category with coproducts. -/
theorem IsMorse.isZero_singularHomology_of_manifoldMorseIndex_le (hf : IsMorse I f) {d : ℕ}
    (hd : ∀ x ∈ criticalPoints I f, manifoldMorseIndex I f x ≤ d)
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) {n : ℕ}
    (hn : d < n) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor A n).obj R).obj (TopCat.of M)) := by
  obtain ⟨a, b, hab, hcompact, ha, hb, hf'⟩ :=
    exists_isRegularValue_forall_mem_Ioc (I := I) hf.contMDiff.continuous
  exact (hf.isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le hab hcompact ha hb
    (fun x hx _ ↦ hd x hx) R hn).of_iso (nonempty_singularHomology_iso_sublevelPair hab
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
    (fun x hx _ ↦ hd x hx) V
  exact .of_equiv (nonempty_singularHomology_iso_sublevelPair hab (fun x ↦ (hf' x).1)
    (fun x ↦ (hf' x).2) V d).some.symm.toLinearEquiv

end Compact

end TauCeti
