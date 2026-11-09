/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Degeneration
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic
public import TauCeti.Geometry.Manifold.Morse.Cell.Homology

/-!
# The spectral sequence of the critical-band filtration of a Morse function

Let `f` be a smooth function on a boundaryless manifold `M`, and let `a : ℤ → ℝ` be a monotone
sequence of values. The sublevels `M_{a q} = {f ≤ a q}` form an increasing filtration of `M`, and
so of its singular chains; its spectral sequence is the spectral sequence of a filtered space
(`TauCeti.filteredSpaceSpectralSequence`) for the family `q ↦ {f ≤ a q}`. Its first page (numbered
`2` in the cohomological indexing used there, with singular chains of degree `n` in degree `-n`)
has at `(p, q)` the relative homology `Hₙ(M_{a (q + 1)}, M_{a q})` of the `q`th band, where
`p + q = -n`, and its first differential is the connecting map of the triple
`(M_{a (q + 1)}, M_{a q}, M_{a (q - 1)})`.

The filtration is a **critical-band filtration** when the values `a q` separate the critical
values: each band `f⁻¹[a q, a (q + 1)]` is compact and contains at most one critical value, which
lies strictly between `a q` and `a (q + 1)`. On a compact manifold every Morse function has such a
filtration, cut by an arithmetic progression of regular values
(`TauCeti.IsMorse.exists_strictMono_criticalBandCut`), which starts below and ends above all
values of `f`, so that the filtration is finite.

For a Morse function the first page is then free on the critical points
(`TauCeti.IsMorse.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma`): the object at
`(p, q)` is the coproduct of one copy of the coefficients for each critical point of index `n` in
the `q`th band, by Milnor's cell attachment theorem in homology
(`TauCeti.IsMorse.nonempty_singularHomology_sublevelPair_iso_sigma`). In particular it vanishes when
the band has no critical point of index `n`, and over a division ring its dimension is the number
of these critical points times the dimension of the coefficients.

If moreover no two critical points have indices differing by one, every differential of every page
vanishes (`TauCeti.IsMorse.filteredSpaceSpectralSequence_page_d_eq_zero`): a differential raises
the total degree by one, so it would join critical points of indices `n` and `n - 1`. On a compact
manifold the spectral sequence converges to the singular homology of `M`, so in this lacunary case
each graded piece `F_{q+1} Hₙ(M) / F_q Hₙ(M)` of the filtration of `Hₙ(M)` by the images of the
homology of the sublevels is free on the critical points of index `n` in the `q`th band
(`TauCeti.IsMorse.nonempty_cokernel_abutmentFiltrationMap_iso_sigma`). This refines the lacunary
principle `TauCeti.IsMorse.finrank_singularHomology_eq_of_forall_ne_add_one`, which records only
the dimensions.

The same filtration, cut at regular values separating the critical values, is the one whose first
page is computed for Morse–Bott functions by the homology of the critical submanifolds shifted by
their indices; here only the ordinary Morse case is identified.

## Main results

* `TauCeti.IsMorse.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma`: the first page is
  free on the critical points of the band.
* `TauCeti.IsMorse.isZero_filteredSpaceSpectralSequence_page_two_X`: it vanishes in a total degree
  in which the band has no critical point.
* `TauCeti.IsMorse.finrank_filteredSpaceSpectralSequence_page_two_X`: its dimension over a
  division ring.
* `TauCeti.IsMorse.exists_strictMono_criticalBandCut`: on a compact manifold, a critical-band
  filtration exists and is finite.
* `TauCeti.IsMorse.filteredSpaceSpectralSequence_page_d_eq_zero`: degeneration when no two
  critical points have adjacent indices.
* `TauCeti.IsMorse.nonempty_cokernel_abutmentFiltrationMap_iso_sigma`: the graded pieces of the
  homology of a compact manifold in the lacunary case.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3 (Theorem 3.2) and §5 (the lacunary principle).
* R. Bott, *Nondegenerate critical manifolds*, Ann. of Math. 60 (1954), 248–261, the filtration of
  a manifold by the sublevels of a function cut between its critical values.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  §2.2, the spectral sequence of a filtered complex.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set
open scoped ContDiff Manifold

universe u v w

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ} {a : ℤ → ℝ}

/-! ### The first page -/

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- In a band `f⁻¹[a q, a (q + 1)]` whose only critical value is `c`, strictly between `a q` and
`a (q + 1)`, the critical points of the level `c` are the critical points with values in
`(a q, a (q + 1)]`. -/
private theorem criticalPoints_inter_preimage_singleton_eq {c : ℝ} {q : ℤ}
    (hc : c ∈ Ioo (a q) (a (q + 1)))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc (a q) (a (q + 1)) → f x = c) :
    criticalPoints I f ∩ f ⁻¹' {c} = criticalPoints I f ∩ f ⁻¹' Ioc (a q) (a (q + 1)) := by
  ext x
  refine ⟨fun ⟨hx, hfx⟩ ↦ ⟨hx, ?_⟩, fun ⟨hx, hfx⟩ ↦ ⟨hx, hcrit x hx (Ioc_subset_Icc_self hfx)⟩⟩
  rw [mem_preimage, mem_singleton_iff.1 hfx]
  exact Ioo_subset_Ioc_self hc

variable {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A)

/-- **The first page of the spectral sequence of a critical-band filtration is free on the
critical points.** Let `f` be a Morse function and `a : ℤ → ℝ` monotone, and let the band
`f⁻¹[a q, a (q + 1)]` be compact with at most one critical value, lying strictly between `a q` and
`a (q + 1)`. Then on the first page of the spectral sequence of the filtration `q ↦ {f ≤ a q}`,
the object at `(p, q)`, with `p + q = -n`, is the coproduct of one copy of `R` for each critical
point of index `n` with value in `(a q, a (q + 1)]`. -/
theorem IsMorse.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma (hf : IsMorse I f)
    (ha : Monotone a) {q : ℤ} (hcompact : IsCompact (f ⁻¹' Icc (a q) (a (q + 1))))
    (hband : ∃ c ∈ Ioo (a q) (a (q + 1)),
      ∀ x ∈ criticalPoints I f, f x ∈ Icc (a q) (a (q + 1)) → f x = c)
    (pq : ℤ × ℤ) (hq : pq.2 = q) (n : ℕ) (hn : pq.1 + pq.2 = -n) :
    Nonempty (((filteredSpaceSpectralSequence (Y := TopCat.of M) R
        ((sublevel_mono f).comp ha)).page 2).X pq ≅
      ∐ fun _ : {x : ↥(criticalPoints I f ∩ f ⁻¹' Ioc (a q) (a (q + 1))) //
        manifoldMorseIndex I f x = n} ↦ R) := by
  obtain ⟨c, hc, hcrit⟩ := hband
  obtain ⟨e⟩ := hf.nonempty_singularHomology_sublevelPair_iso_sigma hc.1 hc.2 hcompact hcrit R n
  -- Reindex the critical points of the level `c` by those of the band.
  let σ : {x : ↥(criticalPoints I f ∩ f ⁻¹' {c}) // manifoldMorseIndex I f x = n} ≃
      {x : ↥(criticalPoints I f ∩ f ⁻¹' Ioc (a q) (a (q + 1))) // manifoldMorseIndex I f x = n} :=
    (Set.equivOfEq (criticalPoints_inter_preimage_singleton_eq hc hcrit)).subtypeEquiv
      fun _ ↦ Iff.rfl
  subst hq
  exact ⟨filteredSpaceSpectralSequenceFirstPageXIso R ((sublevel_mono f).comp ha) pq pq.2
    (pq.2 + 1) rfl rfl _ rfl n hn ≪≫ e ≪≫ Sigma.whiskerEquiv σ fun _ ↦ Iso.refl R⟩

/-- **Vanishing on the first page.** Under the hypotheses of
`TauCeti.IsMorse.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma`, if no critical point
with value in `(a q, a (q + 1)]` has index `n`, the object at `(p, q)` with `p + q = -n` on the
first page of the spectral sequence of the filtration `q ↦ {f ≤ a q}` is zero. -/
theorem IsMorse.isZero_filteredSpaceSpectralSequence_page_two_X (hf : IsMorse I f)
    (ha : Monotone a) {q : ℤ} (hcompact : IsCompact (f ⁻¹' Icc (a q) (a (q + 1))))
    (hband : ∃ c ∈ Ioo (a q) (a (q + 1)),
      ∀ x ∈ criticalPoints I f, f x ∈ Icc (a q) (a (q + 1)) → f x = c)
    (pq : ℤ × ℤ) (hq : pq.2 = q) (n : ℕ) (hn : pq.1 + pq.2 = -n)
    (hindex : ∀ x ∈ criticalPoints I f, f x ∈ Ioc (a q) (a (q + 1)) →
      manifoldMorseIndex I f x ≠ n) :
    IsZero (((filteredSpaceSpectralSequence (Y := TopCat.of M) R
      ((sublevel_mono f).comp ha)).page 2).X pq) := by
  obtain ⟨e⟩ := hf.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma R ha hcompact
    hband pq hq n hn
  have : IsEmpty {x : ↥(criticalPoints I f ∩ f ⁻¹' Ioc (a q) (a (q + 1))) //
      manifoldMorseIndex I f x = n} := ⟨fun x ↦ hindex x.1 x.1.2.1 x.1.2.2 x.2⟩
  exact ((IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ isEmptyElim)).of_iso e

/-- **The dimensions of the first page.** Under the hypotheses of
`TauCeti.IsMorse.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma`, with coefficients
in a finite-dimensional module `V` over a division ring, the object at `(p, q)` with `p + q = -n`
on the first page of the spectral sequence of the filtration `q ↦ {f ≤ a q}` has dimension `dim V`
times the number of critical points of index `n` with value in `(a q, a (q + 1)]`. -/
theorem IsMorse.finrank_filteredSpaceSpectralSequence_page_two_X (hf : IsMorse I f)
    (ha : Monotone a) {q : ℤ} (hcompact : IsCompact (f ⁻¹' Icc (a q) (a (q + 1))))
    (hband : ∃ c ∈ Ioo (a q) (a (q + 1)),
      ∀ x ∈ criticalPoints I f, f x ∈ Icc (a q) (a (q + 1)) → f x = c)
    {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V]
    (pq : ℤ × ℤ) (hq : pq.2 = q) (n : ℕ) (hn : pq.1 + pq.2 = -n) :
    finrank k (((filteredSpaceSpectralSequence (Y := TopCat.of M) V
        ((sublevel_mono f).comp ha)).page 2).X pq : ModuleCat k) =
      Nat.card {x : ↥(criticalPoints I f ∩ f ⁻¹' Ioc (a q) (a (q + 1))) //
        manifoldMorseIndex I f x = n} * finrank k V := by
  obtain ⟨c, hc, hcrit⟩ := hband
  subst hq
  rw [(filteredSpaceSpectralSequenceFirstPageXIso V ((sublevel_mono f).comp ha) pq pq.2
    (pq.2 + 1) rfl rfl _ rfl n hn).toLinearEquiv.finrank_eq,
    hf.finrank_singularHomology_sublevelPair_eq hc.1 hc.2 hcompact hcrit V n,
    criticalPoints_inter_preimage_singleton_eq hc hcrit]

/-! ### Critical-band filtrations of compact manifolds -/

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- **Critical-band filtrations exist on compact manifolds.** A Morse function `f` on a compact
boundaryless manifold has a strictly increasing sequence of cut values `a : ℤ → ℝ` such that each
band `f⁻¹[a q, a (q + 1)]` contains at most one critical value, lying strictly between `a q` and
`a (q + 1)`, and such that the sequence starts below and ends above all values of `f`. The cut
values form an arithmetic progression whose step is smaller than every gap between distinct
critical values, started off the countably many translates of the critical values. -/
theorem IsMorse.exists_strictMono_criticalBandCut [CompactSpace M] (hf : IsMorse I f) :
    ∃ a : ℤ → ℝ, StrictMono a ∧
      (∀ q, ∃ c ∈ Ioo (a q) (a (q + 1)),
        ∀ x ∈ criticalPoints I f, f x ∈ Icc (a q) (a (q + 1)) → f x = c) ∧
      (∃ q₀, ∀ x, a q₀ < f x) ∧ ∃ q₁, ∀ x, f x ≤ a q₁ := by
  set S := f '' criticalPoints I f
  have hS : S.Finite := hf.finite_criticalPoints.image f
  -- A step `δ` smaller than every gap between distinct critical values.
  obtain ⟨δ, hδ, hgap⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S, ∀ t ∈ S, s ≠ t → δ < |s - t| := by
    have hev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Ioi 0), ∀ p ∈ (S ×ˢ S) ∩ {p | p.1 ≠ p.2},
        δ < |p.1 - p.2| :=
      ((hS.prod hS).inter_of_left _).eventually_all.2 fun p hp ↦
        (nhdsWithin_le_nhds (eventually_lt_nhds (abs_pos.2 (sub_ne_zero.2 hp.2))))
    obtain ⟨δ, hδ, hδS⟩ := (hev.and self_mem_nhdsWithin).exists
    exact ⟨δ, hδS, fun s hs t ht hst ↦ hδ (s, t) ⟨⟨hs, ht⟩, hst⟩⟩
  -- An offset `t₀` such that no cut value `t₀ + q δ` is a critical value.
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, t₀ ∉ ⋃ q : ℤ, (fun s ↦ s - q * δ) '' S :=
    ((countable_iUnion fun _ ↦ (hS.image _).countable).dense_compl ℝ).nonempty
  have hcut (q : ℤ) (x : M) (hx : x ∈ criticalPoints I f) : f x ≠ t₀ + q * δ := fun h ↦
    ht₀ (mem_iUnion.2 ⟨q, f x, mem_image_of_mem f hx, by rw [h]; ring⟩)
  have hfc : Continuous f := hf.contMDiff.continuous
  obtain ⟨L, hL⟩ := (isCompact_range hfc).bddBelow
  obtain ⟨U, hU⟩ := (isCompact_range hfc).bddAbove
  obtain ⟨q₀, hq₀⟩ := exists_int_lt ((L - t₀) / δ)
  obtain ⟨q₁, hq₁⟩ := exists_int_gt ((U - t₀) / δ)
  refine ⟨fun q ↦ t₀ + q * δ, fun q q' hqq' ↦ ?_, fun q ↦ ?_,
    ⟨q₀, fun x ↦ ?_⟩, ⟨q₁, fun x ↦ ?_⟩⟩
  · simpa using mul_lt_mul_of_pos_right (Int.cast_lt.2 hqq') hδ
  · by_cases hx : ∃ x ∈ criticalPoints I f, f x ∈ Icc (t₀ + q * δ) (t₀ + ↑(q + 1) * δ)
    · obtain ⟨x, hx, hfx⟩ := hx
      refine ⟨f x, ⟨(hfx.1.lt_of_ne' (hcut q x hx)), hfx.2.lt_of_ne (hcut (q + 1) x hx)⟩,
        fun y hy hfy ↦ ?_⟩
      by_contra hne
      dsimp only at hfy
      push_cast at hfx hfy
      exact (hgap _ (mem_image_of_mem f hy) _ (mem_image_of_mem f hx) hne).not_ge
        (abs_sub_le_iff.2 ⟨by linarith [hfx.1, hfy.2], by linarith [hfx.2, hfy.1]⟩)
    · push Not at hx
      refine ⟨t₀ + q * δ + δ / 2, ⟨by linarith, by push_cast; linarith⟩, fun y hy hfy ↦
        absurd hfy (hx y hy)⟩
  · have := (lt_div_iff₀ hδ).1 hq₀
    linarith [hL (mem_range_self x)]
  · have := (div_lt_iff₀ hδ).1 hq₁
    linarith [hU (mem_range_self x)]

/-! ### Degeneration in the lacunary case -/

/-- A nonzero object on the first page at `(p, q)` comes from a critical point of index
`-(p + q)` with value in `(a q, a (q + 1)]`. -/
private theorem exists_of_not_isZero_page_two_X (hf : IsMorse I f) (ha : Monotone a)
    {pq : ℤ × ℤ} (hcompact : IsCompact (f ⁻¹' Icc (a pq.2) (a (pq.2 + 1))))
    (hband : ∃ c ∈ Ioo (a pq.2) (a (pq.2 + 1)),
      ∀ x ∈ criticalPoints I f, f x ∈ Icc (a pq.2) (a (pq.2 + 1)) → f x = c)
    (h : ¬IsZero (((filteredSpaceSpectralSequence (Y := TopCat.of M) R
      ((sublevel_mono f).comp ha)).page 2).X pq)) :
    ∃ x ∈ criticalPoints I f, f x ∈ Ioc (a pq.2) (a (pq.2 + 1)) ∧
      (manifoldMorseIndex I f x : ℤ) = -(pq.1 + pq.2) := by
  by_cases hpos : 0 < pq.1 + pq.2
  · exact absurd (isZero_filteredSpaceSpectralSequence_page_two_X R _ pq hpos) h
  have hn : pq.1 + pq.2 = -((-(pq.1 + pq.2)).toNat : ℕ) := by lia
  by_contra hne
  push Not at hne
  exact h (hf.isZero_filteredSpaceSpectralSequence_page_two_X R ha hcompact hband pq rfl _ hn
    fun x hx hfx hidx ↦ hne x hx hfx (by rw [hidx]; lia))

variable (hf : IsMorse I f) (ha : Monotone a)
  (hcompact : ∀ q, IsCompact (f ⁻¹' Icc (a q) (a (q + 1))))
  (hband : ∀ q, ∃ c ∈ Ioo (a q) (a (q + 1)),
    ∀ x ∈ criticalPoints I f, f x ∈ Icc (a q) (a (q + 1)) → f x = c)
  (hind : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
    manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1)
include hf hcompact hband hind

/-- If no two critical points have indices differing by one, of two positions of the first page
whose total degrees differ by one, at least one carries the zero object. -/
private theorem isZero_or_isZero_page_two_X {pq pq' : ℤ × ℤ}
    (hdeg : pq.1 + pq.2 + 1 = pq'.1 + pq'.2) :
    IsZero (((filteredSpaceSpectralSequence (Y := TopCat.of M) R
        ((sublevel_mono f).comp ha)).page 2).X pq) ∨
      IsZero (((filteredSpaceSpectralSequence (Y := TopCat.of M) R
        ((sublevel_mono f).comp ha)).page 2).X pq') := by
  by_contra h
  rw [not_or] at h
  obtain ⟨x, hx, -, hxn⟩ :=
    exists_of_not_isZero_page_two_X R hf ha (hcompact _) (hband _) h.1
  obtain ⟨y, hy, -, hyn⟩ :=
    exists_of_not_isZero_page_two_X R hf ha (hcompact _) (hband _) h.2
  exact hind x hx y hy (by lia)

/-- **Lacunary degeneration.** Let `f` be a Morse function and `a : ℤ → ℝ` monotone, such that
every band `f⁻¹[a q, a (q + 1)]` is compact with at most one critical value, lying strictly between
`a q` and `a (q + 1)`. If no two critical points of `f` have indices differing by one, every
differential on every page of the spectral sequence of the filtration `q ↦ {f ≤ a q}` vanishes. -/
theorem IsMorse.filteredSpaceSpectralSequence_page_d_eq_zero (r : ℤ) (hr : 2 ≤ r)
    (pq pq' : ℤ × ℤ) :
    ((filteredSpaceSpectralSequence (Y := TopCat.of M) R
      ((sublevel_mono f).comp ha)).page r).d pq pq' = 0 := by
  by_cases hrel : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).Rel pq pq'
  · exact SpectralSequence.page_d_eq_zero_of_le _ le_rfl
      (isZero_or_isZero_page_two_X R hf ha hcompact hband hind
        (Abelian.SpectralObject.coreE₂Cohomological.hc r pq pq' hrel hr)) r hr
  · exact HomologicalComplex.shape _ _ _ hrel

/-- **The graded homology in the lacunary case.** Let `f` be a Morse function and `a : ℤ → ℝ`
monotone, starting below and ending above all values of `f`, such that every band
`f⁻¹[a q, a (q + 1)]` is compact with at most one critical value, lying strictly between `a q` and
`a (q + 1)`; then `M` is compact. Filter `Hₙ(M; R)` by the images `F_q Hₙ` of the homology of the
sublevels `{f ≤ a q}`. If no two critical points have indices differing by one, the graded piece
`F_{q+1} Hₙ / F_q Hₙ` is the coproduct of one copy of `R` for each critical point of index `n` with
value in `(a q, a (q + 1)]`. The graded piece is written as the cokernel of the inclusion
`F_q Hₙ ⟶ F_{q+1} Hₙ` of the filtration of the abutment of the spectral sequence, which is `Hₙ(M)`
in total degree `p + q = -n` (`TauCeti.filteredSpaceAbutmentIso`). -/
theorem IsMorse.nonempty_cokernel_abutmentFiltrationMap_iso_sigma {q₀ q₁ : ℤ}
    (hq₀ : ∀ x, a q₀ < f x) (hq₁ : ∀ x, f x ≤ a q₁) (pq : ℤ × ℤ) (n : ℕ)
    (hn : pq.1 + pq.2 = -n) :
    Nonempty (cokernel ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        (monotone_singularChainFiltration (Y := TopCat.of M) R
          ((sublevel_mono f).comp ha)))).abutmentFiltrationMap pq.2 (pq.1 + pq.2)) ≅
      ∐ fun _ : {x : ↥(criticalPoints I f ∩ f ⁻¹' Ioc (a pq.2) (a (pq.2 + 1))) //
        manifoldMorseIndex I f x = n} ↦ R) := by
  set E := filteredSpaceSpectralSequence (Y := TopCat.of M) R ((sublevel_mono f).comp ha)
  -- On a late enough page the object at `pq` is the graded piece of the homology of `M`.
  have hX₀ : ((fun b ↦ {x | f x ≤ b}) ∘ a) q₀ = ∅ :=
    eq_empty_of_forall_notMem fun x hx ↦ (hq₀ x).not_ge hx
  have hX₁ : ((fun b ↦ {x | f x ≤ b}) ∘ a) q₁ = univ := eq_univ_of_forall hq₁
  set r := max 2 (max (pq.2 - q₀ + 2) (q₁ - pq.2 + 1))
  have hr : 2 ≤ r := le_max_left _ _
  have eE := filteredSpaceSpectralSequencePageXIsoGradedOfFinite (Y := TopCat.of M) R
    ((sublevel_mono f).comp ha) hX₀ hX₁ r hr pq (by lia) (by lia)
  obtain ⟨e₂⟩ := hf.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma R ha
    (hcompact _) (hband _) pq rfl n hn
  by_cases hpq : IsZero ((E.page 2).X pq)
  · -- The object at `pq` vanishes on every page, and so does the coproduct.
    exact ⟨(eE.isZero_iff.1 (E.isZero_page_X_of_le le_rfl hpq r hr)).iso
      (e₂.isZero_iff.1 hpq)⟩
  -- Otherwise every object joined to `pq` by a differential vanishes, so `pq` survives.
  obtain ⟨e⟩ := E.nonempty_page_X_iso_of_le le_rfl (pq := pq) (fun s hs pq' hpq' ↦ by
    rcases hpq' with hpq' | hpq'
    · exact (isZero_or_isZero_page_two_X R hf ha hcompact hband hind
        (Abelian.SpectralObject.coreE₂Cohomological.hc s pq pq' hpq' hs)).resolve_left hpq
    · exact (isZero_or_isZero_page_two_X R hf ha hcompact hband hind
        (Abelian.SpectralObject.coreE₂Cohomological.hc s pq' pq hpq' hs)).resolve_right hpq) r hr
  exact ⟨eE.symm ≪≫ e ≪≫ e₂⟩

end TauCeti
