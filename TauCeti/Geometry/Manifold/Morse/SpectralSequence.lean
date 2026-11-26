/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Degeneration
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic
public import TauCeti.Geometry.Manifold.Morse.Cell.Homology
import TauCeti.Geometry.Manifold.Morse.Generic.Inequalities

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

For a smooth function the first page only sees the critical levels: a compact band without
critical points contributes nothing
(`TauCeti.isZero_filteredSpaceSpectralSequence_page_two_X_of_forall_notMem`), since the lower
sublevel is a deformation retract of the upper one, and if the critical values in a compact band
all lie in `(s, t)`, the band contributes the relative homology `Hₙ(M_t, M_s)` of its critical part
(`TauCeti.filteredSpaceSpectralSequenceFirstPageXIsoOfCollars`).

The filtration is a **critical-band filtration** when `a` is a critical-band cut of `f`
(`TauCeti.IsCriticalBandCut`): each band `f⁻¹[a q, a (q + 1)]` is compact and contains at most one
critical value, which lies strictly between `a q` and `a (q + 1)` (`TauCeti.IsCriticalBand`). On a
compact manifold every continuous function with finitely many critical values has such a
filtration, cut by a strictly increasing sequence of regular values
(`TauCeti.exists_isCriticalBandCut_of_finite_image_criticalPoints`), which starts below and ends
above all values of `f`, so that the filtration is finite. This applies to Morse functions
(`TauCeti.IsMorse.exists_isCriticalBandCut`) and to Morse–Bott functions
(`TauCeti.IsMorseBottFamily.finite_image_criticalPoints`).

For a Morse function the first page is then free on the critical points
(`TauCeti.IsMorse.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma`): the object at
`(p, q)` is the coproduct of one copy of the coefficients for each critical point of index `n` in
the `q`th band, by Milnor's cell attachment theorem in homology
(`TauCeti.IsMorse.nonempty_singularHomology_sublevelPair_iso_sigma`). In particular it vanishes when
the band has no critical point of index `n`, and over a division ring its dimension is the number
of these critical points times the dimension of the coefficients. For a Morse–Bott function the
object at `(p, q)` is instead the relative homology of the lower sublevel with the negative disc
bundles of the critical submanifolds in the band attached, by Bott's theorem
(`TauCeti.Geometry.Manifold.Morse.Bott.SpectralSequence`).

The spectral sequence is invariant under homeomorphisms and does not depend on where exactly the
bands are cut. If `a ≤ a'` and each band `f⁻¹[a q, a' q]` is compact and free of critical points,
the identity of `M` induces an isomorphism from the spectral sequence of `q ↦ {f ≤ a q}` to that of
`q ↦ {f ≤ a' q}` (`TauCeti.isIso_filteredSpaceSpectralSequenceMap_sublevel`): on the first page it
is the map on the relative homology of the bands induced by the inclusions of sublevels, which
cross bands without critical points. Without comparing `a` and `a'`, if each band between `a q`
and `a' q` is compact and free of critical points, the two spectral sequences are isomorphic
through the cut `a ⊔ a'` (`TauCeti.filteredSpaceSpectralSequenceSublevelIso`): moving each cut of
a critical-band filtration within the regular interval containing it does not change the spectral
sequence. A homeomorphism `σ : M ≃ₜ M'` carries the sublevels of `f' ∘ σ` to those of `f'`, so it
induces an isomorphism between their spectral sequences
(`TauCeti.filteredSpaceSpectralSequenceSublevelCompIso`). A diffeomorphism moreover carries every
critical-band cut of `f'` to one of `f' ∘ σ` (`TauCeti.IsCriticalBandCut.comp_diffeomorph`).

On a compact manifold the filtration of a cut starting below and ending above all values of `f` is
finite, from `∅` to `M`, so the spectral sequence converges to the singular homology of `M`: with
coefficients in a finite-dimensional module `V` over a division ring, the dimension of `Hₙ(M; V)`
is the sum of the dimensions of the objects of total degree `-n` on every late enough page
(`TauCeti.finrank_singularHomology_eq_sum_finrank_filteredSpaceSpectralSequence_page_X_sublevel`).
This needs no hypothesis on `f`, since the homology of a compact manifold is finite-dimensional
(`TauCeti.finite_singularHomology_of_compactSpace`). For a Morse or Morse–Bott function cut into
critical bands, the first page records the relative homology across the critical levels.

If moreover no two critical points have indices differing by one, every differential of every page
vanishes (`TauCeti.IsMorse.filteredSpaceSpectralSequence_page_d_eq_zero_of_forall_ne_add_one`): a
differential raises the total degree by one, so it would join critical points of indices `n` and
`n - 1`. On a compact manifold the spectral sequence converges to the singular homology of `M`, so
in this lacunary case each graded piece `F_{q+1} Hₙ(M) / F_q Hₙ(M)` of the filtration of `Hₙ(M)` by
the images of the homology of the sublevels is free on the critical points of index `n` in the
`q`th band
(`TauCeti.IsMorse.nonempty_cokernel_abutmentFiltrationMap_iso_sigma_of_forall_ne_add_one`). This
refines the lacunary principle `TauCeti.IsMorse.finrank_singularHomology_eq_of_forall_ne_add_one`,
which records only the dimensions.

## Main results

* `TauCeti.isZero_filteredSpaceSpectralSequence_page_two_X_of_forall_notMem`: for a smooth
  function, a compact band without critical points contributes nothing to the first page.
* `TauCeti.filteredSpaceSpectralSequenceFirstPageXIsoOfCollars`: for a smooth function, a compact
  band contributes the relative homology of its critical part.
* `TauCeti.isIso_filteredSpaceSpectralSequenceMap_sublevel`: moving the cuts up within regular
  intervals induces an isomorphism of spectral sequences.
* `TauCeti.filteredSpaceSpectralSequenceSublevelIso`: cuts lying in the same regular intervals
  give isomorphic spectral sequences.
* `TauCeti.filteredSpaceSpectralSequenceSublevelCompIso`: a homeomorphism identifies the spectral
  sequences of the sublevel filtrations of `f' ∘ σ` and `f'`.
* `TauCeti.IsMorse.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma`: the first page is
  free on the critical points of the band.
* `TauCeti.IsMorse.isZero_filteredSpaceSpectralSequence_page_two_X`: it vanishes in a total degree
  in which the band has no critical point.
* `TauCeti.IsMorse.finrank_filteredSpaceSpectralSequence_page_two_X`: its dimension over a
  division ring.
* `TauCeti.finrank_singularHomology_eq_sum_finrank_filteredSpaceSpectralSequence_page_X_sublevel`:
  on a compact manifold, the dimension of the homology is the sum of the dimensions of a late
  page in that total degree.
* `TauCeti.IsMorse.filteredSpaceSpectralSequence_page_d_eq_zero_of_forall_ne_add_one`:
  degeneration when no two critical points have adjacent indices.
* `TauCeti.IsMorse.nonempty_cokernel_abutmentFiltrationMap_iso_sigma_of_forall_ne_add_one`: the
  graded pieces of the homology of a compact manifold in the lacunary case.

The existence of critical-band cuts on compact manifolds,
`TauCeti.exists_isCriticalBandCut_of_finite_image_criticalPoints` and
`TauCeti.IsMorse.exists_isCriticalBandCut`, and their invariance under diffeomorphisms,
`TauCeti.IsCriticalBandCut.comp_diffeomorph`, are in
`TauCeti.Geometry.Manifold.Morse.CriticalPoints`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3 (Theorem 3.2) and §5 (the lacunary principle).
* R. Bott, *Nondegenerate critical manifolds*, Ann. of Math. 60 (1954), 248–261, the filtration of
  a manifold by the sublevels of a function cut between its critical values.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  §2.2, the spectral sequence of a filtered complex.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorems 15.6–15.7 (naturality of the spectral sequence).
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

/-- **Bands without critical points do not contribute.** If the band `f⁻¹[a q, a (q + 1)]` is
compact and contains no critical point of the smooth function `f`, the object at `(p, q)` on the
first page of the spectral sequence of the filtration `q ↦ {f ≤ a q}` is zero. -/
theorem isZero_filteredSpaceSpectralSequence_page_two_X_of_forall_notMem
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (ha : Monotone a) (pq : ℤ × ℤ)
    (hcompact : IsCompact (f ⁻¹' Icc (a pq.2) (a (pq.2 + 1))))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∉ Icc (a pq.2) (a (pq.2 + 1))) :
    IsZero (((filteredSpaceSpectralSequence (Y := TopCat.of M) R
      ((sublevel_mono f).comp ha)).page 2).X pq) := by
  rcases lt_or_ge 0 (pq.1 + pq.2) with hpos | hle
  · exact isZero_filteredSpaceSpectralSequence_page_two_X R _ pq hpos
  obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hle
  exact (isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero hf
    (ha (Int.le_add_one le_rfl)) hcompact
    (fun x h₁ h₂ hx ↦ hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) ⟨h₁, h₂⟩) R n).of_iso
    (filteredSpaceSpectralSequenceFirstPageXIso (Y := TopCat.of M) R ((sublevel_mono f).comp ha) pq
      pq.2 (pq.2 + 1) rfl rfl _ rfl n hn)

/-- **The first page sees only the critical part of a band.** Let the band `f⁻¹[a q, a (q + 1)]`
be compact, and let every critical value of the smooth function `f` in `[a q, a (q + 1)]` lie in
`(s, t)`, where `a q ≤ s ≤ t ≤ a (q + 1)`. Then the object at `(p, q)` on the first page of the
spectral sequence of the filtration `q ↦ {f ≤ a q}` is the relative singular homology
`Hₙ({f ≤ t}, {f ≤ s})`, where `p + q = -n`. For a Morse–Bott function this reduces a column of the
first page to the relative homology across a single critical level. -/
def filteredSpaceSpectralSequenceFirstPageXIsoOfCollars (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (ha : Monotone a) (pq : ℤ × ℤ) (n : ℕ) (hn : pq.1 + pq.2 = -n)
    (hcompact : IsCompact (f ⁻¹' Icc (a pq.2) (a (pq.2 + 1)))) {s t : ℝ} (hs : a pq.2 ≤ s)
    (hst : s ≤ t) (ht : t ≤ a (pq.2 + 1))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc (a pq.2) (a (pq.2 + 1)) → f x ∈ Ioo s t) :
    ((filteredSpaceSpectralSequence (Y := TopCat.of M) R
        ((sublevel_mono f).comp ha)).page 2).X pq ≅
      (sublevelPair f hst).singularHomology R n :=
  have hband {s' t' : ℝ} (hs' : a pq.2 ≤ s') (ht' : t' ≤ a (pq.2 + 1)) :
      IsCompact (f ⁻¹' Icc s' t') :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.continuous)
      (preimage_mono (Icc_subset_Icc hs' ht'))
  filteredSpaceSpectralSequenceFirstPageXIso (Y := TopCat.of M) R ((sublevel_mono f).comp ha) pq
      pq.2 (pq.2 + 1) rfl rfl _ rfl n hn ≪≫
    singularHomologySublevelPairIsoOfCollars hf hs hst ht (hband le_rfl (hst.trans ht))
      (hband (hs.trans hst) le_rfl)
      (fun x h₁ h₂ hx ↦ by
        have := hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) ⟨h₁, by linarith⟩
        linarith [this.1])
      (fun x h₁ h₂ hx ↦ by
        have := hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) ⟨by linarith, h₂⟩
        linarith [this.2])
      R n

/-- **The spectral sequence of the sublevel filtration does not depend on where the bands are
cut.** Let `a ≤ a'` be monotone sequences such that each band `f⁻¹[a q, a' q]` is compact and
contains no critical point of the smooth function `f`. The identity of `M` carries each sublevel
`{f ≤ a q}` into `{f ≤ a' q}`, and the morphism it induces from the spectral sequence of the
filtration `q ↦ {f ≤ a q}` to that of `q ↦ {f ≤ a' q}` is an isomorphism of spectral sequences:
on the first page it is the map on the relative homology of the bands induced by the inclusions of
sublevels, which cross bands without critical points. -/
theorem isIso_filteredSpaceSpectralSequenceMap_sublevel (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {a' : ℤ → ℝ} (ha : Monotone a) (ha' : Monotone a') (haa' : ∀ q, a q ≤ a' q)
    (hcompact : ∀ q, IsCompact (f ⁻¹' Icc (a q) (a' q)))
    (hcrit : ∀ q, ∀ x ∈ criticalPoints I f, f x ∉ Icc (a q) (a' q)) :
    IsIso (filteredSpaceSpectralSequenceMap (Y := TopCat.of M) (Y' := TopCat.of M) R
      ((sublevel_mono f).comp ha) ((sublevel_mono f).comp ha') (𝟙 _)
        fun q _ hx ↦ (hx : f _ ≤ a q).trans (haa' q)) := by
  -- The inclusion `{f ≤ a q} ⊆ {f ≤ a' q}` induces isomorphisms on homology.
  have hiso (q : ℤ) (k : ℕ) :
      IsIso (SSet.homologyMap (TopCat.toSSet.map (sublevelPair f (haa' q)).map) R k) :=
    isIso_homologyMap_map_sublevelPair_of_mfderiv_ne_zero hf (haa' q) (hcompact q)
      (fun x h₁ h₂ hx ↦ hcrit q x (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) ⟨h₁, h₂⟩) R k
  refine isIso_filteredSpaceSpectralSequenceMap R _ _ _ _ fun q n ↦ ?_
  -- The map of pairs induced by the identity consists of the two sublevel inclusions.
  set φ := filteredSpaceStepMap (Y := TopCat.of M) (Y' := TopCat.of M)
    ((sublevel_mono f).comp ha) ((sublevel_mono f).comp ha') (𝟙 _)
      (fun q _ hx ↦ (hx : f _ ≤ a q).trans (haa' q)) (Int.le_add_one le_rfl : q ≤ q + 1)
  have hfst : TopPair.Hom.fst φ = (sublevelPair f (haa' (q + 1))).map :=
    TopCat.hom_ext (ContinuousMap.ext fun x ↦ Subtype.ext (filteredSpaceStepMap_fst_apply ..))
  have hsnd : TopPair.Hom.snd φ = (sublevelPair f (haa' q)).map :=
    TopCat.hom_ext (ContinuousMap.ext fun x ↦ Subtype.ext (filteredSpaceStepMap_snd_apply ..))
  refine TopPair.isIso_singularHomologyMap_of_isIso R φ n ?_ ?_ (fun m _ ↦ ?_) (fun m _ ↦ ?_) <;>
    simp only [hfst, hsnd]
  exacts [hiso (q + 1) n, hiso q n, hiso (q + 1) m, hiso q m]

/-- Moving the cuts `a` up to cuts `b` between `a` and `a ⊔ a'` crosses only bands inside
`f⁻¹[a q ⊓ a' q, a q ⊔ a' q]`, so it induces an isomorphism of spectral sequences when these bands
are compact and contain no critical point. -/
private theorem isIso_filteredSpaceSpectralSequenceMap_sublevel_of_le_sup
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {a' b : ℤ → ℝ} (ha : Monotone a) (hb : Monotone b)
    (hab : ∀ q, a q ≤ b q) (hb' : ∀ q, b q ≤ a q ⊔ a' q)
    (hcompact : ∀ q, IsCompact (f ⁻¹' Icc (a q ⊓ a' q) (a q ⊔ a' q)))
    (hcrit : ∀ q, ∀ x ∈ criticalPoints I f, f x ∉ Icc (a q ⊓ a' q) (a q ⊔ a' q)) :
    IsIso (filteredSpaceSpectralSequenceMap (Y := TopCat.of M) (Y' := TopCat.of M) R
      ((sublevel_mono f).comp ha) ((sublevel_mono f).comp hb) (𝟙 _)
        fun q _ hx ↦ (hx : f _ ≤ a q).trans (hab q)) :=
  isIso_filteredSpaceSpectralSequenceMap_sublevel R hf ha hb hab
    (fun q ↦ (hcompact q).of_isClosed_subset (isClosed_Icc.preimage hf.continuous)
      (preimage_mono (Icc_subset_Icc inf_le_left (hb' q))))
    fun q x hx hfx ↦ hcrit q x hx ⟨inf_le_left.trans hfx.1, hfx.2.trans (hb' q)⟩

/-- **The spectral sequence of the sublevel filtration of a smooth function is independent of the
cut.** Let `a` and `a'` be monotone sequences of values such that, for every `q`, the band of `f`
between `a q` and `a' q` is compact and contains no critical point of the smooth function `f`. Then
the spectral sequences of the filtrations `q ↦ {f ≤ a q}` and `q ↦ {f ≤ a' q}` are isomorphic. The
isomorphism passes through the cut `a ⊔ a'`, through the morphisms induced by the identity of `M`
(`TauCeti.filteredSpaceSpectralSequenceSublevelIso_hom_comp`,
`TauCeti.filteredSpaceSpectralSequenceSublevelIso_inv_comp`). -/
def filteredSpaceSpectralSequenceSublevelIso (hf : ContMDiff I 𝓘(ℝ) ∞ f) {a' : ℤ → ℝ}
    (ha : Monotone a) (ha' : Monotone a')
    (hcompact : ∀ q, IsCompact (f ⁻¹' Icc (a q ⊓ a' q) (a q ⊔ a' q)))
    (hcrit : ∀ q, ∀ x ∈ criticalPoints I f, f x ∉ Icc (a q ⊓ a' q) (a q ⊔ a' q)) :
    filteredSpaceSpectralSequence (Y := TopCat.of M) R ((sublevel_mono f).comp ha) ≅
      filteredSpaceSpectralSequence (Y := TopCat.of M) R ((sublevel_mono f).comp ha') :=
  have := isIso_filteredSpaceSpectralSequenceMap_sublevel_of_le_sup R hf ha (ha.sup ha')
    (fun _ ↦ le_sup_left) (fun _ ↦ le_rfl) hcompact hcrit
  have := isIso_filteredSpaceSpectralSequenceMap_sublevel_of_le_sup R hf ha' (ha.sup ha')
    (fun _ ↦ le_sup_right) (fun _ ↦ (sup_comm ..).le)
    (fun q ↦ by rw [inf_comm, sup_comm]; exact hcompact q)
    (fun q ↦ by rw [inf_comm, sup_comm]; exact hcrit q)
  asIso (filteredSpaceSpectralSequenceMap (Y := TopCat.of M) (Y' := TopCat.of M) R
      ((sublevel_mono f).comp ha) ((sublevel_mono f).comp (ha.sup ha')) (𝟙 _)
        fun q _ hx ↦ (hx : f _ ≤ a q).trans (le_sup_left : a q ≤ (a ⊔ a') q)) ≪≫
    (asIso (filteredSpaceSpectralSequenceMap (Y := TopCat.of M) (Y' := TopCat.of M) R
      ((sublevel_mono f).comp ha') ((sublevel_mono f).comp (ha.sup ha')) (𝟙 _)
        fun q _ hx ↦ (hx : f _ ≤ a' q).trans (le_sup_right : a' q ≤ (a ⊔ a') q))).symm

/-- The isomorphism `TauCeti.filteredSpaceSpectralSequenceSublevelIso` between the spectral
sequences of the cuts `a` and `a'` is the one under which the morphisms induced by the identity of
`M` to the spectral sequence of the cut `a ⊔ a'` agree. Since the second of these morphisms is an
isomorphism, this characterizes it. -/
@[reassoc (attr := simp)]
theorem filteredSpaceSpectralSequenceSublevelIso_hom_comp (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {a' : ℤ → ℝ} (ha : Monotone a) (ha' : Monotone a')
    (hcompact : ∀ q, IsCompact (f ⁻¹' Icc (a q ⊓ a' q) (a q ⊔ a' q)))
    (hcrit : ∀ q, ∀ x ∈ criticalPoints I f, f x ∉ Icc (a q ⊓ a' q) (a q ⊔ a' q)) :
    (filteredSpaceSpectralSequenceSublevelIso R hf ha ha' hcompact hcrit).hom ≫
        filteredSpaceSpectralSequenceMap (Y := TopCat.of M) (Y' := TopCat.of M) R
          ((sublevel_mono f).comp ha') ((sublevel_mono f).comp (ha.sup ha')) (𝟙 _)
          (fun q _ hx ↦ (hx : f _ ≤ a' q).trans (le_sup_right : a' q ≤ (a ⊔ a') q)) =
      filteredSpaceSpectralSequenceMap (Y := TopCat.of M) (Y' := TopCat.of M) R
        ((sublevel_mono f).comp ha) ((sublevel_mono f).comp (ha.sup ha')) (𝟙 _)
        (fun q _ hx ↦ (hx : f _ ≤ a q).trans (le_sup_left : a q ≤ (a ⊔ a') q)) := by
  simp [filteredSpaceSpectralSequenceSublevelIso]

/-- The inverse of the isomorphism `TauCeti.filteredSpaceSpectralSequenceSublevelIso` between the
spectral sequences of the cuts `a` and `a'`, followed by the morphism induced by the identity of
`M` from the cut `a` to the cut `a ⊔ a'`, is the morphism induced by the identity of `M` from the
cut `a'` to the cut `a ⊔ a'`. -/
@[reassoc (attr := simp)]
theorem filteredSpaceSpectralSequenceSublevelIso_inv_comp (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {a' : ℤ → ℝ} (ha : Monotone a) (ha' : Monotone a')
    (hcompact : ∀ q, IsCompact (f ⁻¹' Icc (a q ⊓ a' q) (a q ⊔ a' q)))
    (hcrit : ∀ q, ∀ x ∈ criticalPoints I f, f x ∉ Icc (a q ⊓ a' q) (a q ⊔ a' q)) :
    (filteredSpaceSpectralSequenceSublevelIso R hf ha ha' hcompact hcrit).inv ≫
        filteredSpaceSpectralSequenceMap (Y := TopCat.of M) (Y' := TopCat.of M) R
          ((sublevel_mono f).comp ha) ((sublevel_mono f).comp (ha.sup ha')) (𝟙 _)
          (fun q _ hx ↦ (hx : f _ ≤ a q).trans (le_sup_left : a q ≤ (a ⊔ a') q)) =
      filteredSpaceSpectralSequenceMap (Y := TopCat.of M) (Y' := TopCat.of M) R
        ((sublevel_mono f).comp ha') ((sublevel_mono f).comp (ha.sup ha')) (𝟙 _)
        (fun q _ hx ↦ (hx : f _ ≤ a' q).trans (le_sup_right : a' q ≤ (a ⊔ a') q)) := by
  simp [filteredSpaceSpectralSequenceSublevelIso]

section Homeomorph

variable {M' : Type u} [TopologicalSpace M'] {f' : M' → ℝ}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- **The spectral sequence of a sublevel filtration is invariant under homeomorphisms.** If
`σ : M ≃ₜ M'` is a homeomorphism, the sublevels `{f' ∘ σ ≤ a q}` are the preimages under `σ` of the
sublevels `{f' ≤ a q}`, so `σ` induces an isomorphism from the spectral sequence of the filtration
`q ↦ {f' ∘ σ ≤ a q}` to that of `q ↦ {f' ≤ a q}`. Together with
`TauCeti.IsCriticalBandCut.comp_diffeomorph`, a diffeomorphism identifies the spectral sequences of
the critical-band filtrations of `f' ∘ σ` and `f'`. -/
def filteredSpaceSpectralSequenceSublevelCompIso (σ : M ≃ₜ M') (ha : Monotone a) :
    filteredSpaceSpectralSequence (Y := TopCat.of M) R ((sublevel_mono (f' ∘ σ)).comp ha) ≅
      filteredSpaceSpectralSequence (Y := TopCat.of M') R ((sublevel_mono f').comp ha) :=
  filteredSpaceSpectralSequenceIso R _ _ (TopCat.isoOfHomeo (X := .of M) (Y := .of M') σ)
    (fun _ _ hx ↦ by simpa using hx) fun _ _ hy ↦ by simpa using hy

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- The isomorphism `TauCeti.filteredSpaceSpectralSequenceSublevelCompIso` is the morphism of
spectral sequences induced by the homeomorphism. -/
@[simp]
lemma filteredSpaceSpectralSequenceSublevelCompIso_hom (σ : M ≃ₜ M') (ha : Monotone a) :
    (filteredSpaceSpectralSequenceSublevelCompIso R (f' := f') σ ha).hom =
      filteredSpaceSpectralSequenceMap (Y := TopCat.of M) (Y' := TopCat.of M') R
        ((sublevel_mono (f' ∘ σ)).comp ha) ((sublevel_mono f').comp ha)
        (TopCat.isoOfHomeo (X := .of M) (Y := .of M') σ).hom
        fun _ _ hx ↦ by simpa using hx :=
  filteredSpaceSpectralSequenceIso_hom ..

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- The inverse of the isomorphism `TauCeti.filteredSpaceSpectralSequenceSublevelCompIso` is the
morphism of spectral sequences induced by the inverse homeomorphism. -/
@[simp]
lemma filteredSpaceSpectralSequenceSublevelCompIso_inv (σ : M ≃ₜ M') (ha : Monotone a) :
    (filteredSpaceSpectralSequenceSublevelCompIso R (f' := f') σ ha).inv =
      filteredSpaceSpectralSequenceMap (Y := TopCat.of M') (Y' := TopCat.of M) R
        ((sublevel_mono f').comp ha) ((sublevel_mono (f' ∘ σ)).comp ha)
        (TopCat.isoOfHomeo (X := .of M) (Y := .of M') σ).inv
        fun _ _ hy ↦ by simpa using hy :=
  filteredSpaceSpectralSequenceIso_inv ..

end Homeomorph

/-- **The first page of the spectral sequence of a critical-band filtration is free on the
critical points.** Let `f` be a Morse function and `a : ℤ → ℝ` monotone, and let the band
`f⁻¹[a q, a (q + 1)]` be a critical band: compact with at most one critical value, lying strictly
between `a q` and `a (q + 1)`. Then on the first page of the spectral sequence of the filtration
`q ↦ {f ≤ a q}`, the object at `(p, q)`, with `p + q = -n`, is the coproduct of one copy of `R` for
each critical point of index `n` with value in `(a q, a (q + 1)]`. -/
theorem IsMorse.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma (hf : IsMorse I f)
    (ha : Monotone a) {q : ℤ} (hband : IsCriticalBand I f (a q) (a (q + 1)))
    (pq : ℤ × ℤ) (hq : pq.2 = q) (n : ℕ) (hn : pq.1 + pq.2 = -n) :
    Nonempty (((filteredSpaceSpectralSequence (Y := TopCat.of M) R
        ((sublevel_mono f).comp ha)).page 2).X pq ≅
      ∐ fun _ : {x : ↥(criticalPoints I f ∩ f ⁻¹' Ioc (a q) (a (q + 1))) //
        manifoldMorseIndex I f x = n} ↦ R) := by
  obtain ⟨c, hc, hcrit⟩ := hband.exists_mem_Ioo_forall_eq
  obtain ⟨e⟩ := hf.nonempty_singularHomology_sublevelPair_iso_sigma hc.1 hc.2 hband.isCompact
    hcrit R n
  subst hq
  -- Reindex the critical points of the level `c` by those of the band.
  let σ : {x : ↥(criticalPoints I f ∩ f ⁻¹' {c}) // manifoldMorseIndex I f x = n} ≃
      {x : ↥(criticalPoints I f ∩ f ⁻¹' Ioc (a pq.2) (a (pq.2 + 1))) //
        manifoldMorseIndex I f x = n} :=
    (Set.equivOfEq (criticalPoints_inter_preimage_singleton_eq hc hcrit)).subtypeEquiv
      fun _ ↦ Iff.rfl
  exact ⟨filteredSpaceSpectralSequenceFirstPageXIso R ((sublevel_mono f).comp ha) pq pq.2
    (pq.2 + 1) rfl rfl _ rfl n hn ≪≫ e ≪≫ Sigma.whiskerEquiv σ fun _ ↦ Iso.refl R⟩

/-- **Vanishing on the first page.** Under the hypotheses of
`TauCeti.IsMorse.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma`, if no critical point
with value in `(a q, a (q + 1)]` has index `n`, the object at `(p, q)` with `p + q = -n` on the
first page of the spectral sequence of the filtration `q ↦ {f ≤ a q}` is zero. -/
theorem IsMorse.isZero_filteredSpaceSpectralSequence_page_two_X (hf : IsMorse I f)
    (ha : Monotone a) {q : ℤ} (hband : IsCriticalBand I f (a q) (a (q + 1)))
    (pq : ℤ × ℤ) (hq : pq.2 = q) (n : ℕ) (hn : pq.1 + pq.2 = -n)
    (hindex : ∀ x ∈ criticalPoints I f, f x ∈ Ioc (a q) (a (q + 1)) →
      manifoldMorseIndex I f x ≠ n) :
    IsZero (((filteredSpaceSpectralSequence (Y := TopCat.of M) R
      ((sublevel_mono f).comp ha)).page 2).X pq) := by
  obtain ⟨e⟩ := hf.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma R ha hband pq hq n
    hn
  have : IsEmpty {x : ↥(criticalPoints I f ∩ f ⁻¹' Ioc (a q) (a (q + 1))) //
      manifoldMorseIndex I f x = n} := ⟨fun x ↦ hindex x.val x.val.property.1 x.val.property.2
          x.property⟩
  exact ((IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ isEmptyElim)).of_iso e

/-- **The dimensions of the first page.** Under the hypotheses of
`TauCeti.IsMorse.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma`, with coefficients
in a finite-dimensional module `V` over a division ring, the object at `(p, q)` with `p + q = -n`
on the first page of the spectral sequence of the filtration `q ↦ {f ≤ a q}` has dimension `dim V`
times the number of critical points of index `n` with value in `(a q, a (q + 1)]`. -/
theorem IsMorse.finrank_filteredSpaceSpectralSequence_page_two_X (hf : IsMorse I f)
    (ha : Monotone a) {q : ℤ} (hband : IsCriticalBand I f (a q) (a (q + 1)))
    {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V]
    (pq : ℤ × ℤ) (hq : pq.2 = q) (n : ℕ) (hn : pq.1 + pq.2 = -n) :
    finrank k (((filteredSpaceSpectralSequence (Y := TopCat.of M) V
        ((sublevel_mono f).comp ha)).page 2).X pq : ModuleCat k) =
      Nat.card {x : ↥(criticalPoints I f ∩ f ⁻¹' Ioc (a q) (a (q + 1))) //
        manifoldMorseIndex I f x = n} * finrank k V := by
  obtain ⟨c, hc, hcrit⟩ := hband.exists_mem_Ioo_forall_eq
  subst hq
  rw [(filteredSpaceSpectralSequenceFirstPageXIso V ((sublevel_mono f).comp ha) pq pq.2
    (pq.2 + 1) rfl rfl _ rfl n hn).toLinearEquiv.finrank_eq,
    hf.finrank_singularHomology_sublevelPair_eq hc.1 hc.2 hband.isCompact hcrit V n,
    criticalPoints_inter_preimage_singleton_eq hc hcrit]

/-! ### Convergence on a compact manifold -/

variable (I) in
include I in
/-- **The spectral sequence of the sublevels of a compact manifold converges to its homology.**
Let `M` be a compact boundaryless manifold, `f : M → ℝ` a function and `a : ℤ → ℝ` monotone with
`a q₀ < f ≤ a q₁`, so that the filtration `q ↦ {f ≤ a q}` is `∅` at `q₀` and `M` at `q₁`. On every
page `r ≥ 2` with `q₁ - q₀ + 1 ≤ r` of the spectral sequence of this filtration, the dimension of
`Hₙ(M; V)` is the sum, over `q₀ ≤ q < q₁`, of the dimensions of the objects at `(-n - q, q)`, the
positions of total degree `-n`. For a critical-band cut of a Morse or Morse–Bott function, the first
page at `(-n - q, q)` is the relative homology `Hₙ({f ≤ a (q + 1)}, {f ≤ a q}; V)` across the
critical level of the `q`th band. -/
theorem finrank_singularHomology_eq_sum_finrank_filteredSpaceSpectralSequence_page_X_sublevel
    [CompactSpace M] {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V]
    (ha : Monotone a) {q₀ q₁ : ℤ} (hq₀ : ∀ x, a q₀ < f x) (hq₁ : ∀ x, f x ≤ a q₁) (n : ℕ)
    {r : ℤ} (hr : 2 ≤ r) (hrq : q₁ - q₀ + 1 ≤ r) :
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj V).obj
        (TopCat.of M)) =
      ∑ q ∈ Finset.Ico q₀ q₁, finrank k (((filteredSpaceSpectralSequence (Y := TopCat.of M) V
        ((sublevel_mono f).comp ha)).page r).X (-n - q, q) : ModuleCat k) := by
  have := finite_singularHomology_of_compactSpace M I V n
  have hX₀ : ((fun b ↦ {x | f x ≤ b}) ∘ a) q₀ = ∅ :=
    eq_empty_of_forall_notMem fun x hx ↦ (hq₀ x).not_ge hx
  have hX := (sublevel_mono f).comp ha
  by_cases hq : q₀ ≤ q₁
  · exact hX.finrank_singularHomology_eq_sum_finrank_filteredSpaceSpectralSequence_page_X V hq
      hX₀ (eq_univ_of_forall hq₁) n hr hrq
  -- Otherwise `a q₁ ≤ a q₀ < f ≤ a q₁`, so `M` is empty and the filtration is `M` from `q₀` on.
  rw [Finset.Ico_eq_empty_of_le (not_le.1 hq).le, Finset.sum_empty,
    hX.finrank_singularHomology_eq_sum_finrank_filteredSpaceSpectralSequence_page_X V le_rfl hX₀
      (eq_univ_of_forall fun x ↦ (hq₁ x).trans (ha (not_le.1 hq).le)) n hr (by lia),
    Finset.Ico_self, Finset.sum_empty]

/-! ### Degeneration in the lacunary case -/

/-- A nonzero object on the first page at `(p, q)` comes from a critical point of index
`-(p + q)` with value in `(a q, a (q + 1)]`. -/
private theorem exists_of_not_isZero_page_two_X (hf : IsMorse I f) (ha : Monotone a)
    {pq : ℤ × ℤ} (hband : IsCriticalBand I f (a pq.2) (a (pq.2 + 1)))
    (h : ¬IsZero (((filteredSpaceSpectralSequence (Y := TopCat.of M) R
      ((sublevel_mono f).comp ha)).page 2).X pq)) :
    ∃ x ∈ criticalPoints I f, f x ∈ Ioc (a pq.2) (a (pq.2 + 1)) ∧
      (manifoldMorseIndex I f x : ℤ) = -(pq.1 + pq.2) := by
  by_cases hpos : 0 < pq.1 + pq.2
  · exact absurd (isZero_filteredSpaceSpectralSequence_page_two_X R _ pq hpos) h
  have hn : pq.1 + pq.2 = -((-(pq.1 + pq.2)).toNat : ℕ) := by lia
  by_contra hne
  push Not at hne
  exact h (hf.isZero_filteredSpaceSpectralSequence_page_two_X R ha hband pq rfl _ hn
    fun x hx hfx hidx ↦ hne x hx hfx (by rw [hidx]; lia))

variable (hf : IsMorse I f) (ha : IsCriticalBandCut I f a)
  (hind : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
    manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1)
include hf ha hind

/-- If no two critical points have indices differing by one, of two positions of the first page
whose total degrees differ by one, at least one carries the zero object. -/
private theorem isZero_or_isZero_page_two_X {pq pq' : ℤ × ℤ}
    (hdeg : pq.1 + pq.2 + 1 = pq'.1 + pq'.2) :
    IsZero (((filteredSpaceSpectralSequence (Y := TopCat.of M) R
        ((sublevel_mono f).comp ha.monotone)).page 2).X pq) ∨
      IsZero (((filteredSpaceSpectralSequence (Y := TopCat.of M) R
        ((sublevel_mono f).comp ha.monotone)).page 2).X pq') := by
  by_contra h
  rw [not_or] at h
  obtain ⟨x, hx, -, hxn⟩ :=
    exists_of_not_isZero_page_two_X R hf ha.monotone (ha.isCriticalBand _) h.1
  obtain ⟨y, hy, -, hyn⟩ :=
    exists_of_not_isZero_page_two_X R hf ha.monotone (ha.isCriticalBand _) h.2
  exact hind x hx y hy (by lia)

/-- **Lacunary degeneration.** Let `f` be a Morse function and `a : ℤ → ℝ` a critical-band cut of
`f`: monotone, with every band `f⁻¹[a q, a (q + 1)]` compact with at most one critical value, lying
strictly between `a q` and `a (q + 1)`. If no two critical points of `f` have indices differing by
one, every differential on every page of the spectral sequence of the filtration `q ↦ {f ≤ a q}`
vanishes. -/
theorem IsMorse.filteredSpaceSpectralSequence_page_d_eq_zero_of_forall_ne_add_one (r : ℤ)
    (hr : 2 ≤ r) (pq pq' : ℤ × ℤ) :
    ((filteredSpaceSpectralSequence (Y := TopCat.of M) R
      ((sublevel_mono f).comp ha.monotone)).page r).d pq pq' = 0 :=
  SpectralSequence.page_d_eq_zero_of_isZero_or_isZero _
    (fun _ _ ↦ isZero_or_isZero_page_two_X R hf ha hind) r hr pq pq'

/-- **The graded homology in the lacunary case.** Let `f` be a Morse function and `a : ℤ → ℝ` a
critical-band cut of `f`, starting below and ending above all values of `f`: monotone, with every
band `f⁻¹[a q, a (q + 1)]` compact with at most one critical value, lying strictly between `a q`
and `a (q + 1)`; then `M` is compact. Filter `Hₙ(M; R)` by the images `F_q Hₙ` of the homology of
the sublevels `{f ≤ a q}`. If no two critical points have indices differing by one, the graded
piece `F_{q+1} Hₙ / F_q Hₙ` is the coproduct of one copy of `R` for each critical point of index
`n` with value in `(a q, a (q + 1)]`. The graded piece is written as the cokernel of the inclusion
`F_q Hₙ ⟶ F_{q+1} Hₙ` of the filtration of the abutment of the spectral sequence, which is `Hₙ(M)`
in total degree `p + q = -n` (`TauCeti.chainFiltrationAbutmentIso`). -/
theorem IsMorse.nonempty_cokernel_abutmentFiltrationMap_iso_sigma_of_forall_ne_add_one
    {q₀ q₁ : ℤ} (hq₀ : ∀ x, a q₀ < f x) (hq₁ : ∀ x, f x ≤ a q₁) (pq : ℤ × ℤ) (n : ℕ)
    (hn : pq.1 + pq.2 = -n) :
    Nonempty (cokernel ((filteredSpaceSpectralObject (Y := TopCat.of M) R
        ((sublevel_mono f).comp ha.monotone)).abutmentFiltrationMap pq.2 (pq.1 + pq.2)) ≅
      ∐ fun _ : {x : ↥(criticalPoints I f ∩ f ⁻¹' Ioc (a pq.2) (a (pq.2 + 1))) //
        manifoldMorseIndex I f x = n} ↦ R) := by
  obtain ⟨e₂⟩ := hf.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma R ha.monotone
    (ha.isCriticalBand _) pq rfl n hn
  obtain ⟨e⟩ := nonempty_cokernel_abutmentFiltrationMap_iso_page_two_X_of_isZero_or_isZero R
    ((sublevel_mono f).comp ha.monotone)
    (eq_empty_of_forall_notMem fun x hx ↦ (hq₀ x).not_ge hx) (eq_univ_of_forall hq₁)
    (fun _ hpq' ↦ hpq'.elim (isZero_or_isZero_page_two_X R hf ha hind)
      fun h ↦ (isZero_or_isZero_page_two_X R hf ha hind h).symm)
  exact ⟨e ≪≫ e₂⟩

end TauCeti
