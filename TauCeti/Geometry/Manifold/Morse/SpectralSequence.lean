/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic
public import TauCeti.Geometry.Manifold.Morse.Cell.Homology
public import TauCeti.Topology.Instances.Real.SeparatingGrid

/-!
# The spectral sequence of the critical-level filtration

Let `f : M → ℝ` be a function and `a : ℤ → ℝ` a monotone sequence of levels. The sublevels
`M_{a q} = {f ≤ a q}` filter `M`, and the spectral sequence of this filtration of the singular
chains of `M` (`TauCeti.sublevelSpectralSequence`, an instance of
`TauCeti.filteredSpaceSpectralSequence`) has first page the relative homology of consecutive
sublevel pairs,

`E^{p,q} = Hₙ(M_{a (q + 1)}, M_{a q})`, with `p + q = -n`

(`TauCeti.sublevelSpectralSequenceFirstPageXIso`), in the cohomological indexing of
`CochainComplex.spectralSequence`, where the first page is numbered `2`. If `f` is bounded and the
levels pass below and above all its values, the filtration is finite and the spectral sequence
converges strongly to `H_*(M)` (`TauCeti.sublevelSpectralSequencePageXIsoGradedOfFinite`).

For a smooth function on a boundaryless manifold the first page only sees the critical levels:

* a compact band `f⁻¹[a q, a (q + 1)]` without critical points contributes nothing
  (`TauCeti.isZero_sublevelSpectralSequence_page_two_X`), since the lower sublevel is a deformation
  retract of the upper one;
* if the critical values in a compact band all lie in `(s, t)`, the band contributes the relative
  homology `Hₙ(M_t, M_s)` of the critical part of the band
  (`TauCeti.sublevelSpectralSequenceFirstPageXIsoOfCollars`).

When `f` has finitely many critical values, which holds for a Morse–Bott function on a compact
manifold (`TauCeti.IsMorseBottFamily.finite_image_criticalPoints`), the levels can be chosen
regular with at most one critical value in each band, so that the columns of the first page are
the relative homology groups `Hₙ(M_{c + ε}, M_{c - ε})` of the critical values `c`
(`TauCeti.exists_strictMono_isRegularValue_of_finite_image_criticalPoints`). This is the
critical-level filtration whose spectral sequence computes the homology of `M` from local data at
the critical levels. For a Morse function the column of a critical value `c` is free on the
critical points of level `c`, one copy of the coefficients in degree `n` for each critical point
of index `n` (`TauCeti.IsMorse.nonempty_sublevelSpectralSequence_page_two_X_iso_sigma`).

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. Bott, *Lectures on Morse theory, old and new*, Bulletin of the American Mathematical
  Society 7 (1982), 331–358, §1.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §§3, 5.
-/

public section

noncomputable section

open CategoryTheory Limits Filter Set
open scoped ContDiff Manifold

universe u v w

namespace TauCeti

section Topological

variable {M : Type u} [TopologicalSpace M]
  {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A)

/-- **The spectral sequence of a sublevel filtration.** For a function `f : M → ℝ` and a monotone
sequence of levels `a : ℤ → ℝ`, this is the spectral sequence of the filtration of `M` by the
sublevels `{f ≤ a q}`, with coefficients in `R`. Its first page is the relative homology of
consecutive sublevel pairs (`TauCeti.sublevelSpectralSequenceFirstPageXIso`). -/
abbrev sublevelSpectralSequence (f : M → ℝ) {a : ℤ → ℝ} (ha : Monotone a) :=
  filteredSpaceSpectralSequence (Y := TopCat.of M) R ((sublevel_mono f).comp ha)

/-- **The first page of the spectral sequence of a sublevel filtration.** The object at `(p, q)`
on the first page (numbered `2`) is the relative singular homology
`Hₙ({f ≤ a (q + 1)}, {f ≤ a q})`, where `p + q = -n`. -/
def sublevelSpectralSequenceFirstPageXIso (f : M → ℝ) {a : ℤ → ℝ} (ha : Monotone a)
    (pq : ℤ × ℤ) (n : ℕ) (hn : pq.1 + pq.2 = -n) :
    ((sublevelSpectralSequence R f ha).page 2).X pq ≅
      (sublevelPair f (ha (Int.le_add_one le_rfl) : a pq.2 ≤ a (pq.2 + 1))).singularHomology R
        n :=
  filteredSpaceSpectralSequenceFirstPageXIso R _ pq pq.2 (pq.2 + 1) rfl rfl _ rfl n hn

/-- **Strong convergence of the spectral sequence of a sublevel filtration.** If every value of `f`
lies in `(a q₀, a q₁]`, then on every page `r ≥ 2` with `q - r + 2 ≤ q₀` and `q₁ ≤ q + r - 1`, the
object at `(p, q)` is the graded piece `F_{q+1} H / F_q H` of the filtration of the abutment in
degree `p + q`, which is `H_{-(p+q)}(M)` by `TauCeti.filteredSpaceAbutmentIso`. -/
def sublevelSpectralSequencePageXIsoGradedOfFinite {f : M → ℝ} {a : ℤ → ℝ} (ha : Monotone a)
    {q₀ q₁ : ℤ} (h₀ : ∀ x, a q₀ < f x) (h₁ : ∀ x, f x ≤ a q₁) (r : ℤ) (hr : 2 ≤ r)
    (pq : ℤ × ℤ) (hr₀ : pq.2 - r + 2 ≤ q₀) (hr₁ : q₁ ≤ pq.2 + r - 1) :
    ((sublevelSpectralSequence R f ha).page r).X pq ≅
      cokernel ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        (monotone_singularChainFiltration (Y := TopCat.of M) R
          ((sublevel_mono f).comp ha)))).abutmentFiltrationMap
          pq.2 (pq.1 + pq.2)) :=
  filteredSpaceSpectralSequencePageXIsoGradedOfFinite R _
    (eq_empty_iff_forall_notMem.2 fun x hx ↦ (h₀ x).not_ge hx) (eq_univ_of_forall h₁) r hr pq
    hr₀ hr₁

end Topological

section Manifold

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ} {a : ℤ → ℝ}
  {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A)

/-- **Bands without critical points do not contribute.** If the band `f⁻¹[a q, a (q + 1)]` is
compact and contains no critical point of the smooth function `f`, the first page of the
spectral sequence of the sublevel filtration vanishes in column `q`. -/
theorem isZero_sublevelSpectralSequence_page_two_X (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (ha : Monotone a) (pq : ℤ × ℤ) (hcompact : IsCompact (f ⁻¹' Icc (a pq.2) (a (pq.2 + 1))))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∉ Icc (a pq.2) (a (pq.2 + 1))) :
    IsZero (((sublevelSpectralSequence R f ha).page 2).X pq) := by
  rcases lt_or_ge 0 (pq.1 + pq.2) with hpos | hle
  · exact isZero_filteredSpaceSpectralSequence_page_two_X R _ pq hpos
  obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hle
  exact (isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero hf _ hcompact
    (fun x h₁ h₂ hx ↦ hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) ⟨h₁, h₂⟩) R n).of_iso
    (sublevelSpectralSequenceFirstPageXIso R f ha pq n hn)

/-- **The first page sees only the critical part of a band.** Let the band `f⁻¹[a q, a (q + 1)]`
be compact, and let every critical value of the smooth function `f` in `[a q, a (q + 1)]` lie in
`(s, t)`, where `a q ≤ s ≤ t ≤ a (q + 1)`. Then the object at `(p, q)` on the first page of the
spectral sequence of the sublevel filtration is the relative singular homology
`Hₙ({f ≤ t}, {f ≤ s})`, where `p + q = -n`. -/
def sublevelSpectralSequenceFirstPageXIsoOfCollars (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (ha : Monotone a) (pq : ℤ × ℤ) (n : ℕ) (hn : pq.1 + pq.2 = -n)
    (hcompact : IsCompact (f ⁻¹' Icc (a pq.2) (a (pq.2 + 1)))) {s t : ℝ} (hs : a pq.2 ≤ s)
    (hst : s ≤ t) (ht : t ≤ a (pq.2 + 1))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc (a pq.2) (a (pq.2 + 1)) → f x ∈ Ioo s t) :
    ((sublevelSpectralSequence R f ha).page 2).X pq ≅
      (sublevelPair f hst).singularHomology R n :=
  have hband {s' t' : ℝ} (hs' : a pq.2 ≤ s') (ht' : t' ≤ a (pq.2 + 1)) :
      IsCompact (f ⁻¹' Icc s' t') :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.continuous)
      (preimage_mono (Icc_subset_Icc hs' ht'))
  sublevelSpectralSequenceFirstPageXIso R f ha pq n hn ≪≫
    singularHomologySublevelPairIsoOfCollars hf hs hst ht (hband le_rfl (hst.trans ht))
      (hband (hs.trans hst) le_rfl)
      (fun x h₁ h₂ hx ↦ by
        have := hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) ⟨h₁, by linarith⟩
        linarith [this.1])
      (fun x h₁ h₂ hx ↦ by
        have := hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx) ⟨by linarith, h₂⟩
        linarith [this.2])
      R n

/-- **The first page of the Morse spectral sequence is free on the critical points.** Let `f` be
a Morse function, let the band `f⁻¹[a q, a (q + 1)]` be compact, and let its only critical value be
`c`, with `a q < c < a (q + 1)`. Then the object at `(p, q)` on the first page of the spectral
sequence of the sublevel filtration is the coproduct of one copy of `R` for each critical point of
index `n` on the level `c`, where `p + q = -n`. -/
theorem IsMorse.nonempty_sublevelSpectralSequence_page_two_X_iso_sigma (hf : IsMorse I f)
    (ha : Monotone a) (pq : ℤ × ℤ) (n : ℕ) (hn : pq.1 + pq.2 = -n)
    (hcompact : IsCompact (f ⁻¹' Icc (a pq.2) (a (pq.2 + 1)))) {c : ℝ} (hac : a pq.2 < c)
    (hca : c < a (pq.2 + 1))
    (hc : ∀ x ∈ criticalPoints I f, f x ∈ Icc (a pq.2) (a (pq.2 + 1)) → f x = c) :
    Nonempty (((sublevelSpectralSequence R f ha).page 2).X pq ≅
      ∐ fun _ : {p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) // manifoldMorseIndex I f p = n} ↦ R) := by
  -- Shrink the band to `[c - δ, c + δ]`, and then to a band `[c - ε, c + ε]` across which the
  -- relative homology is free on the critical points of level `c`.
  set δ := min (c - a pq.2) (a (pq.2 + 1) - c)
  have hδ : 0 < δ := lt_min (sub_pos.2 hac) (sub_pos.2 hca)
  have hδ₁ : δ ≤ c - a pq.2 := min_le_left _ _
  have hδ₂ : δ ≤ a (pq.2 + 1) - c := min_le_right _ _
  obtain ⟨ε, hε, hεδ, h⟩ := hf.exists_singularHomology_sublevelPair_iso_sigma (c := c) hδ
    (hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.contMDiff.continuous)
      (preimage_mono (Icc_subset_Icc (by linarith) (by linarith))))
  obtain ⟨e⟩ := h R n
  exact ⟨sublevelSpectralSequenceFirstPageXIsoOfCollars R hf.contMDiff ha pq n hn hcompact
    (by linarith) (by linarith) (by linarith)
    (fun x hx hxI ↦ by rw [hc x hx hxI]; constructor <;> linarith) ≪≫ e⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- **Critical-level filtrations.** If the smooth function `f` on a compact manifold has finitely
many critical values, there is a strictly increasing sequence `a : ℤ → ℝ` of regular values of `f`
with `a q₀ < f ≤ a q₁` for some `q₀` and `q₁`, such that each band `f⁻¹[a q, a (q + 1)]` contains
at most one critical value. The sublevels `{f ≤ a q}` then filter `M` by its critical levels.
When `f` is smooth, `TauCeti.isZero_sublevelSpectralSequence_page_two_X` and
`TauCeti.sublevelSpectralSequenceFirstPageXIsoOfCollars` identify the columns of the first page
of its spectral sequence: a band without critical values contributes nothing, and a band
containing the critical value `c` contributes the relative homology of
`({f ≤ c + ε}, {f ≤ c - ε})` for every small `ε > 0`. -/
theorem exists_strictMono_isRegularValue_of_finite_image_criticalPoints [CompactSpace M]
    (hf : Continuous f) (hfin : (f '' criticalPoints I f).Finite) :
    ∃ a : ℤ → ℝ, StrictMono a ∧ (∀ q, IsRegularValue I 𝓘(ℝ) f (a q)) ∧
      (∃ q₀, ∀ x, a q₀ < f x) ∧ (∃ q₁, ∀ x, f x ≤ a q₁) ∧
      ∀ q, (f '' criticalPoints I f ∩ Icc (a q) (a (q + 1))).Subsingleton := by
  obtain ⟨a, ha, hbot, htop, hreg, hsub⟩ := hfin.exists_strictMono_notMem_subsingleton_inter_Icc
  obtain ⟨m, hm⟩ := (isCompact_range hf).bddBelow
  obtain ⟨m', hm'⟩ := (isCompact_range hf).bddAbove
  obtain ⟨q₀, hq₀⟩ := (hbot.eventually (eventually_lt_atBot m)).exists
  obtain ⟨q₁, hq₁⟩ := (htop.eventually (eventually_ge_atTop m')).exists
  exact ⟨a, ha, fun q ↦ isRegularValue_iff_notMem_image_criticalPoints.2 (hreg q),
    ⟨q₀, fun x ↦ hq₀.trans_le (hm (mem_range_self x))⟩,
    ⟨q₁, fun x ↦ (hm' (mem_range_self x)).trans hq₁⟩, hsub⟩

end Manifold

end TauCeti
