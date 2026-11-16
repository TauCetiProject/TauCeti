/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Int
public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology
public import TauCeti.AlgebraicTopology.Singular.Sublevel
public import TauCeti.Geometry.Manifold.Morse.Projectivization
public import TauCeti.Geometry.Manifold.Morse.SpectralSequence

/-!
# The critical-band spectral sequence of the real projective plane

Let `f = TauCeti.projectiveMomentFunction ℝ w` be the moment function on
`ℝℙ² = ℙ ℝ (Fin 3 → ℝ)`, `f[x] = (∑ i, w i * x i ^ 2) / ∑ i, x i ^ 2`, and let `a : ℤ → ℝ` be
monotone with `a k < w k < a (k + 1)` for `k = 0, 1, 2`. Then the weights increase, `f` is a Morse
function whose critical points are the coordinate points `[eₖ]`, of index `k` and value `w k`, and
the band `f⁻¹[a k, a (k + 1)]` contains `[eₖ]` and no other critical point. This file computes the
first two pages of the spectral sequence of the filtration `q ↦ {f ≤ a q}`
(`TauCeti.filteredSpaceSpectralSequence`), with singular chains of degree `n` in degree `-n`, so
that the band of `[eₖ]` sits at `(-2k, k)`.

* **First page.** The object at `(-2k, k)` is one copy of the coefficients, for any coefficients
  (`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`), and
  every other object is zero
  (`TauCeti.isZero_filteredSpaceSpectralSequence_page_two_X_projectiveMomentFunction`).
* **First differentials.** With integer coefficients, the differential from the band of the
  maximum to the band of the saddle, `ℤ ⟶ ℤ` from `(-4, 2)` to `(-2, 1)`, is injective with
  cokernel `ℤ/2`, so it is multiplication by `±2`; these are
  `TauCeti.mono_filteredSpaceSpectralSequence_page_two_d_projectiveMomentFunction`,
  `TauCeti.nonempty_cokernel_filteredSpaceSpectralSequence_page_two_d_iso_projectiveMomentFunction`
  and
  `filteredSpaceSpectralSequence_page_two_d_eq_two_smul_or_eq_neg_two_smul_projectiveMomentFunction`
  respectively. For any coefficients, the differential from the band of the saddle to the band of
  the minimum vanishes
  (`TauCeti.filteredSpaceSpectralSequence_page_two_d_eq_zero_projectiveMomentFunction`).
* **Second page.** For any coefficients, the object at `(0, 0)` of the second page (numbered `3`)
  is one copy of the coefficients
  (`TauCeti.nonempty_filteredSpaceSpectralSequence_page_three_X_zero_iso_projectiveMomentFunction`).
  With integer coefficients, the object at `(-2, 1)` is `ℤ/2`
  (`TauCeti.nonempty_filteredSpaceSpectralSequence_page_three_X_iso_zmod_projectiveMomentFunction`)
  and every other object is zero
  (`TauCeti.isZero_filteredSpaceSpectralSequence_page_three_X_projectiveMomentFunction`), so the
  second page consists of the integral homology groups `ℤ`, `ℤ/2`, `0` of `ℝℙ²`.

So the first page is the relative homology of the bands, free on the critical points, but it is not
yet the second page: its differential can be nonzero, and the critical counts `1, 1, 1` exceed the
integral Betti numbers `1, 0, 0`.

The differentials are the connecting maps of triples of sublevels
(`TauCeti.filteredSpaceSpectralSequence_first_page_d_eq`), and they are computed from the long exact
sequences of those triples. The inputs are the relative homology of a band with one critical point
(`TauCeti.IsMorse.nonempty_singularHomology_sublevelPair_iso_sigma`), the integral homology of
`ℝℙ²`, `H₁ = ℤ/2` and `H₂ = 0`, computed from its cellular chain complex
(`TauCeti.RealProjectiveSpace.singularHomologyProjectivizationIntLinearEquivOfOdd`), and the
injectivity of the zeroth homology of the bottom sublevel into that of every larger sublevel. The
bottom sublevel is path-connected
(`TauCeti.isPathConnected_setOf_projectiveMomentFunction_le`), and a map out of a path-connected
space is injective on zeroth homology
(`TauCeti.mono_singularHomologyMap_zero_of_pathConnectedSpace`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3 and §4.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Example 2.42 (the cellular
  chain complex of `ℝℙⁿ`, with differentials `0` and `2`).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  §2.2.
-/

public section

noncomputable section

open CategoryTheory Limits Set Projectivization
open scoped Manifold LinearAlgebra.Projectivization

namespace TauCeti

variable {w : Fin 3 → ℝ}

variable {A : Type*} [Category A] [Abelian A] [HasCoproducts.{0} A] (R : A)

/-- The relative homology across a band of the moment function on `ℝℙ²` whose only critical value
is `w k`, as a coproduct over the critical points of index `n` on that level. -/
private theorem nonempty_singularHomology_sublevelPair_iso_sigma (hw : StrictMono w) {s t : ℝ}
    (k : Fin 3) (hs : s < w k) (ht : w k < t) (hcrit : ∀ i, w i ∈ Icc s t → i = k) (n : ℕ) :
    Nonempty ((sublevelPair (projectiveMomentFunction ℝ w) (hs.trans ht).le).singularHomology
        R n ≅
      ∐ fun _ : {p : ↥(criticalPoints 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) ∩
          projectiveMomentFunction ℝ w ⁻¹' {w k}) //
          manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) p = n} ↦ R) := by
  refine IsMorse.nonempty_singularHomology_sublevelPair_iso_sigma
    (isMorse_projectiveMomentFunction hw.injective) hs ht
      (isClosed_Icc.preimage (continuous_projectiveMomentFunction w)).isCompact ?_ R n
  intro x hx hxst
  rw [criticalPoints_projectiveMomentFunction hw.injective] at hx
  obtain ⟨j, rfl⟩ := hx
  rw [projectiveMomentFunction_mk_single] at hxst ⊢
  rw [hcrit j hxst]

/-- Across a band of the moment function on `ℝℙ²` whose only critical value is `w k`, the relative
homology in degree `k` is one copy of the coefficients. -/
private theorem nonempty_singularHomology_sublevelPair_iso (hw : StrictMono w) {s t : ℝ}
    (k : Fin 3) (hs : s < w k) (ht : w k < t) (hcrit : ∀ i, w i ∈ Icc s t → i = k) :
    Nonempty ((sublevelPair (projectiveMomentFunction ℝ w) (hs.trans ht).le).singularHomology
      R k ≅ R) := by
  obtain ⟨e⟩ := nonempty_singularHomology_sublevelPair_iso_sigma R hw k hs ht hcrit k
  have hk := criticalPoints_projectiveMomentFunction_inter_preimage_singleton (𝕜 := ℝ)
    hw.injective k
  have : Unique {p : ↥(criticalPoints 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) ∩
      projectiveMomentFunction ℝ w ⁻¹' {w k}) //
      manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) p = k} :=
    { default := ⟨⟨_, (Set.ext_iff.1 hk _).2 rfl⟩,
        by rw [manifoldMorseIndex_projectiveMomentFunction_of_strictMono hw k,
          Module.finrank_self, one_mul]⟩
      uniq := fun p ↦ Subtype.ext (Subtype.ext ((Set.ext_iff.1 hk p.1.1).1 p.1.2)) }
  exact ⟨e ≪≫ coproductUniqueIso _⟩

/-- Across a band of the moment function on `ℝℙ²` whose only critical value is `w k`, the relative
homology vanishes in every degree other than `k`. -/
private theorem isZero_singularHomology_sublevelPair (hw : StrictMono w) {s t : ℝ}
    (k : Fin 3) (hs : s < w k) (ht : w k < t) (hcrit : ∀ i, w i ∈ Icc s t → i = k) {n : ℕ}
    (hn : n ≠ k) :
    IsZero ((sublevelPair (projectiveMomentFunction ℝ w) (hs.trans ht).le).singularHomology
      R n) := by
  obtain ⟨e⟩ := nonempty_singularHomology_sublevelPair_iso_sigma R hw k hs ht hcrit n
  have : IsEmpty {p : ↥(criticalPoints 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) ∩
      projectiveMomentFunction ℝ w ⁻¹' {w k}) //
      manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) p = n} := by
    refine ⟨fun p ↦ hn ?_⟩
    have hp := (Set.ext_iff.1 (criticalPoints_projectiveMomentFunction_inter_preimage_singleton
      hw.injective k) p.1.1).1 p.1.2
    rw [← p.2, mem_singleton_iff.1 hp,
      manifoldMorseIndex_projectiveMomentFunction_of_strictMono hw k, Module.finrank_self, one_mul]
  exact ((IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ isEmptyElim)).of_iso e

variable {a : ℤ → ℝ}

/-- Weights separated by the values of a monotone sequence are increasing. -/
private theorem strictMono_of_mem_Ioo (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) :
    StrictMono w :=
  Fin.strictMono_iff_lt_succ.2 fun i ↦ (hcut i.castSucc).2.trans_le
    (le_of_eq (by simp)) |>.trans (hcut i.succ).1

/-- The band `[a q, a (q + 1)]` of a monotone sequence separating the weights contains the weight
`w k` exactly when `q = k`. -/
private theorem mem_Icc_iff (ha : Monotone a)
    (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) (k : Fin 3) (q : ℤ) :
    w k ∈ Icc (a q) (a (q + 1)) ↔ q = k := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ Ioo_subset_Icc_self (hcut k)⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact (h.2.trans_lt (lt_of_le_of_lt (ha (by omega)) (hcut k).1)).false
  · exact ((hcut k).2.trans_le (ha (by omega)) |>.trans_le h.1).false

private theorem eq_of_mem_Icc (ha : Monotone a)
    (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) (k : Fin 3) :
    ∀ i, w i ∈ Icc (a k) (a ((k : ℕ) + 1)) → i = k := fun i hi ↦
  Fin.ext (by exact_mod_cast ((mem_Icc_iff ha hcut i k).1 hi).symm)

/-- **The first page of the critical-band spectral sequence of `ℝℙ²`.** Let `f` be the moment
function on `ℝℙ²` with weights `w`, and let `a` be a monotone sequence with
`a k < w k < a (k + 1)` for `k = 0, 1, 2`, so that the band `f⁻¹[a k, a (k + 1)]` contains the
critical point `[eₖ]` of index `k` and no other. On the first page of the spectral sequence of the
filtration `q ↦ {f ≤ a q}`, the object at `(-2k, k)`, of total degree `-k`, is one copy of the
coefficients. -/
theorem nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction
    (ha : Monotone a) (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) (k : Fin 3) :
    Nonempty (((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ))) R
      ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).X
        (-(2 * (k : ℕ) : ℤ), ((k : ℕ) : ℤ)) ≅ R) := by
  obtain ⟨e⟩ := nonempty_singularHomology_sublevelPair_iso R (strictMono_of_mem_Ioo hcut) k
    (hcut k).1 (hcut k).2 (eq_of_mem_Icc ha hcut k)
  exact ⟨filteredSpaceSpectralSequenceFirstPageXIso (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ))) R
    ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha) _ _ _ rfl rfl _ rfl k
      (by push_cast; ring) ≪≫ e⟩

/-- **The first page of the critical-band spectral sequence of `ℝℙ²` away from the critical
points.** Under the hypotheses of
`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, every
object of the first page other than those at `(0, 0)`, `(-2, 1)` and `(-4, 2)` is zero. -/
theorem isZero_filteredSpaceSpectralSequence_page_two_X_projectiveMomentFunction
    (ha : Monotone a) (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) (pq : ℤ × ℤ)
    (hpq : ∀ k : Fin 3, pq ≠ (-(2 * (k : ℕ) : ℤ), ((k : ℕ) : ℤ))) :
    IsZero (((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ))) R
      ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).X pq) := by
  obtain ⟨p, q⟩ := pq
  rcases lt_or_ge 0 (p + q) with hpos | hle
  · exact isZero_filteredSpaceSpectralSequence_page_two_X _ _ _ hpos
  obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hle
  by_cases hq : ∃ k : Fin 3, ((k : ℕ) : ℤ) = q
  · obtain ⟨k, rfl⟩ := hq
    have hnk : n ≠ k := by
      rintro rfl
      exact hpq k (Prod.ext (by simp only at hn ⊢; omega) rfl)
    exact (isZero_singularHomology_sublevelPair R (strictMono_of_mem_Ioo hcut) k (hcut k).1
      (hcut k).2 (eq_of_mem_Icc ha hcut k) hnk).of_iso
        (filteredSpaceSpectralSequenceFirstPageXIso (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ))) R
          ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha) _ _ _ rfl rfl _ rfl n hn)
  · push Not at hq
    refine isZero_filteredSpaceSpectralSequence_page_two_X_of_forall_notMem R
      (contMDiff_projectiveMomentFunction w) ha (p, q)
      (isClosed_Icc.preimage (continuous_projectiveMomentFunction w)).isCompact fun x hx hfx ↦ ?_
    rw [criticalPoints_projectiveMomentFunction (strictMono_of_mem_Ioo hcut).injective] at hx
    obtain ⟨k, rfl⟩ := hx
    rw [projectiveMomentFunction_mk_single] at hfx
    exact hq k ((mem_Icc_iff ha hcut k q).1 hfx).symm

/-! ### Sublevel triples -/

/-- The sublevel triple `({f ≤ u}, {f ≤ t}, {f ≤ s})` of the moment function on `ℝℙ²`. -/
private abbrev sublevelTriple (w : Fin 3 → ℝ) {s t u : ℝ} (hst : s ≤ t) (htu : t ≤ u) :
    TopTriple :=
  TopTriple.ofInclusions (X := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
    (sublevel_mono (projectiveMomentFunction ℝ w) hst)
    (sublevel_mono (projectiveMomentFunction ℝ w) htu)

/-- A sublevel pair covering `ℝℙ²` has the homology of `ℝℙ²`. -/
private def singularHomologySublevelPairIsoOfLT (hw : Monotone w) {s₀ s₃ : ℝ} (h₀ : s₀ < w 0)
    (h₃ : w 2 < s₃) (h : s₀ ≤ s₃) (n : ℕ) :
    (sublevelPair (projectiveMomentFunction ℝ w) h).singularHomology (ModuleCat.of ℤ ℤ) n ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (ℙ ℝ (Fin 3 → ℝ))) :=
  (singularHomologyIsoSublevelPair _
    (fun x ↦ h₀.trans_le (projectiveMomentFunction_mem_Icc hw x).1)
    (fun x ↦ ((projectiveMomentFunction_mem_Icc hw x).2.trans h₃.le)) _ n).symm

section Sublevels

variable (hw : StrictMono w) {s₀ s₁ s₂ s₃ : ℝ} (h₀ : s₀ < w 0) (h₁ : w 0 < s₁) (h₁' : s₁ < w 1)
  (h₂ : w 1 < s₂) (h₂' : s₂ < w 2) (h₃ : w 2 < s₃)
include hw

include h₁' in
private theorem eq_zero_of_mem_Icc : ∀ i, w i ∈ Icc s₀ s₁ → i = 0 := fun i hi ↦ by
  by_contra hne
  exact (hi.2.trans_lt h₁').not_ge (hw.monotone (Fin.pos_iff_ne_zero.2 hne))

include h₂ in
private theorem eq_two_of_mem_Icc : ∀ i, w i ∈ Icc s₂ s₃ → i = 2 := fun i hi ↦ by
  fin_cases i
  · exact absurd (h₂.trans_le hi.1) (hw.monotone (Fin.zero_le 1)).not_gt
  · exact absurd (h₂.trans_le hi.1) (lt_irrefl _)
  · rfl

include h₀ h₁ h₁' in
/-- Below the second critical value, the zeroth homology of the sublevel `{f ≤ s₁}` injects into
that of every larger sublevel, relative to the empty sublevel `{f ≤ s₀}`. -/
private theorem mono_singularHomologyMap_innerToTotal_zero {t : ℝ} (h : s₁ ≤ t) :
    Mono (TopPair.singularHomologyMap
      (TopTriple.innerToTotal.app (sublevelTriple w (h₀.trans h₁).le h)) R 0) := by
  set T := sublevelTriple w (h₀.trans h₁).le h
  -- The common subspace `{f ≤ s₀}` is empty, so both relative groups are absolute ones.
  have hempty : ∀ x, ¬ projectiveMomentFunction ℝ w x ≤ s₀ := fun x hx ↦
    ((projectiveMomentFunction_mem_Icc hw.monotone x).1.trans hx).not_gt h₀
  have : IsEmpty (TopTriple.innerPair.obj T).snd := ⟨fun x ↦ hempty x.1 x.2⟩
  have : IsEmpty (TopTriple.totalPair.obj T).snd := ⟨fun x ↦ hempty x.1 x.2⟩
  -- On absolute homology, the map is injective since `{f ≤ s₁}` is path-connected.
  have : PathConnectedSpace (TopTriple.innerPair.obj T).fst :=
    isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_setOf_projectiveMomentFunction_le
      h₁.le fun i hi ↦ h₁'.trans_le (hw.monotone (Fin.pos_iff_ne_zero.2 hi)))
  have : Mono (SSet.homologyMap (TopCat.toSSet.map
      (TopPair.Hom.fst (TopTriple.innerToTotal.app T))) R 0) :=
    mono_singularHomologyMap_zero_of_pathConnectedSpace R _
  have hπ : IsIso ((TopTriple.totalPair.obj T).singularHomologyπ R 0) := inferInstance
  rw [(IsIso.eq_inv_comp _).2 (TopPair.singularHomologyπ_naturality
    (TopTriple.innerToTotal.app T) R 0).symm]
  -- The source of `singularHomologyπ` is the homology of `(TopPair.toSSetPair.obj _).right`, which
  -- is that of `TopCat.toSSet.obj _` only up to unfolding, so instance search cannot match the
  -- composite and the instances are supplied as terms.
  exact @mono_comp _ _ _ _ _ _ inferInstance _
    (@mono_comp _ _ _ _ _ _ this _ (@IsIso.mono_of_iso _ _ _ _ _ hπ))

include h₀ h₁ h₁' in
/-- Below the second critical value, the connecting map
`H₁({f ≤ t}, {f ≤ s₁}) ⟶ H₀({f ≤ s₁}, {f ≤ s₀})` vanishes. -/
private theorem singularHomologyδ_one_eq_zero {t : ℝ} (h : s₁ ≤ t) :
    (sublevelTriple w (h₀.trans h₁).le h).singularHomologyδ R 1 0 = 0 := by
  have := mono_singularHomologyMap_innerToTotal_zero R hw h₀ h₁ h₁' h
  rw [← cancel_mono (TopPair.singularHomologyMap (TopTriple.innerToTotal.app
    (sublevelTriple w (h₀.trans h₁).le h)) R 0), TopTriple.singularHomologyδ_comp _ _ 1 0,
    zero_comp]

include h₀ h₁ h₁' h₃ in
/-- Below the second critical value, `H₂(ℝℙ², {f ≤ s₁}; ℤ) = 0`. -/
private theorem isZero_singularHomology_two_sublevelPair (h : s₁ ≤ s₃) :
    IsZero ((sublevelPair (projectiveMomentFunction ℝ w) h).singularHomology
      (ModuleCat.of ℤ ℤ) 2) :=
  ((sublevelTriple w (h₀.trans h₁).le h).singularHomology_exact_outer (ModuleCat.of ℤ ℤ)
    2 1).isZero_of_both_isZero
    ((RealProjectiveSpace.isZero_singularHomology_projectivization_of_even (N := 2) ℤ
      (isRegular_iff_ne_zero.2 two_ne_zero).right even_two two_ne_zero).of_iso
      (singularHomologySublevelPairIsoOfLT hw.monotone h₀ h₃ ((h₀.trans h₁).le.trans h) 2))
    (isZero_singularHomology_sublevelPair _ hw 0 h₀ h₁ (eq_zero_of_mem_Icc hw h₁') (by simp))

include h₀ h₁ h₁' h₃ in
/-- Below the second critical value, `H₁(ℝℙ², {f ≤ s₁}; ℤ) ≅ ℤ/2`. -/
private theorem nonempty_singularHomology_one_sublevelPair_iso (h : s₁ ≤ s₃) :
    Nonempty ((sublevelPair (projectiveMomentFunction ℝ w) h).singularHomology
      (ModuleCat.of ℤ ℤ) 1 ≅ ModuleCat.of ℤ (ZMod 2)) := by
  set T := sublevelTriple w (h₀.trans h₁).le h
  -- `H₁(f ≤ s₁, ∅) = 0`, so `H₁(ℝℙ²) ⟶ H₁(ℝℙ², {f ≤ s₁})` is injective.
  have : Mono (TopPair.singularHomologyMap (TopTriple.totalToOuter.app T)
      (ModuleCat.of ℤ ℤ) 1) :=
    (T.singularHomology_exact_total (ModuleCat.of ℤ ℤ) 1).mono_g
      ((isZero_singularHomology_sublevelPair _ hw 0 h₀ h₁ (eq_zero_of_mem_Icc hw h₁')
        (by simp)).eq_of_src _ _)
  -- The connecting map to `H₀(f ≤ s₁, ∅)` vanishes, so the map is also surjective.
  have : Epi (TopPair.singularHomologyMap (TopTriple.totalToOuter.app T)
      (ModuleCat.of ℤ ℤ) 1) :=
    (T.singularHomology_exact_outer (ModuleCat.of ℤ ℤ) 1 0).epi_f
      (singularHomologyδ_one_eq_zero _ hw h₀ h₁ h₁' h)
  have : IsIso (TopPair.singularHomologyMap (TopTriple.totalToOuter.app T)
      (ModuleCat.of ℤ ℤ) 1) := isIso_of_mono_of_epi _
  exact ⟨(asIso (TopPair.singularHomologyMap (TopTriple.totalToOuter.app T)
    (ModuleCat.of ℤ ℤ) 1)).symm ≪≫
      singularHomologySublevelPairIsoOfLT hw.monotone h₀ h₃ ((h₀.trans h₁).le.trans h) 1 ≪≫
        (RealProjectiveSpace.singularHomologyProjectivizationIntLinearEquivOfOdd (N := 2) odd_one
          (by norm_num)).toModuleIso⟩

include h₀ h₁ h₁' h₂ h₂' h₃ in
/-- Across the critical level of index two, the connecting map
`H₂({f ≤ s₃}, {f ≤ s₂}) ⟶ H₁({f ≤ s₂}, {f ≤ s₁})` is injective. -/
private theorem mono_singularHomologyδ_two :
    Mono ((sublevelTriple w (h₁'.trans h₂).le (h₂'.trans h₃).le).singularHomologyδ
      (ModuleCat.of ℤ ℤ) 2 1) :=
  ((sublevelTriple w (h₁'.trans h₂).le (h₂'.trans h₃).le).singularHomology_exact_outer
    (ModuleCat.of ℤ ℤ) 2 1).mono_g
    ((isZero_singularHomology_two_sublevelPair hw h₀ h₁ h₁' h₃
      ((h₁'.trans h₂).le.trans (h₂'.trans h₃).le)).eq_of_src _ _)

include h₀ h₁ h₁' h₂ h₂' h₃ in
/-- Across the critical level of index two, the connecting map
`H₂({f ≤ s₃}, {f ≤ s₂}) ⟶ H₁({f ≤ s₂}, {f ≤ s₁})` has cokernel `ℤ/2`. -/
private theorem nonempty_cokernel_singularHomologyδ_two_iso :
    Nonempty (cokernel ((sublevelTriple w (h₁'.trans h₂).le (h₂'.trans h₃).le).singularHomologyδ
      (ModuleCat.of ℤ ℤ) 2 1) ≅ ModuleCat.of ℤ (ZMod 2)) := by
  set T := sublevelTriple w (h₁'.trans h₂).le (h₂'.trans h₃).le
  -- `H₁({f ≤ s₃}, {f ≤ s₂}) = 0`, so `H₁({f ≤ s₂}, {f ≤ s₁}) ⟶ H₁({f ≤ s₃}, {f ≤ s₁})` is onto.
  have : Epi (TopPair.singularHomologyMap (TopTriple.innerToTotal.app T)
      (ModuleCat.of ℤ ℤ) 1) :=
    (T.singularHomology_exact_total (ModuleCat.of ℤ ℤ) 1).epi_f
      ((isZero_singularHomology_sublevelPair _ hw 2 h₂' h₃ (eq_two_of_mem_Icc hw h₂)
        (by simp)).eq_of_tgt _ _)
  obtain ⟨e⟩ := nonempty_singularHomology_one_sublevelPair_iso hw h₀ h₁ h₁' h₃
    ((h₁'.trans h₂).le.trans (h₂'.trans h₃).le)
  exact ⟨(cokernelIsCokernel _).coconePointUniqueUpToIso
    ((T.singularHomology_exact_inner (ModuleCat.of ℤ ℤ) 2 1).gIsCokernel) ≪≫ e⟩

end Sublevels

/-! ### The differentials and the second page -/

/-- The values of a monotone sequence separating the weights, in the order used below. -/
private theorem lt_of_mem_Ioo (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) :
    a 0 < w 0 ∧ w 0 < a 1 ∧ a 1 < w 1 ∧ w 1 < a 2 ∧ a 2 < w 2 ∧ w 2 < a 3 := by
  have h0 := hcut 0
  have h1 := hcut 1
  have h2 := hcut 2
  norm_num at h0 h1 h2
  exact ⟨h0.1, h0.2, h1.1, h1.2, h2.1, h2.2⟩

/-- On the first page, the differential from `(p, q)` to `pq' = (p + 2, q - 1)`, with
`p + q = -n'` and `n' = n + 1`, is the connecting map
`Hₙ'({f ≤ a q₂}, {f ≤ a q}) ⟶ Hₙ({f ≤ a q}, {f ≤ a q₀})` of the sublevel triple with
`q₀ = q - 1` and `q₂ = q + 1`, up to isomorphisms of its source and target. The indices `pq'`,
`q₀`, `q₂` and `n'` are arguments, so that they can be given as literals in normal form. -/
private theorem exists_page_two_d_eq (ha : Monotone a) {p q q₀ q₂ : ℤ} {n n' : ℕ}
    {pq' : ℤ × ℤ} (hn : p + q = -(n' : ℤ)) (hn' : n' = n + 1) (hpq' : pq' = (p + 2, q - 1))
    (hq₀ : q₀ = q - 1) (hq₂ : q₂ = q + 1) :
    ∃ (e₁ : ((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ))) R
        ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).X (p, q) ≅
          (TopTriple.outerPair.obj (sublevelTriple w (ha (by lia : q₀ ≤ q))
            (ha (by lia : q ≤ q₂)))).singularHomology R n')
      (e₂ : ((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ))) R
        ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).X pq' ≅
          (TopTriple.innerPair.obj (sublevelTriple w (ha (by lia : q₀ ≤ q))
            (ha (by lia : q ≤ q₂)))).singularHomology R n),
      ((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ))) R
        ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).d (p, q) pq' =
        e₁.hom ≫ (sublevelTriple w (ha (by lia : q₀ ≤ q)) (ha (by lia : q ≤ q₂))).singularHomologyδ
          R n' n ≫ e₂.inv := by
  subst hn' hpq' hq₀ hq₂
  exact ⟨_, _, filteredSpaceSpectralSequence_first_page_d_eq (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
    R ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha) q p n hn⟩

/-- **The differential of index two on the first page of `ℝℙ²` is injective.** Under the
hypotheses of
`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, with
integer coefficients, the differential from `(-4, 2)` to `(-2, 1)` on the first page, the
connecting map from the band of the maximum to the band of the saddle, is a monomorphism. -/
theorem mono_filteredSpaceSpectralSequence_page_two_d_projectiveMomentFunction
    (ha : Monotone a) (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) :
    Mono (((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
      (ModuleCat.of ℤ ℤ) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).d
        (-4, 2) (-2, 1)) := by
  obtain ⟨h₀, h₁, h₁', h₂, h₂', h₃⟩ := lt_of_mem_Ioo hcut
  obtain ⟨e₁, e₂, hd⟩ := exists_page_two_d_eq (ModuleCat.of ℤ ℤ) ha (p := -4) (q := 2)
    (q₀ := 1) (q₂ := 3) (n := 1) (n' := 2) (pq' := (-2, 1)) (by norm_num) rfl (by norm_num)
    (by norm_num) (by norm_num)
  have := mono_singularHomologyδ_two (strictMono_of_mem_Ioo hcut) h₀ h₁ h₁' h₂ h₂' h₃
  rw [hd]
  infer_instance

/-- **The differential of index two on the first page of `ℝℙ²` has cokernel `ℤ/2`.** Under the
hypotheses of
`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, with
integer coefficients, the cokernel of the differential from `(-4, 2)` to `(-2, 1)` on the first
page is `ℤ/2`. Together with
`TauCeti.mono_filteredSpaceSpectralSequence_page_two_d_projectiveMomentFunction`, this says that
this differential `ℤ ⟶ ℤ` is multiplication by `±2`. -/
theorem nonempty_cokernel_filteredSpaceSpectralSequence_page_two_d_iso_projectiveMomentFunction
    (ha : Monotone a) (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) :
    Nonempty (cokernel (((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
      (ModuleCat.of ℤ ℤ) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).d
        (-4, 2) (-2, 1)) ≅ ModuleCat.of ℤ (ZMod 2)) := by
  obtain ⟨h₀, h₁, h₁', h₂, h₂', h₃⟩ := lt_of_mem_Ioo hcut
  obtain ⟨e₁, e₂, hd⟩ := exists_page_two_d_eq (ModuleCat.of ℤ ℤ) ha (p := -4) (q := 2)
    (q₀ := 1) (q₂ := 3) (n := 1) (n' := 2) (pq' := (-2, 1)) (by norm_num) rfl (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨e⟩ := nonempty_cokernel_singularHomologyδ_two_iso (strictMono_of_mem_Ioo hcut) h₀ h₁
    h₁' h₂ h₂' h₃
  rw [hd]
  exact ⟨cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫ e⟩

/-- **The differential of index two on the first page of `ℝℙ²` is multiplication by `±2`.**
Under the hypotheses of
`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, with
integer coefficients, read through any identifications of the objects at `(-4, 2)` and `(-2, 1)` of
the first page with `ℤ`, the differential between them is multiplication by `2` or by `-2`; the
sign depends on the identifications. -/
theorem
    filteredSpaceSpectralSequence_page_two_d_eq_two_smul_or_eq_neg_two_smul_projectiveMomentFunction
    (ha : Monotone a) (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1)))
    (e₂ : ((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
      (ModuleCat.of ℤ ℤ) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).X
        (-4, 2) ≅ ModuleCat.of ℤ ℤ)
    (e₁ : ((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
      (ModuleCat.of ℤ ℤ) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).X
        (-2, 1) ≅ ModuleCat.of ℤ ℤ) :
    e₂.inv ≫ ((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
        (ModuleCat.of ℤ ℤ) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).d
          (-4, 2) (-2, 1) ≫ e₁.hom = (2 : ℤ) • 𝟙 _ ∨
      e₂.inv ≫ ((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
        (ModuleCat.of ℤ ℤ) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).d
          (-4, 2) (-2, 1) ≫ e₁.hom = (-2 : ℤ) • 𝟙 _ := by
  obtain ⟨e⟩ :=
    nonempty_cokernel_filteredSpaceSpectralSequence_page_two_d_iso_projectiveMomentFunction ha hcut
  exact ModuleCat.eq_smul_id_or_eq_neg_smul_id_of_cokernel_iso_zmod (n := 2) _
    (cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫ e)

/-- **The differential of index one on the first page of `ℝℙ²` vanishes.** Under the hypotheses
of `TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, for
any coefficients, the differential from `(-2, 1)` to `(0, 0)` on the first page, the connecting
map from the band of the saddle to the band of the minimum, is zero. -/
theorem filteredSpaceSpectralSequence_page_two_d_eq_zero_projectiveMomentFunction
    (ha : Monotone a) (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) :
    ((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ))) R
      ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).d (-2, 1) (0, 0) = 0 := by
  obtain ⟨h₀, h₁, h₁', h₂, -, -⟩ := lt_of_mem_Ioo hcut
  obtain ⟨e₁, e₂, hd⟩ := exists_page_two_d_eq R ha (p := -2) (q := 1) (q₀ := 0) (q₂ := 2)
    (n := 0) (n' := 1) (pq' := (0, 0)) (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
  rw [hd, singularHomologyδ_one_eq_zero R (strictMono_of_mem_Ioo hcut) h₀ h₁ h₁'
    (h₁'.trans h₂).le, zero_comp, comp_zero]

/-- **The second page of `ℝℙ²` vanishes away from total degrees `0` and `-1`.** Under the
hypotheses of
`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, with
integer coefficients, every object of the second page (numbered `3`) other than those at `(0, 0)`
and `(-2, 1)` is zero. At `(-4, 2)` this is because the differential out of it on the first page
is injective. -/
theorem isZero_filteredSpaceSpectralSequence_page_three_X_projectiveMomentFunction
    (ha : Monotone a) (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) (pq : ℤ × ℤ)
    (hpq₀ : pq ≠ (0, 0)) (hpq₁ : pq ≠ (-2, 1)) :
    IsZero (((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
      (ModuleCat.of ℤ ℤ) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 3).X
        pq) := by
  set E := filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
    (ModuleCat.of ℤ ℤ) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)
  by_cases hpq₂ : pq = (-4, 2)
  · subst hpq₂
    refine IsZero.of_iso ?_ (E.iso 2 3 (-4, 2)).symm
    refine HomologicalComplex.ExactAt.isZero_homology (((E.page 2).exactAt_iff' (-6, 3) (-4, 2)
      (-2, 1) ((ComplexShape.up' _).prev_eq' (by norm_num))
      ((ComplexShape.up' _).next_eq' (by norm_num))).2 ?_)
    -- The object at `(-6, 3)` vanishes, since no critical point lies in the band `3`.
    have h₀ := isZero_filteredSpaceSpectralSequence_page_two_X_projectiveMomentFunction
      (ModuleCat.of ℤ ℤ) ha hcut (-6, 3) (by intro k; fin_cases k <;> simp)
    rw [ShortComplex.exact_iff_mono _ (h₀.eq_of_src _ _)]
    exact mono_filteredSpaceSpectralSequence_page_two_d_projectiveMomentFunction ha hcut
  · refine E.isZero_page_X_of_le (r := 2) (by norm_num)
      (isZero_filteredSpaceSpectralSequence_page_two_X_projectiveMomentFunction _ ha hcut pq ?_)
      3 (by norm_num)
    intro k
    fin_cases k
    · simpa using hpq₀
    · simpa using hpq₁
    · simpa using hpq₂

/-- **The second page of `ℝℙ²` in total degree `-1` is `ℤ/2`.** Under the hypotheses of
`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, with
integer coefficients, the object at `(-2, 1)` on the second page (numbered `3`) is `ℤ/2`, the
cokernel of the differential of index two on the first page. -/
theorem nonempty_filteredSpaceSpectralSequence_page_three_X_iso_zmod_projectiveMomentFunction
    (ha : Monotone a) (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) :
    Nonempty (((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
      (ModuleCat.of ℤ ℤ) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 3).X
        (-2, 1) ≅ ModuleCat.of ℤ (ZMod 2)) := by
  set E := filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
    (ModuleCat.of ℤ ℤ) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)
  obtain ⟨e⟩ :=
    nonempty_cokernel_filteredSpaceSpectralSequence_page_two_d_iso_projectiveMomentFunction ha hcut
  exact ⟨(E.iso 2 3 (-2, 1)).symm ≪≫
    (E.page 2).isoHomologyι (-2, 1) (0, 0) ((ComplexShape.up' _).next_eq' (by norm_num))
      (filteredSpaceSpectralSequence_page_two_d_eq_zero_projectiveMomentFunction _ ha hcut) ≪≫
    (E.page 2).opcyclesIsoSc' (-4, 2) (-2, 1) (0, 0) ((ComplexShape.up' _).prev_eq' (by norm_num))
      ((ComplexShape.up' _).next_eq' (by norm_num)) ≪≫
    ((E.page 2).sc' (-4, 2) (-2, 1) (0, 0)).opcyclesIsoCokernel ≪≫ e⟩

/-- **The second page of `ℝℙ²` in total degree `0` is one copy of the coefficients.** Under the
hypotheses of
`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, for any
coefficients, the object at `(0, 0)` on the second page (numbered `3`) is one copy of the
coefficients: both differentials at the band of the minimum vanish on the first page. -/
theorem nonempty_filteredSpaceSpectralSequence_page_three_X_zero_iso_projectiveMomentFunction
    (ha : Monotone a) (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) :
    Nonempty (((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ))) R
      ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 3).X (0, 0) ≅ R) := by
  set E := filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ))) R
    ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)
  obtain ⟨e⟩ := nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction
    R ha hcut 0
  exact ⟨(E.iso 2 3 (0, 0)).symm ≪≫
    ((E.page 2).isoHomologyπ (-2, 1) (0, 0) ((ComplexShape.up' _).prev_eq' (by norm_num))
      (filteredSpaceSpectralSequence_page_two_d_eq_zero_projectiveMomentFunction R ha hcut)).symm ≪≫
    (E.page 2).iCyclesIso (0, 0) (2, -1) ((ComplexShape.up' _).next_eq' (by norm_num))
      ((isZero_filteredSpaceSpectralSequence_page_two_X _ _ (2, -1) (by norm_num)).eq_of_tgt
        _ _) ≪≫
    (E.page 2).XIsoOfEq (by simp) ≪≫ e⟩

end TauCeti
