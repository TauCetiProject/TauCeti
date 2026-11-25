/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.Geometry.Manifold.Morse.Projectivization
public import TauCeti.Geometry.Manifold.Morse.SpectralSequence
import TauCeti.Order.Fin.Basic
import TauCeti.Order.Monotone.Basic

/-!
# The critical-band spectral sequence of real projective space

Let `f = TauCeti.projectiveMomentFunction ℝ w` be the moment function on
`ℝℙᴺ = ℙ ℝ (Fin (N + 1) → ℝ)`, `f[x] = (∑ i, w i * x i ^ 2) / ∑ i, x i ^ 2`, and let `a : ℤ → ℝ` be
monotone with `a k < w k < a (k + 1)` for `k = 0, …, N`. Then the weights increase, `f` is a Morse
function whose critical points are the coordinate points `[eₖ]`, of index `k` and value `w k`, and
for `0 ≤ k ≤ N` the band `f⁻¹[a k, a (k + 1)]` contains `[eₖ]` and no other critical point; the
other bands contain no critical point. This file studies the spectral sequence of the filtration
`q ↦ {f ≤ a q}` (`TauCeti.filteredSpaceSpectralSequence`), with singular chains of degree `n` in
degree `-n`, so that the band of `[eₖ]` sits at `(-2k, k)`.

* **First page.** For any coefficients, the object at `(-2k, k)`, `k ≤ N`, is one copy of the
  coefficients
  (`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`), and
  every other object is zero
  (`TauCeti.isZero_filteredSpaceSpectralSequence_page_two_X_projectiveMomentFunction`).
* **The differential into the minimum.** For any coefficients, the first differential from
  `(-2, 1)`, the position of `[e₁]` when `N ≥ 1`, to `(0, 0)`, the position of the minimum `[e₀]`,
  vanishes
  (`TauCeti.filteredSpaceSpectralSequence_page_two_d_neg_two_one_eq_zero_projectiveMomentFunction`).
  So the object at `(0, 0)` of the second page (numbered `3`) is still one copy of the
  coefficients
  (`TauCeti.nonempty_filteredSpaceSpectralSequence_page_three_X_zero_iso_projectiveMomentFunction`).

The vanishing comes from the sublevel `{f ≤ a 1}` around the minimum, which is contractible
(`TauCeti.contractibleSpace_sublevel_projectiveMomentFunction_of_mem_Ioo`): the differential is
the connecting map of the triple `({f ≤ a 2}, {f ≤ a 1}, {f ≤ a 0})`, and it factors through the
connecting map of the pair `({f ≤ a 2}, {f ≤ a 1})`, which vanishes
(`TopPair.singularHomologyδ_eq_zero_of_contractibleSpace`).

The real projective plane, where with integer coefficients the first differential from `(-4, 2)`
to `(-2, 1)` is multiplication by `±2` after identifying its source and target with `ℤ`, is
studied in the module
`TauCeti.Geometry.Manifold.Morse.Examples.RealProjectivePlane`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3 and §4.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  §2.2.
-/

public section

noncomputable section

open CategoryTheory Limits Set Projectivization
open scoped Manifold LinearAlgebra.Projectivization

namespace TauCeti

variable {N : ℕ} {w : Fin (N + 1) → ℝ}

variable {A : Type*} [Category A] [Abelian A] [HasCoproducts.{0} A] (R : A)

/-- The relative homology across a band of the moment function on `ℝℙᴺ` whose only critical value
is `w k`, as a coproduct over the critical points of index `n` on that level. -/
private theorem nonempty_singularHomology_sublevelPair_iso_sigma (hw : StrictMono w) {s t : ℝ}
    (k : Fin (N + 1)) (hs : s < w k) (ht : w k < t) (hcrit : ∀ i, w i ∈ Icc s t → i = k)
    (n : ℕ) :
    Nonempty ((sublevelPair (projectiveMomentFunction ℝ w) (hs.trans ht).le).singularHomology
        R n ≅
      ∐ fun _ : {p : ↥(criticalPoints 𝓘(ℝ, Fin N → ℝ) (projectiveMomentFunction ℝ w) ∩
          projectiveMomentFunction ℝ w ⁻¹' {w k}) //
          manifoldMorseIndex 𝓘(ℝ, Fin N → ℝ) (projectiveMomentFunction ℝ w) p = n} ↦ R) := by
  refine IsMorse.nonempty_singularHomology_sublevelPair_iso_sigma
    (isMorse_projectiveMomentFunction hw.injective) hs ht
      (isClosed_Icc.preimage (continuous_projectiveMomentFunction w)).isCompact ?_ R n
  intro x hx hxst
  rw [criticalPoints_projectiveMomentFunction hw.injective] at hx
  obtain ⟨j, rfl⟩ := hx
  rw [projectiveMomentFunction_mk_single] at hxst ⊢
  rw [hcrit j hxst]

/-- Across a band of the moment function on `ℝℙᴺ` whose only critical value is `w k`, the relative
homology in degree `k` is one copy of the coefficients. -/
private theorem nonempty_singularHomology_sublevelPair_iso (hw : StrictMono w) {s t : ℝ}
    (k : Fin (N + 1)) (hs : s < w k) (ht : w k < t) (hcrit : ∀ i, w i ∈ Icc s t → i = k) :
    Nonempty ((sublevelPair (projectiveMomentFunction ℝ w) (hs.trans ht).le).singularHomology
      R k ≅ R) := by
  obtain ⟨e⟩ := nonempty_singularHomology_sublevelPair_iso_sigma R hw k hs ht hcrit k
  have hk := criticalPoints_projectiveMomentFunction_inter_preimage_singleton (𝕜 := ℝ)
    hw.injective k
  have : Unique {p : ↥(criticalPoints 𝓘(ℝ, Fin N → ℝ) (projectiveMomentFunction ℝ w) ∩
      projectiveMomentFunction ℝ w ⁻¹' {w k}) //
      manifoldMorseIndex 𝓘(ℝ, Fin N → ℝ) (projectiveMomentFunction ℝ w) p = k} :=
    { default := ⟨⟨_, (Set.ext_iff.1 hk _).2 rfl⟩,
        by rw [manifoldMorseIndex_projectiveMomentFunction_of_strictMono hw k,
          Module.finrank_self, one_mul]⟩
      uniq := fun p ↦ Subtype.ext (Subtype.ext ((Set.ext_iff.1 hk p.val.val).1 p.val.property)) }
  exact ⟨e ≪≫ coproductUniqueIso _⟩

/-- Across a band of the moment function on `ℝℙᴺ` whose only critical value is `w k`, the relative
homology vanishes in every degree other than `k`. -/
private theorem isZero_singularHomology_sublevelPair (hw : StrictMono w) {s t : ℝ}
    (k : Fin (N + 1)) (hs : s < w k) (ht : w k < t) (hcrit : ∀ i, w i ∈ Icc s t → i = k) {n : ℕ}
    (hn : n ≠ k) :
    IsZero ((sublevelPair (projectiveMomentFunction ℝ w) (hs.trans ht).le).singularHomology
      R n) := by
  obtain ⟨e⟩ := nonempty_singularHomology_sublevelPair_iso_sigma R hw k hs ht hcrit n
  have : IsEmpty {p : ↥(criticalPoints 𝓘(ℝ, Fin N → ℝ) (projectiveMomentFunction ℝ w) ∩
      projectiveMomentFunction ℝ w ⁻¹' {w k}) //
      manifoldMorseIndex 𝓘(ℝ, Fin N → ℝ) (projectiveMomentFunction ℝ w) p = n} := by
    refine ⟨fun p ↦ hn ?_⟩
    have hp := (Set.ext_iff.1 (criticalPoints_projectiveMomentFunction_inter_preimage_singleton
      hw.injective k) p.val.val).1 p.val.property
    rw [← p.property, mem_singleton_iff.1 hp,
      manifoldMorseIndex_projectiveMomentFunction_of_strictMono hw k, Module.finrank_self, one_mul]
  exact ((IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ isEmptyElim)).of_iso e

variable {a : ℤ → ℝ}

private theorem eq_of_mem_Icc (ha : Monotone a)
    (hcut : ∀ k : Fin (N + 1), w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) (k : Fin (N + 1)) :
    ∀ i, w i ∈ Icc (a k) (a ((k : ℕ) + 1)) → i = k := fun i hi ↦
  Fin.ext (by exact_mod_cast ((ha.mem_Icc_iff_eq_of_mem_Ioo (hcut i)).1 hi).symm)

/-- **The first page of the critical-band spectral sequence of `ℝℙᴺ`.** Let `f` be the moment
function on `ℝℙᴺ` with weights `w`, and let `a` be a monotone sequence with
`a k < w k < a (k + 1)` for `k = 0, …, N`, so that the band `f⁻¹[a k, a (k + 1)]` contains the
critical point `[eₖ]` of index `k` and no other. On the first page of the spectral sequence of the
filtration `q ↦ {f ≤ a q}`, the object at `(-2k, k)`, of total degree `-k`, is one copy of the
coefficients. -/
theorem nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction
    (ha : Monotone a) (hcut : ∀ k : Fin (N + 1), w k ∈ Ioo (a k) (a ((k : ℕ) + 1)))
    (k : Fin (N + 1)) :
    Nonempty (((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) R
      ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).X
        (-(2 * (k : ℕ) : ℤ), ((k : ℕ) : ℤ)) ≅ R) := by
  obtain ⟨e⟩ := nonempty_singularHomology_sublevelPair_iso R
    (Fin.strictMono_of_forall_mem_Ioo hcut) k (hcut k).1 (hcut k).2 (eq_of_mem_Icc ha hcut k)
  exact ⟨filteredSpaceSpectralSequenceFirstPageXIso (Y := TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) R
    ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha) _ _ _ rfl rfl _ rfl k
      (by push_cast; ring) ≪≫ e⟩

/-- **The first page of the critical-band spectral sequence of `ℝℙᴺ` away from the critical
points.** Under the hypotheses of
`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, every
object of the first page other than those at `(-2k, k)`, `k ≤ N`, is zero. -/
theorem isZero_filteredSpaceSpectralSequence_page_two_X_projectiveMomentFunction
    (ha : Monotone a) (hcut : ∀ k : Fin (N + 1), w k ∈ Ioo (a k) (a ((k : ℕ) + 1)))
    (pq : ℤ × ℤ) (hpq : ∀ k : Fin (N + 1), pq ≠ (-(2 * (k : ℕ) : ℤ), ((k : ℕ) : ℤ))) :
    IsZero (((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) R
      ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).X pq) := by
  obtain ⟨p, q⟩ := pq
  rcases lt_or_ge 0 (p + q) with hpos | hle
  · exact isZero_filteredSpaceSpectralSequence_page_two_X _ _ _ hpos
  obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hle
  by_cases hq : ∃ k : Fin (N + 1), ((k : ℕ) : ℤ) = q
  · obtain ⟨k, rfl⟩ := hq
    have hnk : n ≠ k := by
      rintro rfl
      exact hpq k (Prod.ext (by simp only at hn ⊢; omega) rfl)
    exact (isZero_singularHomology_sublevelPair R (Fin.strictMono_of_forall_mem_Ioo hcut) k
      (hcut k).1 (hcut k).2 (eq_of_mem_Icc ha hcut k) hnk).of_iso
        (filteredSpaceSpectralSequenceFirstPageXIso (Y := TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) R
          ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha) _ _ _ rfl rfl _ rfl n hn)
  · push Not at hq
    refine isZero_filteredSpaceSpectralSequence_page_two_X_of_forall_notMem R
      (contMDiff_projectiveMomentFunction w) ha (p, q)
      (isClosed_Icc.preimage (continuous_projectiveMomentFunction w)).isCompact fun x hx hfx ↦ ?_
    rw [criticalPoints_projectiveMomentFunction
      (Fin.strictMono_of_forall_mem_Ioo hcut).injective] at hx
    obtain ⟨k, rfl⟩ := hx
    rw [projectiveMomentFunction_mk_single] at hfx
    exact hq k ((ha.mem_Icc_iff_eq_of_mem_Ioo (hcut k)).1 hfx).symm

/-- **The sublevel around the minimum is contractible.** Under the hypotheses of
`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, the
sublevel `{f ≤ a 1}` of the moment function on `ℝℙᴺ`, which contains the minimum `[e₀]` and no
other critical point, is contractible. -/
theorem contractibleSpace_sublevel_projectiveMomentFunction_of_mem_Ioo (ha : Monotone a)
    (hcut : ∀ k : Fin (N + 1), w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) :
    ContractibleSpace {x : ℙ ℝ (Fin (N + 1) → ℝ) | projectiveMomentFunction ℝ w x ≤ a 1} :=
  contractibleSpace_sublevel_projectiveMomentFunction (k := 0) (by simpa using (hcut 0).2.le)
    fun i hi ↦ (ha (by have := Fin.val_ne_zero_iff.2 hi; omega)).trans_lt (hcut i).1

/-- The sublevel triple `({f ≤ a 2}, {f ≤ a 1}, {f ≤ a 0})` of the moment function on `ℝℙᴺ`. -/
private abbrev lowerTriple (w : Fin (N + 1) → ℝ) (ha : Monotone a) : TopTriple :=
  TopTriple.ofInclusions (X := TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ)))
    ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha (by norm_num : (0 : ℤ) ≤ 1))
    ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha (by norm_num : (1 : ℤ) ≤ 2))

/-- The object at `(0, 0)` on the first page is `H₀({f ≤ a 1}, {f ≤ a 0})`. -/
private def firstPageXZeroIso (ha : Monotone a) :
    ((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) R
      ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).X (0, 0) ≅
      (TopTriple.innerPair.obj (lowerTriple w ha)).singularHomology R 0 :=
  filteredSpaceSpectralSequenceFirstPageXIso R _ (0, 0) 0 1 rfl rfl 0 rfl 0 rfl

/-- The object at `(-2, 1)` on the first page is `H₁({f ≤ a 2}, {f ≤ a 1})`. -/
private def firstPageXOneIso (ha : Monotone a) :
    ((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) R
      ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).X (-2, 1) ≅
      (TopTriple.outerPair.obj (lowerTriple w ha)).singularHomology R 1 :=
  filteredSpaceSpectralSequenceFirstPageXIso R _ (-2, 1) 1 2 rfl rfl (-1) rfl 1 rfl

/-- **The first differential into the minimum vanishes.** Under the hypotheses of
`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, for any
coefficients, the differential from `(-2, 1)` to `(0, 0)` on the first page is zero. -/
theorem filteredSpaceSpectralSequence_page_two_d_neg_two_one_eq_zero_projectiveMomentFunction
    (ha : Monotone a) (hcut : ∀ k : Fin (N + 1), w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) :
    ((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) R
      ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).d (-2, 1) (0, 0) = 0 := by
  -- The differential is the connecting map of the triple `({f ≤ a 2}, {f ≤ a 1}, {f ≤ a 0})`:
  -- `filteredSpaceSpectralSequence_first_page_d_eq` at `(p, q) = (-2, 1)` and `n = 0`, whose
  -- positions and degrees are the numerals of `h` after evaluating their arithmetic.
  have h : ((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) R
      ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).d (-2, 1) (0, 0) =
      (firstPageXOneIso R ha).hom ≫ (lowerTriple w ha).singularHomologyδ R 1 0 ≫
        (firstPageXZeroIso R ha).inv :=
    filteredSpaceSpectralSequence_first_page_d_eq R _ 1 (-2) 0 (by norm_num)
  -- That connecting map factors through the connecting map of the pair
  -- `({f ≤ a 2}, {f ≤ a 1})`, which vanishes since `{f ≤ a 1}` is contractible.
  have : ContractibleSpace (TopTriple.outerPair.obj (lowerTriple w ha)).snd :=
    contractibleSpace_sublevel_projectiveMomentFunction_of_mem_Ioo ha hcut
  have hδ : (lowerTriple w ha).singularHomologyδ R 1 0 = 0 := by
    rw [(lowerTriple w ha).singularHomologyδ_eq_comp_singularHomologyπ R 1 0 rfl,
      (TopTriple.outerPair.obj (lowerTriple w ha)).singularHomologyδ_eq_zero_of_contractibleSpace
        R 0]
    exact zero_comp
  rw [h, hδ, zero_comp, comp_zero]

/-- **The second page of `ℝℙᴺ` at the minimum is one copy of the coefficients.** Under the
hypotheses of
`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, for any
coefficients, the object at `(0, 0)` on the second page (numbered `3`) is one copy of the
coefficients. -/
theorem nonempty_filteredSpaceSpectralSequence_page_three_X_zero_iso_projectiveMomentFunction
    (ha : Monotone a) (hcut : ∀ k : Fin (N + 1), w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) :
    Nonempty (((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) R
      ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 3).X (0, 0) ≅ R) := by
  set E := filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin (N + 1) → ℝ))) R
    ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)
  obtain ⟨e⟩ := nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction
    R ha hcut 0
  exact ⟨(E.iso 2 3 (0, 0)).symm ≪≫
    ((E.page 2).isoHomologyπ (-2, 1) (0, 0) ((ComplexShape.up' _).prev_eq' (by norm_num))
      (filteredSpaceSpectralSequence_page_two_d_neg_two_one_eq_zero_projectiveMomentFunction R ha
        hcut)).symm ≪≫
    (E.page 2).iCyclesIso (0, 0) (2, -1) ((ComplexShape.up' _).next_eq' (by norm_num))
      ((isZero_filteredSpaceSpectralSequence_page_two_X _ _ (2, -1) (by norm_num)).eq_of_tgt
        _ _) ≪≫
    (E.page 2).XIsoOfEq (by simp) ≪≫ e⟩

end TauCeti
