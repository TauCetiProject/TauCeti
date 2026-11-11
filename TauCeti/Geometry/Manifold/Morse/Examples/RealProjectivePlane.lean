/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Int
public import TauCeti.Algebra.Category.ModuleCat.OrzechProperty
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
  cokernel `ℤ/2`, so it is multiplication by `±2`
  (`TauCeti.mono_filteredSpaceSpectralSequence_page_two_d_projectiveMomentFunction`,
  `TauCeti.nonempty_cokernel_filteredSpaceSpectralSequence_page_two_d_iso_projectiveMomentFunction`
  and `TauCeti.filteredSpaceSpectralSequence_page_two_d_eq_two_smul_or_eq_neg_two_smul`). The
  differential from the band of the saddle to the band of the minimum vanishes
  (`TauCeti.filteredSpaceSpectralSequence_page_two_d_eq_zero_projectiveMomentFunction`).
* **Second page.** With integer coefficients, the objects at `(0, 0)`, `(-2, 1)` and `(-4, 2)` of
  the second page (numbered `3`) are `ℤ`, `ℤ/2` and `0`
  (`TauCeti.nonempty_filteredSpaceSpectralSequence_page_three_X_iso_int_projectiveMomentFunction`,
  `TauCeti.nonempty_filteredSpaceSpectralSequence_page_three_X_iso_zmod_projectiveMomentFunction`
  and `TauCeti.isZero_filteredSpaceSpectralSequence_page_three_X_projectiveMomentFunction`), the
  integral homology groups of `ℝℙ²`.

So the first page is the relative homology of the bands, free on the critical points, but it is not
yet the second page: its differential can be nonzero, and the critical counts `1, 1, 1` exceed the
integral Betti numbers `1, 0, 0`.

The differentials are the connecting maps of triples of sublevels
(`TauCeti.filteredSpaceSpectralSequence_first_page_d_eq`), and they are computed from the long exact
sequences of those triples. The inputs are the relative homology of a band with one critical point
(`TauCeti.IsMorse.nonempty_singularHomology_sublevelPair_iso_sigma`), the integral homology of
`ℝℙ²`, `H₁ = ℤ/2` and `H₂ = 0`, computed from its cellular chain complex
(`TauCeti.RealProjectiveSpace.singularHomologyIntLinearEquivOfOdd`), and the injectivity of the
zeroth homology of the bottom sublevel, a copy of `ℤ` split by the augmentation, into that of every
larger sublevel.

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

/-- The moment function on `ℝℙ²` takes its values between the extreme weights. -/
private theorem projectiveMomentFunction_mem_Icc (hw : Monotone w) (x : ℙ ℝ (Fin 3 → ℝ)) :
    projectiveMomentFunction ℝ w x ∈ Icc (w 0) (w 2) := by
  induction x using Projectivization.ind with
  | h v hv =>
    rw [projectiveMomentFunction_mk]
    have hpos : 0 < ∑ i, ‖v i‖ ^ 2 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
      exact Finset.sum_pos' (fun _ _ ↦ by positivity)
        ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hi) 2⟩
    constructor
    · rw [le_div_iff₀ hpos, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_right (hw (Fin.zero_le i)) (by positivity)
    · rw [div_le_iff₀ hpos, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_right (hw (Fin.le_last i)) (by positivity)

private theorem ncard_setOf_lt (hw : StrictMono w) (k : Fin 3) : {i | w i < w k}.ncard = k := by
  simp_rw [hw.lt_iff_lt]
  have : {i : Fin 3 | i < k} = ↑(Finset.Iio k) := by ext; simp
  rw [this, ncard_coe_finset, Fin.card_Iio]

/-- For increasing weights the coordinate point `[eₖ]` has Morse index `k`. -/
private theorem manifoldMorseIndex_mk_single (hw : StrictMono w) (k : Fin 3) :
    manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w)
      (mk ℝ (Pi.single k 1) (by simp)) = k := by
  rw [manifoldMorseIndex_projectiveMomentFunction, Module.finrank_self, one_mul,
    ncard_setOf_lt hw]

/-- For distinct weights, the coordinate point `[eₖ]` is the only critical point of the moment
function at the level `w k`. -/
private theorem criticalPoints_inter_preimage_singleton (hw : StrictMono w) (k : Fin 3) :
    criticalPoints 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) ∩
        projectiveMomentFunction ℝ w ⁻¹' {w k} = {mk ℝ (Pi.single k 1) (by simp)} := by
  ext x
  rw [criticalPoints_projectiveMomentFunction hw.injective]
  constructor
  · rintro ⟨⟨j, rfl⟩, hj⟩
    rw [mem_preimage, projectiveMomentFunction_mk_single, mem_singleton_iff] at hj
    rw [hw.injective hj]
    rfl
  · rintro rfl
    exact ⟨⟨k, rfl⟩, projectiveMomentFunction_mk_single w k⟩

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
    (isMorse_projectiveMomentFunction hw.injective) hs ht (isClosed_Icc.preimage
      (contMDiff_projectiveMomentFunction (r := 0) w).continuous).isCompact ?_ R n
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
  have : Unique {p : ↥(criticalPoints 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) ∩
      projectiveMomentFunction ℝ w ⁻¹' {w k}) //
      manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) p = k} :=
    { default := ⟨⟨_, (Set.ext_iff.1 (criticalPoints_inter_preimage_singleton hw k) _).2 rfl⟩,
        manifoldMorseIndex_mk_single hw k⟩
      uniq := fun p ↦ by
        have hp := (Set.ext_iff.1 (criticalPoints_inter_preimage_singleton hw k) p.1.1).1 p.1.2
        exact Subtype.ext (Subtype.ext hp) }
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
    have hp := (Set.ext_iff.1 (criticalPoints_inter_preimage_singleton hw k) p.1.1).1 p.1.2
    rw [← p.2, mem_singleton_iff.1 hp, manifoldMorseIndex_mk_single hw k]
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

private theorem continuous_projectiveMomentFunction :
    Continuous (projectiveMomentFunction ℝ w) :=
  (contMDiff_projectiveMomentFunction (r := 0) w).continuous

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
      (isClosed_Icc.preimage continuous_projectiveMomentFunction).isCompact fun x hx hfx ↦ ?_
    rw [criticalPoints_projectiveMomentFunction (strictMono_of_mem_Ioo hcut).injective] at hx
    obtain ⟨k, rfl⟩ := hx
    rw [projectiveMomentFunction_mk_single] at hfx
    exact hq k ((mem_Icc_iff ha hcut k q).1 hfx).symm

/-! ### Integral coefficients -/

/-- `H₁(ℝℙ²; ℤ) ≅ ℤ/2`, on the projectivization carrier. -/
private def singularHomologyOneIsoZMod :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (ℙ ℝ (Fin 3 → ℝ))) ≅ ModuleCat.of ℤ (ZMod 2) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).mapIso (TopCat.isoOfHomeo (X := TopCat.of (RealProjectiveSpace 2))
      (RealProjectiveSpace.homeomorphProjectivization 2))).symm ≪≫
    (RealProjectiveSpace.singularHomologyIntLinearEquivOfOdd (N := 2) odd_one
      (by norm_num)).toModuleIso

/-- `H₂(ℝℙ²; ℤ) = 0`, on the projectivization carrier. -/
private theorem isZero_singularHomology_two :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (ℙ ℝ (Fin 3 → ℝ)))) :=
  RealProjectiveSpace.isZero_singularHomology_projectivization_of_even (N := 2) ℤ
    (isRegular_iff_ne_zero.2 two_ne_zero).right even_two two_ne_zero

/-- Below the second critical value, the zeroth homology of the sublevel injects into that of
every larger sublevel, relative to an empty sublevel. -/
private theorem mono_singularHomologyMap_innerToTotal_zero (hw : StrictMono w) {s₀ s₁ t : ℝ}
    (h₀ : s₀ < w 0) (h₁ : w 0 < s₁) (h₁' : s₁ < w 1) (h₁t : s₁ ≤ t) :
    Mono (TopPair.singularHomologyMap (TopTriple.innerToTotal.app
      (TopTriple.ofInclusions (X := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
        (sublevel_mono (projectiveMomentFunction ℝ w) (h₀.trans h₁).le)
        (sublevel_mono (projectiveMomentFunction ℝ w) h₁t))) (ModuleCat.of ℤ ℤ) 0) := by
  set T := TopTriple.ofInclusions (X := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
    (sublevel_mono (projectiveMomentFunction ℝ w) (h₀.trans h₁).le)
    (sublevel_mono (projectiveMomentFunction ℝ w) h₁t)
  -- The common subspace `{f ≤ s₀}` is empty, so both relative groups are absolute ones.
  have hempty : ∀ x, ¬ projectiveMomentFunction ℝ w x ≤ s₀ := fun x hx ↦
    ((projectiveMomentFunction_mem_Icc hw.monotone x).1.trans hx).not_gt h₀
  have : IsEmpty (TopTriple.innerPair.obj T).snd := ⟨fun x ↦ hempty x.1 x.2⟩
  have : IsEmpty (TopTriple.totalPair.obj T).snd := ⟨fun x ↦ hempty x.1 x.2⟩
  have : IsIso ((TopTriple.innerPair.obj T).singularHomologyπ (ModuleCat.of ℤ ℤ) 0) :=
    inferInstance
  have hπ : IsIso ((TopTriple.totalPair.obj T).singularHomologyπ (ModuleCat.of ℤ ℤ) 0) :=
    inferInstance
  -- On absolute homology, the augmentation of the smaller sublevel factors through the map,
  -- and that augmentation is split by the class of the minimum `[e₀]`, with source `ℤ`.
  obtain ⟨e⟩ := nonempty_singularHomology_sublevelPair_iso (ModuleCat.of ℤ ℤ) hw 0
    (h₀.trans_le le_rfl) h₁ fun i hi ↦ by
      by_contra hne
      exact (hi.2.trans_lt h₁').not_ge (hw.monotone (Fin.pos_iff_ne_zero.2 hne))
  -- The carrier of `(TopTriple.innerPair.obj T).fst` is the subtype `{x | f x ≤ s₁}`; `show`
  -- unfolds the membership to the inequality.
  let x₀ : (TopTriple.innerPair.obj T).fst := ⟨mk ℝ (Pi.single 0 1) (by simp),
    show projectiveMomentFunction ℝ w _ ≤ s₁ by
      rw [projectiveMomentFunction_mk_single]; exact h₁.le⟩
  have hε₁ : Mono (SSet.homology₀ε (TopCat.toSSet.obj (TopTriple.innerPair.obj T).fst)
      (ModuleCat.of ℤ ℤ)) :=
    @ModuleCat.mono_of_epi_of_iso _ _ _ _ _ _ (asIso ((TopTriple.innerPair.obj T).singularHomologyπ
      (ModuleCat.of ℤ ℤ) 0) ≪≫ e) _
      (@IsSplitEpi.epi _ _ _ _ _
        (IsSplitEpi.mk' ⟨_, singularHomology₀Section_singularHomology₀ε _ x₀⟩))
  rw [← SSet.homologyMap_homology₀ε (ModuleCat.of ℤ ℤ)
    (TopCat.toSSet.map (TopPair.Hom.fst (TopTriple.innerToTotal.app T)))] at hε₁
  have hA := @mono_of_mono _ _ _ _ _ _ _ hε₁
  rw [(IsIso.eq_inv_comp _).2 (TopPair.singularHomologyπ_naturality
    (TopTriple.innerToTotal.app T) (ModuleCat.of ℤ ℤ) 0).symm]
  exact @mono_comp _ _ _ _ _ _ inferInstance _
    (@mono_comp _ _ _ _ _ _ hA _ (@IsIso.mono_of_iso _ _ _ _ _ hπ))

/-- A sublevel pair covering `ℝℙ²` has the homology of `ℝℙ²`. -/
private def singularHomologySublevelPairIsoOfLT (hw : Monotone w) {s₀ s₃ : ℝ} (h₀ : s₀ < w 0)
    (h₃ : w 2 < s₃) (h : s₀ ≤ s₃) (n : ℕ) :
    (sublevelPair (projectiveMomentFunction ℝ w) h).singularHomology (ModuleCat.of ℤ ℤ) n ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (ℙ ℝ (Fin 3 → ℝ))) :=
  (singularHomologyIsoSublevelPair _
    (fun x ↦ h₀.trans_le (projectiveMomentFunction_mem_Icc hw x).1)
    (fun x ↦ ((projectiveMomentFunction_mem_Icc hw x).2.trans h₃.le)) _ n).symm

/-- The sublevel triple `({f ≤ u}, {f ≤ t}, {f ≤ s})` of the moment function on `ℝℙ²`. -/
private abbrev sublevelTriple (w : Fin 3 → ℝ) {s t u : ℝ} (hst : s ≤ t) (htu : t ≤ u) :
    TopTriple :=
  TopTriple.ofInclusions (X := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
    (sublevel_mono (projectiveMomentFunction ℝ w) hst)
    (sublevel_mono (projectiveMomentFunction ℝ w) htu)

section Sublevels

variable (hw : StrictMono w) {s₀ s₁ s₂ s₃ : ℝ} (h₀ : s₀ < w 0) (h₁ : w 0 < s₁) (h₁' : s₁ < w 1)
  (h₂ : w 1 < s₂) (h₂' : s₂ < w 2) (h₃ : w 2 < s₃)
include hw

include h₁' in
private theorem eq_zero_of_mem_Icc : ∀ i, w i ∈ Icc s₀ s₁ → i = 0 := fun i hi ↦ by
  by_contra hne
  exact (hi.2.trans_lt h₁').not_ge (hw.monotone (Fin.pos_iff_ne_zero.2 hne))

omit hw in
include h₁ h₂' in
private theorem eq_one_of_mem_Icc : ∀ i, w i ∈ Icc s₁ s₂ → i = 1 := fun i hi ↦ by
  fin_cases i
  · exact absurd (hi.1.trans_lt h₁) (lt_irrefl _)
  · rfl
  · exact absurd (h₂'.trans_le hi.2) (lt_irrefl _)

include h₂ in
private theorem eq_two_of_mem_Icc : ∀ i, w i ∈ Icc s₂ s₃ → i = 2 := fun i hi ↦ by
  fin_cases i
  · exact absurd (h₂.trans_le hi.1) (hw.monotone (Fin.zero_le 1)).not_gt
  · exact absurd (h₂.trans_le hi.1) (lt_irrefl _)
  · rfl

include h₀ h₁ h₁' h₃ in
/-- Below the second critical value, `H₂(ℝℙ², {f ≤ s₁}; ℤ) = 0`. -/
private theorem isZero_singularHomology_two_sublevelPair (h : s₁ ≤ s₃) :
    IsZero ((sublevelPair (projectiveMomentFunction ℝ w) h).singularHomology
      (ModuleCat.of ℤ ℤ) 2) :=
  ((sublevelTriple w (h₀.trans h₁).le h).singularHomology_exact_outer (ModuleCat.of ℤ ℤ)
    2 1).isZero_of_both_isZero
    (isZero_singularHomology_two.of_iso
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
  -- `H₀(f ≤ s₁) ⟶ H₀(ℝℙ²)` is injective, so the map is also surjective.
  have hδ : T.singularHomologyδ (ModuleCat.of ℤ ℤ) 1 0 = 0 := by
    have := mono_singularHomologyMap_innerToTotal_zero hw h₀ h₁ h₁' h
    rw [← cancel_mono (TopPair.singularHomologyMap (TopTriple.innerToTotal.app T)
      (ModuleCat.of ℤ ℤ) 0), TopTriple.singularHomologyδ_comp _ _ 1 0, zero_comp]
  have : Epi (TopPair.singularHomologyMap (TopTriple.totalToOuter.app T)
      (ModuleCat.of ℤ ℤ) 1) :=
    (T.singularHomology_exact_outer (ModuleCat.of ℤ ℤ) 1 0).epi_f hδ
  have : IsIso (TopPair.singularHomologyMap (TopTriple.totalToOuter.app T)
      (ModuleCat.of ℤ ℤ) 1) := isIso_of_mono_of_epi _
  exact ⟨(asIso (TopPair.singularHomologyMap (TopTriple.totalToOuter.app T)
    (ModuleCat.of ℤ ℤ) 1)).symm ≪≫
      singularHomologySublevelPairIsoOfLT hw.monotone h₀ h₃ ((h₀.trans h₁).le.trans h) 1 ≪≫
        singularHomologyOneIsoZMod⟩

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

include h₀ h₁ h₁' h₂ in
/-- Across the critical level of index one, the connecting map
`H₁({f ≤ s₂}, {f ≤ s₁}) ⟶ H₀({f ≤ s₁}, {f ≤ s₀})` vanishes. -/
private theorem singularHomologyδ_one_eq_zero :
    (sublevelTriple w (h₀.trans h₁).le (h₁'.trans h₂).le).singularHomologyδ
      (ModuleCat.of ℤ ℤ) 1 0 = 0 := by
  have := mono_singularHomologyMap_innerToTotal_zero hw h₀ h₁ h₁' (h₁'.trans h₂).le
  rw [← cancel_mono (TopPair.singularHomologyMap (TopTriple.innerToTotal.app
    (sublevelTriple w (h₀.trans h₁).le (h₁'.trans h₂).le)) (ModuleCat.of ℤ ℤ) 0),
    TopTriple.singularHomologyδ_comp _ _ 1 0, zero_comp]

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
  have hd := filteredSpaceSpectralSequence_first_page_d_eq (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
    (ModuleCat.of ℤ ℤ) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha) 2 (-4) 1
    (by norm_num)
  have hδ := mono_singularHomologyδ_two (strictMono_of_mem_Ioo hcut) h₀ (s₁ := a (2 - 1))
    (s₂ := a 2) (s₃ := a (2 + 1)) (by norm_num; exact h₁) (by norm_num; exact h₁') h₂ h₂'
    (by norm_num; exact h₃)
  -- `hd` states the differential with target `(-4 + 2, 2 - 1)`. That index also appears in the
  -- types of the isomorphisms on its right-hand side, so `hd` cannot be normalized; instead the
  -- target `(-2, 1)` of the goal is rewritten into the same unnormalized form.
  rw [show ((-2, 1) : ℤ × ℤ) = (-4 + 2, 2 - 1) by norm_num, hd]
  exact @mono_comp _ _ _ _ _ _ inferInstance _
    (@mono_comp _ _ _ _ _ _ hδ _ (@IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_inv _)))

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
  have hd := filteredSpaceSpectralSequence_first_page_d_eq (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
    (ModuleCat.of ℤ ℤ) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha) 2 (-4) 1
    (by norm_num)
  obtain ⟨e⟩ := nonempty_cokernel_singularHomologyδ_two_iso (strictMono_of_mem_Ioo hcut) h₀
    (s₁ := a (2 - 1)) (s₂ := a 2) (s₃ := a (2 + 1)) (by norm_num; exact h₁)
    (by norm_num; exact h₁') h₂ h₂' (by norm_num; exact h₃)
  -- `hd` states the differential with target `(-4 + 2, 2 - 1)`. That index also appears in the
  -- types of the isomorphisms on its right-hand side, so `hd` cannot be normalized; instead the
  -- target `(-2, 1)` of the goal is rewritten into the same unnormalized form.
  rw [show ((-2, 1) : ℤ × ℤ) = (-4 + 2, 2 - 1) by norm_num, hd]
  exact ⟨cokernelEpiComp _ _ ≪≫
    @cokernelCompIsIso _ _ _ _ _ _ _ _ _ (Iso.isIso_inv _) ≪≫ e⟩

/-- **The differential of index two on the first page of `ℝℙ²` is multiplication by `±2`.**
Under the hypotheses of
`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, with
integer coefficients, read through any identifications of the objects at `(-4, 2)` and `(-2, 1)` of
the first page with `ℤ`, the differential between them is multiplication by `2` or by `-2`; the
sign depends on the identifications. -/
theorem filteredSpaceSpectralSequence_page_two_d_eq_two_smul_or_eq_neg_two_smul
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
of `TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, with
integer coefficients, the differential from `(-2, 1)` to `(0, 0)` on the first page, the
connecting map from the band of the saddle to the band of the minimum, is zero. -/
theorem filteredSpaceSpectralSequence_page_two_d_eq_zero_projectiveMomentFunction
    (ha : Monotone a) (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) :
    ((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
      (ModuleCat.of ℤ ℤ) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).d
        (-2, 1) (0, 0) = 0 := by
  obtain ⟨h₀, h₁, h₁', h₂, -, -⟩ := lt_of_mem_Ioo hcut
  have hd := filteredSpaceSpectralSequence_first_page_d_eq (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
    (ModuleCat.of ℤ ℤ) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha) 1 (-2) 0
    (by norm_num)
  have hδ := singularHomologyδ_one_eq_zero (strictMono_of_mem_Ioo hcut) (s₀ := a (1 - 1))
    (s₁ := a 1) (s₂ := a (1 + 1)) (by norm_num; exact h₀) h₁ h₁' (by norm_num; exact h₂)
  -- As above, `hd` has target `(-2 + 2, 1 - 1)`, which also indexes its right-hand side, so the
  -- target `(0, 0)` of the goal is rewritten into that form.
  rw [show ((0, 0) : ℤ × ℤ) = (-2 + 2, 1 - 1) by norm_num, hd]
  -- The middle factor is the connecting map of `sublevelTriple`, up to unfolding the filtration
  -- `(fun s ↦ {f ≤ s}) ∘ a` and the degree `0 + 1`; `erw` matches it up to that unfolding.
  erw [hδ, zero_comp, comp_zero]

/-- **The second page of `ℝℙ²` vanishes in total degree `-2`.** Under the hypotheses of
`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, with
integer coefficients, the object at `(-4, 2)` on the second page (numbered `3`) is zero: the
differential out of it on the first page is injective. -/
theorem isZero_filteredSpaceSpectralSequence_page_three_X_projectiveMomentFunction
    (ha : Monotone a) (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) :
    IsZero (((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
      (ModuleCat.of ℤ ℤ) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 3).X
        (-4, 2)) := by
  set E := filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
    (ModuleCat.of ℤ ℤ) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)
  refine IsZero.of_iso ?_ (E.iso 2 3 (-4, 2)).symm
  refine HomologicalComplex.ExactAt.isZero_homology (((E.page 2).exactAt_iff' (-6, 3) (-4, 2)
    (-2, 1) ((ComplexShape.up' _).prev_eq' (by norm_num))
    ((ComplexShape.up' _).next_eq' (by norm_num))).2 ?_)
  -- The object at `(-6, 3)` vanishes, since no critical point lies in the band `3`.
  have h₀ := isZero_filteredSpaceSpectralSequence_page_two_X_projectiveMomentFunction
    (ModuleCat.of ℤ ℤ) ha hcut (-6, 3) (by intro k; fin_cases k <;> simp)
  rw [ShortComplex.exact_iff_mono _ (h₀.eq_of_src _ _)]
  exact mono_filteredSpaceSpectralSequence_page_two_d_projectiveMomentFunction ha hcut

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
      (filteredSpaceSpectralSequence_page_two_d_eq_zero_projectiveMomentFunction ha hcut) ≪≫
    (E.page 2).opcyclesIsoSc' (-4, 2) (-2, 1) (0, 0) ((ComplexShape.up' _).prev_eq' (by norm_num))
      ((ComplexShape.up' _).next_eq' (by norm_num)) ≪≫
    ((E.page 2).sc' (-4, 2) (-2, 1) (0, 0)).opcyclesIsoCokernel ≪≫ e⟩

/-- **The second page of `ℝℙ²` in total degree `0` is `ℤ`.** Under the hypotheses of
`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, with
integer coefficients, the object at `(0, 0)` on the second page (numbered `3`) is `ℤ`: both
differentials at the band of the minimum vanish on the first page. -/
theorem nonempty_filteredSpaceSpectralSequence_page_three_X_iso_int_projectiveMomentFunction
    (ha : Monotone a) (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) :
    Nonempty (((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
      (ModuleCat.of ℤ ℤ) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 3).X
        (0, 0) ≅ ModuleCat.of ℤ ℤ) := by
  set E := filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
    (ModuleCat.of ℤ ℤ) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)
  obtain ⟨e⟩ := nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction
    (ModuleCat.of ℤ ℤ) ha hcut 0
  exact ⟨(E.iso 2 3 (0, 0)).symm ≪≫
    ((E.page 2).isoHomologyπ (-2, 1) (0, 0) ((ComplexShape.up' _).prev_eq' (by norm_num))
      (filteredSpaceSpectralSequence_page_two_d_eq_zero_projectiveMomentFunction ha hcut)).symm ≪≫
    (E.page 2).iCyclesIso (0, 0) (2, -1) ((ComplexShape.up' _).next_eq' (by norm_num))
      ((isZero_filteredSpaceSpectralSequence_page_two_X _ _ (2, -1) (by norm_num)).eq_of_tgt
        _ _) ≪≫
    (E.page 2).XIsoOfEq (by simp) ≪≫ e⟩

end TauCeti
