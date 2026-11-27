/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Int
public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology
public import TauCeti.Geometry.Manifold.Morse.Examples.RealProjectiveSpace
import TauCeti.Algebra.Homology.SpectralSequence.Degeneration
import TauCeti.AlgebraicTopology.Singular.Sublevel

/-!
# The critical-band spectral sequence of the real projective plane

Let `f = TauCeti.projectiveMomentFunction ℝ w` be the moment function on
`ℝℙ² = ℙ ℝ (Fin 3 → ℝ)`, `f[x] = (∑ i, w i * x i ^ 2) / ∑ i, x i ^ 2`, and let `a : ℤ → ℝ` be
monotone with `a k < w k < a (k + 1)` for `k = 0, 1, 2`. Then the weights increase, `f` is a Morse
function whose critical points are the coordinate points `[eₖ]`, of index `k` and value `w k`, and
the band `f⁻¹[a k, a (k + 1)]` contains `[eₖ]` and no other critical point. This file computes the
first two pages of the spectral sequence of the filtration `q ↦ {f ≤ a q}`
(`TauCeti.filteredSpaceSpectralSequence`), with singular chains of degree `n` in degree `-n`, so
that the band of `[eₖ]` sits at `(-2k, k)`, with coefficients in a ring `R`.

* **First page.** The object at `(-2k, k)` is one copy of the coefficients, and every other object
  is zero; these are the cases `N = 2` of
  `TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction` and
  `TauCeti.isZero_filteredSpaceSpectralSequence_page_two_X_projectiveMomentFunction` on `ℝℙᴺ`.
* **First differentials.** The differential from the band of the maximum to the band of the
  saddle, `R ⟶ R` from `(-4, 2)` to `(-2, 1)`, has cokernel `R / 2R`
  (`nonempty_cokernel_filteredSpaceSpectralSequence_page_two_d_neg_four_two_iso`) and is
  injective when right multiplication by `2` is injective on `R`
  (`mono_filteredSpaceSpectralSequence_page_two_d_neg_four_two`). With integer coefficients its
  cokernel is `ℤ/2`
  (`nonempty_cokernel_filteredSpaceSpectralSequence_page_two_d_neg_four_two_iso_zmod`), and
  `filteredSpaceSpectralSequence_page_two_d_neg_four_two_eq_two_smul_or_eq_neg_two_smul`
  deduces that it is multiplication by `±2`. The differential from the band of the saddle to the
  band of the minimum vanishes
  (`TauCeti.filteredSpaceSpectralSequence_page_two_d_neg_two_one_eq_zero_projectiveMomentFunction`
  on `ℝℙᴺ`).
* **Second page.** The object at `(0, 0)` of the second page (numbered `3`) is one copy of the
  coefficients
  (`TauCeti.nonempty_filteredSpaceSpectralSequence_page_three_X_zero_iso_projectiveMomentFunction`
  on `ℝℙᴺ`), the object at `(-2, 1)` is `R / 2R`
  (`nonempty_filteredSpaceSpectralSequence_page_three_X_neg_two_one_iso`), or `ℤ/2` with integer
  coefficients (`nonempty_filteredSpaceSpectralSequence_page_three_X_neg_two_one_iso_zmod`), and
  when right multiplication by `2` is injective on `R` every other object is zero
  (`isZero_filteredSpaceSpectralSequence_page_three_X`). So the integral second page consists of
  the integral homology groups `ℤ`, `ℤ/2`, `0` of `ℝℙ²`.

The results specific to `ℝℙ²` are in the namespace `TauCeti.RealProjectivePlane`, and all of them
concern the spectral sequence of the filtration by sublevels of the moment function above.

So the first page is the relative homology of the bands, free on the critical points, but it is not
yet the second page: its differential can be nonzero, and the critical counts `1, 1, 1` exceed the
integral Betti numbers `1, 0, 0`.

The differentials are the connecting maps of triples of sublevels
(`TauCeti.filteredSpaceSpectralSequence_first_page_d_eq`), and they are computed from the long exact
sequences of those triples. The inputs are the first page, the homology of `ℝℙ²`, `H₁ = R / 2R` and
`H₂ = 0` when right multiplication by `2` is injective, computed from its cellular chain complex
(`TauCeti.RealProjectiveSpace.singularHomologyProjectivizationLinearEquivOfOdd`,
`TauCeti.RealProjectiveSpace.isZero_singularHomology_projectivization_of_even`), and the
contractibility of the sublevel `{f ≤ a 1}`
(`TauCeti.contractibleSpace_sublevel_projectiveMomentFunction_of_mem_Ioo`), which identifies the
homology of `(ℝℙ², {f ≤ a 1})` with that of `ℝℙ²` in positive degrees
(`TauCeti.singularHomologyIsoSublevelPairOfContractibleSpace`).

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

namespace TauCeti.RealProjectivePlane

variable {w : Fin 3 → ℝ} {a : ℤ → ℝ} (R : Type) [Ring R]

/-! ### Sublevel pairs and triples -/

/-- The sublevel pair `({f ≤ a 3}, {f ≤ a 1})` of the moment function on `ℝℙ²`. -/
private abbrev pairOneThree (w : Fin 3 → ℝ) (ha : Monotone a) : TopPair :=
  TopPair.ofInclusion (X := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
    ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha (by norm_num : (1 : ℤ) ≤ 3))

/-- In positive degrees, the homology of `({f ≤ a 3}, {f ≤ a 1})` is that of `ℝℙ²`. -/
private def singularHomologyPairOneThreeIso (ha : Monotone a)
    (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) (k : ℕ) :
    (pairOneThree w ha).singularHomology (ModuleCat.of R R) (k + 1) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) (k + 1)).obj
        (ModuleCat.of R R)).obj (TopCat.of (ℙ ℝ (Fin 3 → ℝ))) :=
  -- The subspace `{f ≤ a 1}` is contractible and the space `{f ≤ a 3}` is all of `ℝℙ²`.
  have := contractibleSpace_sublevel_projectiveMomentFunction_of_mem_Ioo ha hcut
  (singularHomologyIsoSublevelPairOfContractibleSpace (ha (by norm_num : (1 : ℤ) ≤ 3))
    (fun x ↦ projectiveMomentFunction_le
      (fun i ↦ ((hcut i).2.trans_le (ha (by have := i.isLt; omega))).le) x) (ModuleCat.of R R)
    k).symm

/-- `H₂({f ≤ a 3}, {f ≤ a 1}; R) = 0` when right multiplication by `2` is injective on `R`. -/
private theorem isZero_singularHomology_pairOneThree_two (ha : Monotone a)
    (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) (h2 : IsRightRegular (2 : R)) :
    IsZero ((pairOneThree w ha).singularHomology (ModuleCat.of R R) 2) :=
  (RealProjectiveSpace.isZero_singularHomology_projectivization_of_even (N := 2) R h2 even_two
    two_ne_zero).of_iso (singularHomologyPairOneThreeIso R ha hcut 1)

/-- `H₁({f ≤ a 3}, {f ≤ a 1}; R) ≅ R / 2R`. -/
private def singularHomologyPairOneThreeOneIso (ha : Monotone a)
    (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) :
    (pairOneThree w ha).singularHomology (ModuleCat.of R R) 1 ≅
      ModuleCat.of R (R ⧸ R ∙ (2 : R)) :=
  singularHomologyPairOneThreeIso R ha hcut 0 ≪≫
    (RealProjectiveSpace.singularHomologyProjectivizationLinearEquivOfOdd (N := 2) R odd_one
      (by norm_num)).toModuleIso

/-- The sublevel triple `({f ≤ a 3}, {f ≤ a 2}, {f ≤ a 1})` of the moment function on `ℝℙ²`. -/
private abbrev upperTriple (w : Fin 3 → ℝ) (ha : Monotone a) : TopTriple :=
  TopTriple.ofInclusions (X := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
    ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha (by norm_num : (1 : ℤ) ≤ 2))
    ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha (by norm_num : (2 : ℤ) ≤ 3))

/-- `H₁({f ≤ a 3}, {f ≤ a 2}; R) = 0`: the band of the maximum has no critical point of index
`1`. -/
private theorem isZero_singularHomology_outerPair_upperTriple_one (ha : Monotone a)
    (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) :
    IsZero ((TopTriple.outerPair.obj (upperTriple w ha)).singularHomology (ModuleCat.of R R) 1) :=
  (isZero_filteredSpaceSpectralSequence_page_two_X_projectiveMomentFunction (ModuleCat.of R R)
    ha hcut (-3, 2) (by intro k; fin_cases k <;> simp)).of_iso
    (filteredSpaceSpectralSequenceFirstPageXIso (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
      (ModuleCat.of R R) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha) (-3, 2) 2 3 rfl
      rfl (-1) rfl 1 rfl).symm

/-- When right multiplication by `2` is injective on `R`, the connecting map
`H₂({f ≤ a 3}, {f ≤ a 2}) ⟶ H₁({f ≤ a 2}, {f ≤ a 1})` is injective. -/
private theorem mono_singularHomologyδ_upperTriple (ha : Monotone a)
    (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) (h2 : IsRightRegular (2 : R)) :
    Mono ((upperTriple w ha).singularHomologyδ (ModuleCat.of R R) 2 1) :=
  ((upperTriple w ha).singularHomology_exact_outer (ModuleCat.of R R) 2 1).mono_g
    ((isZero_singularHomology_pairOneThree_two R ha hcut h2).eq_of_src _ _)

/-- The connecting map `H₂({f ≤ a 3}, {f ≤ a 2}) ⟶ H₁({f ≤ a 2}, {f ≤ a 1})` has cokernel
`H₁({f ≤ a 3}, {f ≤ a 1}) ≅ R / 2R`. -/
private def cokernelSingularHomologyδUpperTripleIso (ha : Monotone a)
    (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) :
    cokernel ((upperTriple w ha).singularHomologyδ (ModuleCat.of R R) 2 1) ≅
      ModuleCat.of R (R ⧸ R ∙ (2 : R)) :=
  -- `H₁({f ≤ a 3}, {f ≤ a 2}) = 0`, so `H₁({f ≤ a 2}, {f ≤ a 1}) ⟶ H₁({f ≤ a 3}, {f ≤ a 1})` is
  -- onto, and it is the cokernel of the connecting map by exactness.
  have : Epi (TopPair.singularHomologyMap (TopTriple.innerToTotal.app (upperTriple w ha))
      (ModuleCat.of R R) 1) :=
    ((upperTriple w ha).singularHomology_exact_total (ModuleCat.of R R) 1).epi_f
      ((isZero_singularHomology_outerPair_upperTriple_one R ha hcut).eq_of_tgt _ _)
  (cokernelIsCokernel _).coconePointUniqueUpToIso
      ((upperTriple w ha).singularHomology_exact_inner (ModuleCat.of R R) 2 1).gIsCokernel ≪≫
    singularHomologyPairOneThreeOneIso R ha hcut

/-! ### The differentials and the second page -/

/-- The object at `(-4, 2)` on the first page is `H₂({f ≤ a 3}, {f ≤ a 2})`. -/
private def firstPageXTwoIso (ha : Monotone a) :
    ((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ))) (ModuleCat.of R R)
      ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).X (-4, 2) ≅
      (TopTriple.outerPair.obj (upperTriple w ha)).singularHomology (ModuleCat.of R R) 2 :=
  filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R) _ (-4, 2) 2 3 rfl rfl (-2) rfl 2
    rfl

/-- The object at `(-2, 1)` on the first page is `H₁({f ≤ a 2}, {f ≤ a 1})`. -/
private def firstPageXOneIso (ha : Monotone a) :
    ((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ))) (ModuleCat.of R R)
      ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).X (-2, 1) ≅
      (TopTriple.innerPair.obj (upperTriple w ha)).singularHomology (ModuleCat.of R R) 1 :=
  filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R) _ (-2, 1) 1 2 rfl rfl (-1) rfl 1
    rfl

/-- The differential from `(-4, 2)` to `(-2, 1)` on the first page is the connecting map of the
triple `({f ≤ a 3}, {f ≤ a 2}, {f ≤ a 1})`, up to the identifications of its source and target. -/
private theorem page_two_d_eq (ha : Monotone a) :
    ((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ))) (ModuleCat.of R R)
      ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).d (-4, 2) (-2, 1) =
      (firstPageXTwoIso R ha).hom ≫ (upperTriple w ha).singularHomologyδ (ModuleCat.of R R) 2 1 ≫
        (firstPageXOneIso R ha).inv :=
  -- `filteredSpaceSpectralSequence_first_page_d_eq` at `(p, q) = (-4, 2)` and `n = 1`, whose
  -- positions and degrees are the numerals above after evaluating their arithmetic.
  filteredSpaceSpectralSequence_first_page_d_eq (ModuleCat.of R R) _ 2 (-4) 1 (by norm_num)

/-- **The differential of index two on the first page of `ℝℙ²` is injective.** Under the
hypotheses of
`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, with
coefficients in a ring `R` on which right multiplication by `2` is injective, the differential from
`(-4, 2)` to `(-2, 1)` on the first page, the connecting map from the band of the maximum to the
band of the saddle, is a monomorphism. -/
theorem mono_filteredSpaceSpectralSequence_page_two_d_neg_four_two
    (ha : Monotone a) (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1)))
    (h2 : IsRightRegular (2 : R)) :
    Mono (((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
      (ModuleCat.of R R) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).d
        (-4, 2) (-2, 1)) := by
  have := mono_singularHomologyδ_upperTriple R ha hcut h2
  rw [page_two_d_eq R ha]
  infer_instance

/-- **The differential of index two on the first page of `ℝℙ²` has cokernel `R / 2R`.** Under
the hypotheses of
`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, with
coefficients in a ring `R`, the cokernel of the differential from `(-4, 2)` to `(-2, 1)` on the
first page is `R / 2R`. -/
theorem nonempty_cokernel_filteredSpaceSpectralSequence_page_two_d_neg_four_two_iso
    (ha : Monotone a) (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) :
    Nonempty (cokernel (((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
      (ModuleCat.of R R) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).d
        (-4, 2) (-2, 1)) ≅ ModuleCat.of R (R ⧸ R ∙ (2 : R))) := by
  rw [page_two_d_eq R ha]
  exact ⟨cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫
    cokernelSingularHomologyδUpperTripleIso R ha hcut⟩

/-- **The integral differential of index two on the first page of `ℝℙ²` has cokernel `ℤ/2`.**
Under the hypotheses of
`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, with
integer coefficients, the cokernel of the differential from `(-4, 2)` to `(-2, 1)` on the first
page is `ℤ/2`. -/
theorem nonempty_cokernel_filteredSpaceSpectralSequence_page_two_d_neg_four_two_iso_zmod
    (ha : Monotone a) (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) :
    Nonempty (cokernel (((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
      (ModuleCat.of ℤ ℤ) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 2).d
        (-4, 2) (-2, 1)) ≅ ModuleCat.of ℤ (ZMod 2)) := by
  obtain ⟨e⟩ :=
    nonempty_cokernel_filteredSpaceSpectralSequence_page_two_d_neg_four_two_iso ℤ ha hcut
  exact ⟨e ≪≫ (Int.quotientSpanNatEquivZMod 2).toAddEquiv.toIntLinearEquiv.toModuleIso⟩

/-- **The differential of index two on the first page of `ℝℙ²` is multiplication by `±2`.**
Under the hypotheses of
`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, with
integer coefficients, read through any identifications of the objects at `(-4, 2)` and `(-2, 1)` of
the first page with `ℤ`, the differential between them is multiplication by `2` or by `-2`; the
sign depends on the identifications. -/
theorem filteredSpaceSpectralSequence_page_two_d_neg_four_two_eq_two_smul_or_eq_neg_two_smul
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
    nonempty_cokernel_filteredSpaceSpectralSequence_page_two_d_neg_four_two_iso_zmod ha hcut
  exact ModuleCat.eq_smul_id_or_eq_neg_smul_id_of_cokernel_iso_zmod (n := 2) _
    (cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫ e)

/-- **The second page of `ℝℙ²` vanishes away from total degrees `0` and `-1`.** Under the
hypotheses of
`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, with
coefficients in a ring `R` on which right multiplication by `2` is injective, every object of the
second page (numbered `3`) other than those at `(0, 0)` and `(-2, 1)` is zero. -/
theorem isZero_filteredSpaceSpectralSequence_page_three_X
    (ha : Monotone a) (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1)))
    (h2 : IsRightRegular (2 : R)) (pq : ℤ × ℤ) (hpq₀ : pq ≠ (0, 0)) (hpq₁ : pq ≠ (-2, 1)) :
    IsZero (((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
      (ModuleCat.of R R) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 3).X
        pq) := by
  set E := filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
    (ModuleCat.of R R) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)
  by_cases hpq₂ : pq = (-4, 2)
  · subst hpq₂
    -- The differential out of `(-4, 2)` on the first page is injective, and the object at
    -- `(-6, 3)` vanishes, since no critical point lies in the band `3`.
    refine IsZero.of_iso ?_ (E.iso 2 3 (-4, 2)).symm
    refine HomologicalComplex.ExactAt.isZero_homology (((E.page 2).exactAt_iff' (-6, 3) (-4, 2)
      (-2, 1) ((ComplexShape.up' _).prev_eq' (by norm_num))
      ((ComplexShape.up' _).next_eq' (by norm_num))).2 ?_)
    have h₀ := isZero_filteredSpaceSpectralSequence_page_two_X_projectiveMomentFunction
      (ModuleCat.of R R) ha hcut (-6, 3) (by intro k; fin_cases k <;> simp)
    rw [ShortComplex.exact_iff_mono _ (h₀.eq_of_src _ _)]
    exact mono_filteredSpaceSpectralSequence_page_two_d_neg_four_two R ha hcut h2
  · refine E.isZero_page_X_of_le (r := 2) (by norm_num)
      (isZero_filteredSpaceSpectralSequence_page_two_X_projectiveMomentFunction _ ha hcut pq ?_)
      3 (by norm_num)
    intro k
    fin_cases k
    · simpa using hpq₀
    · simpa using hpq₁
    · simpa using hpq₂

/-- **The second page of `ℝℙ²` in total degree `-1` is `R / 2R`.** Under the hypotheses of
`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, with
coefficients in a ring `R`, the object at `(-2, 1)` on the second page (numbered `3`) is `R / 2R`,
the cokernel of the differential of index two on the first page. -/
theorem nonempty_filteredSpaceSpectralSequence_page_three_X_neg_two_one_iso
    (ha : Monotone a) (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) :
    Nonempty (((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
      (ModuleCat.of R R) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 3).X
        (-2, 1) ≅ ModuleCat.of R (R ⧸ R ∙ (2 : R))) := by
  set E := filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
    (ModuleCat.of R R) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)
  obtain ⟨e⟩ :=
    nonempty_cokernel_filteredSpaceSpectralSequence_page_two_d_neg_four_two_iso R ha hcut
  exact ⟨(E.iso 2 3 (-2, 1)).symm ≪≫
    (E.page 2).isoHomologyι (-2, 1) (0, 0) ((ComplexShape.up' _).next_eq' (by norm_num))
      (filteredSpaceSpectralSequence_page_two_d_neg_two_one_eq_zero_projectiveMomentFunction _ ha
        hcut) ≪≫
    (E.page 2).opcyclesIsoSc' (-4, 2) (-2, 1) (0, 0) ((ComplexShape.up' _).prev_eq' (by norm_num))
      ((ComplexShape.up' _).next_eq' (by norm_num)) ≪≫
    ((E.page 2).sc' (-4, 2) (-2, 1) (0, 0)).opcyclesIsoCokernel ≪≫ e⟩

/-- **The integral second page of `ℝℙ²` in total degree `-1` is `ℤ/2`.** Under the hypotheses of
`TauCeti.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_projectiveMomentFunction`, with
integer coefficients, the object at `(-2, 1)` on the second page (numbered `3`) is `ℤ/2`. -/
theorem nonempty_filteredSpaceSpectralSequence_page_three_X_neg_two_one_iso_zmod
    (ha : Monotone a) (hcut : ∀ k : Fin 3, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) :
    Nonempty (((filteredSpaceSpectralSequence (Y := TopCat.of (ℙ ℝ (Fin 3 → ℝ)))
      (ModuleCat.of ℤ ℤ) ((sublevel_mono (projectiveMomentFunction ℝ w)).comp ha)).page 3).X
        (-2, 1) ≅ ModuleCat.of ℤ (ZMod 2)) := by
  obtain ⟨e⟩ :=
    nonempty_filteredSpaceSpectralSequence_page_three_X_neg_two_one_iso ℤ ha hcut
  exact ⟨e ≪≫ (Int.quotientSpanNatEquivZMod 2).toAddEquiv.toIntLinearEquiv.toModuleIso⟩

end TauCeti.RealProjectivePlane
