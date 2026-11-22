/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Hyperfunction.Localization
import TauCeti.Analysis.Complex.Runge.Approximation
import TauCeti.Analysis.Distribution.Support

/-!
# The embedding of distributions into one-dimensional hyperfunctions

Let `U ⊆ ℝ` be open and let `B(U) = O(ℂ ∖ ℝ) / O(W(U))`, `W(U) = ℂ ∖ (ℝ ∖ U)`, be the space of
one-dimensional hyperfunctions on `U` (`TauCeti.Hyperfunction.OneDimBoundaryQuotient`). On an open
set `V` whose closure is a compact subset of `U`, a distribution `u` on `U` already has a class in
`B(V)`: the class of its Cauchy transform `(2πi)⁻¹ ⟨u_t, χ(t) / (t - z)⟩` with a cutoff `χ` equal to
one on `V` (`TauCeti.Hyperfunction.cauchyClass`). This file constructs the complex-linear map

`TauCeti.Hyperfunction.distributionToOneDimBoundary U : 𝓓'(U) → B(U)`,

characterized by restricting to these local Cauchy classes on every such `V`
(`TauCeti.Hyperfunction.oneDimBoundaryRestrict_distributionToOneDimBoundary`). It is the
**embedding of distributions into hyperfunctions** in dimension one:

* it is injective; more precisely, its restriction to an open `V ⊆ U` vanishes exactly when `u`
  vanishes on `V`
  (`TauCeti.Hyperfunction.oneDimBoundaryRestrict_distributionToOneDimBoundary_eq_zero_iff`), so
  the largest open set on which the hyperfunction vanishes is the complement of the support of
  `u`;
* it commutes with restriction of distributions and of hyperfunctions to open subsets
  (`TauCeti.Hyperfunction.distributionToOneDimBoundary_restrictCLM`);
* for a distribution with compact support in `U`, it is the class of the Cauchy transform with any
  cutoff equal to one near the support (`TauCeti.Hyperfunction.distributionToOneDimBoundary_eq_mk`).

## Construction

Uniqueness holds because `B` is a separated presheaf and the relatively compact open subsets
cover `U` (`TauCeti.Hyperfunction.eq_of_forall_oneDimBoundaryRestrict_eq`, in
`TauCeti/Analysis/Hyperfunction/OneDimensional.lean`). Existence does not use
the gluing property of `B`; it is a Mittag-Leffler argument. Exhaust `W(U)` by the compact sets
`Lₙ` of `TauCeti.filledExhaustion`, which form Runge compact pairs with `W(U)`, and let
`Kₙ = Lₙ ∩ ℝ`, a compact exhaustion of `U`. Choose cutoffs `ψₙ` equal to one near `Kₙ` and let
`Cₙ` be the Cauchy transform of `u` with cutoff `ψₙ`. The difference `Cₙ₊₁ - Cₙ` extends
holomorphically across the open set where `ψₙ = ψₙ₊₁ = 1`, which contains `Kₙ`, hence to a
neighbourhood of `Lₙ`. By Runge's theorem it is within `2⁻ⁿ` on `Lₙ` of a function `Rₙ` holomorphic
on `W(U)`. The series

`F = C₀ + ∑ₙ (Cₙ₊₁ - Cₙ - Rₙ)`

converges locally uniformly on `ℂ ∖ ℝ`, and `F - Cₘ₊₁ = -∑_{n ≤ m} Rₙ + ∑_{n > m} (Cₙ₊₁ - Cₙ - Rₙ)`
extends holomorphically across the interior of `Kₘ₊₁`. So the class of `F` restricts to the Cauchy
class of `u` on every relatively compact `V`.

## References

* H. Komatsu, *An introduction to the theory of hyperfunctions*, in *Hyperfunctions and
  pseudo-differential equations*, Lecture Notes in Mathematics 287 (1973), 3–40, §1.
* A. Kaneko, *Introduction to hyperfunctions*, Chapter 1.
* L. Hörmander, *The analysis of linear partial differential operators I*, §3.1 and §9.1.
-/

public section

noncomputable section

open Complex Filter Set TopologicalSpace Distribution
open scoped Distributions Topology

namespace TauCeti.Hyperfunction

/-! ### The exhaustions of `W(U)` and of `U` -/

section Stages

variable (U : Opens ℝ)

/-- The `n`-th stage `Lₙ` of the filled exhaustion of `W(U)`. -/
private abbrev complexStage (n : ℕ) : Set ℂ :=
  filledExhaustion (complexNeighborhood U : Set ℂ) n

/-- The real points `Kₙ = Lₙ ∩ ℝ` of the `n`-th stage of the filled exhaustion of `W(U)`. -/
private abbrev realStage (n : ℕ) : Set ℝ :=
  ((↑) : ℝ → ℂ) ⁻¹' complexStage U n

private theorem isCompact_realStage (n : ℕ) : IsCompact (realStage U n) :=
  isometry_ofReal.isClosedEmbedding.isCompact_preimage (isCompact_filledExhaustion _ n)

private theorem realStage_subset (n : ℕ) : realStage U n ⊆ U := fun x hx ↦ by
  simpa using filledExhaustion_subset _ n hx

private theorem realStage_mono {m n : ℕ} (h : m ≤ n) : realStage U m ⊆ realStage U n :=
  preimage_mono (filledExhaustion_mono h)

/-- A stage of the exhaustion of `W(U)` lies in `W(O)` for every real open `O` containing its real
points. -/
private theorem complexStage_subset_complexNeighborhood {n : ℕ} {O : Opens ℝ}
    (h : realStage U n ⊆ O) : complexStage U n ⊆ complexNeighborhood O := by
  intro z hz
  by_cases him : z.im = 0
  · have hz' : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [him])
    refine mem_complexNeighborhood_iff.2 (Or.inr (h ?_))
    rw [realStage, mem_preimage, hz']
    exact hz
  · exact mem_complexNeighborhood_iff.2 (Or.inl him)

/-- Every compact subset of `U` lies in the interior of some `Kₙ`. -/
private theorem exists_subset_interior_realStage {C : Set ℝ} (hC : IsCompact C)
    (hCU : C ⊆ U) : ∃ n, C ⊆ interior (realStage U n) := by
  obtain ⟨n, hn⟩ := (complexNeighborhood U).isOpen.exists_subset_interior_filledExhaustion
    (hC.image continuous_ofReal) (image_subset_iff.2 fun x hx ↦ by simpa using hCU hx)
  exact ⟨n, (image_subset_iff.1 hn).trans (preimage_interior_subset_interior_preimage
    continuous_ofReal)⟩

end Stages

/-! ### Existence of a global class -/

variable {U : Opens ℝ}

/-- The data of the Mittag-Leffler construction: cutoffs `ψₙ` equal to one near `Kₙ`, holomorphic
extensions `Gₙ` of the differences `Cₙ₊₁ - Cₙ` of the Cauchy transforms across real open sets
`Oₙ ⊇ Kₙ`, and Runge approximations `Rₙ` of `Gₙ` on `Lₙ` by functions holomorphic on `W(U)`. -/
private theorem exists_cauchyTransform_runge (u : 𝓓'(U, ℂ)) :
    ∃ (ψ : ℕ → 𝓓(U, ℝ)) (O : ℕ → Opens ℝ) (G R : ℕ → ℂ → ℂ),
      (∀ n, ∀ᶠ t in 𝓝ˢ (realStage U n), ψ n t = 1) ∧ (∀ n, realStage U n ⊆ O n) ∧
      (∀ n, DifferentiableOn ℂ (G n) (complexNeighborhood (O n))) ∧
      (∀ n, ∀ z ∈ nonRealOpen,
        G n z = cauchyTransform u (ψ (n + 1)) z - cauchyTransform u (ψ n) z) ∧
      (∀ n, DifferentiableOn ℂ (R n) (complexNeighborhood U)) ∧
      ∀ n, ∀ z ∈ complexStage U n, ‖G n z - R n z‖ < (1 / 2 : ℝ) ^ n := by
  choose ψ hψ _ using fun n ↦ TestFunction.exists_eventually_eq_one (n := ⊤)
    (isCompact_realStage U n) (realStage_subset U n)
  -- `Oₙ` is the interior of the set where `ψₙ` and `ψₙ₊₁` are both one.
  let O : ℕ → Opens ℝ := fun n ↦ ⟨interior {t | ψ (n + 1) t = 1 ∧ ψ n t = 1}, isOpen_interior⟩
  have hO (n : ℕ) : realStage U n ⊆ O n := subset_interior_iff_mem_nhdsSet.2 <|
    ((hψ (n + 1)).filter_mono (nhdsSet_mono (realStage_mono U n.le_succ))).and (hψ n)
  have hG (n : ℕ) : ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (complexNeighborhood (O n)) ∧
      ∀ z ∈ nonRealOpen,
        G z = cauchyTransform u (ψ (n + 1)) z - cauchyTransform u (ψ n) z := by
    have h : (ψ (n + 1) : ℝ → ℝ) =ᶠ[𝓝ˢ ((O n : Set ℝ) ∩ dsupport u)] ψ n := by
      filter_upwards [(O n).isOpen.mem_nhdsSet.2 inter_subset_left] with t ht
      rw [(interior_subset ht : _ ∧ _).1, (interior_subset ht : _ ∧ _).2]
    obtain ⟨G, hG, hGf⟩ := mem_throughReal_iff.1 (cauchyTransform_sub_mem_throughReal u h)
    exact ⟨G, (mem_holomorphicSections_iff.1 hG).1, fun z hz ↦ hGf hz⟩
  choose G hGd hGe using hG
  have hR (n : ℕ) : ∃ R : ℂ → ℂ, DifferentiableOn ℂ R (complexNeighborhood U) ∧
      ∀ z ∈ complexStage U n, ‖G n z - R z‖ < (1 / 2 : ℝ) ^ n := by
    have hp := (complexNeighborhood U).isOpen.isRungeCompactPair_filledExhaustion n
    exact hp.isFilledIn.exists_differentiableOn_norm_sub_lt hp.isCompact hp.subset
      (complexNeighborhood (O n)).isOpen (complexStage_subset_complexNeighborhood U (hO n))
      (hGd n) (by positivity)
  choose R hRd hRb using hR
  exact ⟨ψ, O, G, R, hψ, hO, hGd, hGe, hRd, hRb⟩

/-- **The telescoping step.** Off the real line, the Mittag-Leffler sum
`F = C₀ + ∑ₖ (Gₖ - Rₖ)` minus `Cₘ₊₁` agrees with a function holomorphic on `W(int Kₘ₊₁)`, namely
`∑_{k > m} (Gₖ - Rₖ) - ∑_{k ≤ m} Rₖ`. -/
private theorem exists_differentiableOn_eq_tsum_sub (u : 𝓓'(U, ℂ)) {ψ : ℕ → 𝓓(U, ℝ)}
    {O : ℕ → Opens ℝ} {G R : ℕ → ℂ → ℂ} (hO : ∀ n, realStage U n ⊆ O n)
    (hGd : ∀ n, DifferentiableOn ℂ (G n) (complexNeighborhood (O n)))
    (hGe : ∀ n, ∀ z ∈ nonRealOpen,
      G n z = cauchyTransform u (ψ (n + 1)) z - cauchyTransform u (ψ n) z)
    (hRd : ∀ n, DifferentiableOn ℂ (R n) (complexNeighborhood U))
    (hRb : ∀ n, ∀ z ∈ complexStage U n, ‖G n z - R n z‖ < (1 / 2 : ℝ) ^ n) (m : ℕ) :
    ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H (complexNeighborhood ⟨interior (realStage U (m + 1)), isOpen_interior⟩) ∧
      ∀ z ∈ nonRealOpen, cauchyTransform u (ψ 0) z + ∑' k, (G k z - R k z) -
        cauchyTransform u (ψ (m + 1)) z = H z := by
  set I : Opens ℝ := ⟨interior (realStage U (m + 1)), isOpen_interior⟩
  have hIU : I ≤ U := interior_subset.trans (realStage_subset U _)
  have htb (k : ℕ) (z : ℂ) (hz : z ∈ complexStage U k) : ‖G k z - R k z‖ ≤ (1 / 2 : ℝ) ^ k :=
    (hRb k z hz).le
  -- The terms from index `m + 1` on are holomorphic on `W(I)`, since `I ⊆ Kₖ ⊆ Oₖ`.
  have htd (k : ℕ) : DifferentiableOn ℂ (fun z ↦ G (k + (m + 1)) z - R (k + (m + 1)) z)
      (complexNeighborhood I) :=
    ((hGd _).mono (complexNeighborhood_mono (interior_subset.trans
      ((realStage_mono U (Nat.le_add_left _ k)).trans (hO _))))).sub
      ((hRd _).mono (complexNeighborhood_mono hIU))
  refine ⟨fun z ↦ ∑' k, (G (k + (m + 1)) z - R (k + (m + 1)) z) -
      ∑ k ∈ Finset.range (m + 1), R k z, ?_, fun z hz ↦ ?_⟩
  · exact (differentiableOn_tsum_of_forall_norm_le_filledExhaustion (complexNeighborhood I).isOpen
      (complexNeighborhood_mono hIU) summable_geometric_two htd fun k z hz ↦
        (htb _ z (filledExhaustion_mono (Nat.le_add_right k _) hz)).trans
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right k _))).sub
      (DifferentiableOn.fun_sum fun k _ ↦ (hRd k).mono (complexNeighborhood_mono hIU))
  have hs : Summable fun k ↦ G k z - R k z :=
    summable_of_forall_norm_le_filledExhaustion summable_geometric_two htb
      ((complexNeighborhood U).isOpen.interior_eq.symm ▸ nonRealOpen_le_complexNeighborhood U hz)
  -- Telescoping: `∑_{k ≤ m} (Gₖ - Rₖ) = Cₘ₊₁ - C₀ - ∑_{k ≤ m} Rₖ` off the real line.
  have htel : ∑ k ∈ Finset.range (m + 1), (G k z - R k z) = cauchyTransform u (ψ (m + 1)) z -
      cauchyTransform u (ψ 0) z - ∑ k ∈ Finset.range (m + 1), R k z := by
    simp only [hGe _ z hz, Finset.sum_sub_distrib,
      Finset.sum_range_sub (fun k ↦ cauchyTransform u (ψ k) z)]
  rw [← hs.sum_add_tsum_nat_add (m + 1), htel]
  ring

/-- **Existence of the hyperfunction of a distribution.** Every distribution `u` on an open set
`U ⊆ ℝ` has a one-dimensional hyperfunction on `U` whose restriction to each open `V` with compact
closure in `U` is the Cauchy class of `u` on `V`. -/
private theorem exists_forall_oneDimBoundaryRestrict_eq_cauchyClass (u : 𝓓'(U, ℂ)) :
    ∃ q : OneDimBoundaryQuotient U, ∀ (V : Opens ℝ) (h : V ≤ U)
      (hV : IsCompact (closure (V : Set ℝ))) (hVU : closure (V : Set ℝ) ⊆ U),
      oneDimBoundaryRestrict h q = cauchyClass V hV hVU u := by
  obtain ⟨ψ, O, G, R, hψ, hO, hGd, hGe, hRd, hRb⟩ := exists_cauchyTransform_runge u
  -- The global representative `F = C₀ + ∑ₖ (Gₖ - Rₖ)` on `ℂ ∖ ℝ`.
  let F₀ : ℂ → ℂ := fun z ↦ cauchyTransform u (ψ 0) z + ∑' k, (G k z - R k z)
  have hF₀ : DifferentiableOn ℂ F₀ nonRealOpen :=
    (mem_holomorphicSections_iff.1 (cauchyTransform_mem_holomorphicSections u (ψ 0))).1.add <|
      differentiableOn_tsum_of_forall_norm_le_filledExhaustion nonRealOpen.isOpen
        (nonRealOpen_le_complexNeighborhood U) summable_geometric_two (fun k ↦ ((hGd k).mono
          (nonRealOpen_le_complexNeighborhood _)).sub
          ((hRd k).mono (nonRealOpen_le_complexNeighborhood U))) fun k z hz ↦ (hRb k z hz).le
  have hF : (nonRealOpen : Set ℂ).indicator F₀ ∈ holomorphicSections nonRealOpen :=
    mem_holomorphicSections_iff.2
      ⟨hF₀.congr fun z hz ↦ indicator_of_mem hz _, fun z hz ↦ indicator_of_notMem hz _⟩
  refine ⟨Submodule.Quotient.mk ⟨_, hF⟩, fun V _ hV hVU ↦ ?_⟩
  obtain ⟨m, hm⟩ := exists_subset_interior_realStage U hV hVU
  have hVK : (V : Set ℝ) ⊆ realStage U (m + 1) :=
    subset_closure.trans (hm.trans (interior_subset.trans (realStage_mono U m.le_succ)))
  rw [cauchyClass_eq_mk V hV hVU u (χ := ψ (m + 1))
      ((hψ (m + 1)).filter_mono (nhdsSet_mono (inter_subset_left.trans hVK))),
    oneDimBoundaryRestrict_mk, Submodule.Quotient.eq]
  -- `F - Cₘ₊₁` extends holomorphically across the interior of `Kₘ₊₁`, which contains `V`.
  obtain ⟨H, hH, hFH⟩ := exists_differentiableOn_eq_tsum_sub u hO hGd hGe hRd hRb m
  refine throughReal_antitone (fun x hx ↦ interior_mono (realStage_mono U m.le_succ)
    (hm (subset_closure hx))) (mem_throughReal_iff.2 ⟨_, mem_holomorphicSections_iff.2
      ⟨hH.congr fun z hz ↦ indicator_of_mem hz _, fun z hz ↦ indicator_of_notMem hz _⟩,
      fun z hz ↦ ?_⟩)
  rw [indicator_of_mem (nonRealOpen_le_complexNeighborhood _ hz), Submodule.coe_sub,
    Pi.sub_apply]
  -- Unfold the representatives to the functions they carry.
  dsimp only
  rw [indicator_of_mem hz]
  exact (hFH z hz).symm

/-! ### The embedding -/

/-- The defining property of `distributionToOneDimBoundary U u`. -/
private theorem spec_choose (u : 𝓓'(U, ℂ)) (V : Opens ℝ) (h : V ≤ U)
    (hV : IsCompact (closure (V : Set ℝ))) (hVU : closure (V : Set ℝ) ⊆ U) :
    oneDimBoundaryRestrict h (exists_forall_oneDimBoundaryRestrict_eq_cauchyClass u).choose =
      cauchyClass V hV hVU u :=
  (exists_forall_oneDimBoundaryRestrict_eq_cauchyClass u).choose_spec V h hV hVU

/-- The **embedding of distributions into one-dimensional hyperfunctions** on an open set
`U ⊆ ℝ`: the unique hyperfunction on `U` whose restriction to every open `V` with compact closure in
`U` is the class of the Cauchy transform `(2πi)⁻¹ ⟨u_t, χ(t) / (t - z)⟩`, `χ` a cutoff equal to one
on `V` (`oneDimBoundaryRestrict_distributionToOneDimBoundary`). It is injective
(`distributionToOneDimBoundary_injective`). -/
def distributionToOneDimBoundary (U : Opens ℝ) : 𝓓'(U, ℂ) →ₗ[ℂ] OneDimBoundaryQuotient U where
  toFun u := (exists_forall_oneDimBoundaryRestrict_eq_cauchyClass u).choose
  map_add' u v := eq_of_forall_oneDimBoundaryRestrict_eq fun V h hV hVU ↦ by
    rw [map_add, spec_choose _ V h hV hVU, spec_choose _ V h hV hVU, spec_choose _ V h hV hVU,
      map_add]
  map_smul' c u := eq_of_forall_oneDimBoundaryRestrict_eq fun V h hV hVU ↦ by
    rw [map_smul, spec_choose _ V h hV hVU, spec_choose _ V h hV hVU, map_smul,
      RingHom.id_apply]

/-- **The local form of the embedding.** On an open set `V` whose closure is a compact subset of
`U`, the hyperfunction of `u` restricts to the Cauchy class of `u` on `V`. -/
theorem oneDimBoundaryRestrict_distributionToOneDimBoundary (V : Opens ℝ) (h : V ≤ U)
    (hV : IsCompact (closure (V : Set ℝ))) (hVU : closure (V : Set ℝ) ⊆ U) (u : 𝓓'(U, ℂ)) :
    oneDimBoundaryRestrict h (distributionToOneDimBoundary U u) = cauchyClass V hV hVU u :=
  spec_choose u V h hV hVU

/-- **Characterization of the embedding.** A hyperfunction on `U` is the hyperfunction of `u` if and
only if its restriction to every open set `V` with compact closure in `U` is the Cauchy class of `u`
on `V`. -/
theorem eq_distributionToOneDimBoundary_iff {q : OneDimBoundaryQuotient U} {u : 𝓓'(U, ℂ)} :
    q = distributionToOneDimBoundary U u ↔
      ∀ (V : Opens ℝ) (h : V ≤ U) (hV : IsCompact (closure (V : Set ℝ)))
        (hVU : closure (V : Set ℝ) ⊆ U), oneDimBoundaryRestrict h q = cauchyClass V hV hVU u := by
  refine ⟨fun hq V h hV hVU ↦ ?_,
    fun hq ↦ eq_of_forall_oneDimBoundaryRestrict_eq fun V h hV hVU ↦ ?_⟩
  · rw [hq, oneDimBoundaryRestrict_distributionToOneDimBoundary]
  · rw [hq V h hV hVU, oneDimBoundaryRestrict_distributionToOneDimBoundary]

/-- **Naturality.** The embedding commutes with restriction: for open `U' ⊆ U`, the hyperfunction of
the restriction `u|_{U'}` is the restriction to `U'` of the hyperfunction of `u`. -/
theorem distributionToOneDimBoundary_restrictCLM {U' : Opens ℝ} (h : U' ≤ U) (u : 𝓓'(U, ℂ)) :
    distributionToOneDimBoundary U' (restrictCLM u) =
      oneDimBoundaryRestrict h (distributionToOneDimBoundary U u) := by
  refine (eq_distributionToOneDimBoundary_iff.2 fun V hV' hV hVU' ↦ ?_).symm
  rw [oneDimBoundaryRestrict_oneDimBoundaryRestrict, cauchyClass_restrictCLM V hV h hVU',
    oneDimBoundaryRestrict_distributionToOneDimBoundary]

/-- **Compactly supported distributions.** If a cutoff `χ` on `U` equals one near the support of
`u` (so that `u` has compact support in `U`), the hyperfunction of `u` is the class of the Cauchy
transform of `u` with cutoff `χ`. -/
theorem distributionToOneDimBoundary_eq_mk (u : 𝓓'(U, ℂ)) {χ : 𝓓(U, ℝ)}
    (hχ : ∀ᶠ t in 𝓝ˢ (dsupport u), χ t = 1) :
    distributionToOneDimBoundary U u =
      Submodule.Quotient.mk ⟨cauchyTransform u χ, cauchyTransform_mem_holomorphicSections u χ⟩ := by
  refine (eq_distributionToOneDimBoundary_iff.2 fun V _ hV hVU ↦ ?_).symm
  rw [oneDimBoundaryRestrict_mk,
    cauchyClass_eq_mk V hV hVU u (hχ.filter_mono (nhdsSet_mono inter_subset_right))]

/-- **The support of the hyperfunction of a distribution.** The hyperfunction of `u` vanishes on an
open set `V ⊆ U` exactly when `u` vanishes on `V`, that is, when `V` does not meet `dsupport u`. -/
theorem oneDimBoundaryRestrict_distributionToOneDimBoundary_eq_zero_iff {V : Opens ℝ} (h : V ≤ U)
    (u : 𝓓'(U, ℂ)) :
    oneDimBoundaryRestrict h (distributionToOneDimBoundary U u) = 0 ↔
      Disjoint (V : Set ℝ) (dsupport u) := by
  constructor
  · -- Each point of `V` lies in an open `V'` with compact closure in `V`, on which the Cauchy class
    -- of `u` vanishes, so `V'` misses the support.
    refine fun h0 ↦ disjoint_left.2 fun x hx hxu ↦ ?_
    obtain ⟨V', hV', hxV', hV'V, hV'c⟩ :=
      exists_open_between_and_isCompact_closure isCompact_singleton V.isOpen
        (singleton_subset_iff.2 hx)
    have h' : closure V' ⊆ U := hV'V.trans h
    have hle : (⟨V', hV'⟩ : Opens ℝ) ≤ V := fun _ hy ↦ hV'V (subset_closure hy)
    have hz := oneDimBoundaryRestrict_distributionToOneDimBoundary ⟨V', hV'⟩
      (hle.trans h) hV'c h' u
    rw [← oneDimBoundaryRestrict_oneDimBoundaryRestrict hle h, h0,
      map_zero, eq_comm, cauchyClass_eq_zero_iff] at hz
    exact disjoint_left.1 hz (hxV' rfl) hxu
  · refine fun hd ↦ eq_of_forall_oneDimBoundaryRestrict_eq fun V' _ hV' hV'V ↦ ?_
    rw [oneDimBoundaryRestrict_oneDimBoundaryRestrict, map_zero,
      oneDimBoundaryRestrict_distributionToOneDimBoundary V' _ hV' (hV'V.trans h),
      cauchyClass_eq_zero_iff]
    exact hd.mono_left (subset_closure.trans hV'V)

/-- The hyperfunction of `u` is zero exactly when `u` is zero. -/
@[simp]
theorem distributionToOneDimBoundary_eq_zero_iff {u : 𝓓'(U, ℂ)} :
    distributionToOneDimBoundary U u = 0 ↔ u = 0 := by
  refine ⟨fun h0 ↦ ?_, fun h ↦ h ▸ map_zero _⟩
  have hd := (oneDimBoundaryRestrict_distributionToOneDimBoundary_eq_zero_iff le_rfl u).1
    (by rw [oneDimBoundaryRestrict_self, h0])
  refine ContinuousLinearMap.ext fun φ ↦ ?_
  exact (isVanishingOn_iff_disjoint_dsupport u U.isOpen).2 hd φ φ.tsupport_subset

/-- **The embedding of distributions into one-dimensional hyperfunctions is injective.** -/
theorem distributionToOneDimBoundary_injective (U : Opens ℝ) :
    Function.Injective (distributionToOneDimBoundary U) :=
  (injective_iff_map_eq_zero _).2 fun _ ↦ distributionToOneDimBoundary_eq_zero_iff.1

end TauCeti.Hyperfunction
