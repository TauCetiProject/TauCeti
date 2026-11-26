/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Analysis.Distribution.TestFunction.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContDiff.Cutoff

/-!
# Finite localization of test functions

A test function can be written as a finite sum of tests subordinate to any open cover of its
support; for a cover by finitely many open sets and one further open set `Z`, the piece supported
in `Z` can be kept separate
(`TestFunction.exists_add_sum_eq_of_tsupport_subset_biUnion_union`). Consequently, an additive
map on test functions which vanishes locally vanishes globally; continuity of the additive map is
not required. If `E` is finite-dimensional, every compact
subset of the domain also has a cutoff test function equal to one on a neighbourhood of it, every
point of the domain has a test function with a prescribed value there, supported in a given
neighbourhood of the point, and every point of the domain has a test function equal to one near it
and supported in a given neighbourhood of it (`TestFunction.exists_eqOn_one_tsupport_subset`); in
infinite dimension every test function is zero (`TestFunction.eq_zero_of_not_finiteDimensional`).
Near a point where a complex test function `φ` does not vanish, every complex test function
supported close enough to the point is a smooth multiple of `φ`
(`TestFunction.exists_mem_nhds_forall_exists_contDiff_eq_mul`); this is how localization
arguments replace one cutoff by another. The multiplier is a quotient `χ / φ`, which is smooth
when no zero of `φ` lies in the closed support of `χ`
(`ContDiff.mul_inv_of_forall_notMem_tsupport`). In particular some cutoff equal to one near the
point is a test-function multiple of `φ` (`TestFunction.exists_eventually_eq_one_and_mul_eq`).
A compact set `K` in the interior of a compact set `K'` has a complex smooth cutoff supported in
`K'` and equal to one on `K` (`ContDiffMapSupportedIn.exists_eqOn_one_of_subset_interior`).

Multiplication by a smooth function `χ` whose closed support meets `Ω` only inside an open set `U`
sends tests on `Ω` to tests on `U`. This is `TestFunction.cutoffCLM`, a continuous linear map
`𝓓^{n}(Ω, F) →L[ℝ] 𝓓^{n}(U, F)` for the LF topologies; it is the localization step used to glue
distributions and currents defined on the members of an open cover.

The decomposition multiplies by a finite smooth partition of unity on the compact support
(`IsCompact.exists_contDiff_tsupport_subset_finset_sum_eq_one`, built from Mathlib's
`SmoothPartitionOfUnity.exists_isSubordinate`), and the cutoff packages
`IsCompact.exists_contDiff_cutoff` as a test function. This is the partition-of-unity localization
of distributions described in Hörmander, *The Analysis of Linear Partial Differential Operators I*,
§2.2 (Localization).
-/

public section

open Set TopologicalSpace Filter
open scoped Distributions ContDiff Manifold Topology

namespace TestFunction

section Cutoff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω U : Opens E} {n : ℕ∞} {χ : E → ℝ}

/-- Multiplication `φ ↦ χ φ` by a `C^n` function `χ` whose topological support meets `Ω` only
inside `U`, as a continuous linear map from tests on `Ω` to tests on `U`. When `U = Ω` this is
`TestFunction.smulLeftCLM`. -/
noncomputable def cutoffCLM (hχ : ContDiff ℝ n χ) (hχU : tsupport χ ∩ Ω ⊆ U) :
    𝓓^{n}(Ω, F) →L[ℝ] 𝓓^{n}(U, F) :=
  TestFunction.limitCLM ℝ
    (fun φ ↦ ⟨fun x ↦ χ x • φ x, hχ.smul φ.contDiff, φ.hasCompactSupport.smul_left,
      (subset_inter (tsupport_smul_subset_left _ _) (tsupport_smul_subset_right _ _)).trans <|
        (inter_subset_inter_right _ φ.tsupport_subset).trans hχU⟩)
    (fun K hKΩ ↦
      -- On tests supported in `K`, the product is supported in the compact set `K ∩ tsupport χ`,
      -- which lies in `U`. Its structure maps are those of the product in `𝓓^{n}_{K}(E, F)`.
      letI K' : Compacts E := ⟨K ∩ tsupport χ, K.isCompact.inter_right (isClosed_tsupport χ)⟩
      haveI hsupp (f : 𝓓^{n}_{K}(E, F)) : Function.support (fun x ↦ χ x • f x) ⊆ (K' : Set E) :=
        fun _ hx ↦ ⟨f.support_subset (Function.support_smul_subset_right _ _ hx),
          subset_tsupport _ (Function.support_smul_subset_left _ _ hx)⟩
      letI M : 𝓓^{n}_{K}(E, F) →L[ℝ] 𝓓^{n}_{K'}(E, F) :=
        { toFun f := .of_support_subset (hχ.smul f.contDiff) (hsupp f)
          map_add' f g := by ext; simp [ContDiffMapSupportedIn.coe_of_support_subset, smul_add]
          map_smul' c f := by
            ext; simp [ContDiffMapSupportedIn.coe_of_support_subset, smul_comm c]
          cont := by
            refine (ContDiffMapSupportedIn.continuous_iff_comp _).2 fun i ↦ ?_
            refine ((ContDiffMapSupportedIn.structureMapCLM ℝ n i).continuous.comp
              (ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ).flip hχ
                (K := K)).continuous).congr fun f ↦ ?_
            have hf : ⇑(ContDiffMapSupportedIn.of_support_subset (hχ.smul f.contDiff) (hsupp f)) =
                fun x ↦ χ x • f x :=
              funext <| ContDiffMapSupportedIn.coe_of_support_subset _ _
            ext x : 1
            simp [ContDiffMapSupportedIn.structureMapCLM_apply, hf] }
      ofSupportedInCLM ℝ (K := K') (fun _ hx ↦ hχU ⟨hx.2, hKΩ hx.1⟩) ∘L M)
    (fun _ _ _ ↦ rfl)

@[simp]
theorem cutoffCLM_apply (hχ : ContDiff ℝ n χ) (hχU : tsupport χ ∩ Ω ⊆ U) (φ : 𝓓^{n}(Ω, F))
    (x : E) : cutoffCLM hχ hχU φ x = χ x • φ x := by
  -- This is the pointwise formula defining `cutoffCLM`; its body is not exported, so the
  -- definitional unfolding happens inside the proof.
  exact rfl

/-- Multiplying by a cutoff does not enlarge the support of a test function. -/
theorem tsupport_cutoffCLM_subset (hχ : ContDiff ℝ n χ) (hχU : tsupport χ ∩ Ω ⊆ U)
    (φ : 𝓓^{n}(Ω, F)) : tsupport (cutoffCLM hχ hχU φ : E → F) ⊆ tsupport χ ∩ tsupport φ :=
  tsupport_subset_inter_of_apply_eq_smul (cutoffCLM_apply hχ hχU φ)

end Cutoff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {n : ℕ∞}

omit [FiniteDimensional ℝ E] in
/-- A test function is a finite sum of test functions supported in members of an open cover
of its topological support. The summands are pointwise no larger in norm than the test function
itself. -/
theorem exists_sum_subordinate (φ : 𝓓^{n}(Ω, F)) {ι : Type*} (U : ι → Set E)
    (hU : ∀ i, IsOpen (U i)) (hcover : tsupport φ ⊆ ⋃ i, U i) :
    ∃ (s : Finset ι) (ψ : s → 𝓓^{n}(Ω, F)),
      (∀ i, tsupport (ψ i) ⊆ U i) ∧ ∑ i, ψ i = φ ∧ ∀ i x, ‖ψ i x‖ ≤ ‖φ x‖ := by
  classical
  by_cases hE : FiniteDimensional ℝ E
  swap
  · exact ⟨∅, isEmptyElim, isEmptyElim, by simp [eq_zero_of_not_finiteDimensional φ hE],
      isEmptyElim⟩
  obtain ⟨s, χ, hχ, hχ0, hχ1, hsum⟩ :=
    φ.hasCompactSupport.isCompact.exists_contDiff_tsupport_subset_finset_sum_eq_one hU hcover
  let ψ : s → 𝓓^{n}(Ω, F) := fun i ↦
    ⟨fun x ↦ χ i x • φ x, ((hχ i).1.of_le (by simp)).smul φ.contDiff,
      φ.hasCompactSupport.smul_left, (tsupport_smul_subset_right _ _).trans φ.tsupport_subset⟩
  refine ⟨s, ψ, fun i ↦ (tsupport_smul_subset_left _ _).trans (hχ i).2.2, ?_, fun i x ↦ ?_⟩
  · ext x
    simp only [sum_apply]
    by_cases hx : x ∈ tsupport φ
    · simp only [ψ, coe_mk, ← Finset.sum_smul, Finset.sum_coe_sort s (fun i ↦ χ i x),
        hsum x hx, one_smul]
    · simp [ψ, image_eq_zero_of_notMem_tsupport hx]
  · -- Each summand is `χ i • φ` with `0 ≤ χ i ≤ 1`.
    have hle : χ i x ≤ 1 := (Finset.single_le_sum (fun j _ ↦ hχ0 j x) i.property).trans (hχ1 x)
    simpa [ψ, norm_smul, abs_of_nonneg (hχ0 i x)] using
      mul_le_of_le_one_left (norm_nonneg (φ x)) hle

omit [FiniteDimensional ℝ E] in
/-- A test function supported in `(⋃ i ∈ t, U i) ∪ Z`, for finitely many open sets `U i` and an
open set `Z`, is the sum of a test function supported in `Z` and test functions supported in the
`U i`. -/
theorem exists_add_sum_eq_of_tsupport_subset_biUnion_union (φ : 𝓓^{n}(Ω, F)) {ι : Type*}
    {t : Finset ι} {U : ι → Set E} (hU : ∀ i, IsOpen (U i)) {Z : Set E} (hZ : IsOpen Z)
    (hφ : tsupport φ ⊆ (⋃ i ∈ t, U i) ∪ Z) :
    ∃ (φ₀ : 𝓓^{n}(Ω, F)) (φs : t → 𝓓^{n}(Ω, F)),
      tsupport φ₀ ⊆ Z ∧ (∀ i, tsupport (φs i) ⊆ U i) ∧ φ₀ + ∑ i, φs i = φ := by
  classical
  obtain ⟨s, ψ, hψ, hsum, -⟩ := φ.exists_sum_subordinate
    (fun i : Option t ↦ i.elim Z fun i ↦ U i) (by rintro (_ | i); exacts [hZ, hU i])
    fun x hx ↦ by
      rcases hφ hx with hx | hx
      · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hx
        exact mem_iUnion.2 ⟨some ⟨i, hi⟩, hxi⟩
      · exact mem_iUnion.2 ⟨none, hx⟩
  -- Extend the pieces by zero from `s` to all of `Option t`.
  let φs : Option t → 𝓓^{n}(Ω, F) := fun i ↦ if h : i ∈ s then ψ ⟨i, h⟩ else 0
  have hφs (i : Option t) : tsupport (φs i) ⊆ i.elim Z fun i ↦ U i := by
    by_cases h : i ∈ s
    · simpa [φs, h] using hψ ⟨i, h⟩
    · simp [φs, h]
  refine ⟨φs none, fun i ↦ φs (some i), hφs none, fun i ↦ hφs (some i),
    (Fintype.sum_option φs).symm.trans ?_⟩
  rw [← hsum, ← Finset.sum_subset (Finset.subset_univ s) fun i _ h ↦ by simp [φs, h],
    ← Finset.sum_coe_sort s]
  exact Finset.sum_congr rfl fun i _ ↦ by simp [φs]

/-- A compact subset `K` of an open set `W` contained in the domain has a test function with values
in `[0, 1]`, equal to one on a neighbourhood of `K`, whose topological support lies in `W`. -/
theorem exists_cutoff_tsupport_subset {K W : Set E} (hK : IsCompact K) (hW : IsOpen W)
    (hKW : K ⊆ W) (hWΩ : W ⊆ Ω) :
    ∃ χ : 𝓓^{n}(Ω, ℝ), (∀ x, χ x ∈ Icc 0 1) ∧ (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ tsupport χ ⊆ W := by
  obtain ⟨χ, hχ, hχ01, hχ1, hχc, hχW⟩ := hK.exists_contDiff_cutoff hW hKW
  exact ⟨⟨χ, hχ.of_le (by simp), hχc, hχW.trans hWΩ⟩, fun x ↦ hχ01 ⟨x, rfl⟩,
    subset_interior_iff_mem_nhdsSet.1 hχ1, hχW⟩

/-- A compact subset `K` of an open set `W` contained in the domain has a complex test function
equal to one on a neighbourhood of `K` whose topological support lies in `W`. -/
theorem exists_complex_cutoff_tsupport_subset {K W : Set E} (hK : IsCompact K) (hW : IsOpen W)
    (hKW : K ⊆ W) (hWΩ : W ⊆ Ω) :
    ∃ χ : 𝓓^{n}(Ω, ℂ), (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ tsupport χ ⊆ W := by
  obtain ⟨χ, -, hχ1, hχW⟩ := exists_cutoff_tsupport_subset (n := n) hK hW hKW hWΩ
  refine ⟨postcompCLM (𝕜 := ℝ) Complex.ofRealCLM χ, hχ1.mono fun x hx ↦ by simp [hx], ?_⟩
  exact (tsupport_comp_subset (g := Complex.ofRealCLM) (by simp) χ).trans hχW

/-- Every compact subset of the domain has a test function with values in `[0, 1]` that is equal
to one on a neighbourhood of it. -/
theorem exists_eventually_eq_one {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ χ : 𝓓^{n}(Ω, ℝ), (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ ∀ x, χ x ∈ Icc 0 1 := by
  obtain ⟨χ, hχ01, hχ1, -⟩ := exists_cutoff_tsupport_subset (n := n) hK Ω.isOpen hKΩ subset_rfl
  exact ⟨χ, hχ1, hχ01⟩

/-- Every point of the domain has a test function that is equal to one near it. -/
theorem exists_eventually_eq_one_nhds {x : E} (hx : x ∈ Ω) :
    ∃ χ : 𝓓^{n}(Ω, ℝ), ∀ᶠ y in 𝓝 x, χ y = 1 :=
  (exists_eventually_eq_one isCompact_singleton (singleton_subset_iff.2 hx)).imp fun _ h ↦ by
    simpa only [nhdsSet_singleton] using h.1

/-- Two test functions on `Ω` have a common cutoff test function on `Ω` equal to one on a
neighbourhood of the union of their supports. -/
theorem exists_eventually_eq_one_nhdsSet_tsupport_union (φ ψ : 𝓓^{n}(Ω, F)) :
    ∃ χ : 𝓓^{n}(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (tsupport φ ∪ tsupport ψ), χ x = 1 :=
  (exists_eventually_eq_one (φ.hasCompactSupport.isCompact.union ψ.hasCompactSupport.isCompact)
    (union_subset φ.tsupport_subset ψ.tsupport_subset)).imp fun _ h ↦ h.1

/-- Every point of the domain has a test function taking a prescribed value at it and supported
in a given neighbourhood of it. -/
theorem exists_tsupport_subset_apply_eq {x : E} {s : Set E} (hs : s ∈ 𝓝 x) (hsΩ : s ⊆ Ω)
    (v : F) : ∃ φ : 𝓓^{n}(Ω, F), tsupport φ ⊆ s ∧ φ x = v := by
  obtain ⟨u, hus, hu, hud, -, hux⟩ := exists_contDiff_tsupport_subset (n := n) hs
  have hsupp : tsupport (fun y ↦ u y • v) ⊆ s := (tsupport_smul_subset_left _ _).trans hus
  exact ⟨⟨fun y ↦ u y • v, hud.smul contDiff_const, hu.smul_right, hsupp.trans hsΩ⟩, hsupp,
    by simp [hux]⟩

/-- Every point `x` of the domain has a test function equal to one on an open neighbourhood of `x`
and supported in a given neighbourhood of `x`. -/
theorem exists_eqOn_one_tsupport_subset {𝕜 : Type*} [RCLike 𝕜] {x : E} {U : Set E}
    (hU : U ∈ 𝓝 x) (hx : x ∈ Ω) :
    ∃ χ : 𝓓^{n}(Ω, 𝕜), ∃ V, IsOpen V ∧ x ∈ V ∧ EqOn χ 1 V ∧ tsupport χ ⊆ U := by
  obtain ⟨χ, -, hχ1, hχs⟩ := exists_cutoff_tsupport_subset (n := n) (isCompact_singleton (x := x))
    (isOpen_interior.inter Ω.isOpen) (singleton_subset_iff.2 ⟨mem_interior_iff_mem_nhds.2 hU, hx⟩)
    inter_subset_right
  rw [nhdsSet_singleton] at hχ1
  obtain ⟨V, hV1, hV, hxV⟩ := eventually_nhds_iff.1 hχ1
  have hs : tsupport (fun y ↦ (χ y : 𝕜)) ⊆ tsupport χ := tsupport_comp_subset RCLike.ofReal_zero χ
  exact ⟨⟨fun y ↦ (χ y : 𝕜), (RCLike.ofRealCLM (K := 𝕜)).contDiff.comp χ.contDiff,
    χ.hasCompactSupport.comp_left RCLike.ofReal_zero, hs.trans χ.tsupport_subset⟩, V, hV, hxV,
    fun y hy ↦ (congrArg (fun r : ℝ ↦ (r : 𝕜)) (hV1 y hy)).trans RCLike.ofReal_one,
    hs.trans (hχs.trans (inter_subset_left.trans interior_subset))⟩

/-- A real test function bounded in norm by one can realize the signs of arbitrary coefficients
on a finite subset of its domain. -/
theorem exists_norm_le_one_mul_eq_abs {s : Finset E} (a : E → ℝ) (hs : (s : Set E) ⊆ Ω) :
    ∃ φ : 𝓓^{n}(Ω, ℝ), (∀ x, ‖φ x‖ ≤ 1) ∧ ∀ x ∈ s, a x * φ x = |a x| := by
  classical
  obtain ⟨χ, hχ, hχ01⟩ := exists_eventually_eq_one (n := n) s.finite_toSet.isCompact hs
  let p := s.filter fun x => 0 ≤ a x
  let q := s.filter fun x => a x < 0
  let U : Opens E := ⟨(Ω : Set E) \ (q : Set E), Ω.isOpen.sdiff q.finite_toSet.isClosed⟩
  have hpU : (p : Set E) ⊆ U := by
    intro x hx
    simp only [p, Finset.mem_coe, Finset.mem_filter] at hx
    exact ⟨hs hx.1, by simp [q, hx.1, not_lt.mpr hx.2]⟩
  obtain ⟨ψ, hψ, hψ01⟩ :=
    exists_eventually_eq_one (n := n) p.finite_toSet.isCompact hpU
  let φ : 𝓓^{n}(Ω, ℝ) :=
    ⟨fun x => χ x * (2 * ψ x - 1),
      χ.contDiff.mul ((contDiff_const.mul ψ.contDiff).sub contDiff_const),
      χ.hasCompactSupport.mul_right,
      tsupport_mul_subset_left.trans χ.tsupport_subset⟩
  refine ⟨φ, fun x => ?_, fun x hx => ?_⟩
  · have h₁ := hχ01 x
    have h₂ := hψ01 x
    rw [Real.norm_eq_abs, abs_le]
    dsimp [φ]
    constructor <;> nlinarith [h₁.1, h₁.2, h₂.1, h₂.2]
  · have hχx : χ x = 1 := hχ.self_of_nhdsSet x hx
    by_cases hxpos : 0 ≤ a x
    · have hψx : ψ x = 1 := hψ.self_of_nhdsSet x (by simp [p, hx, hxpos])
      norm_num [φ, hχx, hψx, abs_of_nonneg hxpos]
    · have hxU : x ∉ U := by simp [U, q, hx, lt_of_not_ge hxpos]
      have hψx : ψ x = 0 := ψ.zero_on_compl hxU
      simp [φ, hχx, hψx, abs_of_neg (lt_of_not_ge hxpos)]

omit [FiniteDimensional ℝ E] in
/-- Near a point where a complex test function `φ` does not vanish, every complex test function
supported close enough to the point is a `C^n` multiple of `φ`. -/
theorem exists_mem_nhds_forall_exists_contDiff_eq_mul
    {φ : 𝓓^{n}(Ω, ℂ)} {x : E} (hφx : φ x ≠ 0) :
    ∃ U ∈ 𝓝 x, ∀ ψ : 𝓓^{n}(Ω, ℂ), tsupport ψ ⊆ U →
      ∃ g : E → ℂ, ContDiff ℝ n g ∧ ∀ y, ψ y = φ y * g y := by
  -- A nonzero test function forces finite dimension.
  have : FiniteDimensional ℝ E := by
    by_contra hE
    simp [eq_zero_of_not_finiteDimensional φ hE] at hφx
  -- A cutoff `χ` equal to one near `x`, supported where `φ ≠ 0`.
  obtain ⟨χ, hχ, -, hχ1, -, hχs⟩ := (isCompact_singleton (x := x)).exists_contDiff_cutoff
    (isOpen_ne_fun φ.continuous continuous_const) (singleton_subset_iff.2 hφx)
  refine ⟨interior (χ ⁻¹' {1}), isOpen_interior.mem_nhds (hχ1 rfl), fun ψ hψ ↦ ?_⟩
  -- Write `ψ = φ (θ ψ)` with the function `θ = χ / φ`, which vanishes near the zeros of `φ`.
  let θ : E → ℂ := fun y ↦ (χ y : ℂ) * (φ y)⁻¹
  have hθ : ContDiff ℝ n θ :=
    (Complex.ofRealCLM.contDiff.comp (hχ.of_le (mod_cast le_top))).mul_inv_of_forall_notMem_tsupport
      φ.contDiff fun y hy h ↦ hχs (tsupport_comp_subset (map_zero _) χ h) hy
  refine ⟨fun y ↦ θ y * ψ y, hθ.mul ψ.contDiff, fun y ↦ ?_⟩
  by_cases hψy : ψ y = 0
  · simp [hψy]
  · have hχy : χ y = 1 := interior_subset (hψ (subset_tsupport _ hψy))
    have hφy : φ y ≠ 0 := hχs (subset_tsupport _ (by simp [hχy]))
    simp only [θ, hχy, Complex.ofReal_one]
    field_simp

/-- Near a point where a complex test function `χ` does not vanish, some test function `ρ` equal
to one near the point is a test-function multiple `h χ` of `χ`. This is how a cutoff which merely
does not vanish at a point is replaced by one equal to one near it. -/
theorem exists_eventually_eq_one_and_mul_eq {χ : 𝓓^{n}(Ω, ℂ)} {x : E}
    (hχx : χ x ≠ 0) :
    ∃ ρ h : 𝓓^{n}(Ω, ℂ), (∀ᶠ y in 𝓝 x, ρ y = 1) ∧ ∀ y, h y * χ y = ρ y := by
  have hxΩ : x ∈ Ω := χ.tsupport_subset (subset_tsupport _ hχx)
  -- Near `x`, every test function is a smooth multiple of `χ`.
  obtain ⟨U, hU, hUg⟩ := exists_mem_nhds_forall_exists_contDiff_eq_mul hχx
  -- A cutoff `ρ` equal to one near `x` and supported in `U ∩ Ω`, so `ρ = χ g` for a smooth `g`.
  obtain ⟨ρ, hρ1, hρU⟩ := exists_complex_cutoff_tsupport_subset (n := n)
    isCompact_singleton isOpen_interior
    (singleton_subset_iff.2 (mem_interior_iff_mem_nhds.2 (inter_mem hU (Ω.isOpen.mem_nhds hxΩ))))
    (interior_subset.trans inter_subset_right)
  rw [nhdsSet_singleton] at hρ1
  obtain ⟨g, hg, hρg⟩ := hUg ρ (hρU.trans (interior_subset.trans inter_subset_left))
  -- A second cutoff `ρ'` equal to one on `tsupport ρ` makes the multiplier `ρ' g` a test function.
  obtain ⟨ρ', hρ'1, -⟩ := exists_complex_cutoff_tsupport_subset (n := n)
    ρ.hasCompactSupport Ω.isOpen ρ.tsupport_subset subset_rfl
  let h : 𝓓^{n}(Ω, ℂ) := ⟨fun y ↦ ρ' y * g y, ρ'.contDiff.mul hg, ρ'.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans ρ'.tsupport_subset⟩
  refine ⟨ρ, h, hρ1, fun y ↦ ?_⟩
  by_cases hy : ρ y = 0
  · simp [h, hy, mul_assoc, mul_comm (g y), ← hρg y]
  · simp [h, (hρ'1.self_of_nhdsSet y (subset_tsupport _ hy)), mul_comm (g y), ← hρg y]

end TestFunction

namespace ContDiffMapSupportedIn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A compact set `K` in the interior of a compact set `K'` has a smooth cutoff supported in `K'`
and equal to one on `K`. In infinite dimension `K'` has empty interior (Riesz), so `K` is empty. -/
theorem exists_eqOn_one_of_subset_interior {K K' : Compacts E}
    (h : (K : Set E) ⊆ interior K') : ∃ χ : 𝓓_{K'}(E, ℂ), EqOn χ 1 K := by
  by_cases hE : FiniteDimensional ℝ E
  swap
  · exact ⟨0, fun x hx => absurd (FiniteDimensional.of_totallyBounded_nhds ℝ
      (mem_interior_iff_mem_nhds.1 (h hx)) K'.isCompact.totallyBounded) hE⟩
  obtain ⟨ψ, hψ, -, hψ1, -, hψK'⟩ := K.isCompact.exists_contDiff_cutoff isOpen_interior h
  have hsmooth : ContDiff ℝ ∞ fun x ↦ (ψ x : ℂ) := Complex.ofRealCLM.contDiff.comp hψ
  have hsupp : Function.support (fun x ↦ (ψ x : ℂ)) ⊆ K' := fun x hx ↦
    interior_subset (hψK' (subset_tsupport ψ (by simpa using hx)))
  refine ⟨.of_support_subset hsmooth hsupp, fun x hx ↦ ?_⟩
  rw [ContDiffMapSupportedIn.coe_of_support_subset, interior_subset (hψ1 hx), Pi.one_apply,
    Complex.ofReal_one]

end ContDiffMapSupportedIn

namespace AddMonoidHom

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [AddCommMonoid G] {Ω : Opens E} {n : ℕ∞}

omit [FiniteDimensional ℝ E] in
/-- An additive map on test functions vanishes if every point of the domain has an open
neighborhood on whose supported tests it vanishes. -/
theorem eq_zero_of_locally_vanishing (T : 𝓓^{n}(Ω, F) →+ G)
    (h : ∀ x ∈ Ω, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ∀ φ : 𝓓^{n}(Ω, F), tsupport φ ⊆ U → T φ = 0) : T = 0 := by
  classical
  choose U hU hxU hT using fun x : Ω ↦ h x x.property
  ext φ
  obtain ⟨s, ψ, hψ, hsum, -⟩ := φ.exists_sum_subordinate U hU fun x hx ↦
    mem_iUnion.mpr ⟨⟨x, φ.tsupport_subset hx⟩, hxU _⟩
  rw [← hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ ↦ hT i (ψ i) (hψ i)

end AddMonoidHom
