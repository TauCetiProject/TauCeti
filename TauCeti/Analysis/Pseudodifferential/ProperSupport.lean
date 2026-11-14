/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import TauCeti.Analysis.Calculus.ParametricIntegral

/-!
# Properly supported binary kernels

A binary kernel `K : X → Y → M` has *proper output support* (`TauCeti.HasProperOutputSupport`) if
`(x, y) ↦ x` on `tsupport (Function.uncurry K)` is proper, *proper input support*
(`TauCeti.HasProperInputSupport`) if `(x, y) ↦ y` is proper, and *proper support*
(`TauCeti.HasProperSupport`) if both projections are proper. Under weak local compactness and
Hausdorffness of the target fiber, these mean that compact sets in one variable force compact slices
in the other (`TauCeti.hasProperOutputSupport_iff`, `TauCeti.hasProperInputSupport_iff`).

For the integral operator `u ↦ (x ↦ ∫ y, K x y (u y))`:
* **Proper input support** preserves compact support
  (`TauCeti.HasProperInputSupport.hasCompactSupport_integral`) without smoothness or separation.
* **Proper output support** of a `C^n` kernel sends every continuous `u` to a `C^n` function
  (`TauCeti.HasProperOutputSupport.contDiff_integral`).
* **Transposition** (`TauCeti.HasProperOutputSupport.integral_apply_integral_eq`,
  `TauCeti.HasProperInputSupport.integral_apply_integral_eq`) swaps `T_K` with the transposed
  operator `(T_K^t v)(y) = ∫ x, (v x).comp (K x y)`.

In a topological additive group, `(x, y) ↦ φ (x - y)` is properly supported when `φ` has compact
support (`TauCeti.hasProperSupport_sub_comp`), giving smooth diagonal cutoffs on finite-dimensional
spaces (`TauCeti.exists_contDiff_hasProperSupport_eventuallyEq_one_diagonal`), whereas nonzero
constant and Gaussian kernels are not properly supported (`TauCeti.not_hasProperSupport_const`,
`TauCeti.not_hasProperSupport_exp_neg_norm_sub_sq`).

## Main declarations

* `TauCeti.HasProperOutputSupport`, `TauCeti.HasProperInputSupport`, `TauCeti.HasProperSupport`,
  `TauCeti.hasProperOutputSupport_iff`, `TauCeti.hasProperInputSupport_iff`.
* `TauCeti.hasProperSupport_sub_comp`,
  `TauCeti.exists_contDiff_hasProperSupport_eventuallyEq_one_diagonal`.
* `TauCeti.HasProperInputSupport.hasCompactSupport_integral`,
  `TauCeti.HasProperOutputSupport.contDiff_integral`,
  `TauCeti.HasProperOutputSupport.integral_apply_integral_eq`,
  `TauCeti.HasProperInputSupport.integral_apply_integral_eq`.
* `TauCeti.not_hasProperSupport_const`,
  `TauCeti.exists_hasCompactSupport_not_hasCompactSupport_integral_const`,
  `TauCeti.not_hasProperSupport_exp_neg_norm_sub_sq`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §1–§2.
-/

public section

open Filter Function MeasureTheory Set
open scoped ContDiff Topology

namespace TauCeti

section Topological

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

section Zero

variable {M N : Type*} [Zero M] [Zero N]

/-- A binary kernel `K : X → Y → M` has **proper output support** if the first projection
`(x, y) ↦ x` restricted to `tsupport (Function.uncurry K)` is a proper map. -/
def HasProperOutputSupport (K : X → Y → M) : Prop :=
  IsProperMap fun p : tsupport (uncurry K) ↦ p.1.1

/-- A binary kernel `K : X → Y → M` has **proper input support** if the second projection
`(x, y) ↦ y` restricted to `tsupport (Function.uncurry K)` is a proper map. -/
def HasProperInputSupport (K : X → Y → M) : Prop :=
  IsProperMap fun p : tsupport (uncurry K) ↦ p.1.2

/-- A binary kernel `K : X → Y → M` is **properly supported** if both projections from
`tsupport (Function.uncurry K)` to `X` and `Y` are proper maps. -/
def HasProperSupport (K : X → Y → M) : Prop :=
  HasProperOutputSupport K ∧ HasProperInputSupport K

theorem HasProperSupport.out {K : X → Y → M} (hK : HasProperSupport K) :
    HasProperOutputSupport K :=
  hK.1

theorem HasProperSupport.inp {K : X → Y → M} (hK : HasProperSupport K) :
    HasProperInputSupport K :=
  hK.2

theorem hasProperSupport_iff {K : X → Y → M} :
    HasProperSupport K ↔ HasProperOutputSupport K ∧ HasProperInputSupport K :=
  Iff.rfl

/-- Shrinking the closed support of a kernel preserves proper output support. No separation axiom is
needed. -/
theorem HasProperOutputSupport.of_tsupport_subset {K : X → Y → M} {K' : X → Y → N}
    (hK : HasProperOutputSupport K) (hsub : tsupport (uncurry K') ⊆ tsupport (uncurry K)) :
    HasProperOutputSupport K' := by
  rw [HasProperOutputSupport, isProperMap_iff_ultrafilter] at hK ⊢
  refine ⟨continuous_fst.comp continuous_subtype_val, fun 𝒰 x hx ↦ ?_⟩
  have hx' : Tendsto (fun p : tsupport (uncurry K) ↦ p.1.1) (𝒰.map (Set.inclusion hsub)) (𝓝 x) := by
    rwa [Ultrafilter.coe_map, tendsto_map'_iff]
  obtain ⟨⟨q, hq⟩, rfl, hlim⟩ := hK.2 hx'
  have hval : Tendsto (Subtype.val : tsupport (uncurry K') → X × Y) 𝒰 (𝓝 q) := by
    simpa [Ultrafilter.coe_map, tendsto_map'_iff] using
      (continuous_subtype_val.tendsto ⟨q, hq⟩).mono_left hlim
  have hq' : q ∈ tsupport (uncurry K') :=
    (isClosed_tsupport _).mem_of_tendsto hval (univ_mem' Subtype.coe_prop)
  exact ⟨⟨q, hq'⟩, rfl, tendsto_subtype_rng.2 hval⟩

private theorem tsupport_uncurry_flip (K : X → Y → M) :
    tsupport (uncurry (_root_.flip K)) = Prod.swap ⁻¹' tsupport (uncurry K) :=
  ((Homeomorph.prodComm Y X).preimage_closure (support (uncurry K))).symm

/-- Flipping the two arguments of a kernel exchanges output and input proper support. -/
theorem HasProperOutputSupport.flip {K : X → Y → M} (hK : HasProperOutputSupport K) :
    HasProperInputSupport (_root_.flip K) :=
  hK.comp ((Homeomorph.prodComm Y X).subtype
    fun p ↦ Set.ext_iff.mp (tsupport_uncurry_flip K) p).isProperMap

theorem HasProperInputSupport.flip {K : X → Y → M} (hK : HasProperInputSupport K) :
    HasProperOutputSupport (_root_.flip K) :=
  hK.comp ((Homeomorph.prodComm Y X).subtype
    fun p ↦ Set.ext_iff.mp (tsupport_uncurry_flip K) p).isProperMap

@[simp]
theorem hasProperOutputSupport_flip_iff {K : X → Y → M} :
    HasProperOutputSupport (_root_.flip K) ↔ HasProperInputSupport K :=
  ⟨fun h ↦ h.flip, fun h ↦ h.flip⟩

@[simp]
theorem hasProperInputSupport_flip_iff {K : X → Y → M} :
    HasProperInputSupport (_root_.flip K) ↔ HasProperOutputSupport K :=
  ⟨fun h ↦ h.flip, fun h ↦ h.flip⟩

@[simp]
theorem hasProperSupport_flip_iff {K : X → Y → M} :
    HasProperSupport (_root_.flip K) ↔ HasProperSupport K :=
  ⟨fun h ↦ ⟨h.2.flip, h.1.flip⟩, fun h ↦ ⟨h.2.flip, h.1.flip⟩⟩

/-- Shrinking the closed support of a kernel preserves proper input support. -/
theorem HasProperInputSupport.of_tsupport_subset {K : X → Y → M} {K' : X → Y → N}
    (hK : HasProperInputSupport K) (hsub : tsupport (uncurry K') ⊆ tsupport (uncurry K)) :
    HasProperInputSupport K' := by
  rw [← hasProperOutputSupport_flip_iff] at hK ⊢
  exact hK.of_tsupport_subset (by simpa only [tsupport_uncurry_flip] using preimage_mono hsub)

theorem HasProperSupport.of_tsupport_subset {K : X → Y → M} {K' : X → Y → N}
    (hK : HasProperSupport K) (hsub : tsupport (uncurry K') ⊆ tsupport (uncurry K)) :
    HasProperSupport K' :=
  ⟨hK.1.of_tsupport_subset hsub, hK.2.of_tsupport_subset hsub⟩

@[simp]
theorem hasProperOutputSupport_zero : HasProperOutputSupport (0 : X → Y → M) := by
  rw [HasProperOutputSupport, isProperMap_iff_ultrafilter]
  refine ⟨continuous_fst.comp continuous_subtype_val, fun 𝒰 _ _ ↦ ?_⟩
  obtain ⟨p, -⟩ := 𝒰.toFilter.nonempty_of_mem univ_mem
  have h0 : tsupport (uncurry (0 : X → Y → M)) = ∅ := tsupport_zero
  exact False.elim (notMem_empty p.1 (h0 ▸ p.prop))

@[simp]
theorem hasProperInputSupport_zero : HasProperInputSupport (0 : X → Y → M) :=
  hasProperOutputSupport_flip_iff.mp hasProperOutputSupport_zero

@[simp]
theorem hasProperSupport_zero : HasProperSupport (0 : X → Y → M) :=
  ⟨hasProperOutputSupport_zero, hasProperInputSupport_zero⟩

/-- If `K` has proper output support, then for every compact set `C ⊆ X` there is a compact closed
set `L ⊆ Y` outside which `K x y = 0` for all `x ∈ C`. No separation axiom is needed. -/
theorem HasProperOutputSupport.exists_isCompact_isClosed_forall_eq_zero {K : X → Y → M}
    (hK : HasProperOutputSupport K) {C : Set X} (hC : IsCompact C) :
    ∃ L : Set Y, IsCompact L ∧ IsClosed L ∧ ∀ x ∈ C, ∀ y ∉ L, K x y = 0 := by
  let S := tsupport (uncurry K)
  let L : Set Y := (fun p : S ↦ p.1.2) '' ((fun p : S ↦ p.1.1) ⁻¹' C)
  have hL : IsCompact L :=
    (hK.isCompact_preimage hC).image (continuous_snd.comp continuous_subtype_val)
  have hLc : IsClosed L := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y₀ hy₀
    have hsub : C ×ˢ ({y₀} : Set Y) ⊆ Sᶜ := by
      rintro ⟨x, y⟩ ⟨hx, rfl : y = y₀⟩ hmem
      exact hy₀ ⟨⟨(x, y), hmem⟩, hx, rfl⟩
    obtain ⟨U, V, _, hVo, hCU, hy₀V, hUV⟩ :=
      generalized_tube_lemma hC isCompact_singleton (isClosed_tsupport _).isOpen_compl hsub
    refine ⟨V, ?_, hVo, hy₀V rfl⟩
    rintro y hyV ⟨⟨⟨x, y'⟩, hmem⟩, hxC, rfl : y' = y⟩
    exact hUV ⟨hCU hxC, hyV⟩ hmem
  exact ⟨L, hL, hLc, fun x hx y hy ↦
    image_eq_zero_of_notMem_tsupport (f := uncurry K) fun hmem ↦ hy ⟨⟨(x, y), hmem⟩, hx, rfl⟩⟩

/-- If `K` has proper output support, then for every compact set `C ⊆ X` there is a compact set
`L ⊆ Y` outside which `K x y = 0` for all `x ∈ C`. No separation axiom is needed. -/
theorem HasProperOutputSupport.exists_isCompact_forall_eq_zero {K : X → Y → M}
    (hK : HasProperOutputSupport K) {C : Set X} (hC : IsCompact C) :
    ∃ L : Set Y, IsCompact L ∧ ∀ x ∈ C, ∀ y ∉ L, K x y = 0 := by
  obtain ⟨L, hL, -, hKL⟩ := hK.exists_isCompact_isClosed_forall_eq_zero hC
  exact ⟨L, hL, hKL⟩

/-- If `K` has proper input support, then for every compact set `L ⊆ Y` there is a compact closed
set `C ⊆ X` outside which `K x y = 0` for all `y ∈ L`. No separation axiom is needed. -/
theorem HasProperInputSupport.exists_isCompact_isClosed_forall_eq_zero {K : X → Y → M}
    (hK : HasProperInputSupport K) {L : Set Y} (hL : IsCompact L) :
    ∃ C : Set X, IsCompact C ∧ IsClosed C ∧ ∀ x ∉ C, ∀ y ∈ L, K x y = 0 := by
  obtain ⟨C, hC, hCc, hCK⟩ := hK.flip.exists_isCompact_isClosed_forall_eq_zero hL
  exact ⟨C, hC, hCc, fun x hx y hy ↦ hCK y hy x hx⟩

/-- If `K` has proper input support, then for every compact set `L ⊆ Y` there is a compact set
`C ⊆ X` outside which `K x y = 0` for all `y ∈ L`. No separation axiom is needed. -/
theorem HasProperInputSupport.exists_isCompact_forall_eq_zero {K : X → Y → M}
    (hK : HasProperInputSupport K) {L : Set Y} (hL : IsCompact L) :
    ∃ C : Set X, IsCompact C ∧ ∀ x ∉ C, ∀ y ∈ L, K x y = 0 := by
  obtain ⟨C, hC, -, hCK⟩ := hK.exists_isCompact_isClosed_forall_eq_zero hL
  exact ⟨C, hC, hCK⟩

/-- If `K` has proper input support and `u : Y → N` has compact support, there is a compact set
`C ⊆ X` outside which `K x y = 0` or `u y = 0` for every `y`. -/
theorem HasProperInputSupport.exists_isCompact_forall_eq_zero_of_hasCompactSupport
    {K : X → Y → M} (hK : HasProperInputSupport K) {u : Y → N} (hu : HasCompactSupport u) :
    ∃ C : Set X, IsCompact C ∧ ∀ x ∉ C, ∀ y, K x y = 0 ∨ u y = 0 := by
  obtain ⟨C, hC, hCK⟩ := hK.exists_isCompact_forall_eq_zero hu
  exact ⟨C, hC, fun x hx y ↦ by_cases (fun hy : y ∈ tsupport u ↦ Or.inl (hCK x hx y hy))
    fun hy ↦ Or.inr (image_eq_zero_of_notMem_tsupport hy)⟩

/-- Characterization of proper output support when `X` is weakly locally compact and `Y` is
Hausdorff: for every compact `C ⊆ X`, `K x y` vanishes for `x ∈ C` and `y` outside some compact
`L ⊆ Y`. -/
theorem hasProperOutputSupport_iff [WeaklyLocallyCompactSpace X] [T2Space Y] {K : X → Y → M} :
    HasProperOutputSupport K ↔
      ∀ C : Set X, IsCompact C → ∃ L : Set Y, IsCompact L ∧ ∀ x ∈ C, ∀ y ∉ L, K x y = 0 := by
  refine ⟨fun hK _ hC ↦ hK.exists_isCompact_forall_eq_zero hC, fun h ↦ ?_⟩
  rw [HasProperOutputSupport, isProperMap_iff_ultrafilter]
  refine ⟨continuous_fst.comp continuous_subtype_val, fun 𝒰 x hx ↦ ?_⟩
  obtain ⟨C, hC, hxC⟩ := exists_compact_mem_nhds x
  obtain ⟨L, hL, hKL⟩ := h C hC
  have hdisj : tsupport (uncurry K) ⊆ (interior C ×ˢ Lᶜ)ᶜ :=
    closure_minimal (fun ⟨x', y'⟩ hxy ⟨hx', hy'⟩ ↦ hxy (hKL x' (interior_subset hx') y' hy'))
      (isOpen_interior.prod hL.isClosed.isOpen_compl).isClosed_compl
  have hL_mem : L ∈ 𝒰.map (fun p : tsupport (uncurry K) ↦ p.1.2) :=
    mem_map.2 (Filter.mem_of_superset (hx (interior_mem_nhds.2 hxC)) fun p hp ↦
      by_contra fun hyL ↦ hdisj p.prop ⟨hp, hyL⟩)
  obtain ⟨y, -, hy⟩ := hL.ultrafilter_le_nhds _ (le_principal_iff.2 hL_mem)
  have hxy : Tendsto (Subtype.val : tsupport (uncurry K) → X × Y) 𝒰 (𝓝 (x, y)) :=
    hx.prodMk_nhds hy
  exact ⟨⟨(x, y), (isClosed_tsupport _).mem_of_tendsto hxy (univ_mem' Subtype.coe_prop)⟩, rfl,
    tendsto_subtype_rng.2 hxy⟩

/-- Characterization of proper input support when `X` is Hausdorff and `Y` is weakly locally
compact: for every compact `L ⊆ Y`, `K x y` vanishes for `y ∈ L` and `x` outside some compact
`C ⊆ X`. -/
theorem hasProperInputSupport_iff [T2Space X] [WeaklyLocallyCompactSpace Y] {K : X → Y → M} :
    HasProperInputSupport K ↔
      ∀ L : Set Y, IsCompact L → ∃ C : Set X, IsCompact C ∧ ∀ x ∉ C, ∀ y ∈ L, K x y = 0 := by
  rw [← hasProperOutputSupport_flip_iff, hasProperOutputSupport_iff]
  exact forall₂_congr fun _ _ ↦ exists_congr fun _ ↦ and_congr_right fun _ ↦
    ⟨fun h x hx y hy ↦ h y hy x hx, fun h y hy x hx ↦ h x hx y hy⟩

/-- A kernel with `tsupport = univ` lacks proper output support if `X` is nonempty and `Y` is
noncompact. -/
theorem not_hasProperOutputSupport_of_tsupport_eq_univ [Nonempty X] [NoncompactSpace Y]
    {K : X → Y → M} (h : tsupport (uncurry K) = univ) : ¬HasProperOutputSupport K := by
  intro hK
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have hcomp : IsCompact ((fun p : tsupport (uncurry K) ↦ p.1.2) '' ((fun p ↦ p.1.1) ⁻¹' {x₀})) :=
    (hK.isCompact_preimage isCompact_singleton).image (continuous_snd.comp continuous_subtype_val)
  have heq : ((fun p : tsupport (uncurry K) ↦ p.1.2) '' ((fun p ↦ p.1.1) ⁻¹' {x₀})) = univ :=
    eq_univ_iff_forall.2 fun y ↦ ⟨⟨(x₀, y), h.symm ▸ mem_univ _⟩, rfl, rfl⟩
  exact NoncompactSpace.noncompact_univ (heq ▸ hcomp)

/-- A kernel with `tsupport = univ` lacks proper input support if `X` is noncompact and `Y` is
nonempty. -/
theorem not_hasProperInputSupport_of_tsupport_eq_univ [NoncompactSpace X] [Nonempty Y]
    {K : X → Y → M} (h : tsupport (uncurry K) = univ) : ¬HasProperInputSupport K := by
  rw [← hasProperOutputSupport_flip_iff]
  exact not_hasProperOutputSupport_of_tsupport_eq_univ (by simp [tsupport_uncurry_flip, h])

theorem not_hasProperSupport_of_tsupport_eq_univ [Nonempty X] [NoncompactSpace Y]
    {K : X → Y → M} (h : tsupport (uncurry K) = univ) : ¬HasProperSupport K :=
  fun hK ↦ not_hasProperOutputSupport_of_tsupport_eq_univ h hK.1

private theorem tsupport_uncurry_const {c : M} (hc : c ≠ 0) :
    tsupport (uncurry fun (_ : X) (_ : Y) ↦ c) = univ := by
  have h : (uncurry fun (_ : X) (_ : Y) ↦ c) = fun _ : X × Y ↦ c := rfl
  rw [h, tsupport, support_const hc, closure_univ]

/-- A nonzero constant kernel lacks proper output support when `X` is nonempty and `Y` is
noncompact. -/
theorem not_hasProperOutputSupport_const [Nonempty X] [NoncompactSpace Y] {c : M} (hc : c ≠ 0) :
    ¬HasProperOutputSupport fun (_ : X) (_ : Y) ↦ c :=
  not_hasProperOutputSupport_of_tsupport_eq_univ (tsupport_uncurry_const hc)

/-- A nonzero constant kernel lacks proper input support when `X` is noncompact and `Y` is
nonempty. -/
theorem not_hasProperInputSupport_const [NoncompactSpace X] [Nonempty Y] {c : M} (hc : c ≠ 0) :
    ¬HasProperInputSupport fun (_ : X) (_ : Y) ↦ c :=
  not_hasProperInputSupport_of_tsupport_eq_univ (tsupport_uncurry_const hc)

/-- A nonzero constant kernel is not properly supported when `X` is nonempty and `Y` is
noncompact. -/
theorem not_hasProperSupport_const [Nonempty X] [NoncompactSpace Y] {c : M} (hc : c ≠ 0) :
    ¬HasProperSupport fun (_ : X) (_ : Y) ↦ c :=
  fun h ↦ not_hasProperOutputSupport_const hc h.1

end Zero

/-! ### Algebraic stability -/

section Algebra

private theorem tsupport_uncurry_neg_subset {G : Type*} [NegZeroClass G] (K : X → Y → G) :
    tsupport (uncurry (-K)) ⊆ tsupport (uncurry K) :=
  closure_mono fun ⟨x, y⟩ h ↦ mem_support.2 fun h0 ↦
    mem_support.1 h (by simp [uncurry_apply_pair, show K x y = 0 from h0])

theorem HasProperOutputSupport.neg {G : Type*} [NegZeroClass G] {K : X → Y → G}
    (hK : HasProperOutputSupport K) : HasProperOutputSupport (-K) :=
  hK.of_tsupport_subset (tsupport_uncurry_neg_subset K)

theorem HasProperInputSupport.neg {G : Type*} [NegZeroClass G] {K : X → Y → G}
    (hK : HasProperInputSupport K) : HasProperInputSupport (-K) :=
  hK.of_tsupport_subset (tsupport_uncurry_neg_subset K)

theorem HasProperSupport.neg {G : Type*} [NegZeroClass G] {K : X → Y → G}
    (hK : HasProperSupport K) : HasProperSupport (-K) :=
  ⟨hK.1.neg, hK.2.neg⟩

private theorem tendsto_of_mem_preimage_tsupport {M : Type*} [AddZeroClass M]
    {K₁ K : X → Y → M} (h₁ : HasProperOutputSupport K₁) {𝒰 : Ultrafilter (tsupport (uncurry K))}
    {x : X} (hx : Tendsto (fun p : tsupport (uncurry K) ↦ p.1.1) 𝒰 (𝓝 x))
    (hmem : ((Subtype.val : tsupport (uncurry K) → X × Y) ⁻¹' tsupport (uncurry K₁)) ∈ 𝒰) :
    ∃ p : tsupport (uncurry K), p.1.1 = x ∧ ↑𝒰 ≤ 𝓝 p := by
  rw [HasProperOutputSupport, isProperMap_iff_ultrafilter] at h₁
  let S₁ : Set (tsupport (uncurry K)) := Subtype.val ⁻¹' tsupport (uncurry K₁)
  have hrange : range (Subtype.val : S₁ → tsupport (uncurry K)) ∈ 𝒰 := by rwa [Subtype.range_coe]
  let i : S₁ → tsupport (uncurry K₁) := fun p ↦ ⟨p.1.1, p.2⟩
  have hi_tendsto : Tendsto (fun p : tsupport (uncurry K₁) ↦ p.1.1)
      ((𝒰.comap Subtype.val_injective hrange).map i) (𝓝 x) := by
    rw [Ultrafilter.coe_map, Ultrafilter.coe_comap, tendsto_map'_iff]
    exact (tendsto_comap'_iff hrange).2 hx
  obtain ⟨⟨q, hq⟩, rfl, hlim⟩ := h₁.2 hi_tendsto
  have h' : Tendsto ((Subtype.val : tsupport (uncurry K) → X × Y) ∘
      (Subtype.val : S₁ → tsupport (uncurry K)))
      (comap (Subtype.val : S₁ → tsupport (uncurry K)) 𝒰) (𝓝 q) := by
    have h0 := (continuous_subtype_val.tendsto ⟨q, hq⟩).mono_left hlim
    rwa [Ultrafilter.coe_map, Ultrafilter.coe_comap, tendsto_map'_iff] at h0
  have hval : Tendsto (Subtype.val : tsupport (uncurry K) → X × Y) 𝒰 (𝓝 q) :=
    (tendsto_comap'_iff hrange).1 h'
  exact ⟨⟨q, (isClosed_tsupport _).mem_of_tendsto hval (univ_mem' Subtype.coe_prop)⟩, rfl,
    tendsto_subtype_rng.2 hval⟩

theorem HasProperOutputSupport.add {M : Type*} [AddZeroClass M] {K₁ K₂ : X → Y → M}
    (h₁ : HasProperOutputSupport K₁) (h₂ : HasProperOutputSupport K₂) :
    HasProperOutputSupport (K₁ + K₂) := by
  rw [HasProperOutputSupport, isProperMap_iff_ultrafilter]
  refine ⟨continuous_fst.comp continuous_subtype_val, fun 𝒰 x hx ↦ ?_⟩
  have hunion : tsupport (uncurry (K₁ + K₂)) ⊆ tsupport (uncurry K₁) ∪ tsupport (uncurry K₂) :=
    tsupport_add (uncurry K₁) (uncurry K₂)
  have hor : ((Subtype.val : tsupport (uncurry (K₁ + K₂)) → X × Y) ⁻¹' tsupport (uncurry K₁)) ∈ 𝒰 ∨
      ((Subtype.val : tsupport (uncurry (K₁ + K₂)) → X × Y) ⁻¹' tsupport (uncurry K₂)) ∈ 𝒰 := by
    rw [← Ultrafilter.union_mem_iff, ← preimage_union]
    exact univ_mem' fun p ↦ hunion p.prop
  exact hor.elim (tendsto_of_mem_preimage_tsupport h₁ hx) (tendsto_of_mem_preimage_tsupport h₂ hx)

theorem HasProperInputSupport.add {M : Type*} [AddZeroClass M] {K₁ K₂ : X → Y → M}
    (h₁ : HasProperInputSupport K₁) (h₂ : HasProperInputSupport K₂) :
    HasProperInputSupport (K₁ + K₂) :=
  hasProperOutputSupport_flip_iff.mp (h₁.flip.add h₂.flip)

theorem HasProperSupport.add {M : Type*} [AddZeroClass M] {K₁ K₂ : X → Y → M}
    (h₁ : HasProperSupport K₁) (h₂ : HasProperSupport K₂) :
    HasProperSupport (K₁ + K₂) :=
  ⟨h₁.1.add h₂.1, h₁.2.add h₂.2⟩

theorem HasProperOutputSupport.sub {G : Type*} [SubNegZeroMonoid G] {K₁ K₂ : X → Y → G}
    (h₁ : HasProperOutputSupport K₁) (h₂ : HasProperOutputSupport K₂) :
    HasProperOutputSupport (K₁ - K₂) := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

theorem HasProperInputSupport.sub {G : Type*} [SubNegZeroMonoid G] {K₁ K₂ : X → Y → G}
    (h₁ : HasProperInputSupport K₁) (h₂ : HasProperInputSupport K₂) :
    HasProperInputSupport (K₁ - K₂) := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

theorem HasProperSupport.sub {G : Type*} [SubNegZeroMonoid G] {K₁ K₂ : X → Y → G}
    (h₁ : HasProperSupport K₁) (h₂ : HasProperSupport K₂) :
    HasProperSupport (K₁ - K₂) :=
  ⟨h₁.1.sub h₂.1, h₁.2.sub h₂.2⟩

/-- Pointwise scalar multiplication by an arbitrary factor on the right of a properly
output-supported cutoff `χ` preserves proper output support. -/
theorem HasProperOutputSupport.smul_right {R M : Type*} [Zero R] [Zero M] [SMulWithZero R M]
    {χ : X → Y → R} (hχ : HasProperOutputSupport χ) (K : X → Y → M) :
    HasProperOutputSupport fun x y ↦ χ x y • K x y :=
  hχ.of_tsupport_subset (closure_mono fun ⟨x, y⟩ h ↦
    mem_support.2 fun h0 ↦ mem_support.1 h
      (by simp only [uncurry_apply_pair] at h0 ⊢; rw [h0, zero_smul]))

/-- Pointwise scalar multiplication by an arbitrary cutoff `χ` on the left of a properly
output-supported kernel `K` preserves proper output support. -/
theorem HasProperOutputSupport.smul_left {R M : Type*} [Zero M] [SMulZeroClass R M]
    (χ : X → Y → R) {K : X → Y → M} (hK : HasProperOutputSupport K) :
    HasProperOutputSupport fun x y ↦ χ x y • K x y :=
  hK.of_tsupport_subset (closure_mono fun ⟨x, y⟩ h ↦
    mem_support.2 fun h0 ↦ mem_support.1 h
      (by simp only [uncurry_apply_pair] at h0 ⊢; rw [h0, smul_zero]))

theorem HasProperInputSupport.smul_right {R M : Type*} [Zero R] [Zero M] [SMulWithZero R M]
    {χ : X → Y → R} (hχ : HasProperInputSupport χ) (K : X → Y → M) :
    HasProperInputSupport fun x y ↦ χ x y • K x y :=
  hasProperOutputSupport_flip_iff.mp (hχ.flip.smul_right (_root_.flip K))

theorem HasProperInputSupport.smul_left {R M : Type*} [Zero M] [SMulZeroClass R M]
    (χ : X → Y → R) {K : X → Y → M} (hK : HasProperInputSupport K) :
    HasProperInputSupport fun x y ↦ χ x y • K x y :=
  hasProperOutputSupport_flip_iff.mp (hK.flip.smul_left (_root_.flip χ))

theorem HasProperSupport.smul_right {R M : Type*} [Zero R] [Zero M] [SMulWithZero R M]
    {χ : X → Y → R} (hχ : HasProperSupport χ) (K : X → Y → M) :
    HasProperSupport fun x y ↦ χ x y • K x y :=
  ⟨hχ.1.smul_right K, hχ.2.smul_right K⟩

theorem HasProperSupport.smul_left {R M : Type*} [Zero M] [SMulZeroClass R M]
    (χ : X → Y → R) {K : X → Y → M} (hK : HasProperSupport K) :
    HasProperSupport fun x y ↦ χ x y • K x y :=
  ⟨hK.1.smul_left χ, hK.2.smul_left χ⟩

end Algebra

end Topological

/-! ### Difference kernels and smooth diagonal cutoffs -/

section Difference

/-- In any topological additive group, composing a compactly supported profile `φ` with subtraction
`(x, y) ↦ φ (x - y)` produces a kernel with proper output support. No separation axiom is needed. -/
theorem hasProperOutputSupport_sub_comp {G M : Type*} [TopologicalSpace G] [AddGroup G]
    [IsTopologicalAddGroup G] [Zero M] {φ : G → M} (hφ : HasCompactSupport φ) :
    HasProperOutputSupport fun x y : G ↦ φ (x - y) := by
  set K : G → G → M := fun x y ↦ φ (x - y)
  have hsub : tsupport (uncurry K) ⊆ {q : G × G | q.1 - q.2 ∈ tsupport φ} :=
    closure_minimal (fun q hq ↦ subset_tsupport φ hq)
      ((isClosed_tsupport φ).preimage (continuous_fst.sub continuous_snd))
  rw [HasProperOutputSupport, isProperMap_iff_ultrafilter]
  refine ⟨continuous_fst.comp continuous_subtype_val, fun 𝒰 x₀ hx₀ ↦ ?_⟩
  obtain ⟨z, -, hz⟩ := hφ.ultrafilter_le_nhds (𝒰.map fun p : tsupport (uncurry K) ↦ p.1.1 - p.1.2)
    (le_principal_iff.2 <| mem_map.2 <| univ_mem' fun p : tsupport (uncurry K) ↦ hsub p.prop)
  have hdiff : Tendsto (fun p : tsupport (uncurry K) ↦ p.1.1 - p.1.2) 𝒰 (𝓝 z) := hz
  have hy : Tendsto (fun p : tsupport (uncurry K) ↦ p.1.2) 𝒰 (𝓝 (-z + x₀)) :=
    (hdiff.neg.add hx₀).congr fun p ↦ by rw [neg_sub, sub_add_cancel]
  have hxy : Tendsto (Subtype.val : tsupport (uncurry K) → G × G) 𝒰 (𝓝 (x₀, -z + x₀)) :=
    hx₀.prodMk_nhds hy
  exact ⟨⟨(x₀, -z + x₀), (isClosed_tsupport _).mem_of_tendsto hxy (univ_mem' Subtype.coe_prop)⟩,
    rfl, tendsto_subtype_rng.2 hxy⟩

/-- In any topological additive group, `(x, y) ↦ φ (x - y)` has proper input support whenever `φ`
has compact support. -/
theorem hasProperInputSupport_sub_comp {G M : Type*} [TopologicalSpace G] [AddGroup G]
    [IsTopologicalAddGroup G] [Zero M] {φ : G → M} (hφ : HasCompactSupport φ) :
    HasProperInputSupport fun x y : G ↦ φ (x - y) := by
  have hneg : HasCompactSupport fun z : G ↦ φ (-z) := hφ.comp_homeomorph (Homeomorph.neg G)
  convert (hasProperOutputSupport_sub_comp hneg).flip using 1
  ext x y
  simp [_root_.flip, neg_sub]

/-- In any topological additive group, `(x, y) ↦ φ (x - y)` is properly supported whenever `φ` has
compact support. -/
theorem hasProperSupport_sub_comp {G M : Type*} [TopologicalSpace G] [AddGroup G]
    [IsTopologicalAddGroup G] [Zero M] {φ : G → M} (hφ : HasCompactSupport φ) :
    HasProperSupport fun x y : G ↦ φ (x - y) :=
  ⟨hasProperOutputSupport_sub_comp hφ, hasProperInputSupport_sub_comp hφ⟩

/-- Every finite-dimensional real normed space admits a smooth `[0, 1]`-valued properly supported
cutoff equal to `1` when `‖x - y‖ ≤ r` (hence on a neighborhood of every diagonal point `(x, x)`)
and vanishing when `‖x - y‖ ≥ R`, whenever `0 < R` and `r < R`. -/
theorem exists_contDiff_hasProperSupport_eventuallyEq_one_diagonal {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {r R : ℝ}
    (hR : 0 < R) (hrR : r < R) :
    ∃ χ : E → E → ℝ, ContDiff ℝ ∞ (uncurry χ) ∧ range (uncurry χ) ⊆ Icc 0 1 ∧
      HasProperSupport χ ∧ (∀ x : E, uncurry χ =ᶠ[𝓝 (x, x)] 1) ∧
      (∀ x y : E, ‖x - y‖ ≤ r → χ x y = 1) ∧ ∀ x y : E, R ≤ ‖x - y‖ → χ x y = 0 := by
  set r' := max r (R / 2)
  have hr' : 0 < r' := (half_pos hR).trans_le (le_max_right r (R / 2))
  let b : ContDiffBump (0 : E) := ⟨r', R, hr', max_lt hrR (half_lt_self hR)⟩
  have hone : ∀ x y : E, ‖x - y‖ ≤ r → b (x - y) = 1 := fun x y hxy ↦
    b.one_of_mem_closedBall
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hxy.trans (le_max_left r _))
  refine ⟨fun x y ↦ b (x - y), (b.contDiff (n := ⊤)).comp (contDiff_fst.sub contDiff_snd),
    range_subset_iff.2 fun p ↦ ⟨b.nonneg' _, b.le_one⟩,
    hasProperSupport_sub_comp b.hasCompactSupport, fun x ↦ ?_, hone,
    fun x y hxy ↦ b.zero_of_le_dist (by simpa [dist_eq_norm] using hxy)⟩
  have hsub : Tendsto (fun p : E × E ↦ p.1 - p.2) (𝓝 (x, x)) (𝓝 (x - x)) :=
    (continuous_fst.sub continuous_snd).tendsto (x, x)
  rw [sub_self] at hsub
  filter_upwards [hsub (Metric.closedBall_mem_nhds 0 hr')] with p hp
  exact b.one_of_mem_closedBall hp

end Difference

/-! ### Smooth integral operators and transposition -/

section IntegralOperator

private theorem hasCompactSupport_of_isCompact_isClosed {Z α : Type*} [TopologicalSpace Z]
    [Zero α] {s : Set Z} (hs : IsCompact s) (hsc : IsClosed s) {f : Z → α}
    (hf : ∀ z ∉ s, f z = 0) : HasCompactSupport f :=
  hs.of_isClosed_subset (isClosed_tsupport f)
    (closure_minimal (fun z hz ↦ by_contra fun hzs ↦ mem_support.1 hz (hf z hzs)) hsc)

/-- **Proper input support preserves compact support.** For any binary operator kernel
`K : X → Y → V →L[𝕜] W` with proper input support, the integral operator
`u ↦ (x ↦ ∫ y, K x y (u y) ∂μ)` maps compactly supported functions to compactly supported
functions. No smoothness or separation axiom is needed. -/
theorem HasProperInputSupport.hasCompactSupport_integral {X Y 𝕜 V W : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace Y] [Semiring 𝕜] [AddCommMonoid V]
    [Module 𝕜 V] [TopologicalSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W] [Module 𝕜 W]
    {K : X → Y → V →L[𝕜] W} (hK : HasProperInputSupport K) {u : Y → V}
    (hu : HasCompactSupport u) (μ : Measure Y := by volume_tac) :
    HasCompactSupport fun x ↦ ∫ y, K x y (u y) ∂μ := by
  obtain ⟨C, hC, hCc, hCK⟩ := hK.exists_isCompact_isClosed_forall_eq_zero hu
  refine hasCompactSupport_of_isCompact_isClosed hC hCc fun x hx ↦ ?_
  have hzero : (fun y ↦ K x y (u y)) = 0 := funext fun y ↦ by
    by_cases hy : y ∈ tsupport u
    · simp [hCK x hx y hy]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  simp [hzero]

private theorem exists_open_isCompact_forall_eq_zero {X Y M : Type*} [TopologicalSpace X]
    [NormedAddCommGroup Y] [TopologicalSpace M] [Zero M] [T1Space M]
    {K : X → Y → M} (hK : HasProperOutputSupport K) (hKc : Continuous (uncurry K))
    {x₁ : X} {y₁ : Y} (hne : K x₁ y₁ ≠ 0) (x₀ : X) :
    ∃ (U : Set X) (L : Set Y), IsOpen U ∧ x₀ ∈ U ∧ IsCompact L ∧
      ∀ x ∈ U, ∀ y ∉ L, K x y = 0 := by
  obtain ⟨L₁, hL₁, hL₁c, hKL₁⟩ :=
    hK.exists_isCompact_isClosed_forall_eq_zero (isCompact_singleton (x := x₁))
  have hc₁ : HasCompactSupport fun y ↦ K x₁ y :=
    hasCompactSupport_of_isCompact_isClosed hL₁ hL₁c fun y hy ↦ hKL₁ x₁ rfl y hy
  have hcont₁ : Continuous fun y ↦ K x₁ y := hKc.comp (continuous_const.prodMk continuous_id)
  have : LocallyCompactSpace Y :=
    (hc₁.eq_zero_or_locallyCompactSpace_of_addGroup hcont₁).resolve_left
      fun h0 ↦ hne (congrFun h0 y₁)
  let S := tsupport (uncurry K)
  obtain ⟨L, hL, hFL⟩ := exists_compact_superset
    ((hK.isCompact_preimage (isCompact_singleton (x := x₀))).image
      (continuous_snd.comp continuous_subtype_val))
  let Z : Set S := (fun p : S ↦ p.1.2) ⁻¹' (interior L)ᶜ
  have hZc : IsClosed Z :=
    isOpen_interior.isClosed_compl.preimage (continuous_snd.comp continuous_subtype_val)
  refine ⟨((fun p : S ↦ p.1.1) '' Z)ᶜ, L, (hK.isClosedMap Z hZc).isOpen_compl,
    fun ⟨p, hpZ, hp1⟩ ↦ hpZ (hFL ⟨p, hp1, rfl⟩), hL, fun x hxU y hyL ↦ ?_⟩
  exact image_eq_zero_of_notMem_tsupport (f := uncurry K) fun hmem ↦
    hxU ⟨⟨(x, y), hmem⟩, fun hy_int ↦ hyL (interior_subset hy_int), rfl⟩

/-- **Proper output support gives smoothness on arbitrary continuous inputs.** If `K` is `C^n` on
`X × Y` and has proper output support, where `μ` is finite on compact subsets of `Y`, then
`x ↦ ∫ y, K x y (u y) ∂μ` is `C^n` for every continuous `u : Y → V` (with no support assumption on
`u` and no finite-dimensionality assumption on `X` or `Y`). -/
theorem HasProperOutputSupport.contDiff_integral {X Y 𝕜 V W : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V] [IsScalarTower ℝ 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W]
    {n : ℕ∞} {K : X → Y → V →L[𝕜] W} (hK : HasProperOutputSupport K)
    (hK_diff : ContDiff ℝ n (uncurry K)) {u : Y → V} (hu : Continuous u)
    (μ : Measure Y := by volume_tac) [IsFiniteMeasureOnCompacts μ] :
    ContDiff ℝ n fun x ↦ ∫ y, K x y (u y) ∂μ := by
  by_cases hne : ∃ x₁ y₁, K x₁ y₁ ≠ 0
  · obtain ⟨x₁, y₁, hne⟩ := hne
    refine contDiff_iff_contDiffAt.2 fun x₀ ↦ ?_
    obtain ⟨U, L, hUo, hx₀U, hL, hKL⟩ :=
      exists_open_isCompact_forall_eq_zero hK hK_diff.continuous hne x₀
    have : CompactSpace L := isCompact_iff_compactSpace.mp hL
    have hmeasL : MeasurableSet L := hL.isClosed.measurableSet
    let μL : Measure L := μ.comap Subtype.val
    have : IsFiniteMeasure μL := ⟨by
      rw [(MeasurableEmbedding.subtype_coe hmeasL).comap_apply, image_univ, Subtype.range_coe]
      exact hL.measure_lt_top⟩
    have hF : ContDiff ℝ n fun q : X × (Y × V) ↦ (K q.1 q.2.1) q.2.2 :=
      ((ContinuousLinearMap.restrictScalarsL 𝕜 V W ℝ ℝ).contDiff.comp
        (hK_diff.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)))).clm_apply
          (contDiff_snd.comp contDiff_snd)
    have hon := contDiffOn_integral_smul_of_contDiffOn (μ := μL) (g := fun _ : L ↦ (1 : ℝ))
      (ι := fun y : L ↦ (y.1, u y.1)) (W := univ) (U := U)
      (integrable_const 1) (continuous_subtype_val.prodMk (hu.comp continuous_subtype_val))
      isOpen_univ hF.contDiffOn (fun _ _ _ ↦ mem_univ _)
    refine (hon.contDiffAt (hUo.mem_nhds hx₀U)).congr_of_eventuallyEq ?_
    filter_upwards [hUo.mem_nhds hx₀U] with x hx
    simp only [one_smul]
    rw [integral_subtype_comap hmeasL (fun y ↦ K x y (u y)),
      setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by simp [hKL x hx y hy]]
  · push Not at hne
    have h0 : (fun x ↦ ∫ y, K x y (u y) ∂μ) = 0 := funext fun x ↦ by simp [hne x]
    exact h0 ▸ contDiff_const

/-- When `K` has proper output support and `v : X → W →L[𝕜] M` has compact support, the transposed
operator `y ↦ ∫ x, (v x).comp (K x y) ∂μ` has compact support. -/
theorem HasProperOutputSupport.hasCompactSupport_integral_comp {X Y 𝕜 V W M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [TopologicalSpace Y] [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W]
    [NormedSpace 𝕜 W] [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedSpace 𝕜 M]
    [IsScalarTower ℝ 𝕜 M] {K : X → Y → V →L[𝕜] W} (hK : HasProperOutputSupport K)
    {v : X → W →L[𝕜] M} (hv : HasCompactSupport v) (μ : Measure X := by volume_tac) :
    HasCompactSupport fun y ↦ ∫ x, (v x).comp (K x y) ∂μ := by
  let K' : Y → X → (W →L[𝕜] M) →L[𝕜] (V →L[𝕜] M) :=
    fun y x ↦ (ContinuousLinearMap.compL 𝕜 V W M).flip (K x y)
  have hK' : HasProperInputSupport K' :=
    hK.flip.of_tsupport_subset <| closure_mono fun ⟨y, x⟩ hxy ↦
      mem_support.2 fun h0 ↦ mem_support.1 hxy
        (by simp [K', uncurry_apply_pair, show K x y = 0 from h0])
  exact hK'.hasCompactSupport_integral hv μ

private theorem integral_apply_integral_eq_restrict {X Y 𝕜 W M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W]
    [CompleteSpace W] [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedSpace 𝕜 M]
    [IsScalarTower ℝ 𝕜 M] [CompleteSpace M]
    {F : X → Y → W} {v : X → W →L[𝕜] M} (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasureOnCompacts ν] {C : Set X} {L : Set Y}
    (hCc : IsClosed C) (hL : IsCompact L) (hLc : IsClosed L) (hF_cont : ∀ x ∈ C, Continuous (F x))
    (hx_out : ∀ x ∉ C, v x = 0 ∨ ∀ y, F x y = 0) (hy_in : ∀ x ∈ C, ∀ y ∉ L, F x y = 0) :
    (∫ x, v x (∫ y, F x y ∂ν) ∂μ) = ∫ x in C, ∫ y in L, v x (F x y) ∂ν ∂μ := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
    (hx_out x hx).elim (fun hv0 ↦ by simp [hv0]) fun hF0 ↦ by simp [hF0]]
  refine integral_congr_ae ((ae_restrict_mem hCc.measurableSet).mono fun x hx ↦ ?_)
  dsimp only
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (hy_in x hx)]
  exact (((v x).restrictScalars ℝ).integral_comp_comm <|
    (hF_cont x hx).integrable_of_hasCompactSupport
      (hasCompactSupport_of_isCompact_isClosed hL hLc (hy_in x hx))).symm

private theorem integral_apply_integral_eq_of_isCompact_isClosed {X Y 𝕜 V W M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [SecondCountableTopologyEither X Y] [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W] [CompleteSpace W]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedSpace 𝕜 M] [IsScalarTower ℝ 𝕜 M]
    {K : X → Y → V →L[𝕜] W} (hKc : Continuous (uncurry K)) {u : Y → V} (hu : Continuous u)
    {v : X → W →L[𝕜] M} (hv : Continuous v) (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] {C : Set X} {L : Set Y}
    (hC : IsCompact C) (hCc : IsClosed C) (hL : IsCompact L) (hLc : IsClosed L)
    (hx_out : ∀ x ∉ C, v x = 0 ∨ ∀ y, K x y (u y) = 0)
    (hy_in : ∀ x ∈ C, ∀ y ∉ L, K x y (u y) = 0)
    (hy_out : ∀ y ∉ L, u y = 0 ∨ ∀ x, (v x).comp (K x y) = 0)
    (hx_in : ∀ y ∈ L, ∀ x ∉ C, (v x).comp (K x y) = 0) :
    (∫ x, v x (∫ y, K x y (u y) ∂ν) ∂μ) = ∫ y, (∫ x, (v x).comp (K x y) ∂μ) (u y) ∂ν := by
  by_cases hM : CompleteSpace M; swap
  · simp [integral_of_not_completeSpace hM]
  set μ' := μ.restrict C
  set ν' := ν.restrict L
  have : IsFiniteMeasure μ' := ⟨by simp [μ', hC.measure_lt_top]⟩
  have : IsFiniteMeasure ν' := ⟨by simp [ν', hL.measure_lt_top]⟩
  have hcont_comp : Continuous fun p : X × Y ↦ (v p.1).comp (K p.1 p.2) :=
    ((ContinuousLinearMap.compL 𝕜 V W M).continuous.comp (hv.comp continuous_fst)).clm_apply hKc
  have hint_prod : Integrable (fun p : X × Y ↦ v p.1 (K p.1 p.2 (u p.2))) (μ'.prod ν') :=
    (hcont_comp.clm_apply (hu.comp continuous_snd)).integrable_of_hasCompactSupport
      (hasCompactSupport_of_isCompact_isClosed (hC.prod hL) (hCc.prod hLc) fun ⟨x, y⟩ hxy ↦ by
        by_cases hx : x ∈ C
        · simp [hy_in x hx y fun hy ↦ hxy ⟨hx, hy⟩]
        · exact (hx_out x hx).elim (fun hv0 ↦ by simp [hv0]) fun hK0 ↦ by simp [hK0])
  have hLHS := integral_apply_integral_eq_restrict (F := fun x y ↦ K x y (u y)) (v := v)
    μ ν hCc hL hLc (fun x _ ↦ (hKc.comp (continuous_const.prodMk continuous_id)).clm_apply hu)
    hx_out hy_in
  have hRHS := integral_apply_integral_eq_restrict (F := fun y x ↦ (v x).comp (K x y))
    (v := fun y ↦ ContinuousLinearMap.apply 𝕜 M (u y)) ν μ hLc hC hCc
    (fun y _ ↦ hcont_comp.comp (continuous_id.prodMk continuous_const))
    (fun y hy ↦ (hy_out y hy).imp (fun hu0 ↦ by ext; simp [hu0]) id) hx_in
  exact hLHS.trans ((integral_integral_swap hint_prod).trans hRHS.symm)

/-- **Transposition identity under proper output support.** If `K` is continuous with proper output
support and `v : X → W →L[𝕜] M` is continuous with compact support, then for *every* continuous
input `u : Y → V` (with no support assumption on `u`), pairing `(T_K u)(x)` with `v(x)` equals
pairing `u(y)` with the transposed operator `(T_K^t v)(y) = ∫ x, (v x).comp (K x y) ∂μ`. -/
theorem HasProperOutputSupport.integral_apply_integral_eq {X Y 𝕜 V W M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [SecondCountableTopologyEither X Y] [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W] [CompleteSpace W]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedSpace 𝕜 M] [IsScalarTower ℝ 𝕜 M]
    {K : X → Y → V →L[𝕜] W} (hK : HasProperOutputSupport K) (hKc : Continuous (uncurry K))
    {u : Y → V} (hu : Continuous u) {v : X → W →L[𝕜] M} (hv : Continuous v)
    (hvc : HasCompactSupport v) (μ : Measure X := by volume_tac)
    (ν : Measure Y := by volume_tac) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] :
    (∫ x, v x (∫ y, K x y (u y) ∂ν) ∂μ) = ∫ y, (∫ x, (v x).comp (K x y) ∂μ) (u y) ∂ν := by
  obtain ⟨L, hL, hLc, hKL⟩ := hK.exists_isCompact_isClosed_forall_eq_zero hvc
  exact integral_apply_integral_eq_of_isCompact_isClosed hKc hu hv μ ν hvc (isClosed_tsupport v)
    hL hLc (fun x hx ↦ Or.inl (image_eq_zero_of_notMem_tsupport hx))
    (fun x hx y hy ↦ by simp [hKL x hx y hy])
    (fun y hy ↦ Or.inr fun x ↦ by
      by_cases hx : x ∈ tsupport v
      · simp [hKL x hx y hy]
      · simp [image_eq_zero_of_notMem_tsupport hx])
    (fun _ _ x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx])

/-- **Transposition identity under proper input support.** Symmetrically, if `K` is continuous with
proper input support and `u : Y → V` is continuous with compact support, then the transposition
identity holds for *every* continuous `v : X → W →L[𝕜] M`. -/
theorem HasProperInputSupport.integral_apply_integral_eq {X Y 𝕜 V W M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [SecondCountableTopologyEither X Y] [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W] [CompleteSpace W]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedSpace 𝕜 M] [IsScalarTower ℝ 𝕜 M]
    {K : X → Y → V →L[𝕜] W} (hK : HasProperInputSupport K) (hKc : Continuous (uncurry K))
    {u : Y → V} (hu : Continuous u) (huc : HasCompactSupport u)
    {v : X → W →L[𝕜] M} (hv : Continuous v) (μ : Measure X := by volume_tac)
    (ν : Measure Y := by volume_tac) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] :
    (∫ x, v x (∫ y, K x y (u y) ∂ν) ∂μ) = ∫ y, (∫ x, (v x).comp (K x y) ∂μ) (u y) ∂ν := by
  obtain ⟨C, hC, hCc, hCK⟩ := hK.exists_isCompact_isClosed_forall_eq_zero huc
  exact integral_apply_integral_eq_of_isCompact_isClosed hKc hu hv μ ν hC hCc
    huc (isClosed_tsupport u)
    (fun x hx ↦ Or.inr fun y ↦ by
      by_cases hy : y ∈ tsupport u
      · simp [hCK x hx y hy]
      · simp [image_eq_zero_of_notMem_tsupport hy])
    (fun _ _ y hy ↦ by simp [image_eq_zero_of_notMem_tsupport hy])
    (fun y hy ↦ Or.inl (image_eq_zero_of_notMem_tsupport hy))
    (fun y hy x hx ↦ by simp [hCK x hx y hy])

end IntegralOperator

/-! ### Constant and Gaussian non-examples -/

section Examples

/-- On any nontrivial finite-dimensional real normed space equipped with an open-positive measure
that is finite on compacts, the constant identity kernel `(x, y) ↦ id` is smooth, sends `u` to the
constant `∫ u ∂μ`, and fails to preserve compact support: there is a smooth compactly supported `u`
whose output is a nonzero constant, hence not compactly supported. -/
theorem exists_hasCompactSupport_not_hasCompactSupport_integral_const {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [OpensMeasurableSpace E] (μ : Measure E := by volume_tac)
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ (∫ y, u y ∂μ) ≠ 0 ∧
      ¬HasCompactSupport fun _ : E ↦ ∫ y, (ContinuousLinearMap.id ℝ ℝ) (u y) ∂μ := by
  let b : ContDiffBump (0 : E) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have hint : Integrable b μ := b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
  have hpos : (∫ y : E, b y ∂μ) ≠ 0 :=
    ((integral_pos_iff_support_of_nonneg b.nonneg' hint).mpr
      (b.support_eq.symm ▸ Metric.measure_ball_pos μ 0 b.rOut_pos)).ne'
  refine ⟨b, b.contDiff, b.hasCompactSupport, hpos, fun hc ↦ ?_⟩
  simp only [ContinuousLinearMap.id_apply, HasCompactSupport] at hc
  rw [tsupport, support_const hpos, closure_univ] at hc
  exact NoncompactSpace.noncompact_univ hc

private theorem tsupport_exp_neg_norm_sub_sq {E : Type*} [SeminormedAddCommGroup E] :
    tsupport (uncurry fun x y : E ↦ Real.exp (-‖x - y‖ ^ 2)) = univ := by
  have h : (uncurry fun x y : E ↦ Real.exp (-‖x - y‖ ^ 2)) =
      fun p : E × E ↦ Real.exp (-‖p.1 - p.2‖ ^ 2) := rfl
  rw [h, tsupport, eq_univ_iff_forall.2 fun p ↦ mem_support.2 (Real.exp_ne_zero _), closure_univ]

/-- On any nonempty noncompact seminormed additive group (in particular any nontrivial real normed
space), the Gaussian kernel `(x, y) ↦ exp (-‖x - y‖²)` does not have proper output support. -/
theorem not_hasProperOutputSupport_exp_neg_norm_sub_sq {E : Type*} [SeminormedAddCommGroup E]
    [Nonempty E] [NoncompactSpace E] :
    ¬HasProperOutputSupport fun x y : E ↦ Real.exp (-‖x - y‖ ^ 2) :=
  not_hasProperOutputSupport_of_tsupport_eq_univ tsupport_exp_neg_norm_sub_sq

/-- On any nonempty noncompact seminormed additive group (in particular any nontrivial real normed
space), the Gaussian kernel `(x, y) ↦ exp (-‖x - y‖²)` does not have proper input support. -/
theorem not_hasProperInputSupport_exp_neg_norm_sub_sq {E : Type*} [SeminormedAddCommGroup E]
    [Nonempty E] [NoncompactSpace E] :
    ¬HasProperInputSupport fun x y : E ↦ Real.exp (-‖x - y‖ ^ 2) :=
  not_hasProperInputSupport_of_tsupport_eq_univ tsupport_exp_neg_norm_sub_sq

/-- On any nonempty noncompact seminormed additive group (in particular any nontrivial real normed
space), the Gaussian kernel `(x, y) ↦ exp (-‖x - y‖²)` is not properly supported, despite its rapid
off-diagonal decay. -/
theorem not_hasProperSupport_exp_neg_norm_sub_sq {E : Type*} [SeminormedAddCommGroup E]
    [Nonempty E] [NoncompactSpace E] :
    ¬HasProperSupport fun x y : E ↦ Real.exp (-‖x - y‖ ^ 2) :=
  not_hasProperSupport_of_tsupport_eq_univ tsupport_exp_neg_norm_sub_sq

end Examples

end TauCeti
