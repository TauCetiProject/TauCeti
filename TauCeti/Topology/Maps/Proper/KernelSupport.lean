/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Support
public import TauCeti.Topology.Algebra.Support
public import TauCeti.Topology.Maps.Proper.Basic
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Properly supported binary kernels

A binary kernel `K : X → Y → M` has *proper input support* (`TauCeti.HasProperInputSupport`) if
`(x, y) ↦ x` on `tsupport (Function.uncurry K)` is proper, *proper output support*
(`TauCeti.HasProperOutputSupport`) if `(x, y) ↦ y` is proper, and *proper support*
(`TauCeti.HasProperSupport`) if both projections are proper. This matches the pseudodifferential
amplitude convention (`TauCeti.Amplitude.HasProperInputSupport`,
`TauCeti.Amplitude.HasProperOutputSupport`): when `x` is the output coordinate and `y` is the input
coordinate of an integral operator `(T_K u)(x) = ∫ y, K x y (u y) ∂μ`, proper input support keeps
`y` in a compact set for `x` in any compact set, while proper output support keeps `x` in a compact
set for `y` in any compact set.

When the projection base (`X` for proper input support, `Y` for proper output support) is weakly
locally compact and the opposite spatial factor (`Y` respectively `X`) is Hausdorff, these mean
that compact sets in the base variable force compact slices in the opposite variable
(`TauCeti.hasProperInputSupport_iff`, `TauCeti.hasProperOutputSupport_iff`).

These support conditions are stable under shrinking support, flipping arguments, addition, negation,
subtraction, and pointwise scalar multiplication on either side. In any topological additive group,
difference kernels `(x, y) ↦ φ (x - y)` of compactly supported functions are properly supported
(`TauCeti.hasProperSupport_comp_sub`), whereas nonzero constant kernels are not properly supported
when the opposite factor is noncompact and the fixed factor is nonempty
(`TauCeti.not_hasProperSupport_const`).

## Main declarations

* `TauCeti.HasProperInputSupport`, `TauCeti.HasProperOutputSupport`, `TauCeti.HasProperSupport`.
* `TauCeti.hasProperInputSupport_iff_isProperMap`,
  `TauCeti.hasProperOutputSupport_iff_isProperMap`.
* `TauCeti.hasProperInputSupport_iff`, `TauCeti.hasProperOutputSupport_iff`.
* `TauCeti.hasProperInputSupport_comp_sub`, `TauCeti.hasProperOutputSupport_comp_sub`,
  `TauCeti.hasProperSupport_comp_sub`.
* `TauCeti.not_hasProperInputSupport_const`, `TauCeti.not_hasProperOutputSupport_const`,
  `TauCeti.not_hasProperSupport_const`.
-/

public section

open Filter Function Set
open scoped Topology

namespace TauCeti

section Topological

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

section Zero

variable {M N : Type*} [Zero M] [Zero N]

/-- A binary kernel `K : X → Y → M` has **proper input support** if the first projection
`(x, y) ↦ x` restricted to `tsupport (Function.uncurry K)` is a proper map. -/
def HasProperInputSupport (K : X → Y → M) : Prop :=
  IsProperMap fun p : tsupport (uncurry K) ↦ p.val.1

/-- A binary kernel `K : X → Y → M` has **proper output support** if the second projection
`(x, y) ↦ y` restricted to `tsupport (Function.uncurry K)` is a proper map. -/
def HasProperOutputSupport (K : X → Y → M) : Prop :=
  IsProperMap fun p : tsupport (uncurry K) ↦ p.val.2

/-- A binary kernel `K : X → Y → M` is **properly supported** if both projections from
`tsupport (Function.uncurry K)` to `X` and `Y` are proper maps. -/
def HasProperSupport (K : X → Y → M) : Prop :=
  HasProperInputSupport K ∧ HasProperOutputSupport K

theorem hasProperInputSupport_iff_isProperMap {K : X → Y → M} :
    HasProperInputSupport K ↔ IsProperMap fun p : tsupport (uncurry K) ↦ p.val.1 :=
  Iff.rfl

theorem hasProperOutputSupport_iff_isProperMap {K : X → Y → M} :
    HasProperOutputSupport K ↔ IsProperMap fun p : tsupport (uncurry K) ↦ p.val.2 :=
  Iff.rfl

theorem HasProperSupport.hasProperInputSupport {K : X → Y → M} (hK : HasProperSupport K) :
    HasProperInputSupport K :=
  hK.1

theorem HasProperSupport.hasProperOutputSupport {K : X → Y → M} (hK : HasProperSupport K) :
    HasProperOutputSupport K :=
  hK.2

theorem hasProperSupport_iff {K : X → Y → M} :
    HasProperSupport K ↔ HasProperInputSupport K ∧ HasProperOutputSupport K :=
  Iff.rfl

/-- Shrinking the closed support of a kernel preserves proper input support. No separation axiom is
needed. -/
theorem HasProperInputSupport.of_tsupport_subset {K : X → Y → M} {K' : X → Y → N}
    (hK : HasProperInputSupport K) (hsub : tsupport (uncurry K') ⊆ tsupport (uncurry K)) :
    HasProperInputSupport K' :=
  hK.comp (Topology.IsClosedEmbedding.inclusion hsub
    ((isClosed_tsupport _).preimage continuous_subtypeVal)).isProperMap

/-- Flipping the two arguments of a kernel exchanges input and output proper support. -/
theorem HasProperInputSupport.flip {K : X → Y → M} (hK : HasProperInputSupport K) :
    HasProperOutputSupport (_root_.flip K) :=
  hK.comp ((Homeomorph.prodComm Y X).subtype
    fun p ↦ Set.ext_iff.mp (tsupport_uncurry_flip K) p).isProperMap

theorem HasProperOutputSupport.flip {K : X → Y → M} (hK : HasProperOutputSupport K) :
    HasProperInputSupport (_root_.flip K) :=
  hK.comp ((Homeomorph.prodComm Y X).subtype
    fun p ↦ Set.ext_iff.mp (tsupport_uncurry_flip K) p).isProperMap

@[simp]
theorem hasProperInputSupport_flip_iff {K : X → Y → M} :
    HasProperInputSupport (_root_.flip K) ↔ HasProperOutputSupport K :=
  ⟨fun h ↦ h.flip, fun h ↦ h.flip⟩

@[simp]
theorem hasProperOutputSupport_flip_iff {K : X → Y → M} :
    HasProperOutputSupport (_root_.flip K) ↔ HasProperInputSupport K :=
  ⟨fun h ↦ h.flip, fun h ↦ h.flip⟩

@[simp]
theorem hasProperSupport_flip_iff {K : X → Y → M} :
    HasProperSupport (_root_.flip K) ↔ HasProperSupport K :=
  ⟨fun h ↦ ⟨h.2.flip, h.1.flip⟩, fun h ↦ ⟨h.2.flip, h.1.flip⟩⟩

/-- Shrinking the closed support of a kernel preserves proper output support. -/
theorem HasProperOutputSupport.of_tsupport_subset {K : X → Y → M} {K' : X → Y → N}
    (hK : HasProperOutputSupport K) (hsub : tsupport (uncurry K') ⊆ tsupport (uncurry K)) :
    HasProperOutputSupport K' := by
  rw [← hasProperInputSupport_flip_iff] at hK ⊢
  exact hK.of_tsupport_subset (by simpa only [tsupport_uncurry_flip] using preimage_mono hsub)

theorem HasProperSupport.of_tsupport_subset {K : X → Y → M} {K' : X → Y → N}
    (hK : HasProperSupport K) (hsub : tsupport (uncurry K') ⊆ tsupport (uncurry K)) :
    HasProperSupport K' :=
  ⟨hK.1.of_tsupport_subset hsub, hK.2.of_tsupport_subset hsub⟩

@[simp]
theorem hasProperInputSupport_zero : HasProperInputSupport (0 : X → Y → M) := by
  rw [HasProperInputSupport, isProperMap_iff_ultrafilter]
  refine ⟨continuous_fst.comp continuous_subtypeVal, fun 𝒰 _ _ ↦ ?_⟩
  obtain ⟨p, -⟩ := 𝒰.toFilter.nonempty_of_mem univ_mem
  have h0 : tsupport (uncurry (0 : X → Y → M)) = ∅ := tsupport_zero
  exact False.elim (notMem_empty p.val (h0 ▸ p.prop))

@[simp]
theorem hasProperOutputSupport_zero : HasProperOutputSupport (0 : X → Y → M) :=
  hasProperInputSupport_flip_iff.mp hasProperInputSupport_zero

@[simp]
theorem hasProperSupport_zero : HasProperSupport (0 : X → Y → M) :=
  ⟨hasProperInputSupport_zero, hasProperOutputSupport_zero⟩

/-- If `K` has proper input support, then for every compact set `C ⊆ X` there is a compact closed
set `L ⊆ Y` outside which `K x y = 0` for all `x ∈ C`. No separation axiom is needed. -/
theorem HasProperInputSupport.exists_isCompact_isClosed_forall_eq_zero {K : X → Y → M}
    (hK : HasProperInputSupport K) {C : Set X} (hC : IsCompact C) :
    ∃ L : Set Y, IsCompact L ∧ IsClosed L ∧ ∀ x ∈ C, ∀ y ∉ L, K x y = 0 := by
  let S := tsupport (uncurry K)
  let L : Set Y := (fun p : S ↦ p.val.2) '' ((fun p : S ↦ p.val.1) ⁻¹' C)
  have hL : IsCompact L :=
    (hK.isCompact_preimage hC).image (continuous_snd.comp continuous_subtypeVal)
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hA : IsClosed {q : C × Y | (q.1.val, q.2) ∈ S} :=
    (isClosed_tsupport _).preimage
      ((continuous_subtypeVal.comp continuous_fst).prodMk continuous_snd)
  have hLc : IsClosed L := by
    have himage : L = Prod.snd '' {q : C × Y | (q.1.val, q.2) ∈ S} := by
      ext y
      simp [L, S]
    rw [himage]
    exact isClosedMap_snd_of_compactSpace _ hA
  exact ⟨L, hL, hLc, fun x hx y hy ↦
    image_eq_zero_of_notMem_tsupport (f := uncurry K) fun hmem ↦ hy ⟨⟨(x, y), hmem⟩, hx, rfl⟩⟩

/-- If `K` has proper output support, then for every compact set `L ⊆ Y` there is a compact closed
set `C ⊆ X` outside which `K x y = 0` for all `y ∈ L`. No separation axiom is needed. -/
theorem HasProperOutputSupport.exists_isCompact_isClosed_forall_eq_zero {K : X → Y → M}
    (hK : HasProperOutputSupport K) {L : Set Y} (hL : IsCompact L) :
    ∃ C : Set X, IsCompact C ∧ IsClosed C ∧ ∀ x ∉ C, ∀ y ∈ L, K x y = 0 := by
  obtain ⟨C, hC, hCc, hCK⟩ := hK.flip.exists_isCompact_isClosed_forall_eq_zero hL
  exact ⟨C, hC, hCc, fun x hx y hy ↦ hCK y hy x hx⟩

/-- If `K` has proper input support and `Y` is weakly locally compact, then every point `x₀ : X`
has an open neighborhood `U` and a compact set `L ⊆ Y` outside which `K x y = 0` for all
`x ∈ U`. -/
theorem HasProperInputSupport.exists_isOpen_isCompact_forall_eq_zero
    [WeaklyLocallyCompactSpace Y] {K : X → Y → M} (hK : HasProperInputSupport K) (x₀ : X) :
    ∃ (U : Set X) (L : Set Y), IsOpen U ∧ x₀ ∈ U ∧ IsCompact L ∧
      ∀ x ∈ U, ∀ y ∉ L, K x y = 0 := by
  let S := tsupport (uncurry K)
  have hKp := hasProperInputSupport_iff_isProperMap.mp hK
  obtain ⟨L, hL, hFL⟩ := exists_compact_superset
    ((hKp.isCompact_preimage (isCompact_singleton (x := x₀))).image
      (continuous_snd.comp continuous_subtypeVal))
  let Z : Set S := (fun p : S ↦ p.val.2) ⁻¹' (interior L)ᶜ
  have hZc : IsClosed Z :=
    isOpen_interior.isClosed_compl.preimage (continuous_snd.comp continuous_subtypeVal)
  refine ⟨((fun p : S ↦ p.val.1) '' Z)ᶜ, L, (hKp.isClosedMap Z hZc).isOpen_compl,
    fun ⟨p, hpZ, hp1⟩ ↦ hpZ (hFL ⟨p, hp1, rfl⟩), hL, fun x hxU y hyL ↦ ?_⟩
  exact image_eq_zero_of_notMem_tsupport (f := uncurry K) fun hmem ↦
    hxU ⟨⟨(x, y), hmem⟩, fun hy_int ↦ hyL (interior_subset hy_int), rfl⟩

/-- If `K` has proper output support and `X` is weakly locally compact, then every point `y₀ : Y`
has an open neighborhood `V` and a compact set `C ⊆ X` outside which `K x y = 0` for all
`y ∈ V`. -/
theorem HasProperOutputSupport.exists_isOpen_isCompact_forall_eq_zero
    [WeaklyLocallyCompactSpace X] {K : X → Y → M} (hK : HasProperOutputSupport K) (y₀ : Y) :
    ∃ (V : Set Y) (C : Set X), IsOpen V ∧ y₀ ∈ V ∧ IsCompact C ∧
      ∀ x ∉ C, ∀ y ∈ V, K x y = 0 := by
  obtain ⟨V, C, hV, hy₀V, hC, hCK⟩ := hK.flip.exists_isOpen_isCompact_forall_eq_zero y₀
  exact ⟨V, C, hV, hy₀V, hC, fun x hx y hy ↦ hCK y hy x hx⟩

namespace HasProperOutputSupport

/-- If `K` has proper output support and `u : Y → N` has compact support, there is a compact closed
set `C ⊆ X` outside which `K x y = 0` or `u y = 0` for every `y`. -/
theorem exists_isCompact_isClosed_forall_eq_zero_or_eq_zero_of_hasCompactSupport
    {K : X → Y → M} (hK : HasProperOutputSupport K) {u : Y → N} (hu : HasCompactSupport u) :
    ∃ C : Set X, IsCompact C ∧ IsClosed C ∧ ∀ x ∉ C, ∀ y, K x y = 0 ∨ u y = 0 := by
  obtain ⟨C, hC, hCc, hCK⟩ := hK.exists_isCompact_isClosed_forall_eq_zero hu
  exact ⟨C, hC, hCc, fun x hx y ↦ by_cases (fun hy : y ∈ tsupport u ↦ Or.inl (hCK x hx y hy))
    fun hy ↦ Or.inr (image_eq_zero_of_notMem_tsupport hy)⟩

end HasProperOutputSupport

namespace HasProperInputSupport

/-- If `K` has proper input support and `v : X → N` has compact support, there is a compact closed
set `L ⊆ Y` outside which `K x y = 0` or `v x = 0` for every `x`. -/
theorem exists_isCompact_isClosed_forall_eq_zero_or_eq_zero_of_hasCompactSupport
    {K : X → Y → M} (hK : HasProperInputSupport K) {v : X → N} (hv : HasCompactSupport v) :
    ∃ L : Set Y, IsCompact L ∧ IsClosed L ∧ ∀ y ∉ L, ∀ x, K x y = 0 ∨ v x = 0 :=
  hK.flip.exists_isCompact_isClosed_forall_eq_zero_or_eq_zero_of_hasCompactSupport hv

end HasProperInputSupport

/-- Characterization of proper input support when `X` is weakly locally compact and `Y` is
Hausdorff: for every compact `C ⊆ X`, `K x y` vanishes for `x ∈ C` and `y` outside some compact
`L ⊆ Y`. -/
theorem hasProperInputSupport_iff [WeaklyLocallyCompactSpace X] [T2Space Y] {K : X → Y → M} :
    HasProperInputSupport K ↔
      ∀ C : Set X, IsCompact C → ∃ L : Set Y, IsCompact L ∧ ∀ x ∈ C, ∀ y ∉ L, K x y = 0 := by
  refine ⟨fun hK _ hC ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨L, hL, -, hKL⟩ := hK.exists_isCompact_isClosed_forall_eq_zero hC
    exact ⟨L, hL, hKL⟩
  rw [HasProperInputSupport, isProperMap_iff_ultrafilter]
  refine ⟨continuous_fst.comp continuous_subtypeVal, fun 𝒰 x hx ↦ ?_⟩
  obtain ⟨C, hC, hxC⟩ := exists_compact_mem_nhds x
  obtain ⟨L, hL, hKL⟩ := h C hC
  have hdisj : tsupport (uncurry K) ⊆ (interior C ×ˢ Lᶜ)ᶜ :=
    closure_minimal (fun ⟨x', y'⟩ hxy ⟨hx', hy'⟩ ↦ hxy (hKL x' (interior_subset hx') y' hy'))
      (isOpen_interior.prod hL.isClosed.isOpen_compl).isClosed_compl
  have hL_mem : L ∈ 𝒰.map (fun p : tsupport (uncurry K) ↦ p.val.2) :=
    mem_map.2 (Filter.mem_of_superset (hx (interior_mem_nhds.2 hxC)) fun p hp ↦
      by_contra fun hyL ↦ hdisj p.prop ⟨hp, hyL⟩)
  obtain ⟨y, -, hy⟩ := hL.ultrafilter_le_nhds _ (le_principal_iff.2 hL_mem)
  have hxy : Tendsto (Subtype.val : tsupport (uncurry K) → X × Y) 𝒰 (𝓝 (x, y)) :=
    hx.prodMk_nhds hy
  exact ⟨⟨(x, y), (isClosed_tsupport _).mem_of_tendsto hxy (univ_mem' Subtype.coe_prop)⟩, rfl,
    tendsto_subtype_rng.2 hxy⟩

/-- Characterization of proper output support when `X` is Hausdorff and `Y` is weakly locally
compact: for every compact `L ⊆ Y`, `K x y` vanishes for `y ∈ L` and `x` outside some compact
`C ⊆ X`. -/
theorem hasProperOutputSupport_iff [T2Space X] [WeaklyLocallyCompactSpace Y] {K : X → Y → M} :
    HasProperOutputSupport K ↔
      ∀ L : Set Y, IsCompact L → ∃ C : Set X, IsCompact C ∧ ∀ x ∉ C, ∀ y ∈ L, K x y = 0 := by
  rw [← hasProperInputSupport_flip_iff, hasProperInputSupport_iff]
  exact forall₂_congr fun _ _ ↦ exists_congr fun _ ↦ and_congr_right fun _ ↦
    ⟨fun h x hx y hy ↦ h y hy x hx, fun h y hy x hx ↦ h x hx y hy⟩

/-- A kernel with `tsupport = univ` lacks proper input support if `X` is nonempty and `Y` is
noncompact. -/
theorem not_hasProperInputSupport_of_tsupport_eq_univ [Nonempty X] [NoncompactSpace Y]
    {K : X → Y → M} (h : tsupport (uncurry K) = univ) : ¬HasProperInputSupport K := by
  intro hK
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have hcomp : IsCompact
      ((fun p : tsupport (uncurry K) ↦ p.val.2) '' ((fun p ↦ p.val.1) ⁻¹' {x₀})) :=
    (hK.isCompact_preimage isCompact_singleton).image (continuous_snd.comp continuous_subtypeVal)
  have heq : ((fun p : tsupport (uncurry K) ↦ p.val.2) '' ((fun p ↦ p.val.1) ⁻¹' {x₀})) = univ :=
    eq_univ_iff_forall.2 fun y ↦ ⟨⟨(x₀, y), h.symm ▸ mem_univ _⟩, rfl, rfl⟩
  exact NoncompactSpace.noncompact_univ (heq ▸ hcomp)

/-- A kernel with `tsupport = univ` lacks proper output support if `X` is noncompact and `Y` is
nonempty. -/
theorem not_hasProperOutputSupport_of_tsupport_eq_univ [NoncompactSpace X] [Nonempty Y]
    {K : X → Y → M} (h : tsupport (uncurry K) = univ) : ¬HasProperOutputSupport K := by
  rw [← hasProperInputSupport_flip_iff]
  exact not_hasProperInputSupport_of_tsupport_eq_univ (by simp [tsupport_uncurry_flip, h])

theorem not_hasProperSupport_of_tsupport_eq_univ [Nonempty X] [NoncompactSpace Y]
    {K : X → Y → M} (h : tsupport (uncurry K) = univ) : ¬HasProperSupport K :=
  fun hK ↦ not_hasProperInputSupport_of_tsupport_eq_univ h hK.1

/-- A nonzero constant kernel lacks proper input support when `X` is nonempty and `Y` is
noncompact. -/
theorem not_hasProperInputSupport_const [Nonempty X] [NoncompactSpace Y] {c : M} (hc : c ≠ 0) :
    ¬HasProperInputSupport fun (_ : X) (_ : Y) ↦ c :=
  not_hasProperInputSupport_of_tsupport_eq_univ
    (by simpa [uncurry_def] using tsupport_const (Y := X × Y) hc)

/-- A nonzero constant kernel lacks proper output support when `X` is noncompact and `Y` is
nonempty. -/
theorem not_hasProperOutputSupport_const [NoncompactSpace X] [Nonempty Y] {c : M} (hc : c ≠ 0) :
    ¬HasProperOutputSupport fun (_ : X) (_ : Y) ↦ c :=
  not_hasProperOutputSupport_of_tsupport_eq_univ
    (by simpa [uncurry_def] using tsupport_const (Y := X × Y) hc)

/-- A nonzero constant kernel is not properly supported when `X` is nonempty and `Y` is
noncompact. -/
theorem not_hasProperSupport_const [Nonempty X] [NoncompactSpace Y] {c : M} (hc : c ≠ 0) :
    ¬HasProperSupport fun (_ : X) (_ : Y) ↦ c :=
  fun h ↦ not_hasProperInputSupport_const hc h.1

end Zero

/-! ### Algebraic stability -/

section Algebra

theorem HasProperInputSupport.neg {G : Type*} [NegZeroClass G] {K : X → Y → G}
    (hK : HasProperInputSupport K) : HasProperInputSupport (-K) :=
  hK.of_tsupport_subset (tsupport_comp_subset neg_zero (uncurry K))

theorem HasProperOutputSupport.neg {G : Type*} [NegZeroClass G] {K : X → Y → G}
    (hK : HasProperOutputSupport K) : HasProperOutputSupport (-K) :=
  hK.of_tsupport_subset (tsupport_comp_subset neg_zero (uncurry K))

theorem HasProperSupport.neg {G : Type*} [NegZeroClass G] {K : X → Y → G}
    (hK : HasProperSupport K) : HasProperSupport (-K) :=
  ⟨hK.1.neg, hK.2.neg⟩

theorem HasProperInputSupport.add {M : Type*} [AddZeroClass M] {K₁ K₂ : X → Y → M}
    (h₁ : HasProperInputSupport K₁) (h₂ : HasProperInputSupport K₂) :
    HasProperInputSupport (K₁ + K₂) := by
  let U : Set (X × Y) := tsupport (uncurry K₁) ∪ tsupport (uncurry K₂)
  let s₁ : Set U := ((↑) : U → X × Y) ⁻¹' tsupport (uncurry K₁)
  let s₂ : Set U := ((↑) : U → X × Y) ⁻¹' tsupport (uncurry K₂)
  have hs₁ : IsClosed s₁ := (isClosed_tsupport _).preimage continuous_subtypeVal
  have hs₂ : IsClosed s₂ := (isClosed_tsupport _).preimage continuous_subtypeVal
  have hcov : s₁ ∪ s₂ = Set.univ := by
    ext ⟨p, hp⟩
    simpa [s₁, s₂, U] using hp
  let e₁ : s₁ ≃ₜ tsupport (uncurry K₁) :=
    { toFun := fun p ↦ ⟨p.val.val, p.property⟩
      invFun := fun p ↦ ⟨⟨p.val, Or.inl p.property⟩, p.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_subtypeVal.subtypeVal.subtype_mk _
      continuous_invFun := (continuous_subtypeVal.subtype_mk _).subtype_mk _ }
  let e₂ : s₂ ≃ₜ tsupport (uncurry K₂) :=
    { toFun := fun p ↦ ⟨p.val.val, p.property⟩
      invFun := fun p ↦ ⟨⟨p.val, Or.inr p.property⟩, p.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_subtypeVal.subtypeVal.subtype_mk _
      continuous_invFun := (continuous_subtypeVal.subtype_mk _).subtype_mk _ }
  have hunion : IsProperMap fun p : U ↦ p.val.1 :=
    (IsClosed.isProperMap_iff_domRestrict_of_union_eq_univ hs₁ hs₂ hcov).2
      ⟨h₁.comp e₁.isProperMap, h₂.comp e₂.isProperMap⟩
  have hsub : tsupport (uncurry (K₁ + K₂)) ⊆ U := tsupport_add (uncurry K₁) (uncurry K₂)
  exact hunion.comp (Topology.IsClosedEmbedding.inclusion hsub
    ((isClosed_tsupport _).preimage continuous_subtypeVal)).isProperMap

theorem HasProperOutputSupport.add {M : Type*} [AddZeroClass M] {K₁ K₂ : X → Y → M}
    (h₁ : HasProperOutputSupport K₁) (h₂ : HasProperOutputSupport K₂) :
    HasProperOutputSupport (K₁ + K₂) :=
  hasProperInputSupport_flip_iff.mp (h₁.flip.add h₂.flip)

theorem HasProperSupport.add {M : Type*} [AddZeroClass M] {K₁ K₂ : X → Y → M}
    (h₁ : HasProperSupport K₁) (h₂ : HasProperSupport K₂) :
    HasProperSupport (K₁ + K₂) :=
  ⟨h₁.1.add h₂.1, h₁.2.add h₂.2⟩

theorem HasProperInputSupport.sub {G : Type*} [SubNegZeroMonoid G] {K₁ K₂ : X → Y → G}
    (h₁ : HasProperInputSupport K₁) (h₂ : HasProperInputSupport K₂) :
    HasProperInputSupport (K₁ - K₂) := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

theorem HasProperOutputSupport.sub {G : Type*} [SubNegZeroMonoid G] {K₁ K₂ : X → Y → G}
    (h₁ : HasProperOutputSupport K₁) (h₂ : HasProperOutputSupport K₂) :
    HasProperOutputSupport (K₁ - K₂) := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

theorem HasProperSupport.sub {G : Type*} [SubNegZeroMonoid G] {K₁ K₂ : X → Y → G}
    (h₁ : HasProperSupport K₁) (h₂ : HasProperSupport K₂) :
    HasProperSupport (K₁ - K₂) :=
  ⟨h₁.1.sub h₂.1, h₁.2.sub h₂.2⟩

/-- Pointwise scalar multiplication by a cutoff `χ` with proper input support on the right
preserves proper input support. -/
theorem HasProperInputSupport.smul_right {R M : Type*} [Zero R] [Zero M] [SMulWithZero R M]
    {χ : X → Y → R} (hχ : HasProperInputSupport χ) (K : X → Y → M) :
    HasProperInputSupport fun x y ↦ χ x y • K x y :=
  hχ.of_tsupport_subset (tsupport_smul_subset_left (uncurry χ) (uncurry K))

/-- Pointwise scalar multiplication by an arbitrary cutoff `χ` on the left of a kernel `K` with
proper input support preserves proper input support. -/
theorem HasProperInputSupport.smul_left {R M : Type*} [Zero M] [SMulZeroClass R M]
    (χ : X → Y → R) {K : X → Y → M} (hK : HasProperInputSupport K) :
    HasProperInputSupport fun x y ↦ χ x y • K x y :=
  hK.of_tsupport_subset (tsupport_smul_subset_right (uncurry χ) (uncurry K))

theorem HasProperOutputSupport.smul_right {R M : Type*} [Zero R] [Zero M] [SMulWithZero R M]
    {χ : X → Y → R} (hχ : HasProperOutputSupport χ) (K : X → Y → M) :
    HasProperOutputSupport fun x y ↦ χ x y • K x y :=
  hasProperInputSupport_flip_iff.mp (hχ.flip.smul_right (_root_.flip K))

theorem HasProperOutputSupport.smul_left {R M : Type*} [Zero M] [SMulZeroClass R M]
    (χ : X → Y → R) {K : X → Y → M} (hK : HasProperOutputSupport K) :
    HasProperOutputSupport fun x y ↦ χ x y • K x y :=
  hasProperInputSupport_flip_iff.mp (hK.flip.smul_left (_root_.flip χ))

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

/-! ### Difference kernels -/

section Difference

/-- In any topological additive group, composing a compactly supported profile `φ` with subtraction
`(x, y) ↦ φ (x - y)` produces a kernel with proper input support. No separation axiom is needed. -/
theorem hasProperInputSupport_comp_sub {G M : Type*} [TopologicalSpace G] [AddGroup G]
    [IsTopologicalAddGroup G] [Zero M] {φ : G → M} (hφ : HasCompactSupport φ) :
    HasProperInputSupport fun x y : G ↦ φ (x - y) := by
  let K : G → G → M := fun x y ↦ φ (x - y)
  have hsub : tsupport (uncurry K) ⊆ (fun q : G × G ↦ q.1 - q.2) ⁻¹' tsupport φ :=
    tsupport_comp_subset_preimage φ (continuous_fst.sub continuous_snd)
  let e : G × G ≃ₜ G × G :=
    ((Homeomorph.refl G).prodCongr (Homeomorph.neg G)).trans (Homeomorph.shearAddRight G)
  let f : tsupport (uncurry K) → G × tsupport φ :=
    fun p ↦ (p.val.1, ⟨p.val.1 - p.val.2, hsub p.prop⟩)
  let g : G × tsupport φ → G × G := Prod.map id Subtype.val
  have hgf : g ∘ f = e ∘ Subtype.val := by
    ext p <;> simp [g, f, e, sub_eq_add_neg]
  have hf : Topology.IsClosedEmbedding f := Topology.IsClosedEmbedding.of_comp
    (Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal)
    (hgf ▸ e.isClosedEmbedding.comp (isClosed_tsupport _).isClosedEmbedding_subtypeVal)
  have : CompactSpace (tsupport φ) := isCompact_iff_compactSpace.mp hφ
  exact (isProperMap_fst_of_compactSpace (X := G) (Y := tsupport φ)).comp hf.isProperMap

/-- In any topological additive group, `(x, y) ↦ φ (x - y)` has proper output support whenever `φ`
has compact support. -/
theorem hasProperOutputSupport_comp_sub {G M : Type*} [TopologicalSpace G] [AddGroup G]
    [IsTopologicalAddGroup G] [Zero M] {φ : G → M} (hφ : HasCompactSupport φ) :
    HasProperOutputSupport fun x y : G ↦ φ (x - y) := by
  have hneg : HasCompactSupport fun z : G ↦ φ (-z) := hφ.comp_homeomorph (Homeomorph.neg G)
  convert (hasProperInputSupport_comp_sub hneg).flip using 1
  ext x y
  simp [_root_.flip, neg_sub]

/-- In any topological additive group, `(x, y) ↦ φ (x - y)` is properly supported whenever `φ` has
compact support. -/
theorem hasProperSupport_comp_sub {G M : Type*} [TopologicalSpace G] [AddGroup G]
    [IsTopologicalAddGroup G] [Zero M] {φ : G → M} (hφ : HasCompactSupport φ) :
    HasProperSupport fun x y : G ↦ φ (x - y) :=
  ⟨hasProperInputSupport_comp_sub hφ, hasProperOutputSupport_comp_sub hφ⟩

end Difference

end TauCeti
