/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Topology.Maps.Proper.Basic
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Properly supported binary kernels

A binary kernel `K : X → Y → M` has *proper output support* (`TauCeti.HasProperOutputSupport`) if
`(x, y) ↦ x` on `tsupport (Function.uncurry K)` is proper, *proper input support*
(`TauCeti.HasProperInputSupport`) if `(x, y) ↦ y` is proper, and *proper support*
(`TauCeti.HasProperSupport`) if both projections are proper. Under weak local compactness and
Hausdorffness of the target fiber, these mean that compact sets in one variable force compact slices
in the other (`TauCeti.hasProperOutputSupport_iff`, `TauCeti.hasProperInputSupport_iff`).

These support conditions are stable under shrinking support, flipping arguments, addition, negation,
subtraction, and pointwise scalar multiplication on either side. In any topological additive group,
difference kernels `(x, y) ↦ φ (x - y)` of compactly supported functions are properly supported
(`TauCeti.hasProperSupport_comp_sub`), whereas nonzero constant kernels are not properly supported
when the opposite factor is noncompact and the fixed factor is nonempty
(`TauCeti.not_hasProperSupport_const`).

## Main declarations

* `TauCeti.HasProperOutputSupport`, `TauCeti.HasProperInputSupport`, `TauCeti.HasProperSupport`.
* `TauCeti.hasProperOutputSupport_iff_isProperMap`,
  `TauCeti.hasProperInputSupport_iff_isProperMap`.
* `TauCeti.hasProperOutputSupport_iff`, `TauCeti.hasProperInputSupport_iff`.
* `TauCeti.hasProperOutputSupport_comp_sub`, `TauCeti.hasProperInputSupport_comp_sub`,
  `TauCeti.hasProperSupport_comp_sub`.
* `TauCeti.not_hasProperOutputSupport_const`, `TauCeti.not_hasProperInputSupport_const`,
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

/-- A binary kernel `K : X → Y → M` has **proper output support** if the first projection
`(x, y) ↦ x` restricted to `tsupport (Function.uncurry K)` is a proper map. -/
def HasProperOutputSupport (K : X → Y → M) : Prop :=
  IsProperMap fun p : tsupport (uncurry K) ↦ p.val.1

/-- A binary kernel `K : X → Y → M` has **proper input support** if the second projection
`(x, y) ↦ y` restricted to `tsupport (Function.uncurry K)` is a proper map. -/
def HasProperInputSupport (K : X → Y → M) : Prop :=
  IsProperMap fun p : tsupport (uncurry K) ↦ p.val.2

/-- A binary kernel `K : X → Y → M` is **properly supported** if both projections from
`tsupport (Function.uncurry K)` to `X` and `Y` are proper maps. -/
def HasProperSupport (K : X → Y → M) : Prop :=
  HasProperOutputSupport K ∧ HasProperInputSupport K

theorem hasProperOutputSupport_iff_isProperMap {K : X → Y → M} :
    HasProperOutputSupport K ↔ IsProperMap fun p : tsupport (uncurry K) ↦ p.val.1 :=
  Iff.rfl

theorem hasProperInputSupport_iff_isProperMap {K : X → Y → M} :
    HasProperInputSupport K ↔ IsProperMap fun p : tsupport (uncurry K) ↦ p.val.2 :=
  Iff.rfl

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
    HasProperOutputSupport K' :=
  hK.comp (Topology.IsClosedEmbedding.inclusion hsub
    ((isClosed_tsupport _).preimage continuous_subtypeVal)).isProperMap

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
  refine ⟨continuous_fst.comp continuous_subtypeVal, fun 𝒰 _ _ ↦ ?_⟩
  obtain ⟨p, -⟩ := 𝒰.toFilter.nonempty_of_mem univ_mem
  have h0 : tsupport (uncurry (0 : X → Y → M)) = ∅ := tsupport_zero
  exact False.elim (notMem_empty p.val (h0 ▸ p.prop))

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
  have hcomp : IsCompact
      ((fun p : tsupport (uncurry K) ↦ p.val.2) '' ((fun p ↦ p.val.1) ⁻¹' {x₀})) :=
    (hK.isCompact_preimage isCompact_singleton).image (continuous_snd.comp continuous_subtypeVal)
  have heq : ((fun p : tsupport (uncurry K) ↦ p.val.2) '' ((fun p ↦ p.val.1) ⁻¹' {x₀})) = univ :=
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

theorem HasProperOutputSupport.neg {G : Type*} [NegZeroClass G] {K : X → Y → G}
    (hK : HasProperOutputSupport K) : HasProperOutputSupport (-K) :=
  hK.of_tsupport_subset (tsupport_comp_subset neg_zero (uncurry K))

theorem HasProperInputSupport.neg {G : Type*} [NegZeroClass G] {K : X → Y → G}
    (hK : HasProperInputSupport K) : HasProperInputSupport (-K) :=
  hK.of_tsupport_subset (tsupport_comp_subset neg_zero (uncurry K))

theorem HasProperSupport.neg {G : Type*} [NegZeroClass G] {K : X → Y → G}
    (hK : HasProperSupport K) : HasProperSupport (-K) :=
  ⟨hK.1.neg, hK.2.neg⟩

theorem HasProperOutputSupport.add {M : Type*} [AddZeroClass M] {K₁ K₂ : X → Y → M}
    (h₁ : HasProperOutputSupport K₁) (h₂ : HasProperOutputSupport K₂) :
    HasProperOutputSupport (K₁ + K₂) := by
  have hunion : IsProperMap fun p : ↥(tsupport (uncurry K₁) ∪ tsupport (uncurry K₂)) ↦ p.val.1 :=
    continuous_fst.isProperMap_restrict_union h₁ h₂
  have hsub : tsupport (uncurry (K₁ + K₂)) ⊆ tsupport (uncurry K₁) ∪ tsupport (uncurry K₂) :=
    tsupport_add (uncurry K₁) (uncurry K₂)
  exact hunion.comp (Topology.IsClosedEmbedding.inclusion hsub
    ((isClosed_tsupport _).preimage continuous_subtypeVal)).isProperMap

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
  hχ.of_tsupport_subset (tsupport_smul_subset_left (uncurry χ) (uncurry K))

/-- Pointwise scalar multiplication by an arbitrary cutoff `χ` on the left of a properly
output-supported kernel `K` preserves proper output support. -/
theorem HasProperOutputSupport.smul_left {R M : Type*} [Zero M] [SMulZeroClass R M]
    (χ : X → Y → R) {K : X → Y → M} (hK : HasProperOutputSupport K) :
    HasProperOutputSupport fun x y ↦ χ x y • K x y :=
  hK.of_tsupport_subset (tsupport_smul_subset_right (uncurry χ) (uncurry K))

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

/-! ### Difference kernels -/

section Difference

/-- In any topological additive group, composing a compactly supported profile `φ` with subtraction
`(x, y) ↦ φ (x - y)` produces a kernel with proper output support. No separation axiom is needed. -/
theorem hasProperOutputSupport_comp_sub {G M : Type*} [TopologicalSpace G] [AddGroup G]
    [IsTopologicalAddGroup G] [Zero M] {φ : G → M} (hφ : HasCompactSupport φ) :
    HasProperOutputSupport fun x y : G ↦ φ (x - y) := by
  let K : G → G → M := fun x y ↦ φ (x - y)
  have hsub : tsupport (uncurry K) ⊆ {q : G × G | q.1 - q.2 ∈ tsupport φ} :=
    closure_minimal (fun q hq ↦ subset_tsupport φ hq)
      ((isClosed_tsupport φ).preimage (continuous_fst.sub continuous_snd))
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

/-- In any topological additive group, `(x, y) ↦ φ (x - y)` has proper input support whenever `φ`
has compact support. -/
theorem hasProperInputSupport_comp_sub {G M : Type*} [TopologicalSpace G] [AddGroup G]
    [IsTopologicalAddGroup G] [Zero M] {φ : G → M} (hφ : HasCompactSupport φ) :
    HasProperInputSupport fun x y : G ↦ φ (x - y) := by
  have hneg : HasCompactSupport fun z : G ↦ φ (-z) := hφ.comp_homeomorph (Homeomorph.neg G)
  convert (hasProperOutputSupport_comp_sub hneg).flip using 1
  ext x y
  simp [_root_.flip, neg_sub]

/-- In any topological additive group, `(x, y) ↦ φ (x - y)` is properly supported whenever `φ` has
compact support. -/
theorem hasProperSupport_comp_sub {G M : Type*} [TopologicalSpace G] [AddGroup G]
    [IsTopologicalAddGroup G] [Zero M] {φ : G → M} (hφ : HasCompactSupport φ) :
    HasProperSupport fun x y : G ↦ φ (x - y) :=
  ⟨hasProperOutputSupport_comp_sub hφ, hasProperInputSupport_comp_sub hφ⟩

end Difference

end TauCeti
