/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Maps on one-point compactifications

The extension `OnePoint.map f` sends infinity, and only infinity, to infinity. Its range is the
range of `f`, embedded in the target compactification, together with infinity, and it is injective
exactly when `f` is injective; it is an involution when `f` is. For a proper map between
arbitrary topological spaces, this extension is continuous. Closed embeddings extend to closed
embeddings. Conversely, a homeomorphism `Ψ : OnePoint X ≃ₜ OnePoint Y` sending `∞` to `∞` restricts
to a homeomorphism `Ψ.ofOnePoint : X ≃ₜ Y` whose `onePointCongr` recovers `Ψ`. These lemmas allow
proper parametrizations and compactified homeomorphisms to pass cleanly between spaces and their
one-point compactifications.
-/

public section

open Set Topology

namespace Homeomorph

/-- Restrict a homeomorphism `Ψ : OnePoint X ≃ₜ OnePoint Y` sending `∞` to `∞` to a homeomorphism
`X ≃ₜ Y` of the finite parts. -/
noncomputable def ofOnePoint {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (Ψ : OnePoint X ≃ₜ OnePoint Y) (hΨ : Ψ OnePoint.infty = OnePoint.infty) : X ≃ₜ Y :=
  let ιX : X ≃ₜ range ((↑) : X → OnePoint X) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph
  let ιY : Y ≃ₜ range ((↑) : Y → OnePoint Y) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph
  let Ψ₀ : range ((↑) : X → OnePoint X) ≃ₜ range ((↑) : Y → OnePoint Y) :=
    Ψ.subtype fun z ↦ by
      simp only [mem_range, ← OnePoint.ne_infty_iff_exists]
      exact ⟨fun hz h ↦ hz (Ψ.injective (h.trans hΨ.symm)), fun hz h ↦ hz (h ▸ hΨ)⟩
  ιX.trans (Ψ₀.trans ιY.symm)

/-- Embedding `Ψ.ofOnePoint hΨ x` into `OnePoint Y` recovers `Ψ x`. -/
@[simp]
theorem coe_ofOnePoint_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (Ψ : OnePoint X ≃ₜ OnePoint Y) (hΨ : Ψ OnePoint.infty = OnePoint.infty) (x : X) :
    ((Ψ.ofOnePoint hΨ x : Y) : OnePoint Y) = Ψ x := by
  let ιY : Y ≃ₜ range ((↑) : Y → OnePoint Y) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph
  have hι : ∀ z : range ((↑) : Y → OnePoint Y), ((ιY.symm z : Y) : OnePoint Y) = z :=
    fun z ↦ congrArg Subtype.val (ιY.apply_symm_apply z)
  exact hι _

/-- Extending `Ψ.ofOnePoint hΨ` back to one-point compactifications recovers `Ψ`. -/
@[simp]
theorem onePointCongr_ofOnePoint {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (Ψ : OnePoint X ≃ₜ OnePoint Y) (hΨ : Ψ OnePoint.infty = OnePoint.infty) :
    (Ψ.ofOnePoint hΨ).onePointCongr = Ψ := by
  ext z
  induction z using OnePoint.rec with
  | infty => exact hΨ.symm
  | coe x => exact Ψ.coe_ofOnePoint_apply hΨ x

/-- Restricting `e.onePointCongr` to the finite parts recovers `e`. -/
@[simp]
theorem ofOnePoint_onePointCongr {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (he : e.onePointCongr OnePoint.infty = OnePoint.infty) :
    e.onePointCongr.ofOnePoint he = e := by
  ext x
  exact OnePoint.coe_injective (e.onePointCongr.coe_ofOnePoint_apply he x)

/-- Restricting the inverse of `Ψ` gives the inverse of `Ψ.ofOnePoint hΨ`. -/
@[simp]
theorem symm_ofOnePoint {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (Ψ : OnePoint X ≃ₜ OnePoint Y) (hΨ : Ψ OnePoint.infty = OnePoint.infty) :
    (Ψ.ofOnePoint hΨ).symm = Ψ.symm.ofOnePoint (Ψ.symm_apply_eq.2 hΨ.symm) := by
  ext y
  apply OnePoint.coe_injective
  rw [Ψ.symm.coe_ofOnePoint_apply, eq_comm, Ψ.symm_apply_eq, ← Ψ.coe_ofOnePoint_apply hΨ,
    Homeomorph.apply_symm_apply]

end Homeomorph

namespace TauCeti

/-- Extension to one-point compactifications preserves and reflects injectivity. -/
@[simp]
theorem onePointMap_injective_iff {X Y : Type*} {f : X → Y} :
    Function.Injective (OnePoint.map f) ↔ Function.Injective f := by
  constructor
  · intro hf x y h
    apply OnePoint.coe_injective
    apply hf
    simpa only [OnePoint.map_some] using congrArg OnePoint.some h
  · intro hf
    -- `OnePoint.map` is implemented by `Option.map`, so its injectivity theorem applies.
    exact Option.map_injective hf

/-- Extension to one-point compactifications preserves involutions. -/
theorem onePointMap_involutive {X : Type*} {f : X → X} (hf : Function.Involutive f) :
    Function.Involutive (OnePoint.map f) := by
  intro x
  induction x using OnePoint.rec <;> simp [hf _]

/-- The range of the extension to one-point compactifications is the embedded range together
with the point at infinity. -/
@[simp]
theorem range_onePointMap {X Y : Type*} (f : X → Y) :
    range (OnePoint.map f) = insert OnePoint.infty (((↑) : Y → OnePoint Y) '' range f) := by
  -- `Option.range_eq` splits the domain into infinity and the finite points.
  exact (Option.range_eq (OnePoint.map f)).trans
    (congrArg (insert OnePoint.infty) (range_comp ((↑) : Y → OnePoint Y) f))

/-- Infinity is the only point that the extension to one-point compactifications sends to
infinity. -/
@[simp]
theorem preimage_onePointMap_infty {X Y : Type*} (f : X → Y) :
    OnePoint.map f ⁻¹' {OnePoint.infty} = {OnePoint.infty} := by
  ext x
  induction x using OnePoint.rec <;> simp

/-- A proper map between arbitrary topological spaces extends continuously
to the one-point compactifications, sending infinity to infinity. -/
theorem continuous_onePointMap_of_isProperMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsProperMap f) : Continuous (OnePoint.map f) :=
  OnePoint.continuous_map hf.continuous (by
    refine Filter.hasBasis_coclosedCompact.tendsto_right_iff.mpr ?_
    intro K hK
    exact (hf.isCompact_preimage hK.2).compl_mem_coclosedCompact_of_isClosed
      (hK.1.preimage hf.continuous))

/-- A closed embedding between arbitrary topological spaces extends to a closed embedding
of their one-point compactifications. -/
theorem isClosedEmbedding_onePointMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Topology.IsClosedEmbedding f) :
    Topology.IsClosedEmbedding (OnePoint.map f) := by
  refine .of_continuous_injective_isClosedMap
    (continuous_onePointMap_of_isProperMap hf.isProperMap)
    (onePointMap_injective_iff.mpr hf.injective) ?_
  intro s hs
  have hpre : ((↑) : Y → OnePoint Y) ⁻¹' (OnePoint.map f '' s) =
      f '' (((↑) : X → OnePoint X) ⁻¹' s) := by
    ext y
    simp [mem_image, OnePoint.exists]
  by_cases hinfty : OnePoint.infty ∈ s
  · apply (OnePoint.isClosed_iff_of_mem
      (by simpa [mem_image, OnePoint.exists] using hinfty)).mpr
    rw [hpre]
    exact hf.isClosedMap _ (hs.preimage OnePoint.continuous_coe)
  · apply (OnePoint.isClosed_iff_of_notMem
      (by simpa [mem_image, OnePoint.exists] using hinfty)).mpr
    rw [hpre]
    exact ⟨hf.isClosedMap _ (hs.preimage OnePoint.continuous_coe),
      ((OnePoint.isClosed_iff_of_notMem hinfty).mp hs).2.image hf.continuous⟩

end TauCeti
