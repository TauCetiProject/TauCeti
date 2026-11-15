/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# The zero section and the zeros of a section

The zero section `Bundle.zeroSection F E : B → TotalSpace F E` of a bundle whose fibres have a
zero is injective (`Bundle.zeroSection_injective`). The image of a section `s` meets the image of
the zero section exactly over the zeros of `s` (`Bundle.range_mk_inter_range_zeroSection`): two
sections of a bundle meet only over the points where they agree. No topology or linear structure
is used for these.

The nonzero vectors form the complement `TauCeti.zeroSectionCompl` of the image of the zero section
(`TauCeti.zeroSectionCompl_eq_compl_range`). In a real topological vector bundle they form an open
subset of the total space (`TauCeti.isOpen_zeroSectionCompl`): in a local trivialization, a vector
is nonzero exactly when its coordinate in the model fibre is.
-/

public section

open Set

namespace Bundle

variable {B F : Type*} {E : B → Type*} [∀ x, Zero (E x)]

variable (F E) in
/-- The zero section of a bundle is injective, since the projection is a left inverse of it. -/
theorem zeroSection_injective : Function.Injective (zeroSection F E) :=
  Function.LeftInverse.injective (g := TotalSpace.proj) fun _ ↦ rfl

/-- **A section meets the zero section over its zeros.** The image of a section `s` of a bundle
meets the image of the zero section exactly in the zero vectors over the points where `s`
vanishes. -/
theorem range_mk_inter_range_zeroSection (s : ∀ x, E x) :
    range (fun x ↦ TotalSpace.mk' F x (s x)) ∩ range (zeroSection F E) =
      zeroSection F E '' {x | s x = 0} := by
  ext v
  simp only [mem_inter_iff, mem_range, mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨x, rfl⟩, y, hy⟩
    -- Both sections pass through `v`, so they lie over the same point and agree there.
    obtain rfl : y = x := congrArg TotalSpace.proj hy
    exact ⟨y, (TotalSpace.mk_inj.mp hy).symm, hy⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, by rw [zeroSection, hx]⟩, x, rfl⟩

end Bundle

open Bundle

namespace TauCeti

section Compl

variable {B : Type*} (F : Type*) (E : B → Type*) [∀ b, Zero (E b)]

/-- The complement `E₀` of the zero section in the total space of a bundle: its nonzero
vectors. -/
def zeroSectionCompl : Set (TotalSpace F E) :=
  {v | v.2 ≠ 0}

variable {F E} in
@[simp]
theorem mem_zeroSectionCompl {v : TotalSpace F E} : v ∈ zeroSectionCompl F E ↔ v.2 ≠ 0 :=
  Iff.rfl

/-- The nonzero vectors are the complement of the range of the zero section. -/
theorem zeroSectionCompl_eq_compl_range :
    zeroSectionCompl F E = (range (zeroSection F E))ᶜ := by
  ext ⟨b, x⟩
  simp only [mem_zeroSectionCompl, mem_compl_iff, mem_range, not_exists]
  constructor
  · rintro hx b' h
    cases h
    exact hx rfl
  · intro h hx
    exact h b (by rw [hx]; rfl)

end Compl

section Open

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

variable (F E) in
/-- The nonzero vectors of a real vector bundle form an open set. -/
theorem isOpen_zeroSectionCompl : IsOpen (zeroSectionCompl F E) := by
  refine isOpen_iff_forall_mem_open.2 fun v hv ↦ ?_
  let e := trivializationAt F E v.proj
  -- Over the base set of `e`, a vector is nonzero exactly when its coordinate in `F` is.
  have key (w : TotalSpace F E) (hw : w ∈ e.source) : (e w).2 ≠ 0 ↔ w.2 ≠ 0 := by
    rw [← e.continuousLinearEquivAt_apply' (R := ℝ) w hw]
    exact map_ne_zero_iff _ (e.continuousLinearEquivAt ℝ _ _).injective
  refine ⟨e.source ∩ e ⁻¹' (univ ×ˢ {0}ᶜ), fun w ⟨hw, hw'⟩ ↦
    mem_zeroSectionCompl.2 ((key w hw).1 hw'.2),
    e.continuousOn.isOpen_inter_preimage e.open_source (isOpen_univ.prod isOpen_compl_singleton),
    FiberBundle.mem_trivializationAt_proj_source,
    mem_univ _, (key v FiberBundle.mem_trivializationAt_proj_source).2 (mem_zeroSectionCompl.1 hv)⟩

end Open

end TauCeti
