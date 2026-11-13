/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.VectorBundle.Basic
import TauCeti.Topology.Homotopy.DeformationRetract
import TauCeti.Topology.VectorBundle.Smul

/-!
# The zero section and the zeros of a section

The zero section `Bundle.zeroSection F E : B → TotalSpace F E` of a bundle whose fibres have a
zero is injective (`Bundle.zeroSection_injective`). The image of a section `s` meets the image of
the zero section exactly over the zeros of `s` (`Bundle.range_mk_inter_range_zeroSection`): two
sections of a bundle meet only over the points where they agree. No topology or linear structure
is used for these.

The total space of a topological vector bundle deformation retracts onto its zero section: the
fibrewise straight-line homotopy `(t, v) ↦ t • v` runs from `zeroSection ∘ proj` to the identity
and fixes the zero section throughout (`TauCeti.zeroSectionDeformation`). Hence the zero section
is a homotopy equivalence from the base to the total space, with homotopy inverse the projection
(`TauCeti.zeroSectionHomotopyEquiv`). The scalars may be any normed field that is a normed
`ℝ`-algebra, so complex vector bundles are included without restricting their scalars to `ℝ`.
No condition on the base is needed. Transported along a tubular neighbourhood, this is the
deformation of a neighbourhood of an embedded submanifold onto the submanifold.
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

namespace TauCeti

open Bundle

section Deformation

open scoped unitInterval ContinuousMap

variable (𝕜 : Type*) {B F : Type*} {E : B → Type*} [NontriviallyNormedField 𝕜]
  [NormedAlgebra ℝ 𝕜] [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle 𝕜 F E]

variable (F E)

/-- **A vector bundle deformation retracts onto its zero section.** The fibrewise straight-line
homotopy `(t, v) ↦ t • v` from `zeroSection ∘ proj` to the identity of the total space; it fixes
the zero section at all times. -/
def zeroSectionDeformation :
    (ContinuousMap.mk (zeroSection F E ∘ TotalSpace.proj)
      ((Trivialization.continuous_zeroSection 𝕜).comp
        (FiberBundle.continuous_proj F E))).HomotopyRel
      (ContinuousMap.id (TotalSpace F E)) (range (zeroSection F E)) where
  toFun p := TotalSpace.mk' F p.2.proj (algebraMap ℝ 𝕜 p.1 • p.2.2)
  continuous_toFun :=
    (TauCeti.VectorBundle.continuous_smul 𝕜 F E).comp
      (((algebraMapCLM ℝ 𝕜).continuous.comp (continuous_subtype_val.comp continuous_fst)).prodMk
        continuous_snd)
  map_zero_left v := by simp [zeroSection]
  map_one_left v := by simp
  prop' := by
    rintro t _ ⟨b, rfl⟩
    simp [zeroSection]

/-- At time `t` the deformation `TauCeti.zeroSectionDeformation` multiplies each vector by `t`. -/
@[simp]
theorem zeroSectionDeformation_apply (t : I) (v : TotalSpace F E) :
    zeroSectionDeformation 𝕜 F E (t, v) = TotalSpace.mk' F v.proj (algebraMap ℝ 𝕜 t • v.2) :=
  (rfl)

/-- **The zero section of a vector bundle is a homotopy equivalence**, from the base to the total
space, with homotopy inverse the projection. -/
def zeroSectionHomotopyEquiv : B ≃ₕ TotalSpace F E :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction
    ⟨zeroSection F E, Trivialization.continuous_zeroSection 𝕜⟩
    ⟨TotalSpace.proj, FiberBundle.continuous_proj F E⟩ (fun _ ↦ rfl)
    ⟨(zeroSectionDeformation 𝕜 F E).toHomotopy⟩

/-- The homotopy equivalence `TauCeti.zeroSectionHomotopyEquiv` is the zero section. -/
@[simp]
theorem zeroSectionHomotopyEquiv_apply (b : B) :
    zeroSectionHomotopyEquiv 𝕜 F E b = zeroSection F E b :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction_apply _ _ _ _ b

/-- The homotopy inverse of `TauCeti.zeroSectionHomotopyEquiv` is the projection. -/
@[simp]
theorem zeroSectionHomotopyEquiv_symm_apply (v : TotalSpace F E) :
    (zeroSectionHomotopyEquiv 𝕜 F E).symm v = v.proj :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction_symm_apply _ _ _ _ v

end Deformation

end TauCeti
