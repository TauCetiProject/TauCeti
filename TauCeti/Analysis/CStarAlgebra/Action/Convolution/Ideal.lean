/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Map
import TauCeti.Algebra.Star.Basic

/-!
# Invariant star subalgebras and ideals in twisted convolution algebras

Let `α` be a point-norm continuous action of a locally compact group `G` on a C⋆-algebra `A`, and
let `I` be a closed `α`-invariant nonunital star subalgebra of `A` equipped with the restricted
action `hI.restrict` and equivariant inclusion `hI.subtypeHom`.

* `hI.subtypeHom.convolutionMap μ` is injective and its range consists of those compactly
  supported functions taking all values in `I`;
* when `I` is a left (hence two-sided) star ideal of `A`, that range absorbs twisted convolution
  on both the left and the right.

These compact-support results require only finiteness of `μ` on compact sets; no Haar invariance,
unitality, separability, or global σ-finiteness is assumed.

## Main statements

* `IsInvariant.convolutionMap_subtypeHom_injective`: injectivity of the induced map of
  compact-support twisted convolution algebras from a closed invariant star subalgebra.
* `IsInvariant.mem_range_convolutionMap_subtypeHom_iff`: pointwise characterization of the image
  of `C_c(G, I)` inside `ConvolutionAlgebra α μ`.
* `IsInvariant.mul_mem_range_convolutionMap_subtypeHom_left` and
  `IsInvariant.mul_mem_range_convolutionMap_subtypeHom_right`: two-sided ideal absorption in the
  compact-support twisted convolution algebra.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Proposition 3.19.
-/

public section

noncomputable section

open MeasureTheory TauCeti

namespace IsInvariant

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
  [NonUnitalCStarAlgebra A] {α : CStarAction G A}
  {I : NonUnitalStarSubalgebra ℂ A} [IsClosed (I : Set A)]
  (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

/-- The induced map of compact-support twisted convolution algebras from a closed invariant star
subalgebra is injective. -/
theorem convolutionMap_subtypeHom_injective :
    Function.Injective (hI.subtypeHom.convolutionMap μ) :=
  hI.subtypeHom.convolutionMap_injective fun _ _ h => Subtype.ext (by simpa using h)

/-- An element of `ConvolutionAlgebra α μ` lies in the range of `hI.subtypeHom.convolutionMap μ`
precisely when its underlying function takes every value in `I`. -/
theorem mem_range_convolutionMap_subtypeHom_iff {f : CStarAction.ConvolutionAlgebra α μ} :
    f ∈ (hI.subtypeHom.convolutionMap μ).range ↔ ∀ s : G, f.ofConv s ∈ I := by
  rw [(hI.subtypeHom.convolutionMap μ).mem_range]
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨g, rfl⟩ s
    simpa only [CStarAction.Hom.convolutionMap_apply, subtypeHom_apply] using (g.ofConv s).2
  · have hsupp : HasCompactSupport (fun s : G => (⟨f.ofConv s, hf s⟩ : I)) := by
      have hEq : Function.support (fun s : G => (⟨f.ofConv s, hf s⟩ : I)) =
          Function.support f.ofConv := by
        ext s
        simp [Subtype.ext_iff]
      simpa only [HasCompactSupport, tsupport, hEq] using f.ofConv.hasCompactSupport
    let g : CStarAction.ConvolutionAlgebra hI.restrict μ :=
      .toConv ⟨⟨fun s => ⟨f.ofConv s, hf s⟩, (map_continuous f.ofConv).subtype_mk hf⟩, hsupp⟩
    refine ⟨g, CStarAction.ConvolutionAlgebra.ext ?_⟩
    ext s
    simp [g]

/-- Pointwise membership of the twisted convolution integrand in `I` places `f * g` in the range
of `hI.subtypeHom.convolutionMap μ`. -/
private theorem mul_mem_range_convolutionMap_subtypeHom_of_forall_mem
    {f g : CStarAction.ConvolutionAlgebra α μ}
    (hfg : ∀ r s : G, f.ofConv r * α r (g.ofConv (r⁻¹ * s)) ∈ I) :
    f * g ∈ (hI.subtypeHom.convolutionMap μ).range := by
  refine (hI.mem_range_convolutionMap_subtypeHom_iff μ).2 fun s => ?_
  let φ : G → I := fun r => ⟨f.ofConv r * α r (g.ofConv (r⁻¹ * s)), hfg r s⟩
  have hint : (∫ r, f.ofConv r * α r (g.ofConv (r⁻¹ * s)) ∂μ) = ((∫ r, φ r ∂μ : I) : A) :=
    I.toSubmodule.subtypeₗᵢ.integral_comp_comm φ
  rw [CStarAction.ConvolutionAlgebra.ofConv_mul, CStarAction.convolution_apply, hint]
  exact (∫ r, φ r ∂μ).2

/-- When `I` is a closed invariant two-sided star ideal of `A`, the range of
`hI.subtypeHom.convolutionMap μ` absorbs left twisted convolution by arbitrary elements of
`ConvolutionAlgebra α μ`. -/
theorem mul_mem_range_convolutionMap_subtypeHom_left (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I)
    (f : CStarAction.ConvolutionAlgebra α μ) {g : CStarAction.ConvolutionAlgebra α μ}
    (hg : g ∈ (hI.subtypeHom.convolutionMap μ).range) :
    f * g ∈ (hI.subtypeHom.convolutionMap μ).range := by
  have hg' := (hI.mem_range_convolutionMap_subtypeHom_iff μ).1 hg
  exact hI.mul_mem_range_convolutionMap_subtypeHom_of_forall_mem μ fun r s =>
    hmul (f.ofConv r) _ (hI.apply_mem r (hg' (r⁻¹ * s)))

/-- When `I` is a closed invariant two-sided star ideal of `A`, the range of
`hI.subtypeHom.convolutionMap μ` absorbs right twisted convolution by arbitrary elements of
`ConvolutionAlgebra α μ`. -/
theorem mul_mem_range_convolutionMap_subtypeHom_right (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I)
    {f : CStarAction.ConvolutionAlgebra α μ}
    (hf : f ∈ (hI.subtypeHom.convolutionMap μ).range)
    (g : CStarAction.ConvolutionAlgebra α μ) :
    f * g ∈ (hI.subtypeHom.convolutionMap μ).range := by
  have hf' := (hI.mem_range_convolutionMap_subtypeHom_iff μ).1 hf
  exact hI.mul_mem_range_convolutionMap_subtypeHom_of_forall_mem μ fun r _ =>
    StarMemClass.mul_mem_right_of_mul_mem_left hmul (α r (g.ofConv _)) (hf' r)

end IsInvariant
