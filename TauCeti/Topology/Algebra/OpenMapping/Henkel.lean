/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.OpenMapping.Complete
public import Mathlib.Topology.Maps.Strict.Module
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.Topology.Baire.CompleteMetrizable
import TauCeti.Topology.Algebra.Module.Submodule

/-!
# Henkel's open mapping theorem

A surjective equivariant additive map, continuous at zero, from a complete first-countable uniform
additive group (with scalar action continuous in the scalar at zero) to a `T₀` Baire topological
additive group with continuous constant scalar actions is open, provided the scalars carry a zero
sequence of units. This file assembles that statement from the pieces built around it.

Each hypothesis pays for one step and no other.

* The zero sequence of units and the Baire property give
  `TauCeti.HasZeroSequenceOfUnits.closure_image_mem_nhds_zero`: the *closure* of the image of a
  neighbourhood of zero is a neighbourhood of zero. Supplying that closure step is the only use
  the Baire hypothesis is put to here; whether a weaker hypothesis would do is not addressed.
* Countable generation of `𝓝 0` produces a shrinking sequence of neighbourhoods of zero with
  `V (n + 1) + V (n + 1) ⊆ V n` along which the approximation can run.
* Completeness removes the closure, in `TauCeti.mem_image_of_mem_closure_image_of_add_subset`.

The last two steps do not depend on how the closure step was obtained, and are packaged as
`TauCeti.isOpenMap_of_closure_image_mem_nhds`; this file feeds the Baire step into it. No
nonarchimedean, locally convex, or normed hypothesis is required: the theorem covers Fréchet
spaces, F-spaces, Banach spaces, and complete first-countable modules over Tate rings alike.

## Main results

* `TauCeti.HasZeroSequenceOfUnits.isOpenMap`: Henkel's open mapping theorem.
* `TauCeti.HasZeroSequenceOfUnits.isQuotientMap`: the surjective map in `isOpenMap` induces the
  quotient topology on its target, so the target's topology is determined by the source's.
* `LinearMap.isStrictMap_of_baireSpace_range_of_hasZeroSequenceOfUnits` and
  `LinearMap.isStrictMap_of_isClosed_range_of_hasZeroSequenceOfUnits`: over a semiring with a
  zero sequence of units, linear maps from a complete first-countable uniform additive module
  whose range is `T₀` and Baire (for instance, closed range in a completely metrisable target) are
  strict, assuming continuity at zero for the map and for the scalar action on the source, and
  continuity of each fixed scalar action on the target.

The range equivalence `ContinuousLinearMap.equivRangeOfIsStrictMap` for injective strict maps
lives in `TauCeti.Topology.Maps.Strict.Module`. The other two implications of Wedhorn's
Theorem 6.16, that an open linear map is surjective and that a continuous one has a complete
target, are in `TauCeti.Topology.Algebra.OpenMapping.Converse`.

Mathlib's `MonoidHom.isOpenMap_of_sigmaCompact` proves openness for a continuous surjection from
a σ-compact source onto a T2 Baire target group (locally compact groups being the standard
example of such a target). Neither theorem implies the other: both ask the target to be Baire,
but this one asks the *source* to be complete and first countable over scalars with a zero sequence
of units, where that one asks it to be σ-compact, and neither of those conditions implies the other.

## References

* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  [arXiv:1407.5647](https://arxiv.org/abs/1407.5647).
* T. Wedhorn, *Adic Spaces*, Theorem 6.16.
-/

public section

open Filter Topology

namespace TauCeti

variable {A M N : Type*} [MonoidWithZero A] [TopologicalSpace A] [HasZeroSequenceOfUnits A]
  [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
  [(𝓝 (0 : M)).IsCountablyGenerated] [MulActionWithZero A M]
  [AddGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N] [T0Space N] [BaireSpace N]
  [MulAction A N] [ContinuousConstSMul A N]

/-- **Henkel's open mapping theorem.** A surjective `A`-equivariant additive map from a complete
first-countable uniform additive group `M` to a `T₀` Baire topological additive group `N` is open,
when `A` has a zero sequence of units.

The continuity assumptions are asymmetric between source and target: only continuity at zero is
asked of `f` (`hfc`), only continuity at zero in the scalar variable is asked on the source `M`
(`hc : ∀ x : M, ContinuousAt (fun a : A ↦ a • x) 0`), and continuity of each fixed scalar action
is asked on the target `N` (`ContinuousConstSMul A N`). -/
theorem HasZeroSequenceOfUnits.isOpenMap {F : Type*} [FunLike F M N] [MulActionHomClass F A M N]
    [AddMonoidHomClass F M N] (f : F) (hf : Function.Surjective f)
    (hfc : ContinuousAt (f : M → N) 0) (hc : ∀ x : M, ContinuousAt (fun a : A ↦ a • x) 0) :
    IsOpenMap (f : M → N) :=
  isOpenMap_of_closure_image_mem_nhds f hfc fun _ hU ↦
    HasZeroSequenceOfUnits.closure_image_mem_nhds_zero f hf hc hU

/-- **Henkel's theorem in quotient form.** Under exactly the hypotheses of
`TauCeti.HasZeroSequenceOfUnits.isOpenMap`, the map does not merely carry open sets to open sets:
the topology of `N` is the one coinduced from `M`, so a map out of `N` is continuous exactly when
its composite with `f` is.

The quotient conclusion needs `f` continuous everywhere, but that is not an extra hypothesis: an
additive homomorphism out of a topological group is continuous as soon as it is continuous at `0`
(`continuous_of_continuousAt_zero`), so `hfc` is the same assumption the open-mapping theorem
makes. This is the form behind `TauCeti.Huber.IsTateRing.isModuleTopology`, which pins down the
topology of a finite module over a Tate ring. -/
theorem HasZeroSequenceOfUnits.isQuotientMap {F : Type*} [FunLike F M N]
    [MulActionHomClass F A M N] [AddMonoidHomClass F M N] (f : F) (hf : Function.Surjective f)
    (hfc : ContinuousAt (f : M → N) 0) (hc : ∀ x : M, ContinuousAt (fun a : A ↦ a • x) 0) :
    IsQuotientMap (f : M → N) :=
  have hcont : Continuous (f : M → N) := continuous_of_continuousAt_zero f hfc
  (HasZeroSequenceOfUnits.isOpenMap f hf hfc hc).isQuotientMap hcont hf

end TauCeti

section Strict

open TopologicalSpace

variable {R E F : Type*} [Semiring R] [TopologicalSpace R] [TauCeti.HasZeroSequenceOfUnits R]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [Module R E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [Module R F] [ContinuousConstSMul R F]

namespace LinearMap

/-- A linear map over a semiring with a zero sequence of units whose range is `T₀` and Baire is
strict when the source is complete and first countable. On the source, only continuity at zero is
needed for the map and for scalar multiplication (`hc : ∀ x, ContinuousAt (fun a ↦ a • x) 0`),
while on the codomain `F`, each fixed scalar action must be continuous (`ContinuousConstSMul R F`).
Neither completeness nor metrisability is required of the ambient codomain `F`.

The target's additive operations need only be continuous: no uniform structure on the target
or uniform continuity of its operations is assumed. -/
theorem isStrictMap_of_baireSpace_range_of_hasZeroSequenceOfUnits (f : E →ₗ[R] F)
    [BaireSpace f.range] [T0Space f.range]
    (hfc : ContinuousAt (f : E → F) 0)
    (hc : ∀ x : E, ContinuousAt (fun a : R ↦ a • x) 0) : Topology.IsStrictMap (f : E → F) := by
  let : Neg f.range := ⟨fun y ↦ ⟨-y.val, by
    obtain ⟨x, hx⟩ := y.property
    exact ⟨-x, by simp [hx]⟩⟩⟩
  let : Sub f.range := ⟨fun y₁ y₂ ↦ ⟨y₁.val - y₂.val, by
    obtain ⟨x₁, hx₁⟩ := y₁.property
    obtain ⟨x₂, hx₂⟩ := y₂.property
    exact ⟨x₁ - x₂, by simp [hx₁, hx₂]⟩⟩⟩
  let : AddGroup f.range :=
    { (inferInstance : AddMonoid f.range) with
      neg := Neg.neg
      sub := Sub.sub
      sub_eq_add_neg := fun a b ↦ Subtype.ext (sub_eq_add_neg a.val b.val)
      neg_add_cancel := fun a ↦ Subtype.ext (neg_add_cancel a.val)
      zsmul := zsmulRec }
  have : IsTopologicalAddGroup f.range :=
    { continuous_add :=
        continuous_induced_rng.mpr (continuous_subtypeVal.fst'.add continuous_subtypeVal.snd')
      continuous_neg := continuous_induced_rng.mpr continuous_subtypeVal.neg }
  have hcont : Continuous (f.rangeRestrict : E → f.range) :=
    (continuous_of_continuousAt_zero f hfc).subtype_mk _
  have hopen : IsOpenMap (f.rangeRestrict : E → f.range) :=
    TauCeti.HasZeroSequenceOfUnits.isOpenMap f.rangeRestrict f.surjective_rangeRestrict
      hcont.continuousAt hc
  let Φ : f.range ≃ₜ f.toAddMonoidHom.range := Homeomorph.setCongr rfl
  have hcomp : (f.toAddMonoidHom.rangeRestrict : E → f.toAddMonoidHom.range) =
      Φ ∘ f.rangeRestrict := rfl
  refine f.toAddMonoidHom.isStrictMap_iff_isOpenQuotientMap_rangeRestrict.mpr ?_
  rw [hcomp]
  exact Φ.isOpenQuotientMap.comp ⟨f.surjective_rangeRestrict, hcont, hopen⟩

/-- A linear map with closed range over a semiring with a zero sequence of units is strict when
the source is complete and first countable and the target is completely metrisable. On the source,
only continuity at zero is needed for the map and for scalar multiplication (`hc`), while on the
codomain `F`, each fixed scalar action must be continuous (`ContinuousConstSMul R F`).

The target's additive operations need only be continuous: no uniform structure on the target
or uniform continuity of its operations is assumed. -/
theorem isStrictMap_of_isClosed_range_of_hasZeroSequenceOfUnits
    [IsCompletelyMetrizableSpace F] (f : E →ₗ[R] F)
    (hfc : ContinuousAt (f : E → F) 0)
    (hc : ∀ x : E, ContinuousAt (fun a : R ↦ a • x) 0)
    (hr : IsClosed (f.range : Set F)) : Topology.IsStrictMap (f : E → F) := by
  have : IsCompletelyMetrizableSpace f.range := hr.isCompletelyMetrizableSpace
  exact f.isStrictMap_of_baireSpace_range_of_hasZeroSequenceOfUnits hfc hc

end LinearMap

end Strict

end
