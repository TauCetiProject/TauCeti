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
  `LinearMap.isStrictMap_of_isClosed_range_of_hasZeroSequenceOfUnits`: over a ring with a zero
  sequence of units, linear maps from a complete first-countable uniform additive module whose
  range is `T₀` and Baire (for instance, closed range in a completely metrisable target) are
  strict, assuming continuity at zero for the map and for the scalar action on the source, and
  continuity of each fixed scalar action on the target.
* `ContinuousLinearMap.equivRangeOfIsStrictMap`: an injective strict continuous linear map induces
  a continuous linear equivalence onto its range.

The other two implications of Wedhorn's Theorem 6.16, that an open linear map is surjective and that
a continuous one has a complete target, are in `TauCeti.Topology.Algebra.OpenMapping.Converse`.

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
first-countable uniform additive group to a `T₀` Baire topological additive group is open, when `A`
has a zero sequence of units.

Only continuity at zero is asked of `f`, and only continuity in the scalar at zero is asked of
the action, in the form `hc` that the Baire step already uses. -/
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

variable {R E F : Type*} [Ring R] [TopologicalSpace R] [TauCeti.HasZeroSequenceOfUnits R]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [Module R E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [Module R F] [ContinuousConstSMul R F]

namespace LinearMap

/-- A linear map whose range is `T₀` and Baire is strict when the scalar ring has a zero sequence
of units and the source is complete and first countable. On the source, only continuity at zero is
needed for the map and for scalar multiplication (`hc : ∀ x, ContinuousAt (fun a ↦ a • x) 0`),
while on the codomain `F`, each fixed scalar action must be continuous (`ContinuousConstSMul R F`).
Neither completeness nor metrisability is required of the ambient codomain `F`.

The target's additive operations need only be continuous: no uniform structure on the target
or uniform continuity of its operations is assumed. -/
theorem isStrictMap_of_baireSpace_range_of_hasZeroSequenceOfUnits (f : E →ₗ[R] F)
    [BaireSpace f.range] [T0Space f.range]
    (hfc : ContinuousAt (f : E → F) 0)
    (hc : ∀ x : E, ContinuousAt (fun a : R ↦ a • x) 0) : Topology.IsStrictMap (f : E → F) := by
  have hcont : Continuous (f.rangeRestrict : E → f.range) :=
    (continuous_of_continuousAt_zero f hfc).subtype_mk _
  exact LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict.mpr
    ⟨f.surjective_rangeRestrict, hcont,
      TauCeti.HasZeroSequenceOfUnits.isOpenMap f.rangeRestrict f.surjective_rangeRestrict
        hcont.continuousAt hc⟩

/-- A linear map with closed range is strict when the scalar ring has a zero sequence of units,
the source is complete and first countable, and the target is completely metrisable. On the source,
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

section StrictRangeEquiv

namespace ContinuousLinearMap

variable {R E F : Type*} [Semiring R]
  [AddCommMonoid E] [TopologicalSpace E] [Module R E]
  [AddCommMonoid F] [TopologicalSpace F] [Module R F]

private theorem coe_ofInjective_eq_rangeRestrict (f : E →L[R] F) (hinj : Function.Injective f) :
    ⇑(LinearEquiv.ofInjective f.toLinearMap hinj) = f.rangeRestrict := by
  ext x
  rw [LinearEquiv.ofInjective_apply, coe_codRestrict_apply, coe_coe]

/-- An injective strict continuous linear map induces a continuous linear equivalence onto its
range. -/
noncomputable def equivRangeOfIsStrictMap (f : E →L[R] F)
    (hinj : Function.Injective f) (hstrict : Topology.IsStrictMap f) :
    E ≃L[R] f.range where
  toLinearEquiv := LinearEquiv.ofInjective f.toLinearMap hinj
  continuous_toFun := f.rangeRestrict.continuous.congr fun x ↦
    (congrFun (coe_ofInjective_eq_rangeRestrict f hinj) x).symm
  continuous_invFun :=
    (Topology.isEmbedding_iff_isStrictMap_injective.mpr ⟨hstrict, hinj⟩).continuous_iff.mpr <|
      continuous_subtypeVal.congr fun y ↦
        (LinearEquiv.ofInjective_symm_apply f.toLinearMap (h := hinj) y).symm

@[simp]
theorem toLinearEquiv_equivRangeOfIsStrictMap (f : E →L[R] F)
    (hinj : Function.Injective f) (hstrict : Topology.IsStrictMap f) :
    (f.equivRangeOfIsStrictMap hinj hstrict).toLinearEquiv =
      LinearEquiv.ofInjective f.toLinearMap hinj :=
  (rfl)

@[simp]
theorem coeFn_equivRangeOfIsStrictMap (f : E →L[R] F)
    (hinj : Function.Injective f) (hstrict : Topology.IsStrictMap f) :
    ⇑(f.equivRangeOfIsStrictMap hinj hstrict) = f.rangeRestrict :=
  coe_ofInjective_eq_rangeRestrict f hinj

@[simp]
theorem equivRangeOfIsStrictMap_apply (f : E →L[R] F)
    (hinj : Function.Injective f) (hstrict : Topology.IsStrictMap f) (x : E) :
    f.equivRangeOfIsStrictMap hinj hstrict x = f.rangeRestrict x :=
  congrFun (coeFn_equivRangeOfIsStrictMap f hinj hstrict) x

@[simp]
theorem coe_equivRangeOfIsStrictMap (f : E →L[R] F)
    (hinj : Function.Injective f) (hstrict : Topology.IsStrictMap f) :
    (f.equivRangeOfIsStrictMap hinj hstrict : E →L[R] f.range) = f.rangeRestrict :=
  ContinuousLinearMap.ext (equivRangeOfIsStrictMap_apply f hinj hstrict)

end ContinuousLinearMap

end StrictRangeEquiv

end
