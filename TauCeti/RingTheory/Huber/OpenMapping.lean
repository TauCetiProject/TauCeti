/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ZeroSequenceOfUnits
public import TauCeti.Topology.Algebra.OpenMapping.Henkel
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import TauCeti.Topology.Algebra.Nonarchimedean.Pi

/-!
# The open mapping theorem over a Tate ring

Henkel's open mapping theorem applies over a Tate ring because the powers of a pseudouniformiser
form a zero sequence of units. A surjective linear map, continuous at zero, from a complete
first-countable nonarchimedean module to a Hausdorff Baire topological module is therefore open
and induces the quotient topology.

The source carries a complete uniform additive group structure and a countably generated
neighbourhood filter at zero. Its scalar action is jointly continuous, which supplies the
continuity in the scalar variable that Henkel's theorem needs. The target carries a topology,
continuous additive operations, and continuous constant scalar actions; its Baire and `T0Space`
hypotheses are stated directly. A completely metrisable target satisfies both, but no uniform
structure or metrisability is required of the target in the open and quotient forms.

The closed-range strictness form uses a completely metrisable target. Its closed range is again
completely metrisable and hence Baire, so applying the open mapping theorem to the corestriction
shows that the original map is strict. In all three forms, continuity at zero suffices because
an additive map between topological groups is continuous everywhere as soon as it is continuous
at zero.

A finite spanning family gives a surjective linear-combination map from `ι → A`. When the Tate
ring's additive uniformity is complete, the preceding theorem makes this presentation
open for every Hausdorff Baire topological module. The quotient form determines its topology:
a finitely generated Hausdorff Baire topological module over such a Tate ring carries the module
topology. Consequently every linear map from it to a topological module is continuous, by
Mathlib's `IsModuleTopology.continuous_of_linearMap`.

## Main results

* `LinearMap.isOpenMap_of_isTateRing`: a surjective linear map continuous at zero, from a complete
  first-countable nonarchimedean module to a Hausdorff Baire module over a Tate ring, is open.
* `LinearMap.isQuotientMap_of_isTateRing`: the same map induces the quotient topology.
* `LinearMap.isStrictMap_of_isClosed_range_of_isTateRing`: a linear map continuous at zero with
  closed range in a completely metrisable target is strict.
* `TauCeti.Huber.IsTateRing.isOpenMap_linearCombination` and
  `TauCeti.Huber.IsTateRing.isQuotientMap_linearCombination`: a finite spanning family presents a
  Hausdorff Baire topological module as an open quotient of `ι → A`.
* `TauCeti.Huber.IsTateRing.isModuleTopology`: a finitely generated Hausdorff Baire topological
  module over a Tate ring with complete additive uniformity carries the module topology.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Theorem 6.16 and Proposition 6.18(2). The proposition
  assumes `A` noetherian and both modules finitely generated with the topology of 6.18(1), and
  concludes continuity as well as openness onto the image. Here
  `TauCeti.Huber.IsTateRing.isModuleTopology` supplies continuity, while
  `LinearMap.isStrictMap_of_isClosed_range_of_isTateRing` supplies strictness under a closed-range
  hypothesis. The proposition itself is `LinearMap.isStrictMap_of_module_finite`, which obtains
  closedness of the range from `TauCeti.Huber.isClosed_of_isNoetherian`.
* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  [arXiv:1407.5647](https://arxiv.org/abs/1407.5647).

## Provenance

`TauCeti.Huber.IsTateRing.isModuleTopology` is adapted from the AINTLIB project
(Chris Birkbeck, Apache-2.0), `projects/AdicSpaces/Adic spaces/WedhornBanachTheorem.lean` at commit
`37bbdaeb9ad9e3bc9f0d660feadc2779e455a91c`, whose private
`continuous_of_moduleFinite_of_topNilpUnit` (lines 1113-1149) proves the continuity consequence by
the same route: present the source as a topological quotient along a finite generating family, then
transfer continuity across the quotient.

The proof is not transcribed, and the route is only the same as far as the presentation. There the
presentation map is built by hand, its openness is discharged by a `wedhorn_6_16_of_topNilpUnit`
that this repository does not have, and continuity is then pushed across the quotient by hand, in
twenty-five lines. Here the presentation is
`TauCeti.Huber.IsTateRing.isQuotientMap_linearCombination` above, and what is transferred is not
continuity of one map but the module topology itself, after which every linear map out of the source
is continuous by Mathlib's `IsModuleTopology.continuous_of_linearMap`. The hypotheses differ too:
the topologically nilpotent unit is supplied by `[IsTateRing A]` rather than taken as an explicit
argument, and in the consequence the target is asked only to be a topological `A`-module, where the
source lemma asks it to be complete, separated and countably uniform.

-/

public section

open Filter Topology

namespace LinearMap

open TauCeti.Huber

variable {A M N : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
  [(𝓝 (0 : M)).IsCountablyGenerated] [NonarchimedeanAddGroup M] [Module A M] [ContinuousSMul A M]
  [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [Module A N] [ContinuousConstSMul A N]

section Baire

variable [T0Space N] [BaireSpace N]

/-- **The open mapping theorem over a Tate ring.** A surjective linear map continuous at zero,
from a complete first-countable nonarchimedean module to a Hausdorff Baire module, is open.
The target needs only continuous constant scalar actions. -/
theorem isOpenMap_of_isTateRing (f : M →ₗ[A] N) (hf : Function.Surjective f)
    (hfc : ContinuousAt (f : M → N) 0) : IsOpenMap (f : M → N) :=
  TauCeti.HasZeroSequenceOfUnits.isOpenMap f hf hfc
    fun _ ↦ (continuous_id.smul continuous_const).continuousAt

/-- **The quotient form of the open mapping theorem over a Tate ring.** Under the hypotheses of
`LinearMap.isOpenMap_of_isTateRing`, the topology of the target is coinduced along the map. -/
theorem isQuotientMap_of_isTateRing (f : M →ₗ[A] N) (hf : Function.Surjective f)
    (hfc : ContinuousAt (f : M → N) 0) : IsQuotientMap (f : M → N) :=
  TauCeti.HasZeroSequenceOfUnits.isQuotientMap f hf hfc
    fun _ ↦ (continuous_id.smul continuous_const).continuousAt

end Baire

/-- **Strictness from a closed range over a Tate ring.** A linear map continuous at zero from a
complete first-countable nonarchimedean module to a completely metrisable module is strict when
its range is closed. The target needs only continuous constant scalar actions.

The closed range supplies a Baire target for the corestriction. This is the strictness step of
Wedhorn Proposition 6.18(2); `LinearMap.isStrictMap_of_module_finite` additionally obtains
continuity and closedness of the range from its finite and noetherian module hypotheses. -/
theorem isStrictMap_of_isClosed_range_of_isTateRing
    [TopologicalSpace.IsCompletelyMetrizableSpace N] (f : M →ₗ[A] N)
    (hfc : ContinuousAt (f : M → N) 0) (hr : IsClosed (f.range : Set N)) :
    Topology.IsStrictMap (f : M → N) :=
  f.isStrictMap_of_isClosed_range_of_hasZeroSequenceOfUnits hfc
    (fun _ ↦ (continuous_id.smul continuous_const).continuousAt) hr

end LinearMap

namespace TauCeti.Huber

section LinearCombination

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
  [IsTopologicalRing A] [IsTateRing A]
  {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [T0Space N] [BaireSpace N] [Module A N] [ContinuousSMul A N]
  {ι : Type*} [Fintype ι]

/-- **A finite spanning family presents `N` as an open quotient of `Aᶥ`.** The
linear-combination map `a ↦ ∑ aᵢ • gᵢ` is surjective because `g` spans and continuous because
the action is, hence open by `LinearMap.isOpenMap_of_isTateRing`.

Openness is the content. It is what turns "every element of `N` is a combination of the `gᵢ`" into
"every *small* element is a combination with *small* coefficients", and that quantitative form is
what the Banach-theorem arguments over a Tate ring consume. It is the open presentation used by
the BGR §3.7.2/1 density argument, `TauCeti.Huber.eq_top_of_dense_of_module_finite`.

The target is Hausdorff and Baire, and `g` spans. The source of
`LinearMap.isOpenMap_of_isTateRing` is instantiated at `ι → A`. The Tate ring is nonarchimedean
and first countable, and the `Pi` instances transfer these properties and completeness to
`ι → A`. -/
theorem IsTateRing.isOpenMap_linearCombination (g : ι → N)
    (hspan : Submodule.span A (Set.range g) = ⊤) :
    IsOpenMap (Fintype.linearCombination A g : (ι → A) → N) :=
  (Fintype.linearCombination A g).isOpenMap_of_isTateRing
    (span_range_eq_top_iff_surjective_fintypeLinearCombination A g |>.mp hspan)
    (IsModuleTopology.continuous_of_linearMap (Fintype.linearCombination A g)).continuousAt

/-- **The quotient form of `TauCeti.Huber.IsTateRing.isOpenMap_linearCombination`.** A finite
spanning family does not merely present `N` as an open image of `ι → A`: the topology of `N` is
the one coinduced along the linear-combination map.

This is the pairing that `LinearMap.isQuotientMap_of_isTateRing` makes with
`LinearMap.isOpenMap_of_isTateRing`, at the named finite-presentation API. -/
theorem IsTateRing.isQuotientMap_linearCombination (g : ι → N)
    (hspan : Submodule.span A (Set.range g) = ⊤) :
    IsQuotientMap (Fintype.linearCombination A g : (ι → A) → N) :=
  (Fintype.linearCombination A g).isQuotientMap_of_isTateRing
    (span_range_eq_top_iff_surjective_fintypeLinearCombination A g |>.mp hspan)
    (IsModuleTopology.continuous_of_linearMap (Fintype.linearCombination A g)).continuousAt

end LinearCombination

section ModuleFinite

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
  [IsTopologicalRing A] [IsTateRing A]
  {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [T0Space M] [BaireSpace M] [Module A M] [ContinuousSMul A M] [Module.Finite A M]

/-- **A module-finite Hausdorff Baire topological module over a Tate ring with complete additive
uniformity carries the module topology.**
That is: the topology `M` was given is already the finest one making it a topological `A`-module,
so nothing about `M`'s topology is left free once `A`'s is fixed.

This is the one reason `TauCeti.Huber.IsTateRing.isQuotientMap_linearCombination` is stated as a
quotient map rather than merely an open one. A finite generating family presents `M` as a
topological quotient of `Fin n → A`; the source of that presentation carries the module topology,
because `A` does over itself and Mathlib's `IsModuleTopology.instPi` carries that to a finite
product; and the module topology passes along a surjection, which is
`ModuleTopology.eq_coinduced_of_surjective`. Comparing the two descriptions of `M`'s topology as a
coinduced one gives the claim.

It is stated as a theorem rather than an instance deliberately. Its conclusion
`IsModuleTopology A M` has no discriminating head, so as an instance it would be tried on every
module-topology goal in every file that transitively imports this one, each attempt dragging in a
search for `IsTateRing`, `BaireSpace` and `Module.Finite`. Call it explicitly, as
`have := IsTateRing.isModuleTopology (A := A) (M := M)`.

The **continuity conjunct** of Wedhorn Proposition 6.18(2) is the immediate consequence: with that
in scope, `IsModuleTopology.continuous_of_linearMap f` gives `Continuous f` for every linear
`f : M →ₗ[A] N` into every topological `A`-module `N`, with no continuity hypothesis on `f` —
finiteness of the source is what supplies it. Two hypotheses of 6.18(2) are absent from that
consequence, and their absence is the content. `A` is **not** asked to be noetherian: that
hypothesis is spent entirely on closedness of the range, which continuity does not need. And the
target is asked only to be a topological `A`-module — no completeness, no separation, no countably
generated uniformity, not even a uniform structure. Both are genuine weakenings, not oversights;
the source carries the whole burden, as it must, since it is the source being finitely generated
that makes the quotient presentation available. The openness conjunct of 6.18(2) is
`LinearMap.isStrictMap_of_isClosed_range_of_isTateRing`, which takes the closed range as a
hypothesis; `LinearMap.isStrictMap_of_module_finite` combines the two conjuncts into 6.18(2).

Mathlib's `LinearMap.continuous_of_finiteDimensional` is the same phenomenon over a complete
nontrivially normed field, where finite-dimensionality plays the role finite generation plays here;
neither statement subsumes the other, since a Tate ring need not be a field. -/
theorem IsTateRing.isModuleTopology : IsModuleTopology A M := by
  obtain ⟨n, g, hspan⟩ := Module.Finite.exists_fin (R := A) (M := M)
  exact ⟨(IsTateRing.isQuotientMap_linearCombination g hspan).eq_coinduced.trans
    (ModuleTopology.eq_coinduced_of_surjective
      (span_range_eq_top_iff_surjective_fintypeLinearCombination A g |>.mp hspan)).symm⟩

end ModuleFinite

end TauCeti.Huber

end
