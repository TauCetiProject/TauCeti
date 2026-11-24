/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import TauCeti.AlgebraicGeometry.Scheme.Normal
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Normal
import TauCeti.RingTheory.Etale.Field

/-!
# Normal schemes under étale morphisms and separable base change

An étale morphism `f : X ⟶ Y` preserves and reflects normality of local rings
(`AlgebraicGeometry.Scheme.Hom.isDomain_and_isIntegrallyClosed_stalk_iff_of_etale`, Stacks,
Proposition 41.19.7 (025P)). So an étale scheme over a normal scheme is normal
(`TauCeti.AlgebraicGeometry.IsNormalScheme.of_etale`, the scheme form of Stacks, Lemma 10.163.9
(033C)), and a scheme with a surjective étale morphism from a normal scheme is normal
(`TauCeti.AlgebraicGeometry.IsNormalScheme.of_etale_of_surjective`).

Étale morphisms are stable under base change, so the base change `X ×_S Y` of a normal scheme `X`
along an étale morphism `Y ⟶ S` is normal (`TauCeti.AlgebraicGeometry.isNormalScheme_pullback`).
In particular, for a normal scheme `X` over a field `k` and a finite separable extension `K / k`,
the base change `X_K = X ×_{Spec k} Spec K` is normal
(`TauCeti.AlgebraicGeometry.isNormalScheme_pullback_of_isSeparable`); no finiteness or Noetherian
hypothesis is made on `X`. This is the finite separable case of Stacks, Lemma 33.10.6 (0C3M); the
general case of a separable, not necessarily algebraic, extension needs normality of filtered
colimits of normal rings.

## Main results

* `TauCeti.AlgebraicGeometry.IsNormalScheme.of_etale`: the source of an étale morphism to a normal
  scheme is normal.
* `TauCeti.AlgebraicGeometry.IsNormalScheme.of_etale_of_surjective`: the target of a surjective
  étale morphism from a normal scheme is normal.
* `TauCeti.AlgebraicGeometry.isNormalScheme_pullback`: étale base change preserves normality.
* `TauCeti.AlgebraicGeometry.isNormalScheme_pullback_of_isSeparable`: finite separable base change
  of the ground field preserves normality.

## References

* [Stacks Project, Proposition 41.19.7](https://stacks.math.columbia.edu/tag/025P),
  [Lemma 10.163.9](https://stacks.math.columbia.edu/tag/033C) and
  [Lemma 33.10.6](https://stacks.math.columbia.edu/tag/0C3M).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- **Étale over normal is normal.** The source of an étale morphism to a normal scheme is normal:
every local ring of the source is étale over a local ring of the target. -/
@[stacks 033C "scheme form"]
theorem IsNormalScheme.of_etale (f : X ⟶ Y) [Etale f] [IsNormalScheme Y] : IsNormalScheme X :=
  isNormalScheme_iff_forall_stalk.2 fun x ↦
    (f.isDomain_and_isIntegrallyClosed_stalk_iff_of_etale x).1
      (isNormalScheme_iff_forall_stalk.1 ‹_› (f x))

/-- **Normality descends along surjective étale morphisms.** The target of a surjective étale
morphism from a normal scheme is normal. -/
theorem IsNormalScheme.of_etale_of_surjective (f : X ⟶ Y) [Etale f] [Surjective f]
    [IsNormalScheme X] : IsNormalScheme Y :=
  isNormalScheme_iff_forall_stalk.2 fun y ↦ by
    obtain ⟨x, rfl⟩ := f.surjective y
    exact (f.isDomain_and_isIntegrallyClosed_stalk_iff_of_etale x).2
      (isNormalScheme_iff_forall_stalk.1 ‹_› x)

/-- **Étale base change preserves normality.** The base change `X ×_S Y` of a normal scheme `X`
along an étale morphism `Y ⟶ S` is normal, since its projection to `X` is étale. -/
instance isNormalScheme_pullback {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [Etale g]
    [IsNormalScheme X] : IsNormalScheme (pullback f g) :=
  .of_etale (pullback.fst f g)

/-- **Finite separable base change of the ground field preserves normality.** For a normal scheme
`X` over a field `k` and a finite separable field extension `K / k`, the base change
`X_K = X ×_{Spec k} Spec K` is normal. -/
@[stacks 0C3M "finite separable extension"]
theorem isNormalScheme_pullback_of_isSeparable {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [Algebra.IsSeparable k K] (f : X ⟶ Spec (.of k))
    [IsNormalScheme X] :
    IsNormalScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
  have : Algebra.Etale k K := Algebra.Etale.of_isSeparable k K
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.etale_algebraMap.2 ‹_›)
  inferInstance

end AlgebraicGeometry

end TauCeti
