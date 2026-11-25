/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.FiniteAdeleRing
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place
public import TauCeti.Topology.Algebra.Group.DiscontinuousSubgroup
import TauCeti.NumberTheory.NumberField.FinitePlace.Basic
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# A number field is not discrete in its finite adeles

The additive group `G_a(K) = K` of a number field `K` is not discrete in the finite adele ring
`𝔸_{K,f}`. It meets the compact open integral adeles `∏_v 𝒪_v` in an infinite set, containing
the natural numbers, so the criterion
`AddSubgroup.discreteTopology_iff_finite_inter_of_isCompact` fails. This is the additive group
`G_a`, read directly in the finite adele ring, for the criterion
`TauCeti.AdelicPoints.discreteTopology_range_finiteDiagonal_iff`: the rational points of an affine
group scheme need not be discrete in its finite adelic points, unlike in its full adelic points.

## Main declarations

* `TauCeti.FiniteAdelicDiscreteness.not_discreteTopology_range_algebraMap`: `K` is not discrete in
  `𝔸_{K,f}`.

## References

* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), §1.8, p. 9.
-/

public section

open IsDedekindDomain NumberField
open scoped NumberField.AdeleRing

namespace TauCeti.FiniteAdelicDiscreteness

variable (K : Type*) [Field K] [NumberField K]

/-- **A number field is not discrete in its finite adeles.** The diagonal copy of `K` meets the
compact open integral adeles in the infinitely many natural numbers. -/
theorem not_discreteTopology_range_algebraMap :
    ¬ DiscreteTopology (algebraMap K 𝔸ᶠ[K]).range.toAddSubgroup := by
  intro h
  have hfin := ((algebraMap K 𝔸ᶠ[K]).range.toAddSubgroup
    |>.discreteTopology_iff_finite_inter_of_isCompact FiniteAdeleRing.isCompact_integralAdeles
    ((FiniteAdeleRing.isOpen_integralAdeles (𝓞 K) K).mem_nhds
      (FiniteAdeleRing.integralAdeles (𝓞 K) K).zero_mem)).mp h
  obtain ⟨v⟩ : Nonempty (HeightOneSpectrum (𝓞 K)) := inferInstance
  have : Nontrivial 𝔸ᶠ[K] := (FiniteAdeleRing.proj_surjective (K := K) v).nontrivial
  have : CharZero 𝔸ᶠ[K] := charZero_of_injective_algebraMap (algebraMap K 𝔸ᶠ[K]).injective
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ ↦ (n : 𝔸ᶠ[K])) Nat.cast_injective
    (fun n ↦ ?_) hfin
  exact ⟨⟨n, map_natCast _ n⟩, (FiniteAdeleRing.integralAdeles (𝓞 K) K).natCast_mem n⟩

end TauCeti.FiniteAdelicDiscreteness
