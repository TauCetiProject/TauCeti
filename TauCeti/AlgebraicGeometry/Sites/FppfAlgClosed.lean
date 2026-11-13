/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.CommAlgCat.Fppf
public import TauCeti.AlgebraicGeometry.RationalPoint.Image

/-!
# Fppf covers of an algebraically closed field

Let `K` be an algebraically closed field. Every fppf covering of `Spec K` has a section: some
member `Y ⟶ Spec K` of the covering family is nonempty and locally of finite type, so it has a
closed point, and by the Nullstellensatz that closed point is a `K`-rational point of `Y`. Hence
the only fppf covering sieve of `Spec K` is the maximal sieve.

The same holds on the affine fppf site `(CommAlgCat K)ᵒᵖ`, whose object `K` is `Spec K`. In
particular a section of an fppf sheafification over `K` is already a section of the original
presheaf, and two sections of the presheaf over `K` are identified by sheafification only if
they are equal. This identifies the `K`-points of fppf quotient sheaves, such as homogeneous
spaces of affine groups, with the pointwise quotients.

## Main results

* `AlgebraicGeometry.Scheme.eq_top_of_mem_fppfTopology_of_isAlgClosed`: the only fppf covering
  sieve of `Spec K` is the maximal sieve.
* `TauCeti.CommAlgCat.eq_top_of_mem_fppfTopology_of_isAlgClosed`: the same statement on the
  affine fppf site.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 5, quotient sheaves of affine groups and
  their rational points.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable (K : Type u) [Field K] [IsAlgClosed K]

/-- **Fppf covers of an algebraically closed field split.** The only fppf covering sieve of
`Spec K` is the maximal sieve. -/
theorem eq_top_of_mem_fppfTopology_of_isAlgClosed (S : Sieve (Spec (.of K)))
    (hS : S ∈ fppfTopology (Spec (.of K))) : S = ⊤ := by
  have : fppfPrecoverage.HasIsos := ⟨fun f _ ↦ f.singleton_mem_fppfPrecoverage⟩
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
  obtain ⟨R, ⟨hsurj, hR⟩, hRS⟩ := hS
  -- Some member `g : Y ⟶ Spec K` of the covering family has a point over the closed point.
  obtain ⟨_, _, hg, y, -⟩ := hsurj (IsLocalRing.closedPoint K)
  cases hg with
  | @of Y g hg =>
  have : LocallyOfFinitePresentation g := (hR hg).2
  -- The nonempty scheme `Y` has a `K`-rational point, which is a section of `g`.
  obtain ⟨p, hp, -⟩ := isClosed_univ.isLocallyClosed.exists_rationalPoint_mem g ⟨y, trivial⟩
  rw [← Sieve.id_mem_iff_eq_top, ← hp]
  exact S.downward_closed (hRS Y g hg) p

end AlgebraicGeometry.Scheme

namespace TauCeti.CommAlgCat

variable (K : Type u) [Field K] [IsAlgClosed K]

/-- **Fppf covers of an algebraically closed field split, affine form.** On the affine fppf
site over `K`, the only covering sieve of `K` itself is the maximal sieve. -/
theorem eq_top_of_mem_fppfTopology_of_isAlgClosed (S : Sieve (op (CommAlgCat.of K K)))
    (hS : S ∈ fppfTopology K (op (CommAlgCat.of K K))) : S = ⊤ := by
  let _ : (algSpec (CommRingCat.of K)).Full :=
    (algSpec.fullyFaithful (R := CommRingCat.of K)).full
  let _ : (algSpec (CommRingCat.of K)).Faithful :=
    (algSpec.fullyFaithful (R := CommRingCat.of K)).faithful
  rw [fppfTopology_def, Functor.mem_inducedTopology_iff_of_isCoverDense,
    GrothendieckTopology.mem_over_iff] at hS
  have htop : Sieve.overEquiv _ (S.functorPushforward (algSpec (CommRingCat.of K))) = ⊤ :=
    Scheme.eq_top_of_mem_fppfTopology_of_isAlgClosed K _ hS
  -- A fully faithful functor recovers a sieve from its pushforward.
  rw [← Sieve.functorPullback_functorPushforward_eq (F := algSpec (CommRingCat.of K)) (S := S),
    ← (Sieve.overEquiv _).symm_apply_apply (Sieve.functorPushforward _ S), htop,
    OrderIso.map_top]
  exact Sieve.functorPullback_top _ _

end TauCeti.CommAlgCat
