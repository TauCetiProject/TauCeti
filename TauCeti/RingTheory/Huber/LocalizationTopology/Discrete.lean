/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Completion
public import TauCeti.Topology.UniformSpace.DiscreteUniformity

/-!
# Completed localisations of a discrete ring

Let `A` be a ring with the discrete topology and `P = (A₀, I)` any pair of definition of `A`.
Since `{0}` is a neighbourhood of zero, it contains the image of some power `Iⁿ`, so `I` is
nilpotent (`PairOfDefinition.exists_pow_idealOfDefinition_eq_bot`). Two consequences for the
localisation `Aₛ` of `A` away from `s` follow.

* Every presentation `(T, s)` satisfies the standing hypothesis `HasDenominatorPower`: the
  fractions `b/s` with `b ∈ Iⁿ = 0` are zero.
* The localisation topology on `Aₛ` is discrete: its basic neighbourhood `image(Jⁿ)`, where
  `J = I · A₀[T/s]`, is the image of `Iⁿ · A₀[T/s] = 0`.

The uniformity of `Aₛ` is then discrete too, so `Aₛ` is complete and Hausdorff, and the completed
localisation `A⟨T/s⟩` is `Aₛ` itself, again with the discrete topology. Thus, on a discrete
Huber pair, the coordinate ring of the rational subset `R(T/s)` is the localisation `A_s`, and no
completion occurs. This is the description of the coordinate rings used in Wedhorn's proof of
Theorem 8.28 for discrete Huber pairs, where sheafiness of `Spa(A, A⁺)` is reduced to the exactness
of the Čech complexes of localisations.

## Main results

* `TauCeti.Huber.PairOfDefinition.hasDenominatorPower_of_discreteTopology`: over a discrete ring
  every presentation satisfies the standing hypothesis of the localisation topology.
* `TauCeti.Huber.PairOfDefinition.discreteTopology_locTopology` and
  `TauCeti.Huber.PairOfDefinition.discreteUniformity_locUniformSpace`: the localisation topology
  and its uniformity are discrete.
* `TauCeti.Huber.PairOfDefinition.discreteTopology_completion_locUniformSpace`: `A⟨T/s⟩` is
  discrete.
* `TauCeti.Huber.PairOfDefinition.completionLocEquivOfDiscreteTopology`: the canonical map
  `Aₛ → A⟨T/s⟩` is a ring isomorphism.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition and
  Definition 5.51, and Theorem 8.28, case (c).
-/

public section

open Filter Topology

namespace TauCeti.Huber

namespace PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [DiscreteTopology A]

/-- **Over a discrete ring every presentation is admissible for the localisation topology.** The
ideal of definition is nilpotent, so the fractions `b/s` with `b` in a high enough power of it are
zero, and lie in the candidate ring of definition `A₀[T/s]`. -/
theorem hasDenominatorPower_of_discreteTopology (P : PairOfDefinition A) (T : Set A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] :
    HasDenominatorPower P T s S := by
  obtain ⟨N, hN⟩ := P.exists_pow_idealOfDefinition_eq_bot
  refine (hasDenominatorPower_iff P T s S).mpr ⟨N, fun b hb ↦ ?_⟩
  rw [hN, Ideal.mem_bot] at hb
  subst hb
  rw [ZeroMemClass.coe_zero, Localization.divBy_zero]
  exact zero_mem _

/-- **The localisation topology of a discrete ring is discrete**, for every pair of definition
and every admissible presentation. If `Iⁿ = 0` then `Jⁿ = Iⁿ · A₀[T/s] = 0`, so `{0}` is a basic
neighbourhood of zero in `Aₛ`. -/
theorem discreteTopology_locTopology (P : PairOfDefinition A) (T : Set A) (s : A) (S : Type*)
    [CommRing S] [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) :
    @DiscreteTopology S (locTopology P T s S hden) := by
  let _ := locTopology P T s S hden
  have _ := isTopologicalRing_locTopology P T s S hden
  obtain ⟨N, hN⟩ := P.exists_pow_idealOfDefinition_eq_bot
  have h0 : (locIdealImage P T s S N : Set S) = {0} := by
    ext x
    simp [mem_locIdealImage_iff, locIdeal_def, ← Ideal.map_pow, hN, eq_comm]
  refine discreteTopology_of_isOpen_singleton_zero (isOpen_singleton_iff_nhds_eq_pure _ |>.mpr ?_)
  refine le_antisymm (le_pure_iff.mpr ?_) (pure_le_nhds 0)
  exact h0 ▸ (hasBasis_nhds_zero_locTopology P T s S hden).mem_of_mem trivial

/-- **The uniformity of the localisation topology of a discrete ring is discrete.** It is the
uniformity of an additive group whose topology is discrete. Consequently `Aₛ` is complete and
Hausdorff for it. -/
theorem discreteUniformity_locUniformSpace (P : PairOfDefinition A) (T : Set A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    @DiscreteUniformity S (locUniformSpace P T s S hden) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ : DiscreteTopology S := by
    rw [locUniformSpace_toTopologicalSpace]
    exact discreteTopology_locTopology P T s S hden
  exact DiscreteUniformity.of_discreteTopology

/-- **The completed localisation `A⟨T/s⟩` of a discrete ring is discrete.** The uniformity of `Aₛ`
is discrete, so this is an instance of
`UniformSpace.Completion.discreteTopology_of_discreteUniformity`. -/
theorem discreteTopology_completion_locUniformSpace (P : PairOfDefinition A) (T : Set A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    DiscreteTopology (UniformSpace.Completion S) := by
  let _ := locUniformSpace P T s S hden
  have _ := discreteUniformity_locUniformSpace P T s S hden
  infer_instance

/-- **`Aₛ ≃+* A⟨T/s⟩` over a discrete ring.** The localisation `Aₛ` is complete and Hausdorff for
its discrete uniformity, so the canonical map into its completion `A⟨T/s⟩` is a ring isomorphism.
It is a homeomorphism as well, both sides being discrete
(`discreteTopology_locTopology`, `discreteTopology_completion_locUniformSpace`). -/
noncomputable def completionLocEquivOfDiscreteTopology (P : PairOfDefinition A) (T : Set A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    S ≃+* UniformSpace.Completion S :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  haveI := discreteUniformity_locUniformSpace P T s S hden
  (UniformSpace.Completion.completeRingEquivSelf S).symm

/-- The isomorphism `Aₛ ≃+* A⟨T/s⟩` is the canonical map into the completion. -/
@[simp]
theorem completionLocEquivOfDiscreteTopology_apply (P : PairOfDefinition A) (T : Set A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) (x : S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    completionLocEquivOfDiscreteTopology P T s S hden x = (x : UniformSpace.Completion S) := by
  let _ := locUniformSpace P T s S hden
  let _ := isUniformAddGroup_locUniformSpace P T s S hden
  let _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := discreteUniformity_locUniformSpace P T s S hden
  exact UniformSpace.Completion.completeRingEquivSelf_symm_apply S x

/-- The inverse of the isomorphism `Aₛ ≃+* A⟨T/s⟩` sends the image of `x ∈ Aₛ` back to `x`. -/
@[simp]
theorem completionLocEquivOfDiscreteTopology_symm_coe (P : PairOfDefinition A) (T : Set A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) (x : S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (completionLocEquivOfDiscreteTopology P T s S hden).symm (x : UniformSpace.Completion S) =
      x := by
  let _ := locUniformSpace P T s S hden
  let _ := isUniformAddGroup_locUniformSpace P T s S hden
  let _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := discreteUniformity_locUniformSpace P T s S hden
  exact UniformSpace.Completion.completeRingEquivSelf_coe S x

end PairOfDefinition

end TauCeti.Huber
