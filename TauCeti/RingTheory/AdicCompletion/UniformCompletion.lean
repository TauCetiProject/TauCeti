/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.UniformSpace.AbstractCompletion
import TauCeti.RingTheory.AdicCompletion.Algebra

/-!
# The uniform completion of an adic ring is its adic completion

Let `R` be a commutative topological ring whose topology is the `I`-adic topology for a finitely
generated ideal `I`. There are two completions of `R`: the Hausdorff completion
`UniformSpace.Completion R` for the additive uniformity, and Mathlib's algebraic adic completion
`AdicCompletion I R = lim R ⧸ Iⁿ`. This file identifies them: the extension of the canonical map
`R → AdicCompletion I R` is a ring isomorphism, and it is a homeomorphism when
`AdicCompletion I R` carries the adic topology of the extended ideal `I · AdicCompletion I R`.

The point is that `AdicCompletion I R`, with that topology, is an abstract completion of `R`. It is
complete and Hausdorff because it is adically complete (`AdicCompletion.isAdicComplete`, using
that `I` is finitely generated). The canonical map induces the `I`-adic topology on `R`, because
the preimage of `Iⁿ · AdicCompletion I R` is `Iⁿ`, and it has dense range, because every element
of `AdicCompletion I R` is congruent to an element of `R` modulo `Iⁿ · AdicCompletion I R`.

This is how completions of adic rings defined through uniform completion, such as completed tensor
products of adic rings, are compared with the corresponding algebraic adic completions.

## Main definitions

* `IsAdic.completionEquivAdicCompletion`: the ring isomorphism
  `UniformSpace.Completion R ≃+* AdicCompletion I R`.

## Main results

* `IsAdic.completionEquivAdicCompletion_coe`: it extends the canonical map
  `R → AdicCompletion I R`.
* `IsAdic.isHomeomorph_completionEquivAdicCompletion`: it is a homeomorphism for the adic topology
  of the extended ideal on `AdicCompletion I R`.

## References

* [The Stacks Project][stacks], Lemma 10.96.3 (tag
  [05GG](https://stacks.math.columbia.edu/tag/05GG)).
* N. Bourbaki, *Commutative Algebra*, Chapter III, §2, no. 12.
-/

public section

open UniformSpace Filter Topology

namespace IsAdic

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  {I : Ideal R}

/-- The adic topology of the extended ideal `I · AdicCompletion I R` on `AdicCompletion I R`, used
locally to view it as a completion of `R`. -/
private noncomputable abbrev withIdeal (I : Ideal R) : WithIdeal (AdicCompletion I R) :=
  ⟨I.map (algebraMap R (AdicCompletion I R))⟩

attribute [local instance] withIdeal AbstractCompletion.uniformStruct AbstractCompletion.complete
  AbstractCompletion.separation

omit [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R] in
/-- The local topology on `AdicCompletion I R` is, by definition, the adic topology of the extended
ideal. -/
private theorem isAdic_map_algebraMap :
    IsAdic (I.map (algebraMap R (AdicCompletion I R))) :=
  rfl

omit [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R] in
/-- For a finitely generated `I`, `AdicCompletion I R` is complete and Hausdorff for the adic
topology of the extended ideal. -/
private theorem completeSpace_and_t2Space (hfg : I.FG) :
    CompleteSpace (AdicCompletion I R) ∧ T2Space (AdicCompletion I R) :=
  isAdic_map_algebraMap.isAdicComplete_iff.mp
    ((IsAdicComplete.map_algebraMap_iff I _).mpr (AdicCompletion.isAdicComplete hfg))

/-- `AdicCompletion I R`, with the adic topology of the extended ideal, as an abstract completion of
the `I`-adic ring `R`. -/
private noncomputable def adicCompletionPkg (hI : IsAdic I) (hfg : I.FG) :
    AbstractCompletion R where
  space := AdicCompletion I R
  coe := algebraMap R (AdicCompletion I R)
  uniformStruct := inferInstance
  complete := (completeSpace_and_t2Space hfg).1
  separation := have := (completeSpace_and_t2Space (R := R) hfg).2; inferInstance
  isUniformInducing := by
    refine AddMonoidHom.isUniformInducing_of_isInducing
      (IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr ?_)
    refine hI.hasBasis_nhds_zero.eq_of_same_basis
      ((isAdic_map_algebraMap.hasBasis_nhds_zero.comap (algebraMap R (AdicCompletion I R))).congr
        (fun _ ↦ Iff.rfl) fun n _ ↦ ?_)
    ext x
    simp [← Ideal.map_pow, AdicCompletion.algebraMap_mem_map_pow_iff hfg]
  dense x := by
    refine (mem_closure_iff_nhds_basis (isAdic_map_algebraMap.hasBasis_nhds x)).mpr fun n _ ↦ ?_
    obtain ⟨y, hy⟩ := AdicCompletion.exists_sub_algebraMap_mem_map_pow hfg n x
    refine ⟨algebraMap R (AdicCompletion I R) y, ⟨y, rfl⟩,
      algebraMap R (AdicCompletion I R) y - x, ?_, add_sub_cancel x _⟩
    rw [SetLike.mem_coe, ← neg_sub, neg_mem_iff, ← Ideal.map_pow]
    exact hy

/-- The extension of the canonical map `R → AdicCompletion I R` to the uniform completion is the
comparison map between the two abstract completions of `R`. -/
private theorem extension_eq_compare (hI : IsAdic I) (hfg : I.FG) :
    Completion.extension (algebraMap R (AdicCompletion I R)) =
      Completion.cPkg.compare (adicCompletionPkg hI hfg) := by
  have := (completeSpace_and_t2Space (R := R) hfg).1
  have := (completeSpace_and_t2Space (R := R) hfg).2
  refine Completion.ext Completion.continuous_extension
    (Completion.cPkg.uniformContinuous_compare _).continuous fun a ↦ ?_
  have hf : UniformContinuous (algebraMap R (AdicCompletion I R)) :=
    (adicCompletionPkg hI hfg).isUniformInducing.uniformContinuous
  rw [Completion.extension_coe hf]
  exact (Completion.cPkg.compare_coe (adicCompletionPkg hI hfg) a).symm

/-- **The uniform completion of an adic ring is its adic completion.** If the topology of `R` is
the `I`-adic topology for a finitely generated ideal `I`, the Hausdorff completion of `R` is
isomorphic to `AdicCompletion I R`, through the extension of the canonical map. -/
noncomputable def completionEquivAdicCompletion (hI : IsAdic I) (hfg : I.FG) :
    Completion R ≃+* AdicCompletion I R :=
  haveI := (completeSpace_and_t2Space (R := R) hfg).1
  haveI := (completeSpace_and_t2Space (R := R) hfg).2
  RingEquiv.ofBijective (Completion.extensionHom (algebraMap R (AdicCompletion I R))
      (adicCompletionPkg hI hfg).isUniformInducing.isInducing.continuous) <| by
    -- The underlying function of `extensionHom` is `Completion.extension`.
    change Function.Bijective (Completion.extension _)
    rw [extension_eq_compare hI hfg]
    exact (Completion.cPkg.compareEquiv (adicCompletionPkg hI hfg)).bijective

/-- The underlying function of `completionEquivAdicCompletion` is the comparison map of the two
abstract completions. -/
private theorem coe_completionEquivAdicCompletion (hI : IsAdic I) (hfg : I.FG) :
    ⇑(completionEquivAdicCompletion hI hfg) =
      Completion.cPkg.compareEquiv (adicCompletionPkg hI hfg) :=
  extension_eq_compare hI hfg

/-- The isomorphism `completionEquivAdicCompletion` extends the canonical map
`R → AdicCompletion I R`. -/
@[simp]
theorem completionEquivAdicCompletion_coe (hI : IsAdic I) (hfg : I.FG) (x : R) :
    completionEquivAdicCompletion hI hfg x = algebraMap R (AdicCompletion I R) x := by
  rw [coe_completionEquivAdicCompletion]
  exact Completion.cPkg.compare_coe (adicCompletionPkg hI hfg) x

/-- The inverse of `completionEquivAdicCompletion` sends the image of `x ∈ R` in the adic completion
to its image in the uniform completion. -/
@[simp]
theorem completionEquivAdicCompletion_symm_algebraMap (hI : IsAdic I) (hfg : I.FG) (x : R) :
    (completionEquivAdicCompletion hI hfg).symm (algebraMap R (AdicCompletion I R) x) = x := by
  rw [RingEquiv.symm_apply_eq, completionEquivAdicCompletion_coe]

/-- The isomorphism `completionEquivAdicCompletion` is a homeomorphism when `AdicCompletion I R`
carries the adic topology of the extended ideal `I · AdicCompletion I R`. -/
theorem isHomeomorph_completionEquivAdicCompletion (hI : IsAdic I) (hfg : I.FG) :
    @IsHomeomorph _ _ _ (I.map (algebraMap R (AdicCompletion I R))).adicTopology
      (completionEquivAdicCompletion hI hfg) := by
  rw [coe_completionEquivAdicCompletion]
  exact (Completion.cPkg.compareEquiv (adicCompletionPkg hI hfg)).toHomeomorph.isHomeomorph

end IsAdic
