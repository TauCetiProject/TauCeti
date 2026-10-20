/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Completion.Basic
public import TauCeti.RingTheory.Huber.NoetherianType.Basic

import TauCeti.RingTheory.AdicCompletion.Noetherian
import TauCeti.RingTheory.Huber.Adic
import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Noetherianity of completions of adic rings and of rings of definition

Let `R` be a commutative ring whose topology is the `I`-adic topology for a finitely generated
ideal `I`. Its Hausdorff completion `R̂` (Mathlib's `UniformSpace.Completion`) carries the adic
topology of the extended ideal `I·R̂`, and is complete for it. If `R` is Noetherian, so is `R̂`.

The same argument applies to a ring of definition `A₀` of a Huber ring `A`: if `A₀` is Noetherian,
then so is the ring of definition `Â₀` of the completion `Â`, namely the closure of the image of
`A₀` (`TauCeti.Huber.PairOfDefinition.completion`). Consequently the completion of a Huber ring of
noetherian type is again of noetherian type. This is the form in which a noetherian hypothesis on
a possibly incomplete Huber ring reaches its completion, as in Huber's sheafiness theorem for rings
with a noetherian ring of definition.

In both cases the completed ring is adically complete for a finitely generated open ideal and
contains a dense image of a Noetherian ring, which makes its quotient by that ideal Noetherian;
`Ideal.isNoetherianRing_of_isAdicComplete_of_denseRange` concludes.

## Main results

* `IsAdic.map_coeRingHom`: the topology of `R̂` is the `I·R̂`-adic topology, for `I` finitely
  generated.
* `IsAdic.isAdicComplete_map_coeRingHom`: `R̂` is `I·R̂`-adically complete.
* `IsAdic.isNoetherianRing_completion`: the completion of a Noetherian ring for an adic topology
  is Noetherian.
* `TauCeti.Huber.PairOfDefinition.isNoetherianRing_completion`: the completion of a Noetherian ring
  of definition is a Noetherian ring of definition of the completion.
* `TauCeti.Huber.IsNoetherianType.completion`: the completion of a Huber ring of noetherian type is
  of noetherian type.

## References

* [The Stacks Project][stacks], Lemma 10.96.3 (tag
  [05GG](https://stacks.math.columbia.edu/tag/05GG)).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, (7.2.6) and
  (7.3.1).
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, Theorem 2.2.
* T. Wedhorn, *Adic Spaces*, Proposition 6.35 and Remark 6.37.
-/

public section

open UniformSpace

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]

namespace IsAdic

variable {I : Ideal R}

open TauCeti.Huber.PairOfDefinition in
/-- **The completion of an adic ring is adic for the extended ideal** (Stacks, Tag 05GG). If the
topology of `R` is `I`-adic for a finitely generated ideal `I`, the topology of its Hausdorff
completion `R̂` is the `I·R̂`-adic topology. -/
theorem map_coeRingHom (hI : IsAdic I) (hfg : I.FG) :
    IsAdic (I.map (Completion.coeRingHom : R →+* Completion R)) := by
  let P := adic I hI hfg
  -- The ring of definition of `P` is all of `R`, so `Â₀ = R̂`.
  have htop (t : Completion R) : t ∈ P.completionRingOfDefinition := by
    simp [P, adic_ringOfDefinition, Completion.denseRange_coe.closure_range]
  -- The `n`-th power of `I·R̂` is the closure of the image of `Iⁿ`.
  have hpow (n : ℕ) : ((I.map (Completion.coeRingHom : R →+* Completion R) ^ n : Ideal _) :
      Set (Completion R)) = P.completionIdealImage n := by
    have hmem {a : R} : a ∈ P.idealImage n ↔ a ∈ I ^ n := by
      simp [P, adic_idealImage]
    refine subset_antisymm ?_ (P.completionIdealImage_le_of_image_subset n fun a ha ↦ ?_)
    · let K : Ideal (Completion R) :=
        { carrier := P.completionIdealImage n
          add_mem' := (P.completionIdealImage n).add_mem
          zero_mem' := (P.completionIdealImage n).zero_mem
          smul_mem' := fun t _ hy ↦ P.mul_mem_completionIdealImage (htop t) hy }
      have hK : (I ^ n).map (Completion.coeRingHom : R →+* Completion R) ≤ K :=
        Ideal.map_le_iff_le_comap.mpr fun a ha ↦ P.coe_mem_completionIdealImage (hmem.mpr ha)
      rw [← Ideal.map_pow]
      exact hK
    · rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (hmem.mp ha)
  refine isAdic_iff.mpr ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
  · rw [hpow]
    exact P.isOpen_completionIdealImage n
  · obtain ⟨n, -, hn⟩ := P.hasBasis_nhds_zero_completion.mem_iff.mp hs
    exact ⟨n, (hpow n).symm ▸ hn⟩

/-- **The completion of an adic ring is adically complete for the extended ideal** (Stacks, Tag
05GG). If the topology of `R` is `I`-adic for a finitely generated ideal `I`, its Hausdorff
completion `R̂` is `I·R̂`-adically complete and separated. -/
theorem isAdicComplete_map_coeRingHom (hI : IsAdic I) (hfg : I.FG) :
    IsAdicComplete (I.map (Completion.coeRingHom : R →+* Completion R)) (Completion R) :=
  (hI.map_coeRingHom hfg).isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

/-- **The completion of a Noetherian ring for an adic topology is Noetherian** (EGA I, Ch. 0,
(7.3.1)). If the topology of a Noetherian ring `R` is `I`-adic for some ideal `I`, its Hausdorff
completion is Noetherian. -/
theorem isNoetherianRing_completion [IsNoetherianRing R] (hI : IsAdic I) :
    IsNoetherianRing (Completion R) :=
  have hfg : I.FG := IsNoetherian.noetherian I
  have := hI.isAdicComplete_map_coeRingHom hfg
  Ideal.isNoetherianRing_of_isAdicComplete_of_denseRange (hfg.map _)
    (by simpa using (hI.map_coeRingHom hfg).isOpen_pow 1) (f := Completion.coeRingHom)
    Completion.denseRange_coe

end IsAdic

namespace TauCeti.Huber

namespace PairOfDefinition

/-- **The completion of a Noetherian ring of definition is Noetherian** (EGA I, Ch. 0, (7.2.6)).
If a pair of definition `(A₀, I)` of `R` has `A₀` Noetherian, the ring of definition `Â₀` of the
completed pair `P.completion`, the closure of the image of `A₀` in `R̂`, is Noetherian. -/
instance isNoetherianRing_completion (P : PairOfDefinition R)
    [IsNoetherianRing P.ringOfDefinition] : IsNoetherianRing P.completion.ringOfDefinition := by
  have hmem (x : P.ringOfDefinition) :
      ((x : R) : Completion R) ∈ P.completion.ringOfDefinition := by
    rw [completion_ringOfDefinition, mem_completionRingOfDefinition_iff]
    exact subset_closure ⟨x, x.2, rfl⟩
  let f : P.ringOfDefinition →+* P.completion.ringOfDefinition :=
    (Completion.coeRingHom.comp P.ringOfDefinition.subtype).codRestrict _ hmem
  -- `Â₀` is the closure of the image of `A₀`, so the image of `f` is dense in it.
  have hf : DenseRange f := by
    refine Subtype.dense_iff.mpr fun x hx ↦ ?_
    rw [SetLike.mem_coe, completion_ringOfDefinition, mem_completionRingOfDefinition_iff] at hx
    convert hx using 2
    rw [← Set.range_comp]
    exact (Set.range_comp ((↑) : R → Completion R) ((↑) : P.ringOfDefinition → R)).trans
      (congrArg _ Subtype.range_coe)
  have hopen := P.completion.isAdic_idealOfDefinition.isOpen_pow 1
  rw [pow_one] at hopen
  exact Ideal.isNoetherianRing_of_isAdicComplete_of_denseRange P.completion.fg_idealOfDefinition
    hopen hf

end PairOfDefinition

/-- **The completion of a Huber ring of noetherian type is of noetherian type.** A Noetherian ring
of definition of `R` completes to a Noetherian ring of definition of `R̂`
(`TauCeti.Huber.PairOfDefinition.isNoetherianRing_completion`), and a strongly noetherian Tate ring
completes to a strongly noetherian Tate ring. -/
instance IsNoetherianType.completion [IsHuberRing R] [IsNoetherianType R] :
    IsNoetherianType (Completion R) :=
  IsNoetherianType.elim ‹_› (fun P _ ↦ .of_pairOfDefinition P.completion inferInstance)
    fun _ _ ↦
      have : IsStronglyNoetherian (Completion R) :=
        (Completion.isDenseInducing_coe.isStronglyNoetherian_iff
          (φ := (Completion.coeRingHom : R →+* Completion R))).mp ‹_›
      inferInstance

end TauCeti.Huber
