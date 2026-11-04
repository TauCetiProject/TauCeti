/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Algebra

/-!
# Adic topologies as initial topologies of discrete quotients

For an ideal `I` of a commutative ring `R`, the `I`-adic topology on `R` is the initial topology
induced by the quotient maps `R → R ⧸ I ^ (n + 1)` (or `R → R ⧸ I ^ n`) onto the discrete quotient
rings: at each element `x ∈ R`, the fibres of `R → R ⧸ I ^ (n + 1)` are the cosets
`x + I ^ (n + 1)` forming the `I`-adic neighbourhood basis.

When `I` is finitely generated, the kernel of the evaluation map
`AdicCompletion I R → R ⧸ I ^ n` is the `n`-th power of the extended ideal
`I · AdicCompletion I R` (`AdicCompletion.ker_evalₐ_eq_map_pow`), so the adic topology of the
extended ideal on `AdicCompletion I R` coincides with the inverse-limit topology induced by the
evaluations into the discrete quotients `R ⧸ I ^ (n + 1)`. This identifies the topology on basic
open sections of the formal spectrum with the adic topology of completed localisations.

## Main results

* `Ideal.adicTopology_eq_iInf_induced`, `Ideal.adicTopology_eq_iInf_induced_pow`: `I.adicTopology`
  is the initial topology for the quotient maps `R → R ⧸ I ^ (n + 1)` (respectively `R → R ⧸ I ^ n`)
  into discrete rings.
* `IsAdic.eq_iInf_induced`: if `I` defines the topology of `R`, that topology is the initial
  topology of the discrete quotients `R ⧸ I ^ (n + 1)`.
* `AdicCompletion.adicTopology_map_eq_iInf_induced`,
  `AdicCompletion.adicTopology_map_eq_iInf_induced_evalₐ`: for finitely generated `I`, the adic
  topology of `I · AdicCompletion I R` is the initial topology of the evaluation maps
  `AdicCompletion I R → R ⧸ I ^ (n + 1)` (respectively `R ⧸ I ^ n`).

## References

* N. Bourbaki, *Commutative Algebra*, Chapter III, §2, no. 6 and no. 12.
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.2 (7.2.1–7.2.2).
-/

public section

open Filter Topology

private theorem induced_bot_of_injective {X Y : Type*} {e : X → Y} (he : Function.Injective e) :
    TopologicalSpace.induced e ⊥ = ⊥ := by
  let _ : TopologicalSpace Y := ⊥
  have := discreteTopology_bot Y
  let _ : TopologicalSpace X := TopologicalSpace.induced e ⊥
  exact (Topology.IsEmbedding.discreteTopology ⟨⟨rfl⟩, he⟩).eq_bot

private theorem nhds_induced_bot {X Y : Type*} (g : X → Y) (x : X) :
    @nhds X (TopologicalSpace.induced g ⊥) x = 𝓟 (g ⁻¹' {g x}) := by
  let _ : TopologicalSpace Y := ⊥
  have := discreteTopology_bot Y
  rw [nhds_induced, nhds_discrete]
  exact comap_pure

namespace Ideal

variable {R : Type*} [CommRing R]

private theorem preimage_quotientMk_singleton (J : Ideal R) (x : R) :
    Ideal.Quotient.mk J ⁻¹' {Ideal.Quotient.mk J x} = (x + ·) '' (J : Set R) := by
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Ideal.Quotient.eq, Set.mem_image,
    SetLike.mem_coe]
  refine ⟨fun h ↦ ⟨y - x, h, add_sub_cancel x y⟩, ?_⟩
  rintro ⟨z, hz, rfl⟩
  simpa using hz

/-- The `I`-adic topology on a commutative ring `R` is the initial topology induced by the quotient
maps `R → R ⧸ I ^ (n + 1)` into the discrete rings `R ⧸ I ^ (n + 1)`. -/
theorem adicTopology_eq_iInf_induced (I : Ideal R) :
    I.adicTopology =
      ⨅ n : ℕ, TopologicalSpace.induced (Ideal.Quotient.mk (I ^ (n + 1))) ⊥ := by
  refine TopologicalSpace.ext_nhds fun x ↦ ?_
  rw [nhds_iInf]
  simp only [nhds_induced_bot, preimage_quotientMk_singleton]
  refine le_antisymm ?_ ?_
  · exact le_iInf fun n ↦ le_principal_iff.mpr
      ((I.hasBasis_nhds_adic x).mem_of_mem (i := n + 1) trivial)
  · exact (I.hasBasis_nhds_adic x).ge_iff.mpr fun n _ ↦
      mem_iInf_of_mem n (mem_principal.mpr (Set.image_mono (Ideal.pow_le_pow_right n.le_succ)))

/-- The `I`-adic topology on a commutative ring `R` is the initial topology induced by the quotient
maps `R → R ⧸ I ^ n` into the discrete rings `R ⧸ I ^ n`. -/
theorem adicTopology_eq_iInf_induced_pow (I : Ideal R) :
    I.adicTopology =
      ⨅ n : ℕ, TopologicalSpace.induced (Ideal.Quotient.mk (I ^ n)) ⊥ := by
  rw [adicTopology_eq_iInf_induced]
  refine le_antisymm (le_iInf fun n ↦ ?_) (le_iInf fun n ↦ iInf_le _ (n + 1))
  cases n with
  | zero =>
    have hsub : Subsingleton (R ⧸ I ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]
      exact Ideal.Quotient.subsingleton_iff.mpr rfl
    have htop : TopologicalSpace.induced (Ideal.Quotient.mk (I ^ 0)) ⊥ = ⊤ := by
      refine TopologicalSpace.ext_nhds fun x ↦ ?_
      have hpre : Ideal.Quotient.mk (I ^ 0) ⁻¹' {Ideal.Quotient.mk (I ^ 0) x} = Set.univ :=
        Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _
      rw [nhds_induced_bot, hpre, principal_univ, nhds_top]
    exact htop ▸ le_top
  | succ n => exact iInf_le _ n

end Ideal

namespace IsAdic

variable {R : Type*} [CommRing R] [TopologicalSpace R] {I : Ideal R}

/-- If an ideal `I` defines the topology of `R`, then the topology of `R` is the initial topology
induced by the quotient maps `R → R ⧸ I ^ (n + 1)` into discrete rings. -/
theorem eq_iInf_induced (hI : IsAdic I) :
    ‹TopologicalSpace R› =
      ⨅ n : ℕ, TopologicalSpace.induced (Ideal.Quotient.mk (I ^ (n + 1))) ⊥ :=
  hI.trans (Ideal.adicTopology_eq_iInf_induced I)

end IsAdic

namespace AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}

private theorem induced_mk_map_pow_eq_induced_evalₐ (fg : I.FG) (n : ℕ) :
    TopologicalSpace.induced
        (Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ n)) ⊥ =
      TopologicalSpace.induced (evalₐ I n) ⊥ := by
  have hfun : (evalₐ I n : AdicCompletion I R → R ⧸ I ^ n) =
      (quotientMapPowAlgEquiv fg n ∘ Ideal.quotEquivOfEq (Ideal.map_pow _ I n).symm) ∘
        Ideal.Quotient.mk ((I.map (algebraMap R (AdicCompletion I R))) ^ n) := by
    ext x
    simp [Function.comp_apply, Ideal.quotEquivOfEq_mk]
  rw [hfun, ← induced_compose,
    induced_bot_of_injective
      ((quotientMapPowAlgEquiv fg n).injective.comp (Ideal.quotEquivOfEq _).injective)]

/-- For a finitely generated ideal `I`, the adic topology of the extended ideal
`I · AdicCompletion I R` is the initial topology induced by the evaluation maps
`AdicCompletion I R → R ⧸ I ^ (n + 1)` into the discrete quotients. -/
theorem adicTopology_map_eq_iInf_induced (fg : I.FG) :
    (I.map (algebraMap R (AdicCompletion I R))).adicTopology =
      ⨅ n : ℕ, TopologicalSpace.induced (evalₐ I (n + 1)) ⊥ := by
  rw [Ideal.adicTopology_eq_iInf_induced]
  exact iInf_congr fun n ↦ induced_mk_map_pow_eq_induced_evalₐ fg (n + 1)

/-- For a finitely generated ideal `I`, the adic topology of the extended ideal
`I · AdicCompletion I R` is the initial topology induced by all evaluation maps
`AdicCompletion I R → R ⧸ I ^ n` into the discrete quotients. -/
theorem adicTopology_map_eq_iInf_induced_evalₐ (fg : I.FG) :
    (I.map (algebraMap R (AdicCompletion I R))).adicTopology =
      ⨅ n : ℕ, TopologicalSpace.induced (evalₐ I n) ⊥ := by
  rw [Ideal.adicTopology_eq_iInf_induced_pow]
  exact iInf_congr fun n ↦ induced_mk_map_pow_eq_induced_evalₐ fg n

end AdicCompletion
