/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# The topology of a restricted product

General facts about the restricted-product topology, which Mathlib defines as the final
topology over the principal stages `Πʳ i, [R i, A i]_[𝓟 S]`. A set is open if and only if its
preimage in every principal stage is open: this is the `Prop`-valued form of Mathlib's universal
property `RestrictedProduct.continuous_dom`. Inserting a single factor is continuous, the analogue
of `continuous_mulSingle` for `Pi` types.

The restricted-product topology is finer than the topology induced from the full product
`Π i, R i`, and in general strictly finer. The clearest instance is a family of discrete spaces
with reference sets of at most one element: every principal stage indexed by a cofinite set, and
hence the restricted product itself, is discrete (`discreteTopology_restrictedProduct`), whereas
the full product of discrete groups with infinitely many nontrivial factors is not. So for
discrete groups with trivial reference subgroups, infinitely many of them nontrivial, the coercion
to the full product is not inducing (`not_isInducing_coe_bot`): the restricted-product topology is
not the induced one. This is the reason continuity of a map *into* a restricted product does not
follow from continuity of its coordinates.

## References

* N. Bourbaki, *General Topology*.
* A. Weil, *Basic Number Theory*.
-/
public section

namespace TauCeti

open Filter Topology
open scoped RestrictedProduct

universe u v w

variable {ι : Type u} {R : ι → Type v} {A : ∀ i, Set (R i)} {𝓕 : Filter ι}
variable [∀ i, TopologicalSpace (R i)]

/-- A subset of a restricted product is open if and only if its preimage in every principal
stage `Πʳ i, [R i, A i]_[𝓟 S]` with `𝓕 ≤ 𝓟 S` is open. -/
theorem isOpen_restrictedProduct_iff {s : Set (Πʳ i, [R i, A i]_[𝓕])} :
    IsOpen s ↔ ∀ (S : Set ι) (hS : 𝓕 ≤ 𝓟 S),
      IsOpen (RestrictedProduct.inclusion R A hS ⁻¹' s) := by
  simp only [isOpen_iff_continuous_mem]
  exact RestrictedProduct.continuous_dom

section

variable {S : ι → Type w} {G : ι → Type v} [∀ i, SetLike (S i) (G i)] (B : ∀ i, S i)
variable [DecidableEq ι] [∀ i, One (G i)] [∀ i, OneMemClass (S i) (G i)]
variable [∀ i, TopologicalSpace (G i)]

/-- Inserting a single factor into a restricted product is continuous. -/
@[continuity, fun_prop]
theorem continuous_restrictedProduct_mulSingle (i : ι) :
    Continuous (RestrictedProduct.mulSingle B i) := by
  have h : (cofinite : Filter ι) ≤ 𝓟 {i}ᶜ :=
    le_principal_iff.2 (Set.finite_singleton i).compl_mem_cofinite
  let f : G i → Πʳ j, [G j, B j]_[𝓟 {i}ᶜ] := fun x ↦
    ⟨Pi.mulSingle i x, eventually_principal.2 fun j hj ↦ by
      rw [Pi.mulSingle_eq_of_ne (Set.notMem_singleton_iff.1 hj)]
      exact one_mem _⟩
  have hf : Continuous f :=
    RestrictedProduct.continuous_rng_of_principal.2 (continuous_mulSingle i)
  exact (RestrictedProduct.continuous_inclusion h).comp hf

end

section Discrete

/-- A principal stage `Πʳ i, [R i, A i]_[𝓟 S]` with `S` cofinite is discrete when the reference
sets `A i` for `i ∈ S` have at most one element and the spaces `R i` for `i ∉ S` are discrete: on
the stage the coordinates in `S` are determined by the reference sets, and only finitely many
coordinates remain free. -/
theorem discreteTopology_restrictedProduct_principal {S : Set ι} (hS : Sᶜ.Finite)
    (hA : ∀ i ∈ S, (A i).Subsingleton) (hR : ∀ i ∉ S, DiscreteTopology (R i)) :
    DiscreteTopology (Πʳ i, [R i, A i]_[𝓟 S]) := by
  refine discreteTopology_iff_isOpen_singleton.2 fun x ↦ ?_
  rw [RestrictedProduct.isEmbedding_coe_of_principal.isOpen_iff]
  refine ⟨Set.pi Sᶜ fun i ↦ {x i}, isOpen_set_pi hS fun i hi ↦ ?_, ?_⟩
  · have := hR i hi
    exact isOpen_discrete _
  ext y
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    ext i
    by_cases hi : i ∈ S
    · exact hA i hi (eventually_principal.1 y.2 i hi) (eventually_principal.1 x.2 i hi)
    · exact h i hi
  · rintro rfl i _
    rfl

variable [∀ i, DiscreteTopology (R i)]

/-- A restricted product of discrete spaces relative to reference sets with at most one element
is discrete: every principal stage indexed by a cofinite set is, and the restricted-product
topology is the final topology over these stages. -/
theorem discreteTopology_restrictedProduct (hA : ∀ i, (A i).Subsingleton) :
    DiscreteTopology (Πʳ i, [R i, A i]) := by
  refine discreteTopology_iff_isOpen_singleton.2 fun x ↦
    isOpen_restrictedProduct_iff.2 fun S hS ↦ ?_
  have := discreteTopology_restrictedProduct_principal (mem_cofinite.1 (le_principal_iff.1 hS))
    (fun i _ ↦ hA i) fun i _ ↦ inferInstance
  exact isOpen_discrete _

variable {G : ι → Type v} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]

/-- A restricted product of discrete groups relative to the trivial reference subgroups is
discrete. -/
instance discreteTopology_restrictedProduct_bot [∀ i, DiscreteTopology (G i)] :
    DiscreteTopology (Πʳ i, [G i, ((⊥ : Subgroup (G i)) : Set (G i))]) :=
  discreteTopology_restrictedProduct fun i ↦ by
    rw [Subgroup.coe_bot]
    exact Set.subsingleton_singleton

/-- For discrete groups with trivial reference subgroups, infinitely many of them nontrivial, the
restricted product does not carry the topology induced from the full product: the restricted
product is discrete, but every neighbourhood of `1` in the full product contains an element
supported at a single index with nontrivial group. The restricted-product topology is therefore
strictly finer than the induced one in general, and continuity of a map into a restricted product
does not follow from continuity of its coordinates. -/
theorem not_isInducing_coe_bot [∀ i, DiscreteTopology (G i)]
    (hG : {i | Nontrivial (G i)}.Infinite) :
    ¬ IsInducing ((↑) : Πʳ i, [G i, ((⊥ : Subgroup (G i)) : Set (G i))] → ∀ i, G i) := by
  classical
  intro h
  obtain ⟨t, ht, hts⟩ := h.isOpen_iff.1
    (isOpen_discrete {(1 : Πʳ i, [G i, ((⊥ : Subgroup (G i)) : Set (G i))])})
  obtain ⟨I, u, hu, hIt⟩ := isOpen_pi_iff.1 ht _ (by rw [← Set.mem_preimage, hts]; rfl)
  obtain ⟨j, hj, hjI⟩ := hG.exists_notMem_finset I
  have : Nontrivial (G j) := hj
  obtain ⟨g, hg⟩ := exists_ne (1 : G j)
  -- The element supported at `j` lies in the basic neighbourhood `I.pi u` of `1`, hence in `t`,
  -- but is not `1`.
  have hmem : RestrictedProduct.mulSingle (fun i ↦ (⊥ : Subgroup (G i))) j g ∈ (↑) ⁻¹' t :=
    hIt fun a ha ↦ by
      have haj : a ≠ j := fun hab ↦ hjI (hab ▸ ha)
      rw [RestrictedProduct.coe_mulSingle_apply, Pi.mulSingle_eq_of_ne haj]
      exact (hu a ha).2
  rw [hts, Set.mem_singleton_iff, RestrictedProduct.mulSingle_eq_one_iff] at hmem
  exact hg hmem

end Discrete

end TauCeti
