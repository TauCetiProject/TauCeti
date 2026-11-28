/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Basic
public import TauCeti.RepresentationTheory.BaseChange

/-!
# Change of coefficients for smooth representations

Let `A → B` be a homomorphism of commutative rings and `ρ` a representation of a topological group
`G` on an `A`-module `V`. The base change `B ⊗_A V` (`Representation.baseChange`) of a smooth
representation is smooth: the stabilizer of `b ⊗ v` contains the open stabilizer of `v`.

For a compact group `G` and `B` flat over `A`, the comparison map `B ⊗_A V^G → (B ⊗_A V)^G`
(`Representation.invariantsBaseChangeMap`) of a smooth representation is bijective, and hence so is
the map `B ⊗_A V^U → (B ⊗_A V)^U` for a compact subgroup `U` of any topological group. Injectivity
is flatness alone. For surjectivity, an invariant vector of `B ⊗_A V` is a finite sum `∑ bₖ ⊗ vₖ`,
and the `vₖ` are fixed by an open subgroup `W`. Then `W` has finite index in the compact group `G`,
and so does its normal core `N`. The vector lies in `B ⊗_A V^N`, it is invariant under the finite
group `G/N` there by flatness, and flat base change commutes with the invariants of a finite group
(`Representation.invariantsBaseChangeMap_bijective`), while `(V^N)^{G/N} ⊆ V^G`.

## Main results

* `Representation.stabilizer_le_stabilizer_baseChange_tmul`: the stabilizer of `b ⊗ v` contains
  the stabilizer of `v`.
* `Representation.isSmooth_baseChange`: base change preserves smoothness.
* `Representation.exists_isOpen_mem_range_lTensor_invariants`: every vector of `M ⊗_A V` comes from
  the invariants of an open subgroup.
* `Representation.invariantsBaseChangeMap_bijective_of_compactSpace`: for a compact group `G` and
  flat `B`, `B ⊗_A V^G → (B ⊗_A V)^G` is bijective.
* `Representation.invariantsBaseChangeMap_comp_subtype_bijective_of_isCompact`: for a compact
  subgroup `U` and flat `B`, `B ⊗_A V^U → (B ⊗_A V)^U` is bijective.
-/

public section

open TensorProduct

namespace Representation

/-! ### Smoothness of the base change -/

section Smooth

variable {A B G V : Type*} [CommSemiring A] [Semiring B] [Algebra A B] [Group G]
  [AddCommMonoid V] [Module A V] {ρ : Representation A G V}

/-- The stabilizer of `b ⊗ v` in the base change contains the stabilizer of `v`. -/
theorem stabilizer_le_stabilizer_baseChange_tmul (b : B) (v : V) :
    ρ.stabilizer v ≤ (baseChange B ρ).stabilizer (b ⊗ₜ[A] v) := fun g hg ↦ by
  rw [mem_stabilizer, baseChange_apply, LinearMap.baseChange_tmul, mem_stabilizer.1 hg]

variable [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- **Base change preserves smoothness.** -/
instance isSmooth_baseChange [IsSmooth ρ] : IsSmooth (baseChange B ρ) := by
  rw [isSmooth_iff_forall_mem_smoothVectors]
  intro x
  induction x with
  | add x y hx hy => exact (baseChange B ρ).smoothVectors.toSubmodule.add_mem hx hy
  | tmul b v =>
    exact mem_smoothVectors_iff.2 (Subgroup.isOpen_mono
      (stabilizer_le_stabilizer_baseChange_tmul b v) (IsSmooth.isOpen_stabilizer v))

end Smooth

/-! ### Invariants of a compact subgroup -/

section Invariants

variable {A G V : Type*} [CommRing A] [Group G] [AddCommGroup V] [Module A V]
  {ρ : Representation A G V}

/-- **Every vector of `M ⊗_A V` comes from the invariants of an open subgroup**, when `V` is
smooth: a finite sum `∑ mₖ ⊗ vₖ` lies in `M ⊗_A V^W` for `W` the intersection of the stabilizers of
the `vₖ`. -/
theorem exists_isOpen_mem_range_lTensor_invariants {M : Type*} [AddCommMonoid M] [Module A M]
    [TopologicalSpace G] [IsSmooth ρ] (x : M ⊗[A] V) :
    ∃ W : Subgroup G, IsOpen (W : Set G) ∧
      x ∈ LinearMap.range ((invariants (ρ.comp W.subtype)).subtype.lTensor M) := by
  classical
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  refine ⟨⨅ p ∈ S, ρ.stabilizer p.2, ?_, ?_⟩
  · simp only [Subgroup.coe_iInf]
    exact isOpen_biInter_finset fun p _ ↦ IsSmooth.isOpen_stabilizer p.2
  · refine Submodule.sum_mem _ fun p hp ↦ ⟨p.1 ⊗ₜ ⟨p.2, fun w ↦ ?_⟩, rfl⟩
    have hw := w.property
    simp only [Subgroup.mem_iInf] at hw
    simpa using mem_stabilizer.1 (hw p hp)

variable {B : Type*} [CommRing B] [Algebra A B] [TopologicalSpace G] [SeparatelyContinuousMul G]
  [Module.Flat A B] [IsSmooth ρ]

/-- For a compact group `G` and `B` flat over `A`, the comparison map `B ⊗_A V^G → (B ⊗_A V)^G` of
a smooth representation is surjective. -/
theorem invariantsBaseChangeMap_surjective_of_compactSpace [CompactSpace G] :
    Function.Surjective (invariantsBaseChangeMap (A := B) ρ) := by
  classical
  intro x
  obtain ⟨W, hW, y, hy⟩ := exists_isOpen_mem_range_lTensor_invariants (ρ := ρ) (x : B ⊗[A] V)
  have : W.FiniteIndex :=
    have := Subgroup.quotient_finite_of_isOpen W hW
    Subgroup.finiteIndex_of_finite_quotient
  let N := W.normalCore
  let τ := ρ.quotientToInvariants N
  -- The vectors fixed by `W` are fixed by `N ≤ W`.
  have hNW : invariants (ρ.comp W.subtype) ≤ invariants (ρ.comp N.subtype) := fun v hv ↦
    (mem_invariants _ _).2 fun h ↦ by
      simpa using (mem_invariants _ _).1 hv ⟨h, W.normalCore_le h.property⟩
  let y' := (Submodule.inclusion hNW).lTensor B y
  have hy' : (invariants (ρ.comp N.subtype)).subtype.lTensor B y' = x := by
    rw [← hy, ← LinearMap.lTensor_comp_apply, Submodule.subtype_comp_inclusion]
  -- By flatness, `y'` is invariant under the finite group `G ⧸ N`.
  have hinv : y' ∈ (baseChange B τ).invariants := by
    intro g
    induction g using QuotientGroup.induction_on with | H g => ?_
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := B) _
      (invariants (ρ.comp N.subtype)).injective_subtype
    -- The base change of the inclusion `V^N → V` is `G`-equivariant.
    have h := LinearMap.congr_fun
      (((ρ.quotientToInvariants_lift N).baseChange B).isIntertwining' g) y'
    have hx : (ρ g).lTensor B (x : B ⊗[A] V) = x := by
      simpa [LinearMap.baseChange_eq_lTensor] using (mem_invariants _ _).1 x.property g
    simpa [LinearMap.baseChange_eq_lTensor, hy', hx] using h
  obtain ⟨z, hz⟩ := (τ.invariantsBaseChangeMap_bijective (A := B)).2 ⟨y', hinv⟩
  -- The `G ⧸ N`-invariants of `V^N` are `G`-invariant.
  have hφ (w : τ.invariants) :
      ((invariants (ρ.comp N.subtype)).subtype ∘ₗ τ.invariants.subtype) w ∈ ρ.invariants := by
    refine (mem_invariants _ _).2 fun g ↦ ?_
    simpa [τ] using congrArg Subtype.val ((mem_invariants _ _).1 w.property (g : G ⧸ N))
  refine ⟨(LinearMap.codRestrict _ _ hφ).lTensor B z, Subtype.ext ?_⟩
  have hz' := congrArg Subtype.val hz
  rw [coe_invariantsBaseChangeMap] at hz'
  rw [coe_invariantsBaseChangeMap, ← LinearMap.lTensor_comp_apply,
    LinearMap.subtype_comp_codRestrict, LinearMap.lTensor_comp_apply, hz', hy']

/-- **Flat change of coefficients commutes with the invariants of a compact group.** For a smooth
representation `V` of a compact group `G` and `B` flat over `A`, the comparison map
`B ⊗_A V^G → (B ⊗_A V)^G` is bijective. -/
theorem invariantsBaseChangeMap_bijective_of_compactSpace [CompactSpace G] :
    Function.Bijective (invariantsBaseChangeMap (A := B) ρ) :=
  ⟨invariantsBaseChangeMap_injective _, invariantsBaseChangeMap_surjective_of_compactSpace⟩

variable {U : Subgroup G}

/-- For a compact subgroup `U` and `B` flat over `A`, the comparison map
`B ⊗_A V^U → (B ⊗_A V)^U` of a smooth representation is surjective. -/
theorem invariantsBaseChangeMap_comp_subtype_surjective_of_isCompact (hU : IsCompact (U : Set G)) :
    Function.Surjective (invariantsBaseChangeMap (A := B) (ρ.comp U.subtype)) :=
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have : SeparatelyContinuousMul U := U.toSubmonoid.separatelyContinuousMul
  invariantsBaseChangeMap_surjective_of_compactSpace

/-- **Flat change of coefficients commutes with the invariants of a compact subgroup.** For a
smooth representation `V`, a compact subgroup `U` and `B` flat over `A`, the comparison map
`B ⊗_A V^U → (B ⊗_A V)^U` is bijective. -/
theorem invariantsBaseChangeMap_comp_subtype_bijective_of_isCompact (hU : IsCompact (U : Set G)) :
    Function.Bijective (invariantsBaseChangeMap (A := B) (ρ.comp U.subtype)) :=
  ⟨invariantsBaseChangeMap_injective _,
    invariantsBaseChangeMap_comp_subtype_surjective_of_isCompact hU⟩

end Invariants

end Representation
