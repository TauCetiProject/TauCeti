/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Nondegenerate
public import TauCeti.Analysis.CStarAlgebra.Representation.HilbertSum
public import TauCeti.Analysis.CStarAlgebra.State.Space
import TauCeti.Analysis.CStarAlgebra.Quotient
import TauCeti.Analysis.CStarAlgebra.State.Separation
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Separable

/-!
# The Gelfand–Naimark theorem and separable `ℓ²` representations

Every complex C⋆-algebra `A`, possibly nonunital and nonseparable, admits a faithful (hence
isometric) nondegenerate representation on a complete complex Hilbert space in the universe of `A`
(`TauCeti.universalRepresentation`, `TauCeti.exists_faithful_nondegenerate_representation`), and is
therefore isometrically `⋆`-isomorphic to a norm-closed `⋆`-subalgebra of bounded operators on a
Hilbert space (`TauCeti.exists_starAlgEquiv_nonUnitalStarSubalgebra`).

Concretely, for `A` equipped with its canonical C⋆-order, `TauCeti.universalHilbertSpace A` is the
Hilbert direct sum `ℓ²` of the GNS Hilbert spaces `(statePositiveLinearMap φ).GNS` over all states
`φ ∈ stateSpace A`, and `TauCeti.universalRepresentation A` acts coordinatewise by
`(statePositiveLinearMap φ).gnsNonUnitalStarAlgHom`. Each GNS summand is nondegenerate
(`PositiveLinearMap.isNondegenerate_gnsNonUnitalStarAlgHom`), so their direct sum is nondegenerate
(`NonUnitalStarAlgHom.isNondegenerate_hilbertSum_iff`). When an element `a : A` acts as zero in
every GNS summand, `PositiveLinearMap.apply_star_mul_self_eq_zero_of_gnsNonUnitalStarAlgHom_eq_zero`
gives `φ (star a * a) = 0` for every state `φ`, forcing `a = 0` by state separation
(`TauCeti.eq_zero_iff_forall_mem_stateSpace_star_mul_self`). When `A` is trivial, its state space
is empty and `universalHilbertSpace A` is `0`, on which the zero representation is both injective
and nondegenerate.

When `A` is separable, the faithful state `ω` constructed in
`TauCeti.exists_positiveLinearMap_norm_eq_one_faithful` already has a separable GNS space `ω.GNS`
on which `ω.gnsNonUnitalStarAlgHom` is faithful and nondegenerate
(`TauCeti.exists_faithful_nondegenerate_representation_separable`), with a unit cyclic vector when
`A` is unital and nontrivial (`TauCeti.exists_faithful_cyclic_representation_separable`). For any
nontrivial separable `A`, countably amplifying `ω.gnsNonUnitalStarAlgHom` to
`lp (fun _ : ℕ ↦ ω.GNS) 2` produces a complete separable infinite-dimensional carrier, and
conjugating along a `ℕ`-indexed Hilbert basis
(`TauCeti.nonempty_linearIsometryEquiv_lp_of_infinite`) yields a faithful nondegenerate
representation on `lp (fun _ : ℕ ↦ ℂ) 2`
(`TauCeti.exists_injective_nondegenerate_representation_lp`).

## Main definitions and results

* `TauCeti.statePositiveLinearMap`, `TauCeti.universalHilbertSpace`,
  `TauCeti.universalRepresentation`, and `TauCeti.universalUnitalRepresentation`: the universal
  Hilbert space and representation of a C⋆-algebra over its state space, with
  `universalRepresentation_injective`, `isNondegenerate_universalRepresentation`, and
  `norm_universalRepresentation_apply`.
* `TauCeti.exists_faithful_nondegenerate_representation`,
  `TauCeti.exists_faithful_unital_representation`,
  `TauCeti.exists_starAlgEquiv_nonUnitalStarSubalgebra`, and
  `TauCeti.exists_starAlgEquiv_starSubalgebra`: the Gelfand–Naimark theorem (without assuming a
  pre-existing partial order on `A`).
* `TauCeti.exists_faithful_nondegenerate_representation_separable` and
  `TauCeti.exists_faithful_cyclic_representation_separable`: faithful representations of separable
  C⋆-algebras on separable Hilbert spaces.
* `TauCeti.exists_injective_nondegenerate_representation_lp` and
  `TauCeti.exists_injective_unital_representation_lp`: faithful nondegenerate (and unital)
  representations of nontrivial separable C⋆-algebras on `lp (fun _ : ℕ ↦ ℂ) 2`.

## References

* I. M. Gelfand and M. A. Naimark, *On the imbedding of normed rings into the ring of operators in
  Hilbert space*, Mat. Sb. 12 (54) (1943), 197–217.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Academic Press, 1990, Theorem 3.4.1.
* J. Peterson, *Notes on Operator Algebras*, §4.1, Corollary 4.1.7, p. 58.
-/

public section

noncomputable section

open TopologicalSpace
open scoped ComplexOrder CStarAlgebra ENNReal InnerProductSpace lp

universe u

namespace TauCeti

section UniversalWithOrder

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A state `φ : stateSpace A` bundled as a positive linear map `A →ₚ[ℂ] ℂ`. -/
def statePositiveLinearMap (φ : stateSpace A) : A →ₚ[ℂ] ℂ :=
  .mk₀ (WeakDual.toStrongDual φ.1 : A →ₗ[ℂ] ℂ) fun _ ↦ map_nonneg_of_mem_stateSpace φ.2

@[simp]
theorem statePositiveLinearMap_apply (φ : stateSpace A) (a : A) :
    statePositiveLinearMap φ a = φ.1 a :=
  (rfl)

variable (A) in
/-- The **universal Hilbert space** of a complex C⋆-algebra `A`, realized in the same universe as
`A` as the Hilbert direct sum of the GNS spaces over all states of `A`. When `A` is trivial, the
state space is empty and `universalHilbertSpace A` is `0`. -/
abbrev universalHilbertSpace : Type u :=
  lp (fun φ : stateSpace A ↦ (statePositiveLinearMap φ).GNS) 2

variable (A) in
/-- The **universal representation** of a complex C⋆-algebra `A` on `universalHilbertSpace A`,
acting in each coordinate `φ : stateSpace A` by the GNS representation of `φ`. -/
def universalRepresentation :
    A →⋆ₙₐ[ℂ] (universalHilbertSpace A →L[ℂ] universalHilbertSpace A) :=
  NonUnitalStarAlgHom.hilbertSum fun φ : stateSpace A ↦
    (statePositiveLinearMap φ).gnsNonUnitalStarAlgHom

@[simp]
theorem universalRepresentation_apply_apply (a : A) (x : universalHilbertSpace A)
    (φ : stateSpace A) :
    universalRepresentation A a x φ = (statePositiveLinearMap φ).gnsNonUnitalStarAlgHom a (x φ) :=
  NonUnitalStarAlgHom.hilbertSum_apply_apply _ a x φ

variable (A) in
/-- The universal representation of any complex C⋆-algebra is nondegenerate. -/
theorem isNondegenerate_universalRepresentation :
    (universalRepresentation A).IsNondegenerate :=
  (NonUnitalStarAlgHom.isNondegenerate_hilbertSum_iff _).2 fun φ ↦
    (statePositiveLinearMap φ).isNondegenerate_gnsNonUnitalStarAlgHom

variable (A) in
/-- The universal representation of any complex C⋆-algebra is faithful (injective). -/
theorem universalRepresentation_injective :
    Function.Injective (universalRepresentation A) := by
  refine (NonUnitalStarAlgHom.injective_hilbertSum_iff _).2 fun a ha ↦ ?_
  refine (eq_zero_iff_forall_mem_stateSpace_star_mul_self (a := a)).2 fun φ hφ ↦ ?_
  let ω := statePositiveLinearMap ⟨φ, hφ⟩
  exact ω.apply_star_mul_self_eq_zero_of_gnsNonUnitalStarAlgHom_eq_zero (ha ⟨φ, hφ⟩)

/-- The universal representation is isometric. -/
@[simp]
theorem norm_universalRepresentation_apply (a : A) :
    ‖universalRepresentation A a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (universalRepresentation A) (universalRepresentation_injective A) a

variable (A) in
/-- The universal representation is an isometry. -/
theorem isometry_universalRepresentation :
    Isometry (universalRepresentation A) :=
  NonUnitalStarAlgHom.isometry (universalRepresentation A) (universalRepresentation_injective A)

end UniversalWithOrder

section UnitalWithOrder

variable (B : Type u) [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The **unital universal representation** of a unital C⋆-algebra `B` on
`universalHilbertSpace B`. -/
def universalUnitalRepresentation :
    B →⋆ₐ[ℂ] (universalHilbertSpace B →L[ℂ] universalHilbertSpace B) :=
  (isNondegenerate_universalRepresentation B).toStarAlgHom

@[simp]
theorem coe_universalUnitalRepresentation :
    ⇑(universalUnitalRepresentation B) = universalRepresentation B :=
  (isNondegenerate_universalRepresentation B).coe_toStarAlgHom

@[simp]
theorem toNonUnitalStarAlgHom_universalUnitalRepresentation :
    (universalUnitalRepresentation B).toNonUnitalStarAlgHom = universalRepresentation B :=
  (isNondegenerate_universalRepresentation B).toNonUnitalStarAlgHom_toStarAlgHom

theorem universalUnitalRepresentation_injective :
    Function.Injective (universalUnitalRepresentation B) := by
  rw [coe_universalUnitalRepresentation]
  exact universalRepresentation_injective B

end UnitalWithOrder

section GelfandNaimark

/-- **Gelfand–Naimark theorem.** Every complex C⋆-algebra `A`, possibly nonunital and nonseparable,
admits a faithful nondegenerate representation on a complete complex Hilbert space in the universe
of `A`. -/
theorem exists_faithful_nondegenerate_representation (A : Type u) [NonUnitalCStarAlgebra A] :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)),
      Function.Injective π ∧ π.IsNondegenerate := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  exact ⟨universalHilbertSpace A, inferInstance, inferInstance, inferInstance,
    universalRepresentation A, universalRepresentation_injective A,
    isNondegenerate_universalRepresentation A⟩

/-- **Unital Gelfand–Naimark theorem.** Every unital complex C⋆-algebra `B` admits a faithful
unital representation on a complete complex Hilbert space in the universe of `B`. -/
theorem exists_faithful_unital_representation (B : Type u) [CStarAlgebra B] :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (π : B →⋆ₐ[ℂ] (K →L[ℂ] K)),
      Function.Injective π := by
  let := CStarAlgebra.spectralOrder B
  have := CStarAlgebra.spectralOrderedRing B
  exact ⟨universalHilbertSpace B, inferInstance, inferInstance, inferInstance,
    universalUnitalRepresentation B, universalUnitalRepresentation_injective B⟩

/-- **Concrete Gelfand–Naimark realization.** Every complex C⋆-algebra `A` is isometrically
`⋆`-isomorphic (`StarAlgEquiv.isometry`) to a norm-closed `⋆`-subalgebra of `K →L[ℂ] K` for some
complete complex Hilbert space `K` in the universe of `A`. -/
theorem exists_starAlgEquiv_nonUnitalStarSubalgebra (A : Type u) [NonUnitalCStarAlgebra A] :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (S : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K)),
      IsClosed (S : Set (K →L[ℂ] K)) ∧ Nonempty (A ≃⋆ₐ[ℂ] S) := by
  obtain ⟨K, _, _, _, π, hπ, -⟩ := exists_faithful_nondegenerate_representation A
  refine ⟨K, inferInstance, inferInstance, inferInstance, π.range, π.isClosed_range,
    ⟨StarAlgEquiv.ofBijective π.rangeRestrict
      ⟨fun _ _ h ↦ hπ (congrArg Subtype.val h), π.rangeRestrict_surjective⟩⟩⟩

/-- **Unital concrete Gelfand–Naimark realization.** Every unital complex C⋆-algebra `B` is
isometrically `⋆`-isomorphic to a norm-closed unital `⋆`-subalgebra of `K →L[ℂ] K` for some complete
complex Hilbert space `K` in the universe of `B`. -/
theorem exists_starAlgEquiv_starSubalgebra (B : Type u) [CStarAlgebra B] :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (S : StarSubalgebra ℂ (K →L[ℂ] K)),
      IsClosed (S : Set (K →L[ℂ] K)) ∧ Nonempty (B ≃⋆ₐ[ℂ] S) := by
  obtain ⟨K, _, _, _, π, hπ⟩ := exists_faithful_unital_representation B
  refine ⟨K, inferInstance, inferInstance, inferInstance, π.range, π.isClosed_range,
    ⟨StarAlgEquiv.ofBijective π.rangeRestrict
      ⟨fun _ _ h ↦ hπ (congrArg Subtype.val h), π.rangeRestrict_surjective⟩⟩⟩

/-- Every separable complex C⋆-algebra `A` (including `0`) admits a faithful nondegenerate
representation on a separable complete complex Hilbert space in the universe of `A`. -/
theorem exists_faithful_nondegenerate_representation_separable (A : Type u)
    [NonUnitalCStarAlgebra A] [SeparableSpace A] :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (_ : SeparableSpace K) (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)),
      Function.Injective π ∧ π.IsNondegenerate := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  have ⟨ω, hω⟩ : ∃ ω : A →ₚ[ℂ] ℂ, ∀ a, ω (star a * a) = 0 → a = 0 := by
    by_cases hA : Nontrivial A
    · obtain ⟨ω, -, hω⟩ := exists_positiveLinearMap_norm_eq_one_faithful (A := A)
      exact ⟨ω, fun a ha ↦ (hω a).1 ha⟩
    · have : Subsingleton A := not_nontrivial_iff_subsingleton.1 hA
      exact ⟨0, fun a _ ↦ Subsingleton.elim a 0⟩
  exact ⟨ω.GNS, inferInstance, inferInstance, inferInstance, inferInstance,
    ω.gnsNonUnitalStarAlgHom, ω.gnsNonUnitalStarAlgHom_injective hω,
    ω.isNondegenerate_gnsNonUnitalStarAlgHom⟩

/-- Every nontrivial separable unital complex C⋆-algebra `B` admits a faithful unital representation
on a separable complete complex Hilbert space in the universe of `B` with a unit cyclic vector. -/
theorem exists_faithful_cyclic_representation_separable (B : Type u)
    [CStarAlgebra B] [SeparableSpace B] [Nontrivial B] :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (_ : SeparableSpace K) (π : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (ξ : K),
      Function.Injective π ∧ ‖ξ‖ = 1 ∧ DenseRange (fun b ↦ π b ξ) := by
  let := CStarAlgebra.spectralOrder B
  have := CStarAlgebra.spectralOrderedRing B
  obtain ⟨ω, hω_norm, hω⟩ := exists_positiveLinearMap_norm_eq_one_faithful (A := B)
  have hmem : StrongDual.toWeakDual (PositiveContinuousLinearMap.ofClass ω : B →L[ℂ] ℂ) ∈
      stateSpace B :=
    (PositiveContinuousLinearMap.ofClass ω).toWeakDual_mem_stateSpace_iff.2 hω_norm
  have hω1 : ω 1 = 1 := map_one_of_mem_stateSpace hmem
  exact ⟨ω.GNS, inferInstance, inferInstance, inferInstance, inferInstance,
    ω.gnsStarAlgHom, ω.gnsVector,
    ω.gnsNonUnitalStarAlgHom_injective fun a ha ↦ (hω a).1 ha,
    ω.norm_gnsVector hω1, ω.denseRange_gnsStarAlgHom_gnsVector⟩

/-- **Separable faithful representation on `ℓ²(ℕ)`.** Every nontrivial separable complex
C⋆-algebra, possibly nonunital, admits a faithful nondegenerate representation on
`lp (fun _ : ℕ ↦ ℂ) 2`: take the GNS representation of a faithful state, amplify it countably many
times to obtain an infinite-dimensional separable carrier, and conjugate along a `ℕ`-indexed
Hilbert basis. -/
theorem exists_injective_nondegenerate_representation_lp
    {A : Type*} [NonUnitalCStarAlgebra A] [SeparableSpace A] [Nontrivial A] :
    ∃ π : A →⋆ₙₐ[ℂ] (lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2),
      Function.Injective π ∧ π.IsNondegenerate := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  obtain ⟨ω, -, hω⟩ := exists_positiveLinearMap_norm_eq_one_faithful (A := A)
  set π₀ := ω.gnsNonUnitalStarAlgHom
  have hπ₀_inj : Function.Injective π₀ :=
    ω.gnsNonUnitalStarAlgHom_injective fun a ha ↦ (hω a).1 ha
  have hπ₀_nd : π₀.IsNondegenerate := ω.isNondegenerate_gnsNonUnitalStarAlgHom
  have : Nontrivial ω.GNS := by
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    have hπa : π₀ a ≠ 0 := (map_ne_zero_iff π₀ hπ₀_inj).2 ha
    obtain ⟨ξ, hξ⟩ : ∃ ξ, π₀ a ξ ≠ 0 := by
      contrapose! hπa
      ext η
      exact hπa η
    exact ⟨⟨π₀ a ξ, 0, hξ⟩⟩
  obtain ⟨e⟩ := nonempty_linearIsometryEquiv_lp_of_infinite ℂ (fun _ : ℕ ↦ ω.GNS)
  refine ⟨e.conjStarAlgEquiv.toNonUnitalStarAlgHom.comp (π₀.ampliation ℕ), ?_, ?_⟩
  · exact e.conjStarAlgEquiv.injective.comp ((π₀.injective_ampliation_iff ℕ).2 hπ₀_inj)
  · exact (NonUnitalStarAlgHom.isNondegenerate_comp_conjStarAlgEquiv_iff e _).2
      (hπ₀_nd.ampliation ℕ)

/-- Every nontrivial separable unital complex C⋆-algebra admits a faithful unital representation on
`lp (fun _ : ℕ ↦ ℂ) 2`. -/
theorem exists_injective_unital_representation_lp
    {B : Type*} [CStarAlgebra B] [SeparableSpace B] [Nontrivial B] :
    ∃ π : B →⋆ₐ[ℂ] (lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2),
      Function.Injective π := by
  obtain ⟨π, hπ_inj, hπ_nd⟩ := exists_injective_nondegenerate_representation_lp (A := B)
  refine ⟨hπ_nd.toStarAlgHom, ?_⟩
  rwa [hπ_nd.coe_toStarAlgHom]

end GelfandNaimark

end TauCeti
