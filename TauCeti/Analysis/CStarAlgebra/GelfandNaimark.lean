/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Nondegenerate
public import TauCeti.Analysis.CStarAlgebra.Representation.HilbertSum
public import TauCeti.Analysis.CStarAlgebra.State.Separation
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# The universal representation and the Gelfand–Naimark theorem

Every C⋆-algebra `A`, unital or not and separable or not, embeds isometrically and nondegenerately
as a C⋆-subalgebra of bounded operators `K →L[ℂ] K` on a complex Hilbert space `K` in the same
universe as `A`.

The concrete model is the **universal representation** `TauCeti.universalRepresentation A`: the
Hilbert direct sum over all states `φ : stateSpace A` of the GNS representations
`(statePositiveLinearMap φ).gnsNonUnitalStarAlgHom` on
`TauCeti.UniversalHilbertSpace A = lp (fun φ : stateSpace A ↦ (statePositiveLinearMap φ).GNS) 2`.
Each GNS summand is nondegenerate (`PositiveLinearMap.isNondegenerate_gnsNonUnitalStarAlgHom`), so
their Hilbert direct sum is nondegenerate (`NonUnitalStarAlgHom.isNondegenerate_hilbertSum_iff`).
If `universalRepresentation A a = 0`, then in every state `φ` the vector `[a * star a]` vanishes in
the GNS space, hence `φ (star (a * star a) * (a * star a)) = 0`; state separation
(`TauCeti.forall_mem_stateSpace_star_mul_self_eq_zero_iff`) then forces `a * star a = 0` and thus
`a = 0`. For `Subsingleton A`, `stateSpace A` is empty and `UniversalHilbertSpace A` is the zero
Hilbert space, so no case split is needed.

When `A` is separable, a single positive functional (zero when `Subsingleton A`, and a faithful
state from `TauCeti.exists_faithful_mem_stateSpace` when `Nontrivial A`) already has an injective
nondegenerate GNS representation on a separable Hilbert space.

## Main declarations

* `TauCeti.UniversalHilbertSpace`, `TauCeti.universalRepresentation`, `TauCeti.universalStarAlgHom`:
  the universal Hilbert space and universal (nonunital / unital) representation of `A`, proved
  injective, isometric, and nondegenerate.
* `TauCeti.exists_faithful_nondegenerate_representation` and
  `TauCeti.exists_faithful_representation`: the Gelfand–Naimark representation theorem for arbitrary
  nonunital and unital C⋆-algebras.
* `TauCeti.exists_positiveLinearMap_gnsNonUnitalStarAlgHom_injective`,
  `TauCeti.exists_faithful_nondegenerate_separable_representation`, and
  `TauCeti.exists_faithful_separable_representation`: faithful nondegenerate representations of
  separable C⋆-algebras on separable Hilbert spaces.

## References

* I. M. Gelfand and M. A. Naimark, *On the imbedding of normed rings into the ring of operators in
  Hilbert space*, Mat. Sbornik 12 (1943), 197–213.
* Jesse Peterson, *Notes on operator algebras*, Section 4.1 (Corollary 4.1.7).
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Academic Press (1990), Theorem 3.4.1.
-/

public section

noncomputable section

open WeakDual
open scoped ComplexOrder ENNReal InnerProductSpace lp

namespace TauCeti

universe u

section Universal

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- If a state `φ` is faithful (`0 < φ (star a * a)` for `a ≠ 0`), its GNS representation is
injective. -/
theorem gnsNonUnitalStarAlgHom_statePositiveLinearMap_injective (φ : stateSpace A)
    (hφ : ∀ a ≠ 0, 0 < (φ : WeakDual ℂ A) (star a * a)) :
    Function.Injective (statePositiveLinearMap φ).gnsNonUnitalStarAlgHom := by
  refine (statePositiveLinearMap φ).gnsNonUnitalStarAlgHom_injective fun a ha ↦ ?_
  by_contra ha0
  exact (hφ a ha0).ne' (by simpa using ha)

variable (A) in
/-- The **universal Hilbert space** of a C⋆-algebra `A`: the `ℓ²` Hilbert direct sum of the GNS
Hilbert spaces of all states of `A`. -/
abbrev UniversalHilbertSpace : Type u :=
  lp (fun φ : stateSpace A ↦ (statePositiveLinearMap φ).GNS) 2

variable (A) in
/-- The **universal representation** of a C⋆-algebra `A`: the Hilbert direct sum of the GNS
representations of all states of `A` on `UniversalHilbertSpace A`. -/
def universalRepresentation :
    A →⋆ₙₐ[ℂ] (UniversalHilbertSpace A →L[ℂ] UniversalHilbertSpace A) :=
  NonUnitalStarAlgHom.hilbertSum fun φ : stateSpace A ↦
    (statePositiveLinearMap φ).gnsNonUnitalStarAlgHom

/-- In each state coordinate `φ`, the universal representation acts by the GNS representation of
`φ`. -/
@[simp]
theorem universalRepresentation_apply_apply (a : A) (x : UniversalHilbertSpace A)
    (φ : stateSpace A) :
    universalRepresentation A a x φ =
      (statePositiveLinearMap φ).gnsNonUnitalStarAlgHom a (x φ) :=
  NonUnitalStarAlgHom.hilbertSum_apply_apply _ a x φ

/-- The universal representation of any C⋆-algebra is nondegenerate. -/
theorem isNondegenerate_universalRepresentation :
    (universalRepresentation A).IsNondegenerate :=
  NonUnitalStarAlgHom.isNondegenerate_hilbertSum_iff.2 fun φ ↦
    (statePositiveLinearMap φ).isNondegenerate_gnsNonUnitalStarAlgHom

/-- **Injectivity of the universal representation.** For every C⋆-algebra `A`,
`universalRepresentation A` is injective. -/
theorem universalRepresentation_injective :
    Function.Injective (universalRepresentation A) := by
  refine NonUnitalStarAlgHom.hilbertSum_injective_iff.2 fun a ha ↦ ?_
  have hmul : a * star a = 0 := by
    refine forall_mem_stateSpace_star_mul_self_eq_zero_iff.1 fun φ hφ ↦ ?_
    let s : stateSpace A := ⟨φ, hφ⟩
    have hvec : (statePositiveLinearMap s).toGNS (a * star a) = 0 := by
      simpa [PositiveLinearMap.toGNS_apply] using
        DFunLike.congr_fun (ha s) ((statePositiveLinearMap s).toGNS (star a))
    simpa using ((statePositiveLinearMap s).toGNS_eq_zero_iff (a * star a)).1 hvec
  exact mul_star_self_eq_zero.1 hmul

/-- The universal representation preserves norms: `‖universalRepresentation A a‖ = ‖a‖`. -/
@[simp]
theorem norm_universalRepresentation_apply (a : A) :
    ‖universalRepresentation A a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (universalRepresentation A) universalRepresentation_injective a

/-- The universal representation is an isometry. -/
theorem isometry_universalRepresentation :
    Isometry (universalRepresentation A) :=
  NonUnitalStarAlgHom.isometry (universalRepresentation A) universalRepresentation_injective

/-- Every separable C⋆-algebra `A` admits a positive linear functional whose GNS representation is
injective (and automatically nondegenerate on a separable Hilbert space). -/
theorem exists_positiveLinearMap_gnsNonUnitalStarAlgHom_injective
    [TopologicalSpace.SeparableSpace A] :
    ∃ f : A →ₚ[ℂ] ℂ, Function.Injective f.gnsNonUnitalStarAlgHom := by
  by_cases hsub : Subsingleton A
  · exact ⟨0, Function.injective_of_subsingleton _⟩
  · have : Nontrivial A := not_subsingleton_iff_nontrivial.1 hsub
    obtain ⟨φ, hφ, hfaith⟩ := exists_faithful_mem_stateSpace (A := A)
    exact ⟨statePositiveLinearMap ⟨φ, hφ⟩,
      gnsNonUnitalStarAlgHom_statePositiveLinearMap_injective ⟨φ, hφ⟩ hfaith⟩

end Universal

section UniversalUnital

variable (B : Type u) [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The **unital universal representation** of a unital C⋆-algebra `B` on
`UniversalHilbertSpace B`, obtained from nondegeneracy of `universalRepresentation B`. -/
def universalStarAlgHom :
    B →⋆ₐ[ℂ] (UniversalHilbertSpace B →L[ℂ] UniversalHilbertSpace B) :=
  (isNondegenerate_universalRepresentation (A := B)).toStarAlgHom

@[simp]
theorem toNonUnitalStarAlgHom_universalStarAlgHom :
    (universalStarAlgHom B).toNonUnitalStarAlgHom = universalRepresentation B :=
  NonUnitalStarAlgHom.IsNondegenerate.toNonUnitalStarAlgHom_toStarAlgHom _

@[simp]
theorem coe_universalStarAlgHom :
    ⇑(universalStarAlgHom B) = universalRepresentation B :=
  NonUnitalStarAlgHom.IsNondegenerate.coe_toStarAlgHom _

/-- The unital universal representation is injective. -/
theorem universalStarAlgHom_injective :
    Function.Injective (universalStarAlgHom B) := by
  rw [coe_universalStarAlgHom]
  exact universalRepresentation_injective (A := B)

/-- The unital universal representation preserves norms. -/
theorem norm_universalStarAlgHom_apply (b : B) :
    ‖universalStarAlgHom B b‖ = ‖b‖ :=
  NonUnitalStarAlgHom.norm_map (universalStarAlgHom B) (universalStarAlgHom_injective B) b

/-- The unital universal representation is an isometry. -/
theorem isometry_universalStarAlgHom :
    Isometry (universalStarAlgHom B) := by
  rw [coe_universalStarAlgHom]
  exact isometry_universalRepresentation (A := B)

end UniversalUnital

section GelfandNaimark

/-- **Gelfand–Naimark representation theorem.** Every C⋆-algebra `A` (possibly nonunital and
nonseparable) admits an injective nondegenerate representation on a complete complex Hilbert space
in the same universe as `A`. -/
theorem exists_faithful_nondegenerate_representation (A : Type u) [NonUnitalCStarAlgebra A] :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)), Function.Injective π ∧
        Dense (Submodule.span ℂ (⋃ a, Set.range (π a)) : Set K) := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  exact ⟨UniversalHilbertSpace A, inferInstance, inferInstance, inferInstance,
    universalRepresentation A, universalRepresentation_injective,
    NonUnitalStarAlgHom.isNondegenerate_iff_dense.1 isNondegenerate_universalRepresentation⟩

/-- **Unital Gelfand–Naimark representation theorem.** Every unital C⋆-algebra `B` admits an
injective unital `⋆`-representation on a complete complex Hilbert space in the same universe as
`B`. -/
theorem exists_faithful_representation (B : Type u) [CStarAlgebra B] :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (π : B →⋆ₐ[ℂ] (K →L[ℂ] K)), Function.Injective π := by
  let := CStarAlgebra.spectralOrder B
  have := CStarAlgebra.spectralOrderedRing B
  exact ⟨UniversalHilbertSpace B, inferInstance, inferInstance, inferInstance,
    universalStarAlgHom B, universalStarAlgHom_injective B⟩

/-- **Separable Gelfand–Naimark representation theorem.** Every separable C⋆-algebra `A` (possibly
nonunital) admits an injective nondegenerate representation on a separable complete complex Hilbert
space in the same universe as `A`. -/
theorem exists_faithful_nondegenerate_separable_representation (A : Type u)
    [NonUnitalCStarAlgebra A] [TopologicalSpace.SeparableSpace A] :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (_ : TopologicalSpace.SeparableSpace K) (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)),
        Function.Injective π ∧ π.IsNondegenerate := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  obtain ⟨f, hf⟩ := exists_positiveLinearMap_gnsNonUnitalStarAlgHom_injective (A := A)
  exact ⟨f.GNS, inferInstance, inferInstance, inferInstance, inferInstance,
    f.gnsNonUnitalStarAlgHom, hf, f.isNondegenerate_gnsNonUnitalStarAlgHom⟩

/-- **Unital separable Gelfand–Naimark representation theorem.** Every separable unital C⋆-algebra
`B` admits an injective unital `⋆`-representation on a separable complete complex Hilbert space in
the same universe as `B`. -/
theorem exists_faithful_separable_representation (B : Type u)
    [CStarAlgebra B] [TopologicalSpace.SeparableSpace B] :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (_ : TopologicalSpace.SeparableSpace K) (π : B →⋆ₐ[ℂ] (K →L[ℂ] K)),
        Function.Injective π := by
  obtain ⟨K, _, _, _, _, π, hπ_inj, hπ_nondeg⟩ :=
    exists_faithful_nondegenerate_separable_representation B
  exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance,
    hπ_nondeg.toStarAlgHom, by simpa using hπ_inj⟩

end GelfandNaimark

end TauCeti
