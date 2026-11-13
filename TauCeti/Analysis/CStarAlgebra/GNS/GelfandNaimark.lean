/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Nondegenerate
public import TauCeti.Analysis.CStarAlgebra.Representation.HilbertSum
public import TauCeti.Analysis.CStarAlgebra.State.Space
import TauCeti.Analysis.CStarAlgebra.State.Separation

/-!
# The universal GNS representation and the Gelfand–Naimark theorem

Every C⋆-algebra `A`, possibly nonunital and nonseparable, is isometrically `⋆`-isomorphic to a
norm-closed `⋆`-subalgebra of bounded operators on a complete complex Hilbert space in the same
universe, acting nondegenerately.

When `A` carries its C⋆-order, `TauCeti.gnsUniversalRepresentation A` is the concrete universal
representation of `A`: the Hilbert direct sum (`NonUnitalStarAlgHom.hilbertSum`) of the GNS
representations `PositiveLinearMap.gnsNonUnitalStarAlgHom` over all states `φ : stateSpace A`.
Combining `PositiveLinearMap.isNondegenerate_gnsNonUnitalStarAlgHom` with state norm attainment
(`TauCeti.exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq_of_ne_zero`), this representation is
injective (hence isometric) and nondegenerate; when `A` is trivial, its state space is empty and
the Hilbert direct sum is the zero Hilbert space, on which the zero representation is injective and
nondegenerate.

Installing `CStarAlgebra.spectralOrder A` locally gives the order-free Gelfand–Naimark existence
theorems:

* `TauCeti.exists_faithful_nondegenerate_representation`: every `NonUnitalCStarAlgebra A` in
  `Type u` admits an injective nondegenerate `⋆`-representation on a complete complex Hilbert
  space in `Type u`.
* `TauCeti.exists_faithful_unital_representation`: every unital `CStarAlgebra B` in `Type u` admits
  an injective unital `⋆`-representation `B →⋆ₐ[ℂ] (K →L[ℂ] K)` on a complete complex Hilbert
  space `K : Type u`.

## References

* I. M. Gelfand and M. A. Naimark, *On the imbedding of normed rings into the ring of operators in
  Hilbert space*, Mat. Sbornik 12 (1943), 197–213.
* J. Peterson, *Notes on Operator Algebras*, Theorem 4.1.6 and Corollary 4.1.7, pp. 57–58.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Academic Press, 1990, Theorem 3.4.1.
-/

public section

noncomputable section

universe u

open WeakDual
open scoped ComplexOrder

namespace TauCeti

section UniversalRepresentation

variable (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The **universal GNS representation** of a C⋆-algebra `A`: the Hilbert direct sum over all
states `φ : stateSpace A` of their GNS representations `(StateSpace.toPositiveLinearMap φ).GNS`. -/
def gnsUniversalRepresentation :
    A →⋆ₙₐ[ℂ]
      (lp (fun φ : stateSpace A => (StateSpace.toPositiveLinearMap φ).GNS) 2 →L[ℂ]
        lp (fun φ : stateSpace A => (StateSpace.toPositiveLinearMap φ).GNS) 2) :=
  NonUnitalStarAlgHom.hilbertSum fun φ : stateSpace A =>
    (StateSpace.toPositiveLinearMap φ).gnsNonUnitalStarAlgHom

/-- Unfolding lemma: `gnsUniversalRepresentation A` is the `hilbertSum` of the GNS representations
of all states of `A`. -/
theorem gnsUniversalRepresentation_def :
    gnsUniversalRepresentation A =
      NonUnitalStarAlgHom.hilbertSum fun φ : stateSpace A =>
        (StateSpace.toPositiveLinearMap φ).gnsNonUnitalStarAlgHom :=
  (rfl)

/-- The universal GNS representation acts in each state coordinate `φ` by the GNS representation of
`φ`. -/
@[simp]
theorem gnsUniversalRepresentation_apply_apply (a : A)
    (x : lp (fun φ : stateSpace A => (StateSpace.toPositiveLinearMap φ).GNS) 2)
    (φ : stateSpace A) :
    gnsUniversalRepresentation A a x φ =
      (StateSpace.toPositiveLinearMap φ).gnsNonUnitalStarAlgHom a (x φ) := by
  simp [gnsUniversalRepresentation]

/-- On a single-state coordinate vector `lp.single 2 φ v`, the universal GNS representation acts in
coordinate `φ` by the GNS representation of `φ`. -/
@[simp]
theorem gnsUniversalRepresentation_apply_single [DecidableEq (stateSpace A)] (a : A)
    (φ : stateSpace A) (v : (StateSpace.toPositiveLinearMap φ).GNS) :
    gnsUniversalRepresentation A a (lp.single 2 φ v) =
      lp.single 2 φ ((StateSpace.toPositiveLinearMap φ).gnsNonUnitalStarAlgHom a v) := by
  simp [gnsUniversalRepresentation]

/-- The universal GNS representation is nondegenerate, even when `A` has no unit or is zero. -/
theorem isNondegenerate_gnsUniversalRepresentation :
    (gnsUniversalRepresentation A).IsNondegenerate :=
  (NonUnitalStarAlgHom.isNondegenerate_hilbertSum_iff _).2 fun φ =>
    (StateSpace.toPositiveLinearMap φ).isNondegenerate_gnsNonUnitalStarAlgHom

/-- **Faithfulness of the universal GNS representation.** The direct sum of the GNS
representations of all states of `A` is injective. -/
theorem gnsUniversalRepresentation_injective :
    Function.Injective (gnsUniversalRepresentation A) := by
  refine (NonUnitalStarAlgHom.hilbertSum_injective_iff _).2 fun a ha => ?_
  by_contra ha0
  have hmul : a * star a ≠ 0 := mul_star_self_eq_zero.not.2 ha0
  -- Choose a state witnessing `φ ((a * a⋆)⋆ * (a * a⋆)) = ‖a * a⋆‖ ^ 2 ≠ 0`; then in the `φ`-th
  -- GNS summand, `π_φ(a)` sends `[a⋆]` to `[a * a⋆] ≠ 0`.
  obtain ⟨φ, hφ, hφ_val⟩ := exists_mem_stateSpace_apply_star_mul_self_eq_norm_sq_of_ne_zero hmul
  let s : stateSpace A := ⟨φ, hφ⟩
  have hact : (StateSpace.toPositiveLinearMap s).toGNS (a * star a) = 0 := by
    simpa [PositiveLinearMap.toGNS_apply] using
      DFunLike.congr_fun (ha s) ((StateSpace.toPositiveLinearMap s).toGNS (star a))
  have hzero : φ (star (a * star a) * (a * star a)) = 0 := by
    simpa using ((StateSpace.toPositiveLinearMap s).toGNS_eq_zero_iff (a * star a)).1 hact
  have hnorm_zero : (‖a * star a‖ ^ 2 : ℂ) = 0 := hφ_val.symm.trans hzero
  exact hmul (norm_eq_zero.1 (Complex.ofReal_eq_zero.1 (sq_eq_zero_iff.1 hnorm_zero)))

/-- The universal GNS representation is an isometry. -/
theorem isometry_gnsUniversalRepresentation : Isometry (gnsUniversalRepresentation A) :=
  NonUnitalStarAlgHom.isometry _ (gnsUniversalRepresentation_injective A)

/-- The universal GNS representation preserves norms. -/
@[simp]
theorem norm_gnsUniversalRepresentation_apply (a : A) :
    ‖gnsUniversalRepresentation A a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map _ (gnsUniversalRepresentation_injective A) a

end UniversalRepresentation

/-- **Gelfand–Naimark theorem.** Every C⋆-algebra `A`, possibly nonunital and nonseparable, admits
an injective nondegenerate `⋆`-representation on a complete complex Hilbert space in the universe
of `A`. -/
theorem exists_faithful_nondegenerate_representation (A : Type u) [NonUnitalCStarAlgebra A] :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)), Function.Injective π ∧ π.IsNondegenerate := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  exact ⟨lp (fun φ : stateSpace A => (StateSpace.toPositiveLinearMap φ).GNS) 2, inferInstance,
    inferInstance, inferInstance, gnsUniversalRepresentation A,
    gnsUniversalRepresentation_injective A, isNondegenerate_gnsUniversalRepresentation A⟩

/-- **Unital Gelfand–Naimark theorem.** Every unital C⋆-algebra `B`, possibly nonseparable or
zero, admits an injective unital `⋆`-representation on a complete complex Hilbert space in the
universe of `B`. -/
theorem exists_faithful_unital_representation (B : Type u) [CStarAlgebra B] :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (π : B →⋆ₐ[ℂ] (K →L[ℂ] K)), Function.Injective π := by
  obtain ⟨K, _, _, _, π, hπ_inj, hπ_nondeg⟩ := exists_faithful_nondegenerate_representation B
  exact ⟨K, inferInstance, inferInstance, inferInstance, hπ_nondeg.toStarAlgHom,
    by rwa [hπ_nondeg.coe_toStarAlgHom]⟩

end TauCeti
