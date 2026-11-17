/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import TauCeti.Analysis.CStarAlgebra.Representation.HilbertSum
public import TauCeti.Analysis.CStarAlgebra.State.Space
import TauCeti.Analysis.CStarAlgebra.GNS.Nondegenerate
import TauCeti.Analysis.CStarAlgebra.State.Separation

/-!
# The universal GNS representation of a C⋆-algebra

For a possibly nonunital, possibly nonseparable C⋆-algebra `A` carrying its C⋆-order,
`TauCeti.gnsUniversalRepresentation A` is the concrete **universal GNS representation**: the
Hilbert direct sum (`NonUnitalStarAlgHom.hilbertSum`) of the GNS representations
`PositiveLinearMap.gnsNonUnitalStarAlgHom` over all states `φ : stateSpace A`.

Combining `PositiveLinearMap.isNondegenerate_gnsNonUnitalStarAlgHom` with state separation
(`TauCeti.eq_zero_of_forall_mem_stateSpace_apply_star_mul_self_eq_zero`), this representation is
nondegenerate (`isNondegenerate_gnsUniversalRepresentation`), injective
(`gnsUniversalRepresentation_injective`), and hence isometric
(`isometry_gnsUniversalRepresentation`). When `A` is trivial, its state space is empty and the
Hilbert direct sum is the zero Hilbert space, on which the zero representation is injective and
nondegenerate.

For the order-free existential Gelfand–Naimark theorems, see
`TauCeti.CStarAlgebra.exists_faithful_nondegenerate_representation` and
`TauCeti.CStarAlgebra.exists_faithful_representation` in
`TauCeti.Analysis.CStarAlgebra.Representation.GNS`.

## Main declarations

* `TauCeti.gnsUniversalRepresentation`: the Hilbert direct sum of the GNS representations over
  `stateSpace A`, with coordinate, `lp.evalCLM`, and `lp.single` lemmas.
* `TauCeti.isNondegenerate_gnsUniversalRepresentation`: `gnsUniversalRepresentation A` is
  nondegenerate.
* `TauCeti.gnsUniversalRepresentation_injective`: `gnsUniversalRepresentation A` is faithful.
* `TauCeti.isometry_gnsUniversalRepresentation` and `TauCeti.norm_gnsUniversalRepresentation_apply`:
  `gnsUniversalRepresentation A` is isometric.

## References

* I. M. Gelfand and M. A. Naimark, *On the imbedding of normed rings into the ring of operators in
  Hilbert space*, Mat. Sbornik 12 (1943), 197–213.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Academic Press, 1990, Section 3.4
  (Theorem 3.4.1).
* G. K. Pedersen, *C⋆-Algebras and their Automorphism Groups*, Section 3.7.
* J. Peterson, *Notes on von Neumann algebras* (2013), Theorem 4.1.6, pp. 57–58.
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
states `φ : stateSpace A` of their GNS representations
`(StateSpace.toPositiveLinearMap φ).gnsNonUnitalStarAlgHom` on
`(StateSpace.toPositiveLinearMap φ).GNS`. -/
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

/-- Coordinate evaluation in state `φ` intertwines `gnsUniversalRepresentation A a` with the GNS
representation of `φ`. -/
@[simp]
theorem evalCLM_comp_gnsUniversalRepresentation_apply (a : A) (φ : stateSpace A) :
    lp.evalCLM ℂ (fun ψ : stateSpace A => (StateSpace.toPositiveLinearMap ψ).GNS) 2 φ ∘L
        gnsUniversalRepresentation A a =
      (StateSpace.toPositiveLinearMap φ).gnsNonUnitalStarAlgHom a ∘L
        lp.evalCLM ℂ (fun ψ : stateSpace A => (StateSpace.toPositiveLinearMap ψ).GNS) 2 φ := by
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
@[simp]
theorem isNondegenerate_gnsUniversalRepresentation :
    (gnsUniversalRepresentation A).IsNondegenerate := by
  rw [gnsUniversalRepresentation_def, NonUnitalStarAlgHom.isNondegenerate_hilbertSum_iff]
  exact fun φ => (StateSpace.toPositiveLinearMap φ).isNondegenerate_gnsNonUnitalStarAlgHom

/-- **Faithfulness of the universal GNS representation.** The direct sum of the GNS
representations of all states of `A` is injective. -/
theorem gnsUniversalRepresentation_injective :
    Function.Injective (gnsUniversalRepresentation A) := by
  rw [gnsUniversalRepresentation_def, NonUnitalStarAlgHom.injective_hilbertSum_iff]
  intro a ha
  refine mul_star_self_eq_zero.1 <| eq_zero_of_forall_mem_stateSpace_apply_star_mul_self_eq_zero
    fun φ hφ => ?_
  let s : stateSpace A := ⟨φ, hφ⟩
  have hact : (StateSpace.toPositiveLinearMap s).toGNS (a * star a) = 0 := by
    simpa [PositiveLinearMap.toGNS_apply] using
      DFunLike.congr_fun (ha s) ((StateSpace.toPositiveLinearMap s).toGNS (star a))
  simpa using ((StateSpace.toPositiveLinearMap s).toGNS_eq_zero_iff (a * star a)).1 hact

/-- Two elements have the same image under `gnsUniversalRepresentation A` if and only if they are
equal. -/
@[simp]
theorem gnsUniversalRepresentation_inj {a b : A} :
    gnsUniversalRepresentation A a = gnsUniversalRepresentation A b ↔ a = b :=
  (gnsUniversalRepresentation_injective A).eq_iff

/-- `gnsUniversalRepresentation A a = 0` if and only if `a = 0`. -/
@[simp]
theorem gnsUniversalRepresentation_apply_eq_zero_iff (a : A) :
    gnsUniversalRepresentation A a = 0 ↔ a = 0 :=
  map_eq_zero_iff _ (gnsUniversalRepresentation_injective A)

/-- The universal GNS representation is an isometry. -/
theorem isometry_gnsUniversalRepresentation : Isometry (gnsUniversalRepresentation A) :=
  NonUnitalStarAlgHom.isometry _ (gnsUniversalRepresentation_injective A)

/-- The universal GNS representation preserves norms. -/
@[simp]
theorem norm_gnsUniversalRepresentation_apply (a : A) :
    ‖gnsUniversalRepresentation A a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map _ (gnsUniversalRepresentation_injective A) a

end UniversalRepresentation

end TauCeti
