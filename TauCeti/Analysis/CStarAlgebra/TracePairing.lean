/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.TracialFunctional
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.KZero

/-!
# The pairing of positive tracial functionals with `K₀`

Let `τ` be a positive tracial functional on a C⋆-algebra `A`. Its unnormalized matrix trace
`τ_m(p) = ∑ i, τ (p i i)` takes the same value on Murray–von Neumann equivalent matrix projections
of any sizes: if `vᴴ v = p` and `v vᴴ = q`, both traces are `∑ i k, τ (star (v k i) * v k i)`, by
the trace property of `τ` for rectangular matrices (`Matrix.sum_map_mul_comm`).
It is additive under block sum and nonnegative, so it induces an additive pairing
`τ_* : K₀(A) →+ ℝ` on the projection `K₀`-group (`TauCeti.PositiveTracialFunctional.kZeroPairing`).
The pairing is positive on classes of projections and natural: for a star homomorphism
`φ : A → B` and a positive tracial functional `τ` on `B`, `(τ ∘ φ)_* = τ_* ∘ φ_*`.

For unital `A` the projection `K₀`-group is the operator `K₀`-group, and the identity matrix of size
`k` pairs to `k * τ 1`, which is `k` for a tracial state. The unnormalized matrix trace is used,
so the pairing does not depend on the size in which a projection is written.

## Main definitions

* `TauCeti.PositiveTracialFunctional.kZeroPairing τ`: the pairing `τ_* : K₀(A) →+ ℝ`.

## Main statements

* `TauCeti.PositiveTracialFunctional.coe_kZeroPairing_of_mk`: `τ_* [p] = ∑ i, τ (p i i)`.
* `TauCeti.PositiveTracialFunctional.kZeroPairing_of_mk_nonneg`: `0 ≤ τ_* [p]`.
* `TauCeti.PositiveTracialFunctional.kZeroPairing_comp`: naturality, `(τ ∘ φ)_* = τ_* ∘ φ_*`.
* `TauCeti.PositiveTracialFunctional.kZeroPairing_of_mk_one`: `τ_* [1ₖ] = k * τ 1` for unital `A`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  §6.9.
-/

public section

open Matrix Algebra
open scoped ComplexOrder

namespace TauCeti

namespace PositiveTracialFunctional

variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τ : PositiveTracialFunctional A) {m n : Type*} [Fintype m] [Fintype n]

/-- The unnormalized matrix trace of a matrix projection is a nonnegative real number. -/
theorem sum_map_nonneg {p : Matrix m m A} (hp : IsStarProjection p) : 0 ≤ ∑ i, τ (p i i) :=
  Finset.sum_nonneg fun i _ ↦ τ.toPositiveLinearMap.map_nonneg (hp.diag_nonneg i)

/-- The unnormalized matrix trace of a block sum is the sum of the traces. -/
private theorem sum_map_fromBlocks (p : Matrix m m A) (q : Matrix n n A) :
    ∑ i, τ (fromBlocks p 0 0 q i i) = ∑ i, τ (p i i) + ∑ k, τ (q k k) := by
  simp [Fintype.sum_sum_type]

/-- The real part of the unnormalized matrix trace, as a function on `V(A)`. -/
private noncomputable def pairingFun : ProjectionMonoid A → ℝ :=
  ProjectionMonoid.lift (fun p _ ↦ (∑ i, τ (p i i)).re)
    fun _ _ h ↦ congrArg Complex.re (h.sum_map_eq τ τ.map_mul_comm)

private theorem pairingFun_mk {p : Matrix m m A} (hp : IsStarProjection p) :
    τ.pairingFun (ProjectionMonoid.mk p hp) = (∑ i, τ (p i i)).re := by
  rw [pairingFun, ProjectionMonoid.lift_mk_of_equiv _ _ hp (Fintype.equivFin m)]
  exact congrArg Complex.re
    ((hp.isMurrayVonNeumannEquivalent_reindex _).sum_map_eq τ τ.map_mul_comm).symm

/-- The pairing on `V(A)`, as an additive monoid homomorphism. -/
private noncomputable def pairingMonoidHom : ProjectionMonoid A →+ ℝ where
  toFun := τ.pairingFun
  map_zero' := by
    rw [← ProjectionMonoid.mk_zero (m := Fin 0), pairingFun_mk]
    simp
  map_add' x y := by
    induction x using ProjectionMonoid.ind with | mk k p hp => ?_
    induction y using ProjectionMonoid.ind with | mk l q hq => ?_
    rw [← ProjectionMonoid.mk_fromBlocks, pairingFun_mk, pairingFun_mk, pairingFun_mk,
      sum_map_fromBlocks, Complex.add_re]

/-- The **trace pairing** `τ_* : K₀(A) →+ ℝ` of a positive tracial functional with the projection
`K₀`-group, induced by the unnormalized matrix trace `τ_m(p) = ∑ i, τ (p i i)`. -/
noncomputable def kZeroPairing : ProjectionKZero A →+ ℝ :=
  GrothendieckAddGroup.lift τ.pairingMonoidHom

-- Not `@[simp]`: the simp normal form of `Algebra.GrothendieckAddGroup.of x` is
-- `AddLocalization.addMonoidOf ⊤ x`, as for `TauCeti.ProjectionKZero.map_of_mk`.
/-- The trace pairing sends the class of `p` to the real part of `∑ i, τ (p i i)`. -/
theorem kZeroPairing_of_mk {p : Matrix m m A} (hp : IsStarProjection p) :
    τ.kZeroPairing (GrothendieckAddGroup.of (ProjectionMonoid.mk p hp)) = (∑ i, τ (p i i)).re :=
  (GrothendieckAddGroup.lift_apply_of _ _).trans (τ.pairingFun_mk hp)

/-- The unnormalized matrix trace of a projection is real, and it is the trace pairing:
`τ_* [p] = ∑ i, τ (p i i)`. -/
theorem coe_kZeroPairing_of_mk {p : Matrix m m A} (hp : IsStarProjection p) :
    (τ.kZeroPairing (GrothendieckAddGroup.of (ProjectionMonoid.mk p hp)) : ℂ) =
      ∑ i, τ (p i i) := by
  rw [kZeroPairing_of_mk]
  exact Complex.ext rfl (by simpa using (Complex.nonneg_iff.1 (τ.sum_map_nonneg hp)).2)

/-- **Positivity.** The trace pairing is nonnegative on classes of projections. -/
theorem kZeroPairing_of_mk_nonneg {p : Matrix m m A} (hp : IsStarProjection p) :
    0 ≤ τ.kZeroPairing (GrothendieckAddGroup.of (ProjectionMonoid.mk p hp)) := by
  rw [kZeroPairing_of_mk]
  exact (Complex.nonneg_iff.1 (τ.sum_map_nonneg hp)).1

/-- **Naturality.** For a star homomorphism `φ : A → B` and a positive tracial functional `τ` on
`B`, the pairing of `τ ∘ φ` is the pairing of `τ` composed with `φ_* : K₀(A) → K₀(B)`. -/
theorem kZeroPairing_comp {F : Type*} [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B]
    [StarHomClass F A B] (τ : PositiveTracialFunctional B) (φ : F) :
    (τ.comp φ).kZeroPairing =
      τ.kZeroPairing.comp (ProjectionKZero.map (NonUnitalStarRingHom.ofClass φ)) := by
  refine GrothendieckAddGroup.addHom_ext fun x ↦ ?_
  induction x using ProjectionMonoid.ind with
  | mk k p hp =>
    rw [AddMonoidHom.comp_apply, ProjectionKZero.map_of_mk, kZeroPairing_of_mk,
      kZeroPairing_of_mk]
    simp only [comp_apply, Matrix.map_apply, NonUnitalStarRingHom.coe_ofClass]

/-- Over a unital C⋆-algebra the identity matrix of size `k` pairs to `k * τ 1`. -/
theorem kZeroPairing_of_mk_one {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : PositiveTracialFunctional A) (k : ℕ) :
    τ.kZeroPairing (GrothendieckAddGroup.of
      (ProjectionMonoid.mk (1 : Matrix (Fin k) (Fin k) A) (.one _))) = k * (τ 1).re := by
  rw [kZeroPairing_of_mk]
  simp

end PositiveTracialFunctional

end TauCeti
