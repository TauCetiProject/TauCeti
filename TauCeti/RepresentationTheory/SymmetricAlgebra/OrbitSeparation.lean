/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.RingTheory.Invariant.OrbitSeparation

/-!
# Invariant polynomials of a finite linear group separate orbits

Let a finite group `G` act linearly on a vector space `V` over a field `K` through a
representation `ρ`, and so on the polynomial functions `Sym(V*)` through the contragredient
representation `ρ.dual`. A vector `v : V` defines the evaluation
`SymmetricAlgebra.lift (Module.Dual.eval K V v) : Sym(V*) →ₐ[K] K`, which sends a linear form `φ`
to `φ v`. Translating a polynomial by `g` corresponds to evaluating at `ρ g⁻¹ v`.

The invariant polynomials `Sym(V*)^G` separate the orbits of `G` on `V`: two vectors have the same
value on every invariant exactly when they lie in the same orbit, and vectors in distinct orbits
are separated by an invariant with values `0` and `1`. This is the specialization of
`FixedPoints.forall_mem_subalgebra_eq_iff` to evaluations at vectors; it needs neither
finite-dimensionality nor any hypothesis on the characteristic of `K`.

Since the orbit of `0` is `{0}`, the only vector at which every homogeneous invariant of positive
degree vanishes is `0`. Geometrically, the fibre of the quotient map `V → V/G` over the vertex,
the point cut out by the invariants of positive degree, consists of the origin alone. Over an
algebraically closed field the Nullstellensatz turns this into the equality of the radical of the
Hilbert ideal `Sym(V*)^G₊ · Sym(V*)` with the ideal of positive-degree elements, which is how the
dimension of the invariant ring at its vertex is compared with that of `Sym(V*)`.

## Main results

* `Representation.lift_eval_symmetricAlgebra_dual`: evaluating a translate at `v` is evaluating at
  `ρ g⁻¹ v`.
* `Representation.exists_mem_symmetricAlgebraInvariants_lift_eval_eq_zero_and_eq_one`: vectors
  in distinct orbits are separated by an invariant with values `0` and `1`.
* `Representation.forall_mem_symmetricAlgebraInvariants_lift_eval_eq_iff`: two vectors agree on
  every invariant exactly when they lie in the same orbit.
* `Representation.forall_homogeneous_mem_symmetricAlgebraInvariants_lift_eval_eq_zero_iff`: every
  homogeneous invariant of positive degree vanishes at `v` exactly when `v = 0`.

## References

* H. Derksen, G. Kemper, *Computational Invariant Theory*, Springer (2002), Chapter 2.
-/

public section

open TauCeti.SymmetricAlgebra

namespace Representation

section CommSemiring

variable {K G V : Type*} [CommSemiring K] [Group G] [AddCommMonoid V] [Module K V]
variable (ρ : Representation K G V)

/-- Evaluating the translate by `g` of a polynomial function at `v` is evaluating the polynomial
function at `ρ g⁻¹ v`. -/
theorem lift_eval_symmetricAlgebra_dual (g : G) (v : V)
    (p : SymmetricAlgebra K (Module.Dual K V)) :
    SymmetricAlgebra.lift (Module.Dual.eval K V v) (ρ.dual.symmetricAlgebra g p) =
      SymmetricAlgebra.lift (Module.Dual.eval K V (ρ g⁻¹ v)) p := by
  have h : (SymmetricAlgebra.lift (Module.Dual.eval K V v)).comp
      (SymmetricAlgebra.map K (ρ.dual g)) =
        SymmetricAlgebra.lift (Module.Dual.eval K V (ρ g⁻¹ v)) :=
    SymmetricAlgebra.algHom_ext <| LinearMap.ext fun φ ↦ by simp [Module.Dual.transpose_apply]
  rw [symmetricAlgebra_apply, ← h, AlgHom.comp_apply]

end CommSemiring

section Field

variable {K G V : Type*} [Field K] [Group G] [Finite G] [AddCommGroup V] [Module K V]
variable (ρ : Representation K G V)

/-- **Invariant polynomials separate orbits.** If `w` is not in the orbit of `v`, then some
invariant polynomial function takes the value `0` at `v` and `1` at `w`. -/
theorem exists_mem_symmetricAlgebraInvariants_lift_eval_eq_zero_and_eq_one {v w : V}
    (h : ∀ g : G, ρ g v ≠ w) :
    ∃ p ∈ ρ.dual.symmetricAlgebraInvariants,
      SymmetricAlgebra.lift (Module.Dual.eval K V v) p = 0 ∧
        SymmetricAlgebra.lift (Module.Dual.eval K V w) p = 1 := by
  let := ρ.dual.symmetricAlgebraMulSemiringAction
  have := ρ.dual.smulCommClass_symmetricAlgebraMulSemiringAction
  rw [symmetricAlgebraInvariants_eq_fixedPoints]
  refine FixedPoints.exists_mem_subalgebra_eq_zero_and_eq_one fun g hg ↦ h g⁻¹ ?_
  -- Evaluations at vectors separate vectors, since linear forms do.
  refine Module.eval_apply_injective K (LinearMap.ext fun φ ↦ ?_)
  have := DFunLike.congr_fun hg (SymmetricAlgebra.ι K _ φ)
  rw [AlgHom.comp_apply, MulSemiringAction.toAlgHom_apply, symmetricAlgebraMulSemiringAction_smul,
    lift_eval_symmetricAlgebra_dual] at this
  simpa using this

/-- **Invariant polynomials detect orbits.** Two vectors have the same value on every invariant
polynomial function exactly when they lie in the same orbit. -/
theorem forall_mem_symmetricAlgebraInvariants_lift_eval_eq_iff {v w : V} :
    (∀ p ∈ ρ.dual.symmetricAlgebraInvariants,
        SymmetricAlgebra.lift (Module.Dual.eval K V v) p =
          SymmetricAlgebra.lift (Module.Dual.eval K V w) p) ↔
      ∃ g : G, ρ g v = w := by
  constructor
  · intro heq
    by_contra h
    obtain ⟨p, hp, hv, hw⟩ :=
      ρ.exists_mem_symmetricAlgebraInvariants_lift_eval_eq_zero_and_eq_one (not_exists.mp h)
    simpa [hv, hw] using heq p hp
  · rintro ⟨g, rfl⟩ p hp
    have := ρ.lift_eval_symmetricAlgebra_dual g (ρ g v) p
    rwa [inv_self_apply, (ρ.dual.mem_symmetricAlgebraInvariants p).1 hp g, eq_comm] at this

/-- **The fibre over the vertex is the origin.** Every homogeneous invariant polynomial function
of positive degree vanishes at `v` exactly when `v = 0`. -/
theorem forall_homogeneous_mem_symmetricAlgebraInvariants_lift_eval_eq_zero_iff {v : V} :
    (∀ n, 0 < n → ∀ p ∈ ρ.dual.symmetricAlgebraInvariants,
        p ∈ homogeneousSubmodule K (Module.Dual K V) n →
          SymmetricAlgebra.lift (Module.Dual.eval K V v) p = 0) ↔
      v = 0 := by
  -- Evaluation at `0` kills every homogeneous element of positive degree, and all evaluations
  -- agree with it in degree zero.
  have hzero {n : ℕ} {p : SymmetricAlgebra K (Module.Dual K V)}
      (hp : p ∈ homogeneousSubmodule K (Module.Dual K V) n) (u : V) :
      SymmetricAlgebra.lift (Module.Dual.eval K V 0) p =
        (0 : K) ^ n * SymmetricAlgebra.lift (Module.Dual.eval K V u) p := by
    rw [map_zero, ← zero_smul K (Module.Dual.eval K V u),
      lift_smul_of_mem_homogeneousSubmodule (hp := hp), smul_eq_mul]
  constructor
  · intro h
    refine ((ρ.forall_mem_symmetricAlgebraInvariants_lift_eval_eq_iff).1 fun p hp ↦ ?_).elim
      fun g hg ↦ by rw [← ρ.inv_self_apply g v, hg, map_zero]
    classical
    -- Compare the two evaluations on each homogeneous component, which is again invariant.
    rw [← DirectSum.sum_support_decompose (homogeneousSubmodule K (Module.Dual K V)) p, map_sum,
      map_sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    have hn := SetLike.coe_mem (DirectSum.decompose (homogeneousSubmodule K (Module.Dual K V)) p n)
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [hzero hn v, pow_zero, one_mul]
    · rw [h n hpos _ (ρ.dual.isHomogeneous_symmetricAlgebraInvariants n hp) hn, hzero hn v,
        zero_pow hpos.ne', zero_mul]
  · rintro rfl n hn p _ hp
    rw [hzero hp 0, zero_pow hn.ne', zero_mul]

end Field

end Representation
