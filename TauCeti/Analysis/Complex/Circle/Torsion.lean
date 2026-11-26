/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Fintype.Pi

/-!
# Torsion of products of circles

For `n ≠ 0` the circle group `S¹` has only finitely many elements `z` with `z ^ n = 1`
(`Circle.finite_setOf_pow_eq_one`), the `n`-th roots of unity, so a finite product of circles has
finitely many such elements (`Circle.finite_setOf_pow_eq_one_pi`). An infinite product of circles
has infinitely many as soon as `n ≥ 2` (`Circle.infinite_setOf_pow_eq_one_pi`): a primitive `n`-th
root of unity placed in any single coordinate is one, and different coordinates give different
elements.

A group isomorphism preserves the `n`-torsion elements, so an infinite product of circles is not
isomorphic, even as an abstract group, to a finite one (`Circle.isEmpty_mulEquiv_pi`). In
particular the product `ℕ → S¹` of countably many circles is not isomorphic as a topological group
to any torus `(S¹)ʳ` (`Circle.not_exists_continuousMulEquiv_pi_fin`). It is nevertheless a compact
connected commutative topological group, and it is aspherical (`Circle.isAspherical_pi`), so it
shows that the torus criterion for compact connected Lie groups
(`TauCeti.Lie.isAspherical_iff_exists_continuousMulEquiv_torus`) needs its Lie group hypothesis.
For `n = 2` the argument compares the subgroup `{±1}ᶥ` of elements of order dividing `2` with the
finite group `{±1}ʳ`.

## Main results

* `Circle.finite_setOf_pow_eq_one`, `Circle.finite_setOf_pow_eq_one_pi`: for `n ≠ 0` the
  `n`-torsion of the circle, and of a finite product of circles, is finite.
* `Circle.infinite_setOf_pow_eq_one_pi`: for `n ≥ 2` the `n`-torsion of an infinite product of
  circles is infinite.
* `Circle.isEmpty_mulEquiv_pi`: an infinite product of circles is not isomorphic as a group to a
  finite one.
* `Circle.not_exists_continuousMulEquiv_pi_fin`: an infinite product of circles is not isomorphic
  as a topological group to a torus `(S¹)ʳ`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4 (Example 6.30 and
  Proposition 6.31, the asphericity criterion for compact Lie groups).
-/

public section

open Set

namespace Circle

/-- **The `n`-th roots of unity on the circle are finite.** For `n ≠ 0` only finitely many points
`z` of the circle satisfy `z ^ n = 1`. -/
theorem finite_setOf_pow_eq_one {n : ℕ} (hn : n ≠ 0) : {z : Circle | z ^ n = 1}.Finite := by
  refine Finite.of_finite_image (f := fun z : Circle ↦ (z : ℂ))
    (((Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet).subset ?_) coe_injective.injOn
  rintro _ ⟨z, hz, rfl⟩
  simpa [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hn)] using
    congrArg (fun w : Circle ↦ (w : ℂ)) hz

/-- **The `n`-torsion of a finite product of circles is finite.** For `n ≠ 0` and a finite index
type `κ`, only finitely many `f : κ → S¹` satisfy `f ^ n = 1`. -/
theorem finite_setOf_pow_eq_one_pi {κ : Type*} [Finite κ] {n : ℕ} (hn : n ≠ 0) :
    {f : κ → Circle | f ^ n = 1}.Finite := by
  refine (Finite.pi fun _ ↦ finite_setOf_pow_eq_one hn).subset fun f hf i ↦ ?_
  simpa using congrFun hf i

/-- **The `n`-torsion of an infinite product of circles is infinite.** For `n ≥ 2` and an
infinite index type `ι`, infinitely many `f : ι → S¹` satisfy `f ^ n = 1`: a primitive `n`-th root
of unity `ζ` placed in a single coordinate is one, and `Pi.mulSingle i ζ` determines `i`. -/
theorem infinite_setOf_pow_eq_one_pi {ι : Type*} [Infinite ι] {n : ℕ} (hn : 2 ≤ n) :
    {f : ι → Circle | f ^ n = 1}.Infinite := by
  classical
  have : NeZero n := ⟨by omega⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Circle n
  exact infinite_of_injective_forall_mem (Pi.mulSingle_left_injective (hζ.ne_one (by omega)))
    fun i ↦ by simp [← Pi.mulSingle_pow, hζ.pow_eq_one]

/-- **An infinite product of circles is not a finite one.** For an infinite index type `ι` and a
finite index type `κ`, the products `ι → S¹` and `κ → S¹` are not isomorphic as groups: the former
has infinitely many elements whose square is `1`, the latter finitely many. -/
theorem isEmpty_mulEquiv_pi {ι κ : Type*} [Infinite ι] [Finite κ] :
    IsEmpty ((ι → Circle) ≃* (κ → Circle)) := by
  refine ⟨fun e ↦ infinite_setOf_pow_eq_one_pi (ι := ι) le_rfl ?_⟩
  have h : {f : ι → Circle | f ^ 2 = 1} = e ⁻¹' {g : κ → Circle | g ^ 2 = 1} := by
    ext f
    simp [← map_pow, map_eq_one_iff e e.injective]
  rw [h]
  exact (finite_setOf_pow_eq_one_pi two_ne_zero).preimage e.injective.injOn

/-- **An infinite product of circles is not a torus.** For an infinite index type `ι`, for instance
`ℕ`, the product `ι → S¹` is not isomorphic as a topological group to any torus `(S¹)ʳ`. -/
theorem not_exists_continuousMulEquiv_pi_fin {ι : Type*} [Infinite ι] :
    ¬∃ r : ℕ, Nonempty ((ι → Circle) ≃ₜ* (Fin r → Circle)) :=
  fun ⟨_, ⟨e⟩⟩ ↦ isEmpty_mulEquiv_pi.false e.toMulEquiv

end Circle
