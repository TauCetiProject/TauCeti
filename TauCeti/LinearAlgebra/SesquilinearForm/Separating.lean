/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Forms definite off the origin separate vectors

A semilinear map of two arguments `B` that is definite off the origin, `B x x ≠ 0` for `x ≠ 0`,
**separates** vectors: two vectors pairing identically against every vector are equal, because
their difference pairs to zero with itself. On a finite-dimensional space, a separating form
represents every pairing by a linear map.

## Main results

* `LinearMap.eq_of_forall_sesq_eq`: a form definite off the origin separates vectors.
* `LinearMap.exists_linearMap_forall_apply_eq_apply`: every pairing factors through a separating
  form on a finite-dimensional space.
-/

public section

namespace LinearMap

variable {R S M P : Type*} [Semiring R] [CommSemiring S] [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module S P] {I₁ I₂ : R →+* S}

/-- **A form definite off the origin separates vectors**: two vectors pairing identically against
every vector are equal, because their difference pairs to zero with itself.  Mathlib's
`LinearMap.SeparatingLeft` is the same separation stated as a property of the form; definiteness
off the origin is what supplies it here, and is the shape the callers carry it in. -/
theorem eq_of_forall_sesq_eq {B : M →ₛₗ[I₁] M →ₛₗ[I₂] P} (hdef : ∀ x : M, x ≠ 0 → B x x ≠ 0)
    {u v : M} (h : ∀ y : M, B u y = B v y) : u = v :=
  sub_eq_zero.1 <| not_not.1 fun hne ↦ hdef _ hne <| by simp [h]

/-- **Representing a pairing through a separating form.** Let `B` be a form on a finite-dimensional
space `V`, semilinear in the first variable and separating in the second, for instance a
nondegenerate sesquilinear form. Every pairing `S` of `V` with `W` of the same type has the form
`S x y = B x (T y)` for a linear map `T : W → V`. -/
theorem exists_linearMap_forall_apply_eq_apply {K V W : Type*} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [FiniteDimensional K V] {I : K →+* K}
    {B : V →ₛₗ[I] V →ₗ[K] K} (hB : B.SeparatingRight) (S : V →ₛₗ[I] W →ₗ[K] K) :
    ∃ T : W →ₗ[K] V, ∀ x y, S x y = B x (T y) := by
  let b := Module.finBasis K V
  -- The pairings of `v` with a basis determine `v`, so by dimension they take all values.
  let Φ : V →ₗ[K] Fin (Module.finrank K V) → K := LinearMap.pi fun i ↦ B (b i)
  have hΦ : Function.Injective Φ := (injective_iff_map_eq_zero Φ).mpr fun v hv ↦ by
    have h : B.flip v = 0 := b.ext fun i ↦ congrFun hv i
    exact hB v fun x ↦ LinearMap.congr_fun h x
  let e := Φ.linearEquivOfInjective hΦ (by simp)
  refine ⟨e.symm.toLinearMap ∘ₗ LinearMap.pi fun i ↦ S (b i), fun x y ↦ ?_⟩
  have h : S.flip y = B.flip (e.symm (fun i ↦ S (b i) y)) := b.ext fun i ↦
    (congrFun (e.apply_symm_apply fun i ↦ S (b i) y) i).symm
  exact LinearMap.congr_fun h x

end LinearMap
