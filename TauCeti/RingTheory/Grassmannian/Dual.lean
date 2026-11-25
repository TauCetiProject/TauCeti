/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.LinearAlgebra.Dual.BaseChange
public import TauCeti.RingTheory.Grassmannian.Basic

import TauCeti.LinearAlgebra.Dual.Rank
import TauCeti.Algebra.Module.Projective.Complement

/-!
# Duality of Grassmannians

Let `P` be a finite projective module over a commutative ring `A`, of constant rank `k + l`. A
point `N ∈ G(k, P; A)` is a submodule with finite projective quotient of rank `k`; it is a direct
summand of `P`, finite projective of rank `l` (`Module.Grassmannian.rankAtStalk_toSubmodule`), so
the rank-`k` quotients of `P` are the rank-`l` subbundles of `P`. Restriction of functionals
`P^∨ → N^∨` is surjective with kernel the annihilator `N^⊥` of `N`, so `N^⊥` is a point of
`G(l, P^∨; A)` (`Module.Grassmannian.dualAnnihilator`): the rank-`l` subbundles of `P` are the
rank-`l` quotients of `P^∨`. Conversely the coannihilator of a point of `G(l, P^∨; A)` is a point
of `G(k, P; A)` (`Module.Grassmannian.dualCoannihilator`), and the two constructions are inverse
bijections `G(k, P; A) ≃ G(l, P^∨; A)` (`Module.Grassmannian.dualEquiv`).

Both inverse laws come from `Module.Grassmannian.eq_of_le` in
`TauCeti/RingTheory/Grassmannian/Basic.lean`: two points of the same Grassmannian, one contained in
the other, are equal.

For a finite projective `R`-module `M` of constant rank `k + l` and an `R`-algebra `A`, composing
with the identification `A ⊗[R] M^∨ ≃ (A ⊗[R] M)^∨` gives a bijection
`G(k, A ⊗[R] M; A) ≃ G(l, A ⊗[R] M^∨; A)` (`Module.Grassmannian.baseChangeDualEquiv`), natural in
`A` (`Module.Grassmannian.baseChangeDualEquiv_map`). This is the isomorphism of Grassmannian
functors underlying the isomorphism of Grassmannian schemes `G(k, M) ≅ G(l, M^∨)` in
`TauCeti/AlgebraicGeometry/Grassmannian/Dual.lean`.

## Main definitions

* `Module.Grassmannian.dualAnnihilator h N`: the annihilator of `N ∈ G(k, P; A)`, a point of
  `G(l, P^∨; A)`.
* `Module.Grassmannian.dualCoannihilator h K`: the coannihilator of `K ∈ G(l, P^∨; A)`, a point
  of `G(k, P; A)`.
* `Module.Grassmannian.dualEquiv h`: the bijection `G(k, P; A) ≃ G(l, P^∨; A)`.
* `Module.Grassmannian.baseChangeDualEquiv h A`: the bijection
  `G(k, A ⊗[R] M; A) ≃ G(l, A ⊗[R] M^∨; A)`.

## Main results

* `Module.Grassmannian.mem_baseChangeDualEquiv_iff` and
  `Module.Grassmannian.mem_baseChangeDualEquiv_symm_iff`: `baseChangeDualEquiv` and its inverse on
  points.
* `Module.Grassmannian.baseChangeDualEquiv_map`: naturality of `baseChangeDualEquiv`.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u v w

open TensorProduct

namespace Module.Grassmannian

variable {A : Type*} [CommRing A] {P : Type*} [AddCommGroup P] [Module A P] {k l : ℕ}

section Dual

variable [Module.Finite A P] [Module.Projective A P]

/-- **The annihilator of a point.** If `P` is finite projective of constant rank `k + l`, the
annihilator `N^⊥ ⊆ P^∨` of `N ∈ G(k, P; A)` is a point of `G(l, P^∨; A)`: it is the kernel of the
surjective restriction `P^∨ → N^∨` onto a finite projective module of rank `l`. -/
noncomputable def dualAnnihilator (h : ∀ p, rankAtStalk (R := A) P p = k + l) (N : G(k, P; A)) :
    G(l, Module.Dual A P; A) :=
  ofSurjective N.toSubmodule.dualRestrict Submodule.dualRestrict_surjective_of_projective_quotient
    fun p ↦ by
      rw [TauCeti.Module.rankAtStalk_dual]
      exact rankAtStalk_toSubmodule h N p

@[simp]
theorem toSubmodule_dualAnnihilator (h : ∀ p, rankAtStalk (R := A) P p = k + l)
    (N : G(k, P; A)) :
    (N.dualAnnihilator h).toSubmodule = N.toSubmodule.dualAnnihilator := by
  rw [dualAnnihilator, toSubmodule_ofSurjective, Submodule.dualRestrict_ker_eq_dualAnnihilator]

/-- **The coannihilator of a point.** If `P` is finite projective of constant rank `k + l`, the
coannihilator `K^⊥ ⊆ P` of `K ∈ G(l, P^∨; A)`, the vectors killed by every functional in `K`, is a
point of `G(k, P; A)`: it corresponds to the annihilator of `K` under `P ≃ P^∨∨`. -/
noncomputable def dualCoannihilator (h : ∀ p, rankAtStalk (R := A) P p = k + l)
    (K : G(l, Module.Dual A P; A)) : G(k, P; A) :=
  (Module.evalEquiv A P).symm.grassmannianCongr <| K.dualAnnihilator fun p ↦ by
    rw [TauCeti.Module.rankAtStalk_dual, h, Nat.add_comm]

@[simp]
theorem toSubmodule_dualCoannihilator (h : ∀ p, rankAtStalk (R := A) P p = k + l)
    (K : G(l, Module.Dual A P; A)) :
    (K.dualCoannihilator h).toSubmodule = K.toSubmodule.dualCoannihilator := by
  ext x
  simp [dualCoannihilator, Submodule.mem_map_equiv, Submodule.mem_dualCoannihilator]

/-- **Duality of Grassmannians.** If `P` is finite projective of constant rank `k + l`, taking
annihilators identifies the rank-`k` quotients of `P` with the rank-`l` quotients of its dual
`P^∨`; the inverse takes coannihilators. -/
noncomputable def dualEquiv (h : ∀ p, rankAtStalk (R := A) P p = k + l) :
    G(k, P; A) ≃ G(l, Module.Dual A P; A) where
  toFun N := N.dualAnnihilator h
  invFun K := K.dualCoannihilator h
  left_inv N := (eq_of_le <| by
    simpa using N.toSubmodule.le_dualAnnihilator_dualCoannihilator).symm
  right_inv K := (eq_of_le <| by
    simpa using K.toSubmodule.le_dualCoannihilator_dualAnnihilator).symm

@[simp]
theorem dualEquiv_apply (h : ∀ p, rankAtStalk (R := A) P p = k + l) (N : G(k, P; A)) :
    dualEquiv h N = N.dualAnnihilator h :=
  (rfl)

@[simp]
theorem dualEquiv_symm_apply (h : ∀ p, rankAtStalk (R := A) P p = k + l)
    (K : G(l, Module.Dual A P; A)) :
    (dualEquiv h).symm K = K.dualCoannihilator h :=
  (rfl)

end Dual

section BaseChange

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

open TauCeti.Module.Dual

variable [Module.Finite R M] [Module.Projective R M]

variable (A) in
/-- **Duality of Grassmannian functors.** If `M` is finite projective of constant rank `k + l`
over `R`, then for every `R`-algebra `A` the points of `G(k, M)` over `A` correspond to the
points of `G(l, M^∨)` over `A`: a point `N` goes to its annihilator in
`(A ⊗[R] M)^∨ ≃ A ⊗[R] M^∨` (`Module.Grassmannian.mem_baseChangeDualEquiv_iff`), and its inverse
takes coannihilators (`Module.Grassmannian.mem_baseChangeDualEquiv_symm_iff`). The bijection is
natural in `A` (`Module.Grassmannian.baseChangeDualEquiv_map`). -/
noncomputable def baseChangeDualEquiv (h : ∀ p, rankAtStalk (R := R) M p = k + l) :
    G(k, A ⊗[R] M; A) ≃ G(l, A ⊗[R] Module.Dual R M; A) :=
  (dualEquiv fun p ↦ (rankAtStalk_baseChange p).trans (h _)).trans
    (baseChangeEvaluationEquiv (R := R) (A := A) (M := M)).symm.grassmannianCongr

/-- **`baseChangeDualEquiv` on points.** An element `ξ` of `A ⊗[R] M^∨` lies in the point
corresponding to `N` exactly when it kills `N` under the pairing of `A ⊗[R] M^∨` with
`A ⊗[R] M`. -/
@[simp]
theorem mem_baseChangeDualEquiv_iff (h : ∀ p, rankAtStalk (R := R) M p = k + l)
    (N : G(k, A ⊗[R] M; A)) (ξ : A ⊗[R] Module.Dual R M) :
    ξ ∈ (baseChangeDualEquiv A h N).toSubmodule ↔
      ∀ x ∈ N.toSubmodule, baseChangeEvaluation (R := R) (M := M) (A := A) ξ x = 0 := by
  simp [baseChangeDualEquiv, Submodule.mem_map_equiv]

/-- **The inverse of `baseChangeDualEquiv` on points.** An element `x` of `A ⊗[R] M` lies in the
point corresponding to `K` exactly when every `ξ ∈ K` kills it under the pairing of `A ⊗[R] M^∨`
with `A ⊗[R] M`. -/
@[simp]
theorem mem_baseChangeDualEquiv_symm_iff (h : ∀ p, rankAtStalk (R := R) M p = k + l)
    (K : G(l, A ⊗[R] Module.Dual R M; A)) (x : A ⊗[R] M) :
    x ∈ ((baseChangeDualEquiv A h).symm K).toSubmodule ↔
      ∀ ξ ∈ K.toSubmodule, baseChangeEvaluation (R := R) (M := M) (A := A) ξ x = 0 := by
  simp only [baseChangeDualEquiv, Equiv.symm_trans, LinearEquiv.grassmannianCongr_symm,
    LinearEquiv.symm_symm, Equiv.trans_apply, dualEquiv_symm_apply, toSubmodule_dualCoannihilator,
    LinearEquiv.toSubmodule_grassmannianCongr_apply, Submodule.mem_dualCoannihilator,
    Submodule.mem_map_equiv]
  -- reindex the functionals on `A ⊗[R] M` by `A ⊗[R] M^∨` along `baseChangeEvaluationEquiv`
  refine ⟨fun H ξ hξ ↦ ?_, fun H φ hφ ↦ ?_⟩
  · have := H (baseChangeEvaluationEquiv ξ) (by rwa [LinearEquiv.symm_apply_apply])
    rwa [baseChangeEvaluationEquiv_apply] at this
  · have := H _ hφ
    rwa [← baseChangeEvaluationEquiv_apply, LinearEquiv.apply_symm_apply] at this

/-- **Naturality of `baseChangeDualEquiv`.** For `f : A →ₐ[R] B`, the point corresponding to the
base change of `N` is the base change of the point corresponding to `N`. -/
theorem baseChangeDualEquiv_map (h : ∀ p, rankAtStalk (R := R) M p = k + l) (f : A →ₐ[R] B)
    (N : G(k, A ⊗[R] M; A)) :
    baseChangeDualEquiv B h (map f N) = map f (baseChangeDualEquiv A h N) := by
  refine (eq_of_le ?_).symm
  rw [map_toSubmodule_eq_span, Submodule.span_le]
  rintro _ ⟨ξ, hξ, rfl⟩
  rw [SetLike.mem_coe, mem_baseChangeDualEquiv_iff, map_toSubmodule_eq_span]
  intro y hy
  refine (Submodule.span_le (p := LinearMap.ker (baseChangeEvaluation (R := R) (M := M) (A := B)
    (f.toLinearMap.rTensor _ ξ))).2 ?_) hy
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, AlgHom.baseChangeEvaluation_rTensor,
    (mem_baseChangeDualEquiv_iff h N ξ).1 hξ x hx, map_zero]

/-- **Naturality of the inverse of `baseChangeDualEquiv`.** -/
theorem baseChangeDualEquiv_symm_map (h : ∀ p, rankAtStalk (R := R) M p = k + l)
    (f : A →ₐ[R] B) (K : G(l, A ⊗[R] Module.Dual R M; A)) :
    (baseChangeDualEquiv B h).symm (map f K) = map f ((baseChangeDualEquiv A h).symm K) := by
  rw [Equiv.symm_apply_eq, baseChangeDualEquiv_map, Equiv.apply_symm_apply]

end BaseChange

end Module.Grassmannian
