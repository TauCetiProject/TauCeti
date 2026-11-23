/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.LinearAlgebra.Dual.BaseChange
public import TauCeti.RingTheory.Grassmannian.Basic

import TauCeti.LinearAlgebra.Dual.Rank

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

Both inverse laws come from `Module.Grassmannian.eq_of_le`: two points of the same Grassmannian,
one contained in the other, are equal, because the kernel of the induced surjection of quotients
is a finite projective module of rank zero.

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

* `Module.Grassmannian.eq_of_le`: points of a Grassmannian are maximal under inclusion.
* `Module.Grassmannian.rankAtStalk_toSubmodule`: a point of `G(k, P; A)` is a subbundle of rank
  `l`.
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

section Split

variable {A : Type*} [CommRing A] {K X Y : Type*} [AddCommGroup K] [Module A K] [AddCommGroup X]
  [Module A X] [AddCommGroup Y] [Module A Y] [Module.Projective A Y] {f : K →ₗ[A] X}
  {g : X →ₗ[A] Y}

/-- A short exact sequence `0 → K → X → Y → 0` with `Y` projective splits. -/
private theorem exists_splitting (hfg : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) :
    ∃ e : X ≃ₗ[A] K × Y, f = e.symm.toLinearMap ∘ₗ LinearMap.inl A K Y ∧
      g = LinearMap.snd A K Y ∘ₗ e.toLinearMap := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
  obtain ⟨e, he⟩ := (hfg.splitSurjectiveEquiv hf) ⟨s, hs⟩
  exact ⟨e, he⟩

private theorem finite_of_exact [Module.Finite A X] (hfg : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) : Module.Finite A K := by
  obtain ⟨e, -, -⟩ := exists_splitting hfg hf hg
  exact .of_surjective (LinearMap.fst A K Y ∘ₗ e.toLinearMap)
    (Prod.fst_surjective.comp e.surjective)

private theorem projective_of_exact [Module.Projective A X] (hfg : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) : Module.Projective A K := by
  obtain ⟨e, -, -⟩ := exists_splitting hfg hf hg
  exact .of_split (e.symm.toLinearMap ∘ₗ LinearMap.inl A K Y)
    (LinearMap.fst A K Y ∘ₗ e.toLinearMap) (by ext x; simp)

private theorem rankAtStalk_eq_add [Module.Finite A X] [Module.Projective A X] [Module.Finite A Y]
    (hfg : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    rankAtStalk (R := A) X = rankAtStalk K + rankAtStalk Y := by
  have := finite_of_exact hfg hf hg
  have := projective_of_exact hfg hf hg
  obtain ⟨e, -, -⟩ := exists_splitting hfg hf hg
  rw [rankAtStalk_eq_of_equiv e, rankAtStalk_prod]

end Split

variable {A : Type*} [CommRing A] {P : Type*} [AddCommGroup P] [Module A P] {k l : ℕ}

/-- **Points of a Grassmannian are maximal under inclusion.** If `N₁, N₂ ∈ G(k, P; A)` and
`N₁ ≤ N₂`, then `N₁ = N₂`: the kernel of the surjection `P ⧸ N₁ → P ⧸ N₂` is a direct summand of
`P ⧸ N₁`, hence finite projective, of rank `k - k = 0`, hence zero. -/
theorem eq_of_le {N₁ N₂ : G(k, P; A)} (h : N₁.toSubmodule ≤ N₂.toSubmodule) : N₁ = N₂ := by
  let g := Submodule.factor h
  have hg : Function.Surjective g := fun y ↦ by
    induction y using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hfg := LinearMap.exact_subtype_ker_map g
  have hf := (LinearMap.ker g).injective_subtype
  have := finite_of_exact hfg hf hg
  have := projective_of_exact hfg hf hg
  have hK : rankAtStalk (R := A) (LinearMap.ker g) = 0 := by
    ext p
    have h₁ := congrFun (rankAtStalk_eq_add hfg hf hg) p
    simp only [Pi.add_apply, N₁.rankAtStalk_eq, N₂.rankAtStalk_eq] at h₁
    simp only [Pi.zero_apply]
    omega
  have := rankAtStalk_eq_zero_iff_subsingleton.mp hK
  refine Grassmannian.ext (le_antisymm h fun x hx ↦ ?_)
  have hx' : N₁.toSubmodule.mkQ x ∈ LinearMap.ker g := by
    simpa [g, Submodule.Quotient.mk_eq_zero] using hx
  rw [← Submodule.Quotient.mk_eq_zero]
  exact congrArg Subtype.val (Subsingleton.elim (⟨_, hx'⟩ : LinearMap.ker g) 0)

section Dual

/-- A point of a Grassmannian of a finite module is a finite module. -/
theorem finite_toSubmodule [Module.Finite A P] (N : G(k, P; A)) :
    Module.Finite A N.toSubmodule :=
  finite_of_exact (LinearMap.exact_subtype_mkQ _) N.toSubmodule.injective_subtype
    N.toSubmodule.mkQ_surjective

/-- A point of a Grassmannian of a projective module is a projective module. -/
theorem projective_toSubmodule [Module.Projective A P] (N : G(k, P; A)) :
    Module.Projective A N.toSubmodule :=
  projective_of_exact (LinearMap.exact_subtype_mkQ _) N.toSubmodule.injective_subtype
    N.toSubmodule.mkQ_surjective

/-- **Quotients of rank `k` are subbundles of rank `l`.** If `P` has constant rank `k + l`, a
point of `G(k, P; A)` has constant rank `l`. -/
theorem rankAtStalk_toSubmodule [Module.Finite A P] [Module.Projective A P]
    (h : ∀ p, rankAtStalk (R := A) P p = k + l) (N : G(k, P; A))
    (p : PrimeSpectrum A) : rankAtStalk (R := A) N.toSubmodule p = l := by
  have h₁ := congrFun (rankAtStalk_eq_add (LinearMap.exact_subtype_mkQ N.toSubmodule)
    N.toSubmodule.injective_subtype N.toSubmodule.mkQ_surjective) p
  simp only [Pi.add_apply, N.rankAtStalk_eq, h] at h₁
  omega

/-- Every functional on a point `N` of a Grassmannian extends to the ambient module, since `N` is
a direct summand. -/
theorem dualRestrict_surjective (N : G(k, P; A)) :
    Function.Surjective N.toSubmodule.dualRestrict := by
  obtain ⟨e, hf, -⟩ := exists_splitting (LinearMap.exact_subtype_mkQ N.toSubmodule)
    N.toSubmodule.injective_subtype N.toSubmodule.mkQ_surjective
  intro ψ
  refine ⟨ψ ∘ₗ LinearMap.fst A _ _ ∘ₗ e.toLinearMap, LinearMap.ext fun n ↦ ?_⟩
  have hn : (n : P) = e.symm (n, 0) := LinearMap.congr_fun hf n
  simp [Submodule.dualRestrict_apply, hn]

variable [Module.Finite A P] [Module.Projective A P]

/-- **The annihilator of a point.** If `P` is finite projective of constant rank `k + l`, the
annihilator `N^⊥ ⊆ P^∨` of `N ∈ G(k, P; A)` is a point of `G(l, P^∨; A)`: it is the kernel of the
surjective restriction `P^∨ → N^∨` onto a finite projective module of rank `l`. -/
noncomputable def dualAnnihilator (h : ∀ p, rankAtStalk (R := A) P p = k + l) (N : G(k, P; A)) :
    G(l, Module.Dual A P; A) :=
  have := finite_toSubmodule N
  have := projective_toSubmodule N
  ofSurjective N.toSubmodule.dualRestrict (dualRestrict_surjective N) fun p ↦ by
    rw [TauCeti.Module.rankAtStalk_dual]
    exact rankAtStalk_toSubmodule h N p

@[simp]
theorem toSubmodule_dualAnnihilator (h : ∀ p, rankAtStalk (R := A) P p = k + l)
    (N : G(k, P; A)) :
    (N.dualAnnihilator h).toSubmodule = N.toSubmodule.dualAnnihilator := by
  simp only [dualAnnihilator, toSubmodule_ofSurjective]
  rfl

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
  rw [dualCoannihilator, LinearEquiv.toSubmodule_grassmannianCongr_apply,
    toSubmodule_dualAnnihilator, Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm]
  rfl

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

/-- The base change of a finite flat module of constant rank `k + l` has constant rank
`k + l`. -/
theorem rankAtStalk_baseChange_eq [Module.Finite R M] [Module.Flat R M]
    (h : ∀ p, rankAtStalk (R := R) M p = k + l) (p : PrimeSpectrum A) :
    rankAtStalk (R := A) (A ⊗[R] M) p = k + l := by
  rw [rankAtStalk_baseChange]
  exact h _

/-- The pairing of `A ⊗[R] M^∨` with `A ⊗[R] M` commutes with base change along `A → B`. -/
theorem baseChangeEvaluation_rTensor (f : A →ₐ[R] B) (ξ : A ⊗[R] Module.Dual R M)
    (x : A ⊗[R] M) :
    baseChangeEvaluation (R := R) (M := M) (A := B) (f.toLinearMap.rTensor _ ξ)
        (f.toLinearMap.rTensor M x) =
      f (baseChangeEvaluation (R := R) (M := M) (A := A) ξ x) := by
  induction ξ using TensorProduct.inductionOn with
  | add ξ η hξ hη => simp only [map_add, LinearMap.add_apply, hξ, hη]
  | tmul a φ =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m => simp

variable [Module.Finite R M] [Module.Projective R M]

variable (A) in
/-- **Duality of Grassmannian functors.** If `M` is finite projective of constant rank `k + l`
over `R`, then for every `R`-algebra `A` the points of `G(k, M)` over `A` correspond to the
points of `G(l, M^∨)` over `A`: a point `N` goes to its annihilator in
`(A ⊗[R] M)^∨ ≃ A ⊗[R] M^∨` (`Module.Grassmannian.mem_baseChangeDualEquiv_iff`). The bijection is
natural in `A` (`Module.Grassmannian.baseChangeDualEquiv_map`). -/
noncomputable def baseChangeDualEquiv (h : ∀ p, rankAtStalk (R := R) M p = k + l) :
    G(k, A ⊗[R] M; A) ≃ G(l, A ⊗[R] Module.Dual R M; A) :=
  (dualEquiv (rankAtStalk_baseChange_eq h)).trans
    (baseChangeEvaluationEquiv (R := R) (A := A) (M := M)).symm.grassmannianCongr

/-- **`baseChangeDualEquiv` on points.** An element `ξ` of `A ⊗[R] M^∨` lies in the point
corresponding to `N` exactly when it kills `N` under the pairing of `A ⊗[R] M^∨` with
`A ⊗[R] M`. -/
theorem mem_baseChangeDualEquiv_iff (h : ∀ p, rankAtStalk (R := R) M p = k + l)
    (N : G(k, A ⊗[R] M; A)) (ξ : A ⊗[R] Module.Dual R M) :
    ξ ∈ (baseChangeDualEquiv A h N).toSubmodule ↔
      ∀ x ∈ N.toSubmodule, baseChangeEvaluation (R := R) (M := M) (A := A) ξ x = 0 := by
  rw [baseChangeDualEquiv, Equiv.trans_apply, LinearEquiv.toSubmodule_grassmannianCongr_apply,
    Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, LinearEquiv.symm_symm, dualEquiv_apply,
    toSubmodule_dualAnnihilator, Submodule.mem_dualAnnihilator]
  simp

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
  rw [SetLike.mem_coe, LinearMap.mem_ker, baseChangeEvaluation_rTensor,
    (mem_baseChangeDualEquiv_iff h N ξ).1 hξ x hx, map_zero]

/-- **Naturality of the inverse of `baseChangeDualEquiv`.** -/
theorem baseChangeDualEquiv_symm_map (h : ∀ p, rankAtStalk (R := R) M p = k + l)
    (f : A →ₐ[R] B) (K : G(l, A ⊗[R] Module.Dual R M; A)) :
    (baseChangeDualEquiv B h).symm (map f K) = map f ((baseChangeDualEquiv A h).symm K) := by
  rw [Equiv.symm_apply_eq, baseChangeDualEquiv_map, Equiv.apply_symm_apply]

end BaseChange

end Module.Grassmannian
