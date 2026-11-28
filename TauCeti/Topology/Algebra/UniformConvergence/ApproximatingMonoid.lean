/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.UniformConvergence

/-!
# Approximating monoids

Fix `s : (0, ∞) → ℕ` and write `I = Σ η, Fin (s η)`. A submonoid `N` of `K × (I → K)` is
approximating for coefficients `c η i ∈ K` (`Submonoid.IsApproximating`) if it is closed and
`∑ i, c η i * φ ⟨η, i⟩` tends to `t` as `η → 0`, uniformly over `(t, φ) ∈ N`.

## Main definitions

* `Submonoid.IsApproximating`: the approximating property of a submonoid `N`.

## Main results

* `UniformFun.exists_forall_dist_le_of_mem_closure`: a function in the uniform closure of a set
  `A` is uniformly within any `ε > 0` of some member of `A`.
* `Submonoid.IsApproximating.tendstoUniformly_eval`: the approximation passes to polynomial
  expressions in elements of `N`.
* `Submonoid.exists_isApproximating_of_mem_closure_span`: let `f ≠ 0` lie in the closure, for
  uniform convergence, of the span of a set `S` of functions `X → K`. There are `s`, `c`, an
  approximating `N` and `y : I → S` such that the eigenvalues `(t, φ)` of `f` and of the `y i`
  under any linear operator that does not increase the sup norm lie in `N`.

## Provenance

The definition and both results follow `New.IsApproximatingMonoid`,
`New.IsApproximatingMonoid.tendstoUniformly_eval` and
`New.exists_isApproximatingMonoid_of_mem_uniformClosure` of `grh-lean`
(<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic, PBC; file
`Lib/GaloisRep/Pseudocharacter/Pseudorepresentations`). The uniform closure `New.uniformClosure`
is replaced by Mathlib's `closure` in `X →ᵤ K`, and the scalars of the definition and of the
polynomial statement are generalised from normed fields to uniform commutative rings.
-/

public section

open Filter Finset UniformConvergence

namespace UniformFun

/-- If `f` lies in the closure of a set `A` of functions for uniform convergence, then for every
`ε > 0` some `g ∈ A` is within `ε` of `f` at every point. -/
theorem exists_forall_dist_le_of_mem_closure {X β : Type*} [PseudoMetricSpace β] {A : Set (X → β)}
    {f : X → β} (hf : ofFun f ∈ closure (ofFun '' A)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ A, ∀ x, dist (f x) (g x) ≤ ε := by
  have hb := UniformFun.hasBasis_nhds_of_basis X β (ofFun f) Metric.uniformity_basis_dist_le
  obtain ⟨g, ⟨g, hg, rfl⟩, h⟩ := (mem_closure_iff_nhds_basis hb).1 hf ε hε
  exact ⟨g, hg, h⟩

end UniformFun

namespace Submonoid

variable {K : Type*}

/-- A submonoid `N` of `K × (I → K)`, where `I = Σ η, Fin (s η)` for `s : (0, ∞) → ℕ`, is
approximating for coefficients `c η i` if it is closed and `∑ i, c η i * φ ⟨η, i⟩` tends to `t`
as `η` tends to `0`, uniformly over `(t, φ) ∈ N`. -/
structure IsApproximating [Semiring K] [UniformSpace K] (s : Set.Ioi (0 : ℝ) → ℕ)
    (c : ∀ η : Set.Ioi (0 : ℝ), Fin (s η) → K)
    (N : Submonoid (K × ((Σ η : Set.Ioi (0 : ℝ), Fin (s η)) → K))) : Prop where
  /-- An approximating monoid is closed. -/
  isClosed : IsClosed (N : Set (K × ((Σ η : Set.Ioi (0 : ℝ), Fin (s η)) → K)))
  /-- The combinations `∑ i, c η i * φ ⟨η, i⟩` tend to `t` uniformly over `(t, φ) ∈ N`. -/
  tendstoUniformly : TendstoUniformly
    (fun (η : Set.Ioi (0 : ℝ)) (p : N) ↦ ∑ i : Fin (s η), c η i * p.val.snd ⟨η, i⟩)
    (fun p : N ↦ p.val.fst) atBot

/-- For an approximating monoid `N`, a polynomial `B` and a family `f p` of elements of `N`
indexed by the variables of `B`, `∑ i, c η i * B (fun x ↦ (f p x).2 ⟨η, i⟩)` tends to
`B (fun x ↦ (f p x).1)` as `η` tends to `0`, uniformly in `p`. -/
theorem IsApproximating.tendstoUniformly_eval [CommRing K] [UniformSpace K] [IsUniformAddGroup K]
    [UniformContinuousConstSMul K K] {σ P : Type*} {s : Set.Ioi (0 : ℝ) → ℕ}
    {c : ∀ η : Set.Ioi (0 : ℝ), Fin (s η) → K}
    {N : Submonoid (K × ((Σ η : Set.Ioi (0 : ℝ), Fin (s η)) → K))}
    (hN : N.IsApproximating s c) (B : MvPolynomial σ K) (f : P → σ → N) :
    TendstoUniformly
      (fun (η : Set.Ioi (0 : ℝ)) (p : P) ↦
        ∑ i : Fin (s η), c η i * MvPolynomial.eval (fun x ↦ (f p x).val.snd ⟨η, i⟩) B)
      (fun p ↦ MvPolynomial.eval (fun x ↦ (f p x).val.fst) B) atBot := by
  induction B using MvPolynomial.induction_on' with
  | monomial m a =>
    -- A monomial evaluated at the `f p x` is `a` times a product of elements of `N`.
    have h := hN.tendstoUniformly.comp fun p ↦ m.prod fun x e ↦ f p x ^ e
    simpa [mul_left_comm, MvPolynomial.eval_monomial, Finsupp.prod, Function.comp_def,
      Prod.snd_prod, mul_sum, Prod.fst_prod] using
      (uniformContinuous_mul_left' a).comp_tendstoUniformly h
  | add B B' hB hB' => simpa [mul_add, sum_add_distrib, Pi.add_def] using hB.add hB'

variable [NormedField K] {X : Type*}

/-- Let `T` be a linear operator that does not increase the sup norm, with `T f = t • f` and
`T (y j) = φ j • y j`. If `f` is within `ε` of `∑ j, a j • y j` at every point, then
`t * f z` is within `ε` of `∑ j, a j * φ j * y j z`. -/
private theorem norm_mul_sub_sum_le {m : ℕ} {T : Module.End K (X → K)}
    (hT : ∀ (g : X → K) (r : ℝ), (∀ x, ‖g x‖ ≤ r) → ∀ x, ‖T g x‖ ≤ r) {f : X → K} {t : K}
    (hTf : T f = t • f) {y : Fin m → X → K} {φ : Fin m → K} (hTy : ∀ j, T (y j) = φ j • y j)
    {a : Fin m → K} {ε : ℝ} (hf : ∀ x, ‖f x - ∑ j, a j * y j x‖ ≤ ε) (z : X) :
    ‖t * f z - ∑ j, a j * φ j * y j z‖ ≤ ε := by
  have h := hT (f - ∑ j, a j • y j) ε (fun x ↦ by simpa using hf x) z
  simpa [hTf, hTy, mul_assoc] using h

/-- Let `S` be a set of functions `X → K` and `f ≠ 0` a function in the closure, for uniform
convergence, of the span of `S`. There are `s`, coefficients `c`, an approximating monoid `N` and
`y : I → S` such that, for every linear operator `T` that does not increase the sup norm with
`T f = t • f` and `T (y i) = φ i • y i` for all `i`, the pair `(t, φ)` lies in `N`. -/
theorem exists_isApproximating_of_mem_closure_span {S : Set (X → K)} {f : X → K} (hf₀ : f ≠ 0)
    (hf : UniformFun.ofFun f ∈
      _root_.closure (UniformFun.ofFun '' (Submodule.span K S : Set (X → K)))) :
    ∃ (s : Set.Ioi (0 : ℝ) → ℕ) (c : ∀ η : Set.Ioi (0 : ℝ), Fin (s η) → K)
      (N : Submonoid (K × ((Σ η : Set.Ioi (0 : ℝ), Fin (s η)) → K)))
      (y : (Σ η : Set.Ioi (0 : ℝ), Fin (s η)) → X → K),
      N.IsApproximating s c ∧ (∀ i, y i ∈ S) ∧
      ∀ (T : Module.End K (X → K)) (t : K) (φ : (Σ η : Set.Ioi (0 : ℝ), Fin (s η)) → K),
        (∀ (g : X → K) (r : ℝ), (∀ x, ‖g x‖ ≤ r) → ∀ x, ‖T g x‖ ≤ r) →
        T f = t • f → (∀ i, T (y i) = φ i • y i) → (t, φ) ∈ N := by
  -- Approximate `f` within `η * ‖f z‖` by a combination `∑ j, a η j • y η j` of members of `S`.
  obtain ⟨z, hz : f z ≠ 0⟩ := Function.ne_iff.mp hf₀
  have hz' : 0 < ‖f z‖ := norm_pos_iff.2 hz
  have h_approx (η : Set.Ioi (0 : ℝ)) : ∃ (m : ℕ) (a : Fin m → K) (y : Fin m → X → K),
      (∀ j, y j ∈ S) ∧ ∀ x, ‖f x - ∑ j, a j * y j x‖ ≤ η * ‖f z‖ := by
    obtain ⟨g, hg, hfg⟩ :=
      UniformFun.exists_forall_dist_le_of_mem_closure hf (mul_pos η.prop hz')
    obtain ⟨m, a, y, rfl⟩ := Submodule.mem_span_set'.1 hg
    exact ⟨m, a, fun j ↦ y j, fun j ↦ (y j).prop, fun x ↦ by simpa [dist_eq_norm] using hfg x⟩
  choose s a y hyS hy using h_approx
  -- `N₀`: the eigenvalue systems of contractions with eigenvectors `f` and all `y η j`.
  let N₀ : Submonoid (K × ((Σ η : Set.Ioi (0 : ℝ), Fin (s η)) → K)) :=
    { carrier := {p | ∃ T : Module.End K (X → K),
        (∀ (g : X → K) (r : ℝ), (∀ x, ‖g x‖ ≤ r) → ∀ x, ‖T g x‖ ≤ r) ∧
        T f = p.1 • f ∧ ∀ i, T (y i.1 i.2) = p.2 i • y i.1 i.2}
      mul_mem' := by
        rintro p p' ⟨T, hT, hTf, hTy⟩ ⟨T', hT', hT'f, hT'y⟩
        exact ⟨T * T', fun g r hg x ↦ hT _ _ (hT' g r hg) x,
          by simp [hTf, hT'f, smul_smul, mul_comm],
          fun i ↦ by simp [hTy, hT'y, smul_smul, mul_comm]⟩
      one_mem' := ⟨1, fun g r hg ↦ hg, by simp, by simp⟩ }
  let c (η : Set.Ioi (0 : ℝ)) (j : Fin (s η)) : K := a η j * y η j z / f z
  have h_dist (η : Set.Ioi (0 : ℝ)) :
      ∀ p ∈ N₀, dist p.1 (∑ j, c η j * p.2 ⟨η, j⟩) ≤ η := by
    rintro p ⟨T, hT, hTf, hTy⟩
    have h := norm_mul_sub_sum_le hT hTf (fun j ↦ hTy ⟨η, j⟩) (hy η) z
    rw [dist_eq_norm, ← mul_le_mul_iff_left₀ hz', ← norm_mul, sub_mul, sum_mul]
    convert h using 3
    refine sum_congr rfl fun j _ ↦ ?_
    simp only [c]
    field_simp
  refine ⟨s, c, N₀.topologicalClosure, fun i ↦ y i.1 i.2, ⟨isClosed_closure, ?_⟩,
    fun i ↦ hyS i.1 i.2, fun T t φ hT hTf hTy ↦ N₀.le_topologicalClosure ⟨T, hT, hTf, hTy⟩⟩
  refine Metric.tendstoUniformly_iff.2 fun ε hε ↦ ?_
  filter_upwards [eventually_lt_atBot (⟨ε, hε⟩ : Set.Ioi (0 : ℝ))] with η hη p
  exact (le_on_closure (h_dist η) (by fun_prop) (by fun_prop) p.prop).trans_lt hη

end Submonoid
