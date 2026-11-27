/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.UniformMulAction

/-!
# Approximating monoids

Let `K` be a ring with a uniform structure, `l` a filter on a type `Λ`, and `ι η` a finite type
for each `η : Λ`; write `I = Σ η, ι η`. A submonoid `N` of `K × (I → K)`, with the componentwise
product, is *approximating* along `l` for coefficients `c η i ∈ K` if it is closed and the finite
combinations `∑ i, c η i * φ ⟨η, i⟩` tend to `t` along `l`, uniformly over `(t, φ) ∈ N`.

Approximating monoids record the uniform approximation of one eigenfunction by linear
combinations of others. Let `K` be a normed field and `f ≠ 0` a function `X → K` in the closure,
for uniform convergence, of the span of a set `S` of functions. Then there are an approximating
`N` along `atTop` on `ℕ` and functions `y i ∈ S` such that, for every `K`-linear operator `T` on
functions `X → K` that does not increase the sup norm, with `T f = t • f` and
`T (y i) = φ i • y i` for all `i`, the pair `(t, φ)` lies in `N`. So the eigenvalue of `T` on `f`
is the limit of the same combinations of its eigenvalues on the `y i`, at a rate independent of
`T`, and since `N` is a closed monoid the same holds for limits of such pairs and for polynomial
expressions in several of them. This is how a limit of eigenvalue systems of eigenfunctions
approximating `f` is controlled, for instance to pass trace identities to a limit.

## Main definitions

* `Submonoid.IsApproximating`: a closed submonoid of `K × (I → K)` on which the combinations
  `∑ i, c η i * φ ⟨η, i⟩` converge to the first component uniformly.

## Main results

* `Submonoid.isApproximating_topologicalClosure_iff`: the closure of a submonoid is
  approximating exactly when the combinations converge uniformly on the submonoid.
* `Submonoid.IsApproximating.tendstoUniformlyOn_eval`: for a polynomial `B` and a family `v` of
  elements of an approximating monoid, `∑ i, c η i * B (v.2 ⟨η, i⟩)` tends to `B (v.1)`, uniformly
  in `v`.
* `TauCeti.exists_isApproximating_of_mem_closure_span`: every nonzero uniform limit of linear
  combinations of functions in `S` has an approximating monoid containing the pairs of
  eigenvalues of the operators that do not increase the sup norm.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean` (declarations
  `New.IsApproximatingMonoid`, `New.exists_isApproximatingMonoid_of_mem_uniformClosure`,
  `New.IsApproximatingMonoid.tendstoUniformly_eval`); Apache 2.0, Copyright 2026 Anthropic, PBC.
  The notion of an approximating monoid and the construction of one, by normalising `f` at a
  point where it does not vanish and closing the monoid of pairs of eigenvalues, follow the
  method of these declarations.
-/

public section

open Filter Topology

namespace Submonoid

section Defs

variable {K Λ : Type*} {ι : Λ → Type*} [∀ η, Fintype (ι η)] [Semiring K] [UniformSpace K]

/-- A submonoid `N` of `K × (I → K)`, where `I = Σ η, ι η` has finite fibres `ι η`, is
*approximating* along a filter `l` on `Λ` for the coefficients `c η i` if it is closed and the
finite combinations `∑ i, c η i * φ ⟨η, i⟩` tend to `t` along `l`, uniformly over `(t, φ) ∈ N`. -/
structure IsApproximating (N : Submonoid (K × ((Σ η, ι η) → K))) (l : Filter Λ)
    (c : ∀ η, ι η → K) : Prop where
  /-- An approximating monoid is closed. -/
  isClosed : IsClosed (N : Set (K × ((Σ η, ι η) → K)))
  /-- The combinations `∑ i, c η i * φ ⟨η, i⟩` tend to `t` uniformly over `(t, φ) ∈ N`. -/
  tendstoUniformlyOn :
    TendstoUniformlyOn (fun η (p : K × ((Σ η, ι η) → K)) ↦ ∑ i, c η i * p.2 ⟨η, i⟩) Prod.fst l N

/-- The closure of a submonoid `N` of `K × (I → K)` is approximating exactly when the
combinations `∑ i, c η i * φ ⟨η, i⟩` tend to `t` uniformly over `(t, φ) ∈ N`. -/
theorem isApproximating_topologicalClosure_iff [IsTopologicalSemiring K]
    {N : Submonoid (K × ((Σ η, ι η) → K))} {l : Filter Λ} {c : ∀ η, ι η → K} :
    N.topologicalClosure.IsApproximating l c ↔
      TendstoUniformlyOn (fun η (p : K × ((Σ η, ι η) → K)) ↦ ∑ i, c η i * p.2 ⟨η, i⟩)
        Prod.fst l N := by
  refine ⟨fun h ↦ h.tendstoUniformlyOn.mono N.le_topologicalClosure, fun h ↦
    ⟨N.isClosed_topologicalClosure, fun u hu ↦ ?_⟩⟩
  obtain ⟨V, ⟨hV, hVc⟩, hVu⟩ := uniformity_hasBasis_closed.mem_iff.1 hu
  filter_upwards [h V hV] with η hη p hp
  -- The pairs `(t, φ)` with `(t, ∑ i, c η i * φ ⟨η, i⟩) ∈ V` form a closed set containing `N`.
  have hclosed : IsClosed {p : K × ((Σ η, ι η) → K) | (p.1, ∑ i, c η i * p.2 ⟨η, i⟩) ∈ V} :=
    hVc.preimage (by fun_prop)
  rw [coe_topologicalClosure] at hp
  exact hVu (closure_minimal (fun q hq ↦ hη q hq) hclosed hp)

end Defs

namespace IsApproximating

variable {K Λ : Type*} {ι : Λ → Type*} [∀ η, Fintype (ι η)] [CommRing K] [UniformSpace K]
  [IsUniformAddGroup K] [IsTopologicalRing K] {N : Submonoid (K × ((Σ η, ι η) → K))}
  {l : Filter Λ} {c : ∀ η, ι η → K}

/-- In an approximating monoid the approximation passes to polynomials: for a polynomial `B` in
variables indexed by `σ`, the combinations `∑ i, c η i * B ((v x).2 ⟨η, i⟩)_x` tend to
`B ((v x).1)_x`, uniformly over families `v : σ → K × (I → K)` of elements of `N`. -/
theorem tendstoUniformlyOn_eval (hN : N.IsApproximating l c) {σ : Type*}
    (B : MvPolynomial σ K) :
    TendstoUniformlyOn
      (fun η (v : σ → K × ((Σ η, ι η) → K)) ↦
        ∑ i, c η i * MvPolynomial.eval (fun x ↦ (v x).2 ⟨η, i⟩) B)
      (fun v ↦ MvPolynomial.eval (fun x ↦ (v x).1) B) l (Set.univ.pi fun _ ↦ (N : Set _)) := by
  induction B using MvPolynomial.induction_on' with
  | monomial u a =>
    -- The monomial `v ↦ ∏ x, v x ^ u x` maps families of elements of `N` into `N`.
    let m : (σ → K × ((Σ η, ι η) → K)) → K × ((Σ η, ι η) → K) :=
      fun v ↦ u.prod fun x e ↦ v x ^ e
    have hm : Set.univ.pi (fun _ ↦ (N : Set _)) ⊆ m ⁻¹' N := fun v hv ↦
      SubmonoidClass.finsuppProd_mem N u _ fun x _ ↦ pow_mem (hv x (Set.mem_univ x)) _
    have := ((uniformContinuous_mul_left' a).comp_tendstoUniformlyOn
      (hN.tendstoUniformlyOn.comp m)).mono hm
    convert this using 1
    · ext η v
      simp [m, MvPolynomial.eval_monomial, Finset.mul_sum, Finsupp.prod, Prod.snd_prod,
        Finset.prod_apply, mul_left_comm]
    · ext v
      simp [m, MvPolynomial.eval_monomial, Finsupp.prod, Prod.fst_prod]
  | add p q hp hq =>
    convert hp.add hq using 1
    · ext η v
      simp [mul_add, Finset.sum_add_distrib]
    · ext v
      simp

end IsApproximating

end Submonoid

namespace TauCeti

variable {K X I : Type*} [NormedField K]

/-- The pairs `(t, φ)` for which some `K`-linear operator `T` on functions `X → K` that does not
increase the sup norm has `T f = t • f` and `T (y i) = φ i • y i` for all `i`. They form a
submonoid, since such operators compose. -/
private def eigenvaluePairs (f : X → K) (y : I → X → K) : Submonoid (K × (I → K)) where
  carrier := {p | ∃ T : (X → K) →ₗ[K] X → K,
    (∀ (h : X → K) (C : ℝ), (∀ x, ‖h x‖ ≤ C) → ∀ x, ‖T h x‖ ≤ C) ∧
      T f = p.1 • f ∧ ∀ i, T (y i) = p.2 i • y i}
  mul_mem' := by
    rintro p q ⟨T, hT, hTf, hTy⟩ ⟨T', hT', hT'f, hT'y⟩
    refine ⟨T ∘ₗ T', fun h C hC ↦ hT _ C (hT' h C hC), ?_, fun i ↦ ?_⟩
    · simp [hTf, hT'f, smul_smul, mul_comm]
    · simp [hTy, hT'y, smul_smul, mul_comm]
  one_mem' := ⟨LinearMap.id, fun _ _ hC ↦ hC, by simp, fun _ ↦ by simp⟩

/-- If `f` is within `δ` of the combination `∑ j, a j • y (e j)` everywhere and `f x₀ ≠ 0`, then
for every pair `(t, φ)` of eigenvalues, `∑ j, (a j * y (e j) x₀ / f x₀) * φ (e j)` is within
`δ / ‖f x₀‖` of `t`: apply the operator to the difference and evaluate at `x₀`. -/
private lemma norm_sum_sub_le_of_mem_eigenvaluePairs {J : Type*} [Fintype J] {f : X → K}
    {y : I → X → K} {p : K × (I → K)} (hp : p ∈ eigenvaluePairs f y) {x₀ : X}
    (hx₀ : f x₀ ≠ 0) {e : J → I} (a : J → K) {δ : ℝ}
    (hδ : ∀ x, ‖f x - ∑ j, a j * y (e j) x‖ ≤ δ) :
    ‖∑ j, a j * y (e j) x₀ / f x₀ * p.2 (e j) - p.1‖ ≤ δ / ‖f x₀‖ := by
  obtain ⟨T, hT, hTf, hTy⟩ := hp
  have key := hT (f - ∑ j, a j • y (e j)) δ (fun x ↦ by simpa using hδ x) x₀
  have heq : ∑ j, a j * y (e j) x₀ / f x₀ * p.2 (e j) - p.1 =
      -T (f - ∑ j, a j • y (e j)) x₀ / f x₀ := by
    have hj (j : J) : a j * y (e j) x₀ / f x₀ * p.2 (e j) * f x₀ =
        a j * (p.2 (e j) * y (e j) x₀) := by
      field_simp
    rw [eq_div_iff hx₀, sub_mul, Finset.sum_mul]
    simp [hTf, hTy, hj]
  rw [heq, norm_div, norm_neg]
  exact div_le_div_of_nonneg_right key (norm_nonneg _)

/-- Let `f ≠ 0` be a function `X → K`, `K` a normed field, in the closure, for uniform
convergence, of the span of a set `S` of functions. Then there are `s : ℕ → ℕ`, coefficients
`c n i`, functions `y ⟨n, i⟩ ∈ S` for `i < s n` and a monoid `N` approximating along `atTop` for
`c`, such that for every `K`-linear operator `T` on functions `X → K` that does not increase the
sup norm (it maps functions bounded by `C` to functions bounded by `C`), with `T f = t • f` and
`T (y i) = φ i • y i` for all `i`, the pair `(t, φ)` lies in `N`. -/
theorem exists_isApproximating_of_mem_closure_span {S : Set (X → K)} {f : X → K} (hf₀ : f ≠ 0)
    (hf : UniformFun.ofFun f ∈
      closure (UniformFun.ofFun '' (Submodule.span K S : Set (X → K)))) :
    ∃ (s : ℕ → ℕ) (c : ∀ n, Fin (s n) → K) (y : (Σ n, Fin (s n)) → X → K)
      (N : Submonoid (K × ((Σ n, Fin (s n)) → K))),
      (∀ i, y i ∈ S) ∧ N.IsApproximating atTop c ∧
      ∀ (T : (X → K) →ₗ[K] X → K) (t : K) (φ : (Σ n, Fin (s n)) → K),
        (∀ (h : X → K) (C : ℝ), (∀ x, ‖h x‖ ≤ C) → ∀ x, ‖T h x‖ ≤ C) →
        T f = t • f → (∀ i, T (y i) = φ i • y i) → (t, φ) ∈ N := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ ≠ 0 := Function.ne_iff.mp hf₀
  have hfx₀ : 0 < ‖f x₀‖ := norm_pos_iff.2 hx₀
  -- For each `n`, a combination of members of `S` within `‖f x₀‖ / (n + 1)` of `f`.
  have happrox (n : ℕ) : ∃ (m : ℕ) (a : Fin m → K) (z : Fin m → S),
      ∀ x, ‖f x - ∑ i, a i * (z i : X → K) x‖ ≤ ‖f x₀‖ / (n + 1) := by
    obtain ⟨_, ⟨g, hg, rfl⟩, hfg⟩ :=
      EMetric.mem_closure_iff.1 hf (ENNReal.ofReal (‖f x₀‖ / (n + 1)))
        (ENNReal.ofReal_pos.2 (div_pos hfx₀ n.cast_add_one_pos))
    obtain ⟨m, a, z, rfl⟩ := Submodule.mem_span_set'.1 hg
    refine ⟨m, a, z, fun x ↦ ?_⟩
    have : ‖f x - (∑ i, a i • (z i : X → K)) x‖ < ‖f x₀‖ / (n + 1) := by
      simpa only [UniformFun.toFun_ofFun, edist_lt_ofReal, dist_eq_norm] using
        (UniformFun.edist_eval_le (x := x)).trans_lt hfg
    simpa using this.le
  choose s a z hz using happrox
  let y : (Σ n, Fin (s n)) → X → K := fun i ↦ z i.1 i.2
  refine ⟨s, fun n i ↦ a n i * y ⟨n, i⟩ x₀ / f x₀, y, (eigenvaluePairs f y).topologicalClosure,
    fun i ↦ (z i.1 i.2).property, Submonoid.isApproximating_topologicalClosure_iff.2 ?_,
    fun T t φ hT hTf hTy ↦ Submonoid.le_topologicalClosure _ ⟨T, hT, hTf, hTy⟩⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop n₀] with n hn p hp
  rw [dist_comm, dist_eq_norm]
  calc _ ≤ ‖f x₀‖ / (n + 1) / ‖f x₀‖ :=
        norm_sum_sub_le_of_mem_eigenvaluePairs hp hx₀ (e := Sigma.mk n) (a n) (hz n)
    _ = 1 / (n + 1) := by rw [div_div_cancel_left₀ hfx₀.ne', one_div]
    _ ≤ 1 / (n₀ + 1) := by gcongr
    _ < ε := hn₀

end TauCeti
