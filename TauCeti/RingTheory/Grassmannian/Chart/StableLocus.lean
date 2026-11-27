/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Grassmannian.Chart.Locus
public import TauCeti.RingTheory.Grassmannian.StableLocus

/-!
# The lines stable under a nilpotent Jordan block

Let `M` be a free module of rank two over a commutative ring `R`, with basis `e₁ = b (inl 0)`,
`e₂ = b (inr 0)`, and let `t` be the nilpotent endomorphism with `t e₁ = 0` and `t e₂ = e₁`. This
file computes the `t`-stable points of the Grassmannian `G(1, A ⊗[R] M; A)` of rank-one quotients,
that is of lines, over every `R`-algebra `A`, including nonreduced ones.

A point of the chart at `e₂` (`Module.Grassmannian.chartBasisEquiv`) is the line spanned by
`e₁ + a e₂` for a unique `a ∈ A`. Since `t (e₁ + a e₂) = a e₁`, this line is `t`-stable exactly
when `a e₁ = c (e₁ + a e₂)` for some `c`, that is, when `a² = 0`
(`Module.Grassmannian.stableLocus_chartBasisEquiv_symm_eq_bot_iff_sq_eq_zero`). Every `t`-stable
line lies in this chart: over a residue field of `A`, a stable line containing `e₂` would contain
`t e₂ = e₁`, hence be everything (`Module.Grassmannian.mem_chart_of_stableLocus_eq_bot`). So the
`t`-stable lines over `A` are the lines of `e₁ + a e₂` with `a² = 0`, naturally in `A`
(`Module.Grassmannian.jordanBlockStableEquiv`). Over a reduced ring, such as a field, the only
stable line is the line of `e₁` (`Module.Grassmannian.stableLocus_eq_bot_iff_toSubmodule_eq_span`),
but over the dual numbers of a nontrivial ring `a = ε` gives a second one.

This is a test case for the scheme structure of the closed subscheme of stable submodules
(`Module.Grassmannian.schemeStableLocus`) on nonreduced test rings: here it is `Spec R[a]/(a²)`,
which is not reduced when `R` is nontrivial.

## Main definitions

* `Module.Grassmannian.jordanBlockStableEquiv b ht₁ ht₂ A`: the `t`-stable lines over `A` are the
  `a ∈ A` with `a² = 0`.

## Main results

* `Module.Grassmannian.stableLocus_chartBasisEquiv_symm_eq_bot_iff_sq_eq_zero`: the line of
  `e₁ + a e₂` is stable exactly when `a² = 0`.
* `Module.Grassmannian.mem_chart_of_stableLocus_eq_bot`: every stable line lies in the chart at
  `e₂`.
* `Module.Grassmannian.toSubmodule_jordanBlockStableEquiv_symm_apply` and
  `Module.Grassmannian.map_jordanBlockStableEquiv_symm_apply`: the stable line of `a` is spanned by
  `e₁ + a e₂`, naturally in `A`.
* `Module.Grassmannian.stableLocus_eq_bot_iff_toSubmodule_eq_span`: over a reduced ring the only
  stable line is the line of `e₁`.
-/

public section

universe u v w

open TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  (b : Basis (Fin 1 ⊕ Fin 1) R M) {t : Module.End R M}
  (ht₁ : t (b (.inl 0)) = 0) (ht₂ : t (b (.inr 0)) = b (.inl 0))
  {A : Type w} [CommRing A] [Algebra R A]

include ht₁ ht₂ in
/-- **The stable points of the chart.** The point of the chart at `e₂ = b (inr 0)` with matrix
`Φ`, the line spanned by `e₁ - Φ₀₀ e₂`, is stable under the nilpotent endomorphism `t` with
`t e₁ = 0` and `t e₂ = e₁` exactly when `Φ₀₀² = 0`. -/
theorem stableLocus_chartBasisEquiv_symm_eq_bot_iff_sq_eq_zero (Φ : Matrix (Fin 1) (Fin 1) A) :
    ((chartBasisEquiv b A).symm Φ).val.stableLocus t = ⊥ ↔ Φ 0 0 ^ 2 = 0 := by
  set B := Algebra.TensorProduct.basis A b
  set v := chartGraphVector b Φ 0
  have hv : v = B (.inl 0) - Φ 0 0 • B (.inr 0) := by
    simp [v, B, chartGraphVector_def, Algebra.TensorProduct.basis_apply]
  -- `t_A v = - Φ₀₀ e₁`
  have htv : t.baseChange A v = -(Φ 0 0 • B (.inl 0)) := by
    simp [hv, B, Algebra.TensorProduct.basis_apply, ht₁, ht₂]
  have hspan : ((chartBasisEquiv b A).symm Φ).val.toSubmodule = Submodule.span A {v} := by
    rw [toSubmodule_chartBasisEquiv_symm, Set.range_unique]
    rfl
  rw [stableLocus_eq_bot_iff, hspan, Module.End.mem_invtSubmodule, Submodule.span_le,
    Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_comap, htv,
    Submodule.mem_span_singleton]
  constructor
  · -- compare the coordinates of `c • v = - Φ₀₀ e₁` in the basis `B`
    rintro ⟨c, hc⟩
    have h₁ := congrArg (fun x ↦ B.repr x (.inl 0)) hc
    have h₂ := congrArg (fun x ↦ B.repr x (.inr 0)) hc
    simp only [hv, smul_sub, map_sub, map_smul, map_neg, Basis.repr_self, Finsupp.sub_apply,
      Finsupp.smul_apply, Finsupp.neg_apply, Finsupp.single_eq_same, ne_eq, reduceCtorEq,
      not_false_eq_true, Finsupp.single_eq_of_ne, smul_eq_mul, mul_one, mul_zero, sub_zero,
      zero_sub, neg_zero] at h₁ h₂
    rw [h₁] at h₂
    linear_combination h₂
  · intro h
    refine ⟨-Φ 0 0, ?_⟩
    rw [hv, smul_sub, smul_smul, neg_mul, ← pow_two, h, neg_zero, zero_smul, sub_zero, neg_smul]

include ht₂ in
/-- Over a field, a stable line lies in the chart at `e₂`: if it contained `e₂` it would contain
`t e₂ = e₁`, hence be everything. -/
private theorem mem_chart_of_stableLocus_eq_bot_of_field {K : Type w} [Field K] [Algebra R K]
    {N : G(1, K ⊗[R] M; K)} (hN : N.stableLocus t = ⊥) :
    N ∈ chart K (fun j ↦ (1 : K) ⊗ₜ[R] b (.inr j)) := by
  set B := Algebra.TensorProduct.basis K b
  have := Module.Finite.of_basis B
  rw [stableLocus_eq_bot_iff, Module.End.mem_invtSubmodule] at hN
  have h₂ : B (.inr 0) ∉ N.toSubmodule := by
    intro h
    have h₁ : B (.inl 0) ∈ N.toSubmodule := by
      simpa [B, Algebra.TensorProduct.basis_apply, ht₂] using hN h
    -- `N` would contain the basis `B`, and its quotient of dimension one would vanish
    have htop : N.toSubmodule = ⊤ := by
      rw [eq_top_iff, ← B.span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rcases i with i | i <;> obtain rfl := Subsingleton.elim i 0 <;> assumption
    have := N.finrank_quotient
    rw [htop, finrank_zero_of_subsingleton] at this
    exact zero_ne_one this
  rw [mem_chart_iff_sup_eq_top, Set.range_unique]
  exact (Submodule.sup_span_singleton_eq_top_iff (by simpa [B] using h₂)).2 N.finrank_quotient

include ht₂ in
/-- **Every stable line lies in the chart at `e₂`.** A point of `G(1, A ⊗[R] M; A)` stable under
`t` is a line spanned by `e₁ + a e₂` for some `a ∈ A`: at each residue field of `A` it is a
stable line, which does not contain `e₂`. -/
theorem mem_chart_of_stableLocus_eq_bot {N : G(1, A ⊗[R] M; A)} (hN : N.stableLocus t = ⊥) :
    N ∈ chart A (fun j ↦ (1 : A) ⊗ₜ[R] b (.inr j)) := by
  rw [← chartLocus_eq_top_iff]
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
  let := Ideal.Quotient.field m
  -- at the residue field `A ⧸ m` the line is stable, hence in the chart, so `m` cannot contain
  -- the chart locus
  have hK := mem_chart_of_stableLocus_eq_bot_of_field b ht₂
    (stableLocus_map_eq_bot hN (Ideal.Quotient.mkₐ R m))
  have hbot : (chartLocus N fun j ↦ (1 : A) ⊗ₜ[R] b (.inr j)).map (Ideal.Quotient.mkₐ R m) = ⊥ :=
    le_bot_iff.1 <| Ideal.map_le_iff_le_comap.2 fun x hx ↦ by
      simpa [Ideal.Quotient.eq_zero_iff_mem] using hle hx
  rw [map_mem_chart_iff, hbot] at hK
  exact bot_ne_top hK

include ht₁ ht₂ in
/-- **The lines stable under a nilpotent Jordan block.** For the endomorphism `t` of `M` with
`t e₁ = 0` and `t e₂ = e₁`, the `t`-stable points of `G(1, A ⊗[R] M; A)` are the lines spanned by
`e₁ + a e₂` with `a² = 0` (`Module.Grassmannian.toSubmodule_jordanBlockStableEquiv_symm_apply`),
naturally in `A` (`Module.Grassmannian.map_jordanBlockStableEquiv_symm_apply`). So the closed
subscheme of `t`-stable lines has the points of `Spec R[a]/(a²)`. -/
noncomputable def jordanBlockStableEquiv (A : Type w) [CommRing A] [Algebra R A] :
    {N : G(1, A ⊗[R] M; A) // N.toSubmodule ∈ Module.End.invtSubmodule (t.baseChange A)} ≃
      {a : A // a ^ 2 = 0} where
  toFun N := ⟨-chartBasisEquiv b A ⟨N.val, mem_chart_of_stableLocus_eq_bot b ht₂
      ((stableLocus_eq_bot_iff _ t).2 N.property)⟩ 0 0, by
    rw [neg_sq, ← stableLocus_chartBasisEquiv_symm_eq_bot_iff_sq_eq_zero b ht₁ ht₂,
      Equiv.symm_apply_apply, stableLocus_eq_bot_iff]
    exact N.property⟩
  invFun a := ⟨((chartBasisEquiv b A).symm (Matrix.of fun _ _ ↦ -a.val)).val, by
    rw [← stableLocus_eq_bot_iff, stableLocus_chartBasisEquiv_symm_eq_bot_iff_sq_eq_zero b ht₁ ht₂,
      Matrix.of_apply, neg_sq]
    exact a.property⟩
  left_inv N := Subtype.ext <| by
    obtain ⟨N, hN⟩ := N
    have hc := mem_chart_of_stableLocus_eq_bot b ht₂ ((stableLocus_eq_bot_iff N t).2 hN)
    -- the point of the chart is recovered from the single entry of its `1 × 1` matrix
    have h : (Matrix.of fun _ _ ↦ chartBasisEquiv b A ⟨N, hc⟩ 0 0) = chartBasisEquiv b A ⟨N, hc⟩ :=
      Matrix.ext fun i j ↦ by rw [Subsingleton.elim i 0, Subsingleton.elim j 0, Matrix.of_apply]
    simp only [neg_neg, h, Equiv.symm_apply_apply]
  right_inv a := Subtype.ext <| by
    simp only [Subtype.coe_eta, Equiv.apply_symm_apply, Matrix.of_apply, neg_neg]

include ht₁ ht₂ in
/-- **The stable line of `a`** is spanned by `e₁ + a e₂`. -/
theorem toSubmodule_jordanBlockStableEquiv_symm_apply (a : {a : A // a ^ 2 = 0}) :
    ((jordanBlockStableEquiv b ht₁ ht₂ A).symm a).val.toSubmodule =
      Submodule.span A {(1 : A) ⊗ₜ[R] b (.inl 0) + a.val • (1 : A) ⊗ₜ[R] b (.inr 0)} := by
  simp [jordanBlockStableEquiv, toSubmodule_chartBasisEquiv_symm, Set.range_unique,
    chartGraphVector_def]
  congr 2
  module

include ht₁ ht₂ in
/-- **The stable lines are natural in the algebra**: the base change along `f : A → B` of the
stable line of `a` is the stable line of `f a`. -/
theorem map_jordanBlockStableEquiv_symm_apply {B : Type w} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (a : {a : A // a ^ 2 = 0}) :
    map f ((jordanBlockStableEquiv b ht₁ ht₂ A).symm a).val =
      ((jordanBlockStableEquiv b ht₁ ht₂ B).symm
        ⟨f a.val, by rw [← map_pow, a.property, map_zero]⟩).val := by
  simp only [jordanBlockStableEquiv, Equiv.coe_fn_symm_mk, map_chartBasisEquiv_symm]
  congr 2
  ext
  simp

include ht₁ ht₂ in
/-- **Over a reduced ring there is a single stable line**, the line of `e₁`: a point of
`G(1, K ⊗[R] M; K)` is stable under `t` exactly when it is the line spanned by `e₁`. -/
theorem stableLocus_eq_bot_iff_toSubmodule_eq_span {K : Type w} [CommRing K] [IsReduced K]
    [Algebra R K]
    (N : G(1, K ⊗[R] M; K)) :
    N.stableLocus t = ⊥ ↔ N.toSubmodule = Submodule.span K {(1 : K) ⊗ₜ[R] b (.inl 0)} := by
  rw [stableLocus_eq_bot_iff]
  refine ⟨fun hN ↦ ?_, fun hN ↦ ?_⟩
  · -- the coordinate `a` of `N` satisfies `a² = 0`, so `a = 0`
    set a := jordanBlockStableEquiv b ht₁ ht₂ K ⟨N, hN⟩
    have ha : a.val = 0 := IsNilpotent.eq_zero ⟨2, a.property⟩
    have := toSubmodule_jordanBlockStableEquiv_symm_apply b ht₁ ht₂ a
    rwa [Equiv.symm_apply_apply, ha, zero_smul, add_zero] at this
  · rw [hN, Module.End.mem_invtSubmodule, Submodule.span_le, Set.singleton_subset_iff,
      SetLike.mem_coe, Submodule.mem_comap, LinearMap.baseChange_tmul, ht₁, tmul_zero]
    exact Submodule.zero_mem _

end Module.Grassmannian
