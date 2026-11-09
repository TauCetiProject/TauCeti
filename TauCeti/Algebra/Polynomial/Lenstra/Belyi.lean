/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Belyi
public import TauCeti.Algebra.Polynomial.Lenstra.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import TauCeti.Algebra.Polynomial.Decomposition

/-!
# Lenstra's Belyi polynomials and faithfulness of the Galois action

Let `K` be a field of characteristic zero and `α ∈ K` algebraic over `ℚ`. Lenstra's polynomial
`p_α = TauCeti.lenstraPolynomial α` has critical points `0`, `1` and `α`, whose critical values
are algebraic over `ℚ`. Polynomial Belyification of algebraic numbers gives a nonconstant
`q ∈ ℚ[X]` carrying these values into `{0, 1}` with all its own critical values in `{0, 1}`, so
`P_α = q ∘ p_α` is a Belyi polynomial: all its critical values, in every field extension of `K`,
lie in `{0, 1}`.

Since `q` has rational coefficients, applying a field homomorphism `σ` to the coefficients of
`P_α` gives `q ∘ p_{σ(α)}`. Conversely, `P_α` remembers `α` up to affine changes of variable: if
`f ∘ p_α ∘ (a X + b) = g ∘ p_β` with `f` nonconstant and `α, β ∉ {0, 1}`, the decomposition lemma
`Polynomial.eq_C_mul_add_C_of_comp_eq_comp` makes `p_α ∘ (a X + b)` an affine function of `p_β`,
and the distinct multiplicities of the critical points of Lenstra's polynomial force `a = 1`,
`b = 0` and `α = β`.

Together: for every field endomorphism `σ ≠ id` of a field `K` algebraic over `ℚ`, such as
`AlgebraicClosure ℚ`, there is a Belyi polynomial `P` over `K` such that no affine change of
variable carries `P` to its conjugate `P^σ`. Polynomial Belyi maps related by an affine change
of variable are exactly the isomorphic ones, so this is the polynomial form of the faithfulness
of the action of the absolute Galois group of `ℚ` on Belyi maps, and hence on dessins d'enfants
(trees, here).

## Main results

* `TauCeti.exists_criticalValues_comp_lenstraPolynomial_subset`: for `α` integral over `ℚ`,
  some `q ∘ p_α` with `q ∈ ℚ[X]` nonconstant has all its critical values in `{0, 1}`.
* `Polynomial.map_comp_lenstraPolynomial`: `(q ∘ p_α)^σ = q ∘ p_{σ(α)}` for `q ∈ ℚ[X]`.
* `TauCeti.eq_of_comp_lenstraPolynomial_comp_eq`: `f ∘ p_α ∘ (a X + b) = g ∘ p_β` forces `a = 1`,
  `b = 0` and `α = β`.
* `TauCeti.comp_lenstraPolynomial_comp_ne_map`: if `σ(α) ≠ α`, then no affine change of variable
  carries `q ∘ p_α` to its conjugate under `σ`.
* `TauCeti.exists_polynomial_criticalValues_subset_comp_ne_map`: a field endomorphism `σ ≠ id` of
  a field algebraic over `ℚ` moves some Belyi polynomial off its affine equivalence class.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  Theorem 4.49 (the proof attributed there to Lenstra) and Lemma 4.50.
-/

public section

open Polynomial IntermediateField

namespace TauCeti

universe v

variable {K : Type*} [Field K] [CharZero K]

/-- **Lenstra's Belyi polynomial.** For `α` integral over `ℚ` there is a nonconstant `q ∈ ℚ[X]`
such that `q ∘ p_α`, with `p_α = lenstraPolynomial α`, has all its critical values in `{0, 1}`,
in every field extension of `K`. -/
theorem exists_criticalValues_comp_lenstraPolynomial_subset {α : K} (hα : IsIntegral ℚ α) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧ ∀ (L : Type v) [Field L] [Algebra K L],
      ((q.map (algebraMap ℚ K)).comp (lenstraPolynomial α)).criticalValues L ⊆ {0, 1} := by
  classical
  -- The critical values `p_α(0)`, `p_α(1)`, `p_α(α)` lie in `ℚ⟮α⟯`, so are algebraic over `ℚ`.
  have hS : ∀ s ∈ ({0, 1, α} : Finset K).image (lenstraPolynomial α).eval, IsIntegral ℚ s := by
    have := adjoin.finiteDimensional hα
    have hmap : (lenstraPolynomial (AdjoinSimple.gen ℚ α)).map
        (algebraMap ℚ⟮α⟯ K) = lenstraPolynomial α := by
      rw [RingHom.map_lenstraPolynomial, AdjoinSimple.algebraMap_gen]
    have hint (y : ℚ⟮α⟯) : IsIntegral ℚ ((lenstraPolynomial α).eval (algebraMap ℚ⟮α⟯ K y)) := by
      rw [← hmap, eval_map_algebraMap, aeval_algebraMap_apply]
      exact (IsIntegral.of_finite ℚ _).algebraMap
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    rintro _ ⟨x, hx | hx | hx, rfl⟩
    · simpa [hx] using hint 0
    · simpa [hx] using hint 1
    · simpa [hx] using hint (AdjoinSimple.gen ℚ α)
  obtain ⟨q, hq, hqS, hqcrit⟩ := exists_polynomial_aeval_mem_criticalValues_subset.{v} hS
  refine ⟨q, hq, fun L _ _ ↦ ?_⟩
  let : Algebra ℚ L := ((algebraMap K L).comp (algebraMap ℚ K)).toAlgebra
  have : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq' rfl
  refine (criticalValues_comp_subset _ _).trans (Set.union_subset ?_ ?_)
  · -- The critical points of `p_α` in `L` are `0`, `1` and `α`, all coming from `K`.
    rintro _ ⟨_, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := mem_criticalValues.mp hy
    have hx' : x = algebraMap K L 0 ∨ x = algebraMap K L 1 ∨ x = algebraMap K L α := by
      have := aeval_eq_zero_of_mem_rootSet hx
      simpa [sub_eq_zero, or_assoc] using this
    obtain ⟨x₀, hx₀, rfl⟩ : ∃ x₀ ∈ ({0, 1, α} : Finset K), x = algebraMap K L x₀ := by
      rcases hx' with h | h | h <;> exact ⟨_, by simp, h⟩
    simp only [aeval_algebraMap_apply, aeval_map_algebraMap, coe_aeval_eq_eval]
    obtain h | h : aeval ((lenstraPolynomial α).eval x₀) q = 0 ∨
        aeval ((lenstraPolynomial α).eval x₀) q = 1 := hqS _ (Finset.mem_image_of_mem _ hx₀)
    all_goals simp [h]
  · rw [criticalValues_map]
    exact hqcrit L

variable {K' : Type*} [Field K'] [CharZero K']

/-- Applying a field homomorphism `σ` to the coefficients of `q ∘ p_α`, for `q` with rational
coefficients, gives `q ∘ p_{σ(α)}`. -/
theorem _root_.Polynomial.map_comp_lenstraPolynomial (q : ℚ[X]) (σ : K →+* K') (α : K) :
    ((q.map (algebraMap ℚ K)).comp (lenstraPolynomial α)).map σ =
      (q.map (algebraMap ℚ K')).comp (lenstraPolynomial (σ α)) := by
  rw [map_comp, Polynomial.map_map, Subsingleton.elim (σ.comp (algebraMap ℚ K)),
    RingHom.map_lenstraPolynomial]

/-- **Rigidity of composites with Lenstra's polynomial.** If `f ∘ p_α ∘ (a X + b) = g ∘ p_β`
with `f` nonconstant, `a ≠ 0` and `α, β ∉ {0, 1}`, then the affine change of variable is the
identity and `α = β`. -/
theorem eq_of_comp_lenstraPolynomial_comp_eq {f g : K[X]} {α β a b : K} (hf : 0 < f.natDegree)
    (hα0 : α ≠ 0) (hα1 : α ≠ 1) (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) (ha : a ≠ 0)
    (h : (f.comp (lenstraPolynomial α)).comp (C a * X + C b) = g.comp (lenstraPolynomial β)) :
    a = 1 ∧ b = 0 ∧ α = β := by
  set p := (lenstraPolynomial α).comp (C a * X + C b) with hp
  have hpdeg : p.natDegree = 7 := by
    rw [hp, natDegree_comp, natDegree_lenstraPolynomial, natDegree_linear ha]
  rw [comp_assoc, ← hp] at h
  -- The decomposition lemma makes `p_β` an affine function of `p`.
  obtain ⟨c, d, hpq⟩ : ∃ c d : K, lenstraPolynomial β = C c * p + C d :=
    ⟨_, _, eq_C_mul_add_C_of_comp_eq_comp hf (by omega) (by simp [hpdeg]) h⟩
  have hc : c ≠ 0 := by
    rintro rfl
    simpa using congrArg natDegree hpq
  have hpβ : p = C c⁻¹ * lenstraPolynomial β + C (-(c⁻¹ * d)) := by
    have hcc : C c⁻¹ * C c = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hc, C_1]
    simp only [hpq, map_neg, map_mul]
    linear_combination (-p) * hcc
  obtain ⟨ha1, hb, hαβ, -⟩ :=
    (lenstraPolynomial_comp_affine_eq_iff hα0 hα1 hβ0 hβ1 (inv_ne_zero hc)).mp hpβ
  exact ⟨ha1, hb, hαβ⟩

/-- If a field endomorphism `σ` moves `α`, then no affine change of variable carries `q ∘ p_α`,
for a nonconstant `q` with rational coefficients, to its conjugate under `σ`. -/
theorem comp_lenstraPolynomial_comp_ne_map {q : ℚ[X]} (hq : 0 < q.natDegree) {σ : K →+* K}
    {α : K} (hα : σ α ≠ α) {a : K} (ha : a ≠ 0) (b : K) :
    ((q.map (algebraMap ℚ K)).comp (lenstraPolynomial α)).comp (C a * X + C b) ≠
      ((q.map (algebraMap ℚ K)).comp (lenstraPolynomial α)).map σ := by
  -- `σ` fixes `0` and `1`, so neither `α` nor `σ α` is `0` or `1`.
  have h0 : α ≠ 0 := by rintro rfl; exact hα (map_zero σ)
  have h1 : α ≠ 1 := by rintro rfl; exact hα (map_one σ)
  intro h
  rw [map_comp_lenstraPolynomial] at h
  exact hα (eq_of_comp_lenstraPolynomial_comp_eq (by rwa [natDegree_map]) h0 h1
    ((map_ne_zero σ).mpr h0) (fun h' ↦ h1 (σ.injective (h'.trans (map_one σ).symm))) ha h).2.2.symm

/-- **Faithfulness of the Galois action on Belyi polynomials.** Let `K` be a field algebraic over
`ℚ`, such as `AlgebraicClosure ℚ`. For every field endomorphism `σ ≠ id` of `K` there is a
nonconstant polynomial `P` over `K` with all its critical values in `{0, 1}`, in every field
extension of `K`, such that no affine change of variable carries `P` to its conjugate `P^σ`. -/
theorem exists_polynomial_criticalValues_subset_comp_ne_map [Algebra.IsAlgebraic ℚ K]
    {σ : K →+* K} (hσ : σ ≠ RingHom.id K) :
    ∃ P : K[X], 0 < P.natDegree ∧
      (∀ (L : Type v) [Field L] [Algebra K L], P.criticalValues L ⊆ {0, 1}) ∧
      ∀ a b : K, a ≠ 0 → P.comp (C a * X + C b) ≠ P.map σ := by
  obtain ⟨α, hα⟩ : ∃ α, σ α ≠ α := by
    by_contra! h
    exact hσ (RingHom.ext h)
  obtain ⟨q, hq, hcrit⟩ :=
    exists_criticalValues_comp_lenstraPolynomial_subset.{v} (Algebra.IsIntegral.isIntegral α)
  refine ⟨_, ?_, hcrit, fun a b ha ↦ comp_lenstraPolynomial_comp_ne_map hq hα ha b⟩
  rw [natDegree_comp, natDegree_map, natDegree_lenstraPolynomial]
  omega

end TauCeti
