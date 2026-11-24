/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete

/-!
# Outer products and two-variable functionals on `C₀`

For topological spaces `α` and `β`, a seminormed ring `R`, and a seminormed `R`-module `E` with a
bounded scalar action, `a ∈ C₀(α, R)` and `b ∈ C₀(β, E)` form the elementary tensor
`ZeroAtInftyContinuousMap.prodSMul a b ∈ C₀(α × β, E)` (`(x, y) ↦ a x • b y`), satisfying
`‖prodSMul a b‖ ≤ ‖a‖ * ‖b‖` and `‖prodSMul a b‖ = ‖a‖ * ‖b‖` when scalar multiplication preserves
norms (`norm_prodSMul`).

For discrete index types `I` and `J`, the currying isometry
`ZeroAtInftyContinuousMap.curryEquiv : C₀(I × J, E) ≃ₗᵢ[S] C₀(I, C₀(J, E))` turns operations in
one variable at a time into two-variable operations on the product model space without auxiliary
topological tensor products:

* `ZeroAtInftyContinuousMap.prodSMul_single` and `ZeroAtInftyContinuousMap.curryEquiv_prodSMul`:
  elementary tensors send coordinate vectors to coordinate vectors and curry to coordinatewise
  scalar multiples of the second factor;
* `ZeroAtInftyContinuousMap.prodFunctional`: the continuous linear functional
  `C₀(I × J, R) →L[R] R` built from `u : C₀(I, R) →L[R] R` and a bounded
  `v : C₀(J, R) →L[R] R` by applying `v` to the rows and `u` to the resulting column.

On scalar elementary tensors `prodFunctional u v hv (prodSMul a b) = u a * v b`. Because coordinate
vectors span a dense submodule of `C₀(I × J, R)`, two-variable functionals satisfy Fubini symmetry
under `Homeomorph.prodComm` (`prodFunctional_comp_congrLeft_prodComm`) over any Hausdorff seminormed
commutative ring, with no completeness or ultrametric hypothesis. Over a nontrivially normed field,
the operator norm is multiplicative: `‖prodFunctional u v hv‖ = ‖u‖ * ‖v‖`.

## References

* P. Schneider, *Nonarchimedean Functional Analysis*, Springer, 2002, §§10 and 17.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS 12 (1962), 69–85.
-/

public section

open Filter Topology
open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

section OuterProduct

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

section BoundedSMul

variable {R E : Type*} [SeminormedRing R] [SeminormedAddCommGroup E] [Module R E]
  [IsBoundedSMul R E]

private theorem tendsto_cocompact_prodSMul (a : C₀(α, R)) (b : C₀(β, E)) :
    Tendsto (fun p : α × β ↦ a p.1 • b p.2) (cocompact (α × β)) (𝓝 0) := by
  rw [← Filter.coprod_cocompact, Filter.coprod, tendsto_sup]
  exact ⟨squeeze_zero_norm (fun p ↦ (norm_smul_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_coe_le_norm b p.2) (norm_nonneg _)))
      (by simpa using ((zero_at_infty a).norm.comp tendsto_comap).mul_const ‖b‖),
    squeeze_zero_norm (fun p ↦ (norm_smul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_coe_le_norm a p.1) (norm_nonneg _)))
      (by simpa using ((zero_at_infty b).norm.comp tendsto_comap).const_mul ‖a‖)⟩

/-- **Elementary tensor on a product space.** Given `a ∈ C₀(α, R)` and `b ∈ C₀(β, E)`, the
two-variable map `(x, y) ↦ a x • b y` is continuous and vanishes at infinity on `α × β`. -/
def prodSMul (a : C₀(α, R)) (b : C₀(β, E)) : C₀(α × β, E) where
  toFun p := a p.1 • b p.2
  continuous_toFun := (a.continuous.comp continuous_fst).smul (b.continuous.comp continuous_snd)
  zero_at_infty' := tendsto_cocompact_prodSMul a b

/-- `prodSMul a b` evaluates at `(x, y)` to `a x • b y`. -/
@[simp]
theorem prodSMul_apply (a : C₀(α, R)) (b : C₀(β, E)) (p : α × β) :
    prodSMul a b p = a p.1 • b p.2 := (rfl)

/-- The sup norm of `prodSMul a b` is at most `‖a‖ * ‖b‖`. -/
theorem norm_prodSMul_le (a : C₀(α, R)) (b : C₀(β, E)) :
    ‖prodSMul a b‖ ≤ ‖a‖ * ‖b‖ :=
  (norm_le (by positivity)).2 fun p ↦ (norm_smul_le (a p.1) (b p.2)).trans
    (mul_le_mul (norm_coe_le_norm a p.1) (norm_coe_le_norm b p.2)
      (norm_nonneg _) (norm_nonneg _))

/-- An elementary tensor with `0` on the left is `0`. -/
@[simp]
theorem prodSMul_zero_left (b : C₀(β, E)) : prodSMul (0 : C₀(α, R)) b = 0 := by
  ext; simp

/-- An elementary tensor with `0` on the right is `0`. -/
@[simp]
theorem prodSMul_zero_right (a : C₀(α, R)) : prodSMul a (0 : C₀(β, E)) = 0 := by
  ext; simp

/-- `prodSMul` is additive in its first argument. -/
theorem prodSMul_add_left (a₁ a₂ : C₀(α, R)) (b : C₀(β, E)) :
    prodSMul (a₁ + a₂) b = prodSMul a₁ b + prodSMul a₂ b := by
  ext; simp [add_smul]

/-- `prodSMul` is additive in its second argument. -/
theorem prodSMul_add_right (a : C₀(α, R)) (b₁ b₂ : C₀(β, E)) :
    prodSMul a (b₁ + b₂) = prodSMul a b₁ + prodSMul a b₂ := by
  ext; simp

/-- `prodSMul` associates with compatible scalar multiplication in its first argument. -/
theorem prodSMul_smul_left {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
    [SMulZeroClass S E] [ContinuousConstSMul S E] [IsScalarTower S R E]
    (s : S) (a : C₀(α, R)) (b : C₀(β, E)) :
    prodSMul (s • a) b = s • prodSMul a b := by
  ext; simp [smul_assoc]

/-- `prodSMul` commutes with compatible scalar multiplication in its second argument. -/
theorem prodSMul_smul_right {S : Type*} [SMulZeroClass S E] [ContinuousConstSMul S E]
    [SMulCommClass R S E] (s : S) (a : C₀(α, R)) (b : C₀(β, E)) :
    prodSMul a (s • b) = s • prodSMul a b := by
  ext; simp [smul_comm]

/-- Reassociating `(α × β) × γ` to `α × (β × γ)` reassociates iterated elementary tensors. -/
theorem congrLeft_prodAssoc_prodSMul {S : Type*} [Semiring S] [Module S E] [ContinuousConstSMul S E]
    (a : C₀(α, R)) (b : C₀(β, R)) (c : C₀(γ, E)) :
    congrLeft S E (Homeomorph.prodAssoc α β γ) (prodSMul (prodSMul a b) c) =
      prodSMul a (prodSMul b c) := by
  ext ⟨x, y, z⟩; simp [Homeomorph.prodAssoc, mul_smul]

end BoundedSMul

/-- When scalar multiplication preserves norms, `‖prodSMul a b‖ = ‖a‖ * ‖b‖`. -/
@[simp]
theorem norm_prodSMul {R E : Type*} [SeminormedRing R] [SeminormedAddCommGroup E] [Module R E]
    [NormSMulClass R E] (a : C₀(α, R)) (b : C₀(β, E)) :
    ‖prodSMul a b‖ = ‖a‖ * ‖b‖ := by
  refine le_antisymm (norm_prodSMul_le a b) ?_
  rcases (norm_nonneg b).eq_or_lt with hb | hb
  · rw [← hb, mul_zero]
    exact norm_nonneg _
  · rw [← le_div_iff₀ hb]
    refine (norm_le (by positivity)).2 fun x ↦ ?_
    rw [le_div_iff₀ hb]
    rcases (norm_nonneg (a x)).eq_or_lt with hax | hax
    · rw [← hax, zero_mul]
      exact norm_nonneg _
    · rw [← le_div_iff₀' hax]
      refine (norm_le (by positivity)).2 fun y ↦ ?_
      rw [le_div_iff₀' hax, ← norm_smul]
      exact norm_coe_le_norm (prodSMul a b) (x, y)

/-- Over a commutative seminormed ring, swapping `α × β` swaps elementary tensor factors. -/
@[simp]
theorem congrLeft_prodComm_prodSMul {R : Type*} [SeminormedCommRing R]
    (a : C₀(α, R)) (b : C₀(β, R)) :
    congrLeft R R (Homeomorph.prodComm α β) (prodSMul a b) = prodSMul b a := by
  ext ⟨y, x⟩; simp [mul_comm]

section Discrete

variable {I J R E : Type*} [TopologicalSpace I] [DiscreteTopology I]
  [TopologicalSpace J] [DiscreteTopology J]
  [SeminormedRing R] [SeminormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]

/-- On discrete index types, the elementary tensor of two coordinate vectors is a coordinate
vector. -/
@[simp]
theorem prodSMul_single [DecidableEq I] [DecidableEq J] (i : I) (r : R) (j : J) (e : E) :
    prodSMul (single i r) (single j e) = single (i, j) (r • e) := by
  ext ⟨i', j'⟩
  by_cases hi : i' = i <;> by_cases hj : j' = j <;> simp [single_apply, hi, hj]

/-- Currying `prodSMul a b` scales the second factor by the coordinates of the first. -/
@[simp]
theorem curryEquiv_prodSMul {S : Type*} [Semiring S] [Module S E] [ContinuousConstSMul S E]
    (a : C₀(I, R)) (b : C₀(J, E)) (i : I) :
    curryEquiv S E (prodSMul a b) i = a i • b := by
  ext j; simp

/-- Currying `prodSMul a b` applies coordinatewise right scalar multiplication by `b` to `a`. -/
theorem curryEquiv_prodSMul_eq_compLeft {S : Type*} [Semiring S]
    [Module S R] [ContinuousConstSMul S R] [Module S E] [ContinuousConstSMul S E]
    [IsScalarTower S R E] (a : C₀(I, R)) (b : C₀(J, E)) :
    curryEquiv S E (prodSMul a b) =
      compLeft ((ContinuousLinearMap.toSpanSingleton R b).restrictScalars S)
        ⟨‖b‖, fun r ↦ by
          simpa only [ContinuousLinearMap.coe_restrictScalars',
            ContinuousLinearMap.toSpanSingleton_apply, mul_comm ‖b‖] using norm_smul_le r b⟩ a := by
  ext i j; simp

end Discrete

end OuterProduct

section ProdFunctional

variable {I J R : Type*}
  [TopologicalSpace I] [DiscreteTopology I]
  [TopologicalSpace J] [DiscreteTopology J]

section SeminormedRing

variable [SeminormedRing R]

/-- **Product of two continuous linear functionals on discrete model spaces.** Given
`u : C₀(I, R) →L[R] R` and a uniformly bounded `v : C₀(J, R) →L[R] R`, `prodFunctional u v hv`
applies `v` to each row `j ↦ f (i, j)` via `curryEquiv` and then applies `u` to the resulting
family on `I`. -/
noncomputable def prodFunctional (u : C₀(I, R) →L[R] R) (v : C₀(J, R) →L[R] R)
    (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) : C₀(I × J, R) →L[R] R :=
  u ∘L compLeft v hv ∘L (curryEquiv (I := I) (J := J) R R).toLinearIsometry.toContinuousLinearMap

/-- `prodFunctional u v hv` evaluates `v` on the curried rows and `u` on the result. -/
theorem prodFunctional_apply (u : C₀(I, R) →L[R] R) (v : C₀(J, R) →L[R] R)
    (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) (f : C₀(I × J, R)) :
    prodFunctional u v hv f = u (compLeft v hv (curryEquiv R R f)) := (rfl)

/-- A product functional does not depend on the witness of boundedness of its second factor. -/
theorem prodFunctional_congr_bound (u : C₀(I, R) →L[R] R) (v : C₀(J, R) →L[R] R)
    (hv₁ hv₂ : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) :
    prodFunctional u v hv₁ = prodFunctional u v hv₂ := (rfl)

/-- A product functional with `0` on the left is `0`. -/
@[simp]
theorem prodFunctional_zero_left (v : C₀(J, R) →L[R] R) (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) :
    prodFunctional (0 : C₀(I, R) →L[R] R) v hv = 0 := by
  ext; simp [prodFunctional_apply]

/-- A product functional with `0` on the right is `0`. -/
@[simp]
theorem prodFunctional_zero_right (u : C₀(I, R) →L[R] R)
    (hv : ∃ C, ∀ y, ‖(0 : C₀(J, R) →L[R] R) y‖ ≤ C * ‖y‖) :
    prodFunctional u (0 : C₀(J, R) →L[R] R) hv = 0 := by
  ext f
  simp [prodFunctional_apply]

/-- `prodFunctional` is additive in its first factor. -/
theorem prodFunctional_add_left (u₁ u₂ : C₀(I, R) →L[R] R) (v : C₀(J, R) →L[R] R)
    (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) :
    prodFunctional (u₁ + u₂) v hv = prodFunctional u₁ v hv + prodFunctional u₂ v hv := by
  ext; simp [prodFunctional_apply]

/-- `prodFunctional` is additive in its second factor. -/
theorem prodFunctional_add_right (u : C₀(I, R) →L[R] R) (v₁ v₂ : C₀(J, R) →L[R] R)
    (hv₁ : ∃ C, ∀ y, ‖v₁ y‖ ≤ C * ‖y‖) (hv₂ : ∃ C, ∀ y, ‖v₂ y‖ ≤ C * ‖y‖)
    (hv : ∃ C, ∀ y, ‖(v₁ + v₂) y‖ ≤ C * ‖y‖) :
    prodFunctional u (v₁ + v₂) hv = prodFunctional u v₁ hv₁ + prodFunctional u v₂ hv₂ := by
  ext f
  simp [prodFunctional_apply, compLeft_add v₁ v₂ hv₁ hv₂ hv]

/-- If `u` is bounded by `C₁ ≥ 0` and `v` is bounded by `C₂`, then `prodFunctional u v hv` is
bounded by `C₁ * C₂`. -/
theorem norm_prodFunctional_apply_le (u : C₀(I, R) →L[R] R) (v : C₀(J, R) →L[R] R)
    (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) {C₁ C₂ : ℝ} (hC₁₀ : 0 ≤ C₁)
    (hC₁ : ∀ x, ‖u x‖ ≤ C₁ * ‖x‖) (hC₂ : ∀ y, ‖v y‖ ≤ C₂ * ‖y‖) (f : C₀(I × J, R)) :
    ‖prodFunctional u v hv f‖ ≤ (C₁ * C₂) * ‖f‖ := by
  rw [prodFunctional_apply, mul_assoc]
  refine (hC₁ _).trans (mul_le_mul_of_nonneg_left ?_ hC₁₀)
  exact (norm_compLeft_apply_le v hC₂ (curryEquiv R R f)).trans_eq
    (by rw [(curryEquiv R R).norm_map])

end SeminormedRing

section SeminormedCommRing

variable [SeminormedCommRing R]

/-- On a scalar elementary tensor, `prodFunctional u v hv` multiplies the values of `u` and `v`. -/
@[simp]
theorem prodFunctional_prodSMul (u : C₀(I, R) →L[R] R) (v : C₀(J, R) →L[R] R)
    (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) (a : C₀(I, R)) (b : C₀(J, R)) :
    prodFunctional u v hv (prodSMul a b) = u a * v b := by
  have hrow : compLeft v hv (curryEquiv R R (prodSMul a b)) = v b • a := by
    ext i
    simp [mul_comm]
  rw [prodFunctional_apply, hrow, map_smul, smul_eq_mul, mul_comm]

/-- On a coordinate vector, `prodFunctional u v hv` multiplies the values on the unit coordinate
vectors. -/
@[simp]
theorem prodFunctional_single [DecidableEq I] [DecidableEq J]
    (u : C₀(I, R) →L[R] R) (v : C₀(J, R) →L[R] R) (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖)
    (i : I) (j : J) (r : R) :
    prodFunctional u v hv (single (i, j) r) = r * (u (single i 1) * v (single j 1)) := by
  have hsingle : single (i, j) r = prodSMul (single i r) (single j (1 : R)) := by
    rw [prodSMul_single, smul_eq_mul, mul_one]
  rw [hsingle, prodFunctional_prodSMul, ← smul_single_one i r, map_smul, smul_eq_mul, mul_assoc]

/-- `prodFunctional` commutes with scalar multiplication in its first factor. -/
theorem prodFunctional_smul_left (r : R) (u : C₀(I, R) →L[R] R) (v : C₀(J, R) →L[R] R)
    (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) :
    prodFunctional (r • u) v hv = r • prodFunctional u v hv := by
  ext; simp [prodFunctional_apply]

/-- `prodFunctional` commutes with scalar multiplication in its second factor. -/
theorem prodFunctional_smul_right (r : R) (u : C₀(I, R) →L[R] R) (v : C₀(J, R) →L[R] R)
    (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) (hrv : ∃ C, ∀ y, ‖(r • v) y‖ ≤ C * ‖y‖) :
    prodFunctional u (r • v) hrv = r • prodFunctional u v hv := by
  ext f
  simp [prodFunctional_apply, compLeft_smul r v hv hrv]

/-- **Fubini symmetry for bounded model-space functionals.** Swapping the two indices exchanges
the two factors of `prodFunctional`. -/
theorem prodFunctional_comp_congrLeft_prodComm [T2Space R]
    (u : C₀(I, R) →L[R] R) (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖)
    (v : C₀(J, R) →L[R] R) (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) :
    (prodFunctional v u hu).comp
        (congrLeft R R (Homeomorph.prodComm I J)).toLinearIsometry.toContinuousLinearMap =
      prodFunctional u v hv := by
  classical
  refine continuousLinearMap_ext_single_one fun ij ↦ ?_
  rcases ij with ⟨i, j⟩
  simp [mul_comm]

end SeminormedCommRing

section NontriviallyNormedField

variable {K : Type*} [NontriviallyNormedField K]

/-- Over a nontrivially normed field, the operator norm of `prodFunctional u v` equals the product
of the operator norms `‖u‖ * ‖v‖`. -/
@[simp]
theorem opNorm_prodFunctional (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K)
    (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) :
    ‖prodFunctional u v hv‖ = ‖u‖ * ‖v‖ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      (norm_prodFunctional_apply_le u v hv (norm_nonneg u) u.le_opNorm v.le_opNorm)
  · rcases eq_or_lt_of_le (norm_nonneg u) with hu0 | hu0
    · rw [← hu0, zero_mul]
      exact norm_nonneg (prodFunctional u v hv)
    · have hvb (b : C₀(J, K)) : ‖u‖ * ‖v b‖ ≤ ‖prodFunctional u v hv‖ * ‖b‖ := by
        rcases eq_or_lt_of_le (norm_nonneg (v b)) with hvb0 | hvb0
        · rw [← hvb0, mul_zero]
          exact mul_nonneg (norm_nonneg (prodFunctional u v hv)) (norm_nonneg b)
        · rw [← le_div_iff₀ hvb0]
          refine ContinuousLinearMap.opNorm_le_bound u
            (div_nonneg (mul_nonneg (norm_nonneg (prodFunctional u v hv)) (norm_nonneg b))
              hvb0.le) fun a ↦ ?_
          rw [div_mul_eq_mul_div, le_div_iff₀ hvb0]
          calc
            ‖u a‖ * ‖v b‖ = ‖u a * v b‖ := (norm_mul (u a) (v b)).symm
            _ = ‖prodFunctional u v hv (prodSMul a b)‖ := by rw [prodFunctional_prodSMul]
            _ ≤ ‖prodFunctional u v hv‖ * ‖prodSMul a b‖ :=
              (prodFunctional u v hv).le_opNorm (prodSMul a b)
            _ = ‖prodFunctional u v hv‖ * ‖b‖ * ‖a‖ := by rw [norm_prodSMul]; ring
      rw [← le_div_iff₀' hu0]
      refine ContinuousLinearMap.opNorm_le_bound v
        (div_nonneg (norm_nonneg (prodFunctional u v hv)) hu0.le) fun b ↦ ?_
      rw [div_mul_eq_mul_div, le_div_iff₀' hu0]
      exact hvb b

end NontriviallyNormedField

end ProdFunctional

end ZeroAtInftyContinuousMap
