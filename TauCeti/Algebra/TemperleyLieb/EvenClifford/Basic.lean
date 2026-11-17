/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Star
public import TauCeti.LinearAlgebra.CliffordAlgebra.ScalarTrace.Positivity
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
-- Private: ring involution identities, basis coordinate transport, orthogonal generator and
-- even-bivector identities, functoriality of Clifford involutions, and real-form positivity are
-- used only inside proofs and internal transport constructions.
import TauCeti.Algebra.Ring.Idempotent.Basic
import TauCeti.Basic.Complex.BigOperators
import TauCeti.LinearAlgebra.Basis.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Conjugation
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
import TauCeti.LinearAlgebra.QuadraticForm.PosDef

/-!
# The even Clifford representation of the Temperley–Lieb algebra at `δ = √2`

At the loop parameter `δ = √2 = 2 cos (π / 4)` — corresponding to Jones index `δ² = 2` — the
Temperley–Lieb algebra `TemperleyLieb ℂ (√2 : ℂ) m` surjects onto the even complex Clifford
algebra `Cl_m⁰` of the standard sum-of-squares form on `ℂ^m` via a `ℂ`-algebra homomorphism
`F_m = evenCliffordHom m` that intertwines the Temperley–Lieb analytic adjoint with the
positive-form Clifford adjoint `a ↦ a† = cliffordAdjoint m a`.

Concretely, let `cliffordForm m` be `∑ i, (v i)²` on `Fin m → ℂ`, let `majorana m j` (`c_j`) be the
`j`-th standard basis generator in `CliffordAlgebra (cliffordForm m)`, satisfying `c_j² = 1` and
`c_j c_k = -c_k c_j` for `j ≠ k`, and set

  `cliffordProjection m j = 2⁻¹ • (1 + I • (c_j * c_{j + 1}))`.

Each `p_j = cliffordProjection m j` lies in the even subalgebra `EvenClifford m` (of complex
dimension `2 ^ (m - 1)`, with `2 ^ (0 - 1) = 1` at `m = 0`), is self-adjoint for the
conjugate-linear reversal `cliffordAdjoint m` (`a ↦ a†`) fixing the Majorana generators, is
idempotent (`p_j² = p_j`), satisfies `p_j p_k p_j = 2⁻¹ • p_j` for `|j - k| = 1`, and commutes with
`p_k` for `|j - k| ≥ 2`. Rescaling by `√2` therefore defines the `ℂ`-algebra homomorphism

  `F_m = evenCliffordHom m : TemperleyLieb ℂ (√2 : ℂ) m →ₐ[ℂ] EvenClifford m`

sending `e (√2 : ℂ) j` to `(√2 : ℂ) • p_j`.

* **Analytic adjoint and Parseval positivity**: transporting `CliffordAlgebra.complexConj ∘ reverse`
  from the standard positive-definite real form on `ℝ^m` along
  `QuadraticForm.baseChangeWeightedSumSquares` shows that
  `s_m (a† * a) = ∑_S |a_S|² ≥ 0` for `s_m = CliffordAlgebra.scalarTrace (cliffordForm m)`,
  vanishing only at `a = 0`.
* **Surjectivity**: adjacent Majorana products are recovered by
  `c_j * c_{j + 1} = (-I) • ((√2 : ℂ) • F_m (e j) - 1)`, general pairs `c_j * c_k` with `j < k`
  follow by telescoping multiplication, and `CliffordAlgebra.even_induction` shows these generate
  `EvenClifford m`.

Tower coordinate inclusions, the Markov trace identity, positivity of the Markov Hermitian form at
`δ = √2`, and the identification of the trace-radical Jones quotient with `EvenClifford m` are
established in `TauCeti.Algebra.TemperleyLieb.EvenClifford.Quotient`.

## Main definitions

* `TauCeti.TemperleyLieb.cliffordForm`: the standard sum-of-squares quadratic form on `Fin m → ℂ`.
* `TauCeti.TemperleyLieb.EvenClifford`: the even Clifford subalgebra
  `CliffordAlgebra.even (cliffordForm m)`.
* `TauCeti.TemperleyLieb.majorana`: the Majorana generators `c_j = ι (Pi.single j 1)`.
* `TauCeti.TemperleyLieb.cliffordAdjoint` and `TauCeti.TemperleyLieb.evenCliffordAdjoint`: the
  conjugate-linear reversal `a ↦ a†` fixing each `majorana m j`, and its restriction to
  `EvenClifford m`.
* `TauCeti.TemperleyLieb.cliffordProjection`: the self-adjoint idempotents
  `p_j = 2⁻¹ • (1 + I • (c_j * c_{j + 1}))`.
* `TauCeti.TemperleyLieb.evenCliffordHom`: the comparison map
  `TemperleyLieb ℂ (√2 : ℂ) m →ₐ[ℂ] EvenClifford m`.

## Main results

* `TauCeti.TemperleyLieb.finrank_evenClifford`: `finrank ℂ (EvenClifford m) = 2 ^ (m - 1)`.
* `TauCeti.TemperleyLieb.cliffordAdjoint_unique`: uniqueness of the conjugate-linear,
  product-reversing unital map fixing every Majorana generator.
* `TauCeti.TemperleyLieb.scalarTrace_cliffordAdjoint_mul`,
  `TauCeti.TemperleyLieb.scalarTrace_cliffordAdjoint_mul_self`,
  `TauCeti.TemperleyLieb.scalarTrace_cliffordAdjoint_mul_self_nonneg`, and
  `TauCeti.TemperleyLieb.scalarTrace_cliffordAdjoint_mul_self_eq_zero_iff`: sesquilinear and
  quadratic Parseval formulas, positivity, and faithfulness of
  `CliffordAlgebra.scalarTrace (cliffordForm m) (cliffordAdjoint m a * a)`.
* `TauCeti.TemperleyLieb.evenCliffordHom_surjective` and
  `TauCeti.TemperleyLieb.evenCliffordHom_star`: surjectivity and star compatibility of
  `evenCliffordHom`.

## Implementation notes

Mathlib already equips `CliffordAlgebra Q` with a `StarRing` instance representing complex-linear
Clifford conjugation `star = reverse ∘ involute`. Following `CliffordAlgebra.conjStar` in
`TauCeti.LinearAlgebra.CliffordAlgebra.Complexification`, the conjugate-linear analytic adjoint
fixing the Majorana generators is therefore exposed as the conjugate-linear map `cliffordAdjoint m`
rather than a competing `Star` instance. The scalar-part functional is
`CliffordAlgebra.scalarTrace` directly; its agreement with the empty-subset coordinate in the
ordered-product Majorana basis is `CliffordAlgebra.basis_repr_empty`.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
* K. Iohara, G. I. Lehrer and R. B. Zhang, *The Jones quotients of the Temperley–Lieb algebras*,
  arXiv:1702.08128, §5.3, Theorem 5.4 and §5.4, Proposition 5.5.
* K. Iohara, G. I. Lehrer and R. B. Zhang, *Temperley–Lieb at roots of unity, a fusion category and
  the Jones quotient*, Math. Res. Lett. 26 (2019), no. 1, 121–158.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4.
-/

public section

open scoped ComplexConjugate ComplexOrder TensorProduct

namespace TauCeti.TemperleyLieb

/-! ### Arithmetic helpers for `√2` in `ℂ` -/

/-- Registers `IsSelfAdjoint (Real.sqrt 2 : ℂ)` as a `Fact` so that
`TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m` carries the analytic adjoint instances
`TemperleyLieb.instStarRing` and `TemperleyLieb.instStarModule`. -/
instance : Fact (IsSelfAdjoint (Real.sqrt 2 : ℂ)) :=
  ⟨Complex.conj_ofReal _⟩

private theorem sqrt_two_coe_mul_self :
    (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  exact_mod_cast Real.mul_self_sqrt zero_le_two

/-! ### The quadratic form, even Clifford carrier, and Majorana generators -/

/-- The standard sum-of-squares quadratic form `v ↦ ∑ i, v i * v i` on `Fin m → ℂ`. -/
noncomputable def cliffordForm (m : ℕ) : QuadraticForm ℂ (Fin m → ℂ) :=
  QuadraticMap.weightedSumSquares ℂ (1 : Fin m → ℂ)

/-- Unfolding `cliffordForm` as `QuadraticMap.weightedSumSquares`. -/
theorem cliffordForm_eq_weightedSumSquares (m : ℕ) :
    cliffordForm m = QuadraticMap.weightedSumSquares ℂ (1 : Fin m → ℂ) :=
  (rfl)

/-- Coordinate formula for `cliffordForm m`. -/
theorem cliffordForm_apply (m : ℕ) (v : Fin m → ℂ) :
    cliffordForm m v = ∑ i, v i * v i := by
  simp [cliffordForm_eq_weightedSumSquares, QuadraticMap.weightedSumSquares_apply]

/-- The symmetric bilinear form associated to `cliffordForm m` is the standard dot product. -/
@[simp]
theorem associated_cliffordForm (m : ℕ) (v w : Fin m → ℂ) :
    QuadraticMap.associated (cliffordForm m) v w = ∑ i, v i * w i := by
  simp [cliffordForm_eq_weightedSumSquares]

/-- Evaluating `cliffordForm m` on a single-coordinate vector squares the coordinate. -/
@[simp]
theorem cliffordForm_single (m : ℕ) (j : Fin m) (z : ℂ) :
    cliffordForm m (Pi.single j z) = z * z := by
  rw [cliffordForm_eq_weightedSumSquares, QuadraticMap.weightedSumSquares_apply_single]
  simp

/-- Distinct standard coordinate vectors are orthogonal for `cliffordForm m`. -/
theorem isOrtho_cliffordForm_single {m : ℕ} {j k : Fin m} (hjk : j ≠ k) (z w : ℂ) :
    (cliffordForm m).IsOrtho (Pi.single j z) (Pi.single k w) :=
  QuadraticMap.isOrtho_weightedSumSquares_single (1 : Fin m → ℂ) hjk z w

/-- The standard basis `Pi.basisFun ℂ (Fin m)` is orthogonal for `cliffordForm m`. -/
theorem isOrthoᵢ_associated_cliffordForm (m : ℕ) :
    (QuadraticMap.associated (cliffordForm m)).IsOrthoᵢ (Pi.basisFun ℂ (Fin m)) :=
  QuadraticMap.isOrthoᵢ_associated_weightedSumSquares (1 : Fin m → ℂ)

/-- The standard sum-of-squares form `cliffordForm m` is nondegenerate for every `m`. -/
theorem nondegenerate_cliffordForm (m : ℕ) : (cliffordForm m).Nondegenerate := by
  rw [cliffordForm_eq_weightedSumSquares]
  exact QuadraticMap.nondegenerate_weightedSumSquares fun _ ↦ isRegular_one

/-- The **even complex Clifford algebra** `Cl_m⁰` of `cliffordForm m`. -/
noncomputable abbrev EvenClifford (m : ℕ) : Subalgebra ℂ (CliffordAlgebra (cliffordForm m)) :=
  CliffordAlgebra.even (cliffordForm m)

/-- The full Clifford algebra of `cliffordForm m` has complex dimension `2 ^ m`. -/
@[simp]
theorem finrank_cliffordAlgebra_cliffordForm (m : ℕ) :
    Module.finrank ℂ (CliffordAlgebra (cliffordForm m)) = 2 ^ m := by
  rw [CliffordAlgebra.finrank_eq_two_pow, Module.finrank_fin_fun]

/-- The complex dimension of `EvenClifford m` is `2 ^ (m - 1)` for every `m : ℕ`
(including `m = 0` and `m = 1`, where `2 ^ (m - 1) = 1`). -/
@[simp]
theorem finrank_evenClifford (m : ℕ) :
    Module.finrank ℂ (EvenClifford m) = 2 ^ (m - 1) := by
  rw [EvenClifford, CliffordAlgebra.finrank_even, Module.finrank_fin_fun]

/-- The `j`-th **Majorana generator** `c_j = ι (Pi.single j 1)` of
`CliffordAlgebra (cliffordForm m)`. -/
noncomputable def majorana (m : ℕ) (j : Fin m) : CliffordAlgebra (cliffordForm m) :=
  CliffordAlgebra.ι (cliffordForm m) (Pi.single j 1)

/-- Unfolding `majorana` as the Clifford embedding of the `j`-th standard basis vector. -/
theorem majorana_def (m : ℕ) (j : Fin m) :
    majorana m j = CliffordAlgebra.ι (cliffordForm m) (Pi.single j 1) :=
  (rfl)

/-- Coordinate expansion of `CliffordAlgebra.ι (cliffordForm m) v` in the Majorana generators. -/
theorem ι_cliffordForm_eq_sum_majorana (m : ℕ) (v : Fin m → ℂ) :
    CliffordAlgebra.ι (cliffordForm m) v = ∑ j : Fin m, v j • majorana m j := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp [map_sum, majorana_def]

/-- Each Majorana generator squares to `1` under multiplication. -/
@[simp]
theorem majorana_mul_self (m : ℕ) (j : Fin m) :
    majorana m j * majorana m j = 1 := by
  rw [majorana_def, CliffordAlgebra.ι_sq_scalar, cliffordForm_single, mul_one, map_one]

/-- Power form of `majorana_mul_self`: `(c_j)² = 1`. -/
@[simp]
theorem majorana_sq (m : ℕ) (j : Fin m) :
    majorana m j ^ 2 = 1 := by
  rw [sq, majorana_mul_self]

/-- Distinct Majorana generators anticommute: `c_j * c_k + c_k * c_j = 0`. -/
theorem majorana_mul_majorana_add_swap_of_ne {m : ℕ} {j k : Fin m} (hjk : j ≠ k) :
    majorana m j * majorana m k + majorana m k * majorana m j = 0 := by
  rw [majorana_def, majorana_def, CliffordAlgebra.ι_mul_ι_add_swap,
    (isOrtho_cliffordForm_single hjk 1 1).polar_eq_zero, map_zero]

/-- Distinct Majorana generators anticommute: `c_j * c_k = -(c_k * c_j)`. -/
theorem majorana_mul_majorana_comm_of_ne {m : ℕ} {j k : Fin m} (hjk : j ≠ k) :
    majorana m j * majorana m k = -(majorana m k * majorana m j) :=
  eq_neg_of_add_eq_zero_left (majorana_mul_majorana_add_swap_of_ne hjk)

/-- For distinct indices `a ≠ b`, the Majorana product `c_a * c_b` squares to `-1`. -/
theorem majorana_mul_majorana_mul_self_of_ne {m : ℕ} {a b : Fin m} (hab : a ≠ b) :
    (majorana m a * majorana m b) * (majorana m a * majorana m b) = -1 := by
  simpa [majorana_def] using
    CliffordAlgebra.ι_mul_ι_mul_self_of_isOrtho (isOrtho_cliffordForm_single hab 1 1)

/-- For distinct indices `a ≠ b`, the scaled Majorana product `I • (c_a * c_b)` squares to `1`. -/
theorem I_smul_majorana_mul_majorana_mul_self_of_ne {m : ℕ} {a b : Fin m} (hab : a ≠ b) :
    (Complex.I • (majorana m a * majorana m b)) *
      (Complex.I • (majorana m a * majorana m b)) = 1 := by
  rw [smul_mul_smul_comm, majorana_mul_majorana_mul_self_of_ne hab, Complex.I_mul_I,
    neg_one_smul, neg_neg]

/-- A Majorana generator distinct from `c` and `d` commutes with `c_c * c_d`. -/
theorem commute_majorana_majorana_mul_majorana_of_ne {m : ℕ} {a c d : Fin m}
    (hac : a ≠ c) (had : a ≠ d) :
    Commute (majorana m a) (majorana m c * majorana m d) :=
  (CliffordAlgebra.commute_ι_mul_ι_ι_of_isOrtho
    (isOrtho_cliffordForm_single hac.symm 1 1)
    (isOrtho_cliffordForm_single had.symm 1 1)).symm

/-- Products of Majorana generators at disjoint index pairs commute. -/
theorem commute_majorana_mul_majorana_of_ne {m : ℕ} {a b c d : Fin m}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Commute (majorana m a * majorana m b) (majorana m c * majorana m d) :=
  (commute_majorana_majorana_mul_majorana_of_ne hac had).mul_left
    (commute_majorana_majorana_mul_majorana_of_ne hbc hbd)

/-- Every Majorana generator has odd Clifford parity. -/
theorem majorana_mem_evenOdd_one (m : ℕ) (j : Fin m) :
    majorana m j ∈ CliffordAlgebra.evenOdd (cliffordForm m) 1 :=
  CliffordAlgebra.ι_mem_evenOdd_one _ _

/-- Any product of two Majorana generators lies in `EvenClifford m`. -/
theorem majorana_mul_majorana_mem_even (m : ℕ) (j k : Fin m) :
    majorana m j * majorana m k ∈ EvenClifford m := by
  simpa [majorana_def, ← CliffordAlgebra.even_toSubmodule] using
    CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (cliffordForm m) (Pi.single j 1) (Pi.single k 1)

/-- The grade involution negates each Majorana generator. -/
@[simp]
theorem involute_majorana (m : ℕ) (j : Fin m) :
    CliffordAlgebra.involute (majorana m j) = -majorana m j := by
  simp [majorana_def]

/-- Reversion fixes each Majorana generator. -/
@[simp]
theorem reverse_majorana (m : ℕ) (j : Fin m) :
    CliffordAlgebra.reverse (majorana m j) = majorana m j := by
  simp [majorana_def]

/-- Complex-linear Clifford conjugation `star` negates each Majorana generator. -/
@[simp]
theorem star_majorana (m : ℕ) (j : Fin m) :
    star (majorana m j) = -majorana m j := by
  simp [majorana_def]

/-- Every Majorana generator has scalar part `0`. -/
@[simp]
theorem scalarTrace_majorana (m : ℕ) (j : Fin m) :
    CliffordAlgebra.scalarTrace (cliffordForm m) (majorana m j) = 0 := by
  simp [majorana_def]

/-- The scalar part of `c_j * c_k` is the Kronecker delta `if j = k then 1 else 0`. -/
@[simp]
theorem scalarTrace_majorana_mul_majorana (m : ℕ) (j k : Fin m) :
    CliffordAlgebra.scalarTrace (cliffordForm m) (majorana m j * majorana m k) =
      if j = k then 1 else 0 := by
  by_cases hjk : j = k
  · subst hjk
    simp
  · simp [majorana_def, hjk,
      QuadraticMap.associated_isOrtho.mpr (isOrtho_cliffordForm_single hjk 1 1)]

/-- In the standard coordinate basis, the ordered-product Clifford basis element indexed by `s` is
the ordered product of the corresponding Majorana generators. -/
theorem basis_cliffordForm_eq_prod_majorana (m : ℕ) (s : Finset (Fin m)) :
    CliffordAlgebra.basis (cliffordForm m) (Pi.basisFun ℂ (Fin m)) s =
      ((s.sort (· ≤ ·)).map (majorana m)).prod := by
  rw [CliffordAlgebra.basis_eq_prod_map_sort (isOrthoᵢ_associated_cliffordForm m)]
  simp only [List.map_map, Function.comp_def, Pi.basisFun_apply, ← majorana_def]

/-! ### The analytic adjoint and positivity of the Clifford scalar trace -/

/-- Canonical quadratic isometry identifying the complexification of the standard real form on
`ℝ^m` with `cliffordForm m` on `ℂ^m`. -/
private noncomputable def realCliffordBaseChangeIsometry (m : ℕ) :
    (QuadraticForm.baseChange ℂ (QuadraticMap.weightedSumSquares ℝ (1 : Fin m → ℝ))).IsometryEquiv
      (cliffordForm m) :=
  (QuadraticForm.baseChangeWeightedSumSquares (A := ℂ) (1 : Fin m → ℝ)).trans
    (QuadraticForm.weightedSumSquaresCongr (by ext; simp))

private noncomputable def realCliffordEquiv (m : ℕ) :
    CliffordAlgebra
        (QuadraticForm.baseChange ℂ (QuadraticMap.weightedSumSquares ℝ (1 : Fin m → ℝ))) ≃ₐ[ℂ]
      CliffordAlgebra (cliffordForm m) :=
  CliffordAlgebra.equivOfIsometry (realCliffordBaseChangeIsometry m)

private theorem realCliffordBaseChangeIsometry_one_tmul_single (m : ℕ) (j : Fin m) :
    realCliffordBaseChangeIsometry m (1 ⊗ₜ[ℝ] Pi.single j (1 : ℝ)) = Pi.single j (1 : ℂ) := by
  -- Project to `LinearEquiv` before rewriting, since `weightedSumSquaresCongr` has codomain
  -- `weightedSumSquares ℂ 1`, which matches `cliffordForm m` only at `default` transparency.
  have hlin : (realCliffordBaseChangeIsometry m : (ℂ ⊗[ℝ] (Fin m → ℝ)) ≃ₗ[ℂ] (Fin m → ℂ)) =
      (QuadraticForm.baseChangeWeightedSumSquares (A := ℂ) (1 : Fin m → ℝ) :
        (ℂ ⊗[ℝ] (Fin m → ℝ)) ≃ₗ[ℂ] (Fin m → ℂ)).trans (LinearEquiv.refl ℂ (Fin m → ℂ)) := rfl
  apply (TensorProduct.piScalarRight ℝ ℂ ℂ (Fin m)).symm.injective
  rw [← QuadraticMap.IsometryEquiv.coe_toLinearEquiv, hlin, LinearEquiv.trans_apply,
    LinearEquiv.refl_apply, QuadraticMap.IsometryEquiv.coe_toLinearEquiv,
    QuadraticForm.baseChangeWeightedSumSquares_apply, ← TensorProduct.piScalarRight_apply,
    LinearEquiv.symm_apply_apply, TensorProduct.piScalarRight_symm_single]

private theorem realCliffordEquiv_ι_single (m : ℕ) (j : Fin m) :
    realCliffordEquiv m
      (CliffordAlgebra.ι
        (QuadraticForm.baseChange ℂ (QuadraticMap.weightedSumSquares ℝ (1 : Fin m → ℝ)))
        (1 ⊗ₜ[ℝ] Pi.single j (1 : ℝ))) = majorana m j := by
  simp [realCliffordEquiv, majorana_def, realCliffordBaseChangeIsometry_one_tmul_single]

private theorem realCliffordEquiv_symm_majorana (m : ℕ) (j : Fin m) :
    (realCliffordEquiv m).symm (majorana m j) =
      CliffordAlgebra.ι
        (QuadraticForm.baseChange ℂ (QuadraticMap.weightedSumSquares ℝ (1 : Fin m → ℝ)))
        (1 ⊗ₜ[ℝ] Pi.single j (1 : ℝ)) :=
  (realCliffordEquiv m).injective <| by simp [realCliffordEquiv_ι_single]

/-- The **analytic adjoint** `a ↦ a†` on `CliffordAlgebra (cliffordForm m)`: the conjugate-linear,
product-reversing involution fixing each Majorana generator `majorana m j`. Under the canonical
isometry with the complexification of `ℝ^m`, it is the positive-form adjoint
`x ↦ complexConj (reverse x)`. -/
noncomputable def cliffordAdjoint (m : ℕ) :
    CliffordAlgebra (cliffordForm m) →ₗ⋆[ℂ] CliffordAlgebra (cliffordForm m) where
  toFun a := realCliffordEquiv m
    (CliffordAlgebra.complexConj (QuadraticMap.weightedSumSquares ℝ (1 : Fin m → ℝ))
      (CliffordAlgebra.reverse ((realCliffordEquiv m).symm a)))
  map_add' a b := by simp
  map_smul' z a := by simp

/-- `cliffordAdjoint` fixes `1`. -/
@[simp]
theorem cliffordAdjoint_one (m : ℕ) : cliffordAdjoint m 1 = 1 := by
  simp [cliffordAdjoint]

/-- `cliffordAdjoint` acts on scalars by complex conjugation. -/
@[simp]
theorem cliffordAdjoint_algebraMap (m : ℕ) (z : ℂ) :
    cliffordAdjoint m (algebraMap ℂ (CliffordAlgebra (cliffordForm m)) z) =
      algebraMap ℂ (CliffordAlgebra (cliffordForm m)) (conj z) := by
  simp [cliffordAdjoint]

/-- `cliffordAdjoint` reverses products. -/
@[simp]
theorem cliffordAdjoint_mul (m : ℕ) (a b : CliffordAlgebra (cliffordForm m)) :
    cliffordAdjoint m (a * b) = cliffordAdjoint m b * cliffordAdjoint m a := by
  simp [cliffordAdjoint]

/-- `cliffordAdjoint` is involutive. -/
@[simp]
theorem cliffordAdjoint_cliffordAdjoint (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordAdjoint m (cliffordAdjoint m a) = a := by
  simp [cliffordAdjoint, ← CliffordAlgebra.complexConj_reverse]

/-- `cliffordAdjoint` fixes every Majorana generator. -/
@[simp]
theorem cliffordAdjoint_majorana (m : ℕ) (j : Fin m) :
    cliffordAdjoint m (majorana m j) = majorana m j := by
  simp [cliffordAdjoint, realCliffordEquiv_symm_majorana, realCliffordEquiv_ι_single]

/-- `cliffordAdjoint` acts on vectors by coordinatewise complex conjugation. -/
@[simp]
theorem cliffordAdjoint_ι (m : ℕ) (v : Fin m → ℂ) :
    cliffordAdjoint m (CliffordAlgebra.ι (cliffordForm m) v) =
      CliffordAlgebra.ι (cliffordForm m) (star v) := by
  rw [ι_cliffordForm_eq_sum_majorana m v, ι_cliffordForm_eq_sum_majorana m (star v), map_sum]
  simp [Pi.star_apply]

/-- The analytic adjoint is the unique conjugate-linear, product-reversing unital map on
`CliffordAlgebra (cliffordForm m)` fixing every Majorana generator. -/
theorem cliffordAdjoint_unique {m : ℕ}
    {f : CliffordAlgebra (cliffordForm m) →ₗ⋆[ℂ] CliffordAlgebra (cliffordForm m)}
    (hone : f 1 = 1) (hmul : ∀ a b, f (a * b) = f b * f a)
    (hmaj : ∀ j, f (majorana m j) = majorana m j) :
    f = cliffordAdjoint m := by
  ext a
  induction a using CliffordAlgebra.induction with
  | algebraMap z =>
    rw [Algebra.algebraMap_eq_smul_one, map_smulₛₗ, map_smulₛₗ, hone, cliffordAdjoint_one]
  | ι v =>
    rw [ι_cliffordForm_eq_sum_majorana, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smulₛₗ, map_smulₛₗ, hmaj, cliffordAdjoint_majorana]
  | mul a b ha hb => rw [hmul, cliffordAdjoint_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- `cliffordAdjoint` commutes with the Clifford grade involution. -/
@[simp]
theorem cliffordAdjoint_involute (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordAdjoint m (CliffordAlgebra.involute a) =
      CliffordAlgebra.involute (cliffordAdjoint m a) := by
  simp [cliffordAdjoint, realCliffordEquiv, CliffordAlgebra.reverse_involute]

/-- The even Clifford subalgebra `EvenClifford m` is stable under `cliffordAdjoint m`. -/
theorem cliffordAdjoint_mem_even (m : ℕ) {a : CliffordAlgebra (cliffordForm m)}
    (ha : a ∈ EvenClifford m) :
    cliffordAdjoint m a ∈ EvenClifford m := by
  have ha0 : CliffordAlgebra.involute a = a :=
    CliffordAlgebra.involute_eq_self_iff.mpr
      (by simpa [← CliffordAlgebra.even_toSubmodule] using ha)
  have hadj : CliffordAlgebra.involute (cliffordAdjoint m a) = cliffordAdjoint m a := by
    rw [← cliffordAdjoint_involute, ha0]
  simpa [← CliffordAlgebra.even_toSubmodule] using CliffordAlgebra.involute_eq_self_iff.mp hadj

/-- `cliffordAdjoint m a` lies in `EvenClifford m` if and only if `a` does. -/
@[simp]
theorem cliffordAdjoint_mem_even_iff (m : ℕ) {a : CliffordAlgebra (cliffordForm m)} :
    cliffordAdjoint m a ∈ EvenClifford m ↔ a ∈ EvenClifford m :=
  ⟨fun h ↦ cliffordAdjoint_cliffordAdjoint m a ▸ cliffordAdjoint_mem_even m h,
    cliffordAdjoint_mem_even m⟩

/-- Restriction of `cliffordAdjoint m` to the even Clifford subalgebra `EvenClifford m`. -/
noncomputable def evenCliffordAdjoint (m : ℕ) :
    EvenClifford m →ₗ⋆[ℂ] EvenClifford m where
  toFun x := ⟨cliffordAdjoint m x, cliffordAdjoint_mem_even m x.2⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' z x := Subtype.ext (by simp)

/-- Coercing `evenCliffordAdjoint m x` to the ambient Clifford algebra gives `cliffordAdjoint m x`.
-/
@[simp]
theorem coe_evenCliffordAdjoint (m : ℕ) (x : EvenClifford m) :
    (evenCliffordAdjoint m x : CliffordAlgebra (cliffordForm m)) = cliffordAdjoint m x :=
  (rfl)

/-- `evenCliffordAdjoint` fixes `1`. -/
@[simp]
theorem evenCliffordAdjoint_one (m : ℕ) : evenCliffordAdjoint m 1 = 1 :=
  Subtype.ext (cliffordAdjoint_one m)

/-- `evenCliffordAdjoint` acts on scalars by complex conjugation. -/
@[simp]
theorem evenCliffordAdjoint_algebraMap (m : ℕ) (z : ℂ) :
    evenCliffordAdjoint m (algebraMap ℂ (EvenClifford m) z) =
      algebraMap ℂ (EvenClifford m) (conj z) :=
  Subtype.ext (cliffordAdjoint_algebraMap m z)

/-- `evenCliffordAdjoint` reverses products. -/
@[simp]
theorem evenCliffordAdjoint_mul (m : ℕ) (x y : EvenClifford m) :
    evenCliffordAdjoint m (x * y) = evenCliffordAdjoint m y * evenCliffordAdjoint m x :=
  Subtype.ext (cliffordAdjoint_mul m x y)

/-- `evenCliffordAdjoint` is involutive. -/
@[simp]
theorem evenCliffordAdjoint_evenCliffordAdjoint (m : ℕ) (x : EvenClifford m) :
    evenCliffordAdjoint m (evenCliffordAdjoint m x) = x :=
  Subtype.ext (cliffordAdjoint_cliffordAdjoint m x)

/-- `CliffordAlgebra.scalarTrace` intertwines `cliffordAdjoint` with complex conjugation. -/
@[simp]
theorem scalarTrace_cliffordAdjoint (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    CliffordAlgebra.scalarTrace (cliffordForm m) (cliffordAdjoint m a) =
      conj (CliffordAlgebra.scalarTrace (cliffordForm m) a) := by
  simp [cliffordAdjoint, realCliffordEquiv]

private theorem realCliffordEquiv_basis (m : ℕ) (s : Finset (Fin m)) :
    realCliffordEquiv m
        (CliffordAlgebra.basis
          (QuadraticForm.baseChange ℂ (QuadraticMap.weightedSumSquares ℝ (1 : Fin m → ℝ)))
          ((Pi.basisFun ℝ (Fin m)).baseChange ℂ) s) =
      CliffordAlgebra.basis (cliffordForm m) (Pi.basisFun ℂ (Fin m)) s := by
  have hb : ((Pi.basisFun ℝ (Fin m)).baseChange ℂ).map
      (realCliffordBaseChangeIsometry m).toLinearEquiv = Pi.basisFun ℂ (Fin m) :=
    Module.Basis.eq_of_apply_eq fun j ↦ by
      simp [Pi.basisFun_apply, realCliffordBaseChangeIsometry_one_tmul_single]
  rw [realCliffordEquiv, CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_basis, hb]

private theorem basis_repr_realCliffordEquiv_symm (m : ℕ)
    (a : CliffordAlgebra (cliffordForm m)) :
    (CliffordAlgebra.basis
        (QuadraticForm.baseChange ℂ (QuadraticMap.weightedSumSquares ℝ (1 : Fin m → ℝ)))
        ((Pi.basisFun ℝ (Fin m)).baseChange ℂ)).repr ((realCliffordEquiv m).symm a) =
      (CliffordAlgebra.basis (cliffordForm m) (Pi.basisFun ℂ (Fin m))).repr a :=
  Module.Basis.repr_map_eq_of_map_basis _ _ (realCliffordEquiv m).symm.toLinearMap
    (fun s ↦ (realCliffordEquiv m).injective
      (by rw [AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply, realCliffordEquiv_basis])) a

private theorem cliffordAdjoint_apply (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordAdjoint m a =
      realCliffordEquiv m
        (CliffordAlgebra.complexConj (QuadraticMap.weightedSumSquares ℝ (1 : Fin m → ℝ))
          (CliffordAlgebra.reverse ((realCliffordEquiv m).symm a))) :=
  rfl

/-- Transports `cliffordAdjoint m a * b` to the complexification of the standard real form. -/
private theorem cliffordAdjoint_mul_eq_map (m : ℕ)
    (a b : CliffordAlgebra (cliffordForm m)) :
    cliffordAdjoint m a * b =
      CliffordAlgebra.map (realCliffordBaseChangeIsometry m).toIsometry
        (CliffordAlgebra.complexConj (QuadraticMap.weightedSumSquares ℝ (1 : Fin m → ℝ))
          (CliffordAlgebra.reverse ((realCliffordEquiv m).symm a)) *
            (realCliffordEquiv m).symm b) := by
  rw [← CliffordAlgebra.equivOfIsometry_apply, ← realCliffordEquiv, map_mul,
    AlgEquiv.apply_symm_apply, ← cliffordAdjoint_apply]

/-- **Sesquilinear Parseval identity for the Clifford scalar trace**: in the ordered-product
Majorana basis, `scalarTrace (cliffordForm m) (cliffordAdjoint m a * b)` is
`∑_s conj (a_s) * b_s`. -/
theorem scalarTrace_cliffordAdjoint_mul (m : ℕ)
    (a b : CliffordAlgebra (cliffordForm m)) :
    CliffordAlgebra.scalarTrace (cliffordForm m) (cliffordAdjoint m a * b) =
      ((CliffordAlgebra.basis (cliffordForm m) (Pi.basisFun ℂ (Fin m))).repr a).sum
        fun s z ↦
          conj z *
            (CliffordAlgebra.basis (cliffordForm m) (Pi.basisFun ℂ (Fin m))).repr b s := by
  rw [cliffordAdjoint_mul_eq_map, CliffordAlgebra.scalarTrace_map,
    CliffordAlgebra.scalarTrace_complexConj_reverse_mul
      (QuadraticMap.isOrthoᵢ_associated_weightedSumSquares (1 : Fin m → ℝ)),
    basis_repr_realCliffordEquiv_symm, basis_repr_realCliffordEquiv_symm]
  simp only [Pi.basisFun_apply, QuadraticMap.weightedSumSquares_apply_single]
  simp

/-- **Parseval identity for the Clifford scalar trace**: in the ordered-product Majorana basis,
`scalarTrace (cliffordForm m) (cliffordAdjoint m a * a)` is the sum of squared moduli of the
coordinates of `a`. -/
theorem scalarTrace_cliffordAdjoint_mul_self (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    CliffordAlgebra.scalarTrace (cliffordForm m) (cliffordAdjoint m a * a) =
      (((CliffordAlgebra.basis (cliffordForm m) (Pi.basisFun ℂ (Fin m))).repr a).sum
        fun _ z ↦ Complex.normSq z : ℝ) := by
  rw [scalarTrace_cliffordAdjoint_mul]
  simpa using (Finsupp.ofReal_sum_normSq_mul
    ((CliffordAlgebra.basis (cliffordForm m) (Pi.basisFun ℂ (Fin m))).repr a) 1).symm

/-- **Positivity of the Clifford scalar trace** for `cliffordAdjoint m`. -/
theorem scalarTrace_cliffordAdjoint_mul_self_nonneg (m : ℕ)
    (a : CliffordAlgebra (cliffordForm m)) :
    0 ≤ CliffordAlgebra.scalarTrace (cliffordForm m) (cliffordAdjoint m a * a) := by
  rw [scalarTrace_cliffordAdjoint_mul_self, Complex.zero_le_real]
  exact Finsupp.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _

/-- **Faithfulness of the Clifford scalar trace** for `cliffordAdjoint m`:
`scalarTrace (cliffordForm m) (cliffordAdjoint m a * a) = 0` if and only if `a = 0`. -/
@[simp]
theorem scalarTrace_cliffordAdjoint_mul_self_eq_zero_iff (m : ℕ)
    {a : CliffordAlgebra (cliffordForm m)} :
    CliffordAlgebra.scalarTrace (cliffordForm m) (cliffordAdjoint m a * a) = 0 ↔ a = 0 := by
  have hpos : (QuadraticMap.weightedSumSquares ℝ (1 : Fin m → ℝ)).PosDef :=
    (QuadraticMap.posDef_weightedSumSquares_iff (1 : Fin m → ℝ)).mpr fun _ ↦ zero_lt_one
  rw [cliffordAdjoint_mul_eq_map, CliffordAlgebra.scalarTrace_map,
    CliffordAlgebra.scalarTrace_complexConj_reverse_mul_self_eq_zero_iff hpos,
    map_eq_zero_iff _ (realCliffordEquiv m).symm.injective]

/-! ### Clifford projections and the comparison homomorphism `evenCliffordHom` -/

/-- The `j`-th **Clifford projection** `p_j = 2⁻¹ • (1 + I • (c_j * c_{j + 1}))` in
`CliffordAlgebra (cliffordForm m)` for `j : Fin (m - 1)`. -/
noncomputable def cliffordProjection (m : ℕ) (j : Fin (m - 1)) :
    CliffordAlgebra (cliffordForm m) :=
  (2 : ℂ)⁻¹ •
    (1 + Complex.I • (majorana m ⟨j.1, by omega⟩ * majorana m ⟨j.1 + 1, by omega⟩))

/-- Explicit Majorana formula for `cliffordProjection`. -/
theorem cliffordProjection_def (m : ℕ) (j : Fin (m - 1)) :
    cliffordProjection m j =
      (2 : ℂ)⁻¹ •
        (1 + Complex.I • (majorana m ⟨j.1, by omega⟩ * majorana m ⟨j.1 + 1, by omega⟩)) :=
  (rfl)

/-- Each Clifford projection lies in `EvenClifford m`. -/
theorem cliffordProjection_mem_even (m : ℕ) (j : Fin (m - 1)) :
    cliffordProjection m j ∈ EvenClifford m := by
  rw [cliffordProjection_def]
  exact Subalgebra.smul_mem _
    (add_mem (one_mem _) (Subalgebra.smul_mem _ (majorana_mul_majorana_mem_even m _ _) _)) _

/-- Every Clifford projection has scalar part `2⁻¹`. -/
@[simp]
theorem scalarTrace_cliffordProjection (m : ℕ) (j : Fin (m - 1)) :
    CliffordAlgebra.scalarTrace (cliffordForm m) (cliffordProjection m j) = (2 : ℂ)⁻¹ := by
  have hne : (⟨j.1, by omega⟩ : Fin m) ≠ ⟨j.1 + 1, by omega⟩ :=
    ne_of_apply_ne Fin.val (by dsimp; omega)
  simp [cliffordProjection_def, hne]

/-- Two Majorana-pair involutions sharing exactly one index anticommute. -/
private theorem smul_I_majorana_anticommute {m : ℕ} {a b c d : Fin m}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b = c) (hbd : b ≠ d) :
    (Complex.I • (majorana m a * majorana m b)) *
        (Complex.I • (majorana m c * majorana m d)) +
      (Complex.I • (majorana m c * majorana m d)) *
        (Complex.I • (majorana m a * majorana m b)) = 0 := by
  subst hbc
  have hanti :
      (majorana m a * majorana m b) * (majorana m b * majorana m d) =
        -((majorana m b * majorana m d) * (majorana m a * majorana m b)) := by
    have h := congrArg Subtype.val
      (CliffordAlgebra.even_ι_bilin_comm_of_isOrtho
        (isOrtho_cliffordForm_single hac.symm 1 1)
        (isOrtho_cliffordForm_single hbd 1 1)
        (isOrtho_cliffordForm_single had 1 1))
    simpa [← majorana_def, majorana_mul_majorana_comm_of_ne hac.symm] using h.symm
  rw [smul_mul_smul_comm, smul_mul_smul_comm, hanti, ← smul_add, neg_add_cancel, smul_zero]

/-- Every Clifford projection is self-adjoint for `cliffordAdjoint m`. -/
@[simp]
theorem cliffordAdjoint_cliffordProjection (m : ℕ) (j : Fin (m - 1)) :
    cliffordAdjoint m (cliffordProjection m j) = cliffordProjection m j := by
  have hne : (⟨j.1, by omega⟩ : Fin m) ≠ ⟨j.1 + 1, by omega⟩ :=
    ne_of_apply_ne Fin.val (by dsimp; omega)
  simp [cliffordProjection_def, majorana_mul_majorana_comm_of_ne hne.symm, smul_neg, smul_add,
    map_ofNat]

/-- Every Clifford projection is idempotent. -/
@[simp]
theorem cliffordProjection_mul_self (m : ℕ) (j : Fin (m - 1)) :
    cliffordProjection m j * cliffordProjection m j = cliffordProjection m j := by
  have hne : (⟨j.1, by omega⟩ : Fin m) ≠ ⟨j.1 + 1, by omega⟩ :=
    ne_of_apply_ne Fin.val (by dsimp; omega)
  rw [cliffordProjection_def]
  set u := Complex.I • (majorana m ⟨j.1, by omega⟩ * majorana m ⟨j.1 + 1, by omega⟩)
  have hu : u * u = 1 := I_smul_majorana_mul_majorana_mul_self_of_ne hne
  rw [smul_mul_smul_comm, TauCeti.one_add_mul_self_of_mul_self_eq_one hu, ← two_smul ℂ, smul_smul]
  norm_num

/-- Adjacent Clifford projections satisfy `p_i * p_j * p_i = 2⁻¹ • p_i`. -/
theorem cliffordProjection_mul_cliffordProjection_mul_cliffordProjection {m : ℕ}
    {i j : Fin (m - 1)} (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    cliffordProjection m i * cliffordProjection m j * cliffordProjection m i =
      (2 : ℂ)⁻¹ • cliffordProjection m i := by
  have hi_ne : (⟨i.1, by omega⟩ : Fin m) ≠ ⟨i.1 + 1, by omega⟩ :=
    ne_of_apply_ne Fin.val (by dsimp; omega)
  rw [cliffordProjection_def m i, cliffordProjection_def m j]
  set u := Complex.I • (majorana m ⟨i.1, by omega⟩ * majorana m ⟨i.1 + 1, by omega⟩)
  set v := Complex.I • (majorana m ⟨j.1, by omega⟩ * majorana m ⟨j.1 + 1, by omega⟩)
  have hu : u * u = 1 := I_smul_majorana_mul_majorana_mul_self_of_ne hi_ne
  have huv : u * v + v * u = 0 := by
    rcases h with hij | hji
    · exact smul_I_majorana_anticommute
        (ne_of_apply_ne Fin.val (by dsimp; omega))
        (ne_of_apply_ne Fin.val (by dsimp; omega))
        (Fin.ext (by dsimp; omega))
        (ne_of_apply_ne Fin.val (by dsimp; omega))
    · rw [add_comm]
      exact smul_I_majorana_anticommute
        (ne_of_apply_ne Fin.val (by dsimp; omega))
        (ne_of_apply_ne Fin.val (by dsimp; omega))
        (Fin.ext (by dsimp; omega))
        (ne_of_apply_ne Fin.val (by dsimp; omega))
  have hprod : (1 + u) * (1 + v) * (1 + u) = (2 : ℂ) • (1 + u) := by
    rw [TauCeti.one_add_mul_one_add_mul_one_add_of_mul_self_eq_one hu huv, ← two_smul ℂ]
  simp only [smul_mul_assoc, mul_smul_comm, hprod, smul_smul]
  norm_num

/-- Distant Clifford projections commute. -/
theorem commute_cliffordProjection {m : ℕ} {i j : Fin (m - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (cliffordProjection m i) (cliffordProjection m j) := by
  have hpair : Commute
      (majorana m ⟨i.1, by omega⟩ * majorana m ⟨i.1 + 1, by omega⟩)
      (majorana m ⟨j.1, by omega⟩ * majorana m ⟨j.1 + 1, by omega⟩) := by
    refine commute_majorana_mul_majorana_of_ne ?_ ?_ ?_ ?_ <;>
      exact ne_of_apply_ne Fin.val (by dsimp; omega)
  rw [cliffordProjection_def, cliffordProjection_def]
  exact (((Commute.one_left _).add_left
    ((Commute.one_right _).add_right
      (hpair.smul_left _ |>.smul_right _))).smul_left _).smul_right _

/-- The `j`-th Temperley–Lieb generator `(√2 : ℂ) • cliffordProjection m j`, bundled as an element
of `EvenClifford m`. -/
private noncomputable def evenCliffordGenerator (m : ℕ) (j : Fin (m - 1)) : EvenClifford m :=
  ⟨(Real.sqrt 2 : ℂ) • cliffordProjection m j,
    Subalgebra.smul_mem _ (cliffordProjection_mem_even m j) _⟩

/-- The **even Clifford comparison homomorphism**
`TemperleyLieb ℂ (√2 : ℂ) m →ₐ[ℂ] EvenClifford m`, sending `e (√2 : ℂ) j` to
`(√2 : ℂ) • cliffordProjection m j`. -/
noncomputable def evenCliffordHom (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m →ₐ[ℂ] EvenClifford m :=
  lift (evenCliffordGenerator m)
    (fun i ↦ Subtype.ext <| by
      simp only [Subalgebra.coe_mul, SetLike.val_smul, evenCliffordGenerator, smul_mul_smul_comm,
        cliffordProjection_mul_self, smul_smul])
    (fun {i j} h ↦ Subtype.ext <| by
      simp only [Subalgebra.coe_mul, evenCliffordGenerator, smul_mul_assoc, mul_smul_comm,
        cliffordProjection_mul_cliffordProjection_mul_cliffordProjection h, smul_smul]
      rw [sqrt_two_coe_mul_self]
      norm_num)
    (fun {i j} h ↦ Subtype.ext <| by
      simp only [Subalgebra.coe_mul, evenCliffordGenerator]
      exact ((commute_cliffordProjection h).smul_left _ |>.smul_right _).eq)

/-- Action of `evenCliffordHom` on the `j`-th Temperley–Lieb generator, coerced to the ambient
Clifford algebra. -/
@[simp]
theorem coe_evenCliffordHom_e (m : ℕ) (j : Fin (m - 1)) :
    (evenCliffordHom m (e (Real.sqrt 2 : ℂ) j) : CliffordAlgebra (cliffordForm m)) =
      (Real.sqrt 2 : ℂ) • cliffordProjection m j := by
  simp [evenCliffordHom, evenCliffordGenerator]

/-- `evenCliffordHom` intertwines the Temperley–Lieb analytic adjoint with `cliffordAdjoint`. -/
theorem coe_evenCliffordHom_star {m : ℕ} (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m) :
    (evenCliffordHom m (star x) : CliffordAlgebra (cliffordForm m)) =
      cliffordAdjoint m (evenCliffordHom m x) := by
  induction x using TemperleyLieb.induction with
  | e j =>
    rw [star_e, coe_evenCliffordHom_e, map_smulₛₗ, cliffordAdjoint_cliffordProjection]
    simp [Complex.conj_ofReal]
  | algebraMap z =>
    simp [Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
    simp only [star_add, map_add, Subalgebra.coe_add, hx, hy]
  | mul x y hx hy =>
    simp only [star_mul, map_mul, Subalgebra.coe_mul, cliffordAdjoint_mul, hx, hy]

/-- `evenCliffordHom` intertwines the Temperley–Lieb analytic adjoint with `evenCliffordAdjoint`. -/
@[simp]
theorem evenCliffordHom_star {m : ℕ} (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m) :
    evenCliffordHom m (star x) = evenCliffordAdjoint m (evenCliffordHom m x) :=
  Subtype.ext (coe_evenCliffordHom_star x)

/-- Ambient `ℂ`-algebra homomorphism into `CliffordAlgebra (cliffordForm m)` used to show
surjectivity of `evenCliffordHom m` without subtype bookkeeping. -/
private noncomputable def ambientEvenCliffordHom (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m →ₐ[ℂ] CliffordAlgebra (cliffordForm m) :=
  (EvenClifford m).val.comp (evenCliffordHom m)

/-- Adjacent Majorana products lie in the range of `ambientEvenCliffordHom m`:
`c_j * c_{j + 1} = (-I) • ((√2 : ℂ) • F_m (e j) - 1)`. -/
private theorem majorana_mul_succ_mem_range_ambient {m : ℕ} (j : ℕ) (hj : j + 1 < m) :
    majorana m ⟨j, by omega⟩ * majorana m ⟨j + 1, hj⟩ ∈
      (ambientEvenCliffordHom m).range := by
  let i : Fin (m - 1) := ⟨j, by omega⟩
  rw [AlgHom.mem_range]
  refine ⟨(-Complex.I) • ((Real.sqrt 2 : ℂ) • e (Real.sqrt 2 : ℂ) i - 1), ?_⟩
  have he : ambientEvenCliffordHom m (e (Real.sqrt 2 : ℂ) i) =
      (Real.sqrt 2 : ℂ) • cliffordProjection m i :=
    coe_evenCliffordHom_e m i
  have hscale : ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) * (2 : ℂ)⁻¹ = 1 := by
    rw [sqrt_two_coe_mul_self]
    norm_num
  rw [map_smul, map_sub, map_smul, he, cliffordProjection_def, smul_smul, smul_smul, hscale]
  simp [smul_smul, i]

/-- Every ordered Majorana product `c_j * c_k` with `j < k` lies in
`(ambientEvenCliffordHom m).range`, by telescoping multiplication along `j < j + 1 < ⋯ < k`. -/
private theorem majorana_mul_mem_range_ambient_of_lt {m : ℕ} :
    ∀ {d j : ℕ} (hjk : j + d + 1 < m),
      majorana m ⟨j, by omega⟩ * majorana m ⟨j + d + 1, hjk⟩ ∈
        (ambientEvenCliffordHom m).range
  | 0, j, hjk => majorana_mul_succ_mem_range_ambient j hjk
  | d + 1, j, hjk => by
    have hleft := majorana_mul_mem_range_ambient_of_lt (m := m) (d := d) (j := j) (by omega)
    have hright := majorana_mul_succ_mem_range_ambient (m := m) (j + d + 1) (by omega)
    have htel : majorana m ⟨j, by omega⟩ * majorana m ⟨j + (d + 1) + 1, hjk⟩ =
        (majorana m ⟨j, by omega⟩ * majorana m ⟨j + d + 1, by omega⟩) *
          (majorana m ⟨j + d + 1, by omega⟩ * majorana m ⟨j + d + 1 + 1, by omega⟩) := by
      have hidx : (⟨j + (d + 1) + 1, hjk⟩ : Fin m) = ⟨j + d + 1 + 1, by omega⟩ :=
        Fin.ext (by dsimp; omega)
      rw [hidx]
      calc
        majorana m ⟨j, by omega⟩ * majorana m ⟨j + d + 1 + 1, by omega⟩
            = majorana m ⟨j, by omega⟩ *
                (majorana m ⟨j + d + 1, by omega⟩ * majorana m ⟨j + d + 1, by omega⟩) *
                  majorana m ⟨j + d + 1 + 1, by omega⟩ := by
              rw [majorana_mul_self, mul_one]
        _ = (majorana m ⟨j, by omega⟩ * majorana m ⟨j + d + 1, by omega⟩) *
              (majorana m ⟨j + d + 1, by omega⟩ * majorana m ⟨j + d + 1 + 1, by omega⟩) := by
              simp only [mul_assoc]
    rw [htel]
    exact mul_mem hleft hright

private theorem majorana_mul_majorana_mem_range_ambient_of_lt {m : ℕ} {j k : Fin m}
    (hjk : j < k) :
    majorana m j * majorana m k ∈ (ambientEvenCliffordHom m).range := by
  have hj_eq : (⟨j.1, by omega⟩ : Fin m) = j := Fin.ext rfl
  have hk_eq : (⟨j.1 + (k.1 - j.1 - 1) + 1, by omega⟩ : Fin m) = k :=
    Fin.ext (by dsimp; omega)
  simpa only [hj_eq, hk_eq] using
    majorana_mul_mem_range_ambient_of_lt (m := m) (d := k.1 - j.1 - 1) (j := j.1) (by omega)

/-- Every Majorana pair `c_j * c_k` lies in `(ambientEvenCliffordHom m).range`. -/
private theorem majorana_mul_majorana_mem_range_ambient (m : ℕ) (j k : Fin m) :
    majorana m j * majorana m k ∈ (ambientEvenCliffordHom m).range := by
  rcases lt_trichotomy j k with hlt | rfl | hgt
  · exact majorana_mul_majorana_mem_range_ambient_of_lt hlt
  · rw [majorana_mul_self]
    exact one_mem _
  · rw [majorana_mul_majorana_comm_of_ne hgt.ne']
    exact neg_mem (majorana_mul_majorana_mem_range_ambient_of_lt hgt)

/-- Every product of two vectors `ι v * ι w` lies in `(ambientEvenCliffordHom m).range`. -/
private theorem ι_mul_ι_mem_range_ambient (m : ℕ) (v w : Fin m → ℂ) :
    CliffordAlgebra.ι (cliffordForm m) v * CliffordAlgebra.ι (cliffordForm m) w ∈
      (ambientEvenCliffordHom m).range := by
  rw [ι_cliffordForm_eq_sum_majorana m v, ι_cliffordForm_eq_sum_majorana m w, Finset.sum_mul]
  refine sum_mem fun j _ ↦ ?_
  rw [Finset.mul_sum]
  refine sum_mem fun k _ ↦ ?_
  rw [smul_mul_smul_comm]
  exact Subalgebra.smul_mem _ (majorana_mul_majorana_mem_range_ambient m j k) _

/-- **Surjectivity of the even Clifford comparison map**: for every `m : ℕ`,
`evenCliffordHom m : TemperleyLieb ℂ (√2 : ℂ) m →ₐ[ℂ] EvenClifford m` is surjective. -/
theorem evenCliffordHom_surjective (m : ℕ) : Function.Surjective (evenCliffordHom m) := by
  rintro ⟨x, hx⟩
  have hmem : x ∈ (ambientEvenCliffordHom m).range := by
    have hx0 : x ∈ CliffordAlgebra.evenOdd (cliffordForm m) 0 := by
      simpa [← CliffordAlgebra.even_toSubmodule] using hx
    clear hx
    induction x, hx0 using CliffordAlgebra.even_induction with
    | algebraMap z => exact Subalgebra.algebraMap_mem _ z
    | add _ _ _ _ ihx ihy => exact add_mem ihx ihy
    | ι_mul_ι_mul v w _ _ ih => exact mul_mem (ι_mul_ι_mem_range_ambient m v w) ih
  obtain ⟨t, ht⟩ := hmem
  exact ⟨t, Subtype.ext ht⟩

end TauCeti.TemperleyLieb
