/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.MarkovTrace
public import TauCeti.Algebra.TemperleyLieb.Star
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
public import TauCeti.LinearAlgebra.CliffordAlgebra.ScalarTrace.Positivity
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
-- Private: real-form base change and grading involutions are used only inside proofs and internal
-- transport constructions.
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
import TauCeti.LinearAlgebra.QuadraticForm.BaseChange

/-!
# The Jones quotient at `δ = √2` as an even Clifford algebra

At the loop parameter `δ = √2 = 2 cos (π / 4)` — corresponding to Jones index `δ² = 2` — the
Temperley–Lieb algebra `TemperleyLieb ℂ (√2 : ℂ) m` surjects onto the even complex Clifford
algebra `Cl_m⁰` of the standard sum-of-squares form on `ℂ^m`, with kernel equal to the radical of
the Markov trace. Passing to the trace-radical quotient identifies the `m`-strand Jones quotient at
`δ = √2` with `Cl_m⁰` of dimension `2 ^ (m - 1)` (with `2 ^ (0 - 1) = 1` at `m = 0`), intertwines
the Temperley–Lieb analytic adjoint with the positive-form Clifford adjoint, and identifies the
unnormalized Markov trace with `(√2) ^ m` times the Clifford scalar trace
`CliffordAlgebra.scalarTrace`.

Concretely, let `cliffordForm m` be `∑ i, (v i)²` on `Fin m → ℂ`, let `majorana m j` (`c_j`) be the
`j`-th standard basis generator in `CliffordAlgebra (cliffordForm m)`, satisfying `c_j² = 1` and
`c_j c_k = -c_k c_j` for `j ≠ k`, and set

  `cliffordProjection m j = 2⁻¹ • (1 + I • (c_j * c_{j + 1}))`.

Each `p_j = cliffordProjection m j` lies in the even subalgebra `EvenClifford m`, is self-adjoint
for the conjugate-linear reversal `cliffordAdjoint m` fixing the Majorana generators, is idempotent
(`p_j² = p_j`), satisfies `p_j p_k p_j = 2⁻¹ • p_j` for `|j - k| = 1`, and commutes with `p_k` for
`|j - k| ≥ 2`. Rescaling by `√2` therefore defines a `ℂ`-algebra homomorphism

  `evenCliffordHom m : TemperleyLieb ℂ (√2 : ℂ) m →ₐ[ℂ] EvenClifford m`

sending `e (√2 : ℂ) j` to `(√2 : ℂ) • p_j`.

* **Surjectivity**: adjacent Majorana products are recovered by
  `c_j * c_{j + 1} = (-I) • ((√2 : ℂ) • F_m (e j) - 1)`, general pairs `c_j * c_k` with `j < k`
  follow by telescoping multiplication, and `CliffordAlgebra.even_induction` shows these generate
  `EvenClifford m`.
* **Markov trace identity**: extending `ℂ^m → ℂ^(m + 1)` by zero induces `cliffordIncl m`, which
  intertwines `strandIncl`, preserves `CliffordAlgebra.scalarTrace`, and sends
  `cliffordIncl (n + 1) x * p_{n}` to `2⁻¹ • cliffordIncl (n + 1) x` plus a term ending in the
  orthogonal generator `c_{n + 1}`, whose scalar part vanishes by
  `CliffordAlgebra.scalarTrace_map_mul_ι_eq_zero`. Hence `(√2) ^ m • s_m (F_m ·)` satisfies
  `IsMarkovTrace`, and Markov uniqueness identifies every Markov trace at `√2` with it.
* **Positivity and the trace radical**: transporting `CliffordAlgebra.complexConj ∘ reverse` from
  the standard positive-definite real form on `ℝ^m` along
  `QuadraticForm.baseChangeWeightedSumSquares` shows `s_m (a† * a) = ∑_S |a_S|² ≥ 0`, vanishing
  only at `a = 0`. Thus at `δ = √2` the Markov Hermitian form `tr m (star x * x)` is positive
  semidefinite (the `m = 4` discrete-series point of Jones's positivity theorem), and both its null
  space and `(tr m).traceRadical` equal `RingHom.ker (evenCliffordHom m)`. In particular, at three
  strands (`dim TL_3 = 5`, `dim Cl_3⁰ = 4`), `evenCliffordHom 3` kills the negligible Jones–Wenzl
  projection `jonesWenzl (√2 : ℂ) 3`.

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
* `TauCeti.TemperleyLieb.cliffordIncl` and `TauCeti.TemperleyLieb.evenCliffordIncl`: the coordinate
  inclusions extending `Fin m → ℂ` by zero.
* `TauCeti.TemperleyLieb.evenCliffordTrace`: the unnormalized Markov trace at `√2` induced by
  `CliffordAlgebra.scalarTrace`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientEvenCliffordEquiv`: the algebra isomorphism between
  the `m`-strand Temperley–Lieb trace quotient at `√2` and `EvenClifford m`.

## Main results

* `TauCeti.TemperleyLieb.finrank_evenClifford`: `finrank ℂ (EvenClifford m) = 2 ^ (m - 1)`.
* `TauCeti.TemperleyLieb.scalarTrace_cliffordAdjoint_mul_self`,
  `TauCeti.TemperleyLieb.scalarTrace_cliffordAdjoint_mul_self_nonneg`, and
  `TauCeti.TemperleyLieb.scalarTrace_cliffordAdjoint_mul_self_eq_zero`: Parseval formula,
  positivity, and faithfulness of `s_m (a† * a)`.
* `TauCeti.TemperleyLieb.evenCliffordHom_surjective` and
  `TauCeti.TemperleyLieb.evenCliffordHom_star`: surjectivity and star compatibility of
  `evenCliffordHom`.
* `TauCeti.TemperleyLieb.isMarkovTrace_evenClifford` and
  `TauCeti.TemperleyLieb.IsMarkovTrace.apply_eq_mul_scalarTrace_evenCliffordHom`: the Markov-trace
  formula `tr m x = (√2) ^ m * scalarTrace (cliffordForm m) (evenCliffordHom m x)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_sqrt_two` and
  `TauCeti.TemperleyLieb.IsMarkovTrace.traceRadical_eq_ker_evenCliffordHom`: positivity of the
  Markov Hermitian form at `δ = √2` and identification of the trace radical with `ker F_m`.
* `TauCeti.TemperleyLieb.exists_evenCliffordModel`: packaged existence theorem for the even
  Clifford model at `δ = √2`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientEvenCliffordEquiv_quotientStrandIncl`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.finrank_quotient_traceRadical_sqrt_two`, and
  `TauCeti.TemperleyLieb.evenCliffordHom_jonesWenzl_three`: tower compatibility, quotient dimension
  `2 ^ (m - 1)`, and vanishing of the three-strand Jones–Wenzl projection.

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
* K. Iohara, G. I. Lehrer and R. B. Zhang, *Temperley–Lieb at roots of unity, a fusion category and
  the Jones quotient*, Math. Res. Lett. 26 (2019), no. 1, 121–158 (arXiv:1702.08128, Section 5.3,
  Theorem 5.4 and Proposition 5.5).
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4.
-/

public section

open scoped ComplexConjugate ComplexOrder TensorProduct

namespace TauCeti.TemperleyLieb

/-! ### Arithmetic helpers for `√2` in `ℂ` -/

/-- Viewed in `ℂ`, the real loop value `√2` is self-adjoint. -/
theorem isSelfAdjoint_ofReal_sqrt_two : IsSelfAdjoint (Real.sqrt 2 : ℂ) :=
  Complex.conj_ofReal _

instance : Fact (IsSelfAdjoint (Real.sqrt 2 : ℂ)) :=
  ⟨isSelfAdjoint_ofReal_sqrt_two⟩

private theorem sqrt_two_coe_mul_self :
    (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  exact_mod_cast Real.mul_self_sqrt zero_le_two

private theorem sqrt_two_coe_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr zero_lt_two)

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
  rw [cliffordForm_apply, Fintype.sum_eq_single j]
  · simp
  · intro i hij
    simp [hij]

/-- Distinct standard coordinate vectors are orthogonal for `cliffordForm m`. -/
theorem isOrtho_cliffordForm_single {m : ℕ} {j k : Fin m} (hjk : j ≠ k) (z w : ℂ) :
    (cliffordForm m).IsOrtho (Pi.single j z) (Pi.single k w) := by
  rw [← QuadraticMap.associated_isOrtho, associated_cliffordForm]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  by_cases hij : i = j
  · subst hij
    simp [hjk]
  · simp [hij]

/-- The standard basis `Pi.basisFun ℂ (Fin m)` is orthogonal for `cliffordForm m`. -/
theorem isOrthoᵢ_associated_cliffordForm (m : ℕ) :
    (QuadraticMap.associated (cliffordForm m)).IsOrthoᵢ (Pi.basisFun ℂ (Fin m)) := by
  intro j k hjk
  simpa [Function.onFun, Pi.basisFun_apply] using
    QuadraticMap.associated_isOrtho.mpr (isOrtho_cliffordForm_single hjk 1 1)

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
  rcases m with _ | m
  · have hle : Module.finrank ℂ (EvenClifford 0) ≤
        Module.finrank ℂ (CliffordAlgebra (cliffordForm 0)) :=
      Submodule.finrank_le (EvenClifford 0).toSubmodule
    rw [finrank_cliffordAlgebra_cliffordForm] at hle
    have hone : (1 : EvenClifford 0) ≠ 0 := by
      intro h0
      have htr := congrArg (CliffordAlgebra.scalarTrace (cliffordForm 0) ∘ Subtype.val) h0
      simp at htr
    have hpos : 0 < Module.finrank ℂ (EvenClifford 0) :=
      let _ : Nontrivial (EvenClifford 0) := ⟨⟨1, 0, hone⟩⟩
      Module.finrank_pos
    omega
  · rw [EvenClifford, CliffordAlgebra.finrank_even (cliffordForm (m + 1)),
      Module.finrank_fin_fun]

/-- The `j`-th **Majorana generator** `c_j = ι (Pi.single j 1)` of
`CliffordAlgebra (cliffordForm m)`. -/
noncomputable def majorana (m : ℕ) (j : Fin m) : CliffordAlgebra (cliffordForm m) :=
  CliffordAlgebra.ι (cliffordForm m) (Pi.single j 1)

/-- Unfolding `majorana` as the Clifford embedding of the `j`-th standard basis vector. -/
theorem majorana_def (m : ℕ) (j : Fin m) :
    majorana m j = CliffordAlgebra.ι (cliffordForm m) (Pi.single j 1) :=
  (rfl)

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
theorem majorana_mul_majorana_add_comm {m : ℕ} {j k : Fin m} (hjk : j ≠ k) :
    majorana m j * majorana m k + majorana m k * majorana m j = 0 := by
  rw [majorana_def, majorana_def, CliffordAlgebra.ι_mul_ι_add_swap,
    (isOrtho_cliffordForm_single hjk 1 1).polar_eq_zero, map_zero]

/-- Distinct Majorana generators anticommute: `c_j * c_k = -(c_k * c_j)`. -/
theorem majorana_mul_majorana_of_ne {m : ℕ} {j k : Fin m} (hjk : j ≠ k) :
    majorana m j * majorana m k = -(majorana m k * majorana m j) :=
  eq_neg_of_add_eq_zero_left (majorana_mul_majorana_add_comm hjk)

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
  simp only [List.map_map, Function.comp_def, Pi.basisFun_apply]
  rfl

/-! ### The analytic adjoint and positivity of the Clifford scalar trace -/

private noncomputable abbrev realCliffordForm (m : ℕ) : QuadraticForm ℝ (Fin m → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ (1 : Fin m → ℝ)

private theorem isOrthoᵢ_associated_realCliffordForm (m : ℕ) :
    (QuadraticMap.associated (realCliffordForm m)).IsOrthoᵢ (Pi.basisFun ℝ (Fin m)) := by
  intro j k hjk
  simp only [Function.onFun, Pi.basisFun_apply, QuadraticMap.associated_weightedSumSquares]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  by_cases hij : i = j
  · subst hij
    simp [hjk]
  · simp [hij]

private theorem posDef_realCliffordForm (m : ℕ) : (realCliffordForm m).PosDef := by
  intro v hv
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  simp only [realCliffordForm, QuadraticMap.weightedSumSquares_apply, Pi.one_apply, one_smul]
  exact Finset.sum_pos' (fun j _ ↦ mul_self_nonneg (v j))
    ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

/-- Canonical quadratic isometry identifying the complexification of the standard real form on
`ℝ^m` with `cliffordForm m` on `ℂ^m`. -/
private noncomputable def realCliffordBaseChangeIsometry (m : ℕ) :
    ((realCliffordForm m).baseChange ℂ).IsometryEquiv (cliffordForm m) :=
  (QuadraticForm.baseChangeWeightedSumSquares (A := ℂ) (1 : Fin m → ℝ)).trans
    { toLinearEquiv := LinearEquiv.refl ℂ (Fin m → ℂ)
      map_app' := fun v ↦ by simp [cliffordForm_apply, QuadraticMap.weightedSumSquares_apply] }

private noncomputable def realCliffordEquiv (m : ℕ) :
    CliffordAlgebra ((realCliffordForm m).baseChange ℂ) ≃ₐ[ℂ] CliffordAlgebra (cliffordForm m) :=
  CliffordAlgebra.equivOfIsometry (realCliffordBaseChangeIsometry m)

private theorem realCliffordBaseChangeIsometry_one_tmul_single (m : ℕ) (j : Fin m) :
    realCliffordBaseChangeIsometry m (1 ⊗ₜ[ℝ] Pi.single j (1 : ℝ)) = Pi.single j (1 : ℂ) := by
  ext k
  simp only [realCliffordBaseChangeIsometry, QuadraticMap.IsometryEquiv.trans_apply,
    QuadraticForm.baseChangeWeightedSumSquares_apply,
    ← QuadraticMap.IsometryEquiv.coe_toLinearEquiv, LinearEquiv.refl_apply,
    TensorProduct.piScalarRightHom_tmul]
  by_cases hkj : k = j
  · subst hkj
    simp
  · simp [hkj]

private theorem realCliffordEquiv_ι_single (m : ℕ) (j : Fin m) :
    realCliffordEquiv m (CliffordAlgebra.ι ((realCliffordForm m).baseChange ℂ)
      (1 ⊗ₜ[ℝ] Pi.single j (1 : ℝ))) = majorana m j := by
  simp [realCliffordEquiv, majorana_def, realCliffordBaseChangeIsometry_one_tmul_single]

private theorem realCliffordEquiv_symm_majorana (m : ℕ) (j : Fin m) :
    (realCliffordEquiv m).symm (majorana m j) =
      CliffordAlgebra.ι ((realCliffordForm m).baseChange ℂ) (1 ⊗ₜ[ℝ] Pi.single j (1 : ℝ)) :=
  (realCliffordEquiv m).injective <| by simp [realCliffordEquiv_ι_single]

/-- The **analytic adjoint** `a ↦ a†` on `CliffordAlgebra (cliffordForm m)`: the conjugate-linear,
product-reversing involution fixing each Majorana generator `majorana m j`. Under the canonical
isometry with the complexification of `ℝ^m`, it is the positive-form adjoint
`x ↦ complexConj (reverse x)`. -/
noncomputable def cliffordAdjoint (m : ℕ) :
    CliffordAlgebra (cliffordForm m) →ₗ⋆[ℂ] CliffordAlgebra (cliffordForm m) where
  toFun a := realCliffordEquiv m
    (CliffordAlgebra.complexConj (realCliffordForm m)
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
    have hv : v = ∑ j : Fin m, v j • Pi.single j (1 : ℂ) := by
      ext j
      simp [Pi.single_apply]
    rw [hv, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [← majorana_def, hmaj]
  | mul a b ha hb => rw [hmul, cliffordAdjoint_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- `cliffordAdjoint` commutes with the Clifford grade involution. -/
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
        (CliffordAlgebra.basis ((realCliffordForm m).baseChange ℂ)
          ((Pi.basisFun ℝ (Fin m)).baseChange ℂ) s) =
      CliffordAlgebra.basis (cliffordForm m) (Pi.basisFun ℂ (Fin m)) s := by
  have hb := QuadraticForm.isOrthoᵢ_associated_baseChange (A := ℂ)
    (isOrthoᵢ_associated_realCliffordForm m)
  rw [CliffordAlgebra.basis_eq_prod_map_sort hb, basis_cliffordForm_eq_prod_majorana, map_list_prod]
  simp [List.map_map, Function.comp_def, Pi.basisFun_apply, realCliffordEquiv_ι_single]

private theorem basis_repr_realCliffordEquiv_symm (m : ℕ)
    (a : CliffordAlgebra (cliffordForm m)) (s : Finset (Fin m)) :
    (CliffordAlgebra.basis ((realCliffordForm m).baseChange ℂ)
        ((Pi.basisFun ℝ (Fin m)).baseChange ℂ)).repr ((realCliffordEquiv m).symm a) s =
      (CliffordAlgebra.basis (cliffordForm m) (Pi.basisFun ℂ (Fin m))).repr a s := by
  let bR := CliffordAlgebra.basis ((realCliffordForm m).baseChange ℂ)
    ((Pi.basisFun ℝ (Fin m)).baseChange ℂ)
  let bC := CliffordAlgebra.basis (cliffordForm m) (Pi.basisFun ℂ (Fin m))
  have ha : (realCliffordEquiv m).symm a =
      Finsupp.linearCombination ℂ bR (bC.repr a) := by
    apply (realCliffordEquiv m).injective
    rw [AlgEquiv.apply_symm_apply]
    conv_lhs => rw [← bC.linearCombination_repr a]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum]
    refine Finsupp.sum_congr fun t _ ↦ ?_
    rw [map_smul, realCliffordEquiv_basis]
  rw [ha, Module.Basis.repr_linearCombination]

/-- Transports `cliffordAdjoint m a * a` to the complexification of `realCliffordForm m`. -/
private theorem cliffordAdjoint_mul_self_eq_map (m : ℕ)
    (a : CliffordAlgebra (cliffordForm m)) :
    cliffordAdjoint m a * a =
      CliffordAlgebra.map (realCliffordBaseChangeIsometry m).toIsometry
        (CliffordAlgebra.complexConj (realCliffordForm m)
          (CliffordAlgebra.reverse ((realCliffordEquiv m).symm a)) *
            (realCliffordEquiv m).symm a) := by
  rw [← CliffordAlgebra.equivOfIsometry_apply]
  have h : cliffordAdjoint m a * a =
      realCliffordEquiv m
        (CliffordAlgebra.complexConj (realCliffordForm m)
          (CliffordAlgebra.reverse ((realCliffordEquiv m).symm a)) *
            (realCliffordEquiv m).symm a) := by
    rw [map_mul, AlgEquiv.apply_symm_apply]
    rfl
  exact h

/-- **Parseval identity for the Clifford scalar trace**: in the ordered-product Majorana basis,
`scalarTrace (cliffordForm m) (cliffordAdjoint m a * a)` is the sum of squared moduli of the
coordinates of `a`. -/
theorem scalarTrace_cliffordAdjoint_mul_self (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    CliffordAlgebra.scalarTrace (cliffordForm m) (cliffordAdjoint m a * a) =
      (((CliffordAlgebra.basis (cliffordForm m) (Pi.basisFun ℂ (Fin m))).repr a).sum
        fun _ z ↦ Complex.normSq z : ℝ) := by
  have hrepr : (CliffordAlgebra.basis ((realCliffordForm m).baseChange ℂ)
        ((Pi.basisFun ℝ (Fin m)).baseChange ℂ)).repr ((realCliffordEquiv m).symm a) =
      (CliffordAlgebra.basis (cliffordForm m) (Pi.basisFun ℂ (Fin m))).repr a :=
    Finsupp.ext (basis_repr_realCliffordEquiv_symm m a)
  have hQ (i : Fin m) : realCliffordForm m (Pi.basisFun ℝ (Fin m) i) = 1 := by
    rw [Pi.basisFun_apply]
    simp only [realCliffordForm, QuadraticMap.weightedSumSquares_apply, Pi.one_apply, one_smul]
    rw [Fintype.sum_eq_single i]
    · simp
    · intro k hki
      simp [hki]
  rw [cliffordAdjoint_mul_self_eq_map, CliffordAlgebra.scalarTrace_map,
    CliffordAlgebra.scalarTrace_complexConj_reverse_mul_self
      (isOrthoᵢ_associated_realCliffordForm m), hrepr]
  simp only [hQ, Finset.prod_const_one, mul_one]

/-- **Positivity of the Clifford scalar trace** for `cliffordAdjoint m`. -/
theorem scalarTrace_cliffordAdjoint_mul_self_nonneg (m : ℕ)
    (a : CliffordAlgebra (cliffordForm m)) :
    0 ≤ CliffordAlgebra.scalarTrace (cliffordForm m) (cliffordAdjoint m a * a) := by
  rw [scalarTrace_cliffordAdjoint_mul_self, Complex.zero_le_real]
  exact Finsupp.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _

/-- **Faithfulness of the Clifford scalar trace** for `cliffordAdjoint m`:
`scalarTrace (cliffordForm m) (cliffordAdjoint m a * a) = 0` if and only if `a = 0`. -/
@[simp]
theorem scalarTrace_cliffordAdjoint_mul_self_eq_zero (m : ℕ)
    {a : CliffordAlgebra (cliffordForm m)} :
    CliffordAlgebra.scalarTrace (cliffordForm m) (cliffordAdjoint m a * a) = 0 ↔ a = 0 := by
  rw [cliffordAdjoint_mul_self_eq_map, CliffordAlgebra.scalarTrace_map,
    CliffordAlgebra.scalarTrace_complexConj_reverse_mul_self_eq_zero_iff
      (posDef_realCliffordForm m),
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

/-- Auxiliary involution `I • (c_a * c_b)` for distinct Majorana indices `a ≠ b`: its square is
`1`. -/
private theorem smul_I_majorana_mul_self {m : ℕ} {a b : Fin m} (hab : a ≠ b) :
    (Complex.I • (majorana m a * majorana m b)) *
      (Complex.I • (majorana m a * majorana m b)) = 1 := by
  have hmaj : (majorana m a * majorana m b) * (majorana m a * majorana m b) = -1 := by
    calc
      (majorana m a * majorana m b) * (majorana m a * majorana m b)
          = majorana m a * (majorana m b * majorana m a) * majorana m b := by
            simp only [mul_assoc]
      _ = -(majorana m a * majorana m a * (majorana m b * majorana m b)) := by
            rw [majorana_mul_majorana_of_ne hab.symm]
            simp only [mul_neg, neg_mul, mul_assoc]
      _ = -1 := by simp
  rw [smul_mul_smul_comm, hmaj, Complex.I_mul_I, neg_one_smul, neg_neg]

/-- Two Majorana-pair involutions sharing exactly one index anticommute. -/
private theorem smul_I_majorana_anticommute {m : ℕ} {a b c d : Fin m}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b = c) (hbd : b ≠ d) :
    (Complex.I • (majorana m a * majorana m b)) *
        (Complex.I • (majorana m c * majorana m d)) +
      (Complex.I • (majorana m c * majorana m d)) *
        (Complex.I • (majorana m a * majorana m b)) = 0 := by
  subst hbc
  have hleft : (majorana m a * majorana m b) * (majorana m b * majorana m d) =
      majorana m a * majorana m d := by
    calc
      (majorana m a * majorana m b) * (majorana m b * majorana m d)
          = majorana m a * (majorana m b * majorana m b) * majorana m d := by
            simp only [mul_assoc]
      _ = majorana m a * majorana m d := by simp
  have hright : (majorana m b * majorana m d) * (majorana m a * majorana m b) =
      -(majorana m a * majorana m d) := by
    calc
      (majorana m b * majorana m d) * (majorana m a * majorana m b)
          = majorana m b * (majorana m d * majorana m a) * majorana m b := by
            simp only [mul_assoc]
      _ = -(majorana m b * majorana m a * majorana m d * majorana m b) := by
            rw [majorana_mul_majorana_of_ne had.symm]
            simp only [mul_neg, neg_mul, mul_assoc]
      _ = majorana m a * majorana m b * majorana m d * majorana m b := by
            rw [majorana_mul_majorana_of_ne hac.symm]
            simp only [neg_mul, neg_neg]
      _ = -(majorana m a * majorana m d * (majorana m b * majorana m b)) := by
            calc
              majorana m a * majorana m b * majorana m d * majorana m b
                  = majorana m a * (majorana m b * majorana m d) * majorana m b := by
                    simp only [mul_assoc]
              _ = -(majorana m a * majorana m d * (majorana m b * majorana m b)) := by
                    rw [majorana_mul_majorana_of_ne hbd]
                    simp only [mul_neg, neg_mul, mul_assoc]
      _ = -(majorana m a * majorana m d) := by simp
  rw [smul_mul_smul_comm, smul_mul_smul_comm, hleft, hright, ← smul_add, add_neg_cancel, smul_zero]

/-- In any ring, if `u * u = 1` and `u * v + v * u = 0`, then `(1 + u) * (1 + v) * (1 + u)`
simplifies to `(1 + u) + (1 + u)`. -/
private theorem one_add_mul_one_add_mul_one_add {A : Type*} [Ring A] {u v : A}
    (hu : u * u = 1) (huv : u * v + v * u = 0) :
    (1 + u) * (1 + v) * (1 + u) = (1 + u) + (1 + u) := by
  have hvu : v * u = -(u * v) := eq_neg_of_add_eq_zero_right huv
  have huvu : u * v * u = -v := by
    rw [mul_assoc, hvu, mul_neg, ← mul_assoc, hu, one_mul]
  calc
    (1 + u) * (1 + v) * (1 + u)
        = (1 + u + v + u * v) * (1 + u) := by
          simp only [add_mul, mul_add, one_mul, mul_one]
          abel
    _ = 1 + u + v + u * v + (u + u * u + v * u + u * v * u) := by
          simp only [mul_add, add_mul, mul_one, one_mul]
    _ = (1 + u) + (1 + u) := by
          rw [hu, hvu, huvu]
          abel

/-- Every Clifford projection is self-adjoint for `cliffordAdjoint m`. -/
@[simp]
theorem cliffordAdjoint_cliffordProjection (m : ℕ) (j : Fin (m - 1)) :
    cliffordAdjoint m (cliffordProjection m j) = cliffordProjection m j := by
  have hne : (⟨j.1, by omega⟩ : Fin m) ≠ ⟨j.1 + 1, by omega⟩ :=
    ne_of_apply_ne Fin.val (by dsimp; omega)
  rw [cliffordProjection_def, map_smulₛₗ, map_add, cliffordAdjoint_one, map_smulₛₗ,
    cliffordAdjoint_mul, cliffordAdjoint_majorana, cliffordAdjoint_majorana,
    majorana_mul_majorana_of_ne hne.symm]
  simp [smul_neg, smul_add, map_inv₀, map_ofNat]

/-- Every Clifford projection is idempotent. -/
@[simp]
theorem cliffordProjection_mul_self (m : ℕ) (j : Fin (m - 1)) :
    cliffordProjection m j * cliffordProjection m j = cliffordProjection m j := by
  have hne : (⟨j.1, by omega⟩ : Fin m) ≠ ⟨j.1 + 1, by omega⟩ :=
    ne_of_apply_ne Fin.val (by dsimp; omega)
  rw [cliffordProjection_def]
  set u := Complex.I • (majorana m ⟨j.1, by omega⟩ * majorana m ⟨j.1 + 1, by omega⟩)
  have hu : u * u = 1 := smul_I_majorana_mul_self hne
  have h1u : (1 + u) * (1 + u) = (2 : ℂ) • (1 + u) := by
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, hu, two_smul]
    abel
  rw [smul_mul_smul_comm, h1u, smul_smul]
  norm_num

/-- Adjacent Clifford projections satisfy `p_i * p_j * p_i = 2⁻¹ • p_i`. -/
theorem cliffordProjection_mul_cliffordProjection_mul_self {m : ℕ} {i j : Fin (m - 1)}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    cliffordProjection m i * cliffordProjection m j * cliffordProjection m i =
      (2 : ℂ)⁻¹ • cliffordProjection m i := by
  have hi_ne : (⟨i.1, by omega⟩ : Fin m) ≠ ⟨i.1 + 1, by omega⟩ :=
    ne_of_apply_ne Fin.val (by dsimp; omega)
  rw [cliffordProjection_def m i, cliffordProjection_def m j]
  set u := Complex.I • (majorana m ⟨i.1, by omega⟩ * majorana m ⟨i.1 + 1, by omega⟩)
  set v := Complex.I • (majorana m ⟨j.1, by omega⟩ * majorana m ⟨j.1 + 1, by omega⟩)
  have hu : u * u = 1 := smul_I_majorana_mul_self hi_ne
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
    rw [one_add_mul_one_add_mul_one_add hu huv, two_smul]
  simp only [smul_mul_assoc, mul_smul_comm, hprod, smul_smul]
  norm_num

/-- Disjoint Majorana pairs commute. -/
private theorem commute_majorana_pair {m : ℕ} {a b c d : Fin m}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Commute (majorana m a * majorana m b) (majorana m c * majorana m d) := by
  have ha_comm : Commute (majorana m a) (majorana m c * majorana m d) := by
    rw [commute_iff_eq, ← mul_assoc, majorana_mul_majorana_of_ne hac, neg_mul, mul_assoc,
      majorana_mul_majorana_of_ne had, mul_neg, neg_neg, mul_assoc]
  have hb_comm : Commute (majorana m b) (majorana m c * majorana m d) := by
    rw [commute_iff_eq, ← mul_assoc, majorana_mul_majorana_of_ne hbc, neg_mul, mul_assoc,
      majorana_mul_majorana_of_ne hbd, mul_neg, neg_neg, mul_assoc]
  exact ha_comm.mul_left hb_comm

/-- Distant Clifford projections commute. -/
theorem commute_cliffordProjection {m : ℕ} {i j : Fin (m - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (cliffordProjection m i) (cliffordProjection m j) := by
  have hpair : Commute
      (majorana m ⟨i.1, by omega⟩ * majorana m ⟨i.1 + 1, by omega⟩)
      (majorana m ⟨j.1, by omega⟩ * majorana m ⟨j.1 + 1, by omega⟩) := by
    refine commute_majorana_pair ?_ ?_ ?_ ?_ <;>
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
        cliffordProjection_mul_cliffordProjection_mul_self h, smul_smul]
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

/-- On at most one strand, where `TemperleyLieb` is the base field `ℂ`, `evenCliffordHom` acts as
the scalar `algebraMap`. -/
theorem evenCliffordHom_algEquivOfLeOne_symm {m : ℕ} (hm : m ≤ 1) (z : ℂ) :
    evenCliffordHom m ((algEquivOfLeOne (Real.sqrt 2 : ℂ) hm).symm z) =
      algebraMap ℂ (EvenClifford m) z := by
  rw [algEquivOfLeOne_symm_apply, AlgHom.commutes]

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
  rw [map_smul, map_sub, map_smul, map_one, he, cliffordProjection_def, smul_smul, smul_smul,
    hscale, one_smul, add_sub_cancel_left, smul_smul]
  simp [i]

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

/-- Every Majorana pair `c_j * c_k` lies in `(ambientEvenCliffordHom m).range`. -/
private theorem majorana_mul_majorana_mem_range_ambient (m : ℕ) (j k : Fin m) :
    majorana m j * majorana m k ∈ (ambientEvenCliffordHom m).range := by
  rcases lt_trichotomy j.1 k.1 with hlt | heq | hgt
  · have hj_eq : (⟨j.1, by omega⟩ : Fin m) = j := Fin.ext rfl
    have hk_eq : (⟨j.1 + (k.1 - j.1 - 1) + 1, by omega⟩ : Fin m) = k :=
      Fin.ext (by dsimp; omega)
    simpa only [hj_eq, hk_eq] using
      majorana_mul_mem_range_ambient_of_lt (m := m) (d := k.1 - j.1 - 1) (j := j.1) (by omega)
  · have hjk : j = k := Fin.ext heq
    subst hjk
    rw [majorana_mul_self]
    exact one_mem _
  · have hk_eq : (⟨k.1, by omega⟩ : Fin m) = k := Fin.ext rfl
    have hj_eq : (⟨k.1 + (j.1 - k.1 - 1) + 1, by omega⟩ : Fin m) = j :=
      Fin.ext (by dsimp; omega)
    have hmem : majorana m k * majorana m j ∈ (ambientEvenCliffordHom m).range := by
      simpa only [hk_eq, hj_eq] using
        majorana_mul_mem_range_ambient_of_lt (m := m) (d := j.1 - k.1 - 1) (j := k.1) (by omega)
    rw [majorana_mul_majorana_of_ne (Fin.ne_of_gt hgt)]
    exact neg_mem hmem

/-- Every product of two vectors `ι v * ι w` lies in `(ambientEvenCliffordHom m).range`. -/
private theorem ι_mul_ι_mem_range_ambient (m : ℕ) (v w : Fin m → ℂ) :
    CliffordAlgebra.ι (cliffordForm m) v * CliffordAlgebra.ι (cliffordForm m) w ∈
      (ambientEvenCliffordHom m).range := by
  have hv : v = ∑ j : Fin m, v j • Pi.single j (1 : ℂ) := by
    ext j
    simp [Pi.single_apply]
  have hw : w = ∑ k : Fin m, w k • Pi.single k (1 : ℂ) := by
    ext k
    simp [Pi.single_apply]
  rw [hv, hw, map_sum, map_sum, Finset.sum_mul]
  refine sum_mem fun j _ ↦ ?_
  rw [Finset.mul_sum]
  refine sum_mem fun k _ ↦ ?_
  simp only [map_smul, smul_mul_smul_comm, ← majorana_def]
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

/-! ### Coordinate inclusions and the Markov trace identity -/

/-- Extending a coordinate vector `v : Fin m → ℂ` by `0` in the last coordinate gives a quadratic
isometry `cliffordForm m →qᵢ cliffordForm (m + 1)`. -/
noncomputable def cliffordExtendIsometry (m : ℕ) :
    cliffordForm m →qᵢ cliffordForm (m + 1) where
  toFun v := Fin.snoc v 0
  map_add' u v := by
    ext i
    refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp
  map_smul' z v := by
    ext i
    refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp
  map_app' v := by
    simp [cliffordForm_apply, Fin.sum_univ_castSucc]

/-- Evaluation of `cliffordExtendIsometry` as `Fin.snoc · 0`. -/
@[simp]
theorem cliffordExtendIsometry_apply (m : ℕ) (v : Fin m → ℂ) :
    cliffordExtendIsometry m v = Fin.snoc v 0 :=
  (rfl)

/-- The algebra inclusion
`CliffordAlgebra (cliffordForm m) →ₐ[ℂ] CliffordAlgebra (cliffordForm (m + 1))` induced by
extending `Fin m → ℂ` by zero. -/
noncomputable def cliffordIncl (m : ℕ) :
    CliffordAlgebra (cliffordForm m) →ₐ[ℂ] CliffordAlgebra (cliffordForm (m + 1)) :=
  CliffordAlgebra.map (cliffordExtendIsometry m)

/-- Unfolding `cliffordIncl` as `CliffordAlgebra.map (cliffordExtendIsometry m)`. -/
theorem cliffordIncl_def (m : ℕ) :
    cliffordIncl m = CliffordAlgebra.map (cliffordExtendIsometry m) :=
  (rfl)

/-- The restricted coordinate inclusion `EvenClifford m →ₐ[ℂ] EvenClifford (m + 1)`. -/
noncomputable def evenCliffordIncl (m : ℕ) :
    EvenClifford m →ₐ[ℂ] EvenClifford (m + 1) :=
  ((cliffordIncl m).comp (EvenClifford m).val).codRestrict (EvenClifford (m + 1)) fun x ↦
    CliffordAlgebra.map_mem_even (cliffordExtendIsometry m) x.2

/-- Coercing `evenCliffordIncl` to the ambient Clifford algebra recovers `cliffordIncl`. -/
@[simp]
theorem coe_evenCliffordIncl (m : ℕ) (x : EvenClifford m) :
    (evenCliffordIncl m x : CliffordAlgebra (cliffordForm (m + 1))) = cliffordIncl m x :=
  (rfl)

/-- `cliffordIncl` maps the `j`-th Majorana generator to `majorana (m + 1) j.castSucc`. -/
@[simp]
theorem cliffordIncl_majorana (m : ℕ) (j : Fin m) :
    cliffordIncl m (majorana m j) = majorana (m + 1) j.castSucc := by
  have hsnoc :
      Fin.snoc (Pi.single j (1 : ℂ)) 0 = (Pi.single j.castSucc 1 : Fin (m + 1) → ℂ) := by
    ext k
    refine Fin.lastCases ?_ (fun k ↦ ?_) k
    · simp [(Fin.castSucc_lt_last j).ne']
    · simp [Pi.single_apply]
  simp [cliffordIncl_def, majorana_def, hsnoc]

/-- `cliffordIncl` maps the `j`-th Clifford projection to the `j`-th projection on `m + 1`
coordinates. -/
@[simp]
theorem cliffordIncl_cliffordProjection (m : ℕ) (j : Fin (m - 1)) :
    cliffordIncl m (cliffordProjection m j) =
      cliffordProjection (m + 1) ⟨j.1, by omega⟩ := by
  have h0 : (⟨j.1, by omega⟩ : Fin m).castSucc = (⟨j.1, by omega⟩ : Fin (m + 1)) := rfl
  have h1 : (⟨j.1 + 1, by omega⟩ : Fin m).castSucc = (⟨j.1 + 1, by omega⟩ : Fin (m + 1)) := rfl
  simp [cliffordProjection_def, h0, h1]

/-- `cliffordIncl` intertwines `cliffordAdjoint` across adjacent dimensions. -/
@[simp]
theorem cliffordIncl_cliffordAdjoint (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordIncl m (cliffordAdjoint m a) = cliffordAdjoint (m + 1) (cliffordIncl m a) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap z =>
    simp [Algebra.algebraMap_eq_smul_one]
  | ι v =>
    have hv : v = ∑ j : Fin m, v j • Pi.single j (1 : ℂ) := by
      ext j
      simp [Pi.single_apply]
    rw [hv, map_sum, map_sum, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [← majorana_def]
  | mul a b ha hb =>
    simp [ha, hb]
  | add a b ha hb =>
    simp [ha, hb]

/-- Coordinate inclusion preserves the Clifford scalar trace. -/
@[simp]
theorem scalarTrace_cliffordIncl (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    CliffordAlgebra.scalarTrace (cliffordForm (m + 1)) (cliffordIncl m a) =
      CliffordAlgebra.scalarTrace (cliffordForm m) a :=
  CliffordAlgebra.scalarTrace_map (cliffordExtendIsometry m) a

/-- The coordinate inclusion `cliffordIncl m` is injective. -/
theorem cliffordIncl_injective (m : ℕ) : Function.Injective (cliffordIncl m) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  apply (scalarTrace_cliffordAdjoint_mul_self_eq_zero m).mp
  rw [← scalarTrace_cliffordIncl m, map_mul, cliffordIncl_cliffordAdjoint, ha, mul_zero, map_zero]

/-- The even coordinate inclusion `evenCliffordIncl m` is injective. -/
theorem evenCliffordIncl_injective (m : ℕ) : Function.Injective (evenCliffordIncl m) := by
  intro x y hxy
  apply Subtype.ext
  exact cliffordIncl_injective m (congrArg Subtype.val hxy)

/-- `evenCliffordHom` intertwines Temperley–Lieb `strandIncl` with `evenCliffordIncl`. -/
@[simp]
theorem evenCliffordHom_strandIncl (n : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) (n + 1)) :
    evenCliffordHom (n + 2) (strandIncl x) =
      evenCliffordIncl (n + 1) (evenCliffordHom (n + 1) x) := by
  have hhom : (evenCliffordHom (n + 2)).comp strandIncl =
      (evenCliffordIncl (n + 1)).comp (evenCliffordHom (n + 1)) := by
    apply TemperleyLieb.hom_ext
    intro i
    apply Subtype.ext
    simp only [AlgHom.comp_apply, strandIncl_e, coe_evenCliffordHom_e, coe_evenCliffordIncl,
      map_smul, cliffordIncl_cliffordProjection]
    rfl
  exact AlgHom.congr_fun hhom x

/-- Multiplying an included Clifford element on the right by the last Clifford projection scales its
scalar trace by `2⁻¹`: the term containing `c_{n + 1}` vanishes by orthogonality. -/
theorem scalarTrace_cliffordIncl_mul_cliffordProjection_last (n : ℕ)
    (a : CliffordAlgebra (cliffordForm (n + 1))) :
    CliffordAlgebra.scalarTrace (cliffordForm (n + 2))
        (cliffordIncl (n + 1) a * cliffordProjection (n + 2) (Fin.last n)) =
      (2 : ℂ)⁻¹ * CliffordAlgebra.scalarTrace (cliffordForm (n + 1)) a := by
  have hortho : ∀ v : Fin (n + 1) → ℂ,
      (cliffordForm (n + 2)).IsOrtho (Pi.single (Fin.last (n + 1)) 1)
        (cliffordExtendIsometry (n + 1) v) := by
    intro v
    rw [← QuadraticMap.associated_isOrtho, associated_cliffordForm]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    refine Fin.lastCases ?_ (fun k ↦ ?_) k
    · simp
    · simp [(Fin.castSucc_lt_last k).ne]
  have hcast : (⟨(Fin.last n).1, by omega⟩ : Fin (n + 2)) = (Fin.last n).castSucc := rfl
  have hlast : (⟨(Fin.last n).1 + 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) := rfl
  have hterm : CliffordAlgebra.scalarTrace (cliffordForm (n + 2))
      (cliffordIncl (n + 1) a *
        (majorana (n + 2) (Fin.last n).castSucc * majorana (n + 2) (Fin.last (n + 1)))) = 0 := by
    rw [← cliffordIncl_majorana (n + 1) (Fin.last n), ← mul_assoc, ← map_mul, majorana_def,
      cliffordIncl_def]
    exact CliffordAlgebra.scalarTrace_map_mul_ι_eq_zero (cliffordExtendIsometry (n + 1)) hortho _
  rw [cliffordProjection_def, hcast, hlast, mul_smul_comm, mul_add, mul_one, mul_smul_comm,
    map_smul, map_add, map_smul, scalarTrace_cliffordIncl, hterm, smul_zero, add_zero, smul_eq_mul]

/-- The unnormalized Markov trace on `TemperleyLieb ℂ (√2 : ℂ) m` obtained by pulling back
`(√2) ^ m` times `CliffordAlgebra.scalarTrace (cliffordForm m)` along `evenCliffordHom m`. -/
noncomputable def evenCliffordTrace (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m →ₗ[ℂ] ℂ :=
  ((Real.sqrt 2 : ℂ) ^ m) •
    (CliffordAlgebra.scalarTrace (cliffordForm m) ∘ₗ
      (EvenClifford m).val.toLinearMap ∘ₗ (evenCliffordHom m).toLinearMap)

/-- Evaluation formula for `evenCliffordTrace`. -/
theorem evenCliffordTrace_apply (m : ℕ) (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m) :
    evenCliffordTrace m x =
      (Real.sqrt 2 : ℂ) ^ m *
        CliffordAlgebra.scalarTrace (cliffordForm m) (evenCliffordHom m x) :=
  (rfl)

/-- **The Clifford scalar trace defines a Markov trace at `δ = √2`.** -/
theorem isMarkovTrace_evenClifford :
    IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) evenCliffordTrace where
  map_one m := by simp [evenCliffordTrace_apply]
  map_mul_comm m x y := by
    simp only [evenCliffordTrace_apply, map_mul, Subalgebra.coe_mul,
      CliffordAlgebra.scalarTrace_mul_comm]
  map_strandIncl n x := by
    simp only [evenCliffordTrace_apply, evenCliffordHom_strandIncl, coe_evenCliffordIncl,
      scalarTrace_cliffordIncl, pow_succ']
    ring
  map_strandIncl_mul_e_last n x := by
    simp only [evenCliffordTrace_apply, map_mul, Subalgebra.coe_mul, evenCliffordHom_strandIncl,
      coe_evenCliffordIncl, coe_evenCliffordHom_e, mul_smul_comm, map_smul,
      scalarTrace_cliffordIncl_mul_cliffordProjection_last, smul_eq_mul]
    rw [pow_succ]
    calc
      (Real.sqrt 2 : ℂ) ^ (n + 1) * (Real.sqrt 2 : ℂ) *
          ((Real.sqrt 2 : ℂ) *
            ((2 : ℂ)⁻¹ *
              CliffordAlgebra.scalarTrace (cliffordForm (n + 1)) (evenCliffordHom (n + 1) x)))
          = (Real.sqrt 2 : ℂ) ^ (n + 1) *
              (((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) * (2 : ℂ)⁻¹) *
                CliffordAlgebra.scalarTrace (cliffordForm (n + 1)) (evenCliffordHom (n + 1) x) := by
            ring
      _ = (Real.sqrt 2 : ℂ) ^ (n + 1) *
            CliffordAlgebra.scalarTrace (cliffordForm (n + 1)) (evenCliffordHom (n + 1) x) := by
            rw [sqrt_two_coe_mul_self]
            norm_num

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 2 : ℂ) n →ₗ[ℂ] ℂ}

/-- Every Markov trace on `TemperleyLieb ℂ (√2 : ℂ)` coincides with `evenCliffordTrace`. -/
theorem eq_evenCliffordTrace (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) :
    tr = evenCliffordTrace :=
  htr.unique isMarkovTrace_evenClifford

/-- **The Markov trace at `δ = √2` as the Clifford scalar trace**: for every Markov trace `tr`,
`tr m x = (√2 : ℂ) ^ m * scalarTrace (cliffordForm m) (evenCliffordHom m x)`. -/
theorem apply_eq_mul_scalarTrace_evenCliffordHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m) :
    tr m x =
      (Real.sqrt 2 : ℂ) ^ m *
        CliffordAlgebra.scalarTrace (cliffordForm m) (evenCliffordHom m x) := by
  rw [htr.eq_evenCliffordTrace, evenCliffordTrace_apply]

/-- **Positivity of the Markov trace at `δ = √2`** (the `m = 4` discrete-series point
`2 cos (π / 4)` of Jones's positivity theorem): `0 ≤ tr m (star x * x)` on every number of
strands. -/
theorem map_star_mul_self_nonneg_sqrt_two
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) {m : ℕ}
    (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m) :
    0 ≤ tr m (star x * x) := by
  rw [htr.apply_eq_mul_scalarTrace_evenCliffordHom, map_mul, Subalgebra.coe_mul,
    coe_evenCliffordHom_star, scalarTrace_cliffordAdjoint_mul_self, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.zero_le_real]
  exact mul_nonneg (by positivity) (Finsupp.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _)

/-- At `δ = √2`, `tr m (star x * x) = 0` if and only if `evenCliffordHom m x = 0`. -/
theorem map_star_mul_self_eq_zero_iff_evenCliffordHom_eq_zero
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) {m : ℕ}
    {x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m} :
    tr m (star x * x) = 0 ↔ evenCliffordHom m x = 0 := by
  rw [htr.apply_eq_mul_scalarTrace_evenCliffordHom, map_mul, Subalgebra.coe_mul,
    coe_evenCliffordHom_star, mul_eq_zero,
    or_iff_right (pow_ne_zero m sqrt_two_coe_ne_zero),
    scalarTrace_cliffordAdjoint_mul_self_eq_zero, Subtype.ext_iff, Subalgebra.coe_zero]

/-! ### Kernel = trace radical and the Jones quotient equivalence -/

/-- **The trace radical at `δ = √2` is the kernel of `evenCliffordHom`.** -/
theorem traceRadical_eq_ker_evenCliffordHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) (m : ℕ) :
    (tr m).traceRadical (htr.map_mul_comm m) = RingHom.ker (evenCliffordHom m) := by
  ext x
  rw [LinearMap.mem_traceRadical, RingHom.mem_ker]
  simp only [htr.apply_eq_mul_scalarTrace_evenCliffordHom, map_mul, mul_eq_zero,
    pow_ne_zero m sqrt_two_coe_ne_zero, false_or]
  exact ((evenCliffordHom_surjective m).forall
    (p := fun b ↦ CliffordAlgebra.scalarTrace (cliffordForm m)
      ((evenCliffordHom m x * b : EvenClifford m) :
        CliffordAlgebra (cliffordForm m)) = 0)).symm.trans
    (CliffordAlgebra.forall_even_scalarTrace_mul_eq_zero_iff_eq_zero (nondegenerate_cliffordForm m))

/-- At `δ = √2`, the null vectors of `x ↦ tr m (star x * x)` are precisely the trace radical. -/
theorem map_star_mul_self_eq_zero_iff_mem_traceRadical_sqrt_two
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) {m : ℕ}
    {x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m} :
    tr m (star x * x) = 0 ↔ x ∈ (tr m).traceRadical (htr.map_mul_comm m) := by
  rw [htr.map_star_mul_self_eq_zero_iff_evenCliffordHom_eq_zero,
    htr.traceRadical_eq_ker_evenCliffordHom, RingHom.mem_ker]

/-- **The Jones quotient at `δ = √2` is isomorphic to the even Clifford algebra**
`EvenClifford m`. -/
noncomputable def quotientEvenCliffordEquiv
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) (m : ℕ) :
    (TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) ≃ₐ[ℂ]
      EvenClifford m :=
  (Ideal.quotientEquivAlgOfEq ℂ (htr.traceRadical_eq_ker_evenCliffordHom m)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (evenCliffordHom_surjective m))

/-- `quotientEvenCliffordEquiv` evaluates on a quotient representative via `evenCliffordHom`. -/
@[simp]
theorem quotientEvenCliffordEquiv_mk
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m) :
    htr.quotientEvenCliffordEquiv m
        (Ideal.Quotient.mk ((tr m).traceRadical (htr.map_mul_comm m)) x) =
      evenCliffordHom m x :=
  Ideal.quotientKerAlgEquivOfSurjective_mk (evenCliffordHom_surjective m) x

/-- `quotientEvenCliffordEquiv` intertwines the Temperley–Lieb quotient strand map
`quotientStrandIncl` with the even Clifford coordinate inclusion `evenCliffordIncl`. -/
@[simp]
theorem quotientEvenCliffordEquiv_quotientStrandIncl
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) (n : ℕ)
    (q : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) (n + 1) ⧸
      (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientEvenCliffordEquiv (n + 2) (htr.quotientStrandIncl n q) =
      evenCliffordIncl (n + 1) (htr.quotientEvenCliffordEquiv (n + 1) q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp

/-- The induced trace on the `m`-strand Temperley–Lieb quotient at `δ = √2` is `(√2 : ℂ) ^ m` times
`CliffordAlgebra.scalarTrace` under `quotientEvenCliffordEquiv`. -/
@[simp]
theorem quotientTrace_eq_mul_scalarTrace_quotientEvenCliffordEquiv
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) (m : ℕ)
    (q : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m ⧸
      (tr m).traceRadical (htr.map_mul_comm m)) :
    (tr m).quotientTrace (htr.map_mul_comm m) q =
      (Real.sqrt 2 : ℂ) ^ m *
        CliffordAlgebra.scalarTrace (cliffordForm m) (htr.quotientEvenCliffordEquiv m q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [htr.apply_eq_mul_scalarTrace_evenCliffordHom]

/-- The `m`-strand Temperley–Lieb trace quotient at `δ = √2` has complex dimension `2 ^ (m - 1)`. -/
@[simp]
theorem finrank_quotient_traceRadical_sqrt_two
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) (m : ℕ) :
    Module.finrank ℂ
        (TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) =
      2 ^ (m - 1) := by
  rw [(htr.quotientEvenCliffordEquiv m).toLinearEquiv.finrank_eq, finrank_evenClifford]

end IsMarkovTrace

/-- Specialization of `IsMarkovTrace.apply_eq_mul_scalarTrace_evenCliffordHom` to the spin-model
`markovTrace` at any unit `q : ℂˣ` satisfying `(√2 : ℂ) = -(q + q⁻¹)`. -/
theorem markovTrace_eq_mul_scalarTrace_evenCliffordHom (q : ℂˣ)
    (hq : (Real.sqrt 2 : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) {m : ℕ}
    (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m) :
    markovTrace q hq x =
      (Real.sqrt 2 : ℂ) ^ m *
        CliffordAlgebra.scalarTrace (cliffordForm m) (evenCliffordHom m x) :=
  (isMarkovTrace_markovTrace q hq).apply_eq_mul_scalarTrace_evenCliffordHom m x

/-! ### Packaged even Clifford model and vanishing of the three-strand Jones–Wenzl projection -/

/-- **The even Clifford model of `TemperleyLieb ℂ (√2 : ℂ) m`.** For every Markov trace `tr` at
loop value `√2` and every `m : ℕ`, there is a surjective `ℂ`-algebra homomorphism
`F : TemperleyLieb ℂ (√2 : ℂ) m →ₐ[ℂ] EvenClifford m` sending each generator `e j` to
`(√2 : ℂ) • cliffordProjection m j`, intertwining `star` with `cliffordAdjoint m`, expressing
`tr m` as `(√2 : ℂ) ^ m` times `CliffordAlgebra.scalarTrace (cliffordForm m)`, and having kernel
equal to the trace radical `(tr m).traceRadical`. -/
theorem exists_evenCliffordModel
    {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 2 : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) (m : ℕ) :
    ∃ F : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m →ₐ[ℂ] EvenClifford m,
      Function.Surjective F ∧
      (∀ j : Fin (m - 1),
        (F (e (Real.sqrt 2 : ℂ) j) : CliffordAlgebra (cliffordForm m)) =
          (Real.sqrt 2 : ℂ) • cliffordProjection m j) ∧
      (∀ x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m,
        (F (star x) : CliffordAlgebra (cliffordForm m)) =
          cliffordAdjoint m (F x)) ∧
      (∀ x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m,
        tr m x =
          (Real.sqrt 2 : ℂ) ^ m *
            CliffordAlgebra.scalarTrace (cliffordForm m) (F x)) ∧
      RingHom.ker F = (tr m).traceRadical (htr.map_mul_comm m) :=
  ⟨evenCliffordHom m,
    evenCliffordHom_surjective m,
    coe_evenCliffordHom_e m,
    coe_evenCliffordHom_star,
    htr.apply_eq_mul_scalarTrace_evenCliffordHom m,
    (htr.traceRadical_eq_ker_evenCliffordHom m).symm⟩

/-- At `δ = √2`, the three-strand Jones–Wenzl projection `jonesWenzl (√2 : ℂ) 3` is killed by
`evenCliffordHom 3`: the quantum integers `[1] = 1`, `[2] = √2`, `[3] = 1` are units while
`[4] = 0`, spanning the one-dimensional kernel between `dim TL_3 = 5` and `dim Cl_3⁰ = 4`. -/
@[simp]
theorem evenCliffordHom_jonesWenzl_three :
    evenCliffordHom 3 (jonesWenzl (Real.sqrt 2 : ℂ) 3) = 0 := by
  have hq3 : qInt ℂ (Real.sqrt 2 : ℂ) 3 = 1 := by
    rw [qInt_add_two (Real.sqrt 2 : ℂ) 1, qInt_two, qInt_one, sqrt_two_coe_mul_self]
    norm_num
  have hq4 : qInt ℂ (Real.sqrt 2 : ℂ) 4 = 0 := by
    rw [qInt_add_two (Real.sqrt 2 : ℂ) 2, hq3, qInt_two]
    ring
  have hunits : ∀ k ∈ Finset.Icc 1 3, IsUnit (qInt ℂ (Real.sqrt 2 : ℂ) k) := by
    intro k hk
    obtain ⟨hk1, hk3⟩ := Finset.mem_Icc.mp hk
    interval_cases k
    · simp
    · simp [qInt_two]
    · simp [hq3]
  rw [← RingHom.mem_ker, ← isMarkovTrace_evenClifford.traceRadical_eq_ker_evenCliffordHom 3,
    isMarkovTrace_evenClifford.jonesWenzl_mem_traceRadical_iff hunits]
  exact hq4

end TauCeti.TemperleyLieb
