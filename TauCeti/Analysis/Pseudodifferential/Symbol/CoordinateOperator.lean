/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Differential
public import TauCeti.Geometry.Manifold.DifferentialOperator.Coordinates

/-!
# Differential operators on `C^∞(ℝⁿ)` as classical pseudodifferential operators

A linear endomorphism `D` of the smooth real functions `C^∞(ℝⁿ)` is a differential operator of
order at most `m` in Grothendieck's sense (`TauCeti.differentialOperators`) when all its
`(m + 1)`-fold commutators with multiplication operators vanish; no continuity of `D` is assumed.
Such an operator is a coordinate expression `D f = ∑_{|α| ≤ m} c_α ∂^α f` with smooth real
coefficients `c_α` (`Module.Basis.eq_coordinateOperator_coordinateCoeff`). This file identifies
`D` with a classical pseudodifferential operator of order `m`: the quantization of its polynomial
left Fourier symbol

`σ_D(x, ξ) = ∑_{|α| ≤ m} c_α(x) (i ξ)^α`,

in the angular-frequency convention `σ(∂ⱼ) = i ξⱼ`.

* `TauCeti.ClassicalSymbol.ofDifferentialOperator D hD`: the classical symbol of order `m` of
  `D`, acting diagonally on functions with values in a complex normed space `V`. Its full symbol
  is `σ_D(x, ξ) • id` (`TauCeti.ClassicalSymbol.coefficient_toSymbol_ofDifferentialOperator`).
* `TauCeti.ClassicalSymbol.apply_quantizeSchwartzValue_ofDifferentialOperator`: on Schwartz
  input the quantization is `D`, with no smoothing remainder: for every real-linear functional
  `ℓ` on `V`, `ℓ (Op(σ_D) u (x)) = D (ℓ ∘ u) (x)`. For complex-valued input
  (`TauCeti.ClassicalSymbol.quantizeSchwartzValue_ofDifferentialOperator`) this says that
  `Op(σ_D)` is the complexification `u ↦ D (Re u) + i D (Im u)` of `D`.
* `TauCeti.ClassicalSymbol.coefficient_principal_ofDifferentialOperator`: the principal symbol of
  `σ_D` is `i ^ m` times the principal symbol `TauCeti.smoothPrincipalSymbol` of `D`, defined
  intrinsically by iterated commutators, at the covector `⟪ξ, ·⟫`. Hence `D` is elliptic as a
  pseudodifferential operator exactly when its geometric principal symbol vanishes at no nonzero
  covector (`TauCeti.ClassicalSymbol.isElliptic_ofDifferentialOperator_iff`).

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.1)–(1.4).
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §19.
-/

public section

noncomputable section

open Finset
open scoped ContDiff Manifold RealInnerProductSpace LineDeriv SchwartzMap

namespace TauCeti

variable {n : ℕ}

/-! ### Words of coordinate indices -/

/-- The word in which each coordinate index `j` occurs `α j` times, in increasing order. -/
private def multiIndexWord (α : Fin n → ℕ) : List (Fin n) :=
  (List.finRange n).flatMap fun j ↦ List.replicate (α j) j

private theorem count_multiIndexWord (α : Fin n → ℕ) (j : Fin n) :
    (multiIndexWord α).count j = α j := by
  simp [multiIndexWord, List.count_flatMap, List.count_replicate, ← Fin.sum_univ_def]

private theorem length_multiIndexWord (α : Fin n → ℕ) :
    (multiIndexWord α).length = ∑ j, α j := by
  simp [multiIndexWord, List.length_flatMap, ← Fin.sum_univ_def]

/-- The product of `g` over the letters of `multiIndexWord α` is `∏ⱼ g j ^ α j`. -/
private theorem prod_multiIndexWord {M : Type*} [CommMonoid M] (α : Fin n → ℕ) (g : Fin n → M) :
    ∏ t, g ((multiIndexWord α).get t) = ∏ j, g j ^ α j := by
  rw [show ∏ t, g ((multiIndexWord α).get t) = ((multiIndexWord α).map g).prod from
    Fin.prod_univ_fun_getElem (multiIndexWord α) g]
  have key : ∀ L : List (Fin n), ((L.flatMap fun j ↦ List.replicate (α j) j).map g).prod =
      (L.map fun j ↦ g j ^ α j).prod := by
    intro L
    induction L with
    | nil => simp
    | cons j L ih => simp [List.prod_append, List.prod_replicate, ih]
  rw [multiIndexWord, key, Fin.prod_univ_def]

/-- A monomial `∏ₜ i ⟪ξ, e_{wₜ}⟫` of the differential symbol along `multiIndexWord α`, with
`|α| = k`, is `i ^ k ξ^α`. -/
private theorem prod_inner_multiIndexWord {k : ℕ} {α : Fin n → ℕ} (hα : ∑ j, α j = k)
    (ξ : CoordinateSpace n) :
    ∏ t, (Complex.I * (⟪ξ, EuclideanSpace.single ((multiIndexWord α).get t) 1⟫ : ℂ)) =
      Complex.I ^ k * ∏ j, (ξ j : ℂ) ^ α j := by
  have h := prod_multiIndexWord α fun j ↦ (⟪ξ, EuclideanSpace.single j 1⟫ : ℂ)
  rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, h]
  congr 1
  · rw [length_multiIndexWord, hα]
  · refine prod_congr rfl fun j _ ↦ ?_
    rw [EuclideanSpace.inner_single_right]
    simp

/-! ### The coordinate expression in coordinate derivatives -/

/-- The monomial in the partial derivatives along the standard basis of `ℝⁿ` whose multi-index
counts the letters of a word is the iterated coordinate derivative along that word. -/
private theorem coe_multiIndexDeriv_count (l : List (Fin n))
    (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯) :
    ⇑(multiIndexDeriv (fun j ↦ lineDerivation ℝ ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis j))
        (fun i j ↦ commute_lineDerivation ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis i)
          ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis j)) (fun j ↦ l.count j) f) =
      coordinateDeriv l f := by
  induction l with
  | nil =>
    rw [show (fun j : Fin n ↦ ([] : List (Fin n)).count j) = 0 from funext fun _ ↦ by simp,
      multiIndexDeriv_zero, one_apply_eq_self, coordinateDeriv_nil]
  | cons j l ih =>
    have hcount : (fun i ↦ (j :: l).count i) = Pi.single j 1 + fun i ↦ l.count i := by
      funext i
      rcases eq_or_ne i j with rfl | hij
      · simp [add_comm]
      · simp [hij, Ne.symm hij]
    funext x
    rw [hcount, multiIndexDeriv_add, multiIndexDeriv_single, pow_one, mul_apply_eq_comp,
      Derivation.coeFn_coe, lineDerivation_apply_apply, ih, coordinateDeriv_cons]
    simp

/-- The multi-indices of order at most `m`. -/
private def multiIndices (n m : ℕ) : Finset (Fin n → ℕ) :=
  (range (m + 1)).biUnion fun k ↦ piAntidiag univ k

private theorem sum_multiIndices {M : Type*} [AddCommMonoid M] (m : ℕ) (g : (Fin n → ℕ) → M) :
    ∑ α ∈ multiIndices n m, g α = ∑ k ∈ range (m + 1), ∑ α ∈ piAntidiag univ k, g α := by
  refine sum_biUnion fun k _ k' _ hkk' ↦ disjoint_left.2 fun α hk hk' ↦ hkk' ?_
  rw [← (mem_piAntidiag.1 hk).1, ← (mem_piAntidiag.1 hk').1]

private theorem sum_le_of_mem_multiIndices {m : ℕ} {α : Fin n → ℕ} (hα : α ∈ multiIndices n m) :
    ∑ j, α j ≤ m := by
  obtain ⟨k, hk, hα⟩ := mem_biUnion.1 hα
  rw [(mem_piAntidiag.1 hα).1]
  simpa [Nat.lt_succ_iff] using hk

private theorem filter_multiIndices (m : ℕ) :
    {α ∈ multiIndices n m | (multiIndexWord α).length = m} = piAntidiag univ m := by
  ext α
  simp only [mem_filter, length_multiIndexWord, mem_piAntidiag, multiIndices, mem_biUnion,
    mem_range]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨h, by simp⟩
  · rintro ⟨h, -⟩
    exact ⟨⟨m, by omega, h, by simp⟩, h⟩

/-! ### The classical symbol of a differential operator -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {m : ℕ}

/-- Multiplication by a smooth real function, as a smooth family of operators on `V`. -/
private theorem contDiff_ofReal_smul_id (c : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯) :
    ContDiff ℝ ∞ fun x ↦ (c x : ℂ) • ContinuousLinearMap.id ℂ V :=
  (Complex.ofRealCLM.contDiff.comp (contMDiff_iff_contDiff.1 c.contMDiff)).smul contDiff_const

namespace ClassicalSymbol

/-- The classical symbol of order `m` of a differential operator `D` of order at most `m` on the
smooth real functions on `ℝⁿ`, acting diagonally on `V`-valued functions. With the coordinate
expression `D f = ∑_{|α| ≤ m} c_α ∂^α f`, its full symbol is `∑_{|α| ≤ m} c_α(x) (i ξ)^α • id`
(`TauCeti.ClassicalSymbol.coefficient_toSymbol_ofDifferentialOperator`), and its quantization
is `D` on Schwartz input
(`TauCeti.ClassicalSymbol.apply_quantizeSchwartzValue_ofDifferentialOperator`). -/
def ofDifferentialOperator
    (D : differentialOperators ℝ C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯
      C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯
      C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯ m) :
    ClassicalSymbol n V V m :=
  ofDifferentialSymbol (k := fun α ↦ (multiIndexWord α).length) m (multiIndices n m)
    (fun α t ↦ EuclideanSpace.single ((multiIndexWord α).get t) 1)
    (fun α x ↦ (coordinateCoeff (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.smoothCoord
      (D : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯ →ₗ[ℝ]
        C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯) α x : ℂ) •
      ContinuousLinearMap.id ℂ V)
    (fun _ _ ↦ contDiff_ofReal_smul_id _)
    fun α hα ↦ (length_multiIndexWord α).trans_le (sum_le_of_mem_multiIndices hα)

variable (D : differentialOperators ℝ C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯
  C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯
  C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯ m)

/-- The full symbol of a differential operator `D f = ∑_{|α| ≤ m} c_α ∂^α f` is
`σ_D(x, ξ) = ∑_{|α| ≤ m} c_α(x) (i ξ)^α`, acting on `V` by scalar multiplication. -/
@[simp]
theorem coefficient_toSymbol_ofDifferentialOperator (p : CoordinateSpace n × CoordinateSpace n) :
    (ofDifferentialOperator (V := V) D).toSymbol.coefficient p =
      ∑ k ∈ range (m + 1), ∑ α ∈ piAntidiag univ k,
        (Complex.I ^ k * (∏ j, (p.2 j : ℂ) ^ α j) *
          coordinateCoeff (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.smoothCoord
            (D : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯ →ₗ[ℝ]
              C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯) α p.1) •
          ContinuousLinearMap.id ℂ V := by
  rw [ofDifferentialOperator, coefficient_toSymbol_ofDifferentialSymbol, differentialSymbol_def,
    sum_multiIndices]
  refine sum_congr rfl fun k _ ↦ sum_congr rfl fun α hα ↦ ?_
  rw [prod_inner_multiIndexWord (mem_piAntidiag.1 hα).1, smul_smul]

/-- **Differential operators are pseudodifferential operators.** On Schwartz input the
quantization of the symbol of a differential operator `D` on `C^∞(ℝⁿ)` is `D` itself, with no
smoothing remainder: for every real-linear functional `ℓ` on `V`,
`ℓ (Op(σ_D) u (x)) = D (ℓ ∘ u) (x)`. -/
theorem apply_quantizeSchwartzValue_ofDifferentialOperator [CompleteSpace V] (ℓ : V →L[ℝ] ℝ)
    (u : 𝓢(CoordinateSpace n, V)) {f : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯}
    (hf : ∀ y, f y = ℓ (u y)) (x : CoordinateSpace n) :
    ℓ (quantizeSchwartzValue (ofDifferentialOperator (V := V) D).toSymbol.coefficient u x) =
      (D : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯ →ₗ[ℝ]
        C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯) f x := by
  have hf' : ⇑f = ℓ ∘ u := funext hf
  rw [(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.eq_coordinateOperator_coordinateCoeff D.2,
    ofDifferentialOperator, quantizeSchwartzValue_ofDifferentialSymbol, map_sum, sum_multiIndices,
    coordinateOperator_apply]
  simp only [ContMDiffMap.coe_sum, Finset.sum_apply]
  refine sum_congr rfl fun k _ ↦ sum_congr rfl fun α _ ↦ ?_
  rw [smul_apply, ContinuousLinearMap.id_apply, Complex.coe_smul, map_smul, smul_eq_mul,
    smul_eq_mul, ContMDiffMap.coe_mul, Pi.mul_apply, mul_comm,
    SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
    ← coordinateDeriv_eq_iteratedFDeriv _ (u.smooth _),
    ← ℓ.coordinateDeriv_comp_left _ (u.smooth _), ← hf']
  have h := coe_multiIndexDeriv_count (multiIndexWord α) f
  rw [funext (count_multiIndexWord α)] at h
  rw [h]

/-- On complex-valued Schwartz input, the quantization of the symbol of a differential operator
`D` on `C^∞(ℝⁿ)` is the complexification `u ↦ D (Re u) + i D (Im u)` of `D`. -/
theorem quantizeSchwartzValue_ofDifferentialOperator (u : 𝓢(CoordinateSpace n, ℂ))
    {f g : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯} (hf : ∀ y, f y = (u y).re)
    (hg : ∀ y, g y = (u y).im) (x : CoordinateSpace n) :
    quantizeSchwartzValue (ofDifferentialOperator (V := ℂ) D).toSymbol.coefficient u x =
      (D : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯ →ₗ[ℝ]
        C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯) f x +
      (D : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯ →ₗ[ℝ]
        C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯) g x * Complex.I := by
  apply Complex.ext
  · simpa using apply_quantizeSchwartzValue_ofDifferentialOperator D Complex.reCLM u hf x
  · simpa using apply_quantizeSchwartzValue_ofDifferentialOperator D Complex.imCLM u hg x

/-- **The principal symbol of a differential operator.** Away from `ξ = 0`, the principal symbol
of the classical symbol of a differential operator `D` of order at most `m` is `i ^ m` times the
principal symbol `TauCeti.smoothPrincipalSymbol` of `D`, defined by iterated commutators, at the
covector `⟪ξ, ·⟫`: the angular-frequency convention `σ(∂ⱼ) = i ξⱼ`. -/
theorem coefficient_principal_ofDifferentialOperator (x : CoordinateSpace n)
    {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    (ofDifferentialOperator (V := V) D).principal.coefficient (x, ξ) =
      (Complex.I ^ m * smoothPrincipalSymbol 𝓘(ℝ, CoordinateSpace n) (x := x)
        BoundarylessManifold.isInteriorPoint D (innerSL ℝ ξ) : ℂ) • ContinuousLinearMap.id ℂ V := by
  have h : smoothPrincipalSymbol 𝓘(ℝ, CoordinateSpace n) (x := x)
      BoundarylessManifold.isInteriorPoint D (innerSL ℝ ξ) =
        ∑ α ∈ piAntidiag univ m,
          coordinateCoeff (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.smoothCoord
            (D : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯ →ₗ[ℝ]
              C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯) α x *
            ∏ j, ξ j ^ α j := by
    refine ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.smoothPrincipalSymbol_eq_sum_coordinateCoeff
      _ D (innerSL ℝ ξ)).trans ?_
    refine sum_congr rfl fun α _ ↦ congrArg _ (prod_congr rfl fun j _ ↦ ?_)
    -- The covector `⟪ξ, ·⟫` is typed on the tangent space, so evaluate it in a separate step.
    have hj : innerSL ℝ ξ ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis j) = ξ j := by
      simp [EuclideanSpace.inner_single_right]
    exact congrArg (· ^ α j) hj
  rw [h, ofDifferentialOperator, coefficient_principal_ofDifferentialSymbol _ _ _ _ _ _ hξ,
    filter_multiIndices, differentialSymbol_def, Complex.ofReal_sum, mul_sum, sum_smul]
  refine sum_congr rfl fun α hα ↦ ?_
  rw [prod_inner_multiIndexWord (mem_piAntidiag.1 hα).1, smul_smul]
  push_cast
  ring_nf

/-- A differential operator `D` on `C^∞(ℝⁿ)` is elliptic, as a classical pseudodifferential
operator on functions with values in a nonzero space, exactly when its principal symbol vanishes at
no nonzero covector. -/
theorem isElliptic_ofDifferentialOperator_iff [Nontrivial V] :
    (ofDifferentialOperator (V := V) D).IsElliptic ↔
      ∀ x ξ : CoordinateSpace n, ξ ≠ 0 → smoothPrincipalSymbol 𝓘(ℝ, CoordinateSpace n)
        (x := x) BoundarylessManifold.isInteriorPoint D (innerSL ℝ ξ) ≠ 0 := by
  rw [isElliptic_iff]
  refine forall_congr' fun x ↦ forall_congr' fun ξ ↦ forall_congr' fun hξ ↦ ?_
  rw [coefficient_principal_ofDifferentialOperator D x hξ]
  constructor
  · intro h h0
    rw [h0, Complex.ofReal_zero, mul_zero, zero_smul] at h
    exact not_subsingleton V (ContinuousLinearMap.isInvertible_zero_iff.1 h).1
  · intro h
    rw [ContinuousLinearMap.isInvertible_smul_iff (by simp [h])]
    exact ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℂ V)

end ClassicalSymbol

end TauCeti
