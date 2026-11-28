/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.RingTheory.MvPolynomial.DeterminantalIdeal
public import TauCeti.Algebra.Lie.GeneralLinear.KHighest
public import TauCeti.Algebra.Lie.GeneralLinear.Oscillator.DualPair
import TauCeti.Algebra.MvPolynomial.Supported
import TauCeti.RingTheory.MvPolynomial.DeterminantalIdeal
import TauCeti.RingTheory.MvPolynomial.MinorPolarization

/-!
# `K`-highest and termwise harmonic polynomials on the Fock module

On the Fock module `MvPolynomial (I × I') K` of the dual pair `(U(p, q), U(r, s))` of
`TauCeti/Algebra/Lie/GeneralLinear/Oscillator/DualPair.lean`, with signs `ε` on the rows `I` and
`ε'` on the columns `I'`, this file sets up the two conditions on a polynomial that the joint
harmonics of the theta correspondence are made of, and the tools to produce polynomials
satisfying them as products of minors of the matrix of variables.

A polynomial `P` is **termwise harmonic for the rows** (`TauCeti.IsRowTermwiseHarmonic`) if
`∂² P / ∂ z a c ∂ z b c = 0` for every column `c` and all rows `a`, `b` of opposite signs, and
**termwise harmonic for the columns** (`TauCeti.IsColTermwiseHarmonic`) in the symmetric sense.
Each term of the Laplacian `TauCeti.fockRowLower a b` of the noncompact matrix unit `E a b` is such
a second derivative, so a polynomial termwise harmonic for the rows is killed by these Laplacians
(`TauCeti.IsRowTermwiseHarmonic.fockRowLower_eq_zero`). A polynomial in variables no two of which
lie in one column and in rows of opposite signs is termwise harmonic for the rows
(`TauCeti.isRowTermwiseHarmonic_of_mem_supported`).

The compact matrix units `E a b`, `ε a = ε b`, of the rows act on the Fock module by a derivation
plus the scalar by which they act on the vacuum `1`
(`TauCeti.fockRowHom_single_mul`). So weights relative to the vacuum add under products: if `P`
and `Q` are `K`-highest (`TauCeti.IsKHighest`) of weights `ν₀ + μ` and `ν₀ + μ'`, where `ν₀` is
the weight of the vacuum (`TauCeti.isKHighest_fockRowHom_one`), then `P * Q` is `K`-highest of
weight `ν₀ + μ + μ'` (`TauCeti.isKHighest_fockRowHom_mul`, with powers and finite products).

A minor `Matrix.mvPolynomialMinor K r c` of the matrix of variables on rows `r` and columns `c`
whose variables are all even (`TauCeti.IsEvenPair`) is `K`-highest for the rows in the order of
`l` when its rows contain `a` whenever they contain `b`, for every compact raising operator
`E a b`; its weight is that of the vacuum plus one on its rows
(`TauCeti.isKHighest_fockRowHom_mvPolynomialMinor_of_isEvenPair`). For odd variables the rows
must contain `b` whenever they contain `a`, and the weight drops by one on the rows
(`TauCeti.isKHighest_fockRowHom_mvPolynomialMinor_of_not_isEvenPair`). Exchanging the two
members of the pair (`TauCeti.isKHighest_fockColHom_iff`) gives the same for the columns.

## Main definitions

* `TauCeti.IsRowTermwiseHarmonic ε P`, `TauCeti.IsColTermwiseHarmonic ε' P`: termwise harmonic
  polynomials for the rows and for the columns.

## Main results

* `TauCeti.IsRowTermwiseHarmonic.fockRowLower_eq_zero`,
  `TauCeti.IsColTermwiseHarmonic.fockColLower_eq_zero`: termwise harmonic polynomials are killed
  by the Laplacians.
* `TauCeti.isRowTermwiseHarmonic_of_mem_supported`,
  `TauCeti.isColTermwiseHarmonic_of_mem_supported`: a criterion by the variables.
* `TauCeti.fockRowHom_single_mul`, `TauCeti.fockColHom_single_mul`: the Leibniz rule for the
  compact matrix units.
* `TauCeti.isKHighest_fockRowHom_one`, `TauCeti.isKHighest_fockColHom_one`: the vacuum is
  `K`-highest.
* `TauCeti.isKHighest_fockColHom_iff`: exchanging the members of the pair.
* `TauCeti.isKHighest_fockRowHom_mul`, `TauCeti.isKHighest_fockRowHom_pow`,
  `TauCeti.isKHighest_fockRowHom_prod`: the weights add under products.
* `TauCeti.isKHighest_fockRowHom_mvPolynomialMinor_of_isEvenPair`,
  `TauCeti.isKHighest_fockRowHom_mvPolynomialMinor_of_not_isEvenPair`: minors of the matrix of
  variables.

## References

* R. Howe, *Transcending classical invariant theory*, J. Amer. Math. Soc. 2 (1989), 535--552.
* M. Kashiwara and M. Vergne, *On the Segal–Shale–Weil representations and harmonic
  polynomials*, Invent. Math. 44 (1978), 1--47.
* The termwise harmonic polynomials correspond to `New.FockDualPair.IsTermwiseHarmonic` in
  `src/Lib/DiscreteSeries/Theta/FockDualPair.lean` of grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti

open MvPolynomial Finset Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {I I' : Type*}

/-! ### Termwise harmonic polynomials -/

section Harmonic

variable {K : Type*} [CommSemiring K]

/-- A polynomial `P` on `I × I'` is **termwise harmonic for the rows**, with the signs `ε` on the
rows, if `∂² P / ∂ z a c ∂ z b c = 0` for every column `c` and all rows `a`, `b` of opposite signs.
In characteristic zero this says that no monomial of `P` contains two variables of one column from
rows of opposite signs. -/
def IsRowTermwiseHarmonic (ε : I → Bool) (P : MvPolynomial (I × I') K) : Prop :=
  ∀ a b, ε a ≠ ε b → ∀ c, pderiv (a, c) (pderiv (b, c) P) = 0

/-- A polynomial `P` on `I × I'` is **termwise harmonic for the columns**, with the signs `ε'` on
the columns, if `∂² P / ∂ z a c ∂ z a d = 0` for every row `a` and all columns `c`, `d` of opposite
signs. -/
def IsColTermwiseHarmonic (ε' : I' → Bool) (P : MvPolynomial (I × I') K) : Prop :=
  ∀ c d, ε' c ≠ ε' d → ∀ a, pderiv (a, c) (pderiv (a, d) P) = 0

/-- `TauCeti.IsRowTermwiseHarmonic` unfolded. -/
theorem isRowTermwiseHarmonic_iff {ε : I → Bool} {P : MvPolynomial (I × I') K} :
    IsRowTermwiseHarmonic ε P ↔ ∀ a b, ε a ≠ ε b → ∀ c, pderiv (a, c) (pderiv (b, c) P) = 0 :=
  Iff.rfl

/-- `TauCeti.IsColTermwiseHarmonic` unfolded. -/
theorem isColTermwiseHarmonic_iff {ε' : I' → Bool} {P : MvPolynomial (I × I') K} :
    IsColTermwiseHarmonic ε' P ↔ ∀ c d, ε' c ≠ ε' d → ∀ a, pderiv (a, c) (pderiv (a, d) P) = 0 :=
  Iff.rfl

/-- For rows of a single sign, every polynomial is termwise harmonic for the rows. -/
@[simp]
theorem isRowTermwiseHarmonic_const (e : Bool) (P : MvPolynomial (I × I') K) :
    IsRowTermwiseHarmonic (fun _ : I ↦ e) P :=
  fun _ _ h ↦ absurd rfl h

/-- For columns of a single sign, every polynomial is termwise harmonic for the columns. -/
@[simp]
theorem isColTermwiseHarmonic_const (e : Bool) (P : MvPolynomial (I × I') K) :
    IsColTermwiseHarmonic (fun _ : I' ↦ e) P :=
  fun _ _ h ↦ absurd rfl h

/-- **A criterion for termwise harmonicity for the rows.** A polynomial in the variables `V` is
termwise harmonic for the rows if no two variables of `V` lie in one column and in rows of
opposite signs. -/
theorem isRowTermwiseHarmonic_of_mem_supported {ε : I → Bool} {V : Set (I × I')}
    (hV : ∀ a b c, (a, c) ∈ V → (b, c) ∈ V → ε a = ε b) {P : MvPolynomial (I × I') K}
    (hP : P ∈ supported K V) : IsRowTermwiseHarmonic ε P := fun a b hab c ↦ by
  by_cases hb : (b, c) ∈ V
  · exact pderiv_eq_zero_of_mem_supported (pderiv_mem_supported hP _) fun ha ↦ hab (hV a b c ha hb)
  · rw [pderiv_eq_zero_of_mem_supported hP hb, map_zero]

/-- **A criterion for termwise harmonicity for the columns.** A polynomial in the variables `V`
is termwise harmonic for the columns if no two variables of `V` lie in one row and in columns of
opposite signs. -/
theorem isColTermwiseHarmonic_of_mem_supported {ε' : I' → Bool} {V : Set (I × I')}
    (hV : ∀ a c d, (a, c) ∈ V → (a, d) ∈ V → ε' c = ε' d) {P : MvPolynomial (I × I') K}
    (hP : P ∈ supported K V) : IsColTermwiseHarmonic ε' P := fun c d hcd a ↦ by
  by_cases hd : (a, d) ∈ V
  · exact pderiv_eq_zero_of_mem_supported (pderiv_mem_supported hP _) fun hc ↦ hcd (hV a c d hc hd)
  · rw [pderiv_eq_zero_of_mem_supported hP hd, map_zero]

end Harmonic

section Laplacian

variable {K : Type*} [CommRing K]

/-- **The Laplacians of the rows kill a polynomial termwise harmonic for the rows.** -/
theorem IsRowTermwiseHarmonic.fockRowLower_eq_zero [Fintype I'] {ε : I → Bool} (ε' : I' → Bool)
    {P : MvPolynomial (I × I') K} (h : IsRowTermwiseHarmonic ε P) {a b : I} (hab : ε a ≠ ε b) :
    fockRowLower K ε ε' a b P = 0 := by
  rw [fockRowLower_apply]
  exact sum_eq_zero fun c _ ↦ h a b hab c

/-- **The Laplacians of the columns kill a polynomial termwise harmonic for the columns.** -/
theorem IsColTermwiseHarmonic.fockColLower_eq_zero [Fintype I] (ε : I → Bool) {ε' : I' → Bool}
    {P : MvPolynomial (I × I') K} (h : IsColTermwiseHarmonic ε' P) {c d : I'}
    (hcd : ε' c ≠ ε' d) : fockColLower K ε ε' c d P = 0 := by
  rw [fockColLower_apply]
  exact sum_eq_zero fun a _ ↦ h c d hcd a

end Laplacian

/-! ### The compact matrix units act by derivations -/

section Leibniz

variable (K : Type*) [Field K] [Fintype I'] (ε : I → Bool) (ε' : I' → Bool)

/-- The derivation by which the matrix unit `E a b` of the rows acts on the Fock module, for
`ε a = ε b`, up to its scalar on the vacuum: `z a c ∂ / ∂ z b c` on the even columns `c` and
`-z b c ∂ / ∂ z a c` on the odd ones. -/
private noncomputable def fockRowDerivation (a b : I) :
    Derivation K (MvPolynomial (I × I') K) (MvPolynomial (I × I') K) :=
  ∑ c, if IsEvenPair ε ε' (a, c) then polynomialOperator K (a, c) (b, c)
    else -polynomialOperator K (b, c) (a, c)

variable {K ε ε'}

private theorem fockRowDerivation_apply (a b : I) (P : MvPolynomial (I × I') K) :
    fockRowDerivation K ε ε' a b P = ∑ c, if IsEvenPair ε ε' (a, c)
      then polynomialOperator K (a, c) (b, c) P else -polynomialOperator K (b, c) (a, c) P := by
  rw [fockRowDerivation, _root_.sum_apply]
  refine sum_congr rfl fun c _ ↦ ?_
  split_ifs
  · rfl
  · exact _root_.neg_apply _ P

variable {m : Type*} [Fintype m] [DecidableEq m] {r : m → I} {c : m → I'}

omit [Fintype I'] in
/-- A polarization operator differentiating along a variable `y` that is not a variable of the
minor on the rows `r` and the columns `c` kills the minor. -/
private theorem polynomialOperator_minor_eq_zero (x : I × I') {y : I × I'}
    (hy : y ∉ Set.range r ×ˢ Set.range c) :
    polynomialOperator K x y (mvPolynomialMinor K r c) = 0 := by
  rw [polynomialOperator_apply,
    pderiv_eq_zero_of_mem_supported (mvPolynomialMinor_mem_supported r c) hy, mul_zero]

omit [Fintype I'] in
/-- Let the variables of the minor on the rows `r` and the columns `c` all have the parity `p`,
and let `ε a = ε b`. Along a column `v` where the variable `z a v` has the other parity, neither
`z a v` nor `z b v` is a variable of the minor, so the polarization operators between the rows
`a` and `b` along `v` kill the minor. -/
private theorem polynomialOperator_minor_eq_zero_of_not_iff {p : Prop}
    (hp : ∀ i j, IsEvenPair ε ε' (r i, c j) ↔ p) {a b : I} (hab : ε a = ε b) {v : I'}
    (hv : ¬(IsEvenPair ε ε' (a, v) ↔ p)) :
    polynomialOperator K (a, v) (b, v) (mvPolynomialMinor K r c) = 0 ∧
      polynomialOperator K (b, v) (a, v) (mvPolynomialMinor K r c) = 0 := by
  have h (x : I) (hx : ε x = ε a) : (x, v) ∉ Set.range r ×ˢ Set.range c := by
    rintro ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
    exact hv ((isEvenPair_iff_of_eq hx.symm _).trans (hp i j))
  exact ⟨polynomialOperator_minor_eq_zero _ (h b hab.symm),
    polynomialOperator_minor_eq_zero _ (h a rfl)⟩

/-- The polarization operator from a row `y` of the minor on the rows `r` to a row `x`, with `x`
a row of the minor whenever `y` is, kills the minor when `x ≠ y`. -/
private theorem sum_polynomialOperator_minor_eq_zero {x y : I} (hxy : x ≠ y)
    (h : y ∈ Set.range r → x ∈ Set.range r) :
    ∑ v, polynomialOperator K (x, v) (y, v) (mvPolynomialMinor K r c) = 0 := by
  by_cases hy : y ∈ Set.range r
  · obtain ⟨j, rfl⟩ := hy
    obtain ⟨i, rfl⟩ := h ⟨j, rfl⟩
    rw [sum_polynomialOperator_mvPolynomialMinor r c i j, ite_eq_right_iff]
    exact fun h ↦ absurd (congrArg r h) hxy
  · exact sum_eq_zero fun v _ ↦ polynomialOperator_minor_eq_zero _ fun h ↦ hy h.1

/-- The Euler operator of a row `x` multiplies the minor on the rows `r` by one if `x` is a row of
the minor, and kills it otherwise. -/
private theorem sum_polynomialOperator_minor_self (x : I) :
    ∑ v, polynomialOperator K (x, v) (x, v) (mvPolynomialMinor K r c) =
      (Set.range r).indicator (1 : I → K) x • mvPolynomialMinor K r c := by
  by_cases hx : x ∈ Set.range r
  · obtain ⟨i, rfl⟩ := hx
    simp [sum_polynomialOperator_mvPolynomialMinor r c i i]
  · rw [Set.indicator_of_notMem hx, zero_smul]
    exact sum_eq_zero fun v _ ↦ polynomialOperator_minor_eq_zero _ fun h ↦ hx h.1

/-- On a minor whose variables are all even, the derivation of a compact matrix unit `E a b` of
the rows is the polarization operator from the row `b` to the row `a`. -/
private theorem fockRowDerivation_minor_of_isEvenPair
    (heven : ∀ i j, IsEvenPair ε ε' (r i, c j)) {a b : I} (hab : ε a = ε b) :
    fockRowDerivation K ε ε' a b (mvPolynomialMinor K r c) =
      ∑ v, polynomialOperator K (a, v) (b, v) (mvPolynomialMinor K r c) := by
  rw [fockRowDerivation_apply]
  refine sum_congr rfl fun v _ ↦ ?_
  split_ifs with hv
  · rfl
  -- The variable `z a v` is odd, unlike the variables of the minor.
  obtain ⟨h₁, h₂⟩ := polynomialOperator_minor_eq_zero_of_not_iff (K := K)
    (fun i j ↦ iff_true_intro (heven i j)) hab (by rwa [iff_true])
  rw [h₁, h₂, neg_zero]

/-- On a minor whose variables are all odd, the derivation of a compact matrix unit `E a b` of
the rows is minus the polarization operator from the row `a` to the row `b`. -/
private theorem fockRowDerivation_minor_of_not_isEvenPair
    (hodd : ∀ i j, ¬IsEvenPair ε ε' (r i, c j)) {a b : I} (hab : ε a = ε b) :
    fockRowDerivation K ε ε' a b (mvPolynomialMinor K r c) =
      -∑ v, polynomialOperator K (b, v) (a, v) (mvPolynomialMinor K r c) := by
  rw [fockRowDerivation_apply, ← sum_neg_distrib]
  refine sum_congr rfl fun v _ ↦ ?_
  split_ifs with hv
  · -- The variable `z a v` is even, unlike the variables of the minor.
    obtain ⟨h₁, h₂⟩ := polynomialOperator_minor_eq_zero_of_not_iff (K := K)
      (fun i j ↦ iff_false_intro (hodd i j)) hab (by rwa [iff_false, not_not])
    rw [h₁, h₂, neg_zero]
  · rfl

variable [Fintype I] [DecidableEq I] [DecidableEq I']

/-- A compact matrix unit `E a b` of the rows acts on the Fock module by a derivation plus its
scalar on the vacuum. -/
private theorem fockRowHom_single_apply_eq {a b : I} (hab : ε a = ε b)
    (P : MvPolynomial (I × I') K) :
    fockRowHom K ε ε' (single a b 1) P =
      fockRowDerivation K ε ε' a b P + P * fockRowHom K ε ε' (single a b 1) 1 := by
  rw [fockRowHom_single, fockRowDerivation_apply]
  simp only [LinearMap.add_apply, LinearMap.sum_apply, mul_add, mul_sum, ← add_assoc,
    ← sum_add_distrib]
  congr 1
  · refine sum_congr rfl fun c _ ↦ ?_
    by_cases hc : IsEvenPair ε ε' (a, c)
    · have hc' : IsEvenPair ε ε' (b, c) := (isEvenPair_iff_of_eq hab c).1 hc
      simp [hc, hc', polynomialOperator_apply]
    · have hc' : ¬IsEvenPair ε ε' (b, c) := (isEvenPair_iff_of_eq hab c).not.1 hc
      by_cases hab' : a = b
      · subst hab'
        simp only [mul_apply_eq_comp, hc, not_false_eq_true, oscLower_apply_of_neg,
          oscRaise_apply_of_neg, Derivation.leibniz, smul_eq_mul, pderiv_X, Pi.single_eq_same,
          mul_one, neg_add_rev, ↓reduceIte, polynomialOperator_apply, mul_neg]
        ring
      · simp [hc, hc', Ne.symm hab', polynomialOperator_apply]
  · split_ifs <;> simp

/-- **The compact matrix units of the rows act by derivations, up to the vacuum.** For
`ε a = ε b`, the matrix unit `E a b` acts on products by
`E (P * Q) = E P * Q + P * E Q - P * Q * E 1`. -/
theorem fockRowHom_single_mul {a b : I} (hab : ε a = ε b) (P Q : MvPolynomial (I × I') K) :
    fockRowHom K ε ε' (single a b 1) (P * Q) =
      fockRowHom K ε ε' (single a b 1) P * Q + P * fockRowHom K ε ε' (single a b 1) Q -
        P * Q * fockRowHom K ε ε' (single a b 1) 1 := by
  rw [fockRowHom_single_apply_eq hab (P * Q), fockRowHom_single_apply_eq hab P,
    fockRowHom_single_apply_eq hab Q, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  ring

/-- **The compact matrix units of the columns act by derivations, up to the vacuum.** For
`ε' c = ε' d`, the matrix unit `E c d` acts on products by
`E (P * Q) = E P * Q + P * E Q - P * Q * E 1`. -/
theorem fockColHom_single_mul {c d : I'} (hcd : ε' c = ε' d) (P Q : MvPolynomial (I × I') K) :
    fockColHom K ε ε' (single c d 1) (P * Q) =
      fockColHom K ε ε' (single c d 1) P * Q + P * fockColHom K ε ε' (single c d 1) Q -
        P * Q * fockColHom K ε ε' (single c d 1) 1 := by
  apply rename_injective _ Prod.swap_injective
  simp only [map_sub, map_add, map_mul, rename_swap_fockColHom, map_one]
  exact fockRowHom_single_mul hcd _ _

end Leibniz

/-! ### `K`-highest polynomials -/

section KHighest

variable {K : Type*} [Field K] [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
  {ε : I → Bool} {ε' : I' → Bool} {α : Type*}

section LT

variable [LT α]

/-- **Exchanging the two members of the pair.** A polynomial is `K`-highest for the columns of
the pair `(ε, ε')` exactly when its transpose, renaming `z a c` as `z c a`, is `K`-highest for the
rows of the pair `(ε', ε)`. -/
theorem isKHighest_fockColHom_iff {l : I' → α} {ν : I' → K} {P : MvPolynomial (I × I') K} :
    IsKHighest (fockColHom K ε ε') ε' l ν P ↔
      IsKHighest (fockRowHom K ε' ε) ε' l ν (rename Prod.swap P) := by
  have h_inj := rename_injective (R := K) _ (Prod.swap_injective (α := I) (β := I'))
  simp only [isKHighest_iff, ← rename_swap_fockColHom, ← map_smul, h_inj.eq_iff,
    map_eq_zero_iff _ h_inj]

variable {l : I → α} {ν₀ : I → K}

/-- **Weights relative to the vacuum add under products.** If the vacuum is `K`-highest of weight
`ν₀`, and `P`, `Q` are `K`-highest for the rows of weights `ν₀ + μ` and `ν₀ + μ'`, then `P * Q` is
`K`-highest of weight `ν₀ + (μ + μ')`. -/
theorem isKHighest_fockRowHom_mul (h₁ : IsKHighest (fockRowHom K ε ε') ε l ν₀ 1)
    {μ μ' : I → K} {P Q : MvPolynomial (I × I') K}
    (hP : IsKHighest (fockRowHom K ε ε') ε l (ν₀ + μ) P)
    (hQ : IsKHighest (fockRowHom K ε ε') ε l (ν₀ + μ') Q) :
    IsKHighest (fockRowHom K ε ε') ε l (ν₀ + (μ + μ')) (P * Q) := by
  refine isKHighest_iff.2 ⟨fun a ↦ ?_, fun a b hab hl ↦ ?_⟩
  · rw [fockRowHom_single_mul rfl, hP.map_single_self_apply, hQ.map_single_self_apply,
      h₁.map_single_self_apply]
    simp only [Pi.add_apply, smul_eq_C_mul, map_add, mul_one]
    ring
  · rw [fockRowHom_single_mul hab, hP.map_single_apply_eq_zero hab hl,
      hQ.map_single_apply_eq_zero hab hl, h₁.map_single_apply_eq_zero hab hl]
    ring

/-- **Weights relative to the vacuum multiply under powers.** If the vacuum is `K`-highest of
weight `ν₀` and `P` is `K`-highest for the rows of weight `ν₀ + μ`, then `P ^ k` is `K`-highest
of weight `ν₀ + k • μ`. -/
theorem isKHighest_fockRowHom_pow (h₁ : IsKHighest (fockRowHom K ε ε') ε l ν₀ 1) {μ : I → K}
    {P : MvPolynomial (I × I') K} (hP : IsKHighest (fockRowHom K ε ε') ε l (ν₀ + μ) P) (k : ℕ) :
    IsKHighest (fockRowHom K ε ε') ε l (ν₀ + k • μ) (P ^ k) := by
  induction k with
  | zero => simpa using h₁
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact isKHighest_fockRowHom_mul h₁ ih hP

/-- **Weights relative to the vacuum add under finite products.** If the vacuum is `K`-highest of
weight `ν₀` and each `P i` is `K`-highest for the rows of weight `ν₀ + μ i`, then `∏ i ∈ s, P i`
is `K`-highest of weight `ν₀ + ∑ i ∈ s, μ i`. -/
theorem isKHighest_fockRowHom_prod (h₁ : IsKHighest (fockRowHom K ε ε') ε l ν₀ 1)
    {ι : Type*} (s : Finset ι) {μ : ι → I → K} {P : ι → MvPolynomial (I × I') K}
    (hP : ∀ i ∈ s, IsKHighest (fockRowHom K ε ε') ε l (ν₀ + μ i) (P i)) :
    IsKHighest (fockRowHom K ε ε') ε l (ν₀ + ∑ i ∈ s, μ i) (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h₁
  | insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi]
    exact isKHighest_fockRowHom_mul h₁ (hP i (mem_insert_self i s))
      (ih fun j hj ↦ hP j (mem_insert_of_mem hj))

end LT

variable [Preorder α]

variable (ε ε') in
/-- **The vacuum is `K`-highest for the rows**, for every order. Its weight at the row `a` is half
the number of columns of the sign of `a` minus half the number of the others. -/
theorem isKHighest_fockRowHom_one [NeZero (2 : K)] (l : I → α) :
    IsKHighest (fockRowHom K ε ε') ε l
      (fun a ↦ ((#{c | ε a = ε' c} : K) - #{c | ε a ≠ ε' c}) / 2) 1 :=
  isKHighest_iff.2 ⟨fockRowHom_single_self_one, fun _ _ hab hl ↦
    fockRowHom_single_one_of_ne (fun h ↦ hl.ne' (congrArg l h)) hab⟩

variable (ε ε') in
/-- **The vacuum is `K`-highest for the columns**, for every order. Its weight at the column `c`
is half the number of rows of the sign of `c` minus half the number of the others. -/
theorem isKHighest_fockColHom_one [NeZero (2 : K)] (l : I' → α) :
    IsKHighest (fockColHom K ε ε') ε' l
      (fun c ↦ ((#{a | ε a = ε' c} : K) - #{a | ε a ≠ ε' c}) / 2) 1 :=
  isKHighest_iff.2 ⟨fockColHom_single_self_one, fun _ _ hcd hl ↦
    fockColHom_single_one_of_ne (fun h ↦ hl.ne' (congrArg l h)) hcd⟩

variable {l : I → α} {ν₀ : I → K} {m : Type*} [Fintype m] [DecidableEq m] {r : m → I}
  {c : m → I'}

/-- **Minors of even variables are `K`-highest for the rows.** Let the vacuum be `K`-highest of
weight `ν₀`, and consider the minor of the matrix of variables on the rows `r` and the columns `c`
whose variables are all even. If its rows contain `a` whenever they contain `b`, for all `a`, `b`
of one sign with `l b < l a`, then it is `K`-highest for the rows in the order of `l`, of the
weight of the vacuum plus one on its rows. -/
theorem isKHighest_fockRowHom_mvPolynomialMinor_of_isEvenPair
    (h₁ : IsKHighest (fockRowHom K ε ε') ε l ν₀ 1) (heven : ∀ i j, IsEvenPair ε ε' (r i, c j))
    (hl : ∀ a b, ε a = ε b → l b < l a → b ∈ Set.range r → a ∈ Set.range r) :
    IsKHighest (fockRowHom K ε ε') ε l (ν₀ + (Set.range r).indicator 1)
      (mvPolynomialMinor K r c) := by
  refine isKHighest_iff.2 ⟨fun a ↦ ?_, fun a b hab hlt ↦ ?_⟩
  · rw [fockRowHom_single_apply_eq rfl, h₁.map_single_self_apply,
      fockRowDerivation_minor_of_isEvenPair heven rfl, sum_polynomialOperator_minor_self,
      Pi.add_apply, add_smul, add_comm, mul_smul_comm, mul_one]
  · rw [fockRowHom_single_apply_eq hab, h₁.map_single_apply_eq_zero hab hlt,
      fockRowDerivation_minor_of_isEvenPair heven hab,
      sum_polynomialOperator_minor_eq_zero (fun h ↦ hlt.ne' (congrArg l h)) (hl a b hab hlt),
      mul_zero, add_zero]

/-- **Minors of odd variables are `K`-highest for the rows.** Let the vacuum be `K`-highest of
weight `ν₀`, and consider the minor of the matrix of variables on the rows `r` and the columns `c`
whose variables are all odd. If its rows contain `b` whenever they contain `a`, for all `a`, `b`
of one sign with `l b < l a`, then it is `K`-highest for the rows in the order of `l`, of the
weight of the vacuum minus one on its rows. -/
theorem isKHighest_fockRowHom_mvPolynomialMinor_of_not_isEvenPair
    (h₁ : IsKHighest (fockRowHom K ε ε') ε l ν₀ 1) (hodd : ∀ i j, ¬IsEvenPair ε ε' (r i, c j))
    (hl : ∀ a b, ε a = ε b → l b < l a → a ∈ Set.range r → b ∈ Set.range r) :
    IsKHighest (fockRowHom K ε ε') ε l (ν₀ - (Set.range r).indicator 1)
      (mvPolynomialMinor K r c) := by
  refine isKHighest_iff.2 ⟨fun a ↦ ?_, fun a b hab hlt ↦ ?_⟩
  · rw [fockRowHom_single_apply_eq rfl, h₁.map_single_self_apply,
      fockRowDerivation_minor_of_not_isEvenPair hodd rfl, sum_polynomialOperator_minor_self,
      Pi.sub_apply, sub_smul, mul_smul_comm, mul_one, neg_add_eq_sub]
  · rw [fockRowHom_single_apply_eq hab, h₁.map_single_apply_eq_zero hab hlt,
      fockRowDerivation_minor_of_not_isEvenPair hodd hab,
      sum_polynomialOperator_minor_eq_zero (fun h ↦ hlt.ne' (congrArg l h.symm)) (hl a b hab hlt),
      neg_zero, mul_zero, add_zero]

end KHighest

end TauCeti
