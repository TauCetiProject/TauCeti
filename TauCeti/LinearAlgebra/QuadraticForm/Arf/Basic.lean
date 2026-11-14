/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Pi
public import TauCeti.LinearAlgebra.QuadraticForm.Arf.Symplectic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.FinCases
import TauCeti.LinearAlgebra.QuadraticForm.Representation

/-!
# The Arf invariant and classification of nonsingular quadratic forms over `𝔽₂`

Over `ZMod 2`, the **Arf invariant** `Q.arf : ZMod 2` of a quadratic form `Q` with nondegenerate
polar form on a finite-dimensional space is the quantity `∑ i, Q (b (.inl i)) * Q (b (.inr i))`
computed in any symplectic basis `b`. Basis independence follows from the integer **Gauss sum**
`Q.gaussSum = ∑ v : V, (-1 : ℤ) ^ (Q v).val`: in symplectic coordinates
(`QuadraticMap.isometryEquivPiBinarySymplectic`) `Q` splits as an orthogonal product of binary forms
`TauCeti.binarySymplectic (ZMod 2) a c` (`x ↦ a x₀² + x₀ x₁ + c x₁²`), each contributing
`(-1) ^ (a * c).val * 2`, so `Q.gaussSum = (-1) ^ Q.arf.val * 2 ^ m`. Since `2 ^ m > 0` in `ℤ`, the
Gauss sum determines `Q.arf` intrinsically, yielding basis independence, isometry invariance,
additivity under orthogonal products and internal orthogonal direct sums, and the exact count of
`Q`-isotropic vectors (`2 ^ (2 * m - 1) + (-1) ^ Q.arf.val * 2 ^ (m - 1)` when `m ≥ 1`, and `1`
when `m = 0`).

Combining plane diagonalization (`TauCeti.isometryEquivBinarySymplecticDiag`) with the four-variable
isometry between two anisotropic planes and two hyperbolic planes
(`TauCeti.isometryEquivProjProdBinarySymplecticOneOne`), every nonsingular quadratic space over
`ZMod 2` decomposes into hyperbolic planes and at most one anisotropic plane
(`QuadraticMap.equivalent_arfNormalForm`), and two nonsingular spaces are isometric if and only if
they have the same dimension and the same Arf invariant
(`QuadraticMap.equivalent_iff_finrank_eq_and_arf_eq`). In particular, `Q.arf = 0` if and only if
`V` admits a `Q`-totally isotropic Lagrangian (equivalently, half-dimensional) subspace.

## Main definitions

* `QuadraticMap.gaussSum Q`: the integer Gauss sum `∑ v : V, (-1 : ℤ) ^ (Q v).val` of a quadratic
  form over `ZMod 2` on a finite space.
* `QuadraticMap.arf Q`: the Arf invariant in `ZMod 2` of a quadratic form over `ZMod 2` (taking the
  value `0` outside finite-dimensional spaces with nondegenerate polar form).
* `TauCeti.arfNormalForm m ε`: the standard `2 * m`-dimensional nonsingular `𝔽₂`-quadratic form with
  Arf parameter `ε` (`m` hyperbolic planes when `ε = 0`, and one anisotropic plane plus `m - 1`
  hyperbolic planes when `ε = 1` and `m ≥ 1`).

## Main results

* `QuadraticMap.arf_eq_sum_of_toMatrix_polarBilin_eq_J`:
  `Q.arf = ∑ i, Q (b (.inl i)) * Q (b (.inr i))` in every symplectic basis `b`.
* `QuadraticMap.gaussSum_eq_pow_arf_mul_two_pow`:
  `Q.gaussSum = (-1 : ℤ) ^ Q.arf.val * 2 ^ (finrank (ZMod 2) V / 2)`.
* `QuadraticMap.card_filter_apply_eq_zero_of_finrank_eq_two_mul` and
  `QuadraticMap.card_filter_apply_eq_zero_of_finrank_eq_zero`: the number of zeros of `Q` in `ℤ` is
  `2 ^ (2 * m - 1) + (-1 : ℤ) ^ Q.arf.val * 2 ^ (m - 1)` for `m ≥ 1`, and `1` for `m = 0`.
* `QuadraticMap.IsometryEquiv.arf_eq`, `QuadraticMap.arf_prod`, `QuadraticMap.arf_pi`, and
  `QuadraticMap.arf_eq_add_arf_restrict_orthogonal`: invariance under isometry and additivity under
  orthogonal sums and internal orthogonal direct sums.
* `QuadraticMap.equivalent_arfNormalForm` and `QuadraticMap.equivalent_iff_finrank_eq_and_arf_eq`:
  plane normal form and classification of nonsingular `𝔽₂`-quadratic forms by dimension and Arf
  invariant.
* `QuadraticMap.arf_eq_zero_iff_exists_isTotallyIsotropic_orthogonal_eq` and
  `QuadraticMap.arf_eq_zero_iff_exists_isTotallyIsotropic_two_mul_finrank_eq`: Lagrangian and
  half-dimensional `Q`-totally isotropic subspace criteria for `Q.arf = 0`.

## References

* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2 (Teil I)*,
  J. Reine Angew. Math. 183 (1941), 148–167.
* A. Pyronneau, *The Arf and Rohklin's invariant*, January 2024, §2.1, Lemmas 2.11–2.13,
  Corollary 2.14, and Theorem 2.15, pp. 4–5.
-/

public section

open Module QuadraticMap Submodule

namespace QuadraticMap

/-! ### Integer Gauss sums of quadratic forms over `ZMod 2` -/

section ZModTwoSigns

private theorem neg_one_pow_val_add (x y : ZMod 2) :
    (-1 : ℤ) ^ (x + y).val = (-1 : ℤ) ^ x.val * (-1 : ℤ) ^ y.val :=
  (by decide : ∀ a b : ZMod 2, (-1 : ℤ) ^ (a + b).val = (-1 : ℤ) ^ a.val * (-1 : ℤ) ^ b.val) x y

private theorem neg_one_pow_val_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    (-1 : ℤ) ^ (∑ i ∈ s, f i).val = ∏ i ∈ s, (-1 : ℤ) ^ (f i).val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, neg_one_pow_val_add, ih]

private theorem neg_one_pow_val_inj {x y : ZMod 2} :
    (-1 : ℤ) ^ x.val = (-1 : ℤ) ^ y.val ↔ x = y :=
  (by decide : ∀ a b : ZMod 2, (-1 : ℤ) ^ a.val = (-1 : ℤ) ^ b.val ↔ a = b) x y

private theorem one_add_neg_one_pow_val (x : ZMod 2) :
    (1 : ℤ) + (-1 : ℤ) ^ x.val = if x = 0 then 2 else 0 :=
  (by decide : ∀ a : ZMod 2, (1 : ℤ) + (-1 : ℤ) ^ a.val = if a = 0 then 2 else 0) x

end ZModTwoSigns

section GaussSum

variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup V₁] [Module (ZMod 2) V₁] [AddCommGroup V₂] [Module (ZMod 2) V₂]

/-- The integer **Gauss sum** `∑ v : V, (-1 : ℤ) ^ (Q v).val` of a quadratic form over `ZMod 2` on
a finite vector space `V`. -/
def gaussSum [Fintype V] (Q : QuadraticForm (ZMod 2) V) : ℤ :=
  ∑ v : V, (-1 : ℤ) ^ (Q v).val

/-- Defining sum for `QuadraticMap.gaussSum`. -/
theorem gaussSum_def [Fintype V] (Q : QuadraticForm (ZMod 2) V) :
    Q.gaussSum = ∑ v : V, (-1 : ℤ) ^ (Q v).val :=
  (rfl)

/-- On the zero quadratic form, every vector contributes `+1`, so the Gauss sum is `#V`. -/
@[simp]
theorem gaussSum_zero [Fintype V] : (0 : QuadraticForm (ZMod 2) V).gaussSum = Fintype.card V := by
  simp [gaussSum]

/-- On a trivial (`0`-dimensional) vector space, the Gauss sum of any quadratic form is `1`. -/
@[simp]
theorem gaussSum_of_subsingleton [Fintype V] [Subsingleton V] (Q : QuadraticForm (ZMod 2) V) :
    Q.gaussSum = 1 := by
  have : Unique V := uniqueOfSubsingleton (0 : V)
  rw [gaussSum, Fintype.sum_unique, Subsingleton.elim default (0 : V), map_zero, ZMod.val_zero,
    pow_zero]

/-- Isometric quadratic forms over `ZMod 2` have the same Gauss sum. -/
theorem IsometryEquiv.gaussSum_eq [Fintype V₁] [Fintype V₂]
    {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (e : Q₁.IsometryEquiv Q₂) : Q₁.gaussSum = Q₂.gaussSum :=
  Fintype.sum_equiv e.toEquiv _ _ fun v ↦ by rw [← e.map_app]; rfl

/-- Equivalent quadratic forms over `ZMod 2` have the same Gauss sum. -/
theorem Equivalent.gaussSum_eq [Fintype V₁] [Fintype V₂]
    {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (h : Q₁.Equivalent Q₂) : Q₁.gaussSum = Q₂.gaussSum :=
  let ⟨e⟩ := h; e.gaussSum_eq

/-- The Gauss sum is multiplicative over orthogonal products `QuadraticMap.prod`. -/
@[simp]
theorem gaussSum_prod [Fintype V₁] [Fintype V₂]
    (Q₁ : QuadraticForm (ZMod 2) V₁) (Q₂ : QuadraticForm (ZMod 2) V₂) :
    (Q₁.prod Q₂).gaussSum = Q₁.gaussSum * Q₂.gaussSum := by
  rw [gaussSum, gaussSum, gaussSum, Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by
    rw [QuadraticMap.prod_apply, neg_one_pow_val_add]

/-- The Gauss sum is multiplicative over finite orthogonal products `QuadraticMap.pi`. -/
theorem gaussSum_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod 2) (M i)] [∀ i, Fintype (M i)]
    (Q : ∀ i, QuadraticForm (ZMod 2) (M i)) :
    (QuadraticMap.pi Q).gaussSum = ∏ i, (Q i).gaussSum := by
  simp_rw [gaussSum, QuadraticMap.pi_apply, neg_one_pow_val_sum]
  exact (Fintype.prod_sum fun i m ↦ (-1 : ℤ) ^ (Q i m).val).symm

/-- Twice the number of zeros of `Q` equals `#V + Q.gaussSum`. -/
theorem two_mul_card_filter_apply_eq_zero [Fintype V] (Q : QuadraticForm (ZMod 2) V) :
    2 * ((Finset.univ.filter fun v : V ↦ Q v = 0).card : ℤ) = Fintype.card V + Q.gaussSum := by
  have hsum : ∑ v : V, ((1 : ℤ) + (-1 : ℤ) ^ (Q v).val) = Fintype.card V + Q.gaussSum := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_one, gaussSum]
  rw [← hsum]
  simp_rw [one_add_neg_one_pow_val, ← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **Gauss sum of a binary symplectic plane over `ZMod 2`.** The plane `a x₀² + x₀ x₁ + c x₁²`
has Gauss sum `(-1) ^ (a * c).val * 2`: `+2` when `a * c = 0`, and `-2` when `a = c = 1`. -/
@[simp]
theorem gaussSum_binarySymplectic (a c : ZMod 2) :
    (TauCeti.binarySymplectic (ZMod 2) a c).gaussSum = (-1 : ℤ) ^ (a * c).val * 2 := by
  simp only [gaussSum, TauCeti.binarySymplectic_apply]
  exact (by decide : ∀ a c : ZMod 2,
    (∑ v : Fin 2 → ZMod 2, (-1 : ℤ) ^ (a * v 0 ^ 2 + v 0 * v 1 + c * v 1 ^ 2).val) =
      (-1 : ℤ) ^ (a * c).val * 2) a c

/-- The hyperbolic `x 0 * x 1` plane over `ZMod 2` has Gauss sum `2`. -/
@[simp]
theorem gaussSum_proj_zero_one :
    (QuadraticMap.proj (0 : Fin 2) (1 : Fin 2) :
      QuadraticForm (ZMod 2) (Fin 2 → ZMod 2)).gaussSum = 2 := by
  rw [← TauCeti.binarySymplectic_zero_zero, gaussSum_binarySymplectic]
  norm_num

/-- **Gauss sum in symplectic coordinates.** In any symplectic basis `b : Basis (ι ⊕ ι) (ZMod 2) V`
of `Q.polarBilin`, the Gauss sum of `Q` equals
`(-1) ^ (∑ i, Q (b (.inl i)) * Q (b (.inr i))).val * 2 ^ #ι`. -/
theorem gaussSum_eq_of_toMatrix_polarBilin_eq_J {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] (Q : QuadraticForm (ZMod 2) V) (b : Basis (ι ⊕ ι) (ZMod 2) V)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι (ZMod 2)) :
    Q.gaussSum =
      (-1 : ℤ) ^ (∑ i, Q (b (.inl i)) * Q (b (.inr i))).val * 2 ^ Fintype.card ι := by
  rw [← (Q.isometryEquivPiBinarySymplectic b hb).gaussSum_eq, gaussSum_pi]
  simp_rw [gaussSum_binarySymplectic, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ← neg_one_pow_val_sum]

/-- **Basis independence of the symplectic Arf sum.** For any two symplectic bases `b` and `c` of
`Q.polarBilin` over `ZMod 2`, the sums of products `∑ i, Q (b (.inl i)) * Q (b (.inr i))` and
`∑ j, Q (c (.inl j)) * Q (c (.inr j))` coincide. -/
theorem sum_mul_eq_of_toMatrix_polarBilin_eq_J {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (Q : QuadraticForm (ZMod 2) V)
    (b : Basis (ι ⊕ ι) (ZMod 2) V) (c : Basis (κ ⊕ κ) (ZMod 2) V)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι (ZMod 2))
    (hc : LinearMap.BilinForm.toMatrix c Q.polarBilin = Matrix.J κ (ZMod 2)) :
    ∑ i, Q (b (.inl i)) * Q (b (.inr i)) = ∑ j, Q (c (.inl j)) * Q (c (.inr j)) := by
  have : FiniteDimensional (ZMod 2) V := Module.Finite.of_basis b
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Fintype V := Fintype.ofFinite V
  have hcard : Fintype.card ι = Fintype.card κ := by
    have hdim := (finrank_eq_card_basis b).symm.trans (finrank_eq_card_basis c)
    simp only [Fintype.card_sum] at hdim
    omega
  have hg := (Q.gaussSum_eq_of_toMatrix_polarBilin_eq_J b hb).symm.trans
    (Q.gaussSum_eq_of_toMatrix_polarBilin_eq_J c hc)
  rw [hcard] at hg
  exact neg_one_pow_val_inj.mp (mul_right_cancel₀ (by positivity) hg)

end GaussSum

/-! ### The Arf invariant -/

section ArfInvariant

variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup V₁] [Module (ZMod 2) V₁] [AddCommGroup V₂] [Module (ZMod 2) V₂]

open scoped Classical in
/-- The **Arf invariant** `Q.arf : ZMod 2` of a quadratic form over `ZMod 2`.

When `V` is finite-dimensional and `Q.polarBilin` is nondegenerate, `Q.arf` equals
`∑ i, Q (b (.inl i)) * Q (b (.inr i))` in any symplectic basis `b` of `Q.polarBilin`
(`QuadraticMap.arf_eq_sum_of_toMatrix_polarBilin_eq_J`). Outside that domain (`V`
infinite-dimensional or `Q.polarBilin` degenerate), `Q.arf` takes the junk value `0`. -/
noncomputable def arf (Q : QuadraticForm (ZMod 2) V) : ZMod 2 :=
  if h : FiniteDimensional (ZMod 2) V ∧ Q.polarBilin.Nondegenerate then
    have : FiniteDimensional (ZMod 2) V := h.1
    let b := (exists_basis_toMatrix_polarBilin_eq_J h.2).choose_spec.choose
    ∑ i, Q (b (.inl i)) * Q (b (.inr i))
  else 0

/-- `Q.arf` vanishes when `V` is not finite-dimensional. -/
theorem arf_eq_zero_of_not_finiteDimensional (Q : QuadraticForm (ZMod 2) V)
    (h : ¬ FiniteDimensional (ZMod 2) V) : Q.arf = 0 := by
  simp [arf, h]

/-- `Q.arf` vanishes when `Q.polarBilin` is degenerate. -/
theorem arf_eq_zero_of_not_polarBilin_nondegenerate (Q : QuadraticForm (ZMod 2) V)
    (h : ¬ Q.polarBilin.Nondegenerate) : Q.arf = 0 := by
  simp [arf, h]

/-- **Symplectic-basis formula for the Arf invariant.** In *every* finite `ι ⊕ ι`-indexed basis
`b` in which `Q.polarBilin` has matrix `Matrix.J ι (ZMod 2)`, `Q.arf` equals
`∑ i, Q (b (.inl i)) * Q (b (.inr i))`. -/
theorem arf_eq_sum_of_toMatrix_polarBilin_eq_J {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm (ZMod 2) V) (b : Basis (ι ⊕ ι) (ZMod 2) V)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι (ZMod 2)) :
    Q.arf = ∑ i, Q (b (.inl i)) * Q (b (.inr i)) := by
  have hfd : FiniteDimensional (ZMod 2) V := Module.Finite.of_basis b
  have hnd : Q.polarBilin.Nondegenerate := polarBilin_nondegenerate_of_toMatrix_eq_J hb
  have cond : FiniteDimensional (ZMod 2) V ∧ Q.polarBilin.Nondegenerate := ⟨hfd, hnd⟩
  rw [arf, dite_eq_left cond]
  exact Q.sum_mul_eq_of_toMatrix_polarBilin_eq_J
    (exists_basis_toMatrix_polarBilin_eq_J cond.2).choose_spec.choose b
    (exists_basis_toMatrix_polarBilin_eq_J cond.2).choose_spec.choose_spec.1 hb

/-- Explicit polar-pairing form of `arf_eq_sum_of_toMatrix_polarBilin_eq_J` for a symplectic basis
`(b (.inl i), b (.inr i))`. -/
theorem arf_eq_sum_of_polar_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm (ZMod 2) V) (b : Basis (ι ⊕ ι) (ZMod 2) V)
    (hll : ∀ i j, polar Q (b (.inl i)) (b (.inl j)) = 0)
    (hrr : ∀ i j, polar Q (b (.inr i)) (b (.inr j)) = 0)
    (hlr : ∀ i j, polar Q (b (.inl i)) (b (.inr j)) = if i = j then 1 else 0) :
    Q.arf = ∑ i, Q (b (.inl i)) * Q (b (.inr i)) :=
  Q.arf_eq_sum_of_toMatrix_polarBilin_eq_J b <|
    (Q.toMatrix_polarBilin_eq_J_iff b).mpr ⟨hll, hrr, hlr⟩

/-- On a zero-dimensional (`Subsingleton`) space, the Arf invariant is `0`. -/
@[simp]
theorem arf_of_subsingleton [Subsingleton V] (Q : QuadraticForm (ZMod 2) V) : Q.arf = 0 := by
  simpa using Q.arf_eq_sum_of_toMatrix_polarBilin_eq_J (Basis.empty V : Basis (Fin 0 ⊕ Fin 0) _ V)
    (Matrix.ext fun x ↦ isEmptyElim x)

/-- The Arf invariant of the zero quadratic form is `0`. -/
@[simp]
theorem arf_zero : (0 : QuadraticForm (ZMod 2) V).arf = 0 := by
  by_cases h :
      FiniteDimensional (ZMod 2) V ∧ (0 : QuadraticForm (ZMod 2) V).polarBilin.Nondegenerate
  · simp [arf, dite_eq_left h]
  · simp [arf, dite_eq_right h]

/-- If `Module.finrank (ZMod 2) V = 0`, then `Q.arf = 0`. -/
theorem arf_eq_zero_of_finrank_eq_zero (Q : QuadraticForm (ZMod 2) V)
    (hdim : finrank (ZMod 2) V = 0) : Q.arf = 0 := by
  by_cases hfd : FiniteDimensional (ZMod 2) V
  · have : Subsingleton V := (finrank_zero_iff (R := ZMod 2) (M := V)).mp hdim
    exact Q.arf_of_subsingleton
  · exact Q.arf_eq_zero_of_not_finiteDimensional hfd

/-- **Gauss sum formula for the Arf invariant.** On a finite `𝔽₂`-vector space `V`, any quadratic
form `Q` with nondegenerate polar form satisfies
`Q.gaussSum = (-1 : ℤ) ^ Q.arf.val * 2 ^ (finrank (ZMod 2) V / 2)`. -/
theorem gaussSum_eq_pow_arf_mul_two_pow [Fintype V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) :
    Q.gaussSum = (-1 : ℤ) ^ Q.arf.val * 2 ^ (finrank (ZMod 2) V / 2) := by
  obtain ⟨m, b, hb, hdim⟩ := exists_basis_toMatrix_polarBilin_eq_J hQ
  rw [Q.arf_eq_sum_of_toMatrix_polarBilin_eq_J b hb,
    Q.gaussSum_eq_of_toMatrix_polarBilin_eq_J b hb, Fintype.card_fin, hdim,
    Nat.mul_div_right m two_pos]

/-- Explicit `2 * m`-dimensional form of `gaussSum_eq_pow_arf_mul_two_pow`. -/
theorem gaussSum_eq_of_finrank_eq_two_mul [Fintype V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hm : finrank (ZMod 2) V = 2 * m) :
    Q.gaussSum = (-1 : ℤ) ^ Q.arf.val * 2 ^ m := by
  rw [Q.gaussSum_eq_pow_arf_mul_two_pow hQ, hm, Nat.mul_div_right m two_pos]

/-- **Count of `Q`-zeros for `m ≥ 1`.** For a quadratic form `Q` with nondegenerate polar form on
a finite `𝔽₂`-space of dimension `2 * m` with `1 ≤ m`, the number of `v : V` with `Q v = 0` is
`2 ^ (2 * m - 1) + (-1 : ℤ) ^ Q.arf.val * 2 ^ (m - 1)` in `ℤ`. -/
theorem card_filter_apply_eq_zero_of_finrank_eq_two_mul [Fintype V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate) {m : ℕ}
    (hm : finrank (ZMod 2) V = 2 * m) (hm1 : 1 ≤ m) :
    ((Finset.univ.filter fun v : V ↦ Q v = 0).card : ℤ) =
      2 ^ (2 * m - 1) + (-1 : ℤ) ^ Q.arf.val * 2 ^ (m - 1) := by
  have h2 := Q.two_mul_card_filter_apply_eq_zero
  have hcard : (Fintype.card V : ℤ) = 2 * 2 ^ (2 * m - 1) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hm]
    push_cast
    rw [← pow_succ' (2 : ℤ) (2 * m - 1), Nat.sub_add_cancel (by omega)]
  have hgauss : Q.gaussSum = 2 * ((-1 : ℤ) ^ Q.arf.val * 2 ^ (m - 1)) := by
    rw [Q.gaussSum_eq_of_finrank_eq_two_mul hQ hm]
    calc
      (-1 : ℤ) ^ Q.arf.val * 2 ^ m
          = (-1 : ℤ) ^ Q.arf.val * (2 * 2 ^ (m - 1)) := by
            rw [← pow_succ' (2 : ℤ) (m - 1), Nat.sub_add_cancel hm1]
      _ = 2 * ((-1 : ℤ) ^ Q.arf.val * 2 ^ (m - 1)) := by ring
  rw [hcard, hgauss] at h2
  linarith

/-- **Count of `Q`-zeros for `m = 0`.** On a `0`-dimensional finite `𝔽₂`-space, `0` is the unique
zero of `Q`, so the zero count in `ℤ` is `1`. -/
theorem card_filter_apply_eq_zero_of_finrank_eq_zero [Fintype V]
    (Q : QuadraticForm (ZMod 2) V) (h0 : finrank (ZMod 2) V = 0) :
    ((Finset.univ.filter fun v : V ↦ Q v = 0).card : ℤ) = 1 := by
  have : Subsingleton V := (finrank_zero_iff (R := ZMod 2) (M := V)).mp h0
  have : Unique V := uniqueOfSubsingleton (0 : V)
  have h2 := Q.two_mul_card_filter_apply_eq_zero
  rw [Fintype.card_unique, Nat.cast_one, Q.gaussSum_of_subsingleton] at h2
  linarith

/-- **Isometry invariance of the Arf invariant.** -/
theorem IsometryEquiv.arf_eq
    {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (e : Q₁.IsometryEquiv Q₂) : Q₁.arf = Q₂.arf := by
  have hfd_iff : FiniteDimensional (ZMod 2) V₁ ↔ FiniteDimensional (ZMod 2) V₂ :=
    ⟨fun _ ↦ Module.Finite.equiv e.toLinearEquiv,
      fun _ ↦ Module.Finite.equiv e.symm.toLinearEquiv⟩
  by_cases h₁ : FiniteDimensional (ZMod 2) V₁ ∧ Q₁.polarBilin.Nondegenerate
  · have := h₁.1
    have := hfd_iff.mp h₁.1
    have : Finite V₁ := Module.finite_of_finite (ZMod 2)
    have : Finite V₂ := Module.finite_of_finite (ZMod 2)
    have : Fintype V₁ := Fintype.ofFinite V₁
    have : Fintype V₂ := Fintype.ofFinite V₂
    have hnd₂ : Q₂.polarBilin.Nondegenerate := e.polarBilin_nondegenerate_iff.mp h₁.2
    have hg := e.gaussSum_eq
    rw [Q₁.gaussSum_eq_pow_arf_mul_two_pow h₁.2, Q₂.gaussSum_eq_pow_arf_mul_two_pow hnd₂,
      e.toLinearEquiv.finrank_eq] at hg
    exact neg_one_pow_val_inj.mp (mul_right_cancel₀ (by positivity) hg)
  · have h₂ : ¬ (FiniteDimensional (ZMod 2) V₂ ∧ Q₂.polarBilin.Nondegenerate) := by
      rwa [← hfd_iff, ← e.polarBilin_nondegenerate_iff]
    simp [arf, dite_eq_right h₁, dite_eq_right h₂]

/-- Equivalent quadratic forms over `ZMod 2` have equal Arf invariants. -/
theorem Equivalent.arf_eq
    {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (h : Q₁.Equivalent Q₂) : Q₁.arf = Q₂.arf :=
  let ⟨e⟩ := h; e.arf_eq

/-- **Orthogonal-sum additivity of the Arf invariant.** -/
theorem arf_prod [FiniteDimensional (ZMod 2) V₁] [FiniteDimensional (ZMod 2) V₂]
    {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (hQ₁ : Q₁.polarBilin.Nondegenerate) (hQ₂ : Q₂.polarBilin.Nondegenerate) :
    (Q₁.prod Q₂).arf = Q₁.arf + Q₂.arf := by
  have : Finite V₁ := Module.finite_of_finite (ZMod 2)
  have : Finite V₂ := Module.finite_of_finite (ZMod 2)
  have : Fintype V₁ := Fintype.ofFinite V₁
  have : Fintype V₂ := Fintype.ofFinite V₂
  obtain ⟨m₁, -, -, hd₁⟩ := exists_basis_toMatrix_polarBilin_eq_J hQ₁
  obtain ⟨m₂, -, -, hd₂⟩ := exists_basis_toMatrix_polarBilin_eq_J hQ₂
  have hnd : (Q₁.prod Q₂).polarBilin.Nondegenerate :=
    polarBilin_prod_nondegenerate_iff.mpr ⟨hQ₁, hQ₂⟩
  have hdim : finrank (ZMod 2) (V₁ × V₂) = 2 * (m₁ + m₂) := by
    rw [Module.finrank_prod, hd₁, hd₂, mul_add]
  have hg := gaussSum_prod Q₁ Q₂
  rw [(Q₁.prod Q₂).gaussSum_eq_of_finrank_eq_two_mul hnd hdim,
    Q₁.gaussSum_eq_of_finrank_eq_two_mul hQ₁ hd₁,
    Q₂.gaussSum_eq_of_finrank_eq_two_mul hQ₂ hd₂] at hg
  have hcalc :
      ((-1 : ℤ) ^ Q₁.arf.val * 2 ^ m₁) * ((-1 : ℤ) ^ Q₂.arf.val * 2 ^ m₂) =
        (-1 : ℤ) ^ (Q₁.arf + Q₂.arf).val * 2 ^ (m₁ + m₂) := by
    rw [neg_one_pow_val_add, pow_add]
    ring
  rw [hcalc] at hg
  exact neg_one_pow_val_inj.mp (mul_right_cancel₀ (by positivity) hg)

/-- Additivity of the Arf invariant over finite orthogonal products `QuadraticMap.pi`. -/
theorem arf_pi {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod 2) (M i)] [∀ i, FiniteDimensional (ZMod 2) (M i)]
    {Q : ∀ i, QuadraticForm (ZMod 2) (M i)} (hQ : ∀ i, (Q i).polarBilin.Nondegenerate) :
    (QuadraticMap.pi Q).arf = ∑ i, (Q i).arf := by
  classical
  have : ∀ i, Finite (M i) := fun _ ↦ Module.finite_of_finite (ZMod 2)
  have : ∀ i, Fintype (M i) := fun i ↦ Fintype.ofFinite (M i)
  choose m _ _ hdim using fun i ↦ exists_basis_toMatrix_polarBilin_eq_J (hQ i)
  have hnd : (QuadraticMap.pi Q).polarBilin.Nondegenerate :=
    polarBilin_pi_nondegenerate_iff.mpr hQ
  have htot : finrank (ZMod 2) (∀ i, M i) = 2 * ∑ i, m i := by
    rw [Module.finrank_pi_fintype, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ hdim i
  have hg := gaussSum_pi Q
  rw [(QuadraticMap.pi Q).gaussSum_eq_of_finrank_eq_two_mul hnd htot] at hg
  have hrhs : ∏ i, (Q i).gaussSum = (-1 : ℤ) ^ (∑ i, (Q i).arf).val * 2 ^ ∑ i, m i := by
    simp_rw [fun i ↦ (Q i).gaussSum_eq_of_finrank_eq_two_mul (hQ i) (hdim i),
      Finset.prod_mul_distrib, ← neg_one_pow_val_sum, Finset.prod_pow_eq_pow_sum]
  rw [hrhs] at hg
  exact neg_one_pow_val_inj.mp (mul_right_cancel₀ (by positivity) hg)

/-- Additivity of the Arf invariant along an internal polar-orthogonal direct sum
`V = W ⊕ W^⊥`. -/
theorem arf_eq_add_arf_restrict_orthogonal [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate)
    {W : Submodule (ZMod 2) V} (hW : IsCompl W (LinearMap.BilinForm.orthogonal Q.polarBilin W)) :
    Q.arf =
      (Q.restrict W).arf + (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin W)).arf := by
  have he := IsometryEquiv.prodRestrictOrthogonal Q W hW
  have hnd := he.symm.polarBilin_nondegenerate_iff.mp hQ
  rw [polarBilin_prod_nondegenerate_iff] at hnd
  rw [← he.arf_eq, arf_prod hnd.1 hnd.2]

/-- The Arf invariant of the binary symplectic plane `a x₀² + x₀ x₁ + c x₁²` over `ZMod 2` is
`a * c`. -/
@[simp]
theorem arf_binarySymplectic (a c : ZMod 2) :
    (TauCeti.binarySymplectic (ZMod 2) a c).arf = a * c := by
  have hnd := TauCeti.nondegenerate_polarBilin_binarySymplectic (R := ZMod 2) a c
  have hdim : finrank (ZMod 2) (Fin 2 → ZMod 2) = 2 * 1 := by simp
  have hg := (TauCeti.binarySymplectic (ZMod 2) a c).gaussSum_eq_of_finrank_eq_two_mul hnd hdim
  rw [gaussSum_binarySymplectic, pow_one] at hg
  exact neg_one_pow_val_inj.mp (mul_right_cancel₀ two_ne_zero hg.symm)

/-- The hyperbolic `x 0 * x 1` plane `QuadraticMap.proj 0 1` over `ZMod 2` has Arf invariant `0`. -/
@[simp]
theorem arf_proj_zero_one :
    (QuadraticMap.proj (0 : Fin 2) (1 : Fin 2) :
      QuadraticForm (ZMod 2) (Fin 2 → ZMod 2)).arf = 0 := by
  rw [← TauCeti.binarySymplectic_zero_zero, arf_binarySymplectic, zero_mul]

end ArfInvariant

end QuadraticMap

/-! ### Plane decomposition, classification, and Lagrangian criteria -/

namespace TauCeti

/-- **Standard normal-form quadratic space over `ZMod 2`.** On `Fin m → Fin 2 → ZMod 2`,
`arfNormalForm m ε` is the orthogonal sum of `m` hyperbolic planes when `ε = 0`, and of one
anisotropic plane `binarySymplectic (ZMod 2) 1 1` together with `m - 1` hyperbolic planes when
`ε = 1` and `m ≥ 1`. -/
def arfNormalForm (m : ℕ) (ε : ZMod 2) : QuadraticForm (ZMod 2) (Fin m → Fin 2 → ZMod 2) :=
  QuadraticMap.pi fun i : Fin m ↦
    if (i : ℕ) = 0 ∧ ε = 1 then binarySymplectic (ZMod 2) 1 1
    else QuadraticMap.proj (0 : Fin 2) (1 : Fin 2)

/-- At `ε = 0`, `TauCeti.arfNormalForm m 0` is the orthogonal sum of `m` hyperbolic `x 0 * x 1`
planes. -/
theorem arfNormalForm_zero (m : ℕ) :
    arfNormalForm m 0 =
      QuadraticMap.pi fun _ : Fin m ↦
        (QuadraticMap.proj (0 : Fin 2) (1 : Fin 2) :
          QuadraticForm (ZMod 2) (Fin 2 → ZMod 2)) := by
  simp [arfNormalForm]

/-- The polar bilinear form of `TauCeti.arfNormalForm m ε` is nondegenerate. -/
theorem nondegenerate_polarBilin_arfNormalForm (m : ℕ) (ε : ZMod 2) :
    (arfNormalForm m ε).polarBilin.Nondegenerate := by
  rw [arfNormalForm, polarBilin_pi_nondegenerate_iff]
  intro i
  split_ifs
  · exact nondegenerate_polarBilin_binarySymplectic 1 1
  · exact nondegenerate_polarBilin_proj_zero_one

/-- For `m ≥ 1`, `TauCeti.arfNormalForm m ε` has Arf invariant `ε`. -/
@[simp]
theorem arf_arfNormalForm_of_pos {m : ℕ} (hm : 0 < m) (ε : ZMod 2) :
    (arfNormalForm m ε).arf = ε := by
  rw [arfNormalForm, QuadraticMap.arf_pi (fun i ↦ by
    split_ifs
    · exact nondegenerate_polarBilin_binarySymplectic 1 1
    · exact nondegenerate_polarBilin_proj_zero_one)]
  rw [Fintype.sum_eq_single ⟨0, hm⟩]
  · simp only [true_and]
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) ε with rfl | rfl <;> simp
  · intro i hi
    have hi0 : (i : ℕ) ≠ 0 := fun h ↦ hi (Fin.ext h)
    simp [hi0]

/-- `TauCeti.arfNormalForm m 0` has Arf invariant `0` for every `m : ℕ`. -/
@[simp]
theorem arf_arfNormalForm_zero (m : ℕ) : (arfNormalForm m 0).arf = 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact QuadraticMap.arf_of_subsingleton _
  · exact arf_arfNormalForm_of_pos hm 0

/-- Helper reducing any finite orthogonal product of equal-diagonal binary symplectic planes over
`ZMod 2` to `TauCeti.arfNormalForm m (∑ i, d i)` by repeatedly replacing pairs of anisotropic
planes with pairs of hyperbolic planes. -/
private theorem equivalent_arfNormalForm_of_pi_binarySymplectic :
    ∀ (m : ℕ) (d : Fin m → ZMod 2),
      (QuadraticMap.pi fun i : Fin m ↦ binarySymplectic (ZMod 2) (d i) (d i)).Equivalent
        (arfNormalForm m (∑ i, d i))
  | 0, _ => ⟨IsometryEquiv.pi fun i ↦ i.elim0⟩
  | 1, d => by
      refine ⟨IsometryEquiv.pi fun i ↦ IsometryEquiv.ofEq ?_⟩
      fin_cases i
      simp only [Fin.sum_univ_one, Fin.zero_eta, true_and]
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (d 0) with h | h <;> simp [h]
  | m + 2, d => by
      -- Peel off the first summand `0` and apply the induction hypothesis to the `m + 1` tail.
      let head := binarySymplectic (ZMod 2) (d 0) (d 0)
      let tail := QuadraticMap.pi fun i : Fin (m + 1) ↦
        binarySymplectic (ZMod 2) (d i.succ) (d i.succ)
      have hcons₁ : (head.prod tail).Equivalent
          (QuadraticMap.pi fun i : Fin (m + 2) ↦ binarySymplectic (ZMod 2) (d i) (d i)) :=
        ⟨IsometryEquiv.consPi (M := fun _ ↦ Fin 2 → ZMod 2)
          fun i : Fin (m + 2) ↦ binarySymplectic (ZMod 2) (d i) (d i)⟩
      let s : ZMod 2 := ∑ i : Fin (m + 1), d i.succ
      have htail : tail.Equivalent (arfNormalForm (m + 1) s) :=
        equivalent_arfNormalForm_of_pi_binarySymplectic (m + 1) (fun i ↦ d i.succ)
      -- Split `arfNormalForm (m + 1) s` into its `0`-th plane and `m` hyperbolic planes.
      let plane (x : ZMod 2) : QuadraticForm (ZMod 2) (Fin 2 → ZMod 2) :=
        if x = 1 then binarySymplectic (ZMod 2) 1 1
        else QuadraticMap.proj (0 : Fin 2) (1 : Fin 2)
      let rest := QuadraticMap.pi fun _ : Fin m ↦
        (QuadraticMap.proj (0 : Fin 2) (1 : Fin 2) :
          QuadraticForm (ZMod 2) (Fin 2 → ZMod 2))
      have hcons₂ : ((plane s).prod rest).Equivalent (arfNormalForm (m + 1) s) := by
        refine ⟨(IsometryEquiv.consPi (M := fun _ ↦ Fin 2 → ZMod 2) fun i : Fin (m + 1) ↦
          if (i : ℕ) = 0 ∧ s = 1 then binarySymplectic (ZMod 2) 1 1
          else QuadraticMap.proj (0 : Fin 2) (1 : Fin 2)).symm.trans ?_ |>.symm⟩
        exact IsometryEquiv.prod (IsometryEquiv.ofEq (by simp [plane]))
          (IsometryEquiv.pi fun i ↦ IsometryEquiv.ofEq (by simp))
      -- Compare the two-plane head `head.prod (plane s)` with `(plane (d 0 + s)).prod (proj 0 1)`.
      have hhead : (head.prod (plane s)).Equivalent
          ((plane (d 0 + s)).prod (QuadraticMap.proj (0 : Fin 2) (1 : Fin 2))) := by
        have hd0 : head = plane (d 0) := by
          rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (d 0) with h | h <;>
            simp [head, plane, h]
        rw [hd0]
        rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (d 0) with ha | ha <;>
          rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) s with hs | hs
        · rw [ha, hs, add_zero]
          dsimp only [plane]
          rw [ite_eq_right zero_ne_one]
        · rw [ha, hs, zero_add]
          dsimp only [plane]
          rw [ite_eq_right zero_ne_one]
          exact ⟨IsometryEquiv.prodComm _ _⟩
        · rw [ha, hs, add_zero]
          dsimp only [plane]
          rw [ite_eq_right zero_ne_one]
        · have h11 : (1 : ZMod 2) + 1 = 0 := by decide
          rw [ha, hs, h11]
          dsimp only [plane]
          rw [ite_eq_left rfl, ite_eq_right zero_ne_one]
          exact ⟨isometryEquivProjProdBinarySymplecticOneOne.symm⟩
      -- Reassemble `(plane (d 0 + s)) ⊥ (proj 0 1 ⊥ rest)` into `arfNormalForm (m + 2) (∑ i, d i)`.
      have hsum : ∑ i : Fin (m + 2), d i = d 0 + s := Fin.sum_univ_succ d
      have hcons₃ :
          ((plane (d 0 + s)).prod
            ((QuadraticMap.proj (0 : Fin 2) (1 : Fin 2)).prod rest)).Equivalent
          (arfNormalForm (m + 2) (d 0 + s)) := by
        have hrest' : ((QuadraticMap.proj (0 : Fin 2) (1 : Fin 2)).prod rest).Equivalent
            (QuadraticMap.pi fun _ : Fin (m + 1) ↦
              (QuadraticMap.proj (0 : Fin 2) (1 : Fin 2) :
                QuadraticForm (ZMod 2) (Fin 2 → ZMod 2))) :=
          ⟨IsometryEquiv.consPi (M := fun _ ↦ Fin 2 → ZMod 2) fun _ : Fin (m + 1) ↦
            (QuadraticMap.proj (0 : Fin 2) (1 : Fin 2) :
              QuadraticForm (ZMod 2) (Fin 2 → ZMod 2))⟩
        refine (Equivalent.prod (Equivalent.refl _) hrest').trans ?_
        refine ⟨(IsometryEquiv.prod (IsometryEquiv.ofEq ?_)
          (IsometryEquiv.pi fun i : Fin (m + 1) ↦ IsometryEquiv.ofEq ?_)).trans
          (IsometryEquiv.consPi (M := fun _ ↦ Fin 2 → ZMod 2) fun i : Fin (m + 2) ↦
            if (i : ℕ) = 0 ∧ d 0 + s = 1 then binarySymplectic (ZMod 2) 1 1
            else QuadraticMap.proj (0 : Fin 2) (1 : Fin 2))⟩
        · simp [plane]
        · simp
      rw [hsum]
      exact hcons₁.symm.trans <|
        (Equivalent.prod (Equivalent.refl head) (htail.trans hcons₂.symm)).trans <|
          Equivalent.trans ⟨(IsometryEquiv.prodAssoc _ _ _).symm⟩ <|
            (Equivalent.prod hhead (Equivalent.refl rest)).trans <|
              Equivalent.trans ⟨IsometryEquiv.prodAssoc _ _ _⟩ hcons₃

end TauCeti

namespace QuadraticMap

section Classification

variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup V₁] [Module (ZMod 2) V₁] [AddCommGroup V₂] [Module (ZMod 2) V₂]

/-- **Decomposition into hyperbolic and anisotropic planes.** Every finite-dimensional quadratic
space `(V, Q)` over `ZMod 2` with nondegenerate polar form is isometric to an orthogonal sum of
planes `TauCeti.binarySymplectic (ZMod 2) (d i) (d i)` (`QuadraticMap.proj 0 1` when `d i = 0`, and
`TauCeti.binarySymplectic (ZMod 2) 1 1` when `d i = 1`) with `Q.arf = ∑ i, d i`. -/
theorem exists_equivalent_pi_binarySymplectic [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate) :
    ∃ (m : ℕ) (d : Fin m → ZMod 2),
      finrank (ZMod 2) V = 2 * m ∧ Q.arf = ∑ i, d i ∧
        Q.Equivalent (QuadraticMap.pi fun i ↦ TauCeti.binarySymplectic (ZMod 2) (d i) (d i)) := by
  obtain ⟨m, b, hb, hdim⟩ := exists_basis_toMatrix_polarBilin_eq_J hQ
  refine ⟨m, fun i ↦ Q (b (.inl i)) * Q (b (.inr i)), hdim,
    Q.arf_eq_sum_of_toMatrix_polarBilin_eq_J b hb, ?_⟩
  exact ⟨(Q.isometryEquivPiBinarySymplectic b hb).symm.trans
    (IsometryEquiv.pi fun i ↦
      TauCeti.isometryEquivBinarySymplecticDiag (Q (b (.inl i))) (Q (b (.inr i))))⟩

/-- **Normal-form theorem for nonsingular `𝔽₂`-quadratic forms.** Every finite-dimensional
quadratic space `(V, Q)` over `ZMod 2` with nondegenerate polar form is isometric to
`TauCeti.arfNormalForm (finrank (ZMod 2) V / 2) Q.arf`. -/
theorem equivalent_arfNormalForm [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate) :
    Q.Equivalent (TauCeti.arfNormalForm (finrank (ZMod 2) V / 2) Q.arf) := by
  obtain ⟨m, d, hdim, harf, heq⟩ := exists_equivalent_pi_binarySymplectic hQ
  rw [hdim, Nat.mul_div_right m two_pos, harf]
  exact heq.trans (TauCeti.equivalent_arfNormalForm_of_pi_binarySymplectic m d)

/-- **Classification of nonsingular quadratic forms over `ZMod 2` by dimension and Arf invariant.**
Two finite-dimensional quadratic spaces over `ZMod 2` with nondegenerate polar forms are isometric
if and only if they have the same dimension and the same Arf invariant. -/
theorem equivalent_iff_finrank_eq_and_arf_eq
    [FiniteDimensional (ZMod 2) V₁] [FiniteDimensional (ZMod 2) V₂]
    {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (hQ₁ : Q₁.polarBilin.Nondegenerate) (hQ₂ : Q₂.polarBilin.Nondegenerate) :
    Q₁.Equivalent Q₂ ↔
      finrank (ZMod 2) V₁ = finrank (ZMod 2) V₂ ∧ Q₁.arf = Q₂.arf := by
  refine ⟨fun ⟨e⟩ ↦ ⟨e.toLinearEquiv.finrank_eq, e.arf_eq⟩, fun ⟨hdim, harf⟩ ↦ ?_⟩
  have h₁ := Q₁.equivalent_arfNormalForm hQ₁
  rw [hdim, harf] at h₁
  exact h₁.trans (Q₂.equivalent_arfNormalForm hQ₂).symm

/-- On a two-dimensional space over `ZMod 2`, a quadratic form with nondegenerate polar form is
isometric to the hyperbolic `x 0 * x 1` plane `QuadraticMap.proj 0 1` if and only if `Q.arf = 0`. -/
theorem equivalent_proj_zero_one_iff_arf_eq_zero [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2) :
    Q.Equivalent (QuadraticMap.proj (0 : Fin 2) (1 : Fin 2)) ↔ Q.arf = 0 := by
  rw [equivalent_iff_finrank_eq_and_arf_eq hQ TauCeti.nondegenerate_polarBilin_proj_zero_one]
  simp [hdim]

/-- On a two-dimensional space over `ZMod 2`, a quadratic form with nondegenerate polar form is
isometric to the anisotropic plane `TauCeti.binarySymplectic (ZMod 2) 1 1` if and only if
`Q.arf = 1`. -/
theorem equivalent_binarySymplectic_one_one_iff_arf_eq_one [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2) :
    Q.Equivalent (TauCeti.binarySymplectic (ZMod 2) 1 1) ↔ Q.arf = 1 := by
  rw [equivalent_iff_finrank_eq_and_arf_eq hQ
    (TauCeti.nondegenerate_polarBilin_binarySymplectic 1 1)]
  simp [hdim]

/-- A two-dimensional quadratic space over `ZMod 2` with nondegenerate polar form is anisotropic if
and only if its Arf invariant is `1`. -/
theorem anisotropic_iff_arf_eq_one_of_finrank_eq_two [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2) :
    Q.Anisotropic ↔ Q.arf = 1 := by
  refine ⟨fun hani ↦ ?_, fun harf ↦ ?_⟩
  · rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) Q.arf with h0 | h1
    · have heq := (Q.equivalent_proj_zero_one_iff_arf_eq_zero hQ hdim).mpr h0
      exact False.elim (TauCeti.not_anisotropic_proj_zero_one (heq.anisotropic_iff.mp hani))
    · exact h1
  · have heq := (Q.equivalent_binarySymplectic_one_one_iff_arf_eq_one hQ hdim).mpr harf
    exact heq.anisotropic_iff.mpr TauCeti.anisotropic_binarySymplectic_one_one

/-- **Half-dimensional `Q`-totally isotropic subspace criterion.** For a finite-dimensional
quadratic space `(V, Q)` over `ZMod 2` with nondegenerate polar form, `Q.arf = 0` if and only if
`V` contains a `Q`-totally isotropic subspace of half the ambient dimension. -/
theorem arf_eq_zero_iff_exists_isTotallyIsotropic_two_mul_finrank_eq
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf = 0 ↔
      ∃ U : Submodule (ZMod 2) V,
        Q.IsTotallyIsotropic U ∧ 2 * finrank (ZMod 2) U = finrank (ZMod 2) V := by
  refine ⟨fun harf ↦ ?_, ?_⟩
  · obtain ⟨m, -, -, hdim⟩ := exists_basis_toMatrix_polarBilin_eq_J hQ
    obtain ⟨e⟩ := Q.equivalent_arfNormalForm hQ
    rw [harf, hdim, Nat.mul_div_right m two_pos] at e
    let φ : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → Fin 2 → ZMod 2) :=
      { toFun c i := ![c i, 0]
        map_add' c₁ c₂ := funext fun i ↦ by ext j; fin_cases j <;> simp
        map_smul' r c := funext fun i ↦ by ext j; fin_cases j <;> simp }
    have hφ_inj : Function.Injective φ := fun c₁ c₂ h ↦
      funext fun i ↦ by simpa [φ] using congrFun (congrFun h i) 0
    let U : Submodule (ZMod 2) V := (LinearMap.range φ).map e.symm.toLinearMap
    refine ⟨U, ?_, ?_⟩
    · rw [isTotallyIsotropic_iff]
      intro v hv
      rcases Submodule.mem_map.mp hv with ⟨w, ⟨c, rfl⟩, rfl⟩
      have hcoe : e.symm.toLinearMap (φ c) = e.symm (φ c) := rfl
      rw [hcoe, e.symm.map_app]
      simp [TauCeti.arfNormalForm, φ]
    · rw [e.symm.toLinearEquiv.finrank_map_eq, LinearMap.finrank_range_of_inj hφ_inj,
        Module.finrank_fin_fun, hdim]
  · rintro ⟨U, hU, hdim⟩
    let bU := Module.finBasis (ZMod 2) U
    have hcard : Fintype.card (Fin (finrank (ZMod 2) U)) +
        Fintype.card (Fin (finrank (ZMod 2) U)) = finrank (ZMod 2) V := by
      rw [Fintype.card_fin, ← two_mul]
      exact hdim
    obtain ⟨b, hb, -, hbQ⟩ :=
      hU.exists_basis_toMatrix_polarBilin_eq_J_and_apply_eq_zero hQ bU hcard
    rw [Q.arf_eq_sum_of_toMatrix_polarBilin_eq_J b hb]
    simp [hbQ]

/-- Explicit `finrank U = m` form of `arf_eq_zero_iff_exists_isTotallyIsotropic_two_mul_finrank_eq`
when `finrank (ZMod 2) V = 2 * m`. -/
theorem arf_eq_zero_iff_exists_isTotallyIsotropic_finrank_eq
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hm : finrank (ZMod 2) V = 2 * m) :
    Q.arf = 0 ↔ ∃ U : Submodule (ZMod 2) V, Q.IsTotallyIsotropic U ∧ finrank (ZMod 2) U = m := by
  rw [Q.arf_eq_zero_iff_exists_isTotallyIsotropic_two_mul_finrank_eq hQ]
  exact exists_congr fun U ↦ and_congr_right fun _ ↦ by omega

/-- **Lagrangian `Q`-totally isotropic subspace criterion.** For a finite-dimensional quadratic
space `(V, Q)` over `ZMod 2` with nondegenerate polar form, `Q.arf = 0` if and only if `V` contains
a `Q`-totally isotropic subspace equal to its own `Q.polarBilin`-orthogonal complement. -/
theorem arf_eq_zero_iff_exists_isTotallyIsotropic_orthogonal_eq
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) :
    Q.arf = 0 ↔
      ∃ U : Submodule (ZMod 2) V,
        Q.IsTotallyIsotropic U ∧ LinearMap.BilinForm.orthogonal Q.polarBilin U = U := by
  rw [Q.arf_eq_zero_iff_exists_isTotallyIsotropic_two_mul_finrank_eq hQ]
  exact exists_congr fun U ↦
    and_congr_right fun hU ↦ (hU.orthogonal_polarBilin_eq_iff_two_mul_finrank_eq hQ).symm

end Classification

end QuadraticMap

/-! ### Concrete checks -/

section Checks

-- Zero-dimensional space: Arf = 0, Gauss sum = 1, unique zero = 0.
example : (0 : QuadraticForm (ZMod 2) Unit).arf = 0 ∧
    (0 : QuadraticForm (ZMod 2) Unit).gaussSum = 1 ∧
    ((Finset.univ.filter fun v : Unit ↦ (0 : QuadraticForm (ZMod 2) Unit) v = 0).card : ℤ) = 1 :=
  ⟨QuadraticMap.arf_of_subsingleton _, QuadraticMap.gaussSum_of_subsingleton _, by decide⟩

-- Orthogonal sum of two anisotropic planes on `(Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)`:
-- Arf = 0, Gauss sum = 4, and exact zero count = 10 = 2³ + 2¹.
example :
    let A := TauCeti.binarySymplectic (ZMod 2) 1 1
    (A.prod A).arf = 0 ∧ (A.prod A).gaussSum = 4 ∧
      (Finset.univ.filter fun v ↦ (A.prod A) v = 0).card = 10 := by
  intro A
  have hA : A.polarBilin.Nondegenerate := TauCeti.nondegenerate_polarBilin_binarySymplectic 1 1
  have harf : (A.prod A).arf = 0 := by
    rw [QuadraticMap.arf_prod hA hA, QuadraticMap.arf_binarySymplectic]
    decide
  refine ⟨harf, ?_, ?_⟩
  · rw [QuadraticMap.gaussSum_prod, QuadraticMap.gaussSum_binarySymplectic]
    decide
  · have hnd : (A.prod A).polarBilin.Nondegenerate :=
      QuadraticMap.polarBilin_prod_nondegenerate_iff.mpr ⟨hA, hA⟩
    have hdim : finrank (ZMod 2) ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) = 2 * 2 := by simp
    have hc := (A.prod A).card_filter_apply_eq_zero_of_finrank_eq_two_mul hnd hdim (by omega)
    rw [harf, ZMod.val_zero] at hc
    norm_num at hc
    exact_mod_cast hc

-- Symplectic basis change on `x 0 * x 1`: `a = ![1, 1]`, `b = ![0, 1]` has `Q a = 1`, `Q b = 0`,
-- `polar Q a b = 1`, and `Q a * Q b = 0 = Q.arf`, whereas `Q a = 1 ≠ 0 = Q ![1, 0]`.
example :
    let H : QuadraticForm (ZMod 2) (Fin 2 → ZMod 2) := QuadraticMap.proj 0 1
    let a : Fin 2 → ZMod 2 := ![1, 1]
    let b : Fin 2 → ZMod 2 := ![0, 1]
    polar H a b = 1 ∧ H a = 1 ∧ H b = 0 ∧ H a * H b = H.arf := by
  simp

end Checks
