/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NoncommutativeGeometry.UniversalDifferential.Complex
public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# The graded algebra of universal forms and the graded Leibniz rule

The universal forms `Ωⁿ = A⁺ ⊗ A^⊗n` of `TauCeti.UniversalForms` carry Connes' product, under
which the tensor word `x ⊗ a₁ ⊗ ⋯ ⊗ aₙ` is the product `x da₁ ⋯ daₙ`. Splitting off the last
letter identifies `Ωⁿ⁺¹` with `Ωⁿ ⊗ A` (`TauCeti.UniversalForms.snocEquiv`), the word `ω ⊗ b`
standing for `ω db`. The product is determined by three rules:

* zero-forms multiply as elements of `A⁺`;
* `(ω da) y = ω d(ay) - (ω a) dy`, which is the Leibniz rule `d(a)y = d(ay) - a dy`;
* `ω (η db) = (ω η) db`.

The first two give the right action of `A⁺` on `Ωⁿ`, by recursion on `n`; the third then defines
the product `Ωⁿ × Ωᵐ → Ωⁿ⁺ᵐ` by recursion on `m`. This product is associative and unital, so the
universal forms are a graded algebra, and `⨁ n, Ωⁿ` is a ring and a `k`-algebra. The differential of
`TauCeti.UniversalForms.d` satisfies the graded Leibniz rule
`d(ωη) = dω η + (-1)ⁿ ω dη` for `ω ∈ Ωⁿ`. Left multiplication by a zero-form multiplies the
coefficient of a word, and appending a letter is right multiplication by its differential, so
every word `x da₁ ⋯ daₙ` is the product of `x` with the differentials `daᵢ`.

The forced unitization is retained even when `A` has a unit, so the degree-zero part is always
`A⁺`, and nonunital algebra homomorphisms induce maps of graded algebras.

## Main definitions

* `TauCeti.UniversalForms.cast`: reindexing universal forms along an equality of degrees.
* `TauCeti.UniversalForms.snocEquiv`, `TauCeti.UniversalForms.snoc`: `Ωⁿ ⊗ A ≃ Ωⁿ⁺¹`,
  `ω ⊗ b ↦ ω db`.
* `TauCeti.UniversalForms.mul`: the product `Ωⁿ × Ωᵐ → Ωⁿ⁺ᵐ`.
* `TauCeti.UniversalForms.gMonoid`, `TauCeti.UniversalForms.gRing`,
  `TauCeti.UniversalForms.gAlgebra`: the graded algebra structure.

## Main results

* `TauCeti.UniversalForms.mul_snoc`, `TauCeti.UniversalForms.snoc_mul_word`,
  `TauCeti.UniversalForms.zeroEquiv_mul`: the defining rules of the product.
* `TauCeti.UniversalForms.mul_assoc`, `TauCeti.UniversalForms.one_mul`,
  `TauCeti.UniversalForms.mul_one`: associativity and the unit laws.
* `TauCeti.UniversalForms.map_mul`: nonunital algebra homomorphisms preserve the product.
* `TauCeti.UniversalForms.d_mul`: the graded Leibniz rule.
* `TauCeti.UniversalForms.cast_word_mul`, `TauCeti.UniversalForms.mul_d_word`: the tensor-word
  relations `y (x da₁ ⋯ daₙ) = (yx) da₁ ⋯ daₙ` and `ω d(b) = ω db`.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1, Proposition 3, p. 190.
* J. Cuntz and D. Quillen, *Algebra extensions and nonsingularity*, J. Amer. Math. Soc. 8 (1995),
  §1, for the product on `Ω A = A⁺ ⊗ A^⊗n` given by `d(a)b = d(ab) - a db`.
-/

public section

open scoped TensorProduct DirectSum

namespace TauCeti

universe u v

variable (k : Type u) (A : Type v) [CommRing k] [NonUnitalRing A] [Module k A]

namespace UniversalForms

noncomputable section

/-! ### Reindexing and the last letter -/

/-- Reindex universal forms along an equality of degrees. -/
def cast {n m : ℕ} (h : n = m) : UniversalForms k A n ≃ₗ[k] UniversalForms k A m :=
  TensorProduct.congr (LinearEquiv.refl k _) (TensorPower.cast k A h)

/-- Reindexing a word reindexes its letters. -/
@[simp]
theorem cast_word {n m : ℕ} (h : n = m) (x : Unitization k A) (a : Fin n → A) :
    cast k A h (word k A x a) = word k A x (a ∘ Fin.cast h.symm) := by
  simp [cast, word_def, TensorPower.cast_tprod]

/-- Reindexing along a reflexive equality is the identity. -/
@[simp]
theorem cast_refl {n : ℕ} (h : n = n) (ω : UniversalForms k A n) : cast k A h ω = ω := by
  simp [cast, TensorPower.cast_refl]

/-- Reindexing twice is reindexing along the composite equality. -/
@[simp]
theorem cast_cast {n m p : ℕ} (h : n = m) (h' : m = p) (ω : UniversalForms k A n) :
    cast k A h' (cast k A h ω) = cast k A (h.trans h') ω := by
  subst h h'
  simp

/-- Two graded universal forms are equal when their degrees agree and the reindexed forms agree. -/
theorem mk_eq_mk_of_cast {n m : ℕ} (h : n = m) {ω : UniversalForms k A n}
    {η : UniversalForms k A m} (h' : cast k A h ω = η) :
    GradedMonoid.mk (A := UniversalForms k A) n ω = GradedMonoid.mk m η := by
  subst h
  rw [cast_refl] at h'
  rw [h']

variable {k A} in
/-- Including a reindexed form in the direct sum is including the original form. -/
@[simp]
theorem of_cast {n m : ℕ} (h : n = m) (ω : UniversalForms k A n) :
    DirectSum.of (UniversalForms k A) m (cast k A h ω) = DirectSum.of (UniversalForms k A) n ω := by
  subst h
  rw [cast_refl]

/-- Splitting off the last letter identifies `Ωⁿ ⊗ A` with `Ωⁿ⁺¹`; the word `ω ⊗ b` stands
for `ω db`. -/
def snocEquiv (n : ℕ) : UniversalForms k A n ⊗[k] A ≃ₗ[k] UniversalForms k A (n + 1) :=
  (TensorProduct.assoc k _ _ _).trans <| TensorProduct.congr (LinearEquiv.refl k _) <|
    (TensorProduct.congr (LinearEquiv.refl k _) (TauCeti.TensorPower.oneEquiv k A).symm).trans
      TensorPower.mulEquiv

/-- Append the differential `db` of a letter to a form `ω`, giving `ω db`. -/
def snoc (n : ℕ) : UniversalForms k A n →ₗ[k] A →ₗ[k] UniversalForms k A (n + 1) :=
  (TensorProduct.mk k _ A).compr₂ (snocEquiv k A n).toLinearMap

/-- The splitting equivalence sends `ω ⊗ b` to `ω db`. -/
@[simp]
theorem snocEquiv_tmul {n : ℕ} (ω : UniversalForms k A n) (b : A) :
    snocEquiv k A n (ω ⊗ₜ b) = snoc k A n ω b := (rfl)

/-- Appending a letter to a word appends it to the tuple of letters. -/
@[simp]
theorem snoc_word {n : ℕ} (x : Unitization k A) (a : Fin n → A) (b : A) :
    snoc k A n (word k A x a) b = word k A x (Fin.snoc a b) := by
  simp only [snoc, snocEquiv, word_def, LinearMap.compr₂_apply, TensorProduct.mk_apply,
    LinearEquiv.coe_coe, LinearEquiv.trans_apply, TensorProduct.assoc_tmul,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply, TauCeti.TensorPower.oneEquiv_symm_apply,
    ← TensorPower.gMul_def, TensorPower.tprod_mul_tprod, Fin.append_right_eq_snoc]

/-- Every form of positive degree is a sum of forms `ω db`. -/
@[elab_as_elim]
theorem induction_snoc {n : ℕ} {P : UniversalForms k A (n + 1) → Prop}
    (ω : UniversalForms k A (n + 1)) (hsnoc : ∀ η b, P (snoc k A n η b))
    (hadd : ∀ ω η, P ω → P η → P (ω + η)) : P ω := by
  obtain ⟨t, rfl⟩ := (snocEquiv k A n).surjective ω
  induction t using TensorProduct.inductionOn with
  | tmul η b => exact hsnoc η b
  | add s t hs ht => simpa only [map_add] using hadd _ _ hs ht

/-- Linear maps out of forms of positive degree agree when they agree on every `ω db`. -/
theorem ext_snoc {M : Type*} [AddCommMonoid M] [Module k M] {n : ℕ}
    {f g : UniversalForms k A (n + 1) →ₗ[k] M}
    (h : ∀ ω b, f (snoc k A n ω b) = g (snoc k A n ω b)) : f = g := by
  refine LinearMap.ext fun ω ↦ ?_
  induction ω using induction_snoc k A with
  | hsnoc η b => exact h η b
  | hadd ω η hω hη => simp only [map_add, hω, hη]

/-- Reindexing commutes with appending a letter. -/
theorem cast_snoc {n m : ℕ} (h : n + 1 = m + 1) (ω : UniversalForms k A n) (b : A) :
    cast k A h (snoc k A n ω b) = snoc k A m (cast k A (Nat.succ_injective h) ω) b := by
  obtain rfl := Nat.succ_injective h
  simp

/-- The differential commutes with appending a letter: `d(ω db) = dω db`. -/
@[simp]
theorem d_snoc {n : ℕ} (ω : UniversalForms k A n) (b : A) :
    d k A (n + 1) (snoc k A n ω b) = snoc k A (n + 1) (d k A n ω) b := by
  induction ω using induction_on k A with
  | hword x a => simp [Fin.cons_snoc_eq_snoc_cons]
  | hadd ω η hω hη => simp only [map_add, LinearMap.add_apply, hω, hη]

/-- The differential of a zero-form `x` is `1 dx`. -/
theorem d_zeroEquiv_symm (x : Unitization k A) :
    d k A 0 ((zeroEquiv k A).symm x) = snoc k A 0 ((zeroEquiv k A).symm 1) x.snd := by
  rw [zeroEquiv_symm_apply, zeroEquiv_symm_apply, d_word, snoc_word]
  congr 1
  ext i
  fin_cases i
  rfl

instance gOne : GradedMonoid.GOne (UniversalForms k A) where
  one := word k A 1 Fin.elim0

/-- The graded unit is the empty word with coefficient `1`. -/
theorem gOne_def : (GradedMonoid.GOne.one : UniversalForms k A 0) = word k A 1 Fin.elim0 := (rfl)

variable {k A} in
/-- The unit of `⨁ n, Ωⁿ` is the empty word with coefficient `1`. -/
theorem one_def : (1 : ⨁ n, UniversalForms k A n) = DirectSum.of _ 0 (word k A 1 Fin.elim0) := by
  rw [DirectSum.one_def, gOne_def]

/-! ### The right action of the unitization -/

variable [IsScalarTower k A A] [SMulCommClass k A A]

/-- Right multiplication by a letter `b ∈ A`, by recursion on the degree:
`x b` in degree zero and `(ω da) b = ω d(ab) - (ω a) db`. -/
private def rightMul : (n : ℕ) → A →ₗ[k] Module.End k (UniversalForms k A n)
  | 0 => (zeroEquiv k A).symm.conj.toLinearMap ∘ₗ (LinearMap.mul k (Unitization k A)).flip ∘ₗ
      Unitization.inrHom k k A
  | n + 1 => (snocEquiv k A n).conj.toLinearMap ∘ₗ
      -- The endomorphism spaces of these tensor products have no inferred `AddCommGroup`
      -- instance, so the difference is written with the scalar `-1`.
      (LinearMap.lTensorHom (UniversalForms k A n) ∘ₗ (LinearMap.mul k A).flip +
        (-1 : k) • LinearMap.lcomp k _ (TensorProduct.lift (rightMul n).flip) ∘ₗ
          (TensorProduct.mk k (UniversalForms k A n) A).flip)

private theorem zeroEquiv_rightMul (b : A) (ω : UniversalForms k A 0) :
    zeroEquiv k A (rightMul k A 0 b ω) = zeroEquiv k A ω * b := by
  simp [rightMul, LinearEquiv.conj_apply_apply]

private theorem rightMul_zeroEquiv_symm (b : A) (x : Unitization k A) :
    rightMul k A 0 b ((zeroEquiv k A).symm x) = (zeroEquiv k A).symm (x * b) := by
  rw [LinearEquiv.eq_symm_apply, zeroEquiv_rightMul, LinearEquiv.apply_symm_apply]

private theorem rightMul_snoc {n : ℕ} (b a : A) (ω : UniversalForms k A n) :
    rightMul k A (n + 1) b (snoc k A n ω a) =
      snoc k A n ω (a * b) - snoc k A n (rightMul k A n a ω) b := by
  rw [← snocEquiv_tmul]
  simp [rightMul, LinearEquiv.conj_apply_apply, -snocEquiv_tmul, sub_eq_add_neg]
  simp only [snocEquiv_tmul]

private theorem rightMul_rightMul (n : ℕ) (b c : A) (ω : UniversalForms k A n) :
    rightMul k A n c (rightMul k A n b ω) = rightMul k A n (b * c) ω := by
  induction n generalizing b c with
  | zero =>
    obtain ⟨x, rfl⟩ := (zeroEquiv k A).symm.surjective ω
    simp only [rightMul_zeroEquiv_symm, _root_.mul_assoc, Unitization.inr_mul]
  | succ n ih =>
    induction ω using induction_snoc k A with
    | hsnoc η a =>
      simp only [rightMul_snoc, map_sub, ih, _root_.mul_assoc]
      abel
    | hadd ω η hω hη => simp only [map_add, hω, hη]

/-- The graded Leibniz rule for right multiplication by a letter. -/
private theorem d_rightMul (n : ℕ) (b : A) (ω : UniversalForms k A n) :
    d k A n (rightMul k A n b ω) =
      rightMul k A (n + 1) b (d k A n ω) + (n : ℤ).negOnePow • snoc k A n ω b := by
  induction n generalizing b with
  | zero =>
    obtain ⟨x, rfl⟩ := (zeroEquiv k A).symm.surjective ω
    have hx : x - (x.snd : Unitization k A) = x.fst • 1 := by
      ext <;> simp
    have hsub : snoc k A 0 ((zeroEquiv k A).symm x) b -
        snoc k A 0 ((zeroEquiv k A).symm (x.snd : Unitization k A)) b =
          snoc k A 0 ((zeroEquiv k A).symm 1) (x.fst • b) := by
      rw [← LinearMap.sub_apply, ← map_sub (snoc k A 0), ← map_sub, hx, map_smul, map_smul,
        LinearMap.smul_apply, map_smul]
    rw [rightMul_zeroEquiv_symm, d_zeroEquiv_symm, d_zeroEquiv_symm, rightMul_snoc,
      rightMul_zeroEquiv_symm, _root_.one_mul, Nat.cast_zero, Int.negOnePow_zero, one_smul,
      Unitization.snd_mul, Unitization.fst_inr, Unitization.snd_inr, zero_smul, add_zero,
      map_add]
    rw [← hsub]
    abel
  | succ n ih =>
    induction ω using induction_snoc k A with
    | hsnoc η a =>
      simp only [rightMul_snoc, map_sub, d_snoc, ih, LinearMap.map_add₂, Units.smul_def,
        map_zsmul, LinearMap.smul_apply, Nat.cast_succ, Int.negOnePow_succ, Units.val_neg,
        neg_smul]
      abel
    | hadd ω η hω hη =>
      simp only [map_add, LinearMap.add_apply, hω, hη, smul_add]
      abel

/-- Right multiplication by a zero-form `y = (r, b) ∈ A⁺`, that is `r ω + ω b`. -/
private def rightMulUnitization (n : ℕ) :
    Unitization k A →ₗ[k] Module.End k (UniversalForms k A n) :=
  (Unitization.fstHom k A).toLinearMap.smulRight LinearMap.id +
    rightMul k A n ∘ₗ Unitization.sndHom k k A

private theorem rightMulUnitization_apply (n : ℕ) (y : Unitization k A)
    (ω : UniversalForms k A n) :
    rightMulUnitization k A n y ω = y.fst • ω + rightMul k A n y.snd ω := by
  simp [rightMulUnitization]

/-! ### The product -/

/-- Connes' product of universal forms `Ωⁿ × Ωᵐ → Ωⁿ⁺ᵐ`, by recursion on `m`: right
multiplication by `A⁺` in degree zero, and `ω (η db) = (ω η) db`. -/
def mul (n : ℕ) : (m : ℕ) →
    UniversalForms k A n →ₗ[k] UniversalForms k A m →ₗ[k] UniversalForms k A (n + m)
  | 0 => (rightMulUnitization k A n ∘ₗ (zeroEquiv k A).toLinearMap).flip
  | m + 1 => LinearMap.lcomp k _ (snocEquiv k A m).symm.toLinearMap ∘ₗ
      LinearMap.llcomp k _ _ _ (snocEquiv k A (n + m)).toLinearMap ∘ₗ
        LinearMap.rTensorHom A ∘ₗ mul n m

private theorem mul_zeroEquiv_symm {n : ℕ} (ω : UniversalForms k A n) (y : Unitization k A) :
    mul k A n 0 ω ((zeroEquiv k A).symm y) = y.fst • ω + rightMul k A n y.snd ω := by
  simp [mul, rightMulUnitization_apply]

/-- Multiplying by a form ending in a differential: `ω (η db) = (ω η) db`. -/
@[simp]
theorem mul_snoc {n m : ℕ} (ω : UniversalForms k A n) (η : UniversalForms k A m) (b : A) :
    mul k A n (m + 1) ω (snoc k A m η b) = snoc k A (n + m) (mul k A n m ω η) b := by
  rw [← snocEquiv_tmul]
  simp [mul, -snocEquiv_tmul]
  simp only [snocEquiv_tmul]

/-- Right multiplication by a zero-form, on a form ending in a differential:
`(ω da) y = ω d(ay) - (ω a) dy`. -/
theorem snoc_mul_word {n : ℕ} (ω : UniversalForms k A n) (a : A) (y : Unitization k A) :
    mul k A (n + 1) 0 (snoc k A n ω a) (word k A y Fin.elim0) =
      snoc k A n ω ((a : Unitization k A) * y).snd -
        snoc k A n (mul k A n 0 ω (word k A (a : Unitization k A) Fin.elim0)) y.snd := by
  rw [← zeroEquiv_symm_apply, ← zeroEquiv_symm_apply, mul_zeroEquiv_symm, mul_zeroEquiv_symm,
    rightMul_snoc]
  simp only [Unitization.fst_inr, Unitization.snd_inr, Unitization.snd_mul, zero_smul, zero_add,
    map_add, map_smul]
  abel

/-- The product of zero-forms is the product in the unitization. -/
@[simp]
theorem zeroEquiv_mul (ω η : UniversalForms k A 0) :
    zeroEquiv k A (mul k A 0 0 ω η) = zeroEquiv k A ω * zeroEquiv k A η := by
  obtain ⟨y, rfl⟩ := (zeroEquiv k A).symm.surjective η
  rw [mul_zeroEquiv_symm, map_add, zeroEquiv_rightMul, map_smul, LinearEquiv.apply_symm_apply]
  conv_rhs => rw [← Unitization.inl_fst_add_inr_snd_eq y]
  rw [mul_add, ← Unitization.algebraMap_eq_inl, ← Algebra.commutes, ← Algebra.smul_def]

/-- Right multiplication by the unit is the identity. -/
@[simp]
theorem mul_one {n : ℕ} (ω : UniversalForms k A n) :
    mul k A n 0 ω (word k A 1 Fin.elim0) = ω := by
  rw [← zeroEquiv_symm_apply, mul_zeroEquiv_symm]
  simp

/-- Appending a letter is right multiplication by its differential: `ω d(b) = ω db`. -/
theorem mul_d_word {n : ℕ} (ω : UniversalForms k A n) (b : A) :
    mul k A n 1 ω (d k A 0 (word k A (b : Unitization k A) Fin.elim0)) = snoc k A n ω b := by
  rw [← zeroEquiv_symm_apply, d_zeroEquiv_symm, mul_snoc, zeroEquiv_symm_apply, mul_one,
    Unitization.snd_inr]
  -- The degree `n + 0` of the product with a zero-form reduces to `n`.
  rfl

private theorem mul_rightMul {n m : ℕ} (ω : UniversalForms k A n) (b : A)
    (η : UniversalForms k A m) :
    mul k A n m ω (rightMul k A m b η) = rightMul k A (n + m) b (mul k A n m ω η) := by
  induction m generalizing b with
  | zero =>
    obtain ⟨y, rfl⟩ := (zeroEquiv k A).symm.surjective η
    simp only [rightMul_zeroEquiv_symm, mul_zeroEquiv_symm, Unitization.fst_mul,
      Unitization.fst_inr, MulZeroClass.mul_zero, zero_smul, zero_add, Unitization.snd_mul,
      Unitization.snd_inr, add_zero, map_add, map_smul]
    -- The degree `n + 0` of the product with a zero-form reduces to `n`.
    exact congrArg (y.fst • rightMul k A n b ω + ·) (rightMul_rightMul k A n y.snd b ω).symm
  | succ m ih =>
    induction η using induction_snoc k A with
    | hsnoc η a =>
      simp only [rightMul_snoc, map_sub, mul_snoc, ih]
      exact (rightMul_snoc k A b a _).symm
    | hadd η θ hη hθ => simp only [map_add, hη, hθ]

/-- The product is associative, up to reindexing the degree `n + m + p = n + (m + p)`. -/
theorem mul_assoc {n m p : ℕ} (ω : UniversalForms k A n) (η : UniversalForms k A m)
    (θ : UniversalForms k A p) :
    cast k A (Nat.add_assoc n m p) (mul k A (n + m) p (mul k A n m ω η) θ) =
      mul k A n (m + p) ω (mul k A m p η θ) := by
  induction p with
  | zero =>
    obtain ⟨y, rfl⟩ := (zeroEquiv k A).symm.surjective θ
    simp only [cast_refl, mul_zeroEquiv_symm, map_add, map_smul]
    exact congrArg (y.fst • mul k A n m ω η + ·) (mul_rightMul k A ω y.snd η).symm
  | succ p ih =>
    induction θ using induction_snoc k A with
    | hsnoc θ c =>
      rw [mul_snoc, mul_snoc]
      refine (cast_snoc k A _ _ c).trans ?_
      rw [ih]
      exact (mul_snoc k A ω _ c).symm
    | hadd θ θ' hθ hθ' => simp only [map_add, hθ, hθ']

/-- Left multiplication by a zero-form multiplies the coefficient of a word:
`y (x da₁ ⋯ daₙ) = (yx) da₁ ⋯ daₙ`. -/
theorem cast_word_mul {n : ℕ} (y x : Unitization k A) (a : Fin n → A) :
    cast k A (Nat.zero_add n) (mul k A 0 n (word k A y Fin.elim0) (word k A x a)) =
      word k A (y * x) a := by
  induction n with
  | zero =>
    apply (zeroEquiv k A).injective
    rw [cast_refl, zeroEquiv_mul, zeroEquiv_word, zeroEquiv_word, zeroEquiv_word]
  | succ n ih =>
    rw [← Fin.snoc_init_self a, ← snoc_word, ← snoc_word, mul_snoc]
    exact (cast_snoc k A _ _ _).trans (by rw [ih])

/-- The unit is a left unit, up to reindexing the degree `0 + n = n`. -/
theorem one_mul {n : ℕ} (ω : UniversalForms k A n) :
    cast k A (Nat.zero_add n) (mul k A 0 n (word k A 1 Fin.elim0) ω) = ω := by
  induction ω using induction_on k A with
  | hword x a => rw [cast_word_mul, _root_.one_mul]
  | hadd ω η hω hη => rw [map_add, map_add, hω, hη]

/-- The graded Leibniz rule `d(ωη) = dω η + (-1)ⁿ ω dη` for `ω ∈ Ωⁿ`, up to reindexing the
degree `n + 1 + m = n + m + 1`. -/
theorem d_mul {n m : ℕ} (ω : UniversalForms k A n) (η : UniversalForms k A m) :
    d k A (n + m) (mul k A n m ω η) =
      cast k A (Nat.add_right_comm n 1 m) (mul k A (n + 1) m (d k A n ω) η) +
        (n : ℤ).negOnePow • mul k A n (m + 1) ω (d k A m η) := by
  induction m with
  | zero =>
    obtain ⟨y, rfl⟩ := (zeroEquiv k A).symm.surjective η
    have key : d k A n (y.fst • ω + rightMul k A n y.snd ω) =
        y.fst • d k A n ω + rightMul k A (n + 1) y.snd (d k A n ω) +
          (n : ℤ).negOnePow • snoc k A n ω y.snd := by
      rw [map_add, map_smul, d_rightMul]
      abel
    rw [mul_zeroEquiv_symm, mul_zeroEquiv_symm, cast_refl, d_zeroEquiv_symm, mul_snoc,
      zeroEquiv_symm_apply, mul_one]
    -- The degree `n + 0` of the product with a zero-form reduces to `n`.
    exact key
  | succ m ih =>
    induction η using induction_snoc k A with
    | hsnoc η b =>
      rw [mul_snoc k A ω η b, mul_snoc k A (d k A n ω) η b, d_snoc k A η b,
        mul_snoc k A ω (d k A m η) b]
      refine (d_snoc k A (n := n + m) _ b).trans ?_
      rw [ih, map_add, LinearMap.add_apply, Units.smul_def, Units.smul_def, map_zsmul,
        LinearMap.smul_apply]
      congr 1
      exact (cast_snoc k A _ _ b).symm
    | hadd η θ hη hθ =>
      simp only [map_add, hη, hθ, smul_add]
      abel

/-! ### The graded algebra -/

instance gMul : GradedMonoid.GMul (UniversalForms k A) where
  mul ω η := mul k A _ _ ω η

/-- The graded multiplication is `TauCeti.UniversalForms.mul`. -/
theorem gMul_def {n m : ℕ} (ω : UniversalForms k A n) (η : UniversalForms k A m) :
    GradedMonoid.GMul.mul ω η = mul k A n m ω η := (rfl)

/-- The universal forms are a graded monoid under Connes' product. -/
instance gMonoid : GradedMonoid.GMonoid (UniversalForms k A) where
  one_mul ω := mk_eq_mk_of_cast k A (Nat.zero_add _) (one_mul k A ω.snd)
  mul_one ω := mk_eq_mk_of_cast k A (Nat.add_zero _) (by
    rw [cast_refl]
    exact mul_one k A ω.snd)
  mul_assoc ω η θ := mk_eq_mk_of_cast k A (Nat.add_assoc _ _ _)
    (mul_assoc k A ω.snd η.snd θ.snd)

/-- The universal forms are a graded ring, so `⨁ n, Ωⁿ` is a ring. -/
instance gRing : DirectSum.GRing (UniversalForms k A) where
  mul_zero _ := map_zero _
  zero_mul _ := LinearMap.map_zero₂ _ _
  mul_add _ _ _ := map_add _ _ _
  add_mul _ _ _ := LinearMap.map_add₂ _ _ _ _
  natCast n := word k A (n : Unitization k A) Fin.elim0
  natCast_zero := by rw [Nat.cast_zero, word_zero]
  natCast_succ n := by
    rw [gOne_def]
    simp only [Nat.cast_succ, word_def, TensorProduct.add_tmul]
  intCast z := word k A (z : Unitization k A) Fin.elim0
  intCast_ofNat n := by rw [Int.cast_natCast]
  intCast_negSucc_ofNat n := by
    simp only [Int.cast_negSucc, word_def, TensorProduct.neg_tmul]

/-- The graded semiring structure of `TauCeti.UniversalForms.gRing`. Instance search assembles the
addition of `⨁ n, Ωⁿ` from the additive monoids of the tensor products `Ωⁿ`, and it does not
recover this structure from `gRing` compatibly with that addition, so it is registered directly. -/
instance gSemiring : DirectSum.GSemiring (UniversalForms k A) := DirectSum.GRing.toGSemiring

variable {k A} in
/-- The product in `⨁ n, Ωⁿ` of two homogeneous forms is their product of universal forms. -/
@[simp]
theorem of_mul_of {n m : ℕ} (ω : UniversalForms k A n) (η : UniversalForms k A m) :
    DirectSum.of (UniversalForms k A) n ω * DirectSum.of (UniversalForms k A) m η =
      DirectSum.of (UniversalForms k A) (n + m) (mul k A n m ω η) :=
  DirectSum.of_mul_of ω η

variable {k A} in
/-- Left multiplication by a zero-form `y` multiplies the coefficient of a word. -/
theorem of_word_mul_of_word {n : ℕ} (y x : Unitization k A) (a : Fin n → A) :
    DirectSum.of (UniversalForms k A) 0 (word k A y Fin.elim0) *
        DirectSum.of (UniversalForms k A) n (word k A x a) =
      DirectSum.of (UniversalForms k A) n (word k A (y * x) a) := by
  rw [of_mul_of, ← cast_word_mul, of_cast]

/-- Left multiplication by the zero-form `r • 1` is the scalar action of `r`, up to reindexing
the degree `0 + n = n`. -/
theorem cast_smul_one_mul {n : ℕ} (r : k) (ω : UniversalForms k A n) :
    cast k A (Nat.zero_add n) (mul k A 0 n (r • word k A 1 Fin.elim0) ω) = r • ω := by
  rw [map_smul, LinearMap.smul_apply, map_smul, one_mul]

/-- The universal forms are a graded `k`-algebra, so `⨁ n, Ωⁿ` is a `k`-algebra. -/
instance gAlgebra : DirectSum.GAlgebra k (UniversalForms k A) where
  toFun := (LinearMap.toSpanSingleton k _ (word k A 1 Fin.elim0)).toAddMonoidHom
  map_one := by simp [gOne_def]
  map_mul r s := mk_eq_mk_of_cast k A (ω := (r * s) • word k A 1 Fin.elim0)
    (η := mul k A 0 0 (r • word k A 1 Fin.elim0) (s • word k A 1 Fin.elim0)) rfl (by
      rw [cast_refl, mul_comm r s, mul_smul]
      simp only [map_smul, LinearMap.smul_apply, mul_one])
  commutes r x := by
    obtain ⟨n, ω⟩ := x
    refine mk_eq_mk_of_cast k A (ω := mul k A 0 n (r • word k A 1 Fin.elim0) ω)
      (η := mul k A n 0 ω (r • word k A 1 Fin.elim0)) (Nat.add_comm 0 n) ?_
    exact (cast_smul_one_mul k A r ω).trans (by rw [map_smul, mul_one])
  smul_def r x := by
    obtain ⟨n, ω⟩ := x
    refine mk_eq_mk_of_cast k A (ω := r • ω) (η := mul k A 0 n (r • word k A 1 Fin.elim0) ω)
      (Nat.zero_add n).symm ?_
    rw [← cast_smul_one_mul k A r ω, cast_cast, cast_refl]

/-! ### Functoriality -/

section Map

variable {A} {B : Type*} [NonUnitalRing B] [Module k B] [IsScalarTower k B B]
  [SMulCommClass k B B]

/-- Algebra homomorphisms commute with appending a letter: `f(ω db) = f(ω) d(f b)`. -/
@[simp]
theorem map_snoc (f : A →ₙₐ[k] B) {n : ℕ} (ω : UniversalForms k A n) (b : A) :
    map k f (n + 1) (snoc k A n ω b) = snoc k B n (map k f n ω) (f b) := by
  induction ω using induction_on k A with
  | hword x a =>
    simp only [snoc_word, map_word]
    congr 1
    exact Fin.comp_snoc f a b
  | hadd ω η hω hη => simp only [map_add, LinearMap.add_apply, hω, hη]

private theorem map_rightMul (f : A →ₙₐ[k] B) (n : ℕ) (b : A) (ω : UniversalForms k A n) :
    map k f n (rightMul k A n b ω) = rightMul k B n (f b) (map k f n ω) := by
  induction n generalizing b with
  | zero =>
    apply (zeroEquiv k B).injective
    rw [zeroEquiv_map, zeroEquiv_rightMul, zeroEquiv_rightMul, zeroEquiv_map, _root_.map_mul,
      Unitization.map_inr]
  | succ n ih =>
    induction ω using induction_snoc k A with
    | hsnoc η a => simp only [rightMul_snoc, map_sub, map_snoc, ih, _root_.map_mul]
    | hadd ω η hω hη => simp only [map_add, hω, hη]

/-- Algebra homomorphisms preserve the product of universal forms. -/
@[simp]
theorem map_mul (f : A →ₙₐ[k] B) {n m : ℕ} (ω : UniversalForms k A n)
    (η : UniversalForms k A m) :
    map k f (n + m) (mul k A n m ω η) = mul k B n m (map k f n ω) (map k f m η) := by
  induction m with
  | zero =>
    obtain ⟨y, rfl⟩ := (zeroEquiv k A).symm.surjective η
    have hy : map k f 0 ((zeroEquiv k A).symm y) = (zeroEquiv k B).symm (Unitization.map f y) := by
      rw [LinearEquiv.eq_symm_apply, zeroEquiv_map, LinearEquiv.apply_symm_apply]
    rw [mul_zeroEquiv_symm, hy, mul_zeroEquiv_symm, Unitization.fst_map, Unitization.snd_map]
    -- The degree `n + 0` of the product with a zero-form reduces to `n`.
    exact (by rw [map_add, map_smul, map_rightMul] :
      map k f n (y.fst • ω + rightMul k A n y.snd ω) =
        y.fst • map k f n ω + rightMul k B n (f y.snd) (map k f n ω))
  | succ m ih =>
    induction η using induction_snoc k A with
    | hsnoc η b =>
      rw [mul_snoc, map_snoc, mul_snoc, ← ih]
      exact map_snoc k f (n := n + m) _ b
    | hadd η θ hη hθ => simp only [map_add, hη, hθ]

end Map

end

end UniversalForms

end TauCeti
