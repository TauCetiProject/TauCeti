/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.RingTheory.MilnorK.Basic
import TauCeti.Algebra.Ring.Parity

/-!
# Serre's algebra `L(k)` over the Milnor K-ring

For a field `k`, **Serre's algebra** `L(k)` is the ring obtained from the Milnor K-ring
`K_*ᴹ(k)` by adjoining an indeterminate `Π` of degree one subject to

* `Π x = σ(x) Π` for `x ∈ K_*ᴹ(k)`, where `σ` is the grade involution, so that
  `Π x = (-1) ^ n x Π` for `x ∈ K_nᴹ(k)`;
* `Π Π = {-1} Π`.

Every element is uniquely `a + b Π` with `a, b ∈ K_*ᴹ(k)`, and

`(a + b Π) (c + d Π) = a c + (a d + b σ(c) + b σ(d) {-1}) Π`.

This is the target of Serre's construction of the residue maps of Milnor K-theory: for a discrete
valuation on a field `F` with residue field `k` and a uniformizer `t`, the assignment
`u tⁱ ↦ {ū} + i Π` extends to a ring homomorphism `K_*ᴹ(F) → L(k)`, whose `Π`-coefficient is the
residue `K_nᴹ(F) → K_{n-1}ᴹ(k)`. The relation `Π Π = {-1} Π`, rather than `Π Π = 0`, is what
makes `{x, -x}` go to zero.

We model `L(k)` as the structure `TauCeti.SerreAlgebra k` of pairs `(a, b)` standing for `a + b Π`.
The ring axioms are transported from `2 × 2` matrices over `K_*ᴹ(k)`: right multiplication by
`c + d Π` on the free left `K_*ᴹ(k)`-module with basis `1, Π` has the upper triangular matrix
`!![c, d; 0, σ(c) + σ(d) {-1}]`, and this representation is faithful.

## Main definitions

* `TauCeti.SerreAlgebra k`: Serre's algebra `L(k)`, with components `fst` and `snd`.
* `TauCeti.SerreAlgebra.C`: the ring embedding `K_*ᴹ(k) → L(k)`.
* `TauCeti.SerreAlgebra.X`: the indeterminate `Π`.
* `TauCeti.SerreAlgebra.lift`: the universal property: a ring homomorphism `φ` out of `K_*ᴹ(k)`
  and an element `p` with `p φ(x) = φ(σ x) p` and `p p = φ {-1} p` determine a ring homomorphism
  out of `L(k)`.
* `TauCeti.SerreAlgebra.fstHom`, `TauCeti.SerreAlgebra.rho`: the ring homomorphisms
  `a + b Π ↦ a` and `a + b Π ↦ a + b {-1}` to `K_*ᴹ(k)`.
* `TauCeti.SerreAlgebra.shift c`: for `c ∈ kˣ`, the ring automorphism fixing `K_*ᴹ(k)` and sending
  `Π` to `Π - {c}`.
* `TauCeti.SerreAlgebra.rescale n`: for `n : ℤ`, the ring endomorphism fixing `K_*ᴹ(k)` and sending
  `Π` to `n Π`.
* `TauCeti.SerreAlgebra.map`: the ring homomorphism `L(k) → L(k')` induced by a field homomorphism.
* `TauCeti.SerreAlgebra.degree n`: the degree-`n` piece `K_nᴹ(k) ⊕ K_{n-1}ᴹ(k) Π`, making `L(k)`
  a graded monoid, with `degreeZeroEquiv` and `degreeSuccEquiv` identifying the pieces.

## Main results

* `TauCeti.SerreAlgebra.X_mul_X`, `TauCeti.SerreAlgebra.X_mul_C`,
  `TauCeti.SerreAlgebra.X_mul_C_of_mem_degree`: the defining relations of `Π`.
* `TauCeti.SerreAlgebra.C_add_C_mul_X`: every element is `a + b Π`.
* `TauCeti.SerreAlgebra.ringHom_ext`: ring homomorphisms out of `L(k)` are determined by their
  values on `K_*ᴹ(k)` and on `Π`.
* `TauCeti.SerreAlgebra.shift_shift`: `shift c ∘ shift c' = shift (c c')`.
* `TauCeti.SerreAlgebra.mul_comm_of_mem_degree`: `L(k)` is graded-commutative,
  `x y = (-1) ^ (m n) y x` for `x` of degree `m` and `y` of degree `n`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, proof of Theorem 7.3.
* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. 9 (1970), 318–344, §2,
  where the construction is attributed to Serre.
-/

public section

noncomputable section

namespace TauCeti

open MilnorK

variable (k : Type*) [Field k]

/-- **Serre's algebra** `L(k)`: the Milnor K-ring `K_*ᴹ(k)` with an adjoined indeterminate `Π`
satisfying `Π x = σ(x) Π` and `Π Π = {-1} Π`. The pair `(fst, snd)` stands for `fst + snd Π`. -/
@[ext]
structure SerreAlgebra where
  /-- The component `a` of `a + b Π`. -/
  fst : MilnorK k
  /-- The coefficient `b` of `Π`, written on the left, in `a + b Π`. -/
  snd : MilnorK k

namespace SerreAlgebra

variable {k}

/-! ### The ring structure -/

instance : Zero (SerreAlgebra k) := ⟨⟨0, 0⟩⟩
instance : One (SerreAlgebra k) := ⟨⟨1, 0⟩⟩
instance : Add (SerreAlgebra k) := ⟨fun x y ↦ ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
instance : Neg (SerreAlgebra k) := ⟨fun x ↦ ⟨-x.fst, -x.snd⟩⟩
instance : Sub (SerreAlgebra k) := ⟨fun x y ↦ ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
instance : SMul ℕ (SerreAlgebra k) := ⟨fun n x ↦ ⟨n • x.fst, n • x.snd⟩⟩
instance : SMul ℤ (SerreAlgebra k) := ⟨fun n x ↦ ⟨n • x.fst, n • x.snd⟩⟩
instance : NatCast (SerreAlgebra k) := ⟨fun n ↦ ⟨n, 0⟩⟩
instance : IntCast (SerreAlgebra k) := ⟨fun n ↦ ⟨n, 0⟩⟩

/-- The product `(a + b Π) (c + d Π) = a c + (a d + b σ(c) + b σ(d) {-1}) Π`. -/
instance : Mul (SerreAlgebra k) :=
  ⟨fun x y ↦ ⟨x.fst * y.fst,
    x.fst * y.snd + x.snd * involute y.fst + x.snd * involute y.snd * ofUnit (-1)⟩⟩

instance : Pow (SerreAlgebra k) ℕ := ⟨fun x n ↦ npowRec n x⟩

@[simp] theorem fst_zero : (0 : SerreAlgebra k).fst = 0 := rfl
@[simp] theorem snd_zero : (0 : SerreAlgebra k).snd = 0 := rfl
@[simp] theorem fst_one : (1 : SerreAlgebra k).fst = 1 := rfl
@[simp] theorem snd_one : (1 : SerreAlgebra k).snd = 0 := rfl
@[simp] theorem fst_add (x y : SerreAlgebra k) : (x + y).fst = x.fst + y.fst := rfl
@[simp] theorem snd_add (x y : SerreAlgebra k) : (x + y).snd = x.snd + y.snd := rfl
@[simp] theorem fst_neg (x : SerreAlgebra k) : (-x).fst = -x.fst := rfl
@[simp] theorem snd_neg (x : SerreAlgebra k) : (-x).snd = -x.snd := rfl
@[simp] theorem fst_sub (x y : SerreAlgebra k) : (x - y).fst = x.fst - y.fst := rfl
@[simp] theorem snd_sub (x y : SerreAlgebra k) : (x - y).snd = x.snd - y.snd := rfl
@[simp] theorem fst_nsmul (n : ℕ) (x : SerreAlgebra k) : (n • x).fst = n • x.fst := rfl
@[simp] theorem snd_nsmul (n : ℕ) (x : SerreAlgebra k) : (n • x).snd = n • x.snd := rfl
@[simp] theorem fst_zsmul (n : ℤ) (x : SerreAlgebra k) : (n • x).fst = n • x.fst := rfl
@[simp] theorem snd_zsmul (n : ℤ) (x : SerreAlgebra k) : (n • x).snd = n • x.snd := rfl
@[simp] theorem fst_natCast (n : ℕ) : (n : SerreAlgebra k).fst = n := rfl
@[simp] theorem snd_natCast (n : ℕ) : (n : SerreAlgebra k).snd = 0 := rfl
@[simp] theorem fst_intCast (n : ℤ) : (n : SerreAlgebra k).fst = n := rfl
@[simp] theorem snd_intCast (n : ℤ) : (n : SerreAlgebra k).snd = 0 := rfl

@[simp]
theorem fst_mul (x y : SerreAlgebra k) : (x * y).fst = x.fst * y.fst := rfl

@[simp]
theorem snd_mul (x y : SerreAlgebra k) : (x * y).snd =
    x.fst * y.snd + x.snd * involute y.fst + x.snd * involute y.snd * ofUnit (-1) := rfl

/-- The matrix `!![c, d; 0, σ(c) + σ(d) {-1}]` of right multiplication by `x = c + d Π` on the free
left `K_*ᴹ(k)`-module with basis `1, Π`, acting on row vectors. This representation is faithful
and multiplicative, and the ring structure of `L(k)` is transported along it. -/
private def toMatrix (x : SerreAlgebra k) : Matrix (Fin 2) (Fin 2) (MilnorK k) :=
  !![x.fst, x.snd; 0, involute x.fst + involute x.snd * ofUnit (-1)]

private theorem toMatrix_injective : Function.Injective (toMatrix (k := k)) := fun x y h ↦ by
  have h₀ := congrFun (congrFun h 0) 0
  have h₁ := congrFun (congrFun h 0) 1
  simp only [toMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h₀ h₁
  exact SerreAlgebra.ext h₀ h₁

/-- Moving `{-1}` past `σ(x)` turns it into `x`; used to reassociate products in `L(k)`. -/
private theorem ofUnit_neg_one_mul_involute_mul (x y : MilnorK k) :
    ofUnit (-1) * (involute x * y) = x * (ofUnit (-1) * y) := by
  rw [← mul_assoc, ofUnit_mul_involute, mul_assoc]

private theorem toMatrix_mul (x y : SerreAlgebra k) :
    toMatrix (x * y) = toMatrix x * toMatrix y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, Matrix.mul_apply, Fin.sum_univ_two, mul_add, add_mul, mul_assoc, add_assoc,
      ofUnit_mul_involute, ofUnit_neg_one_mul_involute_mul, add_left_comm]

private theorem toMatrix_pow (x : SerreAlgebra k) (n : ℕ) : toMatrix (x ^ n) = toMatrix x ^ n := by
  induction n with
  | zero =>
    -- The `Pow` instance is `npowRec`, so `x ^ 0` is `1` and `x ^ (n + 1)` is `x ^ n * x` by
    -- definition.
    change toMatrix 1 = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toMatrix]
  | succ n ih =>
    change toMatrix (x ^ n * x) = _
    rw [toMatrix_mul, ih, pow_succ]

-- The map is `toMatrix` written out: an instance body is exposed, so it cannot name the private
-- `toMatrix`, but its proof arguments may use the private lemmas about it.
instance instRing : Ring (SerreAlgebra k) :=
  Function.Injective.ring
    (fun x : SerreAlgebra k ↦ !![x.fst, x.snd; 0, involute x.fst + involute x.snd * ofUnit (-1)])
    (by exact toMatrix_injective)
    (by ext i j; fin_cases i <;> fin_cases j <;> simp)
    (by ext i j; fin_cases i <;> fin_cases j <;> simp)
    (fun x y ↦ by ext i j; fin_cases i <;> fin_cases j <;> simp [add_mul, add_add_add_comm])
    (by exact toMatrix_mul)
    (fun x ↦ by ext i j; fin_cases i <;> fin_cases j <;> simp [add_comm])
    (fun x y ↦ by ext i j; fin_cases i <;> fin_cases j <;> simp [sub_mul, add_sub_add_comm])
    (fun n x ↦ by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_assoc])
    (fun n x ↦ by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_assoc])
    (by exact toMatrix_pow)
    (fun n ↦ by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.natCast_apply])
    (fun n ↦ by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.intCast_apply])

/-! ### The embedding of `K_*ᴹ(k)` and the indeterminate `Π` -/

/-- The ring embedding `K_*ᴹ(k) → L(k)`, `a ↦ a + 0 Π`. -/
def C : MilnorK k →+* SerreAlgebra k where
  toFun a := ⟨a, 0⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp
  map_zero' := rfl
  map_add' a b := by ext <;> simp

@[simp] theorem fst_C (a : MilnorK k) : (C a).fst = a := (rfl)
@[simp] theorem snd_C (a : MilnorK k) : (C a).snd = 0 := (rfl)

theorem C_injective : Function.Injective (C (k := k)) := fun a b h ↦ by
  simpa using congrArg fst h

/-- The indeterminate `Π` of degree one. -/
def X : SerreAlgebra k := ⟨0, 1⟩

@[simp] theorem fst_X : (X : SerreAlgebra k).fst = 0 := (rfl)
@[simp] theorem snd_X : (X : SerreAlgebra k).snd = 1 := (rfl)

/-- The pair `(a, b)` is the element `a + b Π`. -/
theorem C_add_C_mul_X (a b : MilnorK k) : C a + C b * X = ⟨a, b⟩ := by
  ext <;> simp

/-- Every element of `L(k)` is `a + b Π` for its components `a` and `b`. -/
theorem C_fst_add_C_snd_mul_X (x : SerreAlgebra k) : C x.fst + C x.snd * X = x :=
  C_add_C_mul_X _ _

/-- The defining relation `Π Π = {-1} Π`. -/
theorem X_mul_X : X * X = C (ofUnit (-1)) * (X : SerreAlgebra k) := by
  ext <;> simp

/-- The defining relation `Π a = σ(a) Π`, where `σ` is the grade involution. -/
theorem X_mul_C (a : MilnorK k) : X * C a = C (involute a) * X := by
  ext <;> simp

/-- For `a ∈ K_nᴹ(k)`, `Π a = (-1) ^ n a Π`. -/
theorem X_mul_C_of_mem_degree {n : ℕ} {a : MilnorK k} (ha : a ∈ degree k n) :
    X * C a = (-1) ^ n * (C a * X) := by
  simp [X_mul_C, involute_of_mem_degree ha, mul_assoc]

/-! ### The universal property -/

section Lift

variable {A : Type*} [Semiring A]

/-- The ring homomorphism `L(k) → A` sending `a + b Π` to `φ a + φ b p`, for a ring homomorphism
`φ : K_*ᴹ(k) → A` and an element `p` satisfying the relations `p φ(x) = φ(σ x) p` and
`p p = φ {-1} p` of `Π`. -/
def lift (φ : MilnorK k →+* A) (p : A) (hp : ∀ x, p * φ x = φ (involute x) * p)
    (hpp : p * p = φ (ofUnit (-1)) * p) : SerreAlgebra k →+* A where
  toFun x := φ x.fst + φ x.snd * p
  map_one' := by simp
  map_mul' x y := by
    have hp' (x : MilnorK k) (z : A) : p * (φ x * z) = φ (involute x) * (p * z) := by
      rw [← mul_assoc, hp, mul_assoc]
    simp only [fst_mul, snd_mul, map_add, map_mul, add_mul, mul_add, mul_assoc, hp, hp', hpp]
    abel
  map_zero' := by simp
  map_add' x y := by simp only [fst_add, snd_add, map_add, add_mul]; abel

variable (φ : MilnorK k →+* A) (p : A) (hp : ∀ x, p * φ x = φ (involute x) * p)
  (hpp : p * p = φ (ofUnit (-1)) * p)

theorem lift_apply (x : SerreAlgebra k) : lift φ p hp hpp x = φ x.fst + φ x.snd * p :=
  (rfl)

@[simp]
theorem lift_C (a : MilnorK k) : lift φ p hp hpp (C a) = φ a := by
  simp [lift_apply]

@[simp]
theorem lift_X : lift φ p hp hpp X = p := by
  simp [lift_apply]

@[simp]
theorem lift_comp_C : (lift φ p hp hpp).comp C = φ :=
  RingHom.ext (lift_C φ p hp hpp)

end Lift

/-- Ring homomorphisms out of `L(k)` agreeing on `K_*ᴹ(k)` and on `Π` are equal. -/
@[ext]
theorem ringHom_ext {A : Type*} [Semiring A] {f g : SerreAlgebra k →+* A}
    (hC : f.comp C = g.comp C) (hX : f X = g X) : f = g := by
  ext x
  have hC' (a : MilnorK k) : f (C a) = g (C a) := RingHom.congr_fun hC a
  rw [← C_fst_add_C_snd_mul_X x]
  simp [hX, hC']

/-- `lift φ p hp hpp` is the unique ring homomorphism restricting to `φ` and sending `Π` to `p`. -/
theorem eq_lift_iff {A : Type*} [Semiring A] (φ : MilnorK k →+* A) (p : A)
    (hp : ∀ x, p * φ x = φ (involute x) * p) (hpp : p * p = φ (ofUnit (-1)) * p)
    (f : SerreAlgebra k →+* A) : f = lift φ p hp hpp ↔ f.comp C = φ ∧ f X = p :=
  ⟨fun h ↦ h ▸ ⟨lift_comp_C .., lift_X ..⟩, fun h ↦ ringHom_ext (by simp [h.1]) (by simp [h.2])⟩

/-! ### The `λ`- and `ρ`-parts -/

/-- The `λ`-part `a + b Π ↦ a`, the ring homomorphism `L(k) → K_*ᴹ(k)` fixing `K_*ᴹ(k)` and killing
`Π`. -/
def fstHom : SerreAlgebra k →+* MilnorK k :=
  lift (RingHom.id _) 0 (by simp) (by simp)

@[simp]
theorem fstHom_apply (x : SerreAlgebra k) : fstHom x = x.fst := by
  simp [fstHom, lift_apply]

@[simp]
theorem fst_pow (x : SerreAlgebra k) (n : ℕ) : (x ^ n).fst = x.fst ^ n := by
  simpa using map_pow fstHom x n

/-- The `ρ`-part `a + b Π ↦ a + b {-1}`, the ring homomorphism `L(k) → K_*ᴹ(k)` fixing
`K_*ᴹ(k)` and sending `Π` to `{-1}`. -/
def rho : SerreAlgebra k →+* MilnorK k :=
  lift (RingHom.id _) (ofUnit (-1)) (ofUnit_mul_eq_involute_mul _) rfl

@[simp]
theorem rho_apply (x : SerreAlgebra k) : rho x = x.fst + x.snd * ofUnit (-1) := by
  simp [rho, lift_apply]

/-! ### Change of the indeterminate -/

/-- The ring endomorphism of `L(k)` fixing `K_*ᴹ(k)` and sending `Π` to `Π - {c}`. -/
private def shiftHom (c : kˣ) : SerreAlgebra k →+* SerreAlgebra k :=
  lift C (X - C (ofUnit c))
    (fun x ↦ by
      ext
      · simpa using ofUnit_mul_involute c (involute x)
      · simp)
    (by
      ext
      · simp only [fst_mul, fst_sub, fst_X, fst_C, zero_sub, mul_neg, neg_mul, neg_neg,
          ofUnit_mul_ofUnit_self]
        rw [ofUnit_mul_ofUnit_comm]
      · simp)

private theorem shiftHom_apply (c : kˣ) (x : SerreAlgebra k) :
    shiftHom c x = ⟨x.fst - x.snd * ofUnit c, x.snd⟩ := by
  ext <;> simp [shiftHom, lift_apply, sub_eq_add_neg]

/-- For `c ∈ kˣ`, the ring automorphism `shift c` of `L(k)` fixing `K_*ᴹ(k)` and sending `Π` to
`Π - {c}`, so `a + b Π ↦ (a - b {c}) + b Π`. Two such automorphisms compose as
`shift c ∘ shift c' = shift (c c')` (`TauCeti.SerreAlgebra.shift_shift`). -/
def shift (c : kˣ) : SerreAlgebra k ≃+* SerreAlgebra k :=
  .ofRingHom (shiftHom c) (shiftHom c⁻¹)
    (RingHom.ext fun x ↦ by ext <;> simp [shiftHom_apply])
    (RingHom.ext fun x ↦ by ext <;> simp [shiftHom_apply])

@[simp]
theorem fst_shift (c : kˣ) (x : SerreAlgebra k) : (shift c x).fst = x.fst - x.snd * ofUnit c := by
  simp [shift, shiftHom_apply]

@[simp]
theorem snd_shift (c : kˣ) (x : SerreAlgebra k) : (shift c x).snd = x.snd := by
  simp [shift, shiftHom_apply]

@[simp]
theorem shift_C (c : kˣ) (a : MilnorK k) : shift c (C a) = C a := by
  ext <;> simp

@[simp]
theorem shift_X (c : kˣ) : shift c X = X - C (ofUnit c) := by
  ext <;> simp

/-- Shifts compose multiplicatively: `shift c (shift c' x) = shift (c c') x`. -/
@[simp]
theorem shift_shift (c c' : kˣ) (x : SerreAlgebra k) : shift c (shift c' x) = shift (c * c') x := by
  ext <;> simp [mul_add, sub_sub, add_comm]

@[simp]
theorem shift_one : shift (1 : kˣ) = RingEquiv.refl (SerreAlgebra k) := by
  ext x <;> simp

@[simp]
theorem shift_symm (c : kˣ) : (shift c).symm = shift c⁻¹ := by
  ext x : 1
  rw [RingEquiv.symm_apply_eq, shift_shift, mul_inv_cancel, shift_one, RingEquiv.refl_apply]

/-! ### Rescaling the indeterminate -/

/-- For `n : ℤ`, the ring endomorphism `rescale n` of `L(k)` fixing `K_*ᴹ(k)` and sending `Π` to
`n Π`, so `a + b Π ↦ a + n b Π`. It respects `Π Π = {-1} Π` because `n²` and `n` have the same
parity while `{-1}` is killed by two. Two rescalings compose as
`rescale m ∘ rescale n = rescale (m n)` (`TauCeti.SerreAlgebra.rescale_rescale`). -/
def rescale (n : ℤ) : SerreAlgebra k →+* SerreAlgebra k :=
  lift C (n • X) (fun x ↦ by rw [smul_mul_assoc, X_mul_C, mul_smul_comm])
    (by
      ext
      · simp
      · simpa [zsmul_eq_mul, Int.cast_comm] using
          zsmul_ofUnit_neg_one_eq_of_even_sub (R := k) (m := n * n) (n := n)
            (by simpa [mul_sub] using Int.even_mul_pred_self n))

@[simp]
theorem fst_rescale (n : ℤ) (x : SerreAlgebra k) : (rescale n x).fst = x.fst := by
  simp [rescale, lift_apply]

@[simp]
theorem snd_rescale (n : ℤ) (x : SerreAlgebra k) : (rescale n x).snd = n • x.snd := by
  simp [rescale, lift_apply, zsmul_eq_mul, Int.cast_comm]

@[simp]
theorem rescale_C (n : ℤ) (a : MilnorK k) : rescale n (C a) = C a := by
  ext <;> simp

@[simp]
theorem rescale_X (n : ℤ) : rescale n X = n • (X : SerreAlgebra k) := by
  ext <;> simp

@[simp]
theorem rescale_one : rescale 1 = RingHom.id (SerreAlgebra k) := by
  ext <;> simp

/-- Rescalings compose multiplicatively: `rescale m (rescale n x) = rescale (m n) x`. -/
@[simp]
theorem rescale_rescale (m n : ℤ) (x : SerreAlgebra k) :
    rescale m (rescale n x) = rescale (m * n) x := by
  ext <;> simp [mul_smul]

/-! ### Functoriality -/

section Map

variable {k' k'' : Type*} [Field k'] [Field k'']

/-- The ring homomorphism `L(k) → L(k')` induced by a field homomorphism `f : k →+* k'`: it acts
as `K_*ᴹ(f)` on both components and fixes `Π`. -/
def map (f : k →+* k') : SerreAlgebra k →+* SerreAlgebra k' :=
  lift (C.comp (MilnorK.map f)) X (fun x ↦ by simp [X_mul_C, map_involute])
    (by
      have : Units.map (f : k →* k') (-1) = -1 := Units.ext (by simp)
      simp [X_mul_X, this])

@[simp]
theorem fst_map (f : k →+* k') (x : SerreAlgebra k) : (map f x).fst = MilnorK.map f x.fst := by
  simp [map, lift_apply]

@[simp]
theorem snd_map (f : k →+* k') (x : SerreAlgebra k) : (map f x).snd = MilnorK.map f x.snd := by
  simp [map, lift_apply]

@[simp]
theorem map_C (f : k →+* k') (a : MilnorK k) : map f (C a) = C (MilnorK.map f a) := by
  ext <;> simp

@[simp]
theorem map_X (f : k →+* k') : map f (X : SerreAlgebra k) = X := by
  ext <;> simp

@[simp]
theorem map_id : map (RingHom.id k) = RingHom.id (SerreAlgebra k) := by
  ext <;> simp

theorem map_comp (g : k' →+* k'') (f : k →+* k') : map (g.comp f) = (map g).comp (map f) := by
  ext <;> simp [MilnorK.map_comp]

end Map

/-! ### The grading -/

variable (k) in
/-- The degree-`n` piece of `L(k)`: `K_0ᴹ(k)` in degree zero, and `K_{n+1}ᴹ(k) ⊕ K_nᴹ(k) Π` in
degree `n + 1`, so that `Π` has degree one. -/
def degree : ℕ → Submodule ℤ (SerreAlgebra k)
  | 0 =>
    { carrier := {x | x.fst ∈ MilnorK.degree k 0 ∧ x.snd = 0}
      add_mem' := fun hx hy ↦ ⟨add_mem hx.1 hy.1, by simp [hx.2, hy.2]⟩
      zero_mem' := ⟨zero_mem _, rfl⟩
      smul_mem' := fun r _ hx ↦ ⟨zsmul_mem hx.1 r, by simp [hx.2]⟩ }
  | n + 1 =>
    { carrier := {x | x.fst ∈ MilnorK.degree k (n + 1) ∧ x.snd ∈ MilnorK.degree k n}
      add_mem' := fun hx hy ↦ ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
      zero_mem' := ⟨zero_mem _, zero_mem _⟩
      smul_mem' := fun r _ hx ↦ ⟨zsmul_mem hx.1 r, zsmul_mem hx.2 r⟩ }

theorem mem_degree_zero {x : SerreAlgebra k} :
    x ∈ degree k 0 ↔ x.fst ∈ MilnorK.degree k 0 ∧ x.snd = 0 :=
  Iff.rfl

theorem mem_degree_succ {n : ℕ} {x : SerreAlgebra k} :
    x ∈ degree k (n + 1) ↔ x.fst ∈ MilnorK.degree k (n + 1) ∧ x.snd ∈ MilnorK.degree k n :=
  Iff.rfl

/-- The `λ`-part is a graded map: it sends `L(k)_n` into `K_nᴹ(k)`. -/
theorem fst_mem_degree {n : ℕ} {x : SerreAlgebra k} (hx : x ∈ degree k n) :
    x.fst ∈ MilnorK.degree k n := by
  cases n with
  | zero => exact (mem_degree_zero.1 hx).1
  | succ n => exact (mem_degree_succ.1 hx).1

theorem C_mem_degree {n : ℕ} {a : MilnorK k} (ha : a ∈ MilnorK.degree k n) :
    C a ∈ degree k n := by
  cases n with
  | zero => exact mem_degree_zero.2 ⟨ha, rfl⟩
  | succ n => exact mem_degree_succ.2 ⟨ha, zero_mem _⟩

theorem X_mem_degree_one : (X : SerreAlgebra k) ∈ degree k 1 :=
  mem_degree_succ.2 ⟨zero_mem _, by rw [snd_X]; exact SetLike.one_mem_graded _⟩

/-- `K_iᴹ(k) K_jᴹ(k) ⊆ K_{i+j}ᴹ(k)`, with the indices rewritten to `n`. -/
private theorem mul_mem_degree_of_add_eq {i j n : ℕ} (h : i + j = n) {a b : MilnorK k}
    (ha : a ∈ MilnorK.degree k i) (hb : b ∈ MilnorK.degree k j) : a * b ∈ MilnorK.degree k n :=
  h ▸ SetLike.mul_mem_graded ha hb

private theorem mul_mem_degree {i j : ℕ} {x y : SerreAlgebra k} (hx : x ∈ degree k i)
    (hy : y ∈ degree k j) : x * y ∈ degree k (i + j) := by
  cases i with
  | zero =>
    obtain ⟨hx₁, hx₂⟩ := mem_degree_zero.1 hx
    cases j with
    | zero =>
      obtain ⟨hy₁, hy₂⟩ := mem_degree_zero.1 hy
      exact mem_degree_zero.2 ⟨SetLike.mul_mem_graded hx₁ hy₁, by simp [hx₂, hy₂]⟩
    | succ j =>
      obtain ⟨hy₁, hy₂⟩ := mem_degree_succ.1 hy
      rw [zero_add, mem_degree_succ]
      refine ⟨mul_mem_degree_of_add_eq (zero_add _) hx₁ hy₁, ?_⟩
      simpa [hx₂] using mul_mem_degree_of_add_eq (zero_add _) hx₁ hy₂
  | succ i =>
    obtain ⟨hx₁, hx₂⟩ := mem_degree_succ.1 hx
    cases j with
    | zero =>
      obtain ⟨hy₁, hy₂⟩ := mem_degree_zero.1 hy
      rw [add_zero, mem_degree_succ]
      refine ⟨mul_mem_degree_of_add_eq (add_zero _) hx₁ hy₁, ?_⟩
      simpa [hy₂] using mul_mem_degree_of_add_eq (add_zero _) hx₂ (involute_mem_degree hy₁)
    | succ j =>
      obtain ⟨hy₁, hy₂⟩ := mem_degree_succ.1 hy
      rw [show i + 1 + (j + 1) = i + j + 1 + 1 by omega, mem_degree_succ, snd_mul]
      refine ⟨mul_mem_degree_of_add_eq (by omega) hx₁ hy₁, add_mem (add_mem
        (mul_mem_degree_of_add_eq (by omega) hx₁ hy₂)
        (mul_mem_degree_of_add_eq (by omega) hx₂ (involute_mem_degree hy₁)))
        (mul_mem_degree_of_add_eq rfl (SetLike.mul_mem_graded hx₂ (involute_mem_degree hy₂))
          (ofUnit_mem_degree_one _))⟩

/-- The degree submodules make `L(k)` a graded monoid. -/
instance instGradedMonoidDegree : SetLike.GradedMonoid (degree k) where
  one_mem := C_mem_degree (SetLike.one_mem_graded _)
  mul_mem _ _ _ _ := mul_mem_degree

/-- Degree zero of `L(k)` is degree zero of `K_*ᴹ(k)`, embedded by `C`. -/
def degreeZeroEquiv : degree k 0 ≃ₗ[ℤ] MilnorK.degree k 0 where
  toFun x := ⟨x.val.fst, (mem_degree_zero.1 x.property).1⟩
  invFun a := ⟨C a.val, C_mem_degree a.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := Subtype.ext <| SerreAlgebra.ext rfl (mem_degree_zero.1 x.property).2.symm
  right_inv _ := rfl

@[simp]
theorem coe_degreeZeroEquiv (x : degree k 0) : (degreeZeroEquiv x : MilnorK k) = x.val.fst :=
  (rfl)

@[simp]
theorem coe_degreeZeroEquiv_symm (a : MilnorK.degree k 0) :
    (degreeZeroEquiv.symm a : SerreAlgebra k) = C a.val :=
  (rfl)

/-- Degree `n + 1` of `L(k)` is `K_{n+1}ᴹ(k) ⊕ K_nᴹ(k)`, through `(a, b) ↦ a + b Π`. -/
def degreeSuccEquiv (n : ℕ) :
    degree k (n + 1) ≃ₗ[ℤ] MilnorK.degree k (n + 1) × MilnorK.degree k n where
  toFun x := (⟨x.val.fst, (mem_degree_succ.1 x.property).1⟩,
    ⟨x.val.snd, (mem_degree_succ.1 x.property).2⟩)
  invFun a := ⟨⟨a.1.val, a.2.val⟩, mem_degree_succ.2 ⟨a.1.property, a.2.property⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_degreeSuccEquiv_fst (n : ℕ) (x : degree k (n + 1)) :
    ((degreeSuccEquiv n x).1 : MilnorK k) = x.val.fst :=
  (rfl)

@[simp]
theorem coe_degreeSuccEquiv_snd (n : ℕ) (x : degree k (n + 1)) :
    ((degreeSuccEquiv n x).2 : MilnorK k) = x.val.snd :=
  (rfl)

@[simp]
theorem coe_degreeSuccEquiv_symm (n : ℕ) (a : MilnorK.degree k (n + 1) × MilnorK.degree k n) :
    ((degreeSuccEquiv n).symm a : SerreAlgebra k) = C a.1.val + C a.2.val * X := by
  rw [C_add_C_mul_X]
  rfl

/-- The `ρ`-part is a graded map: it sends `L(k)_n` into `K_nᴹ(k)`. -/
theorem rho_mem_degree {n : ℕ} {x : SerreAlgebra k} (hx : x ∈ degree k n) :
    rho x ∈ MilnorK.degree k n := by
  cases n with
  | zero =>
    obtain ⟨ha, hb⟩ := mem_degree_zero.1 hx
    simpa [hb] using ha
  | succ n =>
    obtain ⟨ha, hb⟩ := mem_degree_succ.1 hx
    rw [rho_apply]
    exact add_mem ha (SetLike.mul_mem_graded hb (ofUnit_mem_degree_one _))

/-- The automorphism `shift c` preserves the grading. -/
theorem shift_mem_degree (c : kˣ) {n : ℕ} {x : SerreAlgebra k} (hx : x ∈ degree k n) :
    shift c x ∈ degree k n := by
  cases n with
  | zero =>
    obtain ⟨ha, hb⟩ := mem_degree_zero.1 hx
    exact mem_degree_zero.2 ⟨by simpa [hb] using ha, by simpa using hb⟩
  | succ n =>
    obtain ⟨ha, hb⟩ := mem_degree_succ.1 hx
    exact mem_degree_succ.2
      ⟨by simpa using sub_mem ha (SetLike.mul_mem_graded hb (ofUnit_mem_degree_one c)),
        by simpa using hb⟩

/-- The endomorphism `rescale n` preserves the grading. -/
theorem rescale_mem_degree (m : ℤ) {n : ℕ} {x : SerreAlgebra k} (hx : x ∈ degree k n) :
    rescale m x ∈ degree k n := by
  cases n with
  | zero =>
    obtain ⟨ha, hb⟩ := mem_degree_zero.1 hx
    exact mem_degree_zero.2 ⟨by simpa using ha, by simp [hb]⟩
  | succ n =>
    obtain ⟨ha, hb⟩ := mem_degree_succ.1 hx
    exact mem_degree_succ.2 ⟨by simpa using ha, by simpa using zsmul_mem hb m⟩

/-- The maps induced by field homomorphisms preserve the grading. -/
theorem map_mem_degree {k' : Type*} [Field k'] (f : k →+* k') {n : ℕ} {x : SerreAlgebra k}
    (hx : x ∈ degree k n) : map f x ∈ degree k' n := by
  cases n with
  | zero =>
    obtain ⟨ha, hb⟩ := mem_degree_zero.1 hx
    exact mem_degree_zero.2 ⟨by simpa using MilnorK.map_mem_degree f ha, by simp [hb]⟩
  | succ n =>
    obtain ⟨ha, hb⟩ := mem_degree_succ.1 hx
    exact mem_degree_succ.2
      ⟨by simpa using MilnorK.map_mem_degree f ha, by simpa using MilnorK.map_mem_degree f hb⟩

/-! ### Graded commutativity -/

/-- A sign does not change an element of the form `z w {-1}`, which has order dividing two. -/
private theorem neg_one_pow_mul_mul_ofUnit_neg_one (N : ℕ) (z w : MilnorK k) :
    (-1) ^ N * (z * (w * ofUnit (-1))) = z * (w * ofUnit (-1)) := by
  rcases neg_one_pow_eq_or (MilnorK k) N with h | h
  · rw [h, one_mul]
  · rw [h, neg_one_mul, ← mul_neg, ← mul_neg, neg_ofUnit_neg_one]

/-- **Graded commutativity** of Serre's algebra: for `x ∈ L(k)_m` and `y ∈ L(k)_n`,
`x y = (-1) ^ (m n) y x`. -/
theorem mul_comm_of_mem_degree {m n : ℕ} {x y : SerreAlgebra k} (hx : x ∈ degree k m)
    (hy : y ∈ degree k n) : x * y = (-1) ^ (m * n) * (y * x) := by
  have hs : ((-1) ^ (m * n) : SerreAlgebra k) = C ((-1) ^ (m * n)) := by simp
  rw [hs]
  ext
  · simpa using MilnorK.mul_comm_of_mem_degree (fst_mem_degree hx) (fst_mem_degree hy)
  simp only [snd_mul, fst_mul, fst_C, snd_C, zero_mul, add_zero]
  cases m with
  | zero =>
    obtain ⟨ha, hb⟩ := mem_degree_zero.1 hx
    cases n with
    | zero => simp [hb, (mem_degree_zero.1 hy).2]
    | succ j =>
      obtain ⟨-, hd⟩ := mem_degree_succ.1 hy
      simpa [hb, involute_of_mem_degree ha] using MilnorK.mul_comm_of_mem_degree ha hd
  | succ i =>
    obtain ⟨ha, hb⟩ := mem_degree_succ.1 hx
    cases n with
    | zero =>
      obtain ⟨hc, hd⟩ := mem_degree_zero.1 hy
      simpa [hd, involute_of_mem_degree hc] using MilnorK.mul_comm_of_mem_degree hb hc
    | succ j =>
      obtain ⟨hc, hd⟩ := mem_degree_succ.1 hy
      have hdb : y.snd * x.snd = (-1) ^ (j * i) * (x.snd * y.snd) :=
        MilnorK.mul_comm_of_mem_degree hd hb
      -- Write every term as a sign times one of `y.snd x.fst`, `x.snd y.fst` or
      -- `x.snd y.snd {-1}`; the last kind is insensitive to signs, and the signs of the other two
      -- agree modulo two.
      rw [involute_of_mem_degree ha, involute_of_mem_degree hb, involute_of_mem_degree hc,
        involute_of_mem_degree hd, MilnorK.mul_comm_of_mem_degree ha hd,
        MilnorK.mul_comm_of_mem_degree hc hb]
      simp only [mul_assoc, mul_add (R := MilnorK k), mul_neg_one_pow_mul x.snd,
        mul_neg_one_pow_mul y.snd]
      rw [← mul_assoc y.snd x.snd, hdb]
      simp only [mul_assoc, neg_one_pow_mul_mul_ofUnit_neg_one]
      simp only [← mul_assoc, ← pow_add]
      rw [show (i + 1) * (j + 1) + (i + 1) = (i + 1) * j + 2 * (i + 1) by ring,
        show (i + 1) * (j + 1) + (j + 1) * i = (j + 1) + 2 * (i * (j + 1)) by ring,
        neg_one_pow_add_two_mul, neg_one_pow_add_two_mul]
      abel

end SerreAlgebra

end TauCeti
