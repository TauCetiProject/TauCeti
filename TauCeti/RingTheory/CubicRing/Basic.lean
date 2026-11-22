/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CubicDiscriminant
public import Mathlib.RingTheory.Discriminant

/-!
# The cubic ring of a binary cubic form

To a binary cubic form `f(x, y) = a x³ + b x² y + c x y² + d y³` over a commutative ring `R`,
recorded by its coefficients `f : Cubic R`, the Delone–Faddeev–Gan–Gross–Savin construction
attaches a commutative `R`-algebra `R(f)`, free of rank three with basis `⟨1, ω, θ⟩` and
multiplication

  `ω θ = -a d`,  `ω² = -a c + b ω - a θ`,  `θ² = -b d + d ω - c θ`.

This is the multiplication table in the sign convention of Gross–Lucianovic and Wood. It is the
carrier on which binary cubic forms and cubic rings are compared: the Delone–Faddeev
correspondence matches cubic rings with a basis containing `1` to binary cubic forms, `R(f)`
being the ring matched to `f`, and arithmetic properties of `f` (irreducibility, nonvanishing
discriminant, maximality at a prime) are read off `R(f)`. No form is excluded: the
zero form gives the square-zero algebra in which all products of `ω` and `θ` vanish, and the
construction divides by neither `2` nor `3`.

The negated basis `⟨1, -ω, -θ⟩` has the table

  `ω θ = -a d`,  `ω² = -a c - b ω + a θ`,  `θ² = -b d - d ω + c θ`,

which is the convention of Bhargava, Shankar and Tsimerman. The two
bases span the same algebra, so both conventions are available on one carrier.

The discriminant of `R(f)` with respect to either basis is the discriminant of the form,
`b²c² - 4ac³ - 4b³d - 27a²d² + 18abcd`, which is Mathlib's `Cubic.discr f`. Thus `R(f)` is a
rank-three algebra whose trace discriminant is the classical discriminant of `f`.

## Main definitions

* `Cubic.CubicRing f`: the cubic ring of the form `f`, with its `CommRing` and `Algebra` structures.
* `Cubic.CubicRing.omega`, `Cubic.CubicRing.theta`: the basis elements `ω` and `θ`.
* `Cubic.CubicRing.basis`: the normal basis `⟨1, ω, θ⟩`.
* `Cubic.CubicRing.negBasis`: the negated basis `⟨1, -ω, -θ⟩`.
* `Cubic.CubicRing.lift`: algebra homomorphisms out of `R(f)` correspond to pairs of elements
  satisfying the multiplication table.
* `Cubic.CubicRing.mapRingHom`: the ring homomorphism `R(f) → S(f_S)` induced by `R →+* S`.

## Main results

* `Cubic.CubicRing.omega_mul_theta`, `Cubic.CubicRing.omega_mul_omega`,
  `Cubic.CubicRing.theta_mul_theta`: the multiplication table.
* `Cubic.CubicRing.finrank_eq_three`: `R(f)` has rank three.
* `Cubic.CubicRing.trace_apply`: the trace of `c₀ + c₁ ω + c₂ θ` is `3 c₀ + b c₁ - c c₂`.
* `Cubic.CubicRing.discr_basis`, `Cubic.CubicRing.discr_negBasis`: the discriminant of `R(f)` in
  either basis is `Cubic.discr f`.

## Implementation notes

An element is stored by its three coordinates in the basis `⟨1, ω, θ⟩`, as Mathlib's
`QuadraticAlgebra` stores an element by its coordinates in `⟨1, ω⟩`. The algebraic structure is
exposed, so that the `Algebra ℤ` and `Algebra ℕ` instances built here agree definitionally with
Mathlib's `Ring.toIntAlgebra` and `Semiring.toNatAlgebra`; this matters for `R = ℤ`, the case of
cubic rings.

## References

* B. N. Delone and D. K. Faddeev, *The theory of irrationalities of the third degree*, Transl.
  Math. Monogr. 10, AMS (1964).
* W. T. Gan, B. Gross and G. Savin, *Fourier coefficients of modular forms on `G₂`*, Duke Math. J.
  115 (2002), §4.
* B. H. Gross and M. W. Lucianovic, *On cubic rings and quaternion rings*, J. Number Theory 129
  (2009), §2.
* M. M. Wood, *Parametrizing quartic algebras over an arbitrary base*, Algebra Number Theory 5
  (2011), §2, Theorem 2.1 and the explicit construction.
* M. Bhargava, A. Shankar and J. Tsimerman, *On the Davenport–Heilbronn theorems and second order
  terms*, Invent. Math. 193 (2013), §2, (9)–(12).
-/

@[expose] public section

namespace Cubic

variable {R S : Type*}

/-- The **cubic ring** `R(f)` of a binary cubic form `f = a x³ + b x² y + c x y² + d y³`: the free
`R`-module with basis `⟨1, ω, θ⟩`, with the multiplication `ω θ = -a d`,
`ω² = -a c + b ω - a θ` and `θ² = -b d + d ω - c θ`. An element `c₀ + c₁ ω + c₂ θ` is recorded by
its three coordinates. -/
@[ext]
structure CubicRing (f : Cubic R) where
  /-- The coordinate of an element of `R(f)` along `1`. -/
  c₀ : R
  /-- The coordinate of an element of `R(f)` along `ω`. -/
  c₁ : R
  /-- The coordinate of an element of `R(f)` along `θ`. -/
  c₂ : R

namespace CubicRing

variable {f : Cubic R}

/-! ### The additive and module structure -/

instance [Zero R] : Zero f.CubicRing := ⟨⟨0, 0, 0⟩⟩

@[simp] theorem c₀_zero [Zero R] : (0 : f.CubicRing).c₀ = 0 := (rfl)
@[simp] theorem c₁_zero [Zero R] : (0 : f.CubicRing).c₁ = 0 := (rfl)
@[simp] theorem c₂_zero [Zero R] : (0 : f.CubicRing).c₂ = 0 := (rfl)

instance [Zero R] : Inhabited f.CubicRing := ⟨0⟩

instance [Zero R] [One R] : One f.CubicRing := ⟨⟨1, 0, 0⟩⟩

@[simp] theorem c₀_one [Zero R] [One R] : (1 : f.CubicRing).c₀ = 1 := (rfl)
@[simp] theorem c₁_one [Zero R] [One R] : (1 : f.CubicRing).c₁ = 0 := (rfl)
@[simp] theorem c₂_one [Zero R] [One R] : (1 : f.CubicRing).c₂ = 0 := (rfl)

instance [Add R] : Add f.CubicRing := ⟨fun x y => ⟨x.c₀ + y.c₀, x.c₁ + y.c₁, x.c₂ + y.c₂⟩⟩

@[simp] theorem c₀_add [Add R] (x y : f.CubicRing) : (x + y).c₀ = x.c₀ + y.c₀ := (rfl)
@[simp] theorem c₁_add [Add R] (x y : f.CubicRing) : (x + y).c₁ = x.c₁ + y.c₁ := (rfl)
@[simp] theorem c₂_add [Add R] (x y : f.CubicRing) : (x + y).c₂ = x.c₂ + y.c₂ := (rfl)

instance [Neg R] : Neg f.CubicRing := ⟨fun x => ⟨-x.c₀, -x.c₁, -x.c₂⟩⟩

@[simp] theorem c₀_neg [Neg R] (x : f.CubicRing) : (-x).c₀ = -x.c₀ := (rfl)
@[simp] theorem c₁_neg [Neg R] (x : f.CubicRing) : (-x).c₁ = -x.c₁ := (rfl)
@[simp] theorem c₂_neg [Neg R] (x : f.CubicRing) : (-x).c₂ = -x.c₂ := (rfl)

instance [Sub R] : Sub f.CubicRing := ⟨fun x y => ⟨x.c₀ - y.c₀, x.c₁ - y.c₁, x.c₂ - y.c₂⟩⟩

@[simp] theorem c₀_sub [Sub R] (x y : f.CubicRing) : (x - y).c₀ = x.c₀ - y.c₀ := (rfl)
@[simp] theorem c₁_sub [Sub R] (x y : f.CubicRing) : (x - y).c₁ = x.c₁ - y.c₁ := (rfl)
@[simp] theorem c₂_sub [Sub R] (x y : f.CubicRing) : (x - y).c₂ = x.c₂ - y.c₂ := (rfl)

instance [SMul S R] : SMul S f.CubicRing := ⟨fun s x => ⟨s • x.c₀, s • x.c₁, s • x.c₂⟩⟩

@[simp] theorem c₀_smul [SMul S R] (s : S) (x : f.CubicRing) : (s • x).c₀ = s • x.c₀ := (rfl)
@[simp] theorem c₁_smul [SMul S R] (s : S) (x : f.CubicRing) : (s • x).c₁ = s • x.c₁ := (rfl)
@[simp] theorem c₂_smul [SMul S R] (s : S) (x : f.CubicRing) : (s • x).c₂ = s • x.c₂ := (rfl)

/-- The coordinates of an element of `R(f)`, as an additive isomorphism with `R × R × R`. The
additive and module structures of `R(f)` are transported along it. -/
def addEquivProd (f : Cubic R) [Add R] : f.CubicRing ≃+ R × R × R where
  toFun x := (x.c₀, x.c₁, x.c₂)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp] theorem addEquivProd_apply [Add R] (x : f.CubicRing) :
    addEquivProd f x = (x.c₀, x.c₁, x.c₂) := (rfl)

@[simp] theorem addEquivProd_symm_apply [Add R] (p : R × R × R) :
    (addEquivProd f).symm p = ⟨p.1, p.2.1, p.2.2⟩ := (rfl)

instance [AddCommMonoid R] : AddCommMonoid f.CubicRing := by
  apply (addEquivProd f).injective.addCommMonoid <;> intros <;> rfl

instance [AddCommGroup R] : AddCommGroup f.CubicRing := by
  apply (addEquivProd f).injective.addCommGroup <;> intros <;> rfl

instance [Monoid S] [AddCommMonoid R] [DistribMulAction S R] : DistribMulAction S f.CubicRing :=
  (addEquivProd f).injective.distribMulAction (addEquivProd f).toAddMonoidHom fun _ _ => rfl

instance [Semiring S] [AddCommMonoid R] [Module S R] : Module S f.CubicRing :=
  (addEquivProd f).injective.module _ (addEquivProd f).toAddMonoidHom fun _ _ => rfl

/-! ### The ring structure -/

section CommRing

variable [CommRing R]

instance : Mul f.CubicRing where
  mul x y :=
    ⟨x.c₀ * y.c₀ - f.a * f.c * (x.c₁ * y.c₁) - f.a * f.d * (x.c₁ * y.c₂ + x.c₂ * y.c₁) -
        f.b * f.d * (x.c₂ * y.c₂),
      x.c₀ * y.c₁ + x.c₁ * y.c₀ + f.b * (x.c₁ * y.c₁) + f.d * (x.c₂ * y.c₂),
      x.c₀ * y.c₂ + x.c₂ * y.c₀ - f.a * (x.c₁ * y.c₁) - f.c * (x.c₂ * y.c₂)⟩

@[simp] theorem c₀_mul (x y : f.CubicRing) :
    (x * y).c₀ = x.c₀ * y.c₀ - f.a * f.c * (x.c₁ * y.c₁) -
      f.a * f.d * (x.c₁ * y.c₂ + x.c₂ * y.c₁) - f.b * f.d * (x.c₂ * y.c₂) := (rfl)

@[simp] theorem c₁_mul (x y : f.CubicRing) :
    (x * y).c₁ = x.c₀ * y.c₁ + x.c₁ * y.c₀ + f.b * (x.c₁ * y.c₁) + f.d * (x.c₂ * y.c₂) := (rfl)

@[simp] theorem c₂_mul (x y : f.CubicRing) :
    (x * y).c₂ = x.c₀ * y.c₂ + x.c₂ * y.c₀ - f.a * (x.c₁ * y.c₁) - f.c * (x.c₂ * y.c₂) := (rfl)

instance : AddCommGroupWithOne f.CubicRing where
  natCast n := ⟨n, 0, 0⟩
  natCast_zero := CubicRing.ext Nat.cast_zero rfl rfl
  natCast_succ n := CubicRing.ext (Nat.cast_succ n) (add_zero 0).symm (add_zero 0).symm
  intCast n := ⟨n, 0, 0⟩
  intCast_ofNat n := CubicRing.ext (Int.cast_natCast n) rfl rfl
  intCast_negSucc n := CubicRing.ext (Int.cast_negSucc n) neg_zero.symm neg_zero.symm

@[simp, norm_cast] theorem c₀_natCast (n : ℕ) : (n : f.CubicRing).c₀ = n := (rfl)
@[simp, norm_cast] theorem c₁_natCast (n : ℕ) : (n : f.CubicRing).c₁ = 0 := (rfl)
@[simp, norm_cast] theorem c₂_natCast (n : ℕ) : (n : f.CubicRing).c₂ = 0 := (rfl)

@[simp, norm_cast] theorem c₀_intCast (n : ℤ) : (n : f.CubicRing).c₀ = n := (rfl)
@[simp, norm_cast] theorem c₁_intCast (n : ℤ) : (n : f.CubicRing).c₁ = 0 := (rfl)
@[simp, norm_cast] theorem c₂_intCast (n : ℤ) : (n : f.CubicRing).c₂ = 0 := (rfl)

@[simp] theorem c₀_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : f.CubicRing).c₀ = ofNat(n) := (rfl)
@[simp] theorem c₁_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : f.CubicRing).c₁ = 0 := (rfl)
@[simp] theorem c₂_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : f.CubicRing).c₂ = 0 := (rfl)

instance : CommRing f.CubicRing where
  left_distrib _ _ _ := by ext <;> simp <;> ring
  right_distrib _ _ _ := by ext <;> simp <;> ring
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp
  mul_assoc _ _ _ := by ext <;> simp <;> ring
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp
  mul_comm _ _ := by ext <;> simp <;> ring

instance [CommSemiring S] [Algebra S R] : Algebra S f.CubicRing where
  algebraMap.toFun s := ⟨algebraMap S R s, 0, 0⟩
  algebraMap.map_one' := by ext <;> simp
  algebraMap.map_mul' _ _ := by ext <;> simp
  algebraMap.map_zero' := by ext <;> simp
  algebraMap.map_add' _ _ := by ext <;> simp
  commutes' _ _ := by ext <;> simp [mul_comm]
  smul_def' _ _ := by ext <;> simp [Algebra.smul_def]

end CommRing

end CubicRing

end Cubic

end

public section

namespace Cubic.CubicRing

variable {R : Type*} {f : Cubic R}

instance [Nontrivial R] : Nontrivial f.CubicRing :=
  let ⟨x, y, h⟩ := exists_pair_ne R
  ⟨⟨⟨x, x, x⟩, ⟨y, y, y⟩, fun e => h (congrArg c₀ e)⟩⟩

section CommRing

variable [CommRing R]

@[simp] theorem c₀_algebraMap (r : R) : (algebraMap R f.CubicRing r).c₀ = r := (rfl)
@[simp] theorem c₁_algebraMap (r : R) : (algebraMap R f.CubicRing r).c₁ = 0 := (rfl)
@[simp] theorem c₂_algebraMap (r : R) : (algebraMap R f.CubicRing r).c₂ = 0 := (rfl)

theorem algebraMap_injective : Function.Injective (algebraMap R f.CubicRing) :=
  fun _ _ h => congrArg c₀ h

/-! ### The basis elements `ω` and `θ` and the multiplication table -/

/-- The basis element `ω` of the cubic ring `R(f)`. -/
def omega : f.CubicRing := ⟨0, 1, 0⟩

/-- The basis element `θ` of the cubic ring `R(f)`. -/
def theta : f.CubicRing := ⟨0, 0, 1⟩

@[simp] theorem c₀_omega : (omega : f.CubicRing).c₀ = 0 := (rfl)
@[simp] theorem c₁_omega : (omega : f.CubicRing).c₁ = 1 := (rfl)
@[simp] theorem c₂_omega : (omega : f.CubicRing).c₂ = 0 := (rfl)

@[simp] theorem c₀_theta : (theta : f.CubicRing).c₀ = 0 := (rfl)
@[simp] theorem c₁_theta : (theta : f.CubicRing).c₁ = 0 := (rfl)
@[simp] theorem c₂_theta : (theta : f.CubicRing).c₂ = 1 := (rfl)

/-- The product `ω θ` is the scalar `-a d`. -/
theorem omega_mul_theta : (omega : f.CubicRing) * theta = algebraMap R _ (-(f.a * f.d)) := by
  ext <;> simp

/-- `ω² = -a c + b ω - a θ`. -/
theorem omega_mul_omega :
    (omega : f.CubicRing) * omega = algebraMap R _ (-(f.a * f.c)) + f.b • omega - f.a • theta := by
  ext <;> simp

/-- `θ² = -b d + d ω - c θ`. -/
theorem theta_mul_theta :
    (theta : f.CubicRing) * theta = algebraMap R _ (-(f.b * f.d)) + f.d • omega - f.c • theta := by
  ext <;> simp

/-- An element of `R(f)` is `c₀ + c₁ ω + c₂ θ` in terms of its coordinates. -/
theorem algebraMap_add_smul_add_smul (x : f.CubicRing) :
    algebraMap R _ x.c₀ + x.c₁ • omega + x.c₂ • theta = x := by
  ext <;> simp

theorem mk_eq_algebraMap_add_smul_add_smul (x y z : R) :
    (⟨x, y, z⟩ : f.CubicRing) = algebraMap R _ x + y • omega + z • theta := by
  ext <;> simp

/-! ### The normal basis -/

/-- The coordinates of an element of `R(f)` in the basis `⟨1, ω, θ⟩`, as a linear isomorphism
with `Fin 3 → R`. -/
def linearEquivTuple (f : Cubic R) : f.CubicRing ≃ₗ[R] (Fin 3 → R) where
  toFun x := ![x.c₀, x.c₁, x.c₂]
  invFun v := ⟨v 0, v 1, v 2⟩
  left_inv _ := rfl
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

@[simp] theorem linearEquivTuple_apply (x : f.CubicRing) :
    linearEquivTuple f x = ![x.c₀, x.c₁, x.c₂] := (rfl)

@[simp] theorem linearEquivTuple_symm_apply (v : Fin 3 → R) :
    (linearEquivTuple f).symm v = ⟨v 0, v 1, v 2⟩ := (rfl)

/-- The **normal basis** `⟨1, ω, θ⟩` of the cubic ring `R(f)`. -/
noncomputable def basis (f : Cubic R) : Module.Basis (Fin 3) R f.CubicRing :=
  .ofEquivFun (linearEquivTuple f)

@[simp] theorem basis_repr_apply (x : f.CubicRing) :
    (basis f).repr x = ![x.c₀, x.c₁, x.c₂] := (rfl)

@[simp] theorem basis_zero : basis f 0 = 1 := by
  ext <;> simp [basis]

@[simp] theorem basis_one : basis f 1 = omega := by
  ext <;> simp [basis]

@[simp] theorem basis_two : basis f 2 = theta := by
  ext <;> simp [basis]

instance : Module.Free R f.CubicRing := .of_basis (basis f)

instance : Module.Finite R f.CubicRing := .of_basis (basis f)

/-- The cubic ring of a form over a nontrivial ring has rank three. -/
theorem finrank_eq_three [Nontrivial R] : Module.finrank R f.CubicRing = 3 := by
  simp [Module.finrank_eq_card_basis (basis f)]

/-! ### The negated basis -/

/-- The **negated basis** `⟨1, -ω, -θ⟩` of the cubic ring `R(f)`. In it the multiplication table
is that of Bhargava, Shankar and Tsimerman: see `CubicRing.neg_omega_mul_neg_theta`,
`CubicRing.neg_omega_mul_neg_omega` and `CubicRing.neg_theta_mul_neg_theta`. -/
noncomputable def negBasis (f : Cubic R) : Module.Basis (Fin 3) R f.CubicRing :=
  (basis f).unitsSMul ![1, -1, -1]

@[simp] theorem negBasis_zero : negBasis f 0 = 1 := by
  simp [negBasis, Module.Basis.unitsSMul_apply]

@[simp] theorem negBasis_one : negBasis f 1 = -omega := by
  simp [negBasis, Module.Basis.unitsSMul_apply]

@[simp] theorem negBasis_two : negBasis f 2 = -theta := by
  simp [negBasis, Module.Basis.unitsSMul_apply]

/-- In the negated basis, `(-ω)(-θ) = -a d`. -/
theorem neg_omega_mul_neg_theta :
    (-omega : f.CubicRing) * -theta = algebraMap R _ (-(f.a * f.d)) := by
  rw [neg_mul_neg, omega_mul_theta]

/-- In the negated basis, `(-ω)² = -a c - b (-ω) + a (-θ)`. -/
theorem neg_omega_mul_neg_omega :
    (-omega : f.CubicRing) * -omega =
      algebraMap R _ (-(f.a * f.c)) - f.b • -omega + f.a • -theta := by
  rw [neg_mul_neg, omega_mul_omega, smul_neg, smul_neg, sub_neg_eq_add, ← sub_eq_add_neg]

/-- In the negated basis, `(-θ)² = -b d - d (-ω) + c (-θ)`. -/
theorem neg_theta_mul_neg_theta :
    (-theta : f.CubicRing) * -theta =
      algebraMap R _ (-(f.b * f.d)) - f.d • -omega + f.c • -theta := by
  rw [neg_mul_neg, theta_mul_theta, smul_neg, smul_neg, sub_neg_eq_add, ← sub_eq_add_neg]

/-! ### The universal property -/

/-- Two `R`-algebra homomorphisms out of `R(f)` agreeing on `ω` and `θ` are equal. -/
@[ext]
theorem algHom_ext {A : Type*} [Semiring A] [Algebra R A] {φ ψ : f.CubicRing →ₐ[R] A}
    (hω : φ omega = ψ omega) (hθ : φ theta = ψ theta) : φ = ψ := by
  ext x
  rw [← algebraMap_add_smul_add_smul x]
  simp [hω, hθ]

section lift

variable {A : Type*} [CommRing A] [Algebra R A]

/-- The pairs `(u, v)` of elements of an `R`-algebra satisfying the multiplication table of
`R(f)`: `u v = -a d`, `u² = -a c + b u - a v` and `v² = -b d + d u - c v`. -/
def IsMulTable (f : Cubic R) (u v : A) : Prop :=
  u * v = algebraMap R A (-(f.a * f.d)) ∧
    u * u = algebraMap R A (-(f.a * f.c)) + f.b • u - f.a • v ∧
    v * v = algebraMap R A (-(f.b * f.d)) + f.d • u - f.c • v

theorem isMulTable_omega_theta : IsMulTable f (omega : f.CubicRing) theta :=
  ⟨omega_mul_theta, omega_mul_omega, theta_mul_theta⟩

/-- An `R`-algebra homomorphism carries a pair satisfying the multiplication table of `R(f)` to
another such pair. -/
theorem IsMulTable.map {B : Type*} [CommRing B] [Algebra R B] {u v : A} (h : IsMulTable f u v)
    (φ : A →ₐ[R] B) : IsMulTable f (φ u) (φ v) := by
  obtain ⟨huv, huu, hvv⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> simp [← map_mul, huv, huu, hvv]

/-- The `R`-algebra homomorphism `R(f) → A` sending `ω` to `u` and `θ` to `v`, for `u` and `v`
satisfying the multiplication table of `R(f)`. -/
def liftHom {u v : A} (h : IsMulTable f u v) : f.CubicRing →ₐ[R] A where
  toFun x := algebraMap R A x.c₀ + x.c₁ • u + x.c₂ • v
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by simp only [c₀_add, c₁_add, c₂_add, map_add, add_smul]; abel
  map_mul' x y := by
    obtain ⟨huv, huu, hvv⟩ := h
    simp only [Algebra.smul_def, c₀_mul, c₁_mul, c₂_mul, map_add, map_sub, map_mul, map_neg]
      at huv huu hvv ⊢
    linear_combination -(algebraMap R A x.c₁ * algebraMap R A y.c₁) * huu -
      (algebraMap R A x.c₁ * algebraMap R A y.c₂ + algebraMap R A x.c₂ * algebraMap R A y.c₁) *
        huv - (algebraMap R A x.c₂ * algebraMap R A y.c₂) * hvv
  commutes' r := by simp

theorem liftHom_apply {u v : A} (h : IsMulTable f u v) (x : f.CubicRing) :
    liftHom h x = algebraMap R A x.c₀ + x.c₁ • u + x.c₂ • v := (rfl)

@[simp] theorem liftHom_omega {u v : A} (h : IsMulTable f u v) : liftHom h omega = u := by
  simp [liftHom_apply]

@[simp] theorem liftHom_theta {u v : A} (h : IsMulTable f u v) : liftHom h theta = v := by
  simp [liftHom_apply]

/-- The **universal property** of the cubic ring: `R`-algebra homomorphisms `R(f) → A` correspond
to the pairs `(u, v)` in `A` satisfying its multiplication table, by sending `ω` to `u` and `θ`
to `v`. -/
def lift : {p : A × A // IsMulTable f p.1 p.2} ≃ (f.CubicRing →ₐ[R] A) where
  toFun p := liftHom p.property
  invFun φ := ⟨(φ omega, φ theta), isMulTable_omega_theta.map φ⟩
  left_inv p := by simp
  right_inv φ := by ext <;> simp

@[simp] theorem lift_apply (p : {p : A × A // IsMulTable f p.1 p.2}) :
    lift p = liftHom p.property := (rfl)

@[simp] theorem lift_symm_apply_coe (φ : f.CubicRing →ₐ[R] A) :
    (lift.symm φ : A × A) = (φ omega, φ theta) := (rfl)

end lift

/-! ### Base change -/

section map

variable {S : Type*} [CommRing S] (φ : R →+* S)

/-- The ring homomorphism `R(f) → S(f_S)` induced by a ring homomorphism `φ : R →+* S`, where
`f_S = f.map φ` is the form with its coefficients mapped by `φ`. It applies `φ` to each
coordinate, so it sends `ω` and `θ` to `ω` and `θ`. -/
def mapRingHom (f : Cubic R) : f.CubicRing →+* (f.map φ).CubicRing where
  toFun x := ⟨φ x.c₀, φ x.c₁, φ x.c₂⟩
  map_one' := by ext <;> simp
  map_mul' _ _ := by ext <;> simp <;> simp [Cubic.map]
  map_zero' := by ext <;> simp
  map_add' _ _ := by ext <;> simp

@[simp] theorem c₀_mapRingHom (x : f.CubicRing) : (mapRingHom φ f x).c₀ = φ x.c₀ := (rfl)
@[simp] theorem c₁_mapRingHom (x : f.CubicRing) : (mapRingHom φ f x).c₁ = φ x.c₁ := (rfl)
@[simp] theorem c₂_mapRingHom (x : f.CubicRing) : (mapRingHom φ f x).c₂ = φ x.c₂ := (rfl)

@[simp] theorem mapRingHom_omega : mapRingHom φ f omega = omega := by
  ext <;> simp

@[simp] theorem mapRingHom_theta : mapRingHom φ f theta = theta := by
  ext <;> simp

@[simp] theorem mapRingHom_algebraMap (r : R) :
    mapRingHom φ f (algebraMap R _ r) = algebraMap S _ (φ r) := by
  ext <;> simp

theorem mapRingHom_injective (hφ : Function.Injective φ) :
    Function.Injective (mapRingHom φ f) := fun x y h => by
  ext
  · exact hφ (congrArg c₀ h)
  · exact hφ (congrArg c₁ h)
  · exact hφ (congrArg c₂ h)

theorem mapRingHom_surjective (hφ : Function.Surjective φ) :
    Function.Surjective (mapRingHom φ f) := fun y => by
  obtain ⟨x₀, hx₀⟩ := hφ y.c₀
  obtain ⟨x₁, hx₁⟩ := hφ y.c₁
  obtain ⟨x₂, hx₂⟩ := hφ y.c₂
  exact ⟨⟨x₀, x₁, x₂⟩, by ext <;> simp [hx₀, hx₁, hx₂]⟩

end map

/-! ### Trace and discriminant -/

/-- The trace of `c₀ + c₁ ω + c₂ θ` in `R(f)` is `3 c₀ + b c₁ - c c₂`. -/
theorem trace_apply (x : f.CubicRing) :
    Algebra.trace R f.CubicRing x = 3 * x.c₀ + f.b * x.c₁ - f.c * x.c₂ := by
  rw [Algebra.trace_eq_matrix_trace (basis f), Matrix.trace_fin_three]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, basis_zero, basis_one, basis_two,
    basis_repr_apply]
  simp
  ring

/-- The **discriminant** of the cubic ring `R(f)` with respect to its normal basis `⟨1, ω, θ⟩` is
the discriminant `b²c² - 4ac³ - 4b³d - 27a²d² + 18abcd` of the form `f`. -/
theorem discr_basis : Algebra.discr R (basis f) = f.discr := by
  rw [Algebra.discr_def, Matrix.det_fin_three]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, basis_zero, basis_one,
    basis_two, trace_apply]
  simp [Cubic.discr]
  ring

/-- The discriminant of the cubic ring `R(f)` with respect to the negated basis `⟨1, -ω, -θ⟩` is
also the discriminant of `f`. -/
theorem discr_negBasis : Algebra.discr R (negBasis f) = f.discr := by
  rw [Algebra.discr_def, Matrix.det_fin_three]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, negBasis_zero, negBasis_one,
    negBasis_two, trace_apply]
  simp [Cubic.discr]
  ring

end CommRing

end Cubic.CubicRing
