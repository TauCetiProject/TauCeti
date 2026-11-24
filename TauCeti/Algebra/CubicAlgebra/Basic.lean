/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CubicDiscriminant
public import Mathlib.RingTheory.Discriminant
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The cubic algebra of a binary cubic form

To a binary cubic form `f(u, v) = a u³ + b u² v + c u v² + d v³` over a commutative ring `R`,
recorded as Mathlib's `P = ⟨a, b, c, d⟩ : Cubic R`, attach the free rank-three commutative
`R`-algebra `P.CubicAlgebra` with basis `1, ω, θ` and multiplication table
`ωθ = -ad`, `ω² = -ac + bω - aθ`, `θ² = -bd + dω - cθ`.
This is the forward construction `P ↦ P.CubicAlgebra` in the free (globally trivialized) case of
the Delone–Faddeev–Gan–Gross–Savin correspondence between binary cubic forms and cubic algebras,
in the sign convention of Wood. No
division by `2` or `3` is used, so the construction works over every commutative ring, including
`𝔽₂`, `𝔽₃` and `ℤ`. Locally free cubic algebras over a Dedekind domain are glued from these free
pieces.

The traces of `1, ω, θ` are `3, b, -c`, and the discriminant of the basis `1, ω, θ` is the
discriminant `Cubic.discr P` of the form. This identifies the algebraic discriminant of a cubic
algebra with the invariant of its binary cubic form.

## Main definitions

* `Cubic.CubicAlgebra P`: the cubic algebra of `P : Cubic R`, a structure with coordinates `re`,
  `imOmega`, `imTheta` with respect to `1, ω, θ`.
* `Cubic.CubicAlgebra.omega`, `Cubic.CubicAlgebra.theta`: the two non-unit basis vectors, with
  scoped notation `ω` and `θ`.
* `Cubic.CubicAlgebra.basis`: the `R`-basis `1, ω, θ`.
* `Cubic.CubicAlgebra.lift`: the universal property; elements of a commutative `R`-algebra
  satisfying the table of `P` define an algebra map out of `P.CubicAlgebra`.
* `Cubic.CubicAlgebra.splitAlgEquiv`: for the form `uv(u - v)`, the cubic algebra is `R × R × R`.

## Main results

* `Cubic.CubicAlgebra.instCommRing`, `Cubic.CubicAlgebra.instAlgebra`: the multiplication table is
  commutative and associative, so `P.CubicAlgebra` is a commutative `R`-algebra.
* `Cubic.CubicAlgebra.omega_mul_theta`, `Cubic.CubicAlgebra.omega_mul_omega`,
  `Cubic.CubicAlgebra.theta_mul_theta`: the multiplication table.
* `Cubic.CubicAlgebra.trace_apply`: `Tr(x₀ + x₁ω + x₂θ) = 3x₀ + bx₁ - cx₂`.
* `Cubic.CubicAlgebra.discr_basis`: the discriminant of `1, ω, θ` is `Cubic.discr P`.

## Implementation notes

The structure and its additive and scalar instances follow the layout of Mathlib's
`QuadraticAlgebra` (`Mathlib.Algebra.QuadraticAlgebra.Defs`): each instance is stated under the
least structure on `R` it needs, and the multiplication starts at `CommRing R`.

## References

* M. M. Wood, *Parametrizing quartic algebras over an arbitrary base*, Algebra & Number Theory
  **5** (2011), 1069–1094, §2.
* W. T. Gan, B. Gross, G. Savin, *Fourier coefficients of modular forms on `G₂`*, Duke Math. J.
  **115** (2002), 105–169.
-/

@[expose] public section

namespace Cubic

/-- The cubic algebra of the binary cubic form `P = ⟨a, b, c, d⟩`: the free `R`-module with basis
`1, ω, θ` and multiplication `ωθ = -ad`, `ω² = -ac + bω - aθ`, `θ² = -bd + dω - cθ`. An element is
recorded by its coordinates `re`, `imOmega`, `imTheta`. -/
@[ext]
structure CubicAlgebra {R : Type*} (P : Cubic R) where
  /-- The coefficient of `1`. -/
  re : R
  /-- The coefficient of `ω`. -/
  imOmega : R
  /-- The coefficient of `θ`. -/
  imTheta : R

namespace CubicAlgebra

variable {R S T : Type*} {P : Cubic R}

/-- The equivalence between the cubic algebra and `R × R × R`, by coordinates. -/
@[simps]
def equivProd (P : Cubic R) : P.CubicAlgebra ≃ R × R × R where
  toFun x := (x.re, x.imOmega, x.imTheta)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩

instance [Nontrivial R] : Nontrivial P.CubicAlgebra := (equivProd P).nontrivial

section Coordinates

variable (x y : P.CubicAlgebra)

section Zero

variable [Zero R]

instance : Zero P.CubicAlgebra := ⟨⟨0, 0, 0⟩⟩

@[simp] theorem re_zero : (0 : P.CubicAlgebra).re = 0 := rfl
@[simp] theorem imOmega_zero : (0 : P.CubicAlgebra).imOmega = 0 := rfl
@[simp] theorem imTheta_zero : (0 : P.CubicAlgebra).imTheta = 0 := rfl

variable [One R]

instance : One P.CubicAlgebra := ⟨⟨1, 0, 0⟩⟩

@[simp] theorem re_one : (1 : P.CubicAlgebra).re = 1 := rfl
@[simp] theorem imOmega_one : (1 : P.CubicAlgebra).imOmega = 0 := rfl
@[simp] theorem imTheta_one : (1 : P.CubicAlgebra).imTheta = 0 := rfl

variable (P) in
/-- The basis vector `ω`. -/
def omega : P.CubicAlgebra := ⟨0, 1, 0⟩

variable (P) in
/-- The basis vector `θ`. -/
def theta : P.CubicAlgebra := ⟨0, 0, 1⟩

/-- The basis vector `ω = ⟨0, 1, 0⟩` of `P.CubicAlgebra`. -/
scoped notation "ω" => omega

/-- The basis vector `θ = ⟨0, 0, 1⟩` of `P.CubicAlgebra`. -/
scoped notation "θ" => theta

@[simp] theorem re_omega : (ω P).re = 0 := rfl
@[simp] theorem imOmega_omega : (ω P).imOmega = 1 := rfl
@[simp] theorem imTheta_omega : (ω P).imTheta = 0 := rfl
@[simp] theorem re_theta : (θ P).re = 0 := rfl
@[simp] theorem imOmega_theta : (θ P).imOmega = 0 := rfl
@[simp] theorem imTheta_theta : (θ P).imTheta = 1 := rfl

end Zero

instance [Add R] : Add P.CubicAlgebra :=
  ⟨fun x y ↦ ⟨x.re + y.re, x.imOmega + y.imOmega, x.imTheta + y.imTheta⟩⟩

instance [Neg R] : Neg P.CubicAlgebra := ⟨fun x ↦ ⟨-x.re, -x.imOmega, -x.imTheta⟩⟩

instance [Sub R] : Sub P.CubicAlgebra :=
  ⟨fun x y ↦ ⟨x.re - y.re, x.imOmega - y.imOmega, x.imTheta - y.imTheta⟩⟩

@[simp] theorem re_add [Add R] : (x + y).re = x.re + y.re := rfl
@[simp] theorem imOmega_add [Add R] : (x + y).imOmega = x.imOmega + y.imOmega := rfl
@[simp] theorem imTheta_add [Add R] : (x + y).imTheta = x.imTheta + y.imTheta := rfl
@[simp] theorem re_neg [Neg R] : (-x).re = -x.re := rfl
@[simp] theorem imOmega_neg [Neg R] : (-x).imOmega = -x.imOmega := rfl
@[simp] theorem imTheta_neg [Neg R] : (-x).imTheta = -x.imTheta := rfl
@[simp] theorem re_sub [Sub R] : (x - y).re = x.re - y.re := rfl
@[simp] theorem imOmega_sub [Sub R] : (x - y).imOmega = x.imOmega - y.imOmega := rfl
@[simp] theorem imTheta_sub [Sub R] : (x - y).imTheta = x.imTheta - y.imTheta := rfl

section SMul

variable [SMul S R] [SMul T R]

instance : SMul S P.CubicAlgebra := ⟨fun s x ↦ ⟨s • x.re, s • x.imOmega, s • x.imTheta⟩⟩

instance [SMul S T] [IsScalarTower S T R] : IsScalarTower S T P.CubicAlgebra where
  smul_assoc _ _ _ := by ext <;> exact smul_assoc _ _ _

instance [SMulCommClass S T R] : SMulCommClass S T P.CubicAlgebra where
  smul_comm _ _ _ := by ext <;> exact smul_comm _ _ _

@[simp] theorem re_smul (s : S) : (s • x).re = s • x.re := rfl
@[simp] theorem imOmega_smul (s : S) : (s • x).imOmega = s • x.imOmega := rfl
@[simp] theorem imTheta_smul (s : S) : (s • x).imTheta = s • x.imTheta := rfl

end SMul

end Coordinates

instance [AddMonoid R] : AddMonoid P.CubicAlgebra :=
  (equivProd P).injective.addMonoid _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance [AddCommMonoid R] : AddCommMonoid P.CubicAlgebra :=
  (equivProd P).injective.addCommMonoid _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance [AddCommGroup R] : AddCommGroup P.CubicAlgebra :=
  (equivProd P).injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance [Monoid S] [MulAction S R] : MulAction S P.CubicAlgebra where
  one_smul _ := by ext <;> simp
  mul_smul _ _ _ := by ext <;> simp [mul_smul]

instance [Monoid S] [AddMonoid R] [DistribMulAction S R] : DistribMulAction S P.CubicAlgebra where
  smul_zero _ := by ext <;> simp
  smul_add _ _ _ := by ext <;> simp

instance [Semiring S] [AddCommMonoid R] [Module S R] : Module S P.CubicAlgebra where
  add_smul _ _ _ := by ext <;> simp [add_smul]
  zero_smul _ := by ext <;> simp

section AddCommMonoidWithOne

variable [AddCommMonoidWithOne R]

instance : AddCommMonoidWithOne P.CubicAlgebra where
  natCast n := ⟨n, 0, 0⟩
  natCast_zero := by ext <;> simp
  natCast_succ n := by ext <;> simp

@[simp, norm_cast] theorem re_natCast (n : ℕ) : (n : P.CubicAlgebra).re = n := rfl
@[simp, norm_cast] theorem imOmega_natCast (n : ℕ) : (n : P.CubicAlgebra).imOmega = 0 := rfl
@[simp, norm_cast] theorem imTheta_natCast (n : ℕ) : (n : P.CubicAlgebra).imTheta = 0 := rfl

@[simp]
theorem re_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : P.CubicAlgebra).re = ofNat(n) := rfl

@[simp]
theorem imOmega_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : P.CubicAlgebra).imOmega = 0 := rfl

@[simp]
theorem imTheta_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : P.CubicAlgebra).imTheta = 0 := rfl

end AddCommMonoidWithOne

section AddCommGroupWithOne

variable [AddCommGroupWithOne R]

instance : AddCommGroupWithOne P.CubicAlgebra where
  intCast n := ⟨n, 0, 0⟩
  intCast_ofNat n := by ext; exacts [Int.cast_natCast n, rfl, rfl]
  intCast_negSucc n := by ext; exacts [Int.cast_negSucc n, neg_zero.symm, neg_zero.symm]

@[simp, norm_cast] theorem re_intCast (n : ℤ) : (n : P.CubicAlgebra).re = n := rfl
@[simp, norm_cast] theorem imOmega_intCast (n : ℤ) : (n : P.CubicAlgebra).imOmega = 0 := rfl
@[simp, norm_cast] theorem imTheta_intCast (n : ℤ) : (n : P.CubicAlgebra).imTheta = 0 := rfl

end AddCommGroupWithOne

section Semiring

variable [Semiring R]

variable (P) in
/-- The coordinate linear equivalence with `Fin 3 → R`, in the order `1, ω, θ`. -/
def linearEquivTuple : P.CubicAlgebra ≃ₗ[R] (Fin 3 → R) where
  toFun x := ![x.re, x.imOmega, x.imTheta]
  invFun v := ⟨v 0, v 1, v 2⟩
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' r x := by ext i; fin_cases i <;> simp
  left_inv x := by simp
  right_inv v := by ext i; fin_cases i <;> simp

@[simp]
theorem linearEquivTuple_apply (x : P.CubicAlgebra) :
    linearEquivTuple P x = ![x.re, x.imOmega, x.imTheta] := rfl

@[simp]
theorem linearEquivTuple_symm_apply (v : Fin 3 → R) :
    (linearEquivTuple P).symm v = ⟨v 0, v 1, v 2⟩ := rfl

variable (P) in
/-- The basis `1, ω, θ` of the cubic algebra. -/
noncomputable def basis : Module.Basis (Fin 3) R P.CubicAlgebra :=
  .ofEquivFun (linearEquivTuple P)

@[simp] theorem basis_zero : basis P 0 = 1 := by ext <;> simp [basis]
@[simp] theorem basis_one : basis P 1 = ω P := by ext <;> simp [basis, omega]
@[simp] theorem basis_two : basis P 2 = θ P := by ext <;> simp [basis, theta]

@[simp]
theorem basis_repr (x : P.CubicAlgebra) : (basis P).repr x = ![x.re, x.imOmega, x.imTheta] := by
  ext i; fin_cases i <;> simp [basis]

instance : Module.Free R P.CubicAlgebra := .of_basis (basis P)
instance : Module.Finite R P.CubicAlgebra := .of_basis (basis P)

theorem finrank_eq_three [StrongRankCondition R] : Module.finrank R P.CubicAlgebra = 3 := by
  simp [Module.finrank_eq_card_basis (basis P)]

end Semiring

variable [CommRing R]

/-- Multiplication by the table `ωθ = -ad`, `ω² = -ac + bω - aθ`, `θ² = -bd + dω - cθ`. -/
instance : Mul P.CubicAlgebra :=
  ⟨fun x y ↦
    ⟨x.re * y.re - P.a * P.c * (x.imOmega * y.imOmega) -
        P.a * P.d * (x.imOmega * y.imTheta + x.imTheta * y.imOmega) -
        P.b * P.d * (x.imTheta * y.imTheta),
      x.re * y.imOmega + x.imOmega * y.re + P.b * (x.imOmega * y.imOmega) +
        P.d * (x.imTheta * y.imTheta),
      x.re * y.imTheta + x.imTheta * y.re - P.a * (x.imOmega * y.imOmega) -
        P.c * (x.imTheta * y.imTheta)⟩⟩

section Mul

variable (x y : P.CubicAlgebra)

@[simp]
theorem re_mul : (x * y).re = x.re * y.re - P.a * P.c * (x.imOmega * y.imOmega) -
    P.a * P.d * (x.imOmega * y.imTheta + x.imTheta * y.imOmega) -
    P.b * P.d * (x.imTheta * y.imTheta) := rfl

@[simp]
theorem imOmega_mul : (x * y).imOmega = x.re * y.imOmega + x.imOmega * y.re +
    P.b * (x.imOmega * y.imOmega) + P.d * (x.imTheta * y.imTheta) := rfl

@[simp]
theorem imTheta_mul : (x * y).imTheta = x.re * y.imTheta + x.imTheta * y.re -
    P.a * (x.imOmega * y.imOmega) - P.c * (x.imTheta * y.imTheta) := rfl

end Mul

/-- The multiplication table is commutative and associative, with unit `1`. -/
instance instCommRing : CommRing P.CubicAlgebra where
  left_distrib _ _ _ := by ext <;> simp <;> ring
  right_distrib _ _ _ := by ext <;> simp <;> ring
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp
  mul_assoc _ _ _ := by ext <;> simp <;> ring
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp
  mul_comm _ _ := by ext <;> simp <;> ring

instance instAlgebra [CommSemiring S] [Algebra S R] : Algebra S P.CubicAlgebra where
  algebraMap :=
    { toFun s := ⟨algebraMap S R s, 0, 0⟩
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_mul' x y := by ext <;> simp
      map_add' x y := by ext <;> simp }
  smul_def' s x := by ext <;> simp [Algebra.smul_def]
  commutes' s x := by ext <;> simp [mul_comm]

section AlgebraMap

variable [CommSemiring S] [Algebra S R] (s : S)

@[simp]
theorem re_algebraMap : (algebraMap S P.CubicAlgebra s).re = algebraMap S R s := rfl

@[simp] theorem imOmega_algebraMap : (algebraMap S P.CubicAlgebra s).imOmega = 0 := rfl
@[simp] theorem imTheta_algebraMap : (algebraMap S P.CubicAlgebra s).imTheta = 0 := rfl

end AlgebraMap

theorem algebraMap_injective : Function.Injective (algebraMap R P.CubicAlgebra) :=
  fun _ _ h ↦ congr_arg re h

/-- Every element is `x₀ + x₁ ω + x₂ θ` in its coordinates. -/
theorem algebraMap_add_smul_omega_add_smul_theta (x : P.CubicAlgebra) :
    algebraMap R P.CubicAlgebra x.re + x.imOmega • ω P + x.imTheta • θ P = x := by
  ext <;> simp

/-- The multiplication table: `ωθ = -ad`. -/
theorem omega_mul_theta : ω P * θ P = algebraMap R P.CubicAlgebra (-(P.a * P.d)) := by
  ext <;> simp

/-- The multiplication table: `ω² = -ac + bω - aθ`. -/
theorem omega_mul_omega :
    ω P * ω P = algebraMap R P.CubicAlgebra (-(P.a * P.c)) + P.b • ω P - P.a • θ P := by
  ext <;> simp

/-- The multiplication table: `θ² = -bd + dω - cθ`. -/
theorem theta_mul_theta :
    θ P * θ P = algebraMap R P.CubicAlgebra (-(P.b * P.d)) + P.d • ω P - P.c • θ P := by
  ext <;> simp

section Lift

variable {A : Type*} [CommRing A] [Algebra R A]

/-- **Universal property.** Elements `ω'`, `θ'` of a commutative `R`-algebra satisfying the
multiplication table of `P` determine an algebra map `P.CubicAlgebra →ₐ[R] A` sending `ω ↦ ω'` and
`θ ↦ θ'`. -/
def lift (ω' θ' : A) (hωθ : ω' * θ' = algebraMap R A (-(P.a * P.d)))
    (hωω : ω' * ω' = algebraMap R A (-(P.a * P.c)) + P.b • ω' - P.a • θ')
    (hθθ : θ' * θ' = algebraMap R A (-(P.b * P.d)) + P.d • ω' - P.c • θ') :
    P.CubicAlgebra →ₐ[R] A :=
  AlgHom.ofLinearMap
    { toFun x := algebraMap R A x.re + x.imOmega • ω' + x.imTheta • θ'
      map_add' x y := by simp only [re_add, imOmega_add, imTheta_add, map_add, add_smul]; abel
      map_smul' r x := by simp [Algebra.smul_def]; ring }
    (by simp)
    (fun x y ↦ by
      simp only [Algebra.smul_def, map_add, map_sub, map_mul, map_neg, re_mul, imOmega_mul,
        imTheta_mul, LinearMap.coe_mk, AddHom.coe_mk] at hωθ hωω hθθ ⊢
      linear_combination
        (-(algebraMap R A x.imOmega * algebraMap R A y.imOmega)) * hωω +
        (-(algebraMap R A x.imOmega * algebraMap R A y.imTheta +
          algebraMap R A x.imTheta * algebraMap R A y.imOmega)) * hωθ +
        (-(algebraMap R A x.imTheta * algebraMap R A y.imTheta)) * hθθ)

variable {ω' θ' : A} {hωθ : ω' * θ' = algebraMap R A (-(P.a * P.d))}
  {hωω : ω' * ω' = algebraMap R A (-(P.a * P.c)) + P.b • ω' - P.a • θ'}
  {hθθ : θ' * θ' = algebraMap R A (-(P.b * P.d)) + P.d • ω' - P.c • θ'}

theorem lift_apply (x : P.CubicAlgebra) :
    lift ω' θ' hωθ hωω hθθ x = algebraMap R A x.re + x.imOmega • ω' + x.imTheta • θ' := rfl

@[simp]
theorem lift_omega : lift ω' θ' hωθ hωω hθθ (ω P) = ω' := by
  simp [lift_apply]

@[simp]
theorem lift_theta : lift ω' θ' hωθ hωω hθθ (θ P) = θ' := by
  simp [lift_apply]

end Lift

/-- Algebra maps out of the cubic algebra are determined by the images of `ω` and `θ`. -/
@[ext]
theorem algHom_ext {A : Type*} [Semiring A] [Algebra R A] {f g : P.CubicAlgebra →ₐ[R] A}
    (hω : f (ω P) = g (ω P)) (hθ : f (θ P) = g (θ P)) : f = g := by
  ext x
  rw [← algebraMap_add_smul_omega_add_smul_theta x]
  simp [hω, hθ]

/-- The trace of `x₀ + x₁ ω + x₂ θ` is `3 x₀ + b x₁ - c x₂`. -/
theorem trace_apply (x : P.CubicAlgebra) :
    Algebra.trace R P.CubicAlgebra x = 3 * x.re + P.b * x.imOmega - P.c * x.imTheta := by
  rw [Algebra.trace_eq_matrix_trace (basis P), Matrix.trace_fin_three]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, basis_zero, basis_one, basis_two, basis_repr]
  simp
  ring

@[simp]
theorem trace_one : Algebra.trace R P.CubicAlgebra 1 = 3 := by
  simp [trace_apply]

@[simp]
theorem trace_omega : Algebra.trace R P.CubicAlgebra (ω P) = P.b := by
  simp [trace_apply]

@[simp]
theorem trace_theta : Algebra.trace R P.CubicAlgebra (θ P) = -P.c := by
  simp [trace_apply]

/-- **The discriminant of a cubic algebra is the discriminant of its form.** The trace-form
discriminant of the basis `1, ω, θ` is `Cubic.discr P = b²c² - 4ac³ - 4b³d - 27a²d² + 18abcd`. -/
@[simp]
theorem discr_basis : Algebra.discr R (basis P) = P.discr := by
  rw [Algebra.discr_def, Matrix.det_fin_three]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, basis_zero, basis_one,
    basis_two, trace_apply]
  simp [Cubic.discr]
  ring

/-! ### The split form -/

/-- The form `uv(u - v)`, with coefficients `⟨0, 1, -1, 0⟩`. -/
abbrev splitForm (R : Type*) [Zero R] [One R] [Neg R] : Cubic R := ⟨0, 1, -1, 0⟩

/-- For the form `uv(u - v)` the table reads `ωθ = 0`, `ω² = ω`, `θ² = θ`: the cubic algebra is
`R × R × R`, through the three characters sending `(ω, θ)` to `(0, 0)`, `(1, 0)` and `(0, 1)`. -/
def splitAlgEquiv : (splitForm R).CubicAlgebra ≃ₐ[R] R × R × R :=
  AlgEquiv.ofLinearEquiv
    { toFun x := (x.re, x.re + x.imOmega, x.re + x.imTheta)
      invFun v := ⟨v.1, v.2.1 - v.1, v.2.2 - v.1⟩
      map_add' x y := by ext <;> simp <;> ring
      map_smul' r x := by ext <;> simp <;> ring
      left_inv x := by ext <;> simp
      right_inv v := by ext <;> simp }
    (by ext <;> simp)
    (fun x y ↦ by ext <;> simp <;> ring)

@[simp]
theorem splitAlgEquiv_apply (x : (splitForm R).CubicAlgebra) :
    splitAlgEquiv x = (x.re, x.re + x.imOmega, x.re + x.imTheta) := rfl

@[simp]
theorem splitAlgEquiv_symm_apply (v : R × R × R) :
    (splitAlgEquiv (R := R)).symm v = ⟨v.1, v.2.1 - v.1, v.2.2 - v.1⟩ := rfl

end CubicAlgebra

end Cubic
