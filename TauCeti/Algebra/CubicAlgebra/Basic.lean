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
This is the free (globally trivialized) case of the Delone–Faddeev–Gan–Gross–Savin
correspondence between binary cubic forms and cubic algebras, in the sign convention of Wood. No
division by `2` or `3` is used, so the construction works over every commutative ring, including
`𝔽₂`, `𝔽₃` and `ℤ`. Locally free cubic algebras over a Dedekind domain are glued from these free
pieces.

The traces of `1, ω, θ` are `3, b, -c`, and the discriminant of the basis `1, ω, θ` is the
discriminant `Cubic.discr P` of the form. This identifies the algebraic discriminant of a cubic
algebra with the invariant of its binary cubic form.

## Main definitions

* `Cubic.CubicAlgebra P`: the cubic algebra of `P : Cubic R`, a structure with coordinates `re`,
  `imω`, `imθ` with respect to `1, ω, θ`.
* `Cubic.CubicAlgebra.ω`, `Cubic.CubicAlgebra.θ`: the two non-unit basis vectors.
* `Cubic.CubicAlgebra.basis`: the `R`-basis `1, ω, θ`.
* `Cubic.CubicAlgebra.lift`: the universal property; elements of a commutative `R`-algebra
  satisfying the table of `P` define an algebra map out of `P.CubicAlgebra`.
* `Cubic.CubicAlgebra.splitAlgEquiv`: for the form `uv(u - v)`, the cubic algebra is `R × R × R`.

## Main results

* `Cubic.CubicAlgebra.instCommRing`, `Cubic.CubicAlgebra.instAlgebra`: the multiplication table is
  commutative and associative, so `P.CubicAlgebra` is a commutative `R`-algebra.
* `Cubic.CubicAlgebra.ω_mul_θ`, `Cubic.CubicAlgebra.ω_mul_ω`, `Cubic.CubicAlgebra.θ_mul_θ`: the
  multiplication table.
* `Cubic.CubicAlgebra.trace_apply`: `Tr(x₀ + x₁ω + x₂θ) = 3x₀ + bx₁ - cx₂`.
* `Cubic.CubicAlgebra.discr_basis`: the discriminant of `1, ω, θ` is `Cubic.discr P`.

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
recorded by its coordinates `re`, `imω`, `imθ`. -/
@[ext]
structure CubicAlgebra {R : Type*} [CommRing R] (P : Cubic R) where
  /-- The coefficient of `1`. -/
  re : R
  /-- The coefficient of `ω`. -/
  imω : R
  /-- The coefficient of `θ`. -/
  imθ : R

namespace CubicAlgebra

variable {R : Type*} [CommRing R] {P : Cubic R}

/-- The equivalence between the cubic algebra and `R × R × R`, by coordinates. -/
@[simps]
def equivProd (P : Cubic R) : P.CubicAlgebra ≃ R × R × R where
  toFun x := (x.re, x.imω, x.imθ)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩

instance [Nontrivial R] : Nontrivial P.CubicAlgebra := (equivProd P).nontrivial

instance : Zero P.CubicAlgebra := ⟨⟨0, 0, 0⟩⟩
instance : One P.CubicAlgebra := ⟨⟨1, 0, 0⟩⟩
instance : Add P.CubicAlgebra := ⟨fun x y ↦ ⟨x.re + y.re, x.imω + y.imω, x.imθ + y.imθ⟩⟩
instance : Neg P.CubicAlgebra := ⟨fun x ↦ ⟨-x.re, -x.imω, -x.imθ⟩⟩
instance : Sub P.CubicAlgebra := ⟨fun x y ↦ ⟨x.re - y.re, x.imω - y.imω, x.imθ - y.imθ⟩⟩

instance {S : Type*} [SMul S R] : SMul S P.CubicAlgebra :=
  ⟨fun s x ↦ ⟨s • x.re, s • x.imω, s • x.imθ⟩⟩

/-- Multiplication by the table `ωθ = -ad`, `ω² = -ac + bω - aθ`, `θ² = -bd + dω - cθ`. -/
instance : Mul P.CubicAlgebra :=
  ⟨fun x y ↦
    ⟨x.re * y.re - P.a * P.c * (x.imω * y.imω) - P.a * P.d * (x.imω * y.imθ + x.imθ * y.imω) -
        P.b * P.d * (x.imθ * y.imθ),
      x.re * y.imω + x.imω * y.re + P.b * (x.imω * y.imω) + P.d * (x.imθ * y.imθ),
      x.re * y.imθ + x.imθ * y.re - P.a * (x.imω * y.imω) - P.c * (x.imθ * y.imθ)⟩⟩

section Coordinates

variable (x y : P.CubicAlgebra)

@[simp] theorem re_zero : (0 : P.CubicAlgebra).re = 0 := rfl
@[simp] theorem imω_zero : (0 : P.CubicAlgebra).imω = 0 := rfl
@[simp] theorem imθ_zero : (0 : P.CubicAlgebra).imθ = 0 := rfl
@[simp] theorem re_one : (1 : P.CubicAlgebra).re = 1 := rfl
@[simp] theorem imω_one : (1 : P.CubicAlgebra).imω = 0 := rfl
@[simp] theorem imθ_one : (1 : P.CubicAlgebra).imθ = 0 := rfl
@[simp] theorem re_add : (x + y).re = x.re + y.re := rfl
@[simp] theorem imω_add : (x + y).imω = x.imω + y.imω := rfl
@[simp] theorem imθ_add : (x + y).imθ = x.imθ + y.imθ := rfl
@[simp] theorem re_neg : (-x).re = -x.re := rfl
@[simp] theorem imω_neg : (-x).imω = -x.imω := rfl
@[simp] theorem imθ_neg : (-x).imθ = -x.imθ := rfl
@[simp] theorem re_sub : (x - y).re = x.re - y.re := rfl
@[simp] theorem imω_sub : (x - y).imω = x.imω - y.imω := rfl
@[simp] theorem imθ_sub : (x - y).imθ = x.imθ - y.imθ := rfl

@[simp] theorem re_smul {S : Type*} [SMul S R] (s : S) : (s • x).re = s • x.re := rfl
@[simp] theorem imω_smul {S : Type*} [SMul S R] (s : S) : (s • x).imω = s • x.imω := rfl
@[simp] theorem imθ_smul {S : Type*} [SMul S R] (s : S) : (s • x).imθ = s • x.imθ := rfl

@[simp]
theorem re_mul : (x * y).re = x.re * y.re - P.a * P.c * (x.imω * y.imω) -
    P.a * P.d * (x.imω * y.imθ + x.imθ * y.imω) - P.b * P.d * (x.imθ * y.imθ) := rfl

@[simp]
theorem imω_mul : (x * y).imω =
    x.re * y.imω + x.imω * y.re + P.b * (x.imω * y.imω) + P.d * (x.imθ * y.imθ) := rfl

@[simp]
theorem imθ_mul : (x * y).imθ =
    x.re * y.imθ + x.imθ * y.re - P.a * (x.imω * y.imω) - P.c * (x.imθ * y.imθ) := rfl

end Coordinates

instance : AddCommGroup P.CubicAlgebra := by
  refine (equivProd P).injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ ?_) (fun _ _ ↦ ?_) <;> ext <;> simp

/-- The additive equivalence between the cubic algebra and `R × R × R`. -/
def addEquivProd (P : Cubic R) : P.CubicAlgebra ≃+ R × R × R :=
  { equivProd P with map_add' := fun _ _ ↦ rfl }

instance {S : Type*} [Semiring S] [Module S R] : Module S P.CubicAlgebra :=
  (addEquivProd P).injective.module S (addEquivProd P).toAddMonoidHom fun _ _ ↦ rfl

instance : AddCommGroupWithOne P.CubicAlgebra where
  natCast n := ⟨n, 0, 0⟩
  natCast_zero := by ext <;> simp
  natCast_succ n := by ext <;> simp
  intCast n := ⟨n, 0, 0⟩
  intCast_ofNat n := by ext; exacts [Int.cast_natCast n, rfl, rfl]
  intCast_negSucc n := by ext; exacts [Int.cast_negSucc n, neg_zero.symm, neg_zero.symm]

@[simp, norm_cast] theorem re_natCast (n : ℕ) : (n : P.CubicAlgebra).re = n := rfl
@[simp, norm_cast] theorem imω_natCast (n : ℕ) : (n : P.CubicAlgebra).imω = 0 := rfl
@[simp, norm_cast] theorem imθ_natCast (n : ℕ) : (n : P.CubicAlgebra).imθ = 0 := rfl
@[simp, norm_cast] theorem re_intCast (n : ℤ) : (n : P.CubicAlgebra).re = n := rfl
@[simp, norm_cast] theorem imω_intCast (n : ℤ) : (n : P.CubicAlgebra).imω = 0 := rfl
@[simp, norm_cast] theorem imθ_intCast (n : ℤ) : (n : P.CubicAlgebra).imθ = 0 := rfl

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

instance instAlgebra {S : Type*} [CommSemiring S] [Algebra S R] : Algebra S P.CubicAlgebra where
  algebraMap :=
    { toFun s := ⟨algebraMap S R s, 0, 0⟩
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_mul' x y := by ext <;> simp
      map_add' x y := by ext <;> simp }
  smul_def' s x := by ext <;> simp [Algebra.smul_def]
  commutes' s x := by ext <;> simp [mul_comm]

@[simp] theorem re_algebraMap (r : R) : (algebraMap R P.CubicAlgebra r).re = r := rfl
@[simp] theorem imω_algebraMap (r : R) : (algebraMap R P.CubicAlgebra r).imω = 0 := rfl
@[simp] theorem imθ_algebraMap (r : R) : (algebraMap R P.CubicAlgebra r).imθ = 0 := rfl

theorem algebraMap_injective : Function.Injective (algebraMap R P.CubicAlgebra) :=
  fun _ _ h ↦ congr_arg re h

variable (P) in
/-- The basis vector `ω`. -/
def ω : P.CubicAlgebra := ⟨0, 1, 0⟩

variable (P) in
/-- The basis vector `θ`. -/
def θ : P.CubicAlgebra := ⟨0, 0, 1⟩

@[simp] theorem re_ω : (ω P).re = 0 := rfl
@[simp] theorem imω_ω : (ω P).imω = 1 := rfl
@[simp] theorem imθ_ω : (ω P).imθ = 0 := rfl
@[simp] theorem re_θ : (θ P).re = 0 := rfl
@[simp] theorem imω_θ : (θ P).imω = 0 := rfl
@[simp] theorem imθ_θ : (θ P).imθ = 1 := rfl

/-- Every element is `x₀ + x₁ ω + x₂ θ` in its coordinates. -/
theorem algebraMap_add_smul_ω_add_smul_θ (x : P.CubicAlgebra) :
    algebraMap R P.CubicAlgebra x.re + x.imω • ω P + x.imθ • θ P = x := by
  ext <;> simp

/-- The multiplication table: `ωθ = -ad`. -/
theorem ω_mul_θ : ω P * θ P = algebraMap R P.CubicAlgebra (-(P.a * P.d)) := by
  ext <;> simp

/-- The multiplication table: `ω² = -ac + bω - aθ`. -/
theorem ω_mul_ω :
    ω P * ω P = algebraMap R P.CubicAlgebra (-(P.a * P.c)) + P.b • ω P - P.a • θ P := by
  ext <;> simp

/-- The multiplication table: `θ² = -bd + dω - cθ`. -/
theorem θ_mul_θ :
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
    { toFun x := algebraMap R A x.re + x.imω • ω' + x.imθ • θ'
      map_add' x y := by simp only [re_add, imω_add, imθ_add, map_add, add_smul]; abel
      map_smul' r x := by simp [Algebra.smul_def]; ring }
    (by simp)
    (fun x y ↦ by
      simp only [Algebra.smul_def, map_add, map_sub, map_mul, map_neg, re_mul, imω_mul,
        imθ_mul, LinearMap.coe_mk, AddHom.coe_mk] at hωθ hωω hθθ ⊢
      linear_combination
        (-(algebraMap R A x.imω * algebraMap R A y.imω)) * hωω +
        (-(algebraMap R A x.imω * algebraMap R A y.imθ +
          algebraMap R A x.imθ * algebraMap R A y.imω)) * hωθ +
        (-(algebraMap R A x.imθ * algebraMap R A y.imθ)) * hθθ)

variable {ω' θ' : A} {hωθ : ω' * θ' = algebraMap R A (-(P.a * P.d))}
  {hωω : ω' * ω' = algebraMap R A (-(P.a * P.c)) + P.b • ω' - P.a • θ'}
  {hθθ : θ' * θ' = algebraMap R A (-(P.b * P.d)) + P.d • ω' - P.c • θ'}

theorem lift_apply (x : P.CubicAlgebra) :
    lift ω' θ' hωθ hωω hθθ x = algebraMap R A x.re + x.imω • ω' + x.imθ • θ' := rfl

@[simp]
theorem lift_ω : lift ω' θ' hωθ hωω hθθ (ω P) = ω' := by
  simp [lift_apply]

@[simp]
theorem lift_θ : lift ω' θ' hωθ hωω hθθ (θ P) = θ' := by
  simp [lift_apply]

/-- Algebra maps out of the cubic algebra are determined by the images of `ω` and `θ`. -/
@[ext]
theorem algHom_ext {f g : P.CubicAlgebra →ₐ[R] A} (hω : f (ω P) = g (ω P))
    (hθ : f (θ P) = g (θ P)) : f = g := by
  ext x
  rw [← algebraMap_add_smul_ω_add_smul_θ x]
  simp [hω, hθ]

end Lift

variable (P) in
/-- The coordinate linear equivalence with `Fin 3 → R`, in the order `1, ω, θ`. -/
def linearEquivTuple : P.CubicAlgebra ≃ₗ[R] (Fin 3 → R) where
  toFun x := ![x.re, x.imω, x.imθ]
  invFun v := ⟨v 0, v 1, v 2⟩
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' r x := by ext i; fin_cases i <;> simp
  left_inv x := by simp
  right_inv v := by ext i; fin_cases i <;> simp

variable (P) in
/-- The basis `1, ω, θ` of the cubic algebra. -/
noncomputable def basis : Module.Basis (Fin 3) R P.CubicAlgebra :=
  .ofEquivFun (linearEquivTuple P)

@[simp] theorem basis_zero : basis P 0 = 1 := by ext <;> simp [basis, linearEquivTuple]
@[simp] theorem basis_one : basis P 1 = ω P := by ext <;> simp [basis, linearEquivTuple, ω]
@[simp] theorem basis_two : basis P 2 = θ P := by ext <;> simp [basis, linearEquivTuple, θ]

@[simp]
theorem basis_repr (x : P.CubicAlgebra) : (basis P).repr x = ![x.re, x.imω, x.imθ] := by
  ext i; fin_cases i <;> simp [basis, linearEquivTuple]

instance : Module.Free R P.CubicAlgebra := .of_basis (basis P)
instance : Module.Finite R P.CubicAlgebra := .of_basis (basis P)

theorem finrank_eq_three [Nontrivial R] : Module.finrank R P.CubicAlgebra = 3 := by
  simp [Module.finrank_eq_card_basis (basis P)]

/-- The trace of `x₀ + x₁ ω + x₂ θ` is `3 x₀ + b x₁ - c x₂`. -/
theorem trace_apply (x : P.CubicAlgebra) :
    Algebra.trace R P.CubicAlgebra x = 3 * x.re + P.b * x.imω - P.c * x.imθ := by
  rw [Algebra.trace_eq_matrix_trace (basis P), Matrix.trace_fin_three]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, basis_zero, basis_one, basis_two, basis_repr]
  simp
  ring

@[simp]
theorem trace_ω : Algebra.trace R P.CubicAlgebra (ω P) = P.b := by
  simp [trace_apply]

@[simp]
theorem trace_θ : Algebra.trace R P.CubicAlgebra (θ P) = -P.c := by
  simp [trace_apply]

/-- **The discriminant of a cubic algebra is the discriminant of its form.** The trace-form
discriminant of the basis `1, ω, θ` is `Cubic.discr P = b²c² - 4ac³ - 4b³d - 27a²d² + 18abcd`. -/
theorem discr_basis : Algebra.discr R (basis P) = P.discr := by
  rw [Algebra.discr_def, Matrix.det_fin_three]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, basis_zero, basis_one,
    basis_two, trace_apply]
  simp [Cubic.discr]
  ring

/-! ### The split form -/

/-- The form `uv(u - v)`, with coefficients `⟨0, 1, -1, 0⟩`. -/
abbrev splitForm (R : Type*) [CommRing R] : Cubic R := ⟨0, 1, -1, 0⟩

/-- For the form `uv(u - v)` the table reads `ωθ = 0`, `ω² = ω`, `θ² = θ`: the cubic algebra is
`R × R × R`, through the three characters sending `(ω, θ)` to `(0, 0)`, `(1, 0)` and `(0, 1)`. -/
def splitAlgEquiv : (splitForm R).CubicAlgebra ≃ₐ[R] R × R × R :=
  AlgEquiv.ofLinearEquiv
    { toFun x := (x.re, x.re + x.imω, x.re + x.imθ)
      invFun v := ⟨v.1, v.2.1 - v.1, v.2.2 - v.1⟩
      map_add' x y := by ext <;> simp <;> ring
      map_smul' r x := by ext <;> simp <;> ring
      left_inv x := by ext <;> simp
      right_inv v := by ext <;> simp }
    (by ext <;> simp)
    (fun x y ↦ by ext <;> simp <;> ring)

@[simp]
theorem splitAlgEquiv_apply (x : (splitForm R).CubicAlgebra) :
    splitAlgEquiv x = (x.re, x.re + x.imω, x.re + x.imθ) := rfl

end CubicAlgebra

end Cubic
