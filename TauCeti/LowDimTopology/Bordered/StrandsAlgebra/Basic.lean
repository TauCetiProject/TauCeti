/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.StrandDiagram

/-!
# The strands algebra

The strands algebra `A(n)` of Lipshitz, Ozsváth and Thurston is the differential algebra
underlying the bordered Heegaard Floer invariants: the algebra `A(Z)` of a pointed matched circle
`Z` with `4k` points is a (non-unital) subalgebra of `A(4k)`, and for a bordered three-manifold `Y`
with boundary `Z`, `CFA^(Y)` is an `A∞`-module over `A(Z)` and `CFD^(Y)` is a type `D` structure
over `A(-Z)`. As a vector space over `𝔽₂`,
`A(n)` has a basis of strand diagrams (`TauCeti.StrandDiagram`), the upward partial bijections
`φ : S → T` of `{1, …, n}`. The product
of two basis elements `φ : S → T` and `ψ : U → V` is the composite `ψ ∘ φ : S → V` when `T = U`
and the inversion counts add, `inv (ψ ∘ φ) = inv φ + inv ψ`, and zero otherwise. The identity
diagrams `I(S)` on the subsets `S` are orthogonal idempotents summing to the unit.

This file constructs the underlying associative algebra `TauCeti.StrandsAlgebra R α` of the
strands algebra of a finite linear order `α`, over an arbitrary commutative semiring `R`. Its
differential, which resolves crossings, is `TauCeti.StrandsAlgebra.differential`. Lipshitz, Ozsváth
and Thurston work over `𝔽₂`, which is the case `R = ZMod 2`, `α = Fin n`; the product of basis
elements involves no coefficients other than `0` and `1`, so its definition makes sense over any
`R`. Associativity
comes from the subadditivity of inversion counts
(`TauCeti.StrandDiagram.trans_composable_and_composable_iff`).

## Main definitions

* `TauCeti.StrandsAlgebra R α`: the free `R`-module on the strand diagrams of `α`, with the
  strands product; it is an `R`-algebra, and a ring when `R` is a commutative ring.
* `TauCeti.StrandsAlgebra.of φ`: the basis element of a strand diagram `φ`.
* `TauCeti.StrandsAlgebra.basis`: the basis of strand diagrams.
* `TauCeti.StrandsAlgebra.idem s`: the idempotent `I(s)`, the identity diagram on `s`.

## Main results

* `TauCeti.StrandsAlgebra.of_mul_of`: the product of two basis elements.
* `TauCeti.StrandsAlgebra.idem_mul_idem`, `TauCeti.StrandsAlgebra.sum_idem`: the `I(s)` are
  orthogonal idempotents summing to `1`.
* `TauCeti.StrandsAlgebra.idem_mul_of`, `TauCeti.StrandsAlgebra.of_mul_idem`: `I(s) φ` is `φ` when
  `s` is the source of `φ` and zero otherwise, and `φ I(t)` is `φ` when `t` is its target.
* `TauCeti.StrandsAlgebra.map_mul_of_basis`: a linear map out of the strands algebra is
  multiplicative once it is multiplicative on basis elements.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.1,
  Definition 3.2 (the strands algebra `A(n, k)`, its product and its idempotents).
-/

public section

noncomputable section

namespace TauCeti

variable (R α : Type*) [CommSemiring R] [LinearOrder α]

/-- The strands algebra of a finite linear order `α` over a commutative semiring `R`: the free
`R`-module on the strand diagrams of `α`, multiplied by concatenating composable diagrams. For
`α = Fin n` and `R = ZMod 2` it is the algebra underlying the strands algebra `A(n)` of Lipshitz,
Ozsváth and Thurston, the direct sum of their algebras `A(n, k)` over the number `k` of strands.
Its differential, which resolves crossings, is `TauCeti.StrandsAlgebra.differential`. -/
def StrandsAlgebra : Type _ :=
  StrandDiagram α →₀ R

namespace StrandsAlgebra

instance : AddCommMonoid (StrandsAlgebra R α) :=
  inferInstanceAs (AddCommMonoid (StrandDiagram α →₀ R))

instance : Module R (StrandsAlgebra R α) :=
  inferInstanceAs (Module R (StrandDiagram α →₀ R))

instance {R : Type*} [CommRing R] : AddCommGroup (StrandsAlgebra R α) :=
  inferInstanceAs (AddCommGroup (StrandDiagram α →₀ R))

variable {R α}

/-- The basis element of the strands algebra given by a strand diagram. -/
def of (φ : StrandDiagram α) : StrandsAlgebra R α :=
  Finsupp.single φ 1

variable (R α) in
/-- The basis of the strands algebra given by the strand diagrams. -/
def basis : Module.Basis (StrandDiagram α) R (StrandsAlgebra R α) :=
  Finsupp.basisSingleOne

@[simp]
theorem basis_apply (φ : StrandDiagram α) : basis R α φ = of φ :=
  congrFun Finsupp.coe_basisSingleOne φ

/-- The coordinates of a basis element. -/
@[simp]
theorem basis_repr_of (φ : StrandDiagram α) : (basis R α).repr (of φ) = Finsupp.single φ 1 := by
  rw [← basis_apply, Module.Basis.repr_self]

private theorem single_eq_smul_of (φ : StrandDiagram α) (r : R) :
    (Finsupp.single φ r : StrandsAlgebra R α) = r • of φ :=
  (Finsupp.smul_single_one φ r).symm

/-- To prove an additive property of every element of the strands algebra, it suffices to prove
it for multiples of basis elements. -/
@[elab_as_elim]
theorem induction_on {p : StrandsAlgebra R α → Prop} (x : StrandsAlgebra R α) (zero : p 0)
    (add : ∀ x y, p x → p y → p (x + y)) (smul_of : ∀ (r : R) φ, p (r • of φ)) : p x :=
  Finsupp.induction_linear x zero add fun φ r ↦ single_eq_smul_of φ r ▸ smul_of r φ

/-- The idempotent `I(s)` of the strands algebra: the identity diagram on `s`, one horizontal
strand at each point of `s`. -/
def idem (s : Finset α) : StrandsAlgebra R α :=
  of (StrandDiagram.idOn s)

theorem idem_def (s : Finset α) : (idem s : StrandsAlgebra R α) = of (StrandDiagram.idOn s) :=
  (rfl)

open scoped Classical in
/-- The coefficients of a sum of basis elements: `1` on the summed diagrams and `0` elsewhere. -/
theorem repr_sum_of_apply (s : Finset (StrandDiagram α)) (ψ : StrandDiagram α) :
    (basis R α).repr (∑ φ ∈ s, of φ) ψ = if ψ ∈ s then 1 else 0 := by
  simp [Finset.sum_apply', Finsupp.single_apply]

variable [Fintype α]

/-- The strands product: on basis elements, the composite of two diagrams if they are composable,
and zero otherwise, extended bilinearly. -/
instance : Mul (StrandsAlgebra R α) :=
  ⟨fun x y ↦ (basis R α).constr R (fun φ ↦ (basis R α).constr R fun ψ ↦
    (if φ.Composable ψ then of (φ.trans ψ) else 0 : StrandsAlgebra R α)) x y⟩

/-- The unit of the strands algebra: the sum of the idempotents `I(s)` over all subsets `s`. -/
instance : One (StrandsAlgebra R α) :=
  ⟨∑ s : Finset α, idem s⟩

private theorem mul_def (x y : StrandsAlgebra R α) :
    x * y = (basis R α).constr R (fun φ ↦ (basis R α).constr R fun ψ ↦
      (if φ.Composable ψ then of (φ.trans ψ) else 0 : StrandsAlgebra R α)) x y :=
  (rfl)

/-- The idempotents `I(s)` sum to the unit of the strands algebra. -/
theorem sum_idem : ∑ s : Finset α, (idem s : StrandsAlgebra R α) = 1 :=
  (rfl)

/-- The product of two basis elements of the strands algebra is their composite if they are
composable and zero otherwise. -/
theorem of_mul_of (φ ψ : StrandDiagram α) :
    (of φ * of ψ : StrandsAlgebra R α) = if φ.Composable ψ then of (φ.trans ψ) else 0 := by
  rw [mul_def, ← basis_apply φ, ← basis_apply ψ, Module.Basis.constr_basis,
    Module.Basis.constr_basis]

@[simp]
theorem of_mul_of_of_composable {φ ψ : StrandDiagram α} (h : φ.Composable ψ) :
    (of φ * of ψ : StrandsAlgebra R α) = of (φ.trans ψ) := by
  simp [of_mul_of, h]

theorem of_mul_of_of_not_composable {φ ψ : StrandDiagram α} (h : ¬φ.Composable ψ) :
    (of φ * of ψ : StrandsAlgebra R α) = 0 := by
  simp [of_mul_of, h]

/-- Multiplying a basis element `φ` on the left by `I(s)` projects onto the diagrams starting at
`s`: the product is `φ` when `s` is the source of `φ` and zero otherwise. -/
theorem idem_mul_of (s : Finset α) (φ : StrandDiagram α) :
    (idem s * of φ : StrandsAlgebra R α) = if s = φ.source then of φ else 0 := by
  rw [idem_def, of_mul_of]
  simp only [StrandDiagram.composable_idOn_left_iff]
  split_ifs with h
  · rw [StrandDiagram.idOn_trans_of_eq_source h]
  · rfl

/-- Multiplying a basis element `φ` on the right by `I(t)` projects onto the diagrams ending at
`t`: the product is `φ` when `t` is the target of `φ` and zero otherwise. -/
theorem of_mul_idem (φ : StrandDiagram α) (t : Finset α) :
    (of φ * idem t : StrandsAlgebra R α) = if φ.target = t then of φ else 0 := by
  rw [idem_def, of_mul_of]
  simp only [StrandDiagram.composable_idOn_right_iff]
  split_ifs with h
  · rw [StrandDiagram.trans_idOn_of_target_eq h]
  · rfl

@[simp]
theorem idem_source_mul_of (φ : StrandDiagram α) :
    (idem φ.source * of φ : StrandsAlgebra R α) = of φ := by
  simp [idem_mul_of]

@[simp]
theorem of_mul_idem_target (φ : StrandDiagram α) :
    (of φ * idem φ.target : StrandsAlgebra R α) = of φ := by
  simp [of_mul_idem]

/-- The idempotents `I(s)` are orthogonal: `I(s) I(t)` is `I(s)` when `s = t` and zero
otherwise. -/
@[simp]
theorem idem_mul_idem (s t : Finset α) :
    (idem s * idem t : StrandsAlgebra R α) = if s = t then idem s else 0 := by
  rw [idem_def t, idem_mul_of, StrandDiagram.source_idOn]
  split_ifs with h
  · rw [h, idem_def]
  · rfl

theorem idem_mul_idem_of_ne {s t : Finset α} (h : s ≠ t) :
    (idem s * idem t : StrandsAlgebra R α) = 0 := by
  simp [idem_mul_idem, h]

instance : NonUnitalNonAssocSemiring (StrandsAlgebra R α) where
  left_distrib _ _ _ := by simp only [mul_def, map_add]
  right_distrib _ _ z := by simp only [mul_def, map_add, LinearMap.add_apply]
  zero_mul _ := by simp only [mul_def, map_zero, LinearMap.zero_apply]
  mul_zero _ := by simp only [mul_def, map_zero]

instance : IsScalarTower R (StrandsAlgebra R α) (StrandsAlgebra R α) where
  smul_assoc _ _ _ := by simp only [smul_eq_mul, mul_def, map_smul, LinearMap.smul_apply]

instance : SMulCommClass R (StrandsAlgebra R α) (StrandsAlgebra R α) where
  smul_comm _ x _ := by simp only [smul_eq_mul, mul_def, map_smul]

instance : Semiring (StrandsAlgebra R α) where
  mul_assoc x y z := by
    -- By linearity in each factor it suffices to treat basis elements, where both bracketings
    -- are nonzero under the same condition.
    induction x using induction_on with
    | zero => simp only [zero_mul]
    | add x x' hx hx' => simp only [add_mul, hx, hx']
    | smul_of r φ =>
      induction y using induction_on with
      | zero => simp only [zero_mul, mul_zero]
      | add y y' hy hy' => simp only [add_mul, mul_add, hy, hy']
      | smul_of s ψ =>
        induction z using induction_on with
        | zero => simp only [mul_zero]
        | add z z' hz hz' => simp only [mul_add, hz, hz']
        | smul_of t χ =>
          simp only [smul_mul_assoc, mul_smul_comm]
          have h := StrandDiagram.trans_composable_and_composable_iff φ ψ χ
          by_cases hφψ : φ.Composable ψ <;> by_cases hψχ : ψ.Composable χ <;>
            simp only [of_mul_of, hφψ, hψχ, ↓reduceIte, zero_mul, mul_zero] <;>
            simp_all [StrandDiagram.trans_assoc]
  one_mul x := by
    induction x using induction_on with
    | zero => exact mul_zero 1
    | add x y hx hy => rw [mul_add, hx, hy]
    | smul_of r φ => simp [mul_smul_comm, ← sum_idem, Finset.sum_mul, idem_mul_of]
  mul_one x := by
    induction x using induction_on with
    | zero => exact zero_mul 1
    | add x y hx hy => rw [add_mul, hx, hy]
    | smul_of r φ => simp [smul_mul_assoc, ← sum_idem, Finset.mul_sum, of_mul_idem]

instance : Algebra R (StrandsAlgebra R α) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

instance {R : Type*} [CommRing R] : Ring (StrandsAlgebra R α) where
  __ := (inferInstance : Semiring (StrandsAlgebra R α))
  __ := (inferInstance : AddCommGroup (StrandsAlgebra R α))

theorem isIdempotentElem_idem (s : Finset α) : IsIdempotentElem (idem s : StrandsAlgebra R α) := by
  simp [IsIdempotentElem, idem_mul_idem]

/-- **Multiplicativity is a basis-level condition.** An `R`-linear map out of the strands
algebra that is multiplicative on pairs of basis elements is multiplicative. -/
theorem map_mul_of_basis {A : Type*} [NonUnitalNonAssocSemiring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] (f : StrandsAlgebra R α →ₗ[R] A)
    (h : ∀ φ ψ, f (of φ * of ψ) = f (of φ) * f (of ψ)) (x y : StrandsAlgebra R α) :
    f (x * y) = f x * f y := by
  induction x using induction_on with
  | zero => simp only [zero_mul, map_zero]
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
  | smul_of r φ =>
    induction y using induction_on with
    | zero => simp only [mul_zero, map_zero]
    | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
    | smul_of s ψ => simp only [smul_mul_assoc, mul_smul_comm, map_smul, h]

/-- The coefficient of `χ` in a product is the sum of the products of the coefficients of the
pairs of composable diagrams whose composite is `χ`. -/
theorem repr_mul_apply [Fintype (StrandDiagram α)] (x y : StrandsAlgebra R α)
    (χ : StrandDiagram α) :
    (basis R α).repr (x * y) χ = ∑ φ, ∑ ψ, if φ.Composable ψ ∧ φ.trans ψ = χ then
      (basis R α).repr x φ * (basis R α).repr y ψ else 0 := by
  conv_lhs => rw [← (basis R α).sum_repr x, ← (basis R α).sum_repr y, Finset.sum_mul_sum]
  simp only [map_sum, Finset.sum_apply', smul_mul_smul_comm, basis_apply, map_smul,
    Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun φ _ ↦ Finset.sum_congr rfl fun ψ _ ↦ ?_
  rw [of_mul_of]
  by_cases h : φ.Composable ψ
  · rw [ite_eq_left h, ← basis_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h' : φ.trans ψ = χ <;> simp [h, h']
  · simp [h]

end StrandsAlgebra

end TauCeti
