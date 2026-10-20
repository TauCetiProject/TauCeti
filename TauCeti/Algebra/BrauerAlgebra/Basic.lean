/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import TauCeti.Combinatorics.Brauer.Associativity
public import TauCeti.Combinatorics.Brauer.Generator
public import TauCeti.Combinatorics.Brauer.WeightedAssociativity

/-!
# The Brauer algebra

The **Brauer algebra** `B_k(δ)` on `k` strands with loop value `δ`, over a commutative semiring
`R`, is the free `R`-module on the Brauer diagrams on `k` strands (`TauCeti.BrauerDiagram k`),
multiplied by stacking: for diagrams `D₁` and `D₂`,

`D₁ * D₂ = δ ^ c • (D₁ ∘ D₂)`,

where `D₁ ∘ D₂ = TauCeti.composeDiagram D₁ D₂` is the diagram read off by placing `D₁` above `D₂`
and `c = TauCeti.middleLoopCount D₁ D₂` is the number of closed loops left in the middle. It is a
unital associative `R`-algebra with the identity diagram as unit and the diagrams as a basis, so
it has rank `(2 * k - 1)‼`. Brauer introduced it because, for `V = ℂⁿ` with its standard
symmetric form, `B_k(n)` acts on the tensor power `V^{⊗k}` with image the commutant of the
orthogonal group, and with `δ = -2l` the same holds for the symplectic group on `ℂ^{2l}`. This file
builds the algebra itself; its action on tensor powers is not constructed here.

All of the combinatorics is already available: stacking is associative
(`TauCeti.composeDiagram_assoc`), the loop counts of the two bracketings of a triple stack agree
(`TauCeti.middleLoopCount_add_middleLoopCount_composeDiagram`), and the identity diagram is a
two-sided unit for stacking that closes no loop. Those are exactly the associativity and unit laws
of the multiplication on the diagram basis, and bilinear extension does the rest.

The symmetric group sits inside: a permutation diagram closes no loop against anything, and
stacking permutation diagrams multiplies the permutations (`TauCeti.composeDiagram_permToBrauer`),
so `σ ↦ permToBrauer σ` extends to an injective algebra map from the group algebra of `Sₖ`
(`TauCeti.BrauerAlgebra.ofPerm`). The cap-cup generators satisfy Brauer's relations
`e * e = δ • e` and `s * e = e = e * s`.

## Main definitions

* `TauCeti.BrauerAlgebra R δ k`: the Brauer algebra, with its coefficients
  `TauCeti.BrauerAlgebra.coeff` in the diagram basis.
* `TauCeti.BrauerAlgebra.of`: the basis element of a Brauer diagram.
* `TauCeti.BrauerAlgebra.basis`: the diagram basis.
* `TauCeti.BrauerAlgebra.lift`: the algebra map out of the Brauer algebra extending an assignment
  on the diagrams that sends the identity diagram to `1` and obeys the loop rule.
* `TauCeti.BrauerAlgebra.ofPerm`: the algebra map from the group algebra of `Sₖ`.

## Main results

* `TauCeti.BrauerAlgebra.of_mul_of`: **the loop rule**, the multiplication on the diagram basis.
* `TauCeti.BrauerAlgebra.one_def`: the unit is the identity diagram.
* `TauCeti.BrauerAlgebra.finrank_eq_doubleFactorial`: the Brauer algebra has rank `(2 * k - 1)‼`.
* `TauCeti.BrauerAlgebra.algHom_ext`: an algebra map out of the Brauer algebra is determined by
  its values on the diagrams; `TauCeti.BrauerAlgebra.eq_lift` identifies it with a lift.
* `TauCeti.BrauerAlgebra.ofPerm_injective`: the group algebra of `Sₖ` embeds.
* `TauCeti.BrauerAlgebra.of_capCup_mul_of_capCup`,
  `TauCeti.BrauerAlgebra.of_permToBrauer_swap_mul_of_capCup` and
  `TauCeti.BrauerAlgebra.of_capCup_mul_of_permToBrauer_swap`: the relations `e * e = δ • e`,
  `s * e = e` and `e * s = e`.

## Implementation notes

`TauCeti.BrauerAlgebra R δ k` is a one-field structure around the coefficient function
`BrauerDiagram k →₀ R`, as Mathlib's `MonoidAlgebra` is, rather than a type synonym: the loop value
`δ` enters only the multiplication, and a structure keeps the loop-weighted product from being
confused with the pointwise product that `Finsupp` already carries. The additive and module
structures are transported from the coefficients along `TauCeti.BrauerAlgebra.coeffEquiv`.

The twisted monoid algebra `TauCeti.twistedMonoidAlgebra` does not apply: it twists a monoid by a
factor set with values in the units of the base ring, whereas the weight `δ ^ c` of the loop rule
is not a unit in general (it vanishes at `δ = 0`).

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
-/

public section

open scoped Nat

namespace TauCeti

/-- **The Brauer algebra** `B_k(δ)` on `k` strands with loop value `δ` over `R`: the free
`R`-module on the Brauer diagrams on `k` strands, with the multiplication that stacks two diagrams
and weights the result by `δ` to the number of closed loops left in the middle
(`TauCeti.BrauerAlgebra.of_mul_of`). An element is given by its coefficients in the diagram
basis. -/
structure BrauerAlgebra (R : Type*) [CommSemiring R] (δ : R) (k : ℕ) where
  /-- The element of the Brauer algebra with the given coefficients in the diagram basis. -/
  ofCoeff ::
  /-- The coefficients of an element of the Brauer algebra in the diagram basis. -/
  coeff : BrauerDiagram k →₀ R

namespace BrauerAlgebra

variable {R : Type*} [CommSemiring R] {δ : R} {k : ℕ}

/-- Two elements of the Brauer algebra are equal when their coefficients are. -/
@[ext]
theorem ext {x y : BrauerAlgebra R δ k} (h : x.coeff = y.coeff) : x = y := by
  cases x
  cases h
  rfl

@[simp]
theorem coeff_ofCoeff (f : BrauerDiagram k →₀ R) :
    (ofCoeff f : BrauerAlgebra R δ k).coeff = f := (rfl)

@[simp]
theorem ofCoeff_coeff (x : BrauerAlgebra R δ k) : ofCoeff x.coeff = x := (rfl)

variable (R δ k) in
/-- The coefficients in the diagram basis, as an equivalence. -/
def coeffEquiv : BrauerAlgebra R δ k ≃ (BrauerDiagram k →₀ R) where
  toFun := coeff
  invFun := ofCoeff
  left_inv _ := (rfl)
  right_inv _ := (rfl)

noncomputable instance : AddCommMonoid (BrauerAlgebra R δ k) := (coeffEquiv R δ k).addCommMonoid

@[simp]
theorem coeff_zero : (0 : BrauerAlgebra R δ k).coeff = 0 := (rfl)

@[simp]
theorem coeff_add (x y : BrauerAlgebra R δ k) : (x + y).coeff = x.coeff + y.coeff := (rfl)

variable (R δ k) in
/-- The coefficients in the diagram basis, as an additive equivalence. -/
noncomputable def coeffAddEquiv : BrauerAlgebra R δ k ≃+ (BrauerDiagram k →₀ R) :=
  (coeffEquiv R δ k).addEquiv

noncomputable instance : Module R (BrauerAlgebra R δ k) := (coeffAddEquiv R δ k).module R

@[simp]
theorem coeff_smul (r : R) (x : BrauerAlgebra R δ k) : (r • x).coeff = r • x.coeff := (rfl)

variable (R δ k) in
/-- The coefficients in the diagram basis, as a linear equivalence. -/
noncomputable def coeffLinearEquiv : BrauerAlgebra R δ k ≃ₗ[R] (BrauerDiagram k →₀ R) :=
  (coeffAddEquiv R δ k).linearEquiv R

@[simp]
theorem coeffLinearEquiv_apply (x : BrauerAlgebra R δ k) : coeffLinearEquiv R δ k x = x.coeff :=
  (rfl)

@[simp]
theorem coeffLinearEquiv_symm_apply (f : BrauerDiagram k →₀ R) :
    (coeffLinearEquiv R δ k).symm f = ofCoeff f := (rfl)

/-! ### The multiplication -/

variable (δ) in
/-- The loop-weighted stacking on coefficients, as a bilinear map: on basis vectors it sends
`(D₁, D₂)` to `δ ^ middleLoopCount D₁ D₂` times the basis vector of `composeDiagram D₁ D₂`. -/
noncomputable def mulCoeff :
    (BrauerDiagram k →₀ R) →ₗ[R] (BrauerDiagram k →₀ R) →ₗ[R] (BrauerDiagram k →₀ R) :=
  Finsupp.lsum R fun D₁ => LinearMap.smulRight LinearMap.id
    (Finsupp.lsum R fun D₂ => δ ^ middleLoopCount D₁ D₂ • Finsupp.lsingle (composeDiagram D₁ D₂))

/-- The loop-weighted stacking of two basis vectors of coefficients. -/
theorem mulCoeff_single_single (D₁ D₂ : BrauerDiagram k) (a b : R) :
    mulCoeff δ (Finsupp.single D₁ a) (Finsupp.single D₂ b) =
      Finsupp.single (composeDiagram D₁ D₂) (δ ^ middleLoopCount D₁ D₂ * (a * b)) := by
  simp only [mulCoeff, Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.id_apply,
    LinearMap.smul_apply, Finsupp.lsingle_apply, Finsupp.smul_single, smul_eq_mul]
  congr 1
  ring

/-- The loop-weighted stacking is associative: this is where the associativity of stacking
(`TauCeti.composeDiagram_assoc`) and the agreement of the loop counts of the two bracketings
(`TauCeti.middleLoopCount_add_middleLoopCount_composeDiagram`) enter. -/
theorem mulCoeff_assoc (f g h : BrauerDiagram k →₀ R) :
    mulCoeff δ (mulCoeff δ f g) h = mulCoeff δ f (mulCoeff δ g h) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | single D₁ a =>
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g₁ g₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | single D₂ b =>
  induction h using Finsupp.induction_linear with
  | zero => simp
  | add h₁ h₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | single D₃ c =>
  simp only [mulCoeff_single_single, composeDiagram_assoc]
  congr 1
  have hc := middleLoopCount_add_middleLoopCount_composeDiagram D₁ D₂ D₃
  calc δ ^ middleLoopCount (composeDiagram D₁ D₂) D₃ * (δ ^ middleLoopCount D₁ D₂ * (a * b) * c)
      = δ ^ (middleLoopCount D₁ D₂ + middleLoopCount (composeDiagram D₁ D₂) D₃) * (a * b * c) := by
        rw [pow_add]; ring
    _ = δ ^ middleLoopCount D₁ (composeDiagram D₂ D₃) * (a * (δ ^ middleLoopCount D₂ D₃ * (b * c)))
        := by rw [hc, pow_add]; ring

/-- The identity diagram is a left unit for the loop-weighted stacking. -/
theorem mulCoeff_one_left (f : BrauerDiagram k →₀ R) :
    mulCoeff δ (Finsupp.single (permToBrauer 1) 1) f = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | single D b => simp [mulCoeff_single_single]

/-- The identity diagram is a right unit for the loop-weighted stacking. -/
theorem mulCoeff_one_right (f : BrauerDiagram k →₀ R) :
    mulCoeff δ f (Finsupp.single (permToBrauer 1) 1) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | single D b => simp [mulCoeff_single_single]

noncomputable instance : Mul (BrauerAlgebra R δ k) where
  mul x y := ofCoeff (mulCoeff δ x.coeff y.coeff)

/-- The coefficients of a product are the loop-weighted stacking of the coefficients. -/
theorem coeff_mul (x y : BrauerAlgebra R δ k) : (x * y).coeff = mulCoeff δ x.coeff y.coeff :=
  (rfl)

noncomputable instance : One (BrauerAlgebra R δ k) where
  one := ofCoeff (Finsupp.single (permToBrauer 1) 1)

/-- The coefficients of the unit: the identity diagram, with coefficient `1`. -/
theorem coeff_one : (1 : BrauerAlgebra R δ k).coeff = Finsupp.single (permToBrauer 1) 1 := (rfl)

noncomputable instance instSemiring : Semiring (BrauerAlgebra R δ k) where
  left_distrib _ _ _ := ext <| by simp only [coeff_mul, coeff_add, map_add]
  right_distrib _ _ _ := ext <| by simp only [coeff_mul, coeff_add, map_add, LinearMap.add_apply]
  zero_mul _ := ext <| by simp only [coeff_mul, coeff_zero, map_zero, LinearMap.zero_apply]
  mul_zero _ := ext <| by simp only [coeff_mul, coeff_zero, map_zero]
  mul_assoc _ _ _ := ext <| by simp only [coeff_mul, mulCoeff_assoc]
  one_mul _ := ext <| by simp only [coeff_mul, coeff_one, mulCoeff_one_left]
  mul_one _ := ext <| by simp only [coeff_mul, coeff_one, mulCoeff_one_right]

noncomputable instance : Algebra R (BrauerAlgebra R δ k) :=
  Algebra.ofModule
    (fun _ _ _ => ext <| by simp only [coeff_mul, coeff_smul, map_smul, LinearMap.smul_apply])
    (fun _ _ _ => ext <| by simp only [coeff_mul, coeff_smul, map_smul])

/-! ### The ring structure over a commutative ring -/

section Ring

variable {R : Type*} [CommRing R] {δ : R} {k : ℕ}

noncomputable instance : AddCommGroup (BrauerAlgebra R δ k) := (coeffEquiv R δ k).addCommGroup

@[simp]
theorem coeff_neg (x : BrauerAlgebra R δ k) : (-x).coeff = -x.coeff := (rfl)

@[simp]
theorem coeff_sub (x y : BrauerAlgebra R δ k) : (x - y).coeff = x.coeff - y.coeff := (rfl)

noncomputable instance instRing : Ring (BrauerAlgebra R δ k) where
  __ := instSemiring
  __ := (inferInstance : AddCommGroup (BrauerAlgebra R δ k))

end Ring

/-! ### The diagram basis -/

/-- The basis element of the Brauer algebra at the Brauer diagram `D`. -/
noncomputable def of (D : BrauerDiagram k) : BrauerAlgebra R δ k :=
  ofCoeff (Finsupp.single D 1)

@[simp]
theorem coeff_of (D : BrauerDiagram k) :
    (of D : BrauerAlgebra R δ k).coeff = Finsupp.single D 1 := (rfl)

/-- An element with a single nonzero coefficient is a multiple of a basis element. -/
@[simp]
theorem ofCoeff_single (D : BrauerDiagram k) (r : R) :
    (ofCoeff (Finsupp.single D r) : BrauerAlgebra R δ k) = r • of D :=
  ext <| by simp [Finsupp.smul_single]

/-- **The loop rule.** The product of two diagrams is their stack, weighted by `δ` to the number
of closed loops left in the middle. -/
@[simp]
theorem of_mul_of (D₁ D₂ : BrauerDiagram k) :
    (of D₁ * of D₂ : BrauerAlgebra R δ k) =
      δ ^ middleLoopCount D₁ D₂ • of (composeDiagram D₁ D₂) := by
  ext : 1
  simp [coeff_mul, mulCoeff_single_single, Finsupp.smul_single]

/-- The unit of the Brauer algebra is the identity diagram. -/
theorem one_def : (1 : BrauerAlgebra R δ k) = of (permToBrauer 1) := ext coeff_one

variable (R δ k) in
/-- **The diagram basis** of the Brauer algebra. -/
noncomputable def basis : Module.Basis (BrauerDiagram k) R (BrauerAlgebra R δ k) :=
  .ofRepr (coeffLinearEquiv R δ k)

@[simp]
theorem basis_apply (D : BrauerDiagram k) : basis R δ k D = of D := (rfl)

@[simp]
theorem basis_repr (x : BrauerAlgebra R δ k) : (basis R δ k).repr x = x.coeff := (rfl)

instance : Module.Free R (BrauerAlgebra R δ k) := .of_basis (basis R δ k)

instance : Module.Finite R (BrauerAlgebra R δ k) := .of_basis (basis R δ k)

variable (R δ k) in
/-- **The rank of the Brauer algebra**: it is free on the `(2 * k - 1)‼` Brauer diagrams on `k`
strands. -/
theorem finrank_eq_doubleFactorial [StrongRankCondition R] :
    Module.finrank R (BrauerAlgebra R δ k) = (2 * k - 1)‼ := by
  rw [Module.finrank_eq_card_basis (basis R δ k), card_brauerDiagram]

/-- **An algebra map out of the Brauer algebra is determined by its values on the diagrams.** -/
@[ext]
theorem algHom_ext {A : Type*} [Semiring A] [Algebra R A] {f g : BrauerAlgebra R δ k →ₐ[R] A}
    (h : ∀ D, f (of D) = g (of D)) : f = g :=
  AlgHom.toLinearMap_injective <| (basis R δ k).ext fun D => by simpa using h D

section lift

variable {A : Type*} [Semiring A] [Algebra R A]

/-- **Maps out of the Brauer algebra.** An assignment of elements of an `R`-algebra to the
diagrams that sends the identity diagram to `1` and obeys the loop rule extends to an algebra
map. -/
noncomputable def lift (F : BrauerDiagram k → A) (h_one : F (permToBrauer 1) = 1)
    (h_mul : ∀ D₁ D₂, F D₁ * F D₂ = δ ^ middleLoopCount D₁ D₂ • F (composeDiagram D₁ D₂)) :
    BrauerAlgebra R δ k →ₐ[R] A :=
  have hF (D : BrauerDiagram k) : (basis R δ k).constr R F (of D) = F D :=
    (basis R δ k).constr_basis R F D
  AlgHom.ofLinearMap ((basis R δ k).constr R F) (by rw [one_def, hF, h_one]) fun x y =>
    LinearMap.congr_fun₂ (f := (LinearMap.mul R _).compr₂ ((basis R δ k).constr R F))
      (g := (LinearMap.mul R A).compl₁₂ ((basis R δ k).constr R F) ((basis R δ k).constr R F))
      ((basis R δ k).ext fun D₁ => (basis R δ k).ext fun D₂ => by
        simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
          basis_apply, of_mul_of, map_smul, hF, h_mul]) x y

@[simp]
theorem lift_of (F : BrauerDiagram k → A) (h_one : F (permToBrauer 1) = 1)
    (h_mul : ∀ D₁ D₂, F D₁ * F D₂ = δ ^ middleLoopCount D₁ D₂ • F (composeDiagram D₁ D₂))
    (D : BrauerDiagram k) : lift F h_one h_mul (of D : BrauerAlgebra R δ k) = F D :=
  (basis R δ k).constr_basis R F D

/-- An algebra map out of the Brauer algebra is the lift of its values on the diagrams. -/
theorem eq_lift (F : BrauerDiagram k → A) (h_one : F (permToBrauer 1) = 1)
    (h_mul : ∀ D₁ D₂, F D₁ * F D₂ = δ ^ middleLoopCount D₁ D₂ • F (composeDiagram D₁ D₂))
    {f : BrauerAlgebra R δ k →ₐ[R] A} (h : ∀ D, f (of D) = F D) :
    f = lift F h_one h_mul :=
  algHom_ext fun D => by simp [h]

end lift

/-! ### The symmetric group inside the Brauer algebra -/

/-- A permutation diagram closes no loop, so the permutation diagrams multiply as the
permutations do. -/
theorem of_permToBrauer_mul_of_permToBrauer (σ τ : Equiv.Perm (Fin k)) :
    (of (permToBrauer σ) * of (permToBrauer τ) : BrauerAlgebra R δ k) =
      of (permToBrauer (σ * τ)) := by
  simp

variable (R δ k) in
/-- **The group algebra of `Sₖ` inside the Brauer algebra**: the algebra map sending a permutation
to its diagram. -/
noncomputable def ofPerm : MonoidAlgebra R (Equiv.Perm (Fin k)) →ₐ[R] BrauerAlgebra R δ k :=
  MonoidAlgebra.lift R _ _
    { toFun σ := of (permToBrauer σ)
      map_one' := (rfl)
      map_mul' σ τ := (of_permToBrauer_mul_of_permToBrauer σ τ).symm }

@[simp]
theorem ofPerm_single (σ : Equiv.Perm (Fin k)) (r : R) :
    ofPerm R δ k (MonoidAlgebra.single σ r) = r • of (permToBrauer σ) :=
  MonoidAlgebra.lift_single ..

/-- The coefficients of the image of an element of the group algebra are its coefficients moved
along `permToBrauer`. -/
theorem coeff_ofPerm (x : MonoidAlgebra R (Equiv.Perm (Fin k))) :
    (ofPerm R δ k x).coeff = Finsupp.mapDomain permToBrauer x.coeff := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, Finsupp.mapDomain_add]
  | single σ r => simp [Finsupp.smul_single]

/-- **The group algebra of `Sₖ` embeds in the Brauer algebra**, because distinct permutations
have distinct diagrams. -/
theorem ofPerm_injective : Function.Injective (ofPerm R δ k) := fun x y h => by
  have := congrArg coeff h
  rw [coeff_ofPerm, coeff_ofPerm] at this
  exact MonoidAlgebra.ext (Finsupp.mapDomain_injective (permToBrauer_injective k) this)

/-! ### Brauer's relations for the cap-cup generators -/

/-- **`e * e = δ • e`**: stacking a cap-cup diagram on itself closes exactly one loop. -/
theorem of_capCup_mul_of_capCup {a b : Fin k} (hab : a ≠ b) :
    (of (capCup a b) * of (capCup a b) : BrauerAlgebra R δ k) = δ • of (capCup a b) := by
  rw [of_mul_of, composeDiagram_capCup_capCup, middleLoopCount_capCup_capCup hab, pow_one]

/-- **`s * e = e`**: the transposition of the pair of a cap-cup diagram, stacked above it, is
absorbed. -/
theorem of_permToBrauer_swap_mul_of_capCup (a b : Fin k) :
    (of (permToBrauer (Equiv.swap a b)) * of (capCup a b) : BrauerAlgebra R δ k) =
      of (capCup a b) := by
  rw [of_mul_of, composeDiagram_permToBrauer_swap_capCup, middleLoopCount_permToBrauer_left,
    pow_zero, one_smul]

/-- **`e * s = e`**: the transposition of the pair of a cap-cup diagram, stacked below it, is
absorbed. -/
theorem of_capCup_mul_of_permToBrauer_swap (a b : Fin k) :
    (of (capCup a b) * of (permToBrauer (Equiv.swap a b)) : BrauerAlgebra R δ k) =
      of (capCup a b) := by
  rw [of_mul_of, composeDiagram_capCup_permToBrauer_swap, middleLoopCount_permToBrauer_right,
    pow_zero, one_smul]

end BrauerAlgebra

end TauCeti
