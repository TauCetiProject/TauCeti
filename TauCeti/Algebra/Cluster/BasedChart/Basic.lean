/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sort
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic
public import TauCeti.Algebra.MvPolynomial.Laurent.Basic
public import TauCeti.LinearAlgebra.Matrix.FinsuppBilinForm

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Tactic.Ring

/-!
# Based quantum tori and based charts

For `R`, `u : Rˣ`, and `Λ : Matrix I I ℤ`, `TauCeti.formFactorSet u Λ` defines the based quantum
torus `TauCeti.basedTorus R u Λ` with monomials `X^a * X^b = u ^ Λ(a, b) • X^{a + b}` (isomorphic
to `TauCeti.LaurentRing R I` at `u = 1` or `Λ = 0`). `TauCeti.BasedChart R u Λ B` packages an
`R`-linearly independent `(u, Λ)`-monomial family in `B`, equivalent to injective `R`-algebra maps
`basedTorus R u Λ →ₐ[R] B` and reconstructed from quasi-commuting coordinates via
`TauCeti.orderedMonomial`.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Adv. Math. 195 (2005), §4.
* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, J. Amer. Math. Soc. 15 (2002), §3.
-/

public section

namespace TauCeti
section FactorSet
variable {R I : Type*} [CommSemiring R]
/-- The factor set `(ofAdd a, ofAdd b) ↦ u ^ Λ.finsuppBilinForm a b` on
`Multiplicative (I →₀ ℤ)`. -/
noncomputable def formFactorSet (u : Rˣ) (Λ : Matrix I I ℤ) :
    Multiplicative (I →₀ ℤ) → Multiplicative (I →₀ ℤ) → Rˣ :=
  fun g h ↦ u ^ Λ.finsuppBilinForm g.toAdd h.toAdd
@[simp] theorem formFactorSet_ofAdd (u : Rˣ) (Λ : Matrix I I ℤ) (a b : I →₀ ℤ) :
    formFactorSet u Λ (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) =
      u ^ Λ.finsuppBilinForm a b := (rfl)
@[simp] theorem formFactorSet_one_left_unit (Λ : Matrix I I ℤ) : formFactorSet (1 : Rˣ) Λ = 1 := by
  ext; simp [formFactorSet]
@[simp] theorem formFactorSet_zero_right_matrix (u : Rˣ) :
    formFactorSet u (0 : Matrix I I ℤ) = 1 := by ext; simp [formFactorSet]
instance isFactorSet_formFactorSet (u : Rˣ) (Λ : Matrix I I ℤ) :
    IsFactorSet (formFactorSet u Λ) where
  cocycle _ _ _ := by
    simp only [formFactorSet, toAdd_mul, ← zpow_add]
    congr 1; simp only [map_add, LinearMap.add_apply]; ring
  one_left _ := by simp [formFactorSet]
end FactorSet
/-- **The based quantum torus** `T(R, u, Λ)`, the twisted group algebra of `Multiplicative (I →₀ ℤ)`
for `formFactorSet u Λ`. -/
noncomputable abbrev basedTorus (R : Type*) [CommSemiring R] (u : Rˣ) {I : Type*}
    (Λ : Matrix I I ℤ) := twistedMonoidAlgebra R (Multiplicative (I →₀ ℤ)) (formFactorSet u Λ)
namespace BasedTorus
section General
variable {R I : Type*} [CommSemiring R] {u : Rˣ} {Λ : Matrix I I ℤ}
/-- The normalized basis monomial `X^a` of `basedTorus R u Λ` at exponent `a : I →₀ ℤ`. -/
noncomputable def monomial (a : I →₀ ℤ) : basedTorus R u Λ :=
  TwistedMonoidAlgebra.of (Multiplicative.ofAdd a)
theorem monomial_def (a : I →₀ ℤ) :
    (monomial a : basedTorus R u Λ) = TwistedMonoidAlgebra.of (Multiplicative.ofAdd a) := (rfl)
@[simp] theorem monomial_zero : (monomial 0 : basedTorus R u Λ) = 1 := TwistedMonoidAlgebra.of_one
@[simp] theorem monomial_mul (a b : I →₀ ℤ) :
    (monomial a : basedTorus R u Λ) * monomial b =
      ((u ^ Λ.finsuppBilinForm a b : Rˣ) : R) • monomial (a + b) := by
  simp [monomial_def, ← ofAdd_add]
/-- Each normalized monomial `X^a` as a unit of `basedTorus R u Λ`. -/
noncomputable def unitMonomial (a : I →₀ ℤ) : (basedTorus R u Λ)ˣ where
  val := monomial a
  inv := (((u ^ Λ.finsuppBilinForm a (-a))⁻¹ : Rˣ) : R) • monomial (-a)
  val_inv := by simp [smul_smul, ← Units.val_mul]
  inv_val := by simp [smul_smul, ← Units.val_mul]
@[simp] theorem val_unitMonomial (a : I →₀ ℤ) :
    ((unitMonomial a : (basedTorus R u Λ)ˣ) : basedTorus R u Λ) = monomial a := (rfl)
theorem inv_unitMonomial_of_self_eq_zero {a : I →₀ ℤ} (ha : Λ.finsuppBilinForm a a = 0) :
    (unitMonomial a : (basedTorus R u Λ)ˣ)⁻¹ = unitMonomial (-a) :=
  inv_eq_of_mul_eq_one_right <| Units.ext <| by simp [ha]
theorem inv_unitMonomial_of_isAlt (hΛ : Λ.finsuppBilinForm.IsAlt) (a : I →₀ ℤ) :
    (unitMonomial a : (basedTorus R u Λ)ˣ)⁻¹ = unitMonomial (-a) :=
  inv_unitMonomial_of_self_eq_zero (hΛ.self_eq_zero a)
/-- The `i`-th coordinate generator `X_i = X^{e_i}` of `basedTorus R u Λ`. -/
noncomputable def X (i : I) : basedTorus R u Λ := monomial (Finsupp.single i 1)
theorem X_def (i : I) : (X i : basedTorus R u Λ) = monomial (Finsupp.single i 1) := (rfl)
/-- The `i`-th coordinate generator `X_i` as a unit of `basedTorus R u Λ`. -/
noncomputable def unitX (i : I) : (basedTorus R u Λ)ˣ := unitMonomial (Finsupp.single i 1)
@[simp] theorem val_unitX (i : I) : ((unitX i : (basedTorus R u Λ)ˣ) : basedTorus R u Λ) = X i :=
  (rfl)
theorem monomial_mul_comm (a b : I →₀ ℤ) :
    (monomial a : basedTorus R u Λ) * monomial b =
      ((u ^ (Λ.finsuppBilinForm a b - Λ.finsuppBilinForm b a) : Rˣ) : R) •
        (monomial b * monomial a) := by
  rw [monomial_mul, monomial_mul, add_comm b a, smul_smul, ← Units.val_mul, ← zpow_add,
    sub_add_cancel]
theorem monomial_mul_comm_of_isAlt (hΛ : Λ.finsuppBilinForm.IsAlt) (a b : I →₀ ℤ) :
    (monomial a : basedTorus R u Λ) * monomial b =
      ((u ^ (2 * Λ.finsuppBilinForm a b) : Rˣ) : R) • (monomial b * monomial a) := by
  rw [monomial_mul_comm, ← hΛ.neg_eq a b]; congr 3; ring
theorem X_mul_X_of_isAlt (hΛ : Λ.finsuppBilinForm.IsAlt) (i j : I) :
    (X i : basedTorus R u Λ) * X j = ((u ^ (2 * Λ i j) : Rˣ) : R) • (X j * X i) := by
  simpa [X_def, Matrix.finsuppBilinForm_single_single] using
    monomial_mul_comm_of_isAlt (R := R) (u := u) hΛ (Finsupp.single i 1) (Finsupp.single j 1)
variable (R u Λ) in
/-- The `R`-basis of `basedTorus R u Λ` indexed by `I →₀ ℤ`. -/
noncomputable def basis : Module.Basis (I →₀ ℤ) R (basedTorus R u Λ) :=
  (TwistedMonoidAlgebra.basis R (Multiplicative (I →₀ ℤ)) (formFactorSet u Λ)).reindex
    Multiplicative.ofAdd.symm
@[simp] theorem basis_apply (a : I →₀ ℤ) : basis R u Λ a = monomial a := by
  simp [basis, monomial_def]
@[ext] theorem algHom_ext {A : Type*} [Semiring A] [Algebra R A]
    {f g : basedTorus R u Λ →ₐ[R] A} (h : ∀ a : I →₀ ℤ, f (monomial a) = g (monomial a)) : f = g :=
  TwistedMonoidAlgebra.algHom_ext fun x ↦ h x.toAdd
/-- Canonical `R`-algebra isomorphism `basedTorus R u Λ ≃ₐ[R] LaurentRing R I` when
`formFactorSet u Λ = 1`. -/
noncomputable def laurentRingEquivOfFactorSetEqOne (h : formFactorSet u Λ = 1) :
    basedTorus R u Λ ≃ₐ[R] LaurentRing R I :=
  (TwistedMonoidAlgebra.equivOfCoboundary
      (1 : Multiplicative (I →₀ ℤ) → Multiplicative (I →₀ ℤ) → Rˣ)
      (formFactorSet u Λ) 1 (by simp [h])).trans <|
    (TwistedMonoidAlgebra.monoidAlgebraEquiv R (Multiplicative (I →₀ ℤ))).trans
      (AddMonoidAlgebra.toMultiplicativeAlgEquiv R R (I →₀ ℤ)).symm
@[simp] theorem laurentRingEquivOfFactorSetEqOne_monomial (h : formFactorSet u Λ = 1)
    (a : I →₀ ℤ) :
    laurentRingEquivOfFactorSetEqOne h (monomial a) = AddMonoidAlgebra.single a 1 := by
  apply (AddMonoidAlgebra.toMultiplicativeAlgEquiv R R (I →₀ ℤ)).injective
  simp [laurentRingEquivOfFactorSetEqOne, monomial_def]
@[simp] theorem laurentRingEquivOfFactorSetEqOne_symm_single (h : formFactorSet u Λ = 1)
    (a : I →₀ ℤ) (r : R) :
    (laurentRingEquivOfFactorSetEqOne h).symm (AddMonoidAlgebra.single a r) = r • monomial a := by
  apply (laurentRingEquivOfFactorSetEqOne h).injective; simp [AddMonoidAlgebra.smul_single]
/-- At `u = 1`, `basedTorus R 1 Λ ≃ₐ[R] LaurentRing R I`. -/
noncomputable def laurentRingEquivOfUnitOne (R : Type*) [CommSemiring R] {I : Type*}
    (Λ : Matrix I I ℤ) : basedTorus R 1 Λ ≃ₐ[R] LaurentRing R I :=
  laurentRingEquivOfFactorSetEqOne (formFactorSet_one_left_unit Λ)
@[simp] theorem laurentRingEquivOfUnitOne_monomial (R : Type*) [CommSemiring R] {I : Type*}
    (Λ : Matrix I I ℤ) (a : I →₀ ℤ) :
    laurentRingEquivOfUnitOne R Λ (monomial a) = AddMonoidAlgebra.single a 1 :=
  laurentRingEquivOfFactorSetEqOne_monomial _ a
/-- At `Λ = 0`, `basedTorus R u 0 ≃ₐ[R] LaurentRing R I`. -/
noncomputable def laurentRingEquivOfFormZero (R : Type*) [CommSemiring R] (u : Rˣ) (I : Type*) :
    basedTorus R u (0 : Matrix I I ℤ) ≃ₐ[R] LaurentRing R I :=
  laurentRingEquivOfFactorSetEqOne (formFactorSet_zero_right_matrix u)
@[simp] theorem laurentRingEquivOfFormZero_monomial (R : Type*) [CommSemiring R] (u : Rˣ)
    {I : Type*} (a : I →₀ ℤ) :
    laurentRingEquivOfFormZero R u I (monomial a) = AddMonoidAlgebra.single a 1 :=
  laurentRingEquivOfFactorSetEqOne_monomial _ a
end General
end BasedTorus
private theorem map_algebraMap_comm {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
    (w : Rˣ) (x : Bˣ) :
    Units.map (algebraMap R B).toMonoidHom w * x = x * Units.map (algebraMap R B).toMonoidHom w :=
  Units.ext <| Algebra.commutes _ _
theorem units_zpow_mul_of_quasiComm {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
    {w : Rˣ} {x y : Bˣ} (h : x * y = Units.map (algebraMap R B).toMonoidHom w * (y * x))
    (m : ℤ) : x ^ m * y = Units.map (algebraMap R B).toMonoidHom (w ^ m) * (y * x ^ m) := by
  let cw := Units.map (algebraMap R B).toMonoidHom w
  have hyx : SemiconjBy y x (cw⁻¹ * x) := by
    unfold SemiconjBy; apply mul_left_cancel (a := cw)
    rw [← h, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  have hcomm : Commute cw⁻¹ x := by rw [← map_inv]; exact map_algebraMap_comm w⁻¹ x
  have hpow := (hyx.zpow_right m).eq
  rw [hcomm.mul_zpow m, mul_assoc] at hpow
  rw [hpow, ← mul_assoc, ← map_inv, ← map_zpow, inv_zpow', ← map_mul, ← zpow_add,
    add_neg_cancel, zpow_zero, map_one, one_mul]
theorem normalizedMonomial_eq_of_single_one_eq {R I B : Type*} [CommSemiring R] [Semiring B]
    [Algebra R B] {u : Rˣ} {Λ : Matrix I I ℤ} {M₁ M₂ : (I →₀ ℤ) → Bˣ}
    (h₁0 : M₁ 0 = 1) (h₂0 : M₂ 0 = 1)
    (h₁m : ∀ a b, M₁ a * M₁ b =
      Units.map (algebraMap R B).toMonoidHom (u ^ Λ.finsuppBilinForm a b) * M₁ (a + b))
    (h₂m : ∀ a b, M₂ a * M₂ b =
      Units.map (algebraMap R B).toMonoidHom (u ^ Λ.finsuppBilinForm a b) * M₂ (a + b))
    (h : ∀ i, M₁ (Finsupp.single i 1) = M₂ (Finsupp.single i 1)) : M₁ = M₂ := by
  have hadd {a b : I →₀ ℤ} (ha : M₁ a = M₂ a) (hb : M₁ b = M₂ b) : M₁ (a + b) = M₂ (a + b) :=
    mul_left_cancel <| (h₁m a b).symm.trans <| by rw [ha, hb, h₂m]
  have hsub {a b : I →₀ ℤ} (hab : M₁ (a + b) = M₂ (a + b)) (hb : M₁ b = M₂ b) : M₁ a = M₂ a :=
    mul_right_cancel <| (h₁m a b).trans <| by rw [hab, ← h₂m, hb]
  funext a; induction a using Finsupp.induction_linear with
  | zero => simp [h₁0, h₂0]
  | add _ _ ha hb => exact hadd ha hb
  | single i n =>
    induction n using Int.induction_on with
    | zero => simp [h₁0, h₂0]
    | succ _ hk => rw [Finsupp.single_add]; exact hadd hk (h i)
    | pred _ hk =>
      exact hsub (b := Finsupp.single i 1) (by simpa [← Finsupp.single_add] using hk) (h i)
/-- **A based chart** for `(R, u, Λ)` in an `R`-algebra `B`: an `R`-linearly independent
`(u, Λ)`-multiplicative family of units `M : (I →₀ ℤ) → Bˣ`. -/
structure BasedChart (R : Type*) [CommSemiring R] (u : Rˣ) {I : Type*}
    (Λ : Matrix I I ℤ) (B : Type*) [Semiring B] [Algebra R B] where
  /-- The normalized monomial `M(a)` at exponent `a`, as a unit of `B`. -/
  monomial : (I →₀ ℤ) → Bˣ
  /-- The normalized monomial at `0` is `1`. -/
  monomial_zero : monomial 0 = 1
  /-- Multiplication of normalized monomials is twisted by `u ^ Λ(a, b)`. -/
  monomial_mul : ∀ a b, monomial a * monomial b =
    Units.map (algebraMap R B).toMonoidHom (u ^ Λ.finsuppBilinForm a b) * monomial (a + b)
  /-- The normalized monomials are `R`-linearly independent in `B`. -/
  linearIndependent : LinearIndependent R fun a ↦ (monomial a : B)
namespace BasedChart
section Basic
variable {R I J B B' : Type*} [CommSemiring R] {u : Rˣ} {Λ : Matrix I I ℤ}
  [Semiring B] [Algebra R B] [Semiring B'] [Algebra R B']
@[ext] theorem ext {c₁ c₂ : BasedChart R u Λ B} (h : ∀ a, c₁.monomial a = c₂.monomial a) :
    c₁ = c₂ := by cases c₁; cases c₂; congr; exact funext h
section Chart
variable (c : BasedChart R u Λ B)
@[simp] theorem val_monomial_zero : (c.monomial 0 : B) = 1 := by simp [c.monomial_zero]
theorem val_monomial_mul (a b : I →₀ ℤ) :
    (c.monomial a : B) * c.monomial b =
      ((u ^ Λ.finsuppBilinForm a b : Rˣ) : R) • (c.monomial (a + b) : B) := by
  rw [← Units.val_mul, c.monomial_mul, Units.val_mul, Units.coe_map]; simp [Algebra.smul_def]
theorem monomial_mul_comm (a b : I →₀ ℤ) :
    c.monomial a * c.monomial b =
      Units.map (algebraMap R B).toMonoidHom
        (u ^ (Λ.finsuppBilinForm a b - Λ.finsuppBilinForm b a)) *
        (c.monomial b * c.monomial a) := by
  rw [c.monomial_mul, c.monomial_mul, add_comm b a, ← mul_assoc, ← map_mul, ← zpow_add,
    sub_add_cancel]
theorem monomial_mul_comm_of_isAlt (hΛ : Λ.finsuppBilinForm.IsAlt) (a b : I →₀ ℤ) :
    c.monomial a * c.monomial b =
      Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ.finsuppBilinForm a b)) *
        (c.monomial b * c.monomial a) := by
  rw [c.monomial_mul_comm, ← hΛ.neg_eq a b]; congr 3; ring
theorem inv_monomial_of_self_eq_zero {a : I →₀ ℤ} (ha : Λ.finsuppBilinForm a a = 0) :
    (c.monomial a)⁻¹ = c.monomial (-a) :=
  inv_eq_of_mul_eq_one_right <| by simpa [ha, c.monomial_zero] using c.monomial_mul a (-a)
/-- The `i`-th coordinate `X_i = M(e_i)` of a based chart. -/
noncomputable def coordinate (i : I) : Bˣ := c.monomial (Finsupp.single i 1)
theorem coordinate_def (i : I) : c.coordinate i = c.monomial (Finsupp.single i 1) := (rfl)
theorem monomial_single_of_diag_zero {i : I} (hi : Λ i i = 0) (n : ℤ) :
    c.monomial (Finsupp.single i n) = c.coordinate i ^ n := by
  have hmul (p q : ℤ) :
      c.monomial (Finsupp.single i p) * c.monomial (Finsupp.single i q) =
        c.monomial (Finsupp.single i (p + q)) := by
    rw [c.monomial_mul, Finsupp.single_add, Matrix.finsuppBilinForm_single_single, hi, mul_zero,
      zpow_zero, map_one, one_mul]
  induction n using Int.induction_on with
  | zero => simp [c.monomial_zero]
  | succ _ hk => rw [← hmul, hk, ← coordinate_def, ← zpow_add_one]
  | pred _ hk =>
    rw [zpow_sub_one]
    exact eq_mul_inv_of_mul_eq (by rw [← hk, coordinate_def, hmul, sub_add_cancel])
theorem coordinate_mul_comm_of_isAlt (hΛ : Λ.finsuppBilinForm.IsAlt) (i j : I) :
    c.coordinate i * c.coordinate j =
      Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ i j)) *
        (c.coordinate j * c.coordinate i) := by
  simpa [coordinate_def, Matrix.finsuppBilinForm_single_single] using
    c.monomial_mul_comm_of_isAlt hΛ (Finsupp.single i 1) (Finsupp.single j 1)
/-- The chart map on finitely supported coefficient families: `f ↦ ∑_a f(a) • M(a)`. -/
noncomputable def eval : ((I →₀ ℤ) →₀ R) →ₗ[R] B :=
  Finsupp.linearCombination R fun a ↦ (c.monomial a : B)
theorem eval_def : c.eval = Finsupp.linearCombination R fun a ↦ (c.monomial a : B) := (rfl)
@[simp] theorem eval_single (a : I →₀ ℤ) (r : R) :
    c.eval (Finsupp.single a r) = r • (c.monomial a : B) := by simp [eval_def]
theorem eval_injective : Function.Injective c.eval := c.linearIndependent
/-- The `R`-algebra map `basedTorus R u Λ →ₐ[R] B` induced by `c`. -/
noncomputable def toAlgHom : basedTorus R u Λ →ₐ[R] B :=
  TwistedMonoidAlgebra.lift (fun g ↦ (c.monomial g.toAdd : B)) (by simp)
    fun g h ↦ c.val_monomial_mul g.toAdd h.toAdd
@[simp] theorem toAlgHom_monomial (a : I →₀ ℤ) :
    c.toAlgHom (BasedTorus.monomial a) = c.monomial a := TwistedMonoidAlgebra.lift_of ..
@[simp] theorem toAlgHom_X (i : I) :
    c.toAlgHom (BasedTorus.X i) = c.coordinate i := c.toAlgHom_monomial (Finsupp.single i 1)
@[simp] theorem unitsMap_toAlgHom_unitMonomial (a : I →₀ ℤ) :
    Units.map (c.toAlgHom : basedTorus R u Λ →* B) (BasedTorus.unitMonomial a) = c.monomial a :=
  Units.ext <| c.toAlgHom_monomial a
theorem eval_eq_toAlgHom_comp_repr_symm :
    c.eval = c.toAlgHom.toLinearMap.comp (BasedTorus.basis R u Λ).repr.symm.toLinearMap :=
  Finsupp.lhom_ext' fun _ ↦ LinearMap.ext fun _ ↦ by simp
theorem toAlgHom_injective : Function.Injective c.toAlgHom := fun _ _ h ↦
  (BasedTorus.basis R u Λ).repr.injective <| c.eval_injective <| by
    rw [c.eval_eq_toAlgHom_comp_repr_symm]; simpa using h
end Chart
theorem ext_coordinate {c₁ c₂ : BasedChart R u Λ B}
    (h : ∀ i, c₁.coordinate i = c₂.coordinate i) : c₁ = c₂ :=
  BasedChart.ext <| congr_fun <| normalizedMonomial_eq_of_single_one_eq c₁.monomial_zero
    c₂.monomial_zero c₁.monomial_mul c₂.monomial_mul h
variable (R u Λ) in
/-- The tautological based chart of `basedTorus R u Λ` in itself. -/
noncomputable def tautological : BasedChart R u Λ (basedTorus R u Λ) where
  monomial := BasedTorus.unitMonomial
  monomial_zero := Units.ext BasedTorus.monomial_zero
  monomial_mul _ _ := Units.ext <| by
    rw [Units.val_mul, Units.val_mul, Units.coe_map]; simp [Algebra.smul_def]
  linearIndependent := by convert (BasedTorus.basis R u Λ).linearIndependent using 1; ext; simp
@[simp] theorem tautological_monomial (a : I →₀ ℤ) :
    (tautological R u Λ).monomial a = BasedTorus.unitMonomial a := (rfl)
@[simp] theorem tautological_toAlgHom :
    (tautological R u Λ).toAlgHom = AlgHom.id R (basedTorus R u Λ) := by ext; simp
/-- Transport a based chart along an injective `R`-algebra homomorphism `B →ₐ[R] B'`. -/
def map (f : B →ₐ[R] B') (hf : Function.Injective f) (c : BasedChart R u Λ B) :
    BasedChart R u Λ B' where
  monomial a := Units.map f.toMonoidHom (c.monomial a)
  monomial_zero := by simp [c.monomial_zero]
  monomial_mul a b := by
    rw [← map_mul, c.monomial_mul, map_mul]
    exact congrArg (· * _) (Units.ext <| by
      rw [Units.coe_map, Units.coe_map, Units.coe_map]; exact f.commutes _)
  linearIndependent _ _ hl := c.linearIndependent <| hf <| by
    simpa [Finsupp.linearCombination_apply, Finsupp.sum, map_sum] using hl
@[simp] theorem map_monomial (f : B →ₐ[R] B') (hf : Function.Injective f) (c : BasedChart R u Λ B)
    (a : I →₀ ℤ) : (c.map f hf).monomial a = Units.map f.toMonoidHom (c.monomial a) := (rfl)
@[simp] theorem map_coordinate (f : B →ₐ[R] B') (hf : Function.Injective f) (c : BasedChart R u Λ B)
    (i : I) : (c.map f hf).coordinate i = Units.map f.toMonoidHom (c.coordinate i) := (rfl)
@[simp] theorem map_toAlgHom (f : B →ₐ[R] B') (hf : Function.Injective f)
    (c : BasedChart R u Λ B) : (c.map f hf).toAlgHom = f.comp c.toAlgHom := by ext; simp
/-- Equivalence of based charts induced by `B ≃ₐ[R] B'`. -/
def congrAlgEquiv (e : B ≃ₐ[R] B') : BasedChart R u Λ B ≃ BasedChart R u Λ B' where
  toFun := map e.toAlgHom (by rw [AlgEquiv.coe_toAlgHom]; exact e.injective)
  invFun := map e.symm.toAlgHom (by rw [AlgEquiv.coe_toAlgHom]; exact e.symm.injective)
  left_inv _ := BasedChart.ext fun _ ↦ Units.ext (by simp)
  right_inv _ := BasedChart.ext fun _ ↦ Units.ext (by simp)
@[simp] theorem congrAlgEquiv_monomial (e : B ≃ₐ[R] B') (c : BasedChart R u Λ B) (a : I →₀ ℤ) :
    (congrAlgEquiv e c).monomial a = Units.map e.toAlgHom.toMonoidHom (c.monomial a) := (rfl)
/-- Reindex a based chart along `e : I ≃ J`. -/
noncomputable def reindex (e : I ≃ J) :
    BasedChart R u Λ B ≃ BasedChart R u (Λ.submatrix e.symm e.symm) B where
  toFun c :=
    { monomial := fun a ↦ c.monomial (a.mapDomain e.symm)
      monomial_zero := by simp [c.monomial_zero]
      monomial_mul := fun _ _ ↦ by simp [c.monomial_mul, Finsupp.mapDomain_add]
      linearIndependent :=
        c.linearIndependent.comp _ (Finsupp.mapDomain_injective e.symm.injective) }
  invFun c :=
    { monomial := fun a ↦ c.monomial (a.mapDomain e)
      monomial_zero := by simp [c.monomial_zero]
      monomial_mul := fun _ _ ↦ by
        simp [c.monomial_mul, Finsupp.mapDomain_add, ← Finsupp.mapDomain_comp]
      linearIndependent := c.linearIndependent.comp _ (Finsupp.mapDomain_injective e.injective) }
  left_inv _ := BasedChart.ext fun _ ↦ by simp [← Finsupp.mapDomain_comp]
  right_inv _ := BasedChart.ext fun _ ↦ by simp [← Finsupp.mapDomain_comp]
@[simp] theorem reindex_monomial (e : I ≃ J) (c : BasedChart R u Λ B) (a : J →₀ ℤ) :
    (reindex e c).monomial a = c.monomial (a.mapDomain e.symm) := (rfl)
@[simp] theorem reindex_coordinate (e : I ≃ J) (c : BasedChart R u Λ B) (j : J) :
    (reindex e c).coordinate j = c.coordinate (e.symm j) := by
  rw [coordinate_def, reindex_monomial, Finsupp.mapDomain_single, ← coordinate_def]
/-- Construct a based chart from an injective `R`-algebra map `basedTorus R u Λ →ₐ[R] B`. -/
noncomputable def ofAlgHom (χ : basedTorus R u Λ →ₐ[R] B) (hχ : Function.Injective χ) :
    BasedChart R u Λ B := (tautological R u Λ).map χ hχ
@[simp] theorem ofAlgHom_monomial (χ : basedTorus R u Λ →ₐ[R] B) (hχ : Function.Injective χ)
    (a : I →₀ ℤ) :
    (ofAlgHom χ hχ).monomial a = Units.map χ.toMonoidHom (BasedTorus.unitMonomial a) := (rfl)
theorem val_ofAlgHom_monomial (χ : basedTorus R u Λ →ₐ[R] B) (hχ : Function.Injective χ)
    (a : I →₀ ℤ) : ((ofAlgHom χ hχ).monomial a : B) = χ (BasedTorus.monomial a) := (rfl)
@[simp] theorem ofAlgHom_toAlgHom (χ : basedTorus R u Λ →ₐ[R] B) (hχ : Function.Injective χ) :
    (ofAlgHom χ hχ).toAlgHom = χ := by simp [ofAlgHom]
/-- Bijection between injective torus maps `basedTorus R u Λ →ₐ[R] B` and `BasedChart R u Λ B`. -/
noncomputable def algHomEquiv :
    { χ : basedTorus R u Λ →ₐ[R] B // Function.Injective χ } ≃ BasedChart R u Λ B where
  toFun χ := ofAlgHom χ.1 χ.2
  invFun c := ⟨c.toAlgHom, c.toAlgHom_injective⟩
  left_inv χ := Subtype.ext <| ofAlgHom_toAlgHom χ.1 χ.2
  right_inv _ := BasedChart.ext fun _ ↦ Units.ext (by simp)
@[simp] theorem algHomEquiv_monomial (χ : { χ : basedTorus R u Λ →ₐ[R] B // Function.Injective χ })
    (a : I →₀ ℤ) :
    (algHomEquiv χ).monomial a = Units.map χ.1.toMonoidHom (BasedTorus.unitMonomial a) := (rfl)
@[simp] theorem algHomEquiv_symm_coe (c : BasedChart R u Λ B) :
    (algHomEquiv.symm c : basedTorus R u Λ →ₐ[R] B) = c.toAlgHom := (rfl)
end Basic
section LaurentComparison
variable {R I A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
/-- Bijection between injective Laurent charts `LaurentRing R I →ₐ[R] A` and
`BasedChart R 1 0 A`. -/
noncomputable def laurentChartEquiv :
    { φ : LaurentRing R I →ₐ[R] A // Function.Injective φ } ≃
      BasedChart R 1 (0 : Matrix I I ℤ) A :=
  let e := BasedTorus.laurentRingEquivOfFormZero R 1 I
  { toFun := fun φ ↦ ofAlgHom (φ.1.comp e.toAlgHom) (by
      rw [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom]; exact φ.2.comp e.injective)
    invFun := fun c ↦ ⟨c.toAlgHom.comp e.symm.toAlgHom, by
      rw [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom]; exact c.toAlgHom_injective.comp e.symm.injective⟩
    left_inv := fun _ ↦ Subtype.ext <| AlgHom.ext fun _ ↦ by
      dsimp only; rw [ofAlgHom_toAlgHom, AlgHom.comp_apply, AlgHom.comp_apply,
        AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
    right_inv := fun _ ↦ BasedChart.ext fun _ ↦ Units.ext <| by
      dsimp only; rw [val_ofAlgHom_monomial, AlgHom.comp_apply, AlgHom.comp_apply,
        AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply,
        toAlgHom_monomial] }
@[simp] theorem val_laurentChartEquiv_monomial
    (φ : { φ : LaurentRing R I →ₐ[R] A // Function.Injective φ }) (a : I →₀ ℤ) :
    ((laurentChartEquiv φ).monomial a : A) = φ.1 (AddMonoidAlgebra.single a 1) := by
  dsimp only [laurentChartEquiv, Equiv.coe_fn_mk]
  rw [val_ofAlgHom_monomial, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    BasedTorus.laurentRingEquivOfFormZero_monomial]
@[simp] theorem val_laurentChartEquiv_coordinate
    (φ : { φ : LaurentRing R I →ₐ[R] A // Function.Injective φ }) (i : I) :
    ((laurentChartEquiv φ).coordinate i : A) = φ.1 (LaurentRing.X i) := by
  simp [coordinate_def, LaurentRing.X_def]
end LaurentComparison
end BasedChart
section OrderedProduct
variable {R I B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
/-- The ordered product `∏_{i ∈ a.support} U_i^{a_i}` taken in increasing order of `I`. -/
noncomputable def orderedCoordProd [LinearOrder I] (U : I → Bˣ) (a : I →₀ ℤ) : Bˣ :=
  ((a.support.sort (· ≤ ·)).map fun i ↦ U i ^ a i).prod
theorem orderedCoordProd_eq_sort_prod [LinearOrder I] (U : I → Bˣ) (a : I →₀ ℤ) {s : Finset I}
    (hs : a.support ⊆ s) :
    orderedCoordProd U a = ((s.sort (· ≤ ·)).map fun i ↦ U i ^ a i).prod := by
  have hfilt : (s.sort (· ≤ ·)).filter (· ∈ a.support) = a.support.sort (· ≤ ·) :=
    List.Perm.eq_of_pairwise' ((s.pairwise_sort _).filter _) (a.support.pairwise_sort _) <|
      (List.perm_ext_iff_of_nodup ((s.sort_nodup _).filter _) (a.support.sort_nodup _)).mpr
        fun i ↦ by
          simp only [List.mem_filter, Finset.mem_sort, decide_eq_true_eq, and_iff_right_iff_imp]
          exact fun hi ↦ hs hi
  have hprod (l : List I) :
      ((l.filter (· ∈ a.support)).map fun i ↦ U i ^ a i).prod =
        (l.map fun i ↦ U i ^ a i).prod := by
    induction l with
    | nil => rfl
    | cons i tl ih =>
      rw [List.filter_cons]; split_ifs with hp
      · rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ih]
      · have hai : a i = 0 := by simpa using hp
        rw [List.map_cons, List.prod_cons, hai, zpow_zero, one_mul, ih]
  rw [orderedCoordProd, ← hfilt, hprod]
theorem orderedCoordProd_eq_univ_sort [LinearOrder I] [Fintype I] (U : I → Bˣ) (a : I →₀ ℤ) :
    orderedCoordProd U a = ((Finset.univ.sort (· ≤ ·)).map fun i ↦ U i ^ a i).prod :=
  orderedCoordProd_eq_sort_prod U a (Finset.subset_univ _)
/-- The normalized ordered-product monomial `u ^ (-∑_{i < j} a_i Λ_{ij} a_j) * ∏_i U_i^{a_i}`. -/
noncomputable def orderedMonomial [LinearOrder I] (u : Rˣ) (Λ : Matrix I I ℤ) (U : I → Bˣ)
    (a : I →₀ ℤ) : Bˣ :=
  Units.map (algebraMap R B).toMonoidHom (u ^ (-Λ.strictUpper.finsuppBilinForm a a)) *
    orderedCoordProd U a
@[simp] theorem orderedMonomial_zero [LinearOrder I] (u : Rˣ) (Λ : Matrix I I ℤ) (U : I → Bˣ) :
    orderedMonomial u Λ U 0 = 1 := by simp [orderedMonomial, orderedCoordProd]
@[simp] theorem orderedMonomial_single_one [LinearOrder I] (u : Rˣ) (Λ : Matrix I I ℤ) (U : I → Bˣ)
    (i : I) : orderedMonomial u Λ U (Finsupp.single i 1) = U i := by
  rw [orderedMonomial, orderedCoordProd_eq_sort_prod U _ Finsupp.support_single_subset,
    Matrix.finsuppBilinForm_single_single]; simp
private theorem strictUpper_finsuppBilinForm_single_of_lt [LinearOrder I] (Λ : Matrix I I ℤ)
    {i : I} (x : ℤ) {a : I →₀ ℤ} (ha : ∀ j ∈ a.support, i < j) :
    Λ.strictUpper.finsuppBilinForm (Finsupp.single i x) a =
        Λ.finsuppBilinForm (Finsupp.single i x) a ∧
      Λ.strictUpper.finsuppBilinForm a (Finsupp.single i x) = 0 :=
  ⟨by rw [Matrix.finsuppBilinForm_apply, Finsupp.sum_single_index (by simp),
        Matrix.finsuppBilinForm_apply, Finsupp.sum_single_index (by simp)]
      exact Finset.sum_congr rfl fun j hj ↦ by simp [ha j hj],
   by rw [Matrix.finsuppBilinForm_apply, Finsupp.sum]
      exact Finset.sum_eq_zero fun j hj ↦ by
        rw [Finsupp.sum_single_index (by simp)]; simp [(ha j hj).not_gt]⟩
private theorem eq_zero_of_support_nil {b : I →₀ ℤ} (hb : ∀ j ∈ b.support, j ∈ ([] : List I)) :
    b = 0 := Finsupp.support_eq_empty.mp
  (Finset.eq_empty_of_forall_notMem fun j hj ↦ List.not_mem_nil (hb j hj))
private theorem erase_support_mem_of_cons {i : I} {tl : List I} {b : I →₀ ℤ}
    (hb : ∀ j ∈ b.support, j ∈ i :: tl) : ∀ j ∈ (b.erase i).support, j ∈ tl := fun j hj ↦ by
  classical
  have hj0 := Finsupp.mem_support_iff.mp hj
  have hji : j ≠ i := fun h ↦ hj0 (by simp [h])
  exact (List.mem_cons.mp
    (hb j (Finsupp.mem_support_iff.mpr (by simpa [hji] using hj0)))).resolve_left hji
private theorem map_zpow_erase_of_lt [LinearOrder I] (U : I → Bˣ) {i : I} {tl : List I}
    (hlt : ∀ j ∈ tl, i < j) (b : I →₀ ℤ) :
    (tl.map fun j ↦ U j ^ b j) = (tl.map fun j ↦ U j ^ (b.erase i) j) :=
  List.map_congr_left fun j hj ↦ by simp [(hlt j hj).ne']
private theorem map_algebraMap_mul_comm (w : Rˣ) (x y : Bˣ) :
    x * (Units.map (algebraMap R B).toMonoidHom w * y) =
      Units.map (algebraMap R B).toMonoidHom w * (x * y) := by
  rw [← mul_assoc, ← map_algebraMap_comm, mul_assoc]
theorem BasedChart.monomial_eq_orderedMonomial [LinearOrder I] (c : BasedChart R u Λ B)
    (hdiag : ∀ i, Λ i i = 0) (a : I →₀ ℤ) :
    c.monomial a = orderedMonomial u Λ c.coordinate a := by
  suffices ∀ (l : List I), l.Pairwise (· < ·) → ∀ b : I →₀ ℤ, (∀ j ∈ b.support, j ∈ l) →
      ((l.map fun i ↦ c.coordinate i ^ b i).prod : Bˣ) =
        Units.map (algebraMap R B).toMonoidHom (u ^ Λ.strictUpper.finsuppBilinForm b b) *
          c.monomial b by
    rw [orderedMonomial, orderedCoordProd,
      this _ a.support.sortedLT_sort.pairwise a fun _ hj ↦ (Finset.mem_sort _).mpr hj,
      ← mul_assoc, ← map_mul, ← zpow_add, neg_add_cancel, zpow_zero, map_one, one_mul]
  intro l hl; induction l with
  | nil => intro b hb; simp [eq_zero_of_support_nil hb, c.monomial_zero]
  | cons i tl ih =>
    rw [List.pairwise_cons] at hl; intro b hb
    set b' := b.erase i; have hb' := erase_support_mem_of_cons hb
    obtain ⟨hup₁, hup₂⟩ := strictUpper_finsuppBilinForm_single_of_lt Λ (b i)
      fun j hj ↦ hl.1 j (hb' j hj)
    have hup : Λ.strictUpper.finsuppBilinForm b b =
        Λ.finsuppBilinForm (Finsupp.single i (b i)) b' + Λ.strictUpper.finsuppBilinForm b' b' := by
      conv_lhs => rw [← Finsupp.single_add_erase i b]
      simp only [map_add, LinearMap.add_apply]
      rw [Matrix.finsuppBilinForm_single_single, hup₁, hup₂]
      simp only [Matrix.strictUpper_apply, lt_irrefl, ↓reduceIte]; ring
    rw [List.map_cons, List.prod_cons, map_zpow_erase_of_lt c.coordinate hl.1 b,
      ← c.monomial_single_of_diag_zero (hdiag i), ih hl.2 b' hb', map_algebraMap_mul_comm,
      c.monomial_mul, Finsupp.single_add_erase i b, ← mul_assoc, ← map_mul, ← zpow_add, add_comm,
      hup]
section QuasiComm
variable {u : Rˣ} {Λ : Matrix I I ℤ} (hΛ : Λ.finsuppBilinForm.IsAlt) {U : I → Bˣ}
  (hU : ∀ i j, U i * U j = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ i j)) * (U j * U i))
include hU in
private theorem zpow_mul_zpow_of_quasiComm (i j : I) (m n : ℤ) :
    U i ^ m * U j ^ n =
      Units.map (algebraMap R B).toMonoidHom (u ^ (2 * (m * Λ i j * n))) * (U j ^ n * U i ^ m) := by
  have hji : U j * U i =
      Units.map (algebraMap R B).toMonoidHom (u ^ (-(2 * Λ i j))) * (U i * U j) := by
    apply mul_left_cancel (a := Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ i j)))
    rw [← hU i j, ← mul_assoc, ← map_mul, ← zpow_add, add_neg_cancel, zpow_zero, map_one, one_mul]
  have h1 : U i * U j ^ n =
      Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ i j * n)) * (U j ^ n * U i) := by
    apply mul_left_cancel (a := Units.map (algebraMap R B).toMonoidHom ((u ^ (-(2 * Λ i j))) ^ n))
    rw [← units_zpow_mul_of_quasiComm hji n, ← mul_assoc, ← map_mul, ← zpow_mul, ← zpow_add,
      (by ring : -(2 * Λ i j) * n + 2 * Λ i j * n = 0), zpow_zero, map_one, one_mul]
  rw [units_zpow_mul_of_quasiComm h1 m, ← zpow_mul]; congr 3; ring
include hΛ hU in
private theorem prod_zpow_mul_zpow_of_lt [LinearOrder I] (tl : List I) {i : I}
    (htl : tl.Pairwise (· < ·)) (hi : ∀ j ∈ tl, i < j) (a : I →₀ ℤ) (ha : ∀ j ∈ a.support, j ∈ tl)
    (n : ℤ) :
    ((tl.map fun j ↦ U j ^ a j).prod) * U i ^ n =
      Units.map (algebraMap R B).toMonoidHom
        (u ^ (-2 * Λ.strictUpper.finsuppBilinForm (Finsupp.single i n) a)) *
        (U i ^ n * (tl.map fun j ↦ U j ^ a j).prod) := by
  induction tl generalizing a with
  | nil => simp [eq_zero_of_support_nil ha]
  | cons j rest ih =>
    rw [List.pairwise_cons] at htl
    set a' := a.erase j; have ha' := erase_support_mem_of_cons ha
    have hup : Λ.strictUpper.finsuppBilinForm (Finsupp.single i n) a =
        n * Λ i j * a j + Λ.strictUpper.finsuppBilinForm (Finsupp.single i n) a' := by
      conv_lhs => rw [← Finsupp.single_add_erase j a]
      rw [map_add, Matrix.finsuppBilinForm_single_single, Matrix.strictUpper_apply]
      simp only [hi j List.mem_cons_self, ↓reduceIte]; ring
    rw [List.map_cons, List.prod_cons, map_zpow_erase_of_lt U htl.1 a, mul_assoc,
      ih htl.2 (fun k hk ↦ hi k (List.mem_cons_of_mem j hk)) a' ha',
      map_algebraMap_mul_comm, ← mul_assoc (U j ^ a j), zpow_mul_zpow_of_quasiComm hU j i (a j) n,
      mul_assoc (Units.map _ _) (U i ^ n * U j ^ a j), ← mul_assoc, ← map_mul, ← zpow_add, hup]
    simp only [mul_assoc]; congr 3
    rw [← Matrix.neg_apply_eq_of_isAlt_finsuppBilinForm hΛ i j]; ring
include hΛ hU in
private theorem prod_zpow_mul_prod_zpow [LinearOrder I] (l : List I) (hl : l.Pairwise (· < ·))
    (p q : I →₀ ℤ) (hp : ∀ j ∈ p.support, j ∈ l) (hq : ∀ j ∈ q.support, j ∈ l) :
    ((l.map fun i ↦ U i ^ p i).prod) * ((l.map fun i ↦ U i ^ q i).prod) =
      Units.map (algebraMap R B).toMonoidHom (u ^ (-2 * Λ.strictUpper.finsuppBilinForm q p)) *
        ((l.map fun i ↦ U i ^ (p + q) i).prod) := by
  induction l generalizing p q with
  | nil => simp [eq_zero_of_support_nil hp, eq_zero_of_support_nil hq]
  | cons i tl ih =>
    rw [List.pairwise_cons] at hl
    set p' := p.erase i; set q' := q.erase i
    have hp' := erase_support_mem_of_cons hp; have hq' := erase_support_mem_of_cons hq
    have hup : Λ.strictUpper.finsuppBilinForm q p =
        Λ.strictUpper.finsuppBilinForm (Finsupp.single i (q i)) p' +
          Λ.strictUpper.finsuppBilinForm q' p' := by
      conv_lhs => rw [← Finsupp.single_add_erase i p, ← Finsupp.single_add_erase i q]
      simp only [map_add, LinearMap.add_apply]
      rw [Matrix.finsuppBilinForm_single_single,
        (strictUpper_finsuppBilinForm_single_of_lt Λ (p i) fun j hj ↦ hl.1 j (hq' j hj)).2]
      simp only [Matrix.strictUpper_apply, lt_irrefl, ↓reduceIte]; ring
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
      map_zpow_erase_of_lt U hl.1 p, map_zpow_erase_of_lt U hl.1 q,
      map_zpow_erase_of_lt U hl.1 (p + q), Finsupp.erase_add, mul_assoc (U i ^ p i),
      ← mul_assoc _ (U i ^ q i), prod_zpow_mul_zpow_of_lt hΛ hU tl hl.2 hl.1 p' hp' (q i),
      mul_assoc _ (U i ^ q i * _), map_algebraMap_mul_comm, ← mul_assoc (U i ^ p i),
      ← mul_assoc (U i ^ p i) (U i ^ q i), ← zpow_add, ← Finsupp.add_apply,
      mul_assoc (U i ^ (p + q) i), ih hl.2 p' q' hp' hq',
      map_algebraMap_mul_comm, ← mul_assoc, ← map_mul, ← zpow_add, hup]
    congr 3; ring
include hΛ hU in
theorem orderedMonomial_mul [LinearOrder I] (a b : I →₀ ℤ) :
    orderedMonomial u Λ U a * orderedMonomial u Λ U b =
      Units.map (algebraMap R B).toMonoidHom (u ^ Λ.finsuppBilinForm a b) *
        orderedMonomial u Λ U (a + b) := by
  let s := a.support ∪ b.support
  have hprod := prod_zpow_mul_prod_zpow hΛ hU (s.sort (· ≤ ·)) s.sortedLT_sort.pairwise a b
    (fun _ hj ↦ (Finset.mem_sort _).mpr (Finset.subset_union_left hj))
    (fun _ hj ↦ (Finset.mem_sort _).mpr (Finset.subset_union_right hj))
  rw [orderedMonomial, orderedMonomial, orderedMonomial,
    orderedCoordProd_eq_sort_prod U a Finset.subset_union_left,
    orderedCoordProd_eq_sort_prod U b Finset.subset_union_right,
    orderedCoordProd_eq_sort_prod U (a + b) Finsupp.support_add,
    mul_assoc, ← mul_assoc _ _ ((s.sort _).map _).prod,
    ← map_algebraMap_comm _ ((s.sort _).map _).prod, mul_assoc _ ((s.sort _).map _).prod,
    hprod, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, ← zpow_add, ← zpow_add,
    ← mul_assoc, ← map_mul, ← zpow_add, Matrix.finsuppBilinForm_eq_strictUpper_sub_flip hΛ a b]
  simp only [map_add, LinearMap.add_apply]; congr 3; ring
end QuasiComm
theorem orderedMonomial_eq_of_linearOrder (l₁ l₂ : LinearOrder I) {u : Rˣ} {Λ : Matrix I I ℤ}
    (hΛ : Λ.finsuppBilinForm.IsAlt) {U : I → Bˣ}
    (hU : ∀ i j, U i * U j = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ i j)) * (U j * U i))
    (a : I →₀ ℤ) :
    @orderedMonomial R I B _ _ _ l₁ u Λ U a = @orderedMonomial R I B _ _ _ l₂ u Λ U a :=
  congr_fun (normalizedMonomial_eq_of_single_one_eq
    (@orderedMonomial_zero R I B _ _ _ l₁ u Λ U) (@orderedMonomial_zero R I B _ _ _ l₂ u Λ U)
    (@orderedMonomial_mul R I B _ _ _ u Λ hΛ U hU l₁)
    (@orderedMonomial_mul R I B _ _ _ u Λ hΛ U hU l₂) fun i ↦ by
      rw [@orderedMonomial_single_one R I B _ _ _ l₁,
        @orderedMonomial_single_one R I B _ _ _ l₂]) a
private theorem unitsMap_unitMonomial_mul {u : Rˣ} {Λ : Matrix I I ℤ}
    (φ : basedTorus R u Λ →ₐ[R] B) (b c : I →₀ ℤ) :
    Units.map φ.toMonoidHom (BasedTorus.unitMonomial b) *
        Units.map φ.toMonoidHom (BasedTorus.unitMonomial c) =
      Units.map (algebraMap R B).toMonoidHom (u ^ Λ.finsuppBilinForm b c) *
        Units.map φ.toMonoidHom (BasedTorus.unitMonomial (b + c)) := by
  have hm : BasedTorus.unitMonomial (R := R) (u := u) (Λ := Λ) b * BasedTorus.unitMonomial c = _ :=
    (BasedChart.tautological R u Λ).monomial_mul b c
  rw [← map_mul, hm, map_mul]
  exact congrArg (· * _) (Units.ext <| by
    rw [Units.coe_map, Units.coe_map, Units.coe_map]; exact φ.commutes _)
theorem BasedTorus.algHom_ext_X {u : Rˣ} {Λ : Matrix I I ℤ}
    {φ₁ φ₂ : basedTorus R u Λ →ₐ[R] B} (h : ∀ i, φ₁ (BasedTorus.X i) = φ₂ (BasedTorus.X i)) :
    φ₁ = φ₂ :=
  BasedTorus.algHom_ext fun a ↦ congrArg Units.val <| congr_fun
    (normalizedMonomial_eq_of_single_one_eq
      (M₁ := fun b ↦ Units.map φ₁.toMonoidHom (BasedTorus.unitMonomial b))
      (M₂ := fun b ↦ Units.map φ₂.toMonoidHom (BasedTorus.unitMonomial b))
      (Units.ext <| by simp) (Units.ext <| by simp)
      (unitsMap_unitMonomial_mul φ₁) (unitsMap_unitMonomial_mul φ₂)
      fun i ↦ Units.ext <| by simpa [BasedTorus.X_def] using h i) a
section LiftCoordinates
variable {u : Rˣ} {Λ : Matrix I I ℤ} (hΛ : Λ.finsuppBilinForm.IsAlt) (U : I → Bˣ)
  (hU : ∀ i j, U i * U j = Units.map (algebraMap R B).toMonoidHom (u ^ (2 * Λ i j)) * (U j * U i))
/-- Universal `R`-algebra map `basedTorus R u Λ →ₐ[R] B` sending each `X_i` to `U_i`. -/
noncomputable def BasedTorus.liftCoordinates : basedTorus R u Λ →ₐ[R] B :=
  TwistedMonoidAlgebra.lift
    (fun g ↦ (@orderedMonomial R I B _ _ _ (exists_wellFoundedLT I).choose u Λ U g.toAdd : B))
    (by simp [@orderedMonomial_zero R I B _ _ _ (exists_wellFoundedLT I).choose])
    fun g h ↦ by
      rw [← Units.val_mul,
        @orderedMonomial_mul R I B _ _ _ u Λ hΛ U hU (exists_wellFoundedLT I).choose,
        Units.val_mul, Units.coe_map]
      simp [Algebra.smul_def, toAdd_mul, formFactorSet]
@[simp] theorem BasedTorus.liftCoordinates_X (i : I) :
    BasedTorus.liftCoordinates hΛ U hU (BasedTorus.X i) = U i := by
  rw [BasedTorus.liftCoordinates, BasedTorus.X_def, BasedTorus.monomial_def,
    TwistedMonoidAlgebra.lift_of, toAdd_ofAdd,
    @orderedMonomial_single_one R I B _ _ _ (exists_wellFoundedLT I).choose]
theorem BasedTorus.liftCoordinates_monomial [LinearOrder I] (a : I →₀ ℤ) :
    BasedTorus.liftCoordinates hΛ U hU (BasedTorus.monomial a) = orderedMonomial u Λ U a :=
  congrArg Units.val <| congr_fun (normalizedMonomial_eq_of_single_one_eq
    (M₁ := fun b ↦ Units.map (BasedTorus.liftCoordinates hΛ U hU).toMonoidHom
      (BasedTorus.unitMonomial b))
    (M₂ := orderedMonomial u Λ U) (Units.ext <| by simp) (orderedMonomial_zero u Λ U)
    (unitsMap_unitMonomial_mul _) (orderedMonomial_mul hΛ hU)
    fun i ↦ Units.ext <| by simpa [BasedTorus.X_def] using BasedTorus.liftCoordinates_X hΛ U hU i) a
theorem BasedTorus.liftCoordinates_unique {φ : basedTorus R u Λ →ₐ[R] B}
    (hφ : ∀ i, φ (BasedTorus.X i) = U i) : φ = BasedTorus.liftCoordinates hΛ U hU :=
  BasedTorus.algHom_ext_X fun i ↦ (hφ i).trans (BasedTorus.liftCoordinates_X hΛ U hU i).symm
/-- Construct a based chart from quasi-commuting coordinates with linearly independent ordered
products. -/
noncomputable def BasedChart.ofCoordinates [LinearOrder I]
    (hli : LinearIndependent R fun a ↦ (orderedMonomial u Λ U a : B)) : BasedChart R u Λ B where
  monomial := orderedMonomial u Λ U
  monomial_zero := orderedMonomial_zero u Λ U
  monomial_mul := orderedMonomial_mul hΛ hU
  linearIndependent := hli
@[simp] theorem BasedChart.ofCoordinates_coordinate [LinearOrder I]
    (hli : LinearIndependent R fun a ↦ (orderedMonomial u Λ U a : B)) (i : I) :
    (BasedChart.ofCoordinates hΛ U hU hli).coordinate i = U i :=
  orderedMonomial_single_one u Λ U i
end LiftCoordinates
theorem BasedChart.monomial_rankTwo_neg_one_two {u : Rˣ}
    (c : BasedChart R u (!![(0 : ℤ), 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℤ) B) :
    c.monomial (-Finsupp.single 0 1 + 2 • Finsupp.single 1 1) =
      Units.map (algebraMap R B).toMonoidHom (u ^ 2) *
        ((c.coordinate 0)⁻¹ * c.coordinate 1 ^ 2) := by
  set a : Fin 2 →₀ ℤ := -Finsupp.single 0 1 + 2 • Finsupp.single 1 1
  have hsort : (Finset.univ : Finset (Fin 2)).sort (· ≤ ·) = [0, 1] := by
    have huniv : ([0, 1] : List (Fin 2)).toFinset = Finset.univ := by decide
    rw [← huniv]; exact (List.toFinset_sort (r := (· ≤ ·)) (by decide)).mpr (by decide)
  rw [c.monomial_eq_orderedMonomial (fun i ↦ by fin_cases i <;> rfl) a, orderedMonomial,
    orderedCoordProd_eq_univ_sort, hsort, Matrix.finsuppBilinForm_apply_eq_dotProduct]
  have ha : a 0 = -1 ∧ a 1 = 2 := by simp [a]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, ha.1, ha.2]
end OrderedProduct
end TauCeti
