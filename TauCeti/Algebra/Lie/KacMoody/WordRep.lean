/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.MonoidAlgebra.Module
public import TauCeti.Algebra.Lie.KacMoody.Basic

import TauCeti.Algebra.Lie.OfAssociative

/-!
# Kac's word representation on the tensor algebra

For a realization `R` of a matrix `A` over a field `K` and a linear functional
`μ : Module.Dual K H`, this file constructs Kac's representation of the auxiliary Lie algebra
(Chevalley relations without Serre relations) on the tensor algebra `K[FreeMonoid I]` of the space
with basis indexed by `I`.

On a word `w = j₁ ⋯ jₛ`:

* `lowering i` (`fᵢ`) acts by left multiplication by the letter `i`;
* `cartanAction R μ x` (`h ∈ H`) acts by the scalar `(μ - α(w))(x)`, where `α(w)` is the sum
  `rootSum R w` of the simple roots along `w`;
* `raising R μ k` (`eₖ`) acts by `eₖ 1 = 0` and
  `eₖ (j w) = j (eₖ w) + δⱼₖ (μ - α(w))(hₖ) w`.

These operators satisfy the five Chevalley relations
(`TauCeti.KacMoody.satisfiesAuxRelations_wordRep`), providing the shared representation used in
the triangular directness proof (`TauCeti.Algebra.Lie.KacMoody.Auxiliary`, and hence
`TauCeti.Algebra.Lie.KacMoody.Triangular`).

## Main definitions

* `TauCeti.KacMoody.rootSum`: the sum of the simple roots along a word in `FreeMonoid I`.
* `TauCeti.KacMoody.weightDerivation`: the derivation of `K[FreeMonoid I]` scaling each word `w`
  by `rootSum R w x`.
* `TauCeti.KacMoody.cartanAction`, `TauCeti.KacMoody.lowering`, and `TauCeti.KacMoody.raising`:
  the Cartan, lowering, and raising operators on `K[FreeMonoid I]`.

## Main results

* `TauCeti.KacMoody.satisfiesAuxRelations_wordRep`: `cartanAction R μ`, `raising R μ`, and
  `lowering` satisfy `TauCeti.KacMoody.SatisfiesAuxRelations R`.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  Theorem 1.2.
-/

public section

open LieAlgebra
open scoped MonoidAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

namespace KacMoody

section WordRep

open MonoidAlgebra

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (μ : Module.Dual K H)

/-- The sum of the simple roots along a word. -/
def rootSum (w : FreeMonoid I) : Module.Dual K H :=
  (FreeMonoid.lift (Multiplicative.ofAdd ∘ R.root) w).toAdd

/-- The root sum of the empty word is zero. -/
@[simp]
theorem rootSum_one : rootSum R (1 : FreeMonoid I) = 0 := by
  rw [rootSum, map_one, toAdd_one]

/-- Prepending a letter adds its simple root to the root sum. -/
theorem rootSum_of_mul (i : I) (w : FreeMonoid I) :
    rootSum R (.of i * w) = R.root i + rootSum R w := by
  rw [rootSum, map_mul, toAdd_mul, FreeMonoid.lift_eval_of]
  rfl

/-- The root sum of a single-letter word is its simple root. -/
theorem rootSum_of (i : I) : rootSum R (.of i) = R.root i := by
  rw [rootSum, FreeMonoid.lift_eval_of]
  rfl

/-- The root sum is additive under word concatenation. -/
theorem rootSum_mul (w w' : FreeMonoid I) :
    rootSum R (w * w') = rootSum R w + rootSum R w' := by
  rw [rootSum, map_mul, toAdd_mul]
  rfl

/-- The derivation of the tensor algebra multiplying each word by the value at `x` of the sum of
the simple roots along it, as a linear function of `x ∈ H`. -/
noncomputable def weightDerivation : H →ₗ[K] Module.End K K[FreeMonoid I] :=
  ((MonoidAlgebra.basis (FreeMonoid I) K).constr K).toLinearMap ∘ₗ
    LinearMap.pi fun w => (rootSum R w).smulRight (single w (1 : K))

/-- Action of `TauCeti.KacMoody.weightDerivation` on a monomial. -/
theorem weightDerivation_single (x : H) (w : FreeMonoid I) (c : K) :
    weightDerivation R x (single w c) = rootSum R w x • single w c := by
  have hc : single w c = c • MonoidAlgebra.basis (FreeMonoid I) K w := by
    simp [basis_apply]
  rw [hc, map_smul, weightDerivation]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.constr_basis,
    LinearMap.pi_apply, LinearMap.smulRight_apply]
  simp [mul_comm]

/-- The weight derivation is a derivation of the tensor algebra. -/
theorem weightDerivation_mul (x : H) (y z : K[FreeMonoid I]) :
    weightDerivation R x (y * z) = weightDerivation R x y * z + y * weightDerivation R x z := by
  let b := MonoidAlgebra.basis (FreeMonoid I) K
  have key : (LinearMap.mul K K[FreeMonoid I]).compr₂ (weightDerivation R x) =
      (LinearMap.mul K K[FreeMonoid I]).compl₁₂ (weightDerivation R x) LinearMap.id +
        (LinearMap.mul K K[FreeMonoid I]).compl₁₂ LinearMap.id (weightDerivation R x) :=
    b.ext fun w => b.ext fun w' => by
      simp [b, weightDerivation_single, single_mul_single, rootSum_mul, add_smul]
  exact LinearMap.congr_fun₂ key y z

/-- The Cartan operators: `x ∈ H` acts on a word `w` by `(μ - α(w))(x)`, where `α(w)` is the sum
of the simple roots along `w`. -/
noncomputable def cartanAction : H →ₗ[K] Module.End K K[FreeMonoid I] :=
  μ.smulRight 1 - weightDerivation R

/-- Action of `TauCeti.KacMoody.cartanAction` on any element of the tensor algebra. -/
theorem cartanAction_apply (x : H) (y : K[FreeMonoid I]) :
    cartanAction R μ x y = μ x • y - weightDerivation R x y := by
  simp [cartanAction]

/-- Action of `TauCeti.KacMoody.cartanAction` on a monomial. -/
theorem cartanAction_single (x : H) (w : FreeMonoid I) (c : K) :
    cartanAction R μ x (single w c) = (μ x - rootSum R w x) • single w c := by
  simp [cartanAction, weightDerivation_single, sub_smul]

/-- The lowering operator: left multiplication by a letter. -/
noncomputable def lowering (i : I) : Module.End K K[FreeMonoid I] :=
  Algebra.lmul K K[FreeMonoid I] (single (FreeMonoid.of i) 1)

/-- `TauCeti.KacMoody.lowering` equals left multiplication by the single-letter basis element. -/
theorem lowering_eq_lmul (i : I) :
    lowering (K := K) i =
      Algebra.lmul K K[FreeMonoid I] (MonoidAlgebra.of K (FreeMonoid I) (.of i)) := by
  rw [lowering, MonoidAlgebra.of_apply]

/-- `TauCeti.KacMoody.lowering` acts by left multiplication by the single-letter monomial. -/
theorem lowering_apply (i : I) (y : K[FreeMonoid I]) :
    lowering i y = single (FreeMonoid.of i) 1 * y := by
  rw [lowering, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']

/-- Action of `TauCeti.KacMoody.lowering` on a monomial. -/
theorem lowering_single (i : I) (w : FreeMonoid I) (c : K) :
    lowering i (single w c) = single (FreeMonoid.of i * w) c := by
  rw [lowering_apply, single_mul_single, one_mul]

/-- `D_x fⱼ = fⱼ D_x + αⱼ(x) fⱼ` for the weight derivation `D_x`. -/
theorem weightDerivation_lowering (x : H) (j : I) (y : K[FreeMonoid I]) :
    weightDerivation R x (lowering j y) =
      lowering j (weightDerivation R x y) + R.root j x • lowering j y := by
  rw [lowering_apply, lowering_apply, weightDerivation_mul, weightDerivation_single, rootSum_of,
    add_comm, smul_mul_assoc]

/-- The Cartan operators on the tensor algebra commute. -/
theorem lie_cartanAction_cartanAction (x y : H) :
    ⁅cartanAction R μ x, cartanAction R μ y⁆ = 0 := by
  refine (MonoidAlgebra.basis (FreeMonoid I) K).ext fun w => ?_
  simp only [basis_apply, Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp,
    cartanAction_single, map_smul, smul_smul, mul_comm, sub_self, LinearMap.zero_apply]

/-- The raising-style commutator between `cartanAction` and `lowering`:
`⁅h(x), fⱼ⁆ = -αⱼ(x) fⱼ`. -/
theorem lie_cartanAction_lowering (x : H) (j : I) :
    ⁅cartanAction R μ x, lowering j⁆ = -(R.root j x • lowering (K := K) j) := by
  refine (MonoidAlgebra.basis (FreeMonoid I) K).ext fun w => ?_
  simp only [basis_apply, Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp,
    LinearMap.neg_apply, LinearMap.smul_apply, lowering_single, cartanAction_single,
    map_smul, rootSum_of_mul, LinearMap.add_apply]
  module

variable [DecidableEq I]

/-- The raising operator `eₖ` on words: `eₖ 1 = 0` and
`eₖ (j w) = j (eₖ w) + δⱼₖ (μ - α(w))(hₖ) w`. -/
noncomputable def raisingWord (k : I) (w : FreeMonoid I) : K[FreeMonoid I] :=
  w.mulRecOn 0 fun j w r => single (FreeMonoid.of j) 1 * r +
    if j = k then (μ (R.coroot k) - rootSum R w (R.coroot k)) • single w 1 else 0

/-- The raising operator `eₖ`, extended linearly from words. -/
noncomputable def raising (k : I) : Module.End K K[FreeMonoid I] :=
  (MonoidAlgebra.basis (FreeMonoid I) K).constr K (raisingWord R μ k)

/-- Evaluation of `TauCeti.KacMoody.raising` on a basis word `single w 1`. -/
theorem raising_single_one (k : I) (w : FreeMonoid I) :
    raising R μ k (single w 1) = raisingWord R μ k w := by
  rw [raising, ← basis_apply, Module.Basis.constr_basis]

/-- `raisingWord` kills the empty word `1`. -/
@[simp]
theorem raisingWord_one (k : I) : raisingWord R μ k 1 = 0 := by
  simp [raisingWord]

/-- Recursive formula for `TauCeti.KacMoody.raisingWord` on a nonempty word. -/
theorem raisingWord_of_mul (k j : I) (w : FreeMonoid I) :
    raisingWord R μ k (.of j * w) = single (FreeMonoid.of j) 1 * raisingWord R μ k w +
      if j = k then (μ (R.coroot k) - rootSum R w (R.coroot k)) • single w 1 else 0 := by
  simp [raisingWord]

/-- `eₖ fⱼ = fⱼ eₖ + δⱼₖ hₖ` on the tensor algebra. -/
theorem raising_lowering (k j : I) (y : K[FreeMonoid I]) :
    raising R μ k (lowering j y) = lowering j (raising R μ k y) +
      if j = k then cartanAction R μ (R.coroot k) y else 0 := by
  let b := MonoidAlgebra.basis (FreeMonoid I) K
  have key : raising R μ k ∘ₗ lowering j = lowering j ∘ₗ raising R μ k +
      if j = k then cartanAction R μ (R.coroot k) else 0 :=
    b.ext fun w => by
      rw [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply, basis_apply,
        lowering_single, raising_single_one, raising_single_one, raisingWord_of_mul,
        lowering_apply]
      split_ifs <;> simp [cartanAction_single, sub_smul]
  have := LinearMap.congr_fun key y
  split_ifs at this ⊢ <;> simpa using this

/-- The raising operator lowers the weight by a simple root. -/
theorem weightDerivation_raisingWord (x : H) (k : I) (w : FreeMonoid I) :
    weightDerivation R x (raisingWord R μ k w) =
      (rootSum R w x - R.root k x) • raisingWord R μ k w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul j w ih =>
    rw [raisingWord_of_mul, map_add, ← lowering_apply, weightDerivation_lowering, ih,
      rootSum_of_mul]
    split_ifs with hjk
    · subst hjk
      simp only [map_smul, weightDerivation_single, LinearMap.add_apply, smul_add, smul_smul,
        lowering_apply]
      module
    · simp only [map_zero, add_zero, map_smul, lowering_apply, LinearMap.add_apply]
      module

/-- Bracket of a Cartan operator with a raising operator: `⁅h(x), eₖ⁆ = αₖ(x) eₖ`. -/
theorem lie_cartanAction_raising (x : H) (k : I) :
    ⁅cartanAction R μ x, raising R μ k⁆ = R.root k x • raising R μ k := by
  refine (MonoidAlgebra.basis (FreeMonoid I) K).ext fun w => ?_
  simp only [basis_apply, Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp,
    LinearMap.smul_apply, cartanAction_single, map_smul, raising_single_one]
  simp only [cartanAction_apply, weightDerivation_raisingWord]
  module

/-- Bracket of matching raising and lowering operators: `⁅eₖ, fₖ⁆ = h(hₖ)`. -/
theorem lie_raising_lowering_self (k : I) :
    ⁅raising R μ k, lowering k⁆ = cartanAction R μ (R.coroot k) := by
  refine LinearMap.ext fun y => ?_
  simp [Ring.lie_def, raising_lowering]

/-- Distinct raising and lowering operators commute: `⁅eₖ, fⱼ⁆ = 0` for `k ≠ j`. -/
theorem lie_raising_lowering_of_ne {k j : I} (h : k ≠ j) :
    ⁅raising R μ k, lowering (K := K) j⁆ = 0 := by
  refine LinearMap.ext fun y => ?_
  simp [Ring.lie_def, raising_lowering, Ne.symm h]

/-- The Cartan, raising, and lowering operators on `K[FreeMonoid I]` satisfy the auxiliary
Kac–Moody relations `TauCeti.KacMoody.SatisfiesAuxRelations`. -/
theorem satisfiesAuxRelations_wordRep :
    SatisfiesAuxRelations R (cartanAction R μ) (raising R μ) (lowering (K := K)) where
  lie_cartan_cartan := lie_cartanAction_cartanAction R μ
  lie_cartan_positive := lie_cartanAction_raising R μ
  lie_cartan_negative := lie_cartanAction_lowering R μ
  lie_positive_negative_self := lie_raising_lowering_self R μ
  lie_positive_negative_of_ne _ _ := lie_raising_lowering_of_ne R μ

end WordRep

end KacMoody

end TauCeti
