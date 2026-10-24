/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Mathlib.Topology.Algebra.Algebra
public import TauCeti.RingTheory.FormalGroup.AddInv
public import TauCeti.RingTheory.MvPowerSeries.Evaluation
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Points of a formal group law in topologically nilpotent elements

Let `F(X, Y)` be a one-dimensional formal group law over a commutative ring `R`, and let `A` be a
complete Hausdorff linearly topologised `R`-algebra. The power series `F` converges at every pair
of topologically nilpotent elements of `A`, and its value is again topologically nilpotent. So the
topologically nilpotent elements of `A` form a group under `x +_F y = F(x, y)`, with negation the
value `i(x)` of the formal inverse. This is the group `F(A)` of `A`-valued points of `F`; for a
complete local ring `A` with its `𝔪`-adic topology it is the maximal ideal `𝔪` with the law `F`.

The carrier `F.TopNilpotentPoint A` mirrors Mathlib's power-series carrier `F.Point σ` of series
with nilpotent constant coefficient: a point is an element of `A` satisfying
`PowerSeries.HasEval`, the condition under which evaluation converges. Mathlib's carrier is the
special case `A = R⟦σ⟧` with the product topology over discrete `R`
(`FormalGroup.pointEquivTopNilpotentPoint`). Evaluation uses the discrete topology on `R`, so no
topology on the coefficient ring is assumed. Characterising lemmas are stated as convergent sums,
which mention no topology on `R` either.

## Main definitions

* `FormalGroup.TopNilpotentPoint F A`: the topologically nilpotent elements of `A`, carrying an
  `AddGroup` structure, and an `AddCommGroup` structure when `F` is commutative.
* `FormalGroup.TopNilpotentPoint.map`: a continuous `R`-algebra map `A → B` induces an additive
  map `F(A) → F(B)`.
* `FormalGroup.pointEquivTopNilpotentPoint`: the group `F.Point σ` of power-series points is the
  group of points of `F` in `R⟦σ⟧`.

## Main results

* `FormalGroup.TopNilpotentPoint.hasSum_val_add`: `x +_F y` is the sum of the convergent series
  `∑ aᵢⱼ xⁱ yʲ`.
* `FormalGroup.TopNilpotentPoint.hasSum_val_neg`: `-x` is the sum of the convergent series
  `∑ cₙ xⁿ`, where `i(X) = ∑ cₙ Xⁿ` is the formal inverse.
* `FormalGroup.TopNilpotentPoint.map_id`, `FormalGroup.TopNilpotentPoint.map_comp`: functoriality.

## Implementation notes

The group laws are not proved by manipulating the convergent sums. Evaluation at a family of
topologically nilpotent elements turns substitution into evaluation (`MvPowerSeries.eval₂_subst`),
so each law in `F(A)` is the evaluation of the corresponding identity of power series:
associativity of `F`, the unit laws `F(X, 0) = X = F(0, X)` and `F(i(X), X) = 0`.

`WeierstrassCurve.FormalGroupPoint` is the same construction for the formal group law of a
Weierstrass curve, which is not a `FormalGroup`, on an adic ideal.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.3.
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R)

/-- The **points of a formal group law `F` in `A`**: the elements of a topological ring `A`
satisfying `PowerSeries.HasEval`, that is, the topologically nilpotent elements. Evaluation of
power series over `R` at these elements converges only when `A` is a complete, Hausdorff, linearly
topologised `R`-algebra; under those assumptions they form a group under `x +_F y = F(x, y)`.
This is the analogue for `A` of the power-series carrier `F.Point σ`.

This is a structure rather than a subtype of `A` so that its group law, which depends on `F`, is
not confused with the ring operations of `A`. -/
@[ext]
structure TopNilpotentPoint (F : FormalGroup R) (A : Type*) [CommRing A] [TopologicalSpace A] where
  /-- The coordinate of a point. -/
  val : A
  /-- The coordinate of a point is topologically nilpotent. -/
  hasEval : PowerSeries.HasEval val

namespace TopNilpotentPoint

section Basic

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- The zero point. -/
instance : Zero (F.TopNilpotentPoint A) where
  zero := ⟨0, .zero⟩

@[simp]
theorem val_zero : (0 : F.TopNilpotentPoint A).val = 0 := (rfl)

end Basic

variable {A : Type*} [CommRing A] [Algebra R A] [UniformSpace A] [IsUniformAddGroup A]
  [CompleteSpace A] [T2Space A] [IsTopologicalRing A] [IsLinearTopology A A]

/-- The sum `x +_F y = F(x, y)` of two points. -/
noncomputable instance : Add (F.TopNilpotentPoint A) where
  add x y := ⟨letI : UniformSpace R := ⊥
      eval₂ (algebraMap R A) ![x.val, y.val] F.toPowerSeries,
    letI : UniformSpace R := ⊥
    (isTopologicallyNilpotent_eval₂_iff continuous_of_discreteTopology
      (hasEval_finTwo x.hasEval y.hasEval) _).2 (by simpa [F.zero_constantCoeff] using .zero)⟩

/-- The negation `-x = i(x)` of a point, the value of the formal inverse. -/
noncomputable instance : Neg (F.TopNilpotentPoint A) where
  neg x := ⟨letI : UniformSpace R := ⊥
      PowerSeries.eval₂ (algebraMap R A) x.val F.addInvX,
    letI : UniformSpace R := ⊥
    (isTopologicallyNilpotent_eval₂_iff continuous_of_discreteTopology
      (PowerSeries.hasEval x.hasEval) _).2
      (F.hasSubst_addInvX.map (algebraMap R A)).isTopologicallyNilpotent⟩

/-- The sum of two points as an evaluation, for any discrete uniform structure on `R`. -/
theorem val_add_eq_eval₂ [UniformSpace R] [DiscreteUniformity R] (x y : F.TopNilpotentPoint A) :
    (x + y).val = eval₂ (algebraMap R A) ![x.val, y.val] F.toPowerSeries := by
  rw [DiscreteUniformity.eq_bot (X := R)]
  rfl

/-- The negation of a point as an evaluation, for any discrete uniform structure on `R`. -/
theorem val_neg_eq_eval₂ [UniformSpace R] [DiscreteUniformity R] (x : F.TopNilpotentPoint A) :
    (-x).val = PowerSeries.eval₂ (algebraMap R A) x.val F.addInvX := by
  rw [DiscreteUniformity.eq_bot (X := R)]
  rfl

/-- **The sum of two points is a convergent series**: `x +_F y = ∑ aᵢⱼ xⁱ yʲ`, where
`F(X, Y) = ∑ aᵢⱼ Xⁱ Yʲ`. -/
theorem hasSum_val_add (x y : F.TopNilpotentPoint A) :
    HasSum (fun d : Fin 2 →₀ ℕ ↦ coeff d F.toPowerSeries • (x.val ^ d 0 * y.val ^ d 1))
      (x + y).val := by
  let _ : UniformSpace R := ⊥
  rw [val_add_eq_eval₂]
  convert hasSum_eval₂ continuous_of_discreteTopology (hasEval_finTwo x.hasEval y.hasEval)
    F.toPowerSeries using 2 with d
  simp [Algebra.smul_def, Finsupp.prod_fintype, Fin.prod_univ_two]

/-- **The negation of a point is a convergent series**: `-x = ∑ cₙ xⁿ`, where `i(X) = ∑ cₙ Xⁿ` is
the formal inverse of `F`. -/
theorem hasSum_val_neg (x : F.TopNilpotentPoint A) :
    HasSum (fun n ↦ PowerSeries.coeff n F.addInvX • x.val ^ n) (-x).val := by
  let _ : UniformSpace R := ⊥
  rw [val_neg_eq_eval₂]
  simpa only [Algebra.smul_def] using
    PowerSeries.hasSum_eval₂ continuous_of_discreteTopology x.hasEval F.addInvX

/-- The sum of two points is `∑ aᵢⱼ xⁱ yʲ`, where `F(X, Y) = ∑ aᵢⱼ Xⁱ Yʲ`. -/
theorem val_add_eq_tsum (x y : F.TopNilpotentPoint A) :
    (x + y).val = ∑' d : Fin 2 →₀ ℕ, coeff d F.toPowerSeries • (x.val ^ d 0 * y.val ^ d 1) :=
  (hasSum_val_add F x y).tsum_eq.symm

/-- The negation of a point is `∑ cₙ xⁿ`, where `i(X) = ∑ cₙ Xⁿ` is the formal inverse. -/
theorem val_neg_eq_tsum (x : F.TopNilpotentPoint A) :
    (-x).val = ∑' n, PowerSeries.coeff n F.addInvX • x.val ^ n :=
  (hasSum_val_neg F x).tsum_eq.symm

/-- The points of `F` in `A` form a group under `x +_F y = F(x, y)`, with `-x = i(x)`. Each law
is the evaluation of the corresponding identity of power series. -/
noncomputable instance : AddGroup (F.TopNilpotentPoint A) :=
  { add_assoc x y z := by
      let _ : UniformSpace R := ⊥
      have hb : MvPowerSeries.HasEval ![x.val, y.val, z.val] :=
        hasEval_of_finite_of_isTopologicallyNilpotent fun s ↦ by
          fin_cases s <;> simp [x.hasEval, y.hasEval, z.hasEval]
      have hX (i : Fin 3) : PowerSeries.HasSubst (X i : MvPowerSeries (Fin 3) R) :=
        PowerSeries.HasSubst.X i
      -- Evaluate `F(F(X₀, X₁), X₂) = F(X₀, F(X₁, X₂))` at `(x, y, z)`.
      have h := congrArg (eval₂ (algebraMap R A) ![x.val, y.val, z.val])
        (F.assoc' (hX 0) (hX 1) (hX 2))
      rw [eval₂_subst_finTwo (F.hasSubst_subst_pair (hX 0) (hX 1)) (hX 2) hb,
        eval₂_subst_finTwo (hX 0) (F.hasSubst_subst_pair (hX 1) (hX 2)) hb,
        eval₂_subst_finTwo (hX 0) (hX 1) hb, eval₂_subst_finTwo (hX 1) (hX 2) hb] at h
      ext
      simpa [val_add_eq_eval₂] using h
    zero_add x := by
      let _ : UniformSpace R := ⊥
      -- Evaluate `F(0, X) = X` at `x`.
      have h := congrArg (eval₂ (algebraMap R A) fun _ : Unit ↦ x.val)
        (F.zero_add (PowerSeries.HasSubst.X ()))
      rw [eval₂_subst_finTwo PowerSeries.HasSubst.zero (PowerSeries.HasSubst.X ())
        (PowerSeries.hasEval x.hasEval)] at h
      ext
      simpa [val_add_eq_eval₂] using h
    add_zero x := by
      let _ : UniformSpace R := ⊥
      -- Evaluate `F(X, 0) = X` at `x`.
      have h := congrArg (eval₂ (algebraMap R A) fun _ : Unit ↦ x.val)
        (F.add_zero (PowerSeries.HasSubst.X ()))
      rw [eval₂_subst_finTwo (PowerSeries.HasSubst.X ()) PowerSeries.HasSubst.zero
        (PowerSeries.hasEval x.hasEval)] at h
      ext
      simpa [val_add_eq_eval₂] using h
    nsmul := nsmulRec
    zsmul := zsmulRec
    neg_add_cancel x := by
      let _ : UniformSpace R := ⊥
      -- Evaluate `F(i(X), X) = 0` at `x`.
      have h := congrArg (eval₂ (algebraMap R A) fun _ : Unit ↦ x.val) F.subst_addInvX_X_eq_zero
      rw [eval₂_subst_finTwo F.hasSubst_addInvX PowerSeries.HasSubst.X'
        (PowerSeries.hasEval x.hasEval)] at h
      ext
      -- `PowerSeries.eval₂` and `PowerSeries.X` are by definition the evaluation at the family
      -- `fun _ ↦ x` and the variable `X ()`; unfolding them matches `h`.
      simpa [val_add_eq_eval₂, val_neg_eq_eval₂, PowerSeries.eval₂, PowerSeries.X] using h }

/-- The points of a commutative formal group law form a commutative group. -/
noncomputable instance [F.IsComm] : AddCommGroup (F.TopNilpotentPoint A) :=
  { add_comm x y := by
      let _ : UniformSpace R := ⊥
      -- Evaluate `F(X, Y) = F(Y, X)` at `(x, y)`.
      have h := congrArg (eval₂ (algebraMap R A) ![x.val, y.val]) (IsComm.comm (F := F))
      rw [eval₂_subst_finTwo (PowerSeries.HasSubst.X 1) (PowerSeries.HasSubst.X 0)
        (hasEval_finTwo x.hasEval y.hasEval)] at h
      ext
      simpa [val_add_eq_eval₂] using h }

section Map

variable {B C : Type*} [CommRing B] [Algebra R B] [UniformSpace B] [IsUniformAddGroup B]
  [CompleteSpace B] [T2Space B] [IsTopologicalRing B] [IsLinearTopology B B]
  [CommRing C] [Algebra R C] [UniformSpace C] [IsUniformAddGroup C]
  [CompleteSpace C] [T2Space C] [IsTopologicalRing C] [IsLinearTopology C C]

/-- A continuous `R`-algebra map `φ : A → B` maps points of `F` in `A` to points of `F` in `B`,
additively: `φ(F(x, y)) = F(φ(x), φ(y))`. -/
noncomputable def map (φ : A →A[R] B) : F.TopNilpotentPoint A →+ F.TopNilpotentPoint B where
  toFun x := ⟨φ x.val, x.hasEval.map φ.cont⟩
  map_zero' := TopNilpotentPoint.ext (map_zero φ)
  map_add' x y := by
    let _ : UniformSpace R := ⊥
    ext
    have h := congrFun (comp_eval₂ (φ := algebraMap R A) continuous_of_discreteTopology
      (hasEval_finTwo x.hasEval y.hasEval) (ε := (φ : A →+* B)) φ.cont) F.toPowerSeries
    have hφ : (φ : A →+* B).comp (algebraMap R A) = algebraMap R B := RingHom.ext φ.commutes
    rw [hφ] at h
    simp only [val_add_eq_eval₂]
    refine h.trans ?_
    congr 1
    funext s
    fin_cases s <;> rfl

@[simp]
theorem val_map (φ : A →A[R] B) (x : F.TopNilpotentPoint A) : (map F φ x).val = φ x.val := (rfl)

@[simp]
theorem map_id : map F (ContinuousAlgHom.id R A) = AddMonoidHom.id _ := (rfl)

theorem map_comp (ψ : B →A[R] C) (φ : A →A[R] B) :
    map F (ψ.comp φ) = (map F ψ).comp (map F φ) := (rfl)

end Map

end TopNilpotentPoint

section PowerSeries

open scoped WithPiTopology

variable [UniformSpace R] [DiscreteUniformity R] (σ : Type*)

/-- **Power-series points are points in `R⟦σ⟧`.** The group `F.Point σ` of power series with
nilpotent constant coefficient, under substitution into `F`, is the group of points of `F` in
`R⟦σ⟧` with the product topology over discrete `R`: a power series is topologically nilpotent
exactly when its constant coefficient is nilpotent, and substitution is evaluation. -/
noncomputable def pointEquivTopNilpotentPoint :
    F.Point σ ≃+ F.TopNilpotentPoint (MvPowerSeries σ R) where
  toFun x := ⟨x.val, WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_isNilpotent x.2⟩
  invFun x := ⟨x.val,
    (WithPiTopology.isTopologicallyNilpotent_iff_constantCoeff_isNilpotent x.val).1 x.hasEval⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' x y := TopNilpotentPoint.ext <| by
    rw [TopNilpotentPoint.val_add_eq_eval₂, ← subst_eq_eval₂]
    exact add_apply (F := F) (x := x) (y := y)

@[simp]
theorem val_pointEquivTopNilpotentPoint (x : F.Point σ) :
    (F.pointEquivTopNilpotentPoint σ x).val = x.val := (rfl)

@[simp]
theorem val_pointEquivTopNilpotentPoint_symm (x : F.TopNilpotentPoint (MvPowerSeries σ R)) :
    ((F.pointEquivTopNilpotentPoint σ).symm x).val = x.val := (rfl)

end PowerSeries

end FormalGroup
