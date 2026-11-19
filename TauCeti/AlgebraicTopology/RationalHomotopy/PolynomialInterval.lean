/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.TrivSqZeroExt
public import TauCeti.Algebra.Polynomial.Derivative

/-!
# The polynomial interval

The polynomial interval `Λ(t, dt)` over a field `K` is the commutative differential graded algebra
of polynomial differential forms on the unit interval: `K[t]` in degree `0`, `K[t] dt` in degree
`1`, and `d p = p' dt`.  It is the interval object of the homotopy theory of commutative
differential graded algebras in characteristic zero: a polynomial homotopy between two maps
`M → A` is a map `M → A ⊗ Λ(t, dt)`, and its two ends are obtained by evaluating at `t = 0` and
`t = 1`.  It is also the algebra `A_PL(Δ¹)` of polynomial forms on the `1`-simplex.

Here `Λ(t, dt)` is realised as the differential graded algebra of the derivation
`Polynomial.derivative' : K[X] → K[X]` on the trivial square-zero extension `K[X] ⊕ K[X]`
(`TauCeti.Algebra.Homology.DG.Algebra.TrivSqZeroExt`), the second summand standing for `K[X] dt`.

## Main definitions

* `TauCeti.PolynomialInterval`: the underlying algebra `K[t] ⊕ K[t] dt` of `Λ(t, dt)`.
* `TauCeti.PolynomialInterval.eval`: the evaluation `t ↦ a`, `dt ↦ 0` at a point `a : K`, an
  augmentation of `Λ(t, dt)`; `eval 0` and `eval 1` are the two ends of the interval.
* `TauCeti.PolynomialInterval.pullback`: the pullback of polynomial forms along a polynomial map
  `s`, the differential graded algebra endomorphism `t ↦ s`, `dt ↦ s' dt`.

## Main results

* `TauCeti.PolynomialInterval.isDGAlgebra`: `Λ(t, dt)` is a differential graded algebra.
* `TauCeti.PolynomialInterval.bijective_cohomologyMap_unitHom`: in characteristic zero the unit
  `K → Λ(t, dt)` is a quasi-isomorphism, so `H(Λ(t, dt)) = K`.
* `TauCeti.PolynomialInterval.bijective_cohomologyMap_eval`: in characteristic zero every
  evaluation, in particular each end of the interval, is a quasi-isomorphism.
* `TauCeti.PolynomialInterval.not_bijective_cohomologyMap_unitHom_of_charP`: in characteristic
  `p > 0` the unit is not a quasi-isomorphism, since the form `t ^ (p - 1) dt` is not exact.
* `TauCeti.PolynomialInterval.eval_comp_pullback` and
  `TauCeti.PolynomialInterval.pullback_comp_pullback`: pullback is compatible with evaluation and
  with composition; for `s = 1 - t` it is the reflection of the interval, an involution
  exchanging its two ends.

## References

* K. Hess, *Rational homotopy theory: a brief introduction*, §1, before Proposition 1.14.
* J. W. Morgan, *The algebraic topology of smooth algebraic varieties*, §5.
-/

public section

open Polynomial TrivSqZeroExt

namespace TauCeti

variable (K : Type*) [Field K]

/-- The underlying algebra `K[t] ⊕ K[t] dt` of the polynomial interval `Λ(t, dt)`: the trivial
square-zero extension of `K[t]` by itself, the second summand standing for the forms `q dt`. -/
abbrev PolynomialInterval : Type _ :=
  TrivSqZeroExt K[X] K[X]

namespace PolynomialInterval

/-- The polynomial interval `Λ(t, dt)`, with `K[t]` in degree `0`, `K[t] dt` in degree `1` and
differential `d p = p' dt`, is a differential graded algebra. -/
theorem isDGAlgebra :
    IsDGAlgebra (grading K K[X] K[X]) (derivative' (R := K)).trivSqZeroExtDifferential :=
  derivative'.isDGAlgebra_trivSqZeroExtDifferential

variable {K}

/-- The evaluation `t ↦ a`, `dt ↦ 0` of the polynomial interval at a point `a : K`, as an
augmentation; `eval 0` and `eval 1` are the two ends of the interval. -/
noncomputable def eval (a : K) : DGAlgAugmentation (isDGAlgebra K) :=
  derivative'.trivSqZeroExtAugmentation (aeval a)

@[simp]
theorem eval_apply (a : K) (x : PolynomialInterval K) : eval a x = x.fst.eval a := by
  simp [eval, aeval_def, eval₂_id]

/-- **The polynomial interval is acyclic** in characteristic zero: the unit `K → Λ(t, dt)` is a
quasi-isomorphism, since a polynomial with zero derivative is constant and every polynomial has an
antiderivative. -/
theorem bijective_cohomologyMap_unitHom [CharZero K] :
    Function.Bijective (isDGAlgebra K).unitHom.cohomologyMap :=
  derivative'.bijective_cohomologyMap_unitHom_iff.mpr
    ⟨C_injective, fun p hp ↦ ⟨p.coeff 0, (eq_C_of_natDegree_eq_zero
      (derivative_eq_zero.mp hp)).symm⟩, derivative_surjective⟩

/-- In characteristic zero every evaluation of the polynomial interval, in particular each of its
two ends `eval 0` and `eval 1`, is a quasi-isomorphism `Λ(t, dt) → K`. -/
theorem bijective_cohomologyMap_eval [CharZero K] (a : K) :
    Function.Bijective (eval a).cohomologyMap :=
  (DGAlgAugmentation.bijective_cohomologyMap_iff _).mpr bijective_cohomologyMap_unitHom

/-- In characteristic `p > 0` the polynomial interval is not acyclic: the form `t ^ (p - 1) dt`
is a cycle that is not exact, so the unit `K → Λ(t, dt)` is not a quasi-isomorphism. -/
theorem not_bijective_cohomologyMap_unitHom_of_charP (p : ℕ) [CharP K p] [NeZero p] :
    ¬Function.Bijective (isDGAlgebra K).unitHom.cohomologyMap := fun h ↦
  not_surjective_derivative_of_charP p
    (derivative'.bijective_cohomologyMap_unitHom_iff.mp h).2.2

/-- The algebra map underlying `TauCeti.PolynomialInterval.pullback`. -/
private noncomputable def pullbackAlgHom (s : K[X]) :
    PolynomialInterval K →ₐ[K] PolynomialInterval K :=
  lift ((inlAlgHom K K[X] K[X]).comp (aeval s))
    { toFun q := inr (q.comp s * derivative s)
      map_add' q q' := by simp [add_mul]
      map_smul' c q := by simp [smul_comp] }
    (fun _ _ ↦ inr_mul_inr _ _ _)
    (fun r q ↦ by simp [mul_comp, mul_assoc, inl_mul_inr, ← comp_eq_aeval])
    (fun r q ↦ by simp [mul_comp, inr_mul_inl, mul_right_comm, ← comp_eq_aeval])

private theorem pullbackAlgHom_apply (s : K[X]) (x : PolynomialInterval K) :
    pullbackAlgHom s x = inl (x.fst.comp s) + inr (x.snd.comp s * derivative s) := by
  simp [pullbackAlgHom, lift_def, comp_eq_aeval]

/-- The pullback of polynomial forms along a polynomial map `s : K → K`: the differential graded
algebra endomorphism of `Λ(t, dt)` sending `p` to `p ∘ s` and `q dt` to `(q ∘ s) s' dt`. For
`s = 1 - t` it is the reflection of the interval. -/
noncomputable def pullback (s : K[X]) : DGAlgHom (isDGAlgebra K) (isDGAlgebra K) where
  toGradedAlgHom :=
    { toAlgHom := pullbackAlgHom s
      map_mem := fun {n} {x} hx ↦ by
        rw [mem_grading_iff] at hx ⊢
        exact ⟨fun hn ↦ by simp [pullbackAlgHom_apply, hx.1 hn],
          fun hn ↦ by simp [pullbackAlgHom_apply, hx.2 hn]⟩ }
  map_d' x := by
    ext <;> simp [pullbackAlgHom_apply, derivative_comp, mul_comm]

@[simp]
theorem fst_pullback (s : K[X]) (x : PolynomialInterval K) :
    (pullback s x).fst = x.fst.comp s := by
  simp [pullback, pullbackAlgHom_apply]

@[simp]
theorem snd_pullback (s : K[X]) (x : PolynomialInterval K) :
    (pullback s x).snd = x.snd.comp s * derivative s := by
  simp [pullback, pullbackAlgHom_apply]

/-- Evaluating a pulled-back form at `a` is evaluating it at `s a`; for the reflection `s = 1 - t`
this exchanges the two ends `eval 0` and `eval 1` of the interval. -/
@[simp]
theorem eval_comp_pullback (a : K) (s : K[X]) :
    (eval a).comp (pullback s) = eval (s.eval a) := by
  ext x
  simp

/-- Pulling back along `s'` and then along `s` is pulling back along `s' ∘ s`. -/
@[simp]
theorem pullback_comp_pullback (s s' : K[X]) :
    (pullback s).comp (pullback s') = pullback (s'.comp s) := by
  refine DGAlgHom.ext fun x ↦ TrivSqZeroExt.ext ?_ ?_
  · simp [comp_assoc]
  · simp only [DGAlgHom.comp_apply, snd_pullback, mul_comp, derivative_comp, comp_assoc]
    ring

/-- Pulling back along the identity `t ↦ t` is the identity. -/
@[simp]
theorem pullback_X : pullback (X : K[X]) = DGAlgHom.id (isDGAlgebra K) := by
  ext x <;> simp

end PolynomialInterval

end TauCeti
