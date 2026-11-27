/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import TauCeti.NumberTheory.ThetaLift.UpOperator

/-!
# A sanity check of the lift law modulo `N` and the operator `Up`

A small model in which the hypotheses of `TauCeti.ThetaLift.LiftLaw` and
`TauCeti.ThetaLift.IsRamified` hold non-trivially. There is one place and one index:
`A = F = R = (ℤ/3)^{pt}`, the reduction is the identity, and `1 × 1` matrices are read through
their single entry `χ T`. The representation `π g = χ(g)` of `GL₁(R)` on `ℤ/3` is a nontrivial
character, and the lift `L(Ψ) φ = (∑_T Ψ(T) χ(T)) φ` obeys the lift law with `D = D' = 1` and
`γ = 1`. The vector `2` is ramified, being `ψ - π(-1) ψ` for `ψ = 1`, and part (a) computes
`Up 2 = 1` for the weight `ψ(c) = c` and every `Up`-family, in agreement with the direct
evaluation `Up 2 = (1 · 1 + 2 · 2) · 2 = 1`.
-/

public section

open Matrix Matrix.GeneralLinearGroup TauCeti.ThetaLift

namespace TauCeti.Examples.NumberTheory.ThetaLift.UpOperator

/-- The residue ring `(ℤ/3)^P` at a single place. -/
abbrev R : Type := Unit → ZMod 3

/-- The single entry of a `1 × 1` matrix over `R`, a multiplicative map. -/
def χ : Matrix Unit Unit R →* ZMod 3 where
  toFun T := T () () ()
  map_one' := rfl
  map_mul' T S := by simp [Matrix.mul_apply]

@[simp]
theorem χ_apply (T : Matrix Unit Unit R) : χ T = T () () () := (rfl)

/-- The character `g ↦ χ g` of `GL₁(R)` on `ℤ/3`. -/
def π : Representation (ZMod 3) (GL Unit R) (ZMod 3) :=
  (Algebra.lmul (ZMod 3) (ZMod 3)).toRingHom.toMonoidHom.comp (χ.comp (Units.coeHom _))

/-- The lift `L(Ψ) φ = (∑_T Ψ(T) χ(T)) φ`. -/
def L : (Matrix Unit Unit R → ZMod 3) →ₗ[ZMod 3] ZMod 3 →ₗ[ZMod 3] ZMod 3 :=
  (Algebra.lmul (ZMod 3) (ZMod 3)).toLinearMap ∘ₗ ∑ T, χ T • LinearMap.proj T

theorem π_apply (g : GL Unit R) (φ : ZMod 3) : π g φ = χ g * φ := (rfl)

theorem L_apply (Ψ : Matrix Unit Unit R → ZMod 3) (φ : ZMod 3) :
    L Ψ φ = (∑ T, Ψ T * χ T) * φ := by
  simp [L, Finset.mul_sum, mul_comm]

/-- Sums over the `1 × 1` matrices are sums over `ℤ/3`. -/
theorem sum_matrix (f : Matrix Unit Unit R → ZMod 3) :
    ∑ T, f T = ∑ t : ZMod 3, f (of fun _ _ _ ↦ t) :=
  (Equiv.sum_comp ⟨fun t ↦ of fun _ _ _ ↦ t, fun T ↦ T () () (), fun _ ↦ rfl,
    fun _ ↦ by ext; rfl⟩ f).symm

/-- **The lift law holds** with `D = D' = 1` and factor `γ = 1`. -/
theorem liftLaw : LiftLaw (RingHom.id R) π π 1 1 () () L 1 where
  equivariant a b Ψ φ := by
    simp only [Algebra.algebraMap_self, Matrix.GeneralLinearGroup.map_id, MonoidHom.id_apply,
      π_apply, L_apply]
    rw [← Equiv.sum_comp ((Units.mulLeft b).trans (Units.mulRight a)) (fun T ↦ Ψ T * χ T)]
    simp only [Equiv.trans_apply, Units.mulLeft_apply, Units.mulRight_apply, map_mul,
      Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  pole φ := by
    have h : lastRowDatum (ZMod 3) () (Pi.single () 1) =
        directDatum (ZMod 3) (R := R) () () := by
      ext T
      simp [directDatum_def, funext_iff]
    simp [h]

/-- **A nonzero ramified vector**: `2 = 1 - π(-1) 1`. -/
theorem isRamified_two : IsRamified (RingHom.id R) π 2 ∧ (2 : ZMod 3) ≠ 0 := by
  refine ⟨isRamified_iff.2 fun _ ↦ ⟨-1, 1, fun w' h ↦ (h (Subsingleton.elim _ _)).elim, ?_⟩,
    by decide⟩
  simp only [Algebra.algebraMap_self, Matrix.GeneralLinearGroup.map_id, MonoidHom.id_apply,
    π_apply, coe_scalar, Units.val_neg, Units.val_one, scalar_apply, χ_apply, diagonal_apply_eq,
    Pi.neg_apply, Pi.one_apply, mul_one, sub_neg_eq_add]
  decide

/-- **Part (a) computes `Up`**: for `ψ(c) = c` and every `Up`-family `g`, `Up 2 = 1`. -/
example {g : (Unit → R) → GL Unit R} (hg : IsUpFamily (RingHom.id R) () g) :
    upOperator π 1 () g (fun c ↦ c ()) 2 = 1 := by
  have h := liftLaw.mirrorDatum_eq_smul_directDatum_upOperator hg isRamified_two.1
    (fun c ↦ c ())
  rw [one_smul, map_one, one_apply_eq_self, L_apply, L_apply, sum_matrix, sum_matrix] at h
  -- both sides are explicit sums over `ℤ/3`: `(0 + 1 + 4) · 2 = 1` and `1`
  have h₁ : (∑ t : ZMod 3, t * t) * 2 = 1 := by decide
  simp only [mirrorDatum_apply, of_apply, χ_apply, directDatum_def, lastColDatum_apply, col_of,
    funext_iff, Function.swap, Pi.single_eq_same, Pi.one_apply, forall_const, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, h₁] at h
  exact h.symm

end TauCeti.Examples.NumberTheory.ThetaLift.UpOperator
