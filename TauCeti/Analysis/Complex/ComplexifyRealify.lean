/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Star.LinearMap
public import TauCeti.Analysis.Complex.CoordinateRealification

/-!
# Splitting complexified real coordinate spaces

Complexifying the underlying real space of a complex vector space recovers the original
space together with its conjugate. In real-part/imaginary-part block coordinates the
splitting sends `(a, b)` to `(a + I b, a - I b)`. The second component is complex-linear
in the new coordinates: conjugation appears in the operator on that component, not
in the splitting map itself.

`TauCeti.complexifyRealifyCoords` implements this change of coordinates, and
`ContinuousLinearMap.complexifyRealifyCoords_comp_complexifyCoords_realifyCoords`
intertwines complexified real operators with the original operator and its intrinsic
conjugate. This makes the splitting applicable to transition functions of complex vector bundles.

## References

* M. F. Atiyah, *K-Theory*, §1.2, realification and complexification.
-/

public section

open Complex WithConv

namespace TauCeti

/-- The splitting of complexified real coordinates into the original and conjugate
coordinate blocks. The input blocks are real and imaginary coordinates before
complexification; the output blocks are `a + I b` and `a - I b`. -/
noncomputable def complexifyRealifyCoords (n : ℕ) :
    (Fin (n + n) → ℂ) ≃L[ℂ] (Fin (n + n) → ℂ) :=
  let e : ((Fin n → ℂ) × (Fin n → ℂ)) ≃ₗ[ℂ] ((Fin n → ℂ) × (Fin n → ℂ)) := by
    refine
      { toFun p := (p.1 + I • p.2, p.1 - I • p.2)
        invFun p := ((2 : ℂ)⁻¹ • (p.1 + p.2), (2 * I)⁻¹ • (p.1 - p.2))
        left_inv := ?_
        right_inv := ?_
        map_add' p q := by ext i <;> simp <;> ring
        map_smul' c p := by ext i <;> simp <;> ring }
    all_goals
      intro p
      ext i <;> simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      all_goals field_simp; ring
  (splitCoords n n).trans (e.toContinuousLinearEquiv.trans (splitCoords n n).symm)

/-- The two output blocks of the splitting. -/
theorem splitCoords_complexifyRealifyCoords (n : ℕ) (w : Fin (n + n) → ℂ) :
    splitCoords (𝕜 := ℂ) n n (complexifyRealifyCoords n w) =
      ((splitCoords (𝕜 := ℂ) n n w).1 + I • (splitCoords (𝕜 := ℂ) n n w).2,
        (splitCoords (𝕜 := ℂ) n n w).1 - I • (splitCoords (𝕜 := ℂ) n n w).2) := by
  simp [complexifyRealifyCoords]

/-- The inverse splitting takes the half-sum and the difference divided by `2 I`. -/
theorem splitCoords_complexifyRealifyCoords_symm (n : ℕ) (w : Fin (n + n) → ℂ) :
    splitCoords (𝕜 := ℂ) n n ((complexifyRealifyCoords n).symm w) =
      ((2 : ℂ)⁻¹ • ((splitCoords (𝕜 := ℂ) n n w).1 + (splitCoords (𝕜 := ℂ) n n w).2),
        (2 * I)⁻¹ • ((splitCoords (𝕜 := ℂ) n n w).1 - (splitCoords (𝕜 := ℂ) n n w).2)) := by
  simp [complexifyRealifyCoords]

/-- The first block of the splitting is the sum of the first block and `I` times the second. -/
@[simp] theorem complexifyRealifyCoords_apply_castAdd (n : ℕ) (w : Fin (n + n) → ℂ)
    (i : Fin n) :
    complexifyRealifyCoords n w (i.castAdd n) = w (i.castAdd n) + I * w (i.addNat n) := by
  simpa using congrFun (congrArg Prod.fst (splitCoords_complexifyRealifyCoords n w)) i

/-- The second block of the splitting is the first block minus `I` times the second. -/
@[simp] theorem complexifyRealifyCoords_apply_addNat (n : ℕ) (w : Fin (n + n) → ℂ)
    (i : Fin n) :
    complexifyRealifyCoords n w (i.addNat n) = w (i.castAdd n) - I * w (i.addNat n) := by
  simpa using congrFun (congrArg Prod.snd (splitCoords_complexifyRealifyCoords n w)) i

/-- The first block of the inverse splitting is the half-sum of the two input blocks. -/
@[simp] theorem complexifyRealifyCoords_symm_apply_castAdd (n : ℕ) (w : Fin (n + n) → ℂ)
    (i : Fin n) :
    (complexifyRealifyCoords n).symm w (i.castAdd n) =
      (2 : ℂ)⁻¹ * (w (i.castAdd n) + w (i.addNat n)) := by
  simpa using congrFun (congrArg Prod.fst (splitCoords_complexifyRealifyCoords_symm n w)) i

/-- The second block of the inverse splitting is the block difference divided by `2 I`. -/
@[simp] theorem complexifyRealifyCoords_symm_apply_addNat (n : ℕ) (w : Fin (n + n) → ℂ)
    (i : Fin n) :
    (complexifyRealifyCoords n).symm w (i.addNat n) =
      (2 * I)⁻¹ * (w (i.castAdd n) - w (i.addNat n)) := by
  simpa using congrFun (congrArg Prod.snd (splitCoords_complexifyRealifyCoords_symm n w)) i

/-- On the real form the splitting gives a vector and its coordinatewise conjugate. -/
theorem splitCoords_complexifyRealifyCoords_ofReal (n : ℕ) (w : Fin (n + n) → ℝ) :
    splitCoords (𝕜 := ℂ) n n (complexifyRealifyCoords n (fun i => (w i : ℂ))) =
      ((realCoords n).symm w, star ((realCoords n).symm w)) := by
  rw [splitCoords_complexifyRealifyCoords]
  ext i <;> simp [splitCoords_apply, realCoords_symm_apply, Complex.ext_iff]

end TauCeti

namespace ContinuousLinearMap

open TauCeti

/-- Complexification of a realified operator is conjugate to the block diagonal
operator consisting of the original operator and its intrinsic conjugate. -/
theorem complexifyRealifyCoords_comp_complexifyCoords_realifyCoords {m n : ℕ}
    (g : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)) :
    (complexifyRealifyCoords n).toContinuousLinearMap.comp g.realifyCoords.complexifyCoords =
      (splitCoords n n).symm.toContinuousLinearMap.comp
        ((g.prodMap (star (toConv g)).ofConv).comp
          ((splitCoords m m).toContinuousLinearMap.comp
            (complexifyRealifyCoords m).toContinuousLinearMap)) := by
  -- On the real basis vectors, complexification acts by the realified map and
  -- the splitting sends each real coordinate vector to a vector and its conjugate.
  apply coe_injective
  apply (Pi.basisFun ℂ (Fin (m + m))).ext
  intro j
  have hj : (Pi.single j 1 : Fin (m + m) → ℂ) =
      fun i => ((Pi.single j 1 : Fin (m + m) → ℝ) i : ℂ) := by
    ext i
    by_cases h : i = j <;> simp [h]
  apply (splitCoords (𝕜 := ℂ) n n).injective
  simp only [coe_coe, Pi.basisFun_apply, hj, comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [ContinuousLinearEquiv.apply_symm_apply, complexifyCoords_ofReal,
    splitCoords_complexifyRealifyCoords_ofReal, splitCoords_complexifyRealifyCoords_ofReal]
  simp [realifyCoords_apply]

end ContinuousLinearMap
