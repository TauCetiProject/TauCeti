/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CoordinateRealification
public import TauCeti.Analysis.Normed.Operator.IntrinsicStar

/-!
# Splitting complexified real coordinate spaces

Complexifying the underlying real space of a complex vector space recovers the original
space together with its conjugate. In real-part/imaginary-part block coordinates the
splitting sends `(a, b)` to `(a + I b, a - I b)`. The second component is complex-linear
in the new coordinates: conjugation appears in the operator on that component, not
in the splitting map itself.

`TauCeti.complexifyRealifyCoords` implements this change of coordinates, and
`ContinuousLinearMap.complexifyRealifyCoords_comp` intertwines complexified real
operators with the original operator and its intrinsic conjugate. This makes the
splitting applicable to transition functions of complex vector bundles.

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
  let e : ((Fin n → ℂ) × (Fin n → ℂ)) ≃ₗ[ℂ] ((Fin n → ℂ) × (Fin n → ℂ)) :=
    { toFun p := (p.1 + I • p.2, p.1 - I • p.2)
      invFun p := ((2 : ℂ)⁻¹ • (p.1 + p.2), (2 * I)⁻¹ • (p.1 - p.2))
      left_inv p := by
        ext i <;> simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        all_goals field_simp; ring_nf
      right_inv p := by
        ext i <;> simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        all_goals field_simp; ring_nf
      map_add' p q := by ext i <;> simp <;> ring
      map_smul' c p := by ext i <;> simp <;> ring }
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

/-- On the real form the splitting gives a vector and its coordinatewise conjugate. -/
theorem complexifyRealifyCoords_ofReal (n : ℕ) (w : Fin (n + n) → ℝ) :
    splitCoords (𝕜 := ℂ) n n (complexifyRealifyCoords n (fun i => (w i : ℂ))) =
      ((realCoords n).symm w, star ((realCoords n).symm w)) := by
  rw [splitCoords_complexifyRealifyCoords]
  ext i <;> simp [splitCoords_apply, realCoords_symm_apply, Complex.ext_iff]

end TauCeti

namespace ContinuousLinearMap

open TauCeti

/-- Complexification of a realified operator is conjugate to the block diagonal
operator consisting of the original operator and its intrinsic conjugate. -/
theorem complexifyRealifyCoords_comp {m n : ℕ} (g : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)) :
    (complexifyRealifyCoords n).toContinuousLinearMap.comp g.realifyCoords.complexifyCoords =
      (splitCoords n n).symm.toContinuousLinearMap.comp
        ((g.prodMap (star (toConv g)).ofConv).comp
          ((splitCoords m m).toContinuousLinearMap.comp
            (complexifyRealifyCoords m).toContinuousLinearMap)) := by
  apply coe_injective
  apply (Pi.basisFun ℂ (Fin (m + m))).ext
  intro j
  have hj : (Pi.single j 1 : Fin (m + m) → ℂ) =
      fun i => ((Pi.single j 1 : Fin (m + m) → ℝ) i : ℂ) := by
    ext i
    by_cases h : i = j <;> simp [h]
  apply (splitCoords (𝕜 := ℂ) n n).injective
  simp only [coe_coe, Pi.basisFun_apply, hj, comp_apply,
    complexifyCoords_ofReal, complexifyRealifyCoords_ofReal,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    prodMap, prod_apply, coe_fst', coe_snd',
    intrinsicStar_apply, star_star]
  rw [realifyCoords_apply, ContinuousLinearEquiv.symm_apply_apply]

end ContinuousLinearMap
