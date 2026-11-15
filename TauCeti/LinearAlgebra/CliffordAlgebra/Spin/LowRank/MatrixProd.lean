/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.MatrixProd
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Four

/-!
# Quaternary Spin groups in a chosen matrix-product model

A product-of-two-by-two-matrices model of a regular quaternary even Clifford algebra identifies
its Spin group with `SL₂ × SL₂`. Reversal becomes adjugation in each factor, so the reverse
norm-one equation becomes determinant one in each factor.
`spinGroupEquivEvenUnitaryOfFinrankLeFour` supplies the exact image.

The forward and inverse equations keep this equivalence compatible with the chosen algebra
model, in particular when that model is supplied by the half-spin representations.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20.
-/

public section

namespace CliffordAlgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Invertible (2 : K)]
  (Q : QuadraticForm K V)

/-- A chosen matrix-product model identifies the reverse-unitary carrier of a regular quaternary
form with `SL₂ × SL₂`. -/
noncomputable def evenUnitaryGroupEquivSpecialLinearProdOfAlgEquiv
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 4)
    (e : even Q ≃ₐ[K] Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K) :
    evenUnitaryGroup Q ≃* Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K :=
  evenUnitaryGroupEquivOfAlgEquiv Q e (fun y => y.1.det = 1 ∧ y.2.det = 1)
    ((Matrix.SpecialLinearGroup.coeMonoidHom (ι := Fin 2) (R := K)).prodMap
      (Matrix.SpecialLinearGroup.coeMonoidHom (ι := Fin 2) (R := K)))
    ((Matrix.SpecialLinearGroup.coeMonoidHom_injective (ι := Fin 2) (R := K)).prodMap
      (Matrix.SpecialLinearGroup.coeMonoidHom_injective (ι := Fin 2) (R := K)))
    (fun y hy => (⟨y.1, hy.1⟩, ⟨y.2, hy.2⟩)) (fun _ _ => rfl)
    (fun q => ⟨q.1.det_coe, q.2.det_coe⟩)
    (reverseEven_mul_eq_one_iff_det_eq_one_prod_of_finrank_eq_four Q hQ hV e)

/-- The forward unitary equivalence evaluates the chosen even Clifford model. -/
@[simp]
theorem coe_evenUnitaryGroupEquivSpecialLinearProdOfAlgEquiv_apply
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 4)
    (e : even Q ≃ₐ[K] Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K)
    (x : evenUnitaryGroup Q) :
    (((evenUnitaryGroupEquivSpecialLinearProdOfAlgEquiv Q hQ hV e x).1 :
        Matrix (Fin 2) (Fin 2) K),
      ((evenUnitaryGroupEquivSpecialLinearProdOfAlgEquiv Q hQ hV e x).2 :
        Matrix (Fin 2) (Fin 2) K)) = e (evenUnitaryGroupEvenPart Q x) := by
  rw [evenUnitaryGroupEquivSpecialLinearProdOfAlgEquiv]
  exact coe_evenUnitaryGroupEquivOfAlgEquiv_apply Q e _
    ((Matrix.SpecialLinearGroup.coeMonoidHom (ι := Fin 2) (R := K)).prodMap
      (Matrix.SpecialLinearGroup.coeMonoidHom (ι := Fin 2) (R := K))) _ _ _ _ _ x

/-- The inverse unitary equivalence evaluates the inverse even Clifford model. -/
@[simp]
theorem evenUnitaryGroupEquivSpecialLinearProdOfAlgEquiv_symm_apply_evenPart
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 4)
    (e : even Q ≃ₐ[K] Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K)
    (g : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    evenUnitaryGroupEvenPart Q
        ((evenUnitaryGroupEquivSpecialLinearProdOfAlgEquiv Q hQ hV e).symm g) =
      e.symm ((g.1 : Matrix (Fin 2) (Fin 2) K), (g.2 : Matrix (Fin 2) (Fin 2) K)) := by
  apply evenUnitaryGroupEquivOfAlgEquiv_symm_apply_evenPart

/-- A chosen matrix-product model identifies the Spin group of a regular quaternary form with
`SL₂ × SL₂`. -/
noncomputable def spinGroupEquivSpecialLinearProdOfAlgEquiv
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 4)
    (e : even Q ≃ₐ[K] Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K) :
    spinGroup Q ≃* Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K :=
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  (spinGroupEquivEvenUnitaryOfFinrankLeFour Q hQ (by omega) (by omega)).trans
    (evenUnitaryGroupEquivSpecialLinearProdOfAlgEquiv Q hQ hV e)

/-- The Spin equivalence applies the chosen algebra model to the underlying even element. -/
@[simp]
theorem coe_spinGroupEquivSpecialLinearProdOfAlgEquiv_apply
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 4)
    (e : even Q ≃ₐ[K] Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K)
    (g : spinGroup Q) :
    (((spinGroupEquivSpecialLinearProdOfAlgEquiv Q hQ hV e g).1 : Matrix (Fin 2) (Fin 2) K),
      ((spinGroupEquivSpecialLinearProdOfAlgEquiv Q hQ hV e g).2 : Matrix (Fin 2) (Fin 2) K)) =
      e (evenUnitaryGroupEvenPart Q (spinGroupToEvenUnitary Q g)) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  rw [spinGroupEquivSpecialLinearProdOfAlgEquiv, MulEquiv.trans_apply,
    spinGroupEquivEvenUnitaryOfFinrankLeFour_apply,
    coe_evenUnitaryGroupEquivSpecialLinearProdOfAlgEquiv_apply]

/-- The inverse Spin equivalence recovers the Clifford value through the inverse algebra model. -/
@[simp]
theorem coe_spinGroupEquivSpecialLinearProdOfAlgEquiv_symm_apply
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 4)
    (e : even Q ≃ₐ[K] Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K)
    (g : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    ((spinGroupEquivSpecialLinearProdOfAlgEquiv Q hQ hV e).symm g : CliffordAlgebra Q) =
      (e.symm ((g.1 : Matrix (Fin 2) (Fin 2) K), (g.2 : Matrix (Fin 2) (Fin 2) K)) :
        CliffordAlgebra Q) := by
  have h := coe_spinGroupEquivSpecialLinearProdOfAlgEquiv_apply Q hQ hV e
    ((spinGroupEquivSpecialLinearProdOfAlgEquiv Q hQ hV e).symm g)
  rw [MulEquiv.apply_symm_apply] at h
  have he := congrArg e.symm h
  rw [e.symm_apply_apply] at he
  simpa using congrArg Subtype.val he.symm

end CliffordAlgebra
