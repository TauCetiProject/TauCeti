/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.DiagonalCosets
public import TauCeti.NumberTheory.HeckeRing.Multiplication

/-!
# Determinants in the support of Hecke products

The structure constants of a product of two Hecke cosets are supported on cosets whose
representatives have the product determinant. This is a first constraint on the terms in the
triangular expansion used to present the `p`-local `GL_n` Hecke ring as a polynomial ring.

The determinant calculation is independent of the dimension and exposes the invariant needed to
compare support terms with the leading elementary-divisor vector. Its proof generalizes the
determinant argument in AINTLIB's `LeanModularForms/HeckeRIngs/GLn/PolynomialRing.lean`, which is
used there for `n = 2`. -/

public section

open Matrix HeckeRing DoubleCoset Matrix.SpecialLinearGroup

namespace HeckeRing.GLn

variable {n : ℕ}

/-- Representatives of the same `SL_n(ℤ)` double coset have equal determinant. -/
private lemma det_rep_eq_of_heckeCoset_eq {g₁ g₂ : posDetInt n}
    (h : HeckeCoset.mk (SLnZ n) (SLnZ n) g₁ = HeckeCoset.mk (SLnZ n) (SLnZ n) g₂) :
    (↑(↑g₁ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det =
      (↑(↑g₂ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det :=
    det_eq_of_mem_doubleCoset_SLnZ n
    (HeckeCoset.eq_iff.mp h ▸ DoubleCoset.mem_doubleCoset_self _ _ _)

end HeckeRing.GLn

namespace HeckeCoset

variable {n : ℕ}

/-- A nonzero structure constant can occur only at a coset whose representative determinant is
the product of the input representative determinants. -/
theorem rep_det_eq_mul_of_structureConstants_ne_zero
    [IsHeckeTriple (HeckeRing.GLn.posDetInt n) (HeckeRing.GLn.SLnZ n)
      (HeckeRing.GLn.SLnZ n)]
    (D₁ D₂ D : HeckeCoset (HeckeRing.GLn.posDetInt n)
      (HeckeRing.GLn.SLnZ n) (HeckeRing.GLn.SLnZ n))
    (h : (HeckeCosetModule.structureConstants ℤ (HeckeRing.GLn.SLnZ n)
      (HeckeRing.GLn.SLnZ n) (HeckeRing.GLn.SLnZ n)
      (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) D ≠ 0) :
    (↑(↑(HeckeCoset.rep D) : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det =
      (↑(↑(HeckeCoset.rep D₁) : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det *
      (↑(↑(HeckeCoset.rep D₂) : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det := by
  classical
  rw [HeckeCosetModule.structureConstants_apply] at h
  have hD : D ∈ Finset.univ.image
      (HeckeCoset.mulMap (HeckeRing.GLn.SLnZ n) (HeckeRing.GLn.SLnZ n) (HeckeRing.GLn.SLnZ n)
        (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) :=
    (HeckeCoset.mem_image_mulMap_iff _ _ _).mpr (Nat.cast_ne_zero.mp h)
  obtain ⟨p, -, hD⟩ := Finset.mem_image.mp hD
  have hcoset := (HeckeCoset.mk_rep
      (HeckeCoset.mulMap (HeckeRing.GLn.SLnZ n) (HeckeRing.GLn.SLnZ n) (HeckeRing.GLn.SLnZ n)
        (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) p)).trans
    (HeckeCoset.mulMap_eq_mk _ _ _ _ _ _)
  have hDrep : HeckeCoset.mk (HeckeRing.GLn.SLnZ n) (HeckeRing.GLn.SLnZ n)
      (HeckeCoset.rep D) =
    HeckeCoset.mk (HeckeRing.GLn.SLnZ n) (HeckeRing.GLn.SLnZ n)
      (HeckeCoset.rep (HeckeCoset.mulMap (HeckeRing.GLn.SLnZ n) (HeckeRing.GLn.SLnZ n)
        (HeckeRing.GLn.SLnZ n) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) p)) :=
    (HeckeCoset.mk_rep D).trans
      (hD.symm.trans (HeckeCoset.mk_rep _).symm)
  rw [HeckeRing.GLn.det_rep_eq_of_heckeCoset_eq (hDrep.trans hcoset)]
  simp only [GeneralLinearGroup.coe_mul, Matrix.det_mul]
  have h₁ := HeckeRing.GLn.det_eq_one_of_mem_SLnZ n p.1.out.2
  have h₂ := HeckeRing.GLn.det_eq_one_of_mem_SLnZ n p.2.out.2
  rw [h₁, h₂]
  ring

end HeckeCoset
