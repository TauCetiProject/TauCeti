/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.ToLin
public import TauCeti.LinearAlgebra.Pi.Semilinear

/-!
# Matrices of semilinear automorphisms

For a coefficient automorphism `σ` of a commutative ring, an invertible matrix `b` represents
the semilinear automorphism `x ↦ b σ(x)`. A linear change of coordinates with matrix `g`
intertwines the operators for `b` and `c` exactly when `c = g b σ(g)⁻¹`.

## References

* R. E. Kottwitz, *Isocrystals with additional structure*, Compositio Math. 56 (1985), p. 202.
-/

public section

attribute [local instance] RingHomInvPair.of_ringEquiv

namespace Matrix.GeneralLinearGroup

open Matrix
open TauCeti (matrixLinearEquiv matrixLinearEquiv_apply)

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

variable (ι) in
/-- The equivalence sending an invertible matrix `b` to the automorphism `x ↦ b σ(x)`.
Its inverse removes the coefficient automorphism before taking the matrix. -/
noncomputable def semilinearEquiv (σ : R ≃+* R) :
    GeneralLinearGroup ι R ≃ ((ι → R) ≃ₛₗ[(σ : R →+* R)] (ι → R)) where
  toFun b := (σ.piSemilinearEquiv ι).trans (matrixLinearEquiv b)
  invFun e := matrixLinearEquiv.symm ((σ.piSemilinearEquiv ι).symm.trans e)
  left_inv b := by
    apply matrixLinearEquiv.injective
    apply LinearEquiv.ext
    intro x
    rw [MulEquiv.apply_symm_apply]
    -- Project to ordinary equivalences: the inferred semilinear inverse uses `σ.symm.symm`,
    -- which prevents the generic semilinear composition laws from matching implicitly.
    change (matrixLinearEquiv b).toEquiv
      ((σ.piSemilinearEquiv ι).toEquiv ((σ.piSemilinearEquiv ι).toEquiv.symm x)) =
      (matrixLinearEquiv b).toEquiv x
    simp only [Equiv.apply_symm_apply]
  right_inv e := by
    apply LinearEquiv.ext
    intro x
    change (matrixLinearEquiv
      (matrixLinearEquiv.symm ((σ.piSemilinearEquiv ι).symm.trans e))).toEquiv
      ((σ.piSemilinearEquiv ι).toEquiv x) = e.toEquiv x
    rw [MulEquiv.apply_symm_apply]
    change e.toEquiv ((σ.piSemilinearEquiv ι).toEquiv.symm
      ((σ.piSemilinearEquiv ι).toEquiv x)) = e.toEquiv x
    simp only [Equiv.symm_apply_apply]

/-- The semilinear action applies the coefficient automorphism before the linear matrix action. -/
theorem semilinearEquiv_apply_eq_matrixLinearEquiv
    (σ : R ≃+* R) (b : GeneralLinearGroup ι R) (x : ι → R) :
    semilinearEquiv ι σ b x = matrixLinearEquiv b (σ.piSemilinearEquiv ι x) := (rfl)

@[simp]
theorem semilinearEquiv_apply (σ : R ≃+* R) (b : GeneralLinearGroup ι R) (x : ι → R) :
    semilinearEquiv ι σ b x = (b : Matrix ι ι R) *ᵥ (σ ∘ x) := by
  simp only [semilinearEquiv_apply_eq_matrixLinearEquiv, matrixLinearEquiv_apply,
    RingEquiv.piSemilinearEquiv_apply]

@[simp]
theorem semilinearEquiv_symm_apply
    (σ : R ≃+* R) (e : (ι → R) ≃ₛₗ[(σ : R →+* R)] (ι → R)) :
    (semilinearEquiv ι σ).symm e =
      matrixLinearEquiv.symm ((σ.piSemilinearEquiv ι).symm.trans e) := (rfl)

/-- Applying the coefficient automorphism after a matrix action is the same as applying
the entrywise-transformed matrix after the coefficient automorphism. -/
theorem piSemilinearEquiv_matrixLinearEquiv_apply
    (σ : R ≃+* R) (g : GeneralLinearGroup ι R) (x : ι → R) :
    σ.piSemilinearEquiv ι (matrixLinearEquiv g x) =
      matrixLinearEquiv (mapEquiv ι σ g) (σ.piSemilinearEquiv ι x) := by
  simp only [matrixLinearEquiv_apply,
    RingEquiv.piSemilinearEquiv_apply, coe_mapEquiv_apply]
  exact funext (RingHom.map_mulVec (σ : R →+* R) (g : Matrix ι ι R) x)

/-- The linear map with matrix `g` intertwines `bσ` and `cσ` exactly when `g`
twisted-conjugates `b` to `c`. -/
theorem intertwines_semilinearEquiv_iff (σ : R ≃+* R) (b c g : GeneralLinearGroup ι R) :
    (∀ x, semilinearEquiv ι σ c (matrixLinearEquiv g x) =
      matrixLinearEquiv g (semilinearEquiv ι σ b x)) ↔
    c = g * b * (mapEquiv ι σ g)⁻¹ := by
  -- Express the linear actions through a multiplicative equivalence so they can be cancelled.
  simp only [semilinearEquiv_apply_eq_matrixLinearEquiv, piSemilinearEquiv_matrixLinearEquiv_apply,
    eq_mul_inv_iff_mul_eq, ← mul_apply_eq_comp, ← map_mul]
  constructor
  · intro hintertwines
    apply matrixLinearEquiv.injective
    apply LinearEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := (σ.piSemilinearEquiv ι).surjective x
    exact hintertwines y
  · intro heq x
    rw [heq]

end Matrix.GeneralLinearGroup
