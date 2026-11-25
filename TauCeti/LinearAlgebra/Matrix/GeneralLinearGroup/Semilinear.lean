/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Apply a matrix as a linear equivalence of the standard coordinate space. -/
private def coordinateLinearEquiv :
    GeneralLinearGroup ι R ≃* ((ι → R) ≃ₗ[R] (ι → R)) :=
  toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv R (ι → R))

variable (ι) in
/-- The equivalence sending an invertible matrix `b` to the automorphism `x ↦ b σ(x)`.
Its inverse removes the coefficient automorphism before taking the matrix. -/
def semilinearEquiv (σ : R ≃+* R) :
    GeneralLinearGroup ι R ≃ ((ι → R) ≃ₛₗ[(σ : R →+* R)] (ι → R)) where
  toFun b := (σ.piSemilinearEquiv ι).trans (coordinateLinearEquiv b)
  invFun e := coordinateLinearEquiv.symm ((σ.piSemilinearEquiv ι).symm.trans e)
  left_inv b := by
    apply coordinateLinearEquiv.injective
    apply LinearEquiv.ext
    intro x
    rw [MulEquiv.apply_symm_apply]
    exact congrArg (coordinateLinearEquiv b) ((σ.piSemilinearEquiv ι).apply_symm_apply x)
  right_inv e := by
    apply LinearEquiv.ext
    intro x
    have h := coordinateLinearEquiv.apply_symm_apply ((σ.piSemilinearEquiv ι).symm.trans e)
    exact (congrArg (fun f : (ι → R) ≃ₗ[R] (ι → R) => f (σ.piSemilinearEquiv ι x)) h).trans
      (congrArg e ((σ.piSemilinearEquiv ι).symm_apply_apply x))

@[simp]
theorem semilinearEquiv_apply (σ : R ≃+* R) (b : GeneralLinearGroup ι R) (x : ι → R) :
    semilinearEquiv ι σ b x = (b : Matrix ι ι R) *ᵥ (σ ∘ x) :=
  calc
    _ = (b : Matrix ι ι R) *ᵥ (σ.piSemilinearEquiv ι x) := toLin_apply b _
    _ = _ := by rw [σ.piSemilinearEquiv_apply]

/-- Applying the coefficient automorphism after a matrix action is the same as applying
the entrywise-transformed matrix after the coefficient automorphism. -/
theorem piSemilinearEquiv_toLin_apply (σ : R ≃+* R) (g : GeneralLinearGroup ι R) (x : ι → R) :
    σ.piSemilinearEquiv ι ((toLin g).toLinearEquiv x) =
      (toLin (mapEquiv ι σ g)).toLinearEquiv (σ.piSemilinearEquiv ι x) := by
  simp only [LinearMap.GeneralLinearGroup.coe_toLinearEquiv, toLin_apply, Matrix.mulVecLin_apply,
    RingEquiv.piSemilinearEquiv_apply, coe_mapEquiv_apply]
  exact funext (RingHom.map_mulVec (σ : R →+* R) (g : Matrix ι ι R) x)

/-- The linear map with matrix `g` intertwines `bσ` and `cσ` exactly when `g`
twisted-conjugates `b` to `c`. -/
theorem intertwines_semilinearEquiv_iff (σ : R ≃+* R) (b c g : GeneralLinearGroup ι R) :
    (∀ x, semilinearEquiv ι σ c ((toLin g).toLinearEquiv x) =
      (toLin g).toLinearEquiv (semilinearEquiv ι σ b x)) ↔
    c = g * b * (mapEquiv ι σ g)⁻¹ := by
  have h (d : GeneralLinearGroup ι R) (x : ι → R) :
      semilinearEquiv ι σ d x = coordinateLinearEquiv d (σ.piSemilinearEquiv ι x) := (rfl)
  have hg (x : ι → R) : σ.piSemilinearEquiv ι (coordinateLinearEquiv g x) =
      coordinateLinearEquiv (mapEquiv ι σ g) (σ.piSemilinearEquiv ι x) :=
    piSemilinearEquiv_toLin_apply σ g x
  -- Express the linear actions through a multiplicative equivalence so they can be cancelled.
  change (∀ x, semilinearEquiv ι σ c (coordinateLinearEquiv g x) =
    coordinateLinearEquiv g (semilinearEquiv ι σ b x)) ↔ _
  simp only [h, hg, eq_mul_inv_iff_mul_eq, ← mul_apply_eq_comp, ← map_mul]
  constructor
  · intro hintertwines
    apply coordinateLinearEquiv.injective
    apply LinearEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := (σ.piSemilinearEquiv ι).surjective x
    exact hintertwines y
  · intro heq x
    rw [heq]

end Matrix.GeneralLinearGroup
