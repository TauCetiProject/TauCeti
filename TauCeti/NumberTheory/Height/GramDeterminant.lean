/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import TauCeti.NumberTheory.Height.FamilyOverPairs

/-!
# Transferring a height bound between Gram determinants

A family of twists can give different inner products on a single complex vector space.
The determinant of the Gram matrix in a fixed basis differs from the squared norm
determinant of the lift by a factor depending only on the basis. The common factor
cancels when comparing a twisted lift with the untwisted lift, even when their targets
are different inner product spaces.

The resulting height comparison is the factorization step of
`New.TwistedLattice.covolume_add_index_nonneg` in lsernau/grh-lean (`72fead1`,
`grh/src/New/Reduction/Lattices/TwistedLattice.lean`).
-/

public section

namespace TauCeti.PrimePadicIso.HeightLe

open Module

/-- Transfer a height bound for scaled Gram determinants of twists to the constant Gram
determinant of the untwisted lift. The height of the inverse scale is paid `n` times, and
the height of the ratio of squared norm determinants is paid once. Only the twisted lifts
must be injective, and their codomains need not be finite dimensional. -/
theorem det_gram_of_twists {β V W : Type*} {W' : PrimePadicIso → Type*}
    [Fintype β] [DecidableEq β] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [∀ p, NormedAddCommGroup (W' p)] [∀ p, InnerProductSpace ℂ (W' p)]
    {b : Basis β ℂ V} {f : V →ₗ[ℂ] W} {g : ∀ p, V →ₗ[ℂ] W' p}
    {c : PrimePadicIso → ℂˣ} {n : ℕ} {D B R : ℝ}
    (hGram : HeightLe (fun p ↦ (c p : ℂ) ^ n * (Matrix.gram ℂ (g p ∘ b)).det) D)
    (hScale : HeightLe (fun p ↦ (c p : ℂ)⁻¹) B)
    (hRatio : letI : FiniteDimensional ℂ V := b.finiteDimensional_of_finite
      HeightLe (fun p ↦ (f.normDet : ℂ) ^ 2 / ((g p).normDet : ℂ) ^ 2) R)
    (hg : ∀ p, Function.Injective (g p)) :
    HeightLe (fun _ ↦ (Matrix.gram ℂ (f ∘ b)).det) (D + n * B + R) := by
  let : FiniteDimensional ℂ V := b.finiteDimensional_of_finite
  have h := (hGram.mul (hScale.pow n)).mul hRatio
  convert h using 1
  funext p
  let o := EuclideanSpace.basisFun β ℂ
  let e := o.toBasis.equiv b (Equiv.refl β)
  -- Present the given basis as the image of an orthonormal basis under one common map.
  have he (i : β) : e (o i) = b i := by
    simp [e, ← OrthonormalBasis.coe_toBasis, Basis.equiv_apply]
  have hf := (f ∘ₗ e.toLinearMap).normDet_sq_eq_det_gram o
  have hgp := (g p ∘ₗ e.toLinearMap).normDet_sq_eq_det_gram o
  have hcast (x : ℝ) : (RCLike.ofReal x : ℂ) = Complex.ofReal x := rfl
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, he, hcast,
    LinearMap.normDet_comp_of_finrank_eq _ _ e.finrank_eq] at hf hgp
  have hg₀ : ((g p).normDet : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (((g p).normDet_ne_zero_tfae.out 5 1).mp (hg p))
  simp only [Pi.mul_apply, Pi.pow_apply, Function.comp_def, ← hf, ← hgp, inv_pow]
  push_cast
  field_simp [Units.ne_zero (c p), hg₀]

end TauCeti.PrimePadicIso.HeightLe
