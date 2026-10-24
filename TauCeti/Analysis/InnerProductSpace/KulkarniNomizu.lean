/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
public import TauCeti.LinearAlgebra.BilinearForm.KulkarniNomizu

/-!
# Contracting a Kulkarni–Nomizu product with the inner product

On a finite-dimensional real inner product space `W` of dimension `n`, contracting the first and
fourth arguments of the Kulkarni–Nomizu product `h ⊙ g` of a bilinear form `h` with the inner
product `g` gives

`∑ᵢ (h ⊙ g)(eᵢ, y, z, eᵢ) = (n - 2) h(y, z) + (tr_g h) g(y, z)`

for every orthonormal basis `(eᵢ)`. This is the Ricci-type contraction of `h ⊙ g`; it is the
identity that determines the Schouten tensor of a Riemannian metric as the unique bilinear form
`P` with `Ric = (n - 2) P + (tr_g P) g`, and that makes the Weyl tensor trace-free.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
-/

public section

open LinearMap (BilinForm)

namespace LinearMap.BilinForm

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- In an orthonormal basis, contracting the first and fourth arguments of the Kulkarni–Nomizu
product of `h` with the inner product gives `(n - 2) h + (tr h) g`. -/
theorem sum_kulkarniNomizu_innerₗ {ι : Type*} [Fintype ι] (h : BilinForm ℝ W)
    (b : OrthonormalBasis ι ℝ W) (y z : W) :
    ∑ j, kulkarniNomizu h (innerₗ W) (b j) y z (b j) =
      ((Module.finrank ℝ W : ℝ) - 2) * h y z + TauCeti.bilinFormTrace h * inner ℝ y z := by
  have hleft : ∑ j, h (b j) z * inner ℝ y (b j) = h y z := by
    conv_rhs => rw [← b.sum_repr' y]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, real_inner_comm y]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  have hright : ∑ j, h y (b j) * inner ℝ (b j) z = h y z := by
    conv_rhs => rw [← b.sum_repr' z]
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  have hdim : ∑ j, inner ℝ (b j) (b j) = (Module.finrank ℝ W : ℝ) := by
    simpa using (TauCeti.bilinFormTrace_eq_sum (innerₗ W) b).symm
  simp only [kulkarniNomizu_apply, innerₗ_apply_apply, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hleft, hright, hdim,
    ← TauCeti.bilinFormTrace_eq_sum h b]
  ring

end LinearMap.BilinForm
