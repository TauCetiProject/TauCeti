/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.Isometry

/-!
# Classification of symmetric forms when every scalar is a square

A nondegenerate symmetric form over a field in which every element is a square is determined
by its dimension and whether it is alternating. The alternating case uses symplectic bases;
the other case uses orthonormal bases. In particular this applies over finite fields of
characteristic two and separates the two kinds of symmetric pairing on elementary abelian
two-groups.

## References

* J. Milnor, D. Husemoller, *Symmetric Bilinear Forms*, Chapter I.
-/

public section

namespace LinearMap.BilinForm

open Module

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {B : LinearMap.BilinForm K V} {C : LinearMap.BilinForm K W}

/-- Over a field in which every scalar is a square, nondegenerate symmetric forms of the
same dimension and the same alternation type are equivalent. -/
theorem IsSymm.equivalent_of_finrank_eq_of_isAlt_iff (hB : B.IsSymm) (hC : C.IsSymm)
    (hsq : ∀ a : K, IsSquare a) (hndB : B.Nondegenerate) (hndC : C.Nondegenerate)
    (hdim : finrank K V = finrank K W) (halt : B.IsAlt ↔ C.IsAlt) : B.Equivalent C := by
  by_cases hb : B.IsAlt
  · obtain ⟨m, b, hbm⟩ := hb.exists_basis_toMatrix_eq_J hndB
    obtain ⟨n, c, hcn⟩ := (halt.mp hb).exists_basis_toMatrix_eq_J hndC
    have hmn : m = n := by
      rw [finrank_eq_card_basis b, finrank_eq_card_basis c] at hdim
      simp only [Fintype.card_sum, Fintype.card_fin] at hdim
      omega
    subst n
    exact ⟨b.isometryEquivOfToMatrixEq c (hbm.trans hcn.symm)⟩
  · exact hB.equivalent_of_finrank_eq hsq hndB (fun h ↦ (hb h).elim) hC hndC
      (fun h ↦ (hb (halt.mpr h)).elim) hdim

end LinearMap.BilinForm
