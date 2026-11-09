/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Unitary.Adjoint
public import TauCeti.Algebra.Coalgebra.Subcomodule.InnerProduct
public import TauCeti.Algebra.Coalgebra.Subcomodule.Comap
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Subcomodules of finite unitary comodules

A subcomodule of a finite-dimensional unitary Hopf comodule inherits unitarity, and its
orthogonal complement is again a subcomodule. Consequently finite unitary comodules are
completely reducible. These are the splitting results used to decompose finite unitary
coefficient spaces into irreducibles, without any norm on the coefficient Hopf algebra.

The Hopf hypothesis is important: an isometric coefficient matrix has a two-sided inverse
provided by the antipode, so it is unitary even over a noncommutative coefficient algebra.

## References

* A. Klimyk and K. Schmüdgen, *Quantum Groups and Their Representations*, Springer, 1997,
  Section 1.3.
-/

public section

open Module
open scoped Matrix

namespace TauCeti.Comodule

variable {𝕜 A M N : Type*} [RCLike 𝕜] [Semiring A] [StarRing A]
  [HopfAlgebra 𝕜 A] [StarModule 𝕜 A]
  [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [FiniteDimensional 𝕜 M]
  [NormedAddCommGroup N] [InnerProductSpace 𝕜 N] [FiniteDimensional 𝕜 N]
  [Comodule 𝕜 A M] [Comodule 𝕜 A N]

/-- An isometric intertwiner into a finite unitary Hopf comodule makes its source unitary. -/
theorem IsUnitary.of_isometry (hN : IsUnitary 𝕜 A N) (f : Hom 𝕜 A M N)
    (hf : Isometry f) : IsUnitary 𝕜 A M := by
  classical
  let b := stdOrthonormalBasis 𝕜 M
  let c := stdOrthonormalBasis 𝕜 N
  let T := (LinearMap.toMatrix b.toBasis c.toBasis f.toLinearMap).map (algebraMap 𝕜 A)
  let u := coefficientMatrix (C := A) b.toBasis
  let v := coefficientMatrix (C := A) c.toBasis
  have hT : Tᴴ * T = 1 := by
    let i : M →ₗᵢ[𝕜] N :=
      { f.toLinearMap with norm_map' := (AddMonoidHomClass.isometry_iff_norm f).mp hf }
    have hi : f.toLinearMap.adjoint ∘ₗ f.toLinearMap = LinearMap.id :=
      i.adjoint_comp_self'
    rw [← Matrix.conjTranspose_map _ algebraMap_star_comm, ← LinearMap.toMatrix_adjoint b c,
      ← Matrix.map_mul, ← LinearMap.toMatrix_comp, hi, LinearMap.toMatrix_id,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hfv : v * T = T * u := f.coefficientMatrix_mul_toMatrix b.toBasis c.toBasis
  have hleft : uᴴ * u = 1 := by
    calc
      uᴴ * u = uᴴ * (Tᴴ * T) * u := by rw [hT, Matrix.mul_one]
      _ = (T * u)ᴴ * (T * u) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (v * T)ᴴ * (v * T) := by rw [hfv]
      _ = 1 := by
        have hv := (hN.coefficientMatrix_mem_unitary c).1
        simp only [Matrix.star_eq_conjTranspose] at hv
        calc
          (v * T)ᴴ * (v * T) = Tᴴ * (vᴴ * v) * T := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = 1 := by rw [hv, Matrix.mul_one, hT]
  have hS : uᴴ = u.map (HopfAlgebra.antipode 𝕜) :=
    left_inv_eq_right_inv hleft (coefficientMatrix_mul_map_antipode b.toBasis)
  exact b.isUnitary_comodule_iff_map_antipode_eq_conjTranspose.mpr hS.symm

end TauCeti.Comodule

namespace TauCeti.Subcomodule

variable {𝕜 A M : Type*} [RCLike 𝕜] [Ring A] [StarRing A]
  [HopfAlgebra 𝕜 A] [StarModule 𝕜 A]
  [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [FiniteDimensional 𝕜 M]
  [Comodule 𝕜 A M]

/-- Every subcomodule of a finite unitary Hopf comodule is unitary for the restricted
inner product. -/
theorem isUnitary (W : Subcomodule 𝕜 A M) (hM : Comodule.IsUnitary 𝕜 A M) :
    Comodule.IsUnitary 𝕜 A W := by
  apply hM.of_isometry W.subtype
  simpa only [← Comodule.Hom.coe_toLinearMap, subtype_toLinearMap] using W.isometry_subtype

/-- The orthogonal complement of a subcomodule of a finite unitary Hopf comodule,
with its inherited coaction. -/
noncomputable def unitaryOrthogonal (W : Subcomodule 𝕜 A M) (hM : Comodule.IsUnitary 𝕜 A M) :
    Subcomodule 𝕜 A M :=
  (W.subtype.adjoint (W.isUnitary hM) hM).ker

/-- The underlying submodule of the orthogonal subcomodule is the usual orthogonal
complement. -/
@[simp]
theorem unitaryOrthogonal_toSubmodule (W : Subcomodule 𝕜 A M)
    (hM : Comodule.IsUnitary 𝕜 A M) :
    (W.unitaryOrthogonal hM).toSubmodule = W.toSubmoduleᗮ := by
  rw [unitaryOrthogonal, Comodule.Hom.ker_toSubmodule, Comodule.Hom.adjoint_toLinearMap,
    ← LinearMap.orthogonal_range, range_subtype_toLinearMap]

/-- Membership in the orthogonal subcomodule is orthogonality to every vector of the
original subcomodule. -/
@[simp]
theorem mem_unitaryOrthogonal (W : Subcomodule 𝕜 A M) (hM : Comodule.IsUnitary 𝕜 A M)
    (x : M) : x ∈ W.unitaryOrthogonal hM ↔ ∀ w ∈ W, inner 𝕜 w x = 0 := by
  rw [← mem_toSubmodule, unitaryOrthogonal_toSubmodule, Submodule.mem_orthogonal]
  simp only [mem_toSubmodule]

/-- A subcomodule and its orthogonal complement are complementary as submodules. -/
theorem isCompl_unitaryOrthogonal (W : Subcomodule 𝕜 A M)
    (hM : Comodule.IsUnitary 𝕜 A M) :
    IsCompl W.toSubmodule (W.unitaryOrthogonal hM).toSubmodule := by
  rw [unitaryOrthogonal_toSubmodule]
  exact W.toSubmodule.isCompl_orthogonal

/-- Taking orthogonal complements twice recovers the original subcomodule. -/
@[simp]
theorem unitaryOrthogonal_unitaryOrthogonal (W : Subcomodule 𝕜 A M)
    (hM : Comodule.IsUnitary 𝕜 A M) :
    (W.unitaryOrthogonal hM).unitaryOrthogonal hM = W := by
  ext x
  simp only [← mem_toSubmodule, unitaryOrthogonal_toSubmodule, Submodule.orthogonal_orthogonal]

end TauCeti.Subcomodule

namespace TauCeti.Comodule

variable {𝕜 A M : Type*} [RCLike 𝕜] [Ring A] [StarRing A]
  [HopfAlgebra 𝕜 A] [StarModule 𝕜 A]
  [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [FiniteDimensional 𝕜 M]
  [Comodule 𝕜 A M]

/-- Finite-dimensional unitary Hopf comodules are completely reducible. -/
theorem IsUnitary.isCompletelyReducible (hM : IsUnitary 𝕜 A M) :
    IsCompletelyReducible 𝕜 A M :=
  IsCompletelyReducible.of_exists_isCompl fun W =>
    ⟨W.unitaryOrthogonal hM, W.isCompl_unitaryOrthogonal hM⟩

end TauCeti.Comodule
