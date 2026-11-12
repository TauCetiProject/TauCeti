/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Complex.Conjugate
public import TauCeti.LinearAlgebra.TotallyReal.Complex

/-!
# Totally real subspaces of the conjugate

Totally real subspaces only see the real structure and the multiplication by `i` up to sign, so
a real subspace of a complex module `V` is (maximal) totally real exactly when it is so in
`TauCeti.Conjugate V`. The conjugation of a maximal totally real subspace, read as a
complex-linear map `V → Conjugate V`, agrees with the identity exactly on that subspace.

## Main declarations

* `LinearMap.toConjugate_conjugationOfMaximalTotallyReal_eq_iff`: the complex-linear map
  `V → Conjugate V` attached to the conjugation of a maximal totally real subspace agrees with the
  identity exactly on that subspace.
* `Submodule.isTotallyReal_conjugate_iff`, `Submodule.isMaximalTotallyReal_conjugate_iff`: a real
  subspace is (maximal) totally real in `V` exactly when it is so in `Conjugate V`.
-/

public section

open TauCeti TauCeti.Conjugate

namespace LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The complex-linear map `V → Conjugate V` attached to the conjugation of a maximal totally real
subspace agrees with the identity exactly on that subspace. This is the gluing datum identifying
a fibre with its conjugate along a totally real boundary condition. -/
theorem toConjugate_conjugationOfMaximalTotallyReal_eq_iff [Module ℝ V] [IsScalarTower ℝ ℂ V]
    {U : Type*} [AddCommGroup U] [Module ℝ U] (f : U →ₗ[ℝ] V) (hf : Function.Injective f)
    (hmax : IsMaximalTotallyReal ((LinearMap.lsmul ℂ V Complex.I).restrictScalars ℝ) f.range)
    (v : V) : toConjugate (f.conjugationOfMaximalTotallyReal hf hmax) v = toConj v ↔
      v ∈ f.range := by
  rw [toConjugate_apply, toConj_inj, conjugationOfMaximalTotallyReal_eq_self_iff]

end LinearMap

namespace Submodule

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

variable [Module ℂ V] [IsScalarTower ℝ ℂ V]

/-- Multiplication by `i` on the conjugate is multiplication by `-i` on `V`, so it has the same
images of real subspaces. -/
theorem conjugate_map_lsmul_I (L : Submodule ℝ V) :
    L.conjugate.map ((LinearMap.lsmul ℂ (Conjugate V) Complex.I).restrictScalars ℝ) =
      (L.map ((LinearMap.lsmul ℂ V Complex.I).restrictScalars ℝ)).conjugate := by
  have h : (LinearMap.lsmul ℂ (Conjugate V) Complex.I).restrictScalars ℝ ∘ₗ
      (toConjₗ' : V ≃ₗ[ℝ] Conjugate V).toLinearMap =
        (toConjₗ' : V ≃ₗ[ℝ] Conjugate V).toLinearMap ∘ₗ
          (-(LinearMap.lsmul ℂ V Complex.I).restrictScalars ℝ) := by
    ext v
    simp [← neg_smul]
  rw [← map_toConjₗ', ← map_toConjₗ', ← Submodule.map_comp, h, Submodule.map_comp,
    Submodule.map_neg]

/-- A real subspace is totally real in `V` exactly when it is totally real in `Conjugate V`. -/
theorem isTotallyReal_conjugate_iff {L : Submodule ℝ V} :
    IsTotallyReal ((LinearMap.lsmul ℂ (Conjugate V) Complex.I).restrictScalars ℝ) L.conjugate ↔
      IsTotallyReal ((LinearMap.lsmul ℂ V Complex.I).restrictScalars ℝ) L := by
  rw [isTotallyReal_iff, isTotallyReal_iff, conjugate_map_lsmul_I]
  rw [← map_toConjₗ', ← map_toConjₗ']
  exact disjoint_map_orderIso_iff (Submodule.orderIsoMapComap toConjₗ')

/-- A real subspace is maximal totally real in `V` exactly when it is maximal totally real in
`Conjugate V`. -/
theorem isMaximalTotallyReal_conjugate_iff {L : Submodule ℝ V} :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ (Conjugate V) Complex.I).restrictScalars ℝ)
        L.conjugate ↔
      IsMaximalTotallyReal ((LinearMap.lsmul ℂ V Complex.I).restrictScalars ℝ) L := by
  rw [isMaximalTotallyReal_iff, isMaximalTotallyReal_iff, conjugate_map_lsmul_I]
  rw [← map_toConjₗ', ← map_toConjₗ']
  exact ((Submodule.orderIsoMapComap toConjₗ').isCompl_iff).symm

end Submodule
