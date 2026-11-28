/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RepresentationTheory.Intertwining
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Split rank-two representations

When a representation `ρ` over a field `k` is equivalent to a product `ρ₁.prod ρ₂` of two
one-dimensional representations, each `g` acts in those coordinates by scalar multiplication by
`det (ρ₁ g)` and `det (ρ₂ g)` (`Representation.Equiv.apply_eq_prod_det_smul_of_finrank_eq_one`).
Consequently, `ρ g` cannot have `μ` as an eigenvalue unless one of the two determinants equals `μ`
(`Representation.Equiv.not_hasEigenvalue_of_prod_finrank_eq_one_of_det_ne`).

## Main results

* `Representation.Equiv.apply_eq_prod_det_smul_of_finrank_eq_one`: coordinate action by factor
  determinants for a representation equivalent to a product of two lines.
* `Representation.Equiv.not_hasEigenvalue_of_prod_finrank_eq_one_of_det_ne`: eigenvalue exclusion
  when neither factor has determinant `μ`.
-/

public section

namespace Representation

/-- If a representation over a field `k` is equivalent to a product of two one-dimensional
representations `ρ₁` and `ρ₂`, then the equivalence transports `ρ g` to scalar multiplication by
`det (ρ₁ g)` and `det (ρ₂ g)` on the two factors. -/
theorem Equiv.apply_eq_prod_det_smul_of_finrank_eq_one
    {k G W₀ W₁ W₂ : Type*} [Field k] [Monoid G] [AddCommGroup W₀] [Module k W₀]
    [AddCommGroup W₁] [Module k W₁] [AddCommGroup W₂] [Module k W₂]
    {ρ : Representation k G W₀} {ρ₁ : Representation k G W₁} {ρ₂ : Representation k G W₂}
    (e : ρ.Equiv (ρ₁.prod ρ₂))
    (hW₁ : Module.finrank k W₁ = 1) (hW₂ : Module.finrank k W₂ = 1)
    (g : G) (v : W₀) :
    e (ρ g v) = (LinearMap.det (ρ₁ g) • (e v).1, LinearMap.det (ρ₂ g) • (e v).2) := by
  have : FiniteDimensional k W₁ := Module.finite_of_finrank_pos (by omega)
  have : FiniteDimensional k W₂ := Module.finite_of_finrank_pos (by omega)
  have h := LinearMap.congr_fun (e.isIntertwining' g) v
  exact Prod.ext
    (by simpa [LinearMap.apply_eq_det_smul_of_finrank_eq_one hW₁] using congrArg Prod.fst h)
    (by simpa [LinearMap.apply_eq_det_smul_of_finrank_eq_one hW₂] using congrArg Prod.snd h)

/-- If a representation over a field `k` is equivalent to a product of two one-dimensional
representations `ρ₁` and `ρ₂`, and neither `det (ρ₁ g)` nor `det (ρ₂ g)` equals `μ`, then `ρ g`
does not have `μ` as an eigenvalue. -/
theorem Equiv.not_hasEigenvalue_of_prod_finrank_eq_one_of_det_ne
    {k G W₀ W₁ W₂ : Type*} [Field k] [Monoid G] [AddCommGroup W₀] [Module k W₀]
    [AddCommGroup W₁] [Module k W₁] [AddCommGroup W₂] [Module k W₂]
    {ρ : Representation k G W₀} {ρ₁ : Representation k G W₁} {ρ₂ : Representation k G W₂}
    (e : ρ.Equiv (ρ₁.prod ρ₂))
    (hW₁ : Module.finrank k W₁ = 1) (hW₂ : Module.finrank k W₂ = 1)
    {g : G} {μ : k} (hc₁ : LinearMap.det (ρ₁ g) ≠ μ) (hc₂ : LinearMap.det (ρ₂ g) ≠ μ) :
    ¬ Module.End.HasEigenvalue (ρ g) μ := by
  intro hev
  obtain ⟨v, hv, hv0⟩ := hev.exists_hasEigenvector
  have hv_fix : ρ g v = μ • v := by simpa using Module.End.mem_eigenspace_iff.mp hv
  have hpair : (LinearMap.det (ρ₁ g) • (e v).1, LinearMap.det (ρ₂ g) • (e v).2) = μ • e v := by
    calc
      (LinearMap.det (ρ₁ g) • (e v).1, LinearMap.det (ρ₂ g) • (e v).2)
        = e (ρ g v) := (e.apply_eq_prod_det_smul_of_finrank_eq_one hW₁ hW₂ g v).symm
      _ = μ • e v := by rw [hv_fix, map_smul]
  have h1 : (e v).1 = 0 := by
    by_contra hnz
    exact hc₁ (smul_left_injective k hnz (by simpa using congrArg Prod.fst hpair))
  have h2 : (e v).2 = 0 := by
    by_contra hnz
    exact hc₂ (smul_left_injective k hnz (by simpa using congrArg Prod.snd hpair))
  exact hv0 (e.injective ((Prod.ext h1 h2).trans (map_zero e).symm))

end Representation
