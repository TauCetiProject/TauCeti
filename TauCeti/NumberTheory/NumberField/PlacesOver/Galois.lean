/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.AbsoluteValue.Action
public import TauCeti.NumberTheory.NumberField.PlacesOver.FinitePlace

import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.NumberTheory.RamificationInertia.Galois
import TauCeti.NumberTheory.NumberField.AutomorphismAction

/-!
# Conjugate absolute values over a finite place

Let `F / K` be a Galois extension of number fields and `v` a finite place of `K`. The Galois
group `F ≃ₐ[K] F` acts on the absolute values of `F` by `σ • w = w ∘ σ⁻¹`
(`AbsoluteValue.instMulActionAlgEquiv`), preserving those that lie over `v`. This file proves that
it permutes them transitively: any two absolute values of `F` lying over `v` are conjugate
(`NumberField.exists_smul_eq_of_liesOver_finitePlace`), so that they form a single orbit
(`NumberField.setOf_liesOver_finitePlace_eq_orbit`). This is the `AbsoluteValue.LiesOver` form
of the transitivity of the Galois group on the primes of `𝓞 F` over a prime of `𝓞 K`, Mathlib's
`Ideal.exists_smul_eq_of_isGaloisGroup`. The absolute values over `v` are in general real powers of
finite places of `F`, not finite places themselves, so the statement is not one about
`FinitePlace F`.

## Implementation notes

An absolute value `w` lying over `v = FinitePlace.mk 𝔭` is determined by its prime
`{y ∈ 𝓞 F | w y < 1}` (`NumberField.eq_of_liesOver_of_forall_apply_lt_one_iff`), and the prime of
`σ • w` is the image under `σ` of the prime of `w`. So it suffices to move one prime to the other,
and no equivariance of the finite places of `F` or of the adic valuations under `σ` is needed.

The same transitivity statement, along the same route through the primes `{y ∈ 𝓞 F | w y < 1}`, is
formalized in Ralf Stephan's `rwst/Subspace-Theorems` at
`09835cb23557ae5ae0cf55a9c4ab9055f5d60338`, file `DiophantineApproximation/ConjugatePlaces.lean`
(Apache 2.0).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.3, Corollaries 1.3.2 and 1.3.5.
-/

public section

open AbsoluteValue IsDedekindDomain Pointwise

namespace NumberField

variable {K F : Type*} [Field K] [Field F] [NumberField K] [NumberField F] [Algebra K F]

/-- **Conjugate absolute values over a finite place.** Let `F / K` be a Galois extension of number
fields and `v` a finite place of `K`. Any two absolute values of `F` lying over `v` are conjugate
under `F ≃ₐ[K] F`. -/
theorem exists_smul_eq_of_liesOver_finitePlace [IsGalois K F] (v : FinitePlace K)
    (w₁ w₂ : AbsoluteValue F ℝ) [w₁.LiesOver v.1] [w₂.LiesOver v.1] :
    ∃ σ : F ≃ₐ[K] F, σ • w₁ = w₂ := by
  obtain ⟨𝔭, rfl⟩ : ∃ 𝔭, FinitePlace.mk 𝔭 = v := ⟨_, v.mk_maximalIdeal⟩
  obtain ⟨𝔓₁, h𝔓₁, hw₁⟩ := exists_liesOver_forall_mem_iff_apply_lt_one (𝔭 := 𝔭) (w := w₁)
  obtain ⟨𝔓₂, h𝔓₂, hw₂⟩ := exists_liesOver_forall_mem_iff_apply_lt_one (𝔭 := 𝔭) (w := w₂)
  obtain ⟨σ, hσ⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup 𝔭.asIdeal 𝔓₁.asIdeal 𝔓₂.asIdeal (F ≃ₐ[K] F)
  refine ⟨σ, eq_of_liesOver_of_forall_apply_lt_one_iff (𝔭 := 𝔭) fun y ↦ ?_⟩
  -- Transport the prime of `w₁` to the prime of `w₂` along `σ`.
  rw [← hw₂, ← hσ, Ideal.mem_pointwise_smul_iff_inv_smul_mem, hw₁]
  -- The action of `σ⁻¹` on `𝓞 F` is the restriction of its action on `F`.
  simp only [AbsoluteValue.smul_apply, AlgEquiv.aut_inv, algebraMap_smul_eq_apply]

/-- Let `F / K` be a Galois extension of number fields and `v` a finite place of `K`. The absolute
values of `F` lying over `v` form a single orbit of `F ≃ₐ[K] F`. -/
theorem setOf_liesOver_finitePlace_eq_orbit [IsGalois K F] (v : FinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] :
    {w' : AbsoluteValue F ℝ | w'.LiesOver v.1} = MulAction.orbit (F ≃ₐ[K] F) w := by
  ext w'
  simp only [Set.mem_ofPred_eq, MulAction.mem_orbit_iff]
  refine ⟨fun _ ↦ exists_smul_eq_of_liesOver_finitePlace v w w', ?_⟩
  rintro ⟨σ, rfl⟩
  infer_instance

end NumberField
