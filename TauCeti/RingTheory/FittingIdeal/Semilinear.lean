/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FittingIdeal.Basic

/-!
# Fitting ideals and semilinear equivalences

Let `σ : R →+* S` be an isomorphism of commutative rings, and let `e : M ≃ₛₗ[σ] M'` be a
`σ`-semilinear equivalence from an `R`-module to an `S`-module. Transport of structure along
`(σ, e)` carries every invariant of `M` to the corresponding invariant of `M'`; for the Fitting
ideals this reads `Fitt_k(M') = σ(Fitt_k(M))`.

The case of interest is `S = R` with `σ` an automorphism of `R`, for instance the Frobenius of a
perfect ring of characteristic `p`. A module carrying a `σ`-semilinear automorphism then has
Fitting ideals stable under `σ`, which for Frobenius forces them to be idempotent
(`TauCeti.projective_of_addEquiv_iterateFrobenius`).

The minors of a submodule are transported by pulling back linear functionals: if `f` is an
`S`-linear functional on `F'`, then `σ⁻¹ ∘ f ∘ e` is an `R`-linear functional on `F`, and the
determinants built from these functionals differ by `σ`.

## Main results

* `Submodule.minorsIdeal_map_semilinear_le`: the minors of the image of a submodule under a
  `σ`-semilinear map lie in the image under `σ` of its minors.
* `Submodule.minorsIdeal_map_semilinearEquiv`: equality for a `σ`-semilinear equivalence.
* `TauCeti.fittingIdeal_eq_map_of_semilinearEquiv`: `Fitt_k(M') = σ(Fitt_k(M))` for a
  `σ`-semilinear equivalence `M ≃ₛₗ[σ] M'`.
-/

public section

noncomputable section

open Function LinearMap Module

namespace Submodule

variable {R S F F' : Type*} [CommRing R] [CommRing S] [AddCommGroup F] [Module R F]
  [AddCommGroup F'] [Module S F'] {σ : R →+* S} {σ' : S →+* R}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

/-- The minors of the image of a submodule under a `σ`-semilinear map lie in the image under `σ`
of its minors. -/
theorem minorsIdeal_map_semilinear_le (e : F →ₛₗ[σ] F') (N : Submodule R F) (p : ℕ) :
    (N.map e).minorsIdeal p ≤ (N.minorsIdeal p).map σ := by
  refine minorsIdeal_le_iff.2 fun f v hv ↦ ?_
  choose w hw hwv using fun i ↦ mem_map.1 (hv i)
  obtain rfl : v = fun i ↦ e (w i) := funext fun i ↦ (hwv i).symm
  -- Pull back each functional `f j` to the `R`-linear functional `σ' ∘ f j ∘ e` on `F`.
  let g : Fin p → Dual R F := fun j ↦
    (RingHom.toSemilinearMap σ' : S →ₛₗ[σ'] R) ∘ₛₗ f j ∘ₛₗ e
  have hdet : σ (Matrix.of fun i j ↦ g j (w i)).det = (Matrix.of fun i j ↦ f j (e (w i))).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [g]
  rw [← hdet]
  exact Ideal.mem_map_of_mem σ (det_mem_minorsIdeal g hw)

/-- **Minors are transported along semilinear equivalences**: if `e : F ≃ₛₗ[σ] F'` is
semilinear over a ring isomorphism `σ`, the minors of `e(N)` are the image under `σ` of the
minors of `N`. -/
@[simp]
theorem minorsIdeal_map_semilinearEquiv (e : F ≃ₛₗ[σ] F') (N : Submodule R F) (p : ℕ) :
    (N.map (e : F →ₛₗ[σ] F')).minorsIdeal p = (N.minorsIdeal p).map σ := by
  refine le_antisymm (minorsIdeal_map_semilinear_le (e : F →ₛₗ[σ] F') N p) ?_
  -- The reverse inclusion is the first one for `e.symm`, transported back along `σ`.
  have h := minorsIdeal_map_semilinear_le (e.symm : F' →ₛₗ[σ'] F)
    (N.map (e : F →ₛₗ[σ] F')) p
  have hN : (N.map (e : F →ₛₗ[σ] F')).map (e.symm : F' →ₛₗ[σ'] F) = N := by
    ext x
    simp
  rw [hN] at h
  calc (N.minorsIdeal p).map σ
      ≤ (((N.map (e : F →ₛₗ[σ] F')).minorsIdeal p).map σ').map σ := Ideal.map_mono h
    _ = (N.map (e : F →ₛₗ[σ] F')).minorsIdeal p := by
      rw [Ideal.map_map, RingHomInvPair.comp_eq₂, Ideal.map_id]

end Submodule

namespace TauCeti

variable {R S M M' : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [AddCommGroup M'] [Module S M'] [Module.Finite S M']
  {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

/-- **Fitting ideals are transported along semilinear equivalences**: if `e : M ≃ₛₗ[σ] M'` is
semilinear over a ring isomorphism `σ`, then `Fitt_k(M') = σ(Fitt_k(M))`. -/
theorem fittingIdeal_eq_map_of_semilinearEquiv (e : M ≃ₛₗ[σ] M') (k : ℕ) :
    fittingIdeal S M' k = (fittingIdeal R M k).map σ := by
  nontriviality S
  have := σ.domain_nontrivial
  obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' R M
  -- Apply `σ` coordinatewise to transport the presentation `φ` of `M` to a presentation `ψ`
  -- of `M'`, whose relations are the image of those of `φ`.
  let Φ : (Fin n → R) ≃ₛₗ[σ] (Fin n → S) :=
    { toFun x i := σ (x i)
      invFun y i := σ' (y i)
      map_add' x y := funext fun i ↦ map_add σ _ _
      map_smul' a x := funext fun i ↦ map_mul σ _ _
      left_inv x := funext fun i ↦ RingHomInvPair.comp_apply_eq (σ := σ) (σ' := σ')
      right_inv y := funext fun i ↦ RingHomInvPair.comp_apply_eq₂ (σ := σ) (σ' := σ') }
  let ψ : (Fin n → S) →ₗ[S] M' :=
    (e : M →ₛₗ[σ] M') ∘ₛₗ φ ∘ₛₗ (Φ.symm : (Fin n → S) →ₛₗ[σ'] (Fin n → R))
  have hψ : Surjective ψ := e.surjective.comp (hφ.comp Φ.symm.surjective)
  have hker : ker ψ = (ker φ).map (Φ : (Fin n → R) →ₛₗ[σ] (Fin n → S)) := by
    ext y
    simp [ψ, Submodule.mem_map_equiv]
  rw [fittingIdeal_eq_minorsIdeal_ker hψ, fittingIdeal_eq_minorsIdeal_ker hφ, hker,
    Submodule.minorsIdeal_map_semilinearEquiv, finrank_fin_fun, finrank_fin_fun]

end TauCeti
