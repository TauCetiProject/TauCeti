/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.ResidueCocycle
public import TauCeti.Algebra.Lie.Current.Topology

/-!
# Coordinate changes on formal currents

A formal coordinate `φ = a X + ⋯` acts on `K⸨X⸩ ⊗[K] L` by substituting `φ` in the
scalar series. This is a continuous Lie automorphism, preserves every order submodule,
and preserves the residue cocycle of every invariant symmetric form. Thus the cocycle
defining an affine central extension is independent of the formal parameter.

The construction uses Mathlib's `LieAlgebra.ExtendScalars.map` and the Laurent-series
substitution equivalence. Coordinates multiply by composition of parameters, so the
induced automorphisms reverse products: substitution by `φ * ψ` first substitutes `φ`
and then `ψ`. The inverse is substitution by the inverse coordinate.

No finite-dimensionality or characteristic assumption is needed.

## References

* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., Chapter 7, for the
  coordinate-invariant residue cocycle of current algebras.
-/

public section

noncomputable section

open scoped TensorProduct LaurentSeries
open Topology

namespace TauCeti.CurrentAlgebra

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

-- Use the same coefficientwise scalar action as the current-algebra tensor product.
attribute [local instance 1100] HahnSeries.instAlgebra

/-- Substitution by a formal coordinate, as a Lie automorphism of formal currents. -/
def substLieEquiv (φ : FormalCoordinate K) : currentAlgebra K L ≃ₗ⁅K⁆ currentAlgebra K L :=
  -- Rebundle the scalar equivalence for the coefficientwise algebra instance used by currents.
  let er : K⸨X⸩ ≃+* K⸨X⸩ := by
    letI : Algebra K K⸨X⸩ := HahnSeries.powerSeriesAlgebra ℤ K
    exact (LaurentSeries.substAlgEquiv φ).toRingEquiv
  let e : K⸨X⸩ ≃ₐ[K] K⸨X⸩ :=
    { er with
      commutes' := fun a ↦ by
        simp only [HahnSeries.algebraMap_apply, Algebra.algebraMap_self_apply]
        let : Algebra K K⸨X⸩ := HahnSeries.powerSeriesAlgebra ℤ K
        simpa only [er, _root_.LaurentSeries.algebraMap_apply] using
          (LaurentSeries.substAlgEquiv φ).commutes' a }
  { _root_.LieAlgebra.ExtendScalars.map e.toAlgHom
      (LieHom.id : L →ₗ⁅K⁆ L),
    TensorProduct.congr e.toLinearEquiv
      (LinearEquiv.refl K L) with }

/-- Coordinate changes substitute in the scalar factor of a pure tensor. -/
@[simp]
theorem substLieEquiv_tmul (φ : FormalCoordinate K) (f : K⸨X⸩) (x : L) :
    substLieEquiv (L := L) φ (f ⊗ₜ x) = LaurentSeries.substAlgEquiv φ f ⊗ₜ x :=
  (rfl)

/-- Substitution reverses composition of formal parameters. -/
theorem substLieEquiv_mul_apply (φ ψ : FormalCoordinate K) (u : currentAlgebra K L) :
    substLieEquiv (φ * ψ) u = substLieEquiv ψ (substLieEquiv φ u) := by
  induction u using TensorProduct.inductionOn with
  | tmul f x => simp [LaurentSeries.substAlgEquiv_mul, AlgEquiv.mul_apply]
  | add u v hu hv => simp [hu, hv]

@[simp]
theorem substLieEquiv_one (u : currentAlgebra K L) :
    substLieEquiv (1 : FormalCoordinate K) u = u := by
  induction u using TensorProduct.inductionOn with
  | tmul f x => simp
  | add u v hu hv => simp [hu, hv]

/-- The inverse coordinate induces the inverse current automorphism. -/
@[simp]
theorem substLieEquiv_symm (φ : FormalCoordinate K) :
    (substLieEquiv (L := L) φ).symm = substLieEquiv φ⁻¹ := by
  apply LieEquiv.ext
  intro u
  apply (substLieEquiv φ).injective
  simp only [LieEquiv.coe_toLieHom]
  rw [LieEquiv.apply_symm_apply, ← substLieEquiv_mul_apply, inv_mul_cancel, substLieEquiv_one]

/-- Coordinate changes preserve every lower order bound. -/
theorem substLieEquiv_mem_orderSubmodule (φ : FormalCoordinate K) {N : ℤ}
    {u : currentAlgebra K L} (hu : u ∈ orderSubmodule K L N) :
    substLieEquiv φ u ∈ orderSubmodule K L N := by
  rw [orderSubmodule_def] at hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨f, x, hf, rfl⟩ := hu
    rw [substLieEquiv_tmul]
    apply tmul_mem_orderSubmodule
    simpa only [LaurentSeries.coe_substAlgEquiv, LaurentSeries.orderTop_substAlgHom,
      FormalCoordinate.order_toPowerSeries, ENat.toNat_one, one_nsmul] using hf
  | zero => simp
  | add u v _ _ hu hv => simpa only [map_add] using add_mem hu hv
  | smul a u _ hu => simpa only [map_smul] using (orderSubmodule K L N).smul_mem a hu

/-- Membership in each order submodule is invariant under coordinate changes. -/
@[simp]
theorem substLieEquiv_mem_orderSubmodule_iff (φ : FormalCoordinate K) (N : ℤ)
    (u : currentAlgebra K L) :
    substLieEquiv φ u ∈ orderSubmodule K L N ↔ u ∈ orderSubmodule K L N := by
  refine ⟨fun hu ↦ ?_, substLieEquiv_mem_orderSubmodule φ⟩
  have h := substLieEquiv_mem_orderSubmodule φ⁻¹ hu
  rwa [← substLieEquiv_symm, LieEquiv.symm_apply_apply] at h

/-- Coordinate changes are continuous in the order topology. -/
theorem continuous_substLieEquiv (φ : FormalCoordinate K) :
    Continuous (substLieEquiv (L := L) φ) := by
  refine continuous_of_continuousAt_zero (substLieEquiv (L := L) φ).toLinearEquiv.toAddEquiv ?_
  rw [ContinuousAt, map_zero,
    (hasBasis_nhds_zero K L).tendsto_iff (hasBasis_nhds_zero K L)]
  exact fun N _ ↦ ⟨N, trivial, fun u hu ↦ substLieEquiv_mem_orderSubmodule φ hu⟩

/-- The residue pairing on formal currents is invariant under coordinate changes, for every
bilinear form on the coefficient Lie algebra. -/
@[simp]
theorem residuePairing_substLieEquiv (φ : FormalCoordinate K) (Φ : LinearMap.BilinForm K L)
    (u v : currentAlgebra K L) :
    residuePairing K L Φ (substLieEquiv φ u) (substLieEquiv φ v) =
      residuePairing K L Φ u v := by
  induction u using TensorProduct.inductionOn with
  | tmul f x =>
    induction v using TensorProduct.inductionOn with
    | tmul g y => simp
    | add v w hv hw => simp only [map_add, hv, hw]
  | add u w hu hw => simp only [map_add, LinearMap.add_apply, hu, hw]

end TauCeti.CurrentAlgebra
