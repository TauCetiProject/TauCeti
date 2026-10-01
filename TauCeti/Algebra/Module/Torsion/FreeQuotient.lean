/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import TauCeti.Algebra.Module.Torsion.Basic

/-!
# The free quotient of a module containing a lattice of finite index

Let `R` be a principal ideal domain and `M` an `R`-module. Suppose that a free module `R^ι` of
finite rank embeds into `M` with cokernel of finite exponent: some nonzero `r ∈ R` carries all of
`M` into the image. Then `M` modulo its torsion is free of rank `#ι`, that is
`M ⧸ torsion R M ≃ R^ι`. No finiteness of `M` is assumed: multiplication by `r` embeds
`M ⧸ torsion R M` into `R^ι`, which already makes it finitely generated.

This is how the rank of a module is computed from an explicit lattice of finite index, for
instance the rank `[L : ℚ_p] + 1` of the `p`-adic completion of the multiplicative group of a
`p`-adic field from the logarithm on its deep units.

## Main results

* `TauCeti.nonempty_quotient_torsion_linearEquiv_of_injective`: if `f : R^ι → M` is injective and
  `r • M ⊆ range f` for some `r ≠ 0`, then `M ⧸ torsion R M ≃ R^ι`.
-/

public section

namespace TauCeti

open _root_.Submodule

variable {R M ι : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M] [Finite ι]

/-- Over a principal ideal domain `R`, if an injective linear map `f : R^ι → M` has cokernel
killed by some nonzero `r ∈ R`, then `M` modulo its torsion is free on `ι`. -/
theorem nonempty_quotient_torsion_linearEquiv_of_injective {f : (ι → R) →ₗ[R] M}
    (hf : Function.Injective f) {r : R} (hr : r ≠ 0) (hrf : ∀ x, r • x ∈ LinearMap.range f) :
    Nonempty ((M ⧸ torsion R M) ≃ₗ[R] (ι → R)) := by
  -- `φ x = f⁻¹ (r • x)`; it kills the torsion of `M`, and `φ ∘ f = r • id`.
  let φ : M →ₗ[R] (ι → R) := (LinearEquiv.ofInjective f hf).symm.toLinearMap ∘ₗ
    (r • LinearMap.id).codRestrict (LinearMap.range f) hrf
  have hφ (x : M) : f (φ x) = r • x := by
    simp [φ]
  have hφf (y : ι → R) : φ (f y) = r • y := hf (by rw [hφ, map_smul])
  have hr0 : r ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hr
  have hT : torsion R M ≤ LinearMap.ker φ := by
    rintro x ⟨⟨s, hs⟩, hsx⟩
    rw [LinearMap.mem_ker]
    have : s • φ x = 0 := by
      apply hf
      rw [map_smul, hφ, map_zero, smul_comm, ← Submonoid.smul_def ⟨s, hs⟩, hsx, smul_zero]
    exact (smul_eq_zero.mp this).resolve_left (nonZeroDivisors.ne_zero hs)
  -- `φ` descends to an injection `M ⧸ torsion R M → R^ι`, so that quotient is finite free of
  -- rank at most `#ι`; `f` descends to an injection the other way.
  let h := (torsion R M).liftQ φ hT
  have hh : Function.Injective h := by
    refine (injective_iff_map_eq_zero h).mpr fun q hq ↦ ?_
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      rw [liftQ_apply] at hq
      rw [Quotient.mk_eq_zero]
      exact ⟨⟨r, hr0⟩, by rw [Submonoid.smul_def, ← hφ, hq, map_zero]⟩
  have hg : Function.Injective ((torsion R M).mkQ ∘ₗ f) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_comp, ker_mkQ, eq_bot_iff,
      ← isTorsionFree_iff_torsion_eq_bot.mp inferInstance]
    exact Submodule.comap_torsion_le_of_comp_eq_smul hr0 hφf
  have : Module.Finite R (M ⧸ torsion R M) := .of_injective h hh
  exact ⟨LinearEquiv.ofFinrankEq _ _ (le_antisymm (LinearMap.finrank_le_finrank_of_injective hh)
    (LinearMap.finrank_le_finrank_of_injective hg))⟩

end TauCeti
