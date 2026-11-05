/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Module

/-!
# Density for Lie modules with scalar commutant

For a finite completely reducible Lie module whose equivariant endomorphisms are scalars,
the enveloping algebra realizes every linear operator. In particular, this applies to
finite-dimensional irreducible modules over a field without requiring algebraic closure,
once the scalar-commutant condition is known.

The proof uses Mathlib's `Module.Finite.toModuleEnd_moduleEnd_surjective` and the Lie-module /
enveloping-module dictionary of `TauCeti.Algebra.Lie.UniversalEnveloping.Module`.

## References

* N. Jacobson, *Basic Algebra II*, Chapter 4 (the density theorem).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §20.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open Module

variable {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Finite K M] [ComplementedLattice (LieSubmodule K L M)]

/-- If the equivariant endomorphisms of a finite completely reducible Lie module are scalars,
its enveloping algebra acts as the full linear endomorphism algebra. -/
theorem representation_surjective_of_endomorphisms_eq_smul
    (hscalar : ∀ g : M →ₗ⁅K,L⁆ M, ∃ c : K, g = c • LieModuleHom.id) :
    Function.Surjective (representation K L M) := by
  let U := _root_.UniversalEnvelopingAlgebra K L
  let : Module U M := asModule K L M
  let : IsScalarTower K U M := isScalarTower_asModule K L M
  let : IsSemisimpleModule U M :=
    (complementedLattice_lieSubmodule_iff_isSemisimpleModule
      (asModule_ι_smul K L M)).mp inferInstance
  let : Module.Finite (Module.End U M) M :=
    Module.Finite.of_restrictScalars_finite K (Module.End U M) M
  intro f
  -- Every K-linear map commutes with the scalar commutant, hence is linear over End_U(M).
  let f' : Module.End (Module.End U M) M :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun g m => by
        obtain ⟨c, hc⟩ := hscalar
          ((lieModuleHomEquiv (asModule_ι_smul K L M) (asModule_ι_smul K L M)).symm g)
        have hg (m : M) : g m = c • m := by
          have h := congrArg (fun h : M →ₗ⁅K,L⁆ M => h m) hc
          simpa only [coe_lieModuleHomEquiv_symm, smul_apply,
            LieModuleHom.id_apply] using h
        simpa only [Module.End.smul_def, RingHom.id_apply, hg] using f.map_smul c m }
  obtain ⟨u, hu⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := U) (M := M) f'
  refine ⟨u, LinearMap.ext fun m => ?_⟩
  exact (asModule_smul_def K L M u m).symm.trans (LinearMap.congr_fun hu m)

end TauCeti.UniversalEnvelopingAlgebra
