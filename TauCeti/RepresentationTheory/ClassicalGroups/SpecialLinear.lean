/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SpecialLinear
public import TauCeti.RepresentationTheory.Irreducible

/-!
# Irreducibility upon restriction from `GL` to `SL`

Every finite-dimensional irreducible representation of the general linear group over
an algebraically closed field stays irreducible on the special linear group. Scalar
matrices act by scalars by Schur's lemma, and every invertible matrix is a scalar
multiple of a determinant-one matrix. Thus restriction introduces no new invariant
subspaces. No rationality or characteristic assumption is needed for this result.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

namespace Representation

variable {ι K V : Type*} [Fintype ι] [DecidableEq ι] [Field K] [IsAlgClosed K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A finite-dimensional representation of `GL` over an algebraically closed field is
irreducible on `SL` exactly when it is irreducible on `GL`, including in rank zero. -/
@[simp]
theorem isIrreducible_comp_toGL_iff (ρ : Representation K (Matrix.GeneralLinearGroup ι K) V) :
    Representation.IsIrreducible (ρ.comp Matrix.SpecialLinearGroup.toGL) ↔ ρ.IsIrreducible := by
  constructor
  · intro hρ
    have := hρ
    have := hρ.nontrivial
    refine ⟨fun S => ?_⟩
    let T : Subrepresentation (ρ.comp Matrix.SpecialLinearGroup.toGL) :=
      { toSubmodule := S.toSubmodule
        apply_mem_toSubmodule g v hv := S.apply_mem_toSubmodule _ hv }
    refine (eq_bot_or_eq_top T).imp (fun h => ?_) fun h => ?_
    · apply Subrepresentation.toSubmodule_injective
      simpa only [T, Subrepresentation.toSubmodule_bot] using
        congrArg Subrepresentation.toSubmodule h
    · apply Subrepresentation.toSubmodule_injective
      simpa only [T, Subrepresentation.toSubmodule_top] using
        congrArg Subrepresentation.toSubmodule h
  intro hρ
  have := hρ
  have := hρ.nontrivial
  refine ⟨fun S => ?_⟩
  let T : Subrepresentation ρ :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule g v hv := by
        obtain ⟨s, z, rfl⟩ := g.exists_toGL_mul_scalar_eq
        obtain ⟨a, ha⟩ := IsIrreducible.exists_forall_apply_eq_smul
          (ρ (Matrix.GeneralLinearGroup.scalar ι z)) fun g v => by
            simpa only [map_mul, Module.End.mul_apply] using
              congrArg (fun g => ρ g v) (Matrix.GeneralLinearGroup.scalar_commute z g)
        rw [map_mul, Module.End.mul_apply, ha, map_smul]
        exact S.toSubmodule.smul_mem a (S.apply_mem_toSubmodule s hv) }
  refine (eq_bot_or_eq_top T).imp (fun h => ?_) fun h => ?_
  · apply Subrepresentation.toSubmodule_injective
    simpa only [T, Subrepresentation.toSubmodule_bot] using
      congrArg Subrepresentation.toSubmodule h
  · apply Subrepresentation.toSubmodule_injective
    simpa only [T, Subrepresentation.toSubmodule_top] using
      congrArg Subrepresentation.toSubmodule h

end Representation
