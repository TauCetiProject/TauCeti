/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import TauCeti.Algebra.Lie.Weights.Basic
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import TauCeti.LinearAlgebra.TensorProduct.Kernel

/-!
# Lie-module weight spaces under extension of scalars

A linear weight extends to the scalar-extended Lie algebra by `Module.Dual.baseChange`.
The extension of its ordinary weight space lies in the new weight space. If the coefficient
algebra is flat and the Lie algebra is finitely generated as a module, the two spaces agree.
In particular, extension of fields preserves `Module.finrank` of each specified weight space.

These comparisons apply to the Cartan weight spaces of rational highest-weight modules;
neither semisimplicity nor finite dimensionality of the represented module is required.
They concern ordinary simultaneous eigenspaces, not generalized weight spaces or weights
that do not descend to the original coefficient ring.

## Main results

* `LieModule.baseChange_weightSpace_le`: extension preserves weight vectors.
* `LieModule.weightSpace_baseChange`: flat scalar extension commutes with a specified weight space.
* `LieModule.finrank_weightSpace_baseChange`: its dimension is unchanged by extension of fields.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters VII–IX, Chapter VII, §1.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §20.

The invariant-vector comparison `LieModule.maxTrivSubmodule_baseChange` is the zero-weight case.
-/

public section

open TensorProduct

namespace LieModule

variable {R A L M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- Extension of scalars carries an ordinary weight space into the space at the extended weight,
without a flatness or finiteness hypothesis. -/
theorem baseChange_weightSpace_le (χ : Module.Dual R L) :
    (weightSpace M χ).baseChange A ≤
      weightSpace (A ⊗[R] M) (Module.Dual.baseChange A χ) := by
  rw [← LieSubmodule.toSubmodule_le_toSubmodule, LieSubmodule.coe_baseChange,
    Submodule.baseChange_eq_span, Submodule.span_le]
  rintro _ ⟨m, hm, rfl⟩
  rw [SetLike.mem_coe, LieSubmodule.mem_toSubmodule, mem_weightSpace]
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a y =>
    simp [LieAlgebra.ExtendScalars.bracket_tmul, (mem_weightSpace χ m).mp hm y,
      Module.Dual.baseChange_apply_tmul, tmul_smul, smul_tmul']
  | add x y hx hy =>
    simpa only [TensorProduct.mk_apply, add_lie, map_add, add_smul] using
      congrArg₂ (· + ·) hx hy

/-- Flat extension of scalars commutes with an ordinary weight space when the acting Lie algebra
is finitely generated as a module. The represented module need not be finite or free. -/
@[simp]
theorem weightSpace_baseChange [Module.Flat R A] [Module.Finite R L]
    (χ : Module.Dual R L) :
    weightSpace (A ⊗[R] M) (Module.Dual.baseChange A χ) =
      (weightSpace M χ).baseChange A := by
  refine le_antisymm (fun m hm ↦ ?_) (baseChange_weightSpace_le χ)
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := L)
  -- A finite collection of eigenvector equations suffices, so flatness applies to one kernel.
  let φ : M →ₗ[R] (Fin n → M) :=
    LinearMap.pi fun i ↦ toEnd R L M (s i) - χ (s i) • LinearMap.id
  have hker : LinearMap.ker φ = (weightSpace M χ : Submodule R M) := by
    ext v
    simp only [LinearMap.mem_ker, LieSubmodule.mem_toSubmodule, mem_weightSpace]
    constructor
    · intro hv x
      have hext :
          (toEnd R L M : L →ₗ[R] Module.End R M).flip v -
            χ.smulRight v = 0 :=
        LinearMap.ext_on_range hs fun i ↦ by
          simpa [φ] using congrFun hv i
      have hx := LinearMap.congr_fun hext x
      simpa [sub_eq_zero] using hx
    · intro hv
      ext i
      simp [φ, hv (s i)]
  -- The extended kernel equations are precisely those for the elements `1 ⊗ₜ s i`.
  have hφ : φ.baseChange A m = 0 := by
    refine (piRight R A A fun _ : Fin n ↦ M).injective ?_
    rw [map_zero]
    ext i
    have hi := (mem_weightSpace (Module.Dual.baseChange A χ) m).mp hm (1 ⊗ₜ s i)
    have hcomponent :
        piRight R A A (fun _ : Fin n ↦ M) (φ.baseChange A m) i =
          ⁅(1 : A) ⊗ₜ[R] s i, m⁆ -
            Module.Dual.baseChange A χ (1 ⊗ₜ[R] s i) • m := by
      clear hm hi
      induction m using TensorProduct.inductionOn with
      | tmul a v =>
        simp [φ, LieAlgebra.ExtendScalars.bracket_tmul,
          Module.Dual.baseChange_apply_tmul, tmul_sub, tmul_smul, smul_tmul']
      | add v w hv hw =>
        simp only [map_add, Pi.add_apply, hv, hw, lie_add, smul_add]
        abel
    simpa [hi] using hcomponent
  rw [← LieSubmodule.mem_toSubmodule, LieSubmodule.coe_baseChange, ← hker,
    ← LinearMap.ker_baseChange_of_flat]
  exact hφ

/-- Extension of fields preserves the natural-number dimension of every weight space defined over
the original field, provided the acting Lie algebra is finite dimensional. -/
theorem finrank_weightSpace_baseChange {K F : Type*} [Field K] [Field F] [Algebra K F]
    {L M : Type*} [LieRing L] [LieAlgebra K L] [Module.Finite K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (χ : Module.Dual K L) :
    Module.finrank F (weightSpace (F ⊗[K] M) (Module.Dual.baseChange F χ)) =
      Module.finrank K (weightSpace M χ) := by
  rw [weightSpace_baseChange]
  exact ((Submodule.toBaseChange.toLinearEquiv F
    (weightSpace M χ : Submodule K M)).finrank_eq).symm.trans Module.finrank_baseChange

end LieModule
