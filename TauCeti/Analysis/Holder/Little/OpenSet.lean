/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Little.Basic
public import TauCeti.Analysis.Holder.OpenSet.Basic

/-!
# Little Hölder spaces on an open set

For an open set `Ω` of a real normed space, the little Hölder space `h^{k,α}(Ω)` is the subspace
`TauCeti.CkHolderSpaceOn.littleHolder` of the Hölder space `C^{k,α}(Ω, F)` of
`TauCeti.CkHolderSpaceOn` whose `k`-th derivative field has `α`-Hölder difference quotients
tending to zero at small scales (`TauCeti.MemLittleHolder`). It is the preimage of the little
Hölder space `TauCeti.HolderSpace.littleHolder` of derivative fields on `Ω` under the `k`-th
derivative map, so it is closed, and a Banach space when `F` is complete. This is the open-set
version of `TauCeti.CkHolderSpace.littleHolder`.

An element whose `k`-th derivative field is Hölder of an exponent larger than `α` lies in
`h^{k,α}(Ω)` (`TauCeti.CkHolderSpaceOn.mem_littleHolder_of_memHolder`).

## Main declarations

* `TauCeti.CkHolderSpaceOn.littleHolder k α Ω F`: the little Hölder space `h^{k,α}(Ω)`.
* `TauCeti.CkHolderSpaceOn.isClosed_littleHolder`: it is closed in the `C^{k,α}(Ω)` norm.
* `TauCeti.CkHolderSpaceOn.mem_littleHolder_of_memHolder`: a `k`-th derivative field that is
  Hölder of a larger exponent is little `α`-Hölder.

## References

* A. Lunardi, *Analytic Semigroups and Optimal Regularity in Parabolic Problems*, Birkhäuser
  (1995), Chapter 0.
-/

public section

noncomputable section

open TopologicalSpace
open scoped NNReal

namespace TauCeti

namespace CkHolderSpaceOn

variable (k : ℕ) (α : ℝ≥0) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (Ω : Opens E) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The **little Hölder space** `h^{k,α}(Ω)`: the elements of `C^{k,α}(Ω, F)` whose `k`-th
derivative field has `α`-Hölder difference quotients tending to zero at small scales. It is the
preimage of the little Hölder space `HolderSpace.littleHolder` of derivative fields on `Ω` under
the `k`-th derivative map `CkHolderSpaceOn.iteratedFDerivHolderL`. -/
def littleHolder : Submodule ℝ (CkHolderSpaceOn k α Ω F) :=
  (HolderSpace.littleHolder α Ω (E [×k]→L[ℝ] F)).comap
    (iteratedFDerivHolderL : CkHolderSpaceOn k α Ω F →L[ℝ] _).toLinearMap

variable {k α Ω F}

/-- An element of `C^{k,α}(Ω)` lies in `h^{k,α}(Ω)` exactly when its `k`-th derivative field is
little `α`-Hölder on `Ω`. -/
@[simp]
theorem mem_littleHolder_iff {f : CkHolderSpaceOn k α Ω F} :
    f ∈ littleHolder k α Ω F ↔
      MemLittleHolder α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F) := by
  rw [littleHolder, Submodule.mem_comap, ContinuousLinearMap.coe_coe, iteratedFDerivHolderL_apply,
    HolderSpace.mem_littleHolder_iff, coe_iteratedFDerivHolder]

/-- **The little Hölder space `h^{k,α}(Ω)` is closed** in the `C^{k,α}(Ω)` norm. -/
theorem isClosed_littleHolder :
    IsClosed (littleHolder k α Ω F : Set (CkHolderSpaceOn k α Ω F)) := by
  rw [littleHolder, Submodule.comap_coe, ContinuousLinearMap.coe_coe]
  exact HolderSpace.isClosed_littleHolder.preimage iteratedFDerivHolderL.continuous

/-- The little Hölder space `h^{k,α}(Ω)` of a complete space is a Banach space. -/
instance instCompleteSpaceLittleHolder [CompleteSpace F] : CompleteSpace (littleHolder k α Ω F) :=
  isClosed_littleHolder.completeSpace_coe

/-- An element of `C^{k,α}(Ω)` whose `k`-th derivative field is Hölder of an exponent `β > α` on
`Ω` lies in `h^{k,α}(Ω)`. -/
theorem mem_littleHolder_of_memHolder {β : ℝ≥0} (hαβ : α < β) {f : CkHolderSpaceOn k α Ω F}
    (hf : MemHolder β (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F)) :
    f ∈ littleHolder k α Ω F :=
  mem_littleHolder_iff.2 (hf.holderWith.memLittleHolder hαβ)

end CkHolderSpaceOn

end TauCeti
