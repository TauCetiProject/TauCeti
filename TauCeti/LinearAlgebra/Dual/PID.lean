/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import TauCeti.Algebra.Module.Torsion.Basic
import TauCeti.LinearAlgebra.Dual.Basis

/-!
# Linear duals over principal ideal domains

Over a principal ideal domain `R`, every linear functional on an `R`-module `M` vanishes on
`Submodule.torsion R M`, so `Submodule.dualQuotEquivDualAnnihilator` identifies `Module.Dual R M`
with the dual of the torsion-free quotient `M ⧸ Submodule.torsion R M`. When `M` is finitely
generated, `M ⧸ Submodule.torsion R M` is finite free, so `Module.Dual R M` and `M` have the same
`finrank` (`TauCeti.Module.dual_finrank_eq_of_isPrincipalIdealRing`).
-/

public section

namespace TauCeti.Module

/-- Over a principal ideal domain, a finitely generated module and its linear dual have the same
`finrank`. -/
@[simp]
theorem dual_finrank_eq_of_isPrincipalIdealRing (R M : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.finrank R (Module.Dual R M) = Module.finrank R M := by
  let T := Submodule.torsion R M
  have htop : T.dualAnnihilator = ⊤ := eq_top_iff.2 fun φ _ ↦
    (Submodule.mem_dualAnnihilator φ).2 fun x hx ↦ by
      have hmem : φ x ∈ Submodule.torsion R R := φ.le_comap_torsion hx
      rwa [Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance, Submodule.mem_bot] at hmem
  have : Module.Free R (M ⧸ T) := Module.free_of_finite_type_torsion_free'
  exact ((LinearEquiv.ofTop T.dualAnnihilator htop).symm.trans
    T.dualQuotEquivDualAnnihilator.symm).finrank_eq.trans
      ((dual_finrank_eq R (M ⧸ T)).trans (finrank_quotient_eq_of_le_torsion le_rfl))

end TauCeti.Module
