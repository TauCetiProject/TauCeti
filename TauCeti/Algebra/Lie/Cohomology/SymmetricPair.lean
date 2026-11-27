/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Cohomology.Relative.Basic

/-!
# Relative cochains of symmetric Lie algebra pairs

For trivial coefficients, a symmetric Lie algebra pair has zero relative differential.
One can compute the differential on representatives in the complementary submodule,
where every bracket lies in the subalgebra and hence contributes zero.
-/

public section

namespace TauCeti.LieModule.Cohomology

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M] [LieModule.IsTrivial L M]

/-- The relative differential with trivial coefficients vanishes when `P` represents every
class modulo `H` and the bracket of any two elements of `P` lies in `H`. -/
theorem d_eq_zero_of_mem_relativeCochains {H : LieSubalgebra R L} {P : Submodule R L}
    (hsup : H.toSubmodule ⊔ P = ⊤) (hbracket : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ H)
    {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M} (hω : ω ∈ relativeCochains R M H n) :
    d R L M n ω = 0 := by
  ext v
  cases n with
  | zero => simp [d_zero_apply, trivial_lie_zero]
  | succ n =>
    have hv (i : Fin (n + 2)) : v i ∈ H.toSubmodule ⊔ P := by simp [hsup]
    choose a ha p hp hap using fun i ↦ Submodule.mem_sup.mp (hv i)
    have hd : d R L M (n + 1) ω ∈ H.toSubmodule.conormalForms (Fin (n + 2)) M :=
      Submodule.mem_conormalForms.mpr fun w j hj ↦
        (mem_relativeCochains_iff.mp (d_mem_relativeCochains hω)).1 w j hj
    rw [Submodule.conormalForms_apply_eq_of_sub_mem hd (y := p), d_succ_apply]
    · simp only [trivial_lie_zero, smul_zero, Finset.sum_const_zero, zero_add, zero_apply]
      refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_
      rw [(mem_relativeCochains_iff.mp hω).1 _ 0 (hbracket _ (hp _) _ (hp _)), smul_zero]
    · intro j
      rw [← hap j, add_sub_cancel_right]
      exact ha j

end TauCeti.LieModule.Cohomology
