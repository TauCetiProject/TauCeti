/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.EigenvectorVanishing

/-!
# Multiplicity one on the new part of `S_k(N, χ)`

A cusp form in the new part of `S_k(N, χ)` that is an eigenvector of the Hecke ring at every
prime not dividing `N` is determined, up to a scalar, by those eigenvalues. Equivalently: each
simultaneous eigenspace of the good Hecke operators inside `S_k(N, χ)ᵐᵉʷ` is at most
one-dimensional.

It rests on `eq_zero_of_forall_prime_heckeRingHomCusp_of_one_eq_zero_of_mem_cuspFormsNew`
(`Newforms/EigenvectorVanishing.lean`): such an eigenvector with `a₁ = 0` is zero. Scaling each
of the two eigenvectors by the other's first coefficient and subtracting produces exactly such
an eigenvector.

## Main results

* `HeckeRing.GL2.smul_eq_smul_of_forall_prime_heckeRingHomCusp_of_mem_cuspFormsNew`: two good
  Hecke eigenvectors in the new part sharing their eigenvalues are proportional —
  `a₁(g) • f = a₁(f) • g`.

## References

* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.13(1).
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.2.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup TauCeti

open scoped MatrixGroups

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- **Multiplicity one on the new part of `S_k(N, χ)`** (Miyake, Theorem 4.6.13(1)): two cusp
forms in the new part that are eigenvectors of the Hecke ring at every prime not dividing `N`,
*with the same eigenvalue at each such prime*, are proportional: `a₁(g) • f = a₁(f) • g`. So each
simultaneous eigenspace of the good Hecke operators inside the new part is at most
one-dimensional. -/
theorem smul_eq_smul_of_forall_prime_heckeRingHomCusp_of_mem_cuspFormsNew
    {f g : cuspFormCharSpace k χ}
    (ha : ∀ p : ℕ, p.Prime → Nat.Coprime p N → ∃ c : ℂ,
      heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N p) f = c • f ∧
        heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N p) g = c • g)
    (hf : (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsNew N k)
    (hg : (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsNew N k) :
    (qExpansion 1 (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 •
        (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (qExpansion 1 (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 •
        (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  set a := (qExpansion 1 (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 with hadef
  set b := (qExpansion 1 (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 with hbdef
  -- the combination `b • f - a • g` is a good eigenvector in the new part with `a₁ = 0`
  have key : ((b • f - a • g : cuspFormCharSpace k χ) :
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = 0 := by
    refine eq_zero_of_forall_prime_heckeRingHomCusp_of_one_eq_zero_of_mem_cuspFormsNew
      (fun p hp hpN ↦ ?_) ?_ ?_
    · obtain ⟨c, hcf, hcg⟩ := ha p hp hpN
      exact ⟨c, by rw [map_sub, map_smul, map_smul, hcf, hcg, smul_sub, smul_comm c b,
        smul_comm c a]⟩
    · rw [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul, FunLike.coe_sub,
        ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map _), map_sub]
      simp only [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos
        (one_mem_strictPeriods_Gamma1_map _), map_smul, smul_eq_mul, ← hadef, ← hbdef]
      ring
    · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hf) (Submodule.smul_mem _ _ hg)
  rw [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul, sub_eq_zero] at key
  exact key

end HeckeRing.GL2

end
