/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform

/-!
# Stability of the new subspace under the bad-prime operators

For a prime `p` dividing the level `N`, the operator `U_p = T_p` maps the new subspace
`S_k(Γ₁(N))ⁿᵉʷ` into itself. Together with the stability of the new subspace under the good `T_p`
and the diamond operators, and of the old subspace under every `T_p` and every diamond operator,
this is Diamond–Shurman's Proposition 5.6.2: both subspaces are stable under the whole Hecke
algebra.

At a good prime the stability of the new subspace comes from that of the old subspace, since the
Petersson adjoint of `T_p` is `⟨p⟩⁻¹ T_p`. At `p ∣ N` that argument is not available: the
adjoint of `U_p` is not a multiple of `U_p`, and the stability of the old subspace only gives the
stability of the new subspace under the adjoint. Instead, the newforms span the new subspace
(`HeckeRing.GL2.Newform.span_range_toCuspForm_eq_cuspFormsNew`), and each of them is a
`U_p`-eigenvector (`HeckeRing.GL2.Newform.heckeUCuspNat_eq_qExpansion_coeff_smul`, proved without
any bad-prime stability), so `U_p` carries a spanning family of the new subspace into it.

On a character space `S_k(N, χ)`, where the Hecke ring of `Γ₀(N)` acts, the new part is then
stable under every prime generator, hence under every `T_n`
(`HeckeRing.GL2.heckeRingHomCuspCharSpace_heckeTCompositeGamma0_mem_of_forall_prime`).

## Main results

* `TauCeti.heckeUCuspNat_mem_cuspFormsNew`: `U_p` maps the new subspace into itself, for every
  prime `p ∣ N`, with `TauCeti.cuspFormsNew_map_heckeUCuspNat_le` its `Submodule.map` form.
* `TauCeti.coe_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_mem_cuspFormsNew`: the new part of
  `S_k(N, χ)` is stable under every `T_n`, with
  `TauCeti.cuspFormsNew_comap_map_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_le` its
  `Submodule.map` form.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.6.2.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.13.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups

namespace TauCeti

variable {k : ℤ} {N p : ℕ} [NeZero N]

/-- **The new subspace is stable under the bad-prime operator `U_p`**: for a prime `p` dividing
the level, `U_p = T_p` maps `S_k(Γ₁(N))ⁿᵉʷ` into itself. This is the new-space half of
Diamond–Shurman's Proposition 5.6.2 at the primes dividing the level; the good primes are
`heckeTCuspNat_mem_cuspFormsNew`. -/
theorem heckeUCuspNat_mem_cuspFormsNew (hp : p.Prime) (hpN : p ∣ N)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormsNew N k) :
    HeckeRing.GL2.heckeUCuspNat k p hp hpN f ∈ cuspFormsNew N k := by
  -- the newforms span the new subspace, and `U_p` scales each of them
  refine (Submodule.span_le
    (p := (cuspFormsNew N k).comap (HeckeRing.GL2.heckeUCuspNat k p hp hpN))).mpr ?_
    (HeckeRing.GL2.Newform.span_range_toCuspForm_eq_cuspFormsNew.ge hf)
  rintro _ ⟨g, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, g.heckeUCuspNat_eq_qExpansion_coeff_smul hp hpN]
  exact Submodule.smul_mem _ _ g.isNew

/-- The new subspace is stable under `U_p` for `p ∣ N`, in the `Submodule.map` form. -/
theorem cuspFormsNew_map_heckeUCuspNat_le (hp : p.Prime) (hpN : p ∣ N) (k : ℤ) :
    (cuspFormsNew N k).map (HeckeRing.GL2.heckeUCuspNat k p hp hpN) ≤ cuspFormsNew N k := by
  rw [Submodule.map_le_iff_le_comap]
  exact fun _ hf ↦ heckeUCuspNat_mem_cuspFormsNew hp hpN hf

/-- **The new part of `S_k(N, χ)` is stable under every Hecke operator `T_n`**, the composite
element `heckeTCompositeGamma0 N n` of the `Γ₀(N)` Hecke ring acting on `S_k(N, χ)`, whether or
not `n` shares a factor with the level. This is the new-space half of Diamond–Shurman's
Proposition 5.6.2 for the operators `T_n`; the old-space half is
`coe_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_mem_cuspFormsOld`. -/
theorem coe_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_mem_cuspFormsNew
    {χ : (ZMod N)ˣ →* ℂˣ} (n : ℕ) {F : cuspFormCharSpace k χ}
    (hF : (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsNew N k) :
    (HeckeRing.GL2.heckeRingHomCuspCharSpace k χ (HeckeRing.GL2.heckeTCompositeGamma0 N n) F :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsNew N k := by
  refine HeckeRing.GL2.heckeRingHomCuspCharSpace_heckeTCompositeGamma0_mem_of_forall_prime
    (V := (cuspFormsNew N k).comap (cuspFormCharSpace k χ).subtype) (fun p hp G hG ↦ ?_) n hF
  -- at a prime the generator acts as `T_p`, which is `U_p` when `p ∣ N`
  rw [Submodule.mem_comap, Submodule.subtype_apply,
    HeckeRing.GL2.coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k χ hp]
  by_cases hpN : Nat.Coprime p N
  · exact heckeTCuspNat_mem_cuspFormsNew hp hpN hG
  · exact heckeUCuspNat_mem_cuspFormsNew hp ((Nat.Prime.dvd_iff_not_coprime hp).2 hpN) hG

/-- **The new part of `S_k(N, χ)` is stable under every `T_n`**, in `Submodule.map` form. -/
theorem cuspFormsNew_comap_map_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_le
    (χ : (ZMod N)ˣ →* ℂˣ) (n : ℕ) (k : ℤ) :
    ((cuspFormsNew N k).comap (cuspFormCharSpace k χ).subtype).map
        (HeckeRing.GL2.heckeRingHomCuspCharSpace k χ (HeckeRing.GL2.heckeTCompositeGamma0 N n)) ≤
      (cuspFormsNew N k).comap (cuspFormCharSpace k χ).subtype := by
  rw [Submodule.map_le_iff_le_comap]
  exact fun _ hF ↦ coe_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_mem_cuspFormsNew n hF

end TauCeti
