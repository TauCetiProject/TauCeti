/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.AtkinLehner.OldSpace
public import TauCeti.NumberTheory.ModularForms.Newforms.Nebentypus
public import TauCeti.NumberTheory.ModularForms.Petersson.AtkinLehner

/-!
# Atkin–Lehner operators preserve the new subspace

Let `Q ∥ N` be an exact divisor and let `W` be an Atkin–Lehner matrix for `Q`. The slash
operator by `W` on `S_k(Γ₁(N))` preserves the old subspace and scales the Petersson product
by `Q ^ (k - 2)`. Its square is that nonzero scalar times a diamond operator, and diamond
operators also preserve the old subspace. These facts show that `W_Q` preserves the
Petersson-orthogonal complement, hence the new subspace.

Together with the character transport from
`TauCeti/NumberTheory/ModularForms/AtkinLehner/Gamma1.lean`, this gives the general-nebentypus
stability needed for Atkin and Li's pseudo-eigenvalues: `W_Q` carries the new part of
`S_k(N, χ)` into the new part of `S_k(N, χ ∘ ι_Q)`.

## Main results

* `TauCeti.atkinLehnerOperatorGamma1Cusp_mem_cuspFormsNew`: an Atkin–Lehner operator on
  `S_k(Γ₁(N))` preserves the new subspace.
* `TauCeti.atkinLehnerOperatorGamma1Cusp_mem_cuspFormsNew_inf_cuspFormCharSpace`: on a
  nebentypus component it preserves newness and transports the character by `ι_Q`.

## References

* A. O. L. Atkin and W.-C. W. Li, *Twists of newforms and pseudo-eigenvalues of
  `W`-operators*, Invent. Math. **48** (1978), 221–243, §1.
* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §5.8.
-/

public section

noncomputable section

open Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped MatrixGroups ModularForm ComplexConjugate TauCeti.ExactDivisor

namespace TauCeti

variable {N Q : ℕ} [NeZero N] {W : Matrix (Fin 2) (Fin 2) ℤ} {k : ℤ}

/-- **An Atkin–Lehner operator on `S_k(Γ₁(N))` preserves the new subspace.** This holds in
every integral weight `k` and for every Atkin–Lehner matrix `W` of every exact divisor `Q ∥ N`. -/
theorem atkinLehnerOperatorGamma1Cusp_mem_cuspFormsNew
    (hQ : 0 < Q) (hQN : Q ∣ N) (hW : IsAtkinLehnerMatrix N Q W)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormsNew N k) :
    atkinLehnerOperatorGamma1Cusp hQ hQN hW k f ∈ cuspFormsNew N k := by
  rw [cuspFormsNew_def, CuspForm.mem_peterssonOrthogonal_iff] at hf ⊢
  obtain ⟨γ, hγ, hsq⟩ := hW.exists_mem_Gamma0_mul_self hQ.ne' hQN
  let u : (ZMod N)ˣ := (Gamma0Map N).toHomUnits ⟨γ, hγ⟩
  have hu : ZMod.unitsMap hQN u = -1 := by
    simpa [u] using hW.unitsMap_toHomUnits_gamma0Map_of_mul_self_eq hQ.ne' hQN hγ hsq
  have hu' : (Q : ZMod N) * u = ((W 1 1 : ℤ) : ZMod N) ^ 2 := by
    simpa [u] using hW.natCast_mul_toHomUnits_gamma0Map_of_mul_self_eq hγ hsq
  -- `W_Q² = Q ^ (k - 2) • ⟨u⟩`, so each old `g` is, up to that nonzero scalar, `W_Q² g'` for
  -- the old form `g' = ⟨u⁻¹⟩ g`; the Petersson scaling law moves one `W_Q` onto `f`.
  intro g hg
  set g' := diamondOpCusp k u⁻¹ g with hg'_def
  have hg' : g' ∈ cuspFormsOld N k := diamondOpCusp_mem_cuspFormsOld u⁻¹ hg
  have hWg' : atkinLehnerOperatorGamma1Cusp hQ hQN hW k g' ∈ cuspFormsOld N k :=
    atkinLehnerOperatorGamma1Cusp_mem_cuspFormsOld hQ hQN hW hg'
  have hzero : CuspForm.peterssonInnerCosets
      (atkinLehnerOperatorGamma1Cusp hQ hQN hW k g') f = 0 := hf _ hWg'
  have hpair := peterssonInnerCosets_atkinLehnerOperatorGamma1Cusp hQ hQN hW
    (atkinLehnerOperatorGamma1Cusp hQ hQN hW k g') f
  rw [hzero, mul_zero,
    atkinLehnerOperatorGamma1Cusp_atkinLehnerOperatorGamma1Cusp hQ hQN hW hu hu' g',
    CuspForm.peterssonInnerCosets_smul_left] at hpair
  have hug : diamondOpCusp k u g' = g := by
    rw [hg'_def, ← LinearMap.comp_apply,
      ← diamondOpCusp_mul, mul_inv_cancel, diamondOpCusp_one, LinearMap.id_apply]
  rw [hug] at hpair
  have hscalar : conj ((Q : ℂ) ^ (k - 2)) ≠ 0 := by
    exact (map_ne_zero conj).2 (zpow_ne_zero _ (Nat.cast_ne_zero.mpr hQ.ne'))
  exact (mul_eq_zero.mp hpair).resolve_left hscalar

/-- **Atkin–Lehner stability with the nebentypus transport.** The operator `W_Q` carries the
new part of `S_k(N, χ)` into the new part of `S_k(N, χ ∘ ι_Q)`, where `ι_Q` inverts the
residue modulo `Q` and fixes it modulo `N / Q`. -/
theorem atkinLehnerOperatorGamma1Cusp_mem_cuspFormsNew_inf_cuspFormCharSpace
    (hQ : 0 < Q) (hQN : Q ∣ N) (hW : IsAtkinLehnerMatrix N Q W)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} {χ : (ZMod N)ˣ →* ℂˣ}
    (hf : f ∈ cuspFormsNew N k ⊓ cuspFormCharSpace k χ) :
    atkinLehnerOperatorGamma1Cusp hQ hQN hW k f ∈
      cuspFormsNew N k ⊓ cuspFormCharSpace k
        (χ.comp ((hW.isExactDivisor hQ.ne' hQN).unitsInvPart : (ZMod N)ˣ →* (ZMod N)ˣ)) :=
  ⟨atkinLehnerOperatorGamma1Cusp_mem_cuspFormsNew hQ hQN hW hf.1,
    atkinLehnerOperatorGamma1Cusp_mem_cuspFormCharSpace hQ hQN hW hf.2⟩

end TauCeti
