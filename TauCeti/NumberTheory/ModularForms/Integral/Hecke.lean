/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Integral.Basic
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.AtCusp

/-!
# Hecke stability of the forms integral at every cusp

The forms in `M_k(Γ₁(N))` whose expansions at every cusp have coefficients in a subring
`R ⊆ ℂ` (`TauCeti.ModularForm.integralAtCusps`) are stable under the Hecke operator `Tₚ` at
every prime `p ∤ N`, in every weight `k ≥ 1`. Together with their stability under the diamond
operators (`TauCeti.ModularForm.diamondOp_mem_integralAtCusps`), this is the Hecke stability of
Deligne–Serre's lattice of forms with integral expansions at all cusps. That lattice is what
makes the Hecke eigenvalues algebraic integers in weight one as well, where no cohomological
lattice exists.

The proof reads the expansion of `Tₚ f` at a cusp off the expansions of `f` at two other cusps
(`HeckeRing.GL2.exists_qExpansion_coeff_translate_heckeTNat`):
`aₙ((Tₚ f) ∣ γ) = a_{p n}(f ∣ δ₁) + p^{k−1} a_{n/p}(f ∣ δ₂)`. Integrality at one cusp alone
would not survive `Tₚ`, which is why integrality is imposed at every cusp.

The bound `1 ≤ k` is needed: in weight `0` the constant function `1` has integral expansions,
while `Tₚ 1 = 1 + p⁻¹` with the normalization of the slash action used here.

## Main results

* `TauCeti.ModularForm.heckeTNat_mem_integralAtCusps`: `Tₚ` preserves the forms integral at every
  cusp, for a prime `p ∤ N` and `k ≥ 1`.

## References

* P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7
  (1974), 507–530, §2.7.
-/

public section

open Matrix.SpecialLinearGroup CongruenceSubgroup ModularForm HeckeRing.GL2
open scoped MatrixGroups

namespace TauCeti.ModularForm

variable {R : Subring ℂ} {N p : ℕ} [NeZero N] {k : ℤ}

/-- **`Tₚ` preserves integrality at every cusp.** For a prime `p ∤ N` and a weight `k ≥ 1`, the
Hecke operator `Tₚ` maps a form on `Γ₁(N)` whose expansions at every cusp have coefficients in
`R` to another such form. -/
theorem heckeTNat_mem_integralAtCusps (hp : p.Prime) (hpN : p.Coprime N) (hk : 1 ≤ k)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ integralAtCusps R ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeTNat k p (_hn := ⟨hp.ne_zero⟩) f ∈ integralAtCusps R ((Gamma1 N).map (mapGL ℝ)) k := by
  have hΓ := Subgroup.map_mono (f := mapGL ℝ) (Gamma_le_Gamma1 N)
  rw [mem_integralAtCusps_iff_qExpansion_coeff_mem hΓ] at hf ⊢
  intro γ n
  obtain ⟨δ₁, δ₂, hδ⟩ := exists_qExpansion_coeff_translate_heckeTNat k hp hpN f γ
  rw [hδ]
  refine R.add_mem (hf δ₁ _) ?_
  split_ifs
  · -- `p ^ (k - 1)` is a natural number since `k ≥ 1`
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hk)
    rw [hj, zpow_natCast]
    exact R.mul_mem (R.pow_mem (natCast_mem R p) j) (hf δ₂ _)
  · exact R.zero_mem

end TauCeti.ModularForm
