/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators
import TauCeti.Data.ZMod.Units
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Recurrence
public import TauCeti.NumberTheory.ModularForms.Twist.Basic

/-!
# Hecke operators and twists by Dirichlet characters

Let `ψ` be a Dirichlet character modulo `M` and `f ∈ M_k(Γ₁(N), χ)`, and let `L` be a level
with `N * M ∣ L` and `M * M ∣ L`, so that the twist `f ⊗ ψ` lies in `M_k(Γ₁(L), χψ²)`. At a
prime `p ∤ L` the Hecke operators of the two levels are intertwined by the twist:

`T_p (f ⊗ ψ) = ψ(p) · (T_p f) ⊗ ψ`.

On the `m`-th `q`-expansion coefficient this is the identity
`ψ(pm) a_{pm} + χ(p)ψ(p)² p^{k-1} ψ(m/p) a_{m/p} = ψ(p) ψ(m) (a_{pm} + χ(p) p^{k-1} a_{m/p})`,
the terms with `a_{m/p}` present only when `p ∣ m`; it uses only the multiplicativity of `ψ`.
In particular, if `T_p f = c • f`, then `T_p (f ⊗ ψ) = (ψ(p) c) • (f ⊗ ψ)`: the twist satisfies the
eigenrelation with eigenvalue `ψ(p) c`, and is a `T_p`-eigenvector whenever it is nonzero (the
twist can annihilate a nonzero form).

## Main results

* `ModularForm.heckeTNat_twist`: `T_p (f ⊗ ψ) = ψ(p) • (T_p f) ⊗ ψ` for `p ∤ L`.
* `CuspForm.heckeTCuspNat_twist`: the same identity for cusp forms.
* `CuspForm.heckeTCuspNat_twist_eq_smul`: the twist of a `T_p`-eigenrelation.

## References

* G. Shimura, *Introduction to the arithmetic theory of automorphic functions*, Proposition 3.64.
* A. O. L. Atkin, W.-C. W. Li, *Twists of newforms and pseudo-eigenvalues of `W`-operators*,
  Invent. Math. 48 (1978).
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GL2 ZMod

open scoped MatrixGroups

namespace TauCeti

variable {M N L p : ℕ} {k : ℤ}

/-- **Twisting intertwines the Hecke operators at a prime not dividing the level.** For a
Dirichlet character `ψ` modulo `M`, `f ∈ M_k(Γ₁(N), χ)` and a prime `p ∤ L`,
`T_p (f ⊗ ψ) = ψ(p) • (T_p f) ⊗ ψ`, with `T_p` taken at level `L` on the left and at level `N`
on the right. -/
theorem _root_.ModularForm.heckeTNat_twist [NeZero M] [NeZero N] [NeZero L]
    (ψ : DirichletCharacter ℂ M) (hNL : N * M ∣ L) (hML : M * M ∣ L) {χ : (ZMod N)ˣ →* ℂˣ}
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ)
    (hp : p.Prime) (hpL : p.Coprime L) :
    heckeTNat k p (_hn := ⟨hp.ne_zero⟩) (ModularForm.twist ψ hNL hML f) =
      ψ p • ModularForm.twist ψ hNL hML (heckeTNat k p (_hn := ⟨hp.ne_zero⟩) f) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hpN := hpL.coprime_dvd_right (dvd_of_mul_right_dvd hNL)
  refine (ModularForm.qExpansion_inj one_pos (one_mem_strictPeriods_Gamma1_map L)).1
    (PowerSeries.ext fun m ↦ ?_)
  simp only [heckeTNat_def,
    qExpansion_coeff_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_mem_modFormCharSpace k hp
      hpL _ (ModularForm.twist_mem_modFormCharSpace ψ hNL hML hf),
    qExpansion_coeff_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_mem_modFormCharSpace k hp
      hpN χ hf, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map L),
    PowerSeries.coeff_smul, ModularForm.qExpansion_twist_coeff, smul_eq_mul,
    MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.pow_apply, unitsMap_unitOfCoprime,
    Units.val_mul, Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, coe_unitOfCoprime]
  split_ifs with hpm
  · obtain ⟨m, rfl⟩ := hpm
    rw [Nat.mul_div_cancel_left m hp.pos]
    push_cast
    simp only [map_mul]
    ring
  · push_cast
    rw [map_mul]
    ring

/-- **Twisting intertwines the Hecke operators on cusp forms.** For a Dirichlet character `ψ`
modulo `M`, `f ∈ S_k(Γ₁(N), χ)` and a prime `p ∤ L`, `T_p (f ⊗ ψ) = ψ(p) • (T_p f) ⊗ ψ`. -/
theorem _root_.CuspForm.heckeTCuspNat_twist [NeZero M] [NeZero N] [NeZero L]
    (ψ : DirichletCharacter ℂ M) (hNL : N * M ∣ L) (hML : M * M ∣ L) {χ : (ZMod N)ˣ →* ℂˣ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ)
    (hp : p.Prime) (hpL : p.Coprime L) :
    heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) (CuspForm.twist ψ hNL hML f) =
      ψ p • CuspForm.twist ψ hNL hML (heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) f) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have h := ModularForm.heckeTNat_twist ψ hNL hML ((coe_mem_modFormCharSpace_iff k χ f).mpr hf)
    hp hpL
  rw [ModularForm.twist_coe_cuspForm, heckeTNat_coe_cuspForm, heckeTNat_coe_cuspForm,
    ModularForm.twist_coe_cuspForm] at h
  ext τ
  simpa using DFunLike.congr_fun h τ

/-- **Twisting preserves a `T_p`-eigenrelation.** If `f ∈ S_k(Γ₁(N), χ)` satisfies
`T_p f = c • f` at a prime `p ∤ L`, then `T_p (f ⊗ ψ) = (ψ(p) c) • (f ⊗ ψ)`. So `f ⊗ ψ` is a
`T_p`-eigenvector with eigenvalue `ψ(p) c` whenever it is nonzero; the twist of a nonzero form
can vanish. -/
theorem _root_.CuspForm.heckeTCuspNat_twist_eq_smul [NeZero M] [NeZero N] [NeZero L]
    (ψ : DirichletCharacter ℂ M) (hNL : N * M ∣ L) (hML : M * M ∣ L) {χ : (ZMod N)ˣ →* ℂˣ}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ)
    (hp : p.Prime) (hpL : p.Coprime L) {c : ℂ}
    (hc : heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) f = c • f) :
    heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) (CuspForm.twist ψ hNL hML f) =
      (ψ p * c) • CuspForm.twist ψ hNL hML f := by
  rw [CuspForm.heckeTCuspNat_twist ψ hNL hML hf hp hpL, hc, ← CuspForm.twistₗ_apply,
    _root_.map_smul, CuspForm.twistₗ_apply, smul_smul]

end TauCeti
