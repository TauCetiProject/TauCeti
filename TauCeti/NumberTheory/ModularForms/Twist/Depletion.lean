/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.ModularForm
public import TauCeti.NumberTheory.ModularForms.Twist.Basic
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.QExpansion
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# Depletion, and twists by imprimitive characters

For `d ≥ 1`, the **`d`-depletion** of a modular form `f` for `Γ₁(N)` is `f - V_d U_d f`, where
`U_d` is the upper-triangular Hecke operator `∑_{b < d} f ∣ [1, b; 0, d]`, which extracts the
coefficients `a_{d m}`, and `V_d` is the level-raising operator `τ ↦ d τ`, which substitutes
`q ↦ q ^ d`. On `q`-expansions it deletes the terms whose index is divisible by `d`:

`aₙ(f - V_d U_d f) = 0` if `d ∣ n`, and `aₙ(f)` otherwise.

`U_d` acts at a level divisible by `d`, and `V_d` multiplies the level by `d`. Here `f` is read at
the level `L / d`, which `N` and `d` divide, then raised by `V_d` to `L`; so the depletion is a
modular form for `Γ₁(L)` whenever `N * d ∣ L` and `d * d ∣ L`. These are exactly the conditions
under which `TauCeti/NumberTheory/ModularForms/Twist/Basic.lean` places the twist `f ⊗ Φ` of `f`
by a function `Φ` modulo `d` at level `Γ₁(L)`. For instance the `2`-depletion of `Δ` has level
`Γ₁(4)`.

The twist by a Dirichlet character `ψ` uses its zero extension, so it already deletes the
coefficients at the indices sharing a prime with the modulus. Raising the modulus of `ψ` by a
prime `p` therefore deletes the multiples of `p` as well, and that is the `p`-depletion:

`f ⊗ ψ' = (f ⊗ ψ) - V_p U_p (f ⊗ ψ)`, for `ψ'` the character `ψ` read modulo `M p`.

Both sides are compared as functions on `ℍ`, since the two constructions land at their own
levels. If `ψ` is induced from a character `ψ₀` of modulus `r ∣ m`, write `m = r p₁ ⋯ pₛ` with
primes `pᵢ`. Applying the identity once for each `pᵢ`, the twist `f ⊗ ψ` is the iterated
depletion of `f ⊗ ψ₀` at `p₁, …, pₛ`. A depletion at a prime that already divides the modulus
changes nothing (`coe_depletion_twist_of_dvd`), and depleting twice at the same index is depleting
once (`coe_depletion_depletion`), so only the primes dividing `m` but not `r` act, each once. The
first case, `ψ₀ = 1` modulo `1`, says that the twist by the trivial character modulo `p` is the
`p`-depletion. It is not `f`: the trivial character modulo `2` has conductor `1`, but it vanishes
at the even integers.

## Main definitions

* `ModularForm.depletion`, `CuspForm.depletion`: the `d`-depletion `f - V_d U_d f`, from level
  `Γ₁(N)` to level `Γ₁(L)` for `N * d ∣ L` and `d * d ∣ L`.

## Main results

* `ModularForm.depletion_apply`: `(f - V_d U_d f)(τ) = f(τ) - (U_d f)(d τ)`.
* `CuspForm.coe_depletion`, `ModularForm.depletion_coe_cuspForm`: depletion commutes with the
  inclusion of cusp forms into modular forms.
* `ModularForm.qExpansion_depletion_coeff`, `CuspForm.qExpansion_depletion_coeff`: the depletion
  deletes the coefficients at the multiples of `d`.
* `ModularForm.coe_depletion_depletion`, `CuspForm.coe_depletion_depletion`: depletion is
  idempotent.
* `ModularForm.coe_twist_changeLevel_mul_eq_coe_depletion_twist`,
  `CuspForm.coe_twist_changeLevel_mul_eq_coe_depletion_twist`: raising the modulus of the character
  by a prime `p` replaces the twist by its `p`-depletion.
* `ModularForm.coe_depletion_twist_of_dvd`, `CuspForm.coe_depletion_twist_of_dvd`: depleting at a
  divisor `d ≠ 1` of the modulus of the character does not change the twist.
* `ModularForm.coe_twist_one_eq_coe_depletion`, `CuspForm.coe_twist_one_eq_coe_depletion`: the
  twist by the trivial character modulo a prime `p` is the `p`-depletion.

## References

* A. O. L. Atkin, W.-C. W. Li, *Twists of newforms and pseudo-eigenvalues of `W`-operators*,
  Invent. Math. 48 (1978), 221–243, §3.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.64.
-/

public noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GL2

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N L M d p : ℕ} {k : ℤ}

/-- The intermediate level `L / d` of the depletion is positive. -/
private lemma neZero_div [NeZero L] [NeZero d] (hdL : d * d ∣ L) : NeZero (L / d) :=
  ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos L) ((dvd_mul_right d d).trans hdL))
    (NeZero.pos d)).ne'⟩

/-! ### The depletion of a modular form -/

/-- **The `d`-depletion of a modular form**, `f - V_d U_d f`. For `f` a modular form for `Γ₁(N)`,
`N * d ∣ L` and `d * d ∣ L`, it reads `f` at the level `L / d`, which `d` divides, applies the
upper-triangular Hecke operator `U_d` there, raises the result by `V_d` to level `L`, and subtracts
it from `f` read at level `L`. Its `q`-expansion is that of `f` with the terms of index divisible by
`d` deleted (`qExpansion_depletion_coeff`). -/
def _root_.ModularForm.depletion [NeZero L] (d : ℕ) [NeZero d] (hNL : N * d ∣ L)
    (hdL : d * d ∣ L) (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    _root_.ModularForm ((Gamma1 L).map (mapGL ℝ)) k :=
  haveI := neZero_div (L := L) hdL
  _root_.ModularForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd ((dvd_mul_right N d).trans hNL)) f -
    ModularForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd
      (dvd_of_eq (Nat.mul_div_cancel' ((dvd_mul_right d d).trans hdL))))
      (heckeSlashUpperTriModularFormEnd k (Nat.dvd_div_of_mul_dvd hdL)
        (_root_.ModularForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd
          (Nat.dvd_div_of_mul_dvd (mul_comm N d ▸ hNL))) f))

/-- The defining formula of the depletion: `(f - V_d U_d f)(τ) = f(τ) - (U_d f)(d τ)`, where
`U_d f = ∑_{b < d} f ∣ [1, b; 0, d]` is `heckeSlashUpperTri k d f`. -/
@[simp]
lemma _root_.ModularForm.depletion_apply [NeZero L] [NeZero d] (hNL : N * d ∣ L)
    (hdL : d * d ∣ L) (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (τ : ℍ) :
    ModularForm.depletion d hNL hdL f τ = f τ - heckeSlashUpperTri k d f (scaleGL d • τ) := by
  simp [ModularForm.depletion]

/-- **The `q`-expansion of the depletion.** `aₙ(f - V_d U_d f)` is `0` when `d ∣ n` and `aₙ(f)`
otherwise. -/
theorem _root_.ModularForm.qExpansion_depletion_coeff [NeZero L] [NeZero d] (hNL : N * d ∣ L)
    (hdL : d * d ∣ L) (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion 1 (ModularForm.depletion d hNL hdL f)).coeff n =
      if d ∣ n then 0 else (qExpansion 1 f).coeff n := by
  have := neZero_div (L := L) hdL
  rw [ModularForm.depletion, FunLike.coe_sub,
    _root_.ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map L),
    map_sub, ModularForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map _),
    _root_.ModularForm.coe_restrict]
  split_ifs with hdn
  · rw [coe_heckeSlashUpperTriModularFormEnd,
      qExpansion_coeff_heckeSlashUpperTri' k d (one_mem_strictPeriods_Gamma1_map _) (NeZero.pos d),
      _root_.ModularForm.coe_restrict, Nat.mul_div_cancel' hdn, sub_self]
  · rw [sub_zero]

/-- **Depletion is idempotent**: depleting twice at `d` deletes the same coefficients as depleting
once. The two depletions are compared as functions, at their own levels. -/
theorem _root_.ModularForm.coe_depletion_depletion [NeZero L] {L' : ℕ} [NeZero L'] [NeZero d]
    (hNL : N * d ∣ L) (hdL : d * d ∣ L) (hLL' : L * d ∣ L') (hdL' : d * d ∣ L')
    (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(ModularForm.depletion d hLL' hdL' (ModularForm.depletion d hNL hdL f)) =
      ⇑(ModularForm.depletion d hNL hdL f) := by
  refine ModularFormClass.coe_eq_of_qExpansion_eq one_pos (one_mem_strictPeriods_Gamma1_map L')
    (one_mem_strictPeriods_Gamma1_map L) (PowerSeries.ext fun n ↦ ?_)
  simp only [ModularForm.qExpansion_depletion_coeff]
  split_ifs <;> rfl

/-! ### The depletion of a cusp form -/

/-- **The `d`-depletion of a cusp form**, `f - V_d U_d f`, from level `Γ₁(N)` to level `Γ₁(L)`
for `N * d ∣ L` and `d * d ∣ L`. Its underlying function is that of the depletion of `f` as a
modular form (`coe_depletion`). -/
def _root_.CuspForm.depletion [NeZero L] (d : ℕ) [NeZero d] (hNL : N * d ∣ L)
    (hdL : d * d ∣ L) (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    _root_.CuspForm ((Gamma1 L).map (mapGL ℝ)) k :=
  haveI := neZero_div (L := L) hdL
  _root_.CuspForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd ((dvd_mul_right N d).trans hNL)) f -
    CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd
      (dvd_of_eq (Nat.mul_div_cancel' ((dvd_mul_right d d).trans hdL))))
      (heckeSlashUpperTriCuspFormEnd k (Nat.dvd_div_of_mul_dvd hdL)
        (_root_.CuspForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd
          (Nat.dvd_div_of_mul_dvd (mul_comm N d ▸ hNL))) f))

/-- The depletion of a cusp form has the same underlying function as the depletion of `f` regarded
as a modular form. -/
@[simp]
lemma _root_.CuspForm.coe_depletion [NeZero L] [NeZero d] (hNL : N * d ∣ L) (hdL : d * d ∣ L)
    (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(CuspForm.depletion d hNL hdL f) =
      ⇑(ModularForm.depletion d hNL hdL (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  ext τ
  simp [CuspForm.depletion]

/-- The depletion of a cusp form, regarded as a modular form, is the depletion of the underlying
modular form. -/
theorem _root_.ModularForm.depletion_coe_cuspForm [NeZero L] [NeZero d] (hNL : N * d ∣ L)
    (hdL : d * d ∣ L) (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ModularForm.depletion d hNL hdL (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (CuspForm.depletion d hNL hdL f : _root_.ModularForm ((Gamma1 L).map (mapGL ℝ)) k) := by
  ext τ
  simp

/-- **The `q`-expansion of the depletion of a cusp form.** `aₙ(f - V_d U_d f)` is `0` when `d ∣ n`
and `aₙ(f)` otherwise. -/
theorem _root_.CuspForm.qExpansion_depletion_coeff [NeZero L] [NeZero d] (hNL : N * d ∣ L)
    (hdL : d * d ∣ L) (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion 1 (CuspForm.depletion d hNL hdL f)).coeff n =
      if d ∣ n then 0 else (qExpansion 1 f).coeff n := by
  rw [CuspForm.coe_depletion]
  exact ModularForm.qExpansion_depletion_coeff hNL hdL _ n

/-! ### Twists by imprimitive characters -/

/-- **Raising the modulus of the character by a prime depletes the twist.** For a Dirichlet
character `ψ` modulo `M` and a prime `p`, the twist of `f` by `ψ` read modulo `M * p` is the
`p`-depletion of the twist of `f` by `ψ`: the zero extension modulo `M * p` vanishes at the
multiples of `p` and agrees with `ψ` elsewhere. The two sides are compared as functions, each at
its own level. -/
theorem _root_.ModularForm.coe_twist_changeLevel_mul_eq_coe_depletion_twist [NeZero M]
    [NeZero p] {L' L'' : ℕ} [NeZero L''] (hp : p.Prime) (ψ : DirichletCharacter ℂ M)
    (hNL : N * M ∣ L) (hML : M * M ∣ L) (hNL' : N * (M * p) ∣ L') (hML' : M * p * (M * p) ∣ L')
    (hLL'' : L * p ∣ L'') (hpL'' : p * p ∣ L'')
    (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(ModularForm.twist (DirichletCharacter.changeLevel (dvd_mul_right M p) ψ) hNL' hML' f) =
      ⇑(ModularForm.depletion p hLL'' hpL'' (ModularForm.twist ψ hNL hML f)) := by
  refine ModularFormClass.coe_eq_of_qExpansion_eq one_pos (one_mem_strictPeriods_Gamma1_map L')
    (one_mem_strictPeriods_Gamma1_map L'') (PowerSeries.ext fun n ↦ ?_)
  rw [ModularForm.qExpansion_twist_coeff, ModularForm.qExpansion_depletion_coeff,
    ModularForm.qExpansion_twist_coeff,
    DirichletCharacter.changeLevel_mul_prime_natCast hp]
  split_ifs <;> simp

/-- **Depleting at a divisor of the modulus does not change the twist.** If `d ∣ M` and `d ≠ 1`,
the twist of `f` by a character modulo `M` already vanishes at the multiples of `d`, which share
the factor `d` with `M`. -/
theorem _root_.ModularForm.coe_depletion_twist_of_dvd [NeZero M] [NeZero d] {L' : ℕ} [NeZero L']
    (hd : d ≠ 1) (hdM : d ∣ M) (ψ : DirichletCharacter ℂ M) (hNL : N * M ∣ L)
    (hML : M * M ∣ L) (hLL' : L * d ∣ L') (hdL' : d * d ∣ L')
    (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(ModularForm.depletion d hLL' hdL' (ModularForm.twist ψ hNL hML f)) =
      ⇑(ModularForm.twist ψ hNL hML f) := by
  refine ModularFormClass.coe_eq_of_qExpansion_eq one_pos (one_mem_strictPeriods_Gamma1_map L')
    (one_mem_strictPeriods_Gamma1_map L) (PowerSeries.ext fun n ↦ ?_)
  rw [ModularForm.qExpansion_depletion_coeff]
  split_ifs with hdn
  · rw [ModularForm.qExpansion_twist_coeff,
      ψ.map_nonunit (fun hu ↦ hd ((Nat.Coprime.coprime_dvd_right hdM
        ((ZMod.isUnit_iff_coprime n M).mp hu)).symm.eq_one_of_dvd hdn)), zero_mul]
  · rfl

/-- **The twist by the trivial character modulo a prime `p` is the `p`-depletion.** The trivial
character modulo `p` has conductor `1`, but its zero extension vanishes at the multiples of `p`,
so the twist deletes those coefficients of `f` and keeps the others. -/
theorem _root_.ModularForm.coe_twist_one_eq_coe_depletion [NeZero p] {L' : ℕ}
    [NeZero L'] (hp : p.Prime) (hNL : N * p ∣ L) (hpL : p * p ∣ L) (hNL' : N * p ∣ L')
    (hpL' : p * p ∣ L') (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(ModularForm.twist (1 : DirichletCharacter ℂ p) hNL hpL f) =
      ⇑(ModularForm.depletion p hNL' hpL' f) := by
  refine ModularFormClass.coe_eq_of_qExpansion_eq one_pos (one_mem_strictPeriods_Gamma1_map L)
    (one_mem_strictPeriods_Gamma1_map L') (PowerSeries.ext fun n ↦ ?_)
  rw [ModularForm.qExpansion_twist_coeff, ModularForm.qExpansion_depletion_coeff,
    DirichletCharacter.one_natCast]
  split_ifs with hn hpn hpn
  · exact absurd (hn.symm.eq_one_of_dvd hpn) hp.one_lt.ne'
  · rw [one_mul]
  · rw [zero_mul]
  · exact absurd ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn))) hn

/-- **Depletion of cusp forms is idempotent.** -/
theorem _root_.CuspForm.coe_depletion_depletion [NeZero L] {L' : ℕ} [NeZero L'] [NeZero d]
    (hNL : N * d ∣ L) (hdL : d * d ∣ L) (hLL' : L * d ∣ L') (hdL' : d * d ∣ L')
    (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(CuspForm.depletion d hLL' hdL' (CuspForm.depletion d hNL hdL f)) =
      ⇑(CuspForm.depletion d hNL hdL f) := by
  rw [CuspForm.coe_depletion, CuspForm.coe_depletion]
  refine (congrArg _ (_root_.ModularForm.ext fun τ ↦ ?_)).trans
    (ModularForm.coe_depletion_depletion hNL hdL hLL' hdL' _)
  simp

/-- **Depleting a twisted cusp form at a divisor of the modulus does not change it.** The
cusp-form reading of `ModularForm.coe_depletion_twist_of_dvd`. -/
theorem _root_.CuspForm.coe_depletion_twist_of_dvd [NeZero M] [NeZero d] {L' : ℕ} [NeZero L']
    (hd : d ≠ 1) (hdM : d ∣ M) (ψ : DirichletCharacter ℂ M) (hNL : N * M ∣ L)
    (hML : M * M ∣ L) (hLL' : L * d ∣ L') (hdL' : d * d ∣ L')
    (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(CuspForm.depletion d hLL' hdL' (CuspForm.twist ψ hNL hML f)) =
      ⇑(CuspForm.twist ψ hNL hML f) := by
  rw [CuspForm.coe_depletion, CuspForm.coe_twist, ← ModularForm.twist_coe_cuspForm]
  exact ModularForm.coe_depletion_twist_of_dvd hd hdM ψ hNL hML hLL' hdL' _

/-- **Raising the modulus of the character by a prime depletes the twist of a cusp form.** The
cusp-form reading of `ModularForm.coe_twist_changeLevel_mul_eq_coe_depletion_twist`. -/
theorem _root_.CuspForm.coe_twist_changeLevel_mul_eq_coe_depletion_twist [NeZero M]
    [NeZero p] {L' L'' : ℕ} [NeZero L''] (hp : p.Prime) (ψ : DirichletCharacter ℂ M)
    (hNL : N * M ∣ L) (hML : M * M ∣ L) (hNL' : N * (M * p) ∣ L') (hML' : M * p * (M * p) ∣ L')
    (hLL'' : L * p ∣ L'') (hpL'' : p * p ∣ L'')
    (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(CuspForm.twist (DirichletCharacter.changeLevel (dvd_mul_right M p) ψ) hNL' hML' f) =
      ⇑(CuspForm.depletion p hLL'' hpL'' (CuspForm.twist ψ hNL hML f)) := by
  rw [CuspForm.coe_twist, CuspForm.coe_depletion, ← ModularForm.twist_coe_cuspForm]
  exact ModularForm.coe_twist_changeLevel_mul_eq_coe_depletion_twist hp ψ hNL hML hNL' hML'
    hLL'' hpL'' _

/-- **The twist of a cusp form by the trivial character modulo a prime `p` is its
`p`-depletion.** -/
theorem _root_.CuspForm.coe_twist_one_eq_coe_depletion [NeZero p] {L' : ℕ}
    [NeZero L'] (hp : p.Prime) (hNL : N * p ∣ L) (hpL : p * p ∣ L) (hNL' : N * p ∣ L')
    (hpL' : p * p ∣ L') (f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(CuspForm.twist (1 : DirichletCharacter ℂ p) hNL hpL f) =
      ⇑(CuspForm.depletion p hNL' hpL' f) := by
  rw [CuspForm.coe_twist, CuspForm.coe_depletion]
  exact ModularForm.coe_twist_one_eq_coe_depletion hp hNL hpL hNL' hpL' _

end TauCeti
