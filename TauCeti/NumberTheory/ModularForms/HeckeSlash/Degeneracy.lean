/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Diagonal.QExpansion
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.LevelSupported
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Recurrence
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Periodic
public import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# `Tₚ` and the degeneracy operator `V_d`

The degeneracy operator `V_d : S_k(Γ₁(M)) → S_k(Γ₁(N))`, `(V_d f) τ = f (d τ)`, raises the level
along `d * M ∣ N`. This file proves that it commutes with the Hecke operator `Tₚ` at every prime
`p` coprime to `N`, and computes `Tₚ (V_d f)` at the primes dividing `N`. These are the inputs to
the statement that `Tₚ` preserves the old subspace at every prime, and to the stability of the
new subspace at primes coprime to `N`.

## The shape of the proof at primes coprime to the level

`Tₚ` at a prime is `heckeSlashUpperTri k p f + (⟨p⟩ f) ∣[k] diag(p, 1)`, and `V_d` is — up to the
normalising scalar `d ^ (k - 1)` — the slash by `diag(d, 1)`. So the theorem splits into a
statement about each summand, and each is proved in the `diag(d, 1)`-slash form, where the
normalising scalars are absent:

* the upper-triangular sum, which commutes by `heckeSlashUpperTri_slash_scaleRep_comm`
  (`HeckeSlash/UpperTri/Periodic.lean`): the two slashes do **not** commute termwise, but the
  part of `d b` that leaves the range `b < p` becomes a shift `T ^ q`, which invariance under `T`
  absorbs, and coprimality of `d` and `p` makes the surviving index a permutation of `Fin p`. The
  `Γ₁(M)`-invariance of `f` supplies that hypothesis, through `slash_mapGL_T`.
* the diamond term, which commutes because natural diagonal matrices do —
  `HeckeRing.GLn.natDiagGL_comm` — once `TauCeti.CuspForm.diamondOpCusp_levelRaise` has moved
  `⟨p⟩` across `V_d`.

## Main results

* `HeckeRing.GL2.heckeTCuspNat_levelRaise`: **`Tₚ (V_d f) = V_d (Tₚ f)`** for `p` prime and
  coprime to the raised level `N`.
* `HeckeRing.GL2.heckeTCuspNat_levelRaise_mul`: **`T_n (V_{n e} f) = V_e f`** whenever
  `n * e * M ∣ N`; at a prime this is `Uₚ V_p = 1`.
* `HeckeRing.GL2.heckeTCuspNat_levelRaise_of_primeFactors_subset`:
  **`T_n (V_d f) = V_d (T_n f)`** when every prime factor of `n` divides `M` and `n` is coprime
  to `d`.
* `HeckeRing.GL2.heckeTCuspNat_levelRaise_eq_sub`:
  **`Tₚ (V_d f) = V_d (Tₚ f) - p ^ (k - 1) • V_{d p} (⟨p⟩ f)`** for a prime `p` coprime to `d`
  with `d * p * M ∣ N`.

## The primes dividing the level

At an index `n` all of whose prime factors divide `N`, the operator `T_n` on `S_k(Γ₁(N))` reads
off the coefficients `a_{n m}` (`qExpansion_coeff_heckeTCuspNat_of_primeFactors_subset`), and
`aₘ(V_d f) = a_{m/d}(f)` when `d ∣ m` and `0` otherwise. The three formulas above are identities
of `q`-expansions, turned into identities of cusp forms by `CuspForm.qExpansion_injective`. In
the last one the diamond term of the level-`M` recurrence
`aₘ(Tₚ f) = a_{p m}(f) + p ^ (k - 1) a_{m/p}(⟨p⟩ f)` there is what the correction
`V_{d p} (⟨p⟩ f)` removes.

## Provenance

The mathematics follows `heckeT_p_all_levelRaise_comm` and its supporting lemmas in the AINTLIB
[`LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) project, file
`LeanModularForms/HeckeRIngs/GL2/Newforms/LevelRaiseComm.lean`, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck, lines 45–311.
No proof code is transcribed: that development works with bare coset functions `heckeT_p_ut` and
`heckeT_p_fun` and a `Γ₁`-shift matrix of its own, and splits `Tₚ` on whether `p` divides the
level, whereas here `Tₚ` is the single-formula operator of `HeckeSlash/Operators.lean`, the shift is
Mathlib's `ModularGroup.T`, and the level-raise is the general `TauCeti.CuspForm.levelRaise` of
`ModularForms/Degeneracy.lean`, stated at `d * M ∣ N` rather than at `d * M = N`.
The reindexing half of that argument (source lines 66–190) lives with the upper-triangular sum in
`HeckeSlash/UpperTri/Periodic.lean`, which carries its own note.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.6.2.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GLn TauCeti

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {M d N p : ℕ} (k : ℤ)

/-! ### The shift matrix -/

/-- A `Γ₁(M)`-invariant function is fixed by the rational slash of `T`. -/
private lemma slash_mapGL_T {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma1 M).map (mapGL ℝ), f ∣[k] γ = f) :
    f ∣[k] (mapGL ℚ ModularGroup.T : GL (Fin 2) ℚ) = f :=
  ModularForm.slash_eq_of_mem_map_mapGL hf
    (Subgroup.mem_map_of_mem _ (zpow_one ModularGroup.T ▸ T_zpow_mem_Gamma1 M 1))

/-! ### `Tₚ` and `V_d` -/

/-- **`Tₚ` commutes with the degeneracy operator `V_d`.** For `d * M ∣ N` and a prime `p` coprime
to `N`, raising the level of `f` and then applying `Tₚ` at level `N` agrees with applying `Tₚ` at
level `M` and then raising the level.

Coprimality is not decoration: at `p ∣ N` the diamond term of `Tₚ` vanishes at level `N` but need
not vanish at level `M`, and `b ↦ d b mod p` stops being a permutation once `p ∣ d`. -/
@[grind =]
theorem heckeTCuspNat_levelRaise (hdvd : d * M ∣ N) (hp : p.Prime)
    (hpN : Nat.Coprime p N) (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero N := ⟨fun hN ↦ hp.ne_one (by simpa [hN] using hpN)⟩
    haveI : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd hdvd)
    haveI : NeZero M := NeZero.of_dvd (dvd_of_mul_left_dvd hdvd)
    haveI : NeZero p := ⟨hp.ne_zero⟩
    heckeTCuspNat k p (CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) f) =
      CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) (heckeTCuspNat k p f) := by
  have : NeZero N := ⟨fun hN ↦ hp.ne_one (by simpa [hN] using hpN)⟩
  have : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd hdvd)
  have : NeZero M := NeZero.of_dvd (dvd_of_mul_left_dvd hdvd)
  have : NeZero p := ⟨hp.ne_zero⟩
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hMdvd : M ∣ N := dvd_of_mul_left_dvd hdvd
  have hpM : Nat.Coprime p M := hpN.coprime_dvd_right hMdvd
  have hpd : Nat.Coprime p d := hpN.coprime_dvd_right ((dvd_mul_right d M).trans hdvd)
  have hf : ∀ γ ∈ (Gamma1 M).map (mapGL ℝ), ⇑f ∣[k] γ = ⇑f :=
    fun γ hγ ↦ SlashInvariantFormClass.slash_action_eq f γ hγ
  have hunits : ZMod.unitsMap hMdvd (ZMod.unitOfCoprime p hpN) = ZMod.unitOfCoprime p hpM := by
    ext
    simp [ZMod.unitsMap_def, ZMod.coe_unitOfCoprime]
  have hscale : ∀ g : ℍ → ℂ, g ∣[k] scaleGL d = g ∣[k] (scaleRep d : GL (Fin 2) ℚ) :=
    fun g ↦ by rw [ModularForm.rat_slash, scaleRep_def, map_natDiagGL_d_one_eq_scaleGL]
  refine DFunLike.coe_injective ?_
  simp only [coe_heckeTCuspNat_prime k hp, CuspForm.coe_levelRaise,
    diamondOpCuspNat_of_coprime k hpN, diamondOpCuspNat_of_coprime k hpM,
    CuspForm.diamondOpCusp_levelRaise hdvd k (ZMod.unitOfCoprime p hpN) f, hunits,
    SlashAction.add_slash, smul_add, heckeSlashUpperTri_smul, hscale]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [heckeSlashUpperTri_slash_scaleRep_comm k p hdpos hp.pos hpd.symm (slash_mapGL_T k hf)]
  · rw [ModularForm.rat_smul_slash_of_det_pos k (det_scaleRep_pos p), ← SlashAction.slash_mul,
      ← SlashAction.slash_mul, scaleRep_def, scaleRep_def, natDiagGL_comm]

/-! ### `T_n` and `V_d` at indices supported on the level -/

/-- **`T_n` undoes the degeneracy operator `V_n`**: for `n * e * M ∣ N`,
`T_n (V_{n e} g) = V_e g` at level `N`. Every prime factor of `n` divides `N`, so `T_n` reads
off the coefficients `a_{n m}`, and those of `V_{n e} g` are the coefficients of `V_e g`.
At `e = 1` this is the classical `U_p V_p = 1`. -/
theorem heckeTCuspNat_levelRaise_mul {n e : ℕ} [NeZero N] (hdvd : n * e * M ∣ N)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero n := NeZero.of_dvd ((dvd_mul_right n e).trans (dvd_of_mul_right_dvd hdvd))
    haveI : NeZero e := NeZero.of_dvd (dvd_of_mul_left_dvd (dvd_of_mul_right_dvd hdvd))
    heckeTCuspNat k n
        (CuspForm.levelRaise (n * e) (Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) g) =
      CuspForm.levelRaise e (Gamma1_map_le_conjAct_scaleGL_of_dvd
        ((mul_dvd_mul_right (dvd_mul_left e n) M).trans hdvd)) g := by
  have : NeZero n := NeZero.of_dvd ((dvd_mul_right n e).trans (dvd_of_mul_right_dvd hdvd))
  have : NeZero e := NeZero.of_dvd (dvd_of_mul_left_dvd (dvd_of_mul_right_dvd hdvd))
  have hn : n.primeFactors ⊆ N.primeFactors := Nat.primeFactors_mono
    ((dvd_mul_right n e).trans (dvd_of_mul_right_dvd hdvd)) (NeZero.ne N)
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  refine CuspForm.qExpansion_injective one_pos (one_mem_strictPeriods_Gamma1_map N)
    (PowerSeries.ext fun m ↦ ?_)
  simp only [qExpansion_coeff_heckeTCuspNat_of_primeFactors_subset k n hn,
    CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map M)
      (one_mem_strictPeriods_Gamma1_map N), Nat.mul_dvd_mul_iff_left hn0,
    Nat.mul_div_mul_left _ _ hn0]

/-- **`T_n` commutes with `V_d` when `n` is supported on the source level and prime to `d`**:
for `d * M ∣ N`, `n` coprime to `d` and every prime factor of `n` dividing `M`,
`T_n (V_d g) = V_d (T_n g)`. At both levels `T_n` reads off the coefficients `a_{n m}`, and
coprimality makes `d ∣ n m` equivalent to `d ∣ m`.

This is the bad-index counterpart of `heckeTCuspNat_levelRaise`. -/
theorem heckeTCuspNat_levelRaise_of_primeFactors_subset {n : ℕ} [NeZero N] [NeZero n]
    (hdvd : d * M ∣ N) (hn : n.primeFactors ⊆ M.primeFactors) (hnd : Nat.Coprime n d)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd hdvd)
    haveI : NeZero M := NeZero.of_dvd (dvd_of_mul_left_dvd hdvd)
    heckeTCuspNat k n (CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) g) =
      CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) (heckeTCuspNat k n g) := by
  have : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd hdvd)
  have : NeZero M := NeZero.of_dvd (dvd_of_mul_left_dvd hdvd)
  have hnN : n.primeFactors ⊆ N.primeFactors :=
    hn.trans (Nat.primeFactors_mono (dvd_of_mul_left_dvd hdvd) (NeZero.ne N))
  refine CuspForm.qExpansion_injective one_pos (one_mem_strictPeriods_Gamma1_map N)
    (PowerSeries.ext fun m ↦ ?_)
  simp only [qExpansion_coeff_heckeTCuspNat_of_primeFactors_subset k n hnN,
    qExpansion_coeff_heckeTCuspNat_of_primeFactors_subset k n hn,
    CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map M)
      (one_mem_strictPeriods_Gamma1_map N), hnd.symm.dvd_mul_left]
  split_ifs with hdm
  · rw [Nat.mul_div_assoc n hdm]
  · rfl

/-- **`Tₚ` on `V_d g` at a prime dividing the level but not `d`**: for `p` prime to `d` with
`d * p * M ∣ N`,
`Tₚ (V_d g) = V_d (Tₚ g) - p ^ (k - 1) • V_{d p} (⟨p⟩ g)`.
At level `N` the operator `Tₚ` is `Uₚ`, reading off `a_{p m}`; at level `M` the diamond term of
the recurrence for `Tₚ` is exactly what the degeneracy image `V_{d p} (⟨p⟩ g)` cancels. When
`p ∣ M` that diamond term is `0`, and this reduces to
`heckeTCuspNat_levelRaise_of_primeFactors_subset`. -/
theorem heckeTCuspNat_levelRaise_eq_sub [NeZero N] (hp : p.Prime)
    (hpd : Nat.Coprime p d) (hdvd : d * p * M ∣ N)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : NeZero d := NeZero.of_dvd ((dvd_mul_right d p).trans (dvd_of_mul_right_dvd hdvd))
    haveI : NeZero M := NeZero.of_dvd (dvd_of_mul_left_dvd hdvd)
    heckeTCuspNat k p (CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd
        ((mul_dvd_mul_right (dvd_mul_right d p) M).trans hdvd)) g) =
      CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd
          ((mul_dvd_mul_right (dvd_mul_right d p) M).trans hdvd)) (heckeTCuspNat k p g) -
        (p : ℂ) ^ (k - 1) • CuspForm.levelRaise (d * p)
          (Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) (diamondOpCuspNat k p g) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero d := NeZero.of_dvd ((dvd_mul_right d p).trans (dvd_of_mul_right_dvd hdvd))
  have : NeZero M := NeZero.of_dvd (dvd_of_mul_left_dvd hdvd)
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hpN : p.primeFactors ⊆ N.primeFactors := Nat.primeFactors_mono
    ((dvd_mul_left p d).trans (dvd_of_mul_right_dvd hdvd)) (NeZero.ne N)
  have hΓN := one_mem_strictPeriods_Gamma1_map N
  have hΓM := one_mem_strictPeriods_Gamma1_map M
  refine CuspForm.qExpansion_injective one_pos hΓN (PowerSeries.ext fun m ↦ ?_)
  dsimp only
  rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos hΓN, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos hΓN, map_sub, map_smul, smul_eq_mul,
    qExpansion_coeff_heckeTCuspNat_of_primeFactors_subset k p hpN,
    CuspForm.qExpansion_levelRaise_coeff hΓM hΓN, CuspForm.qExpansion_levelRaise_coeff hΓM hΓN,
    CuspForm.qExpansion_levelRaise_coeff hΓM hΓN]
  by_cases hdm : d ∣ m
  · -- `m = d t`: both sides are the `Tₚ` recurrence at level `M`, read at `t`
    obtain ⟨t, rfl⟩ := hdm
    have hpdt : p * (d * t) / d = p * t := by rw [Nat.mul_left_comm, Nat.mul_div_cancel_left _ hd0]
    have hdpt : d ∣ p * (d * t) := dvd_mul_of_dvd_right (dvd_mul_right d t) p
    simp only [hdpt, dvd_mul_right d t, ↓reduceIte, hpdt, heckeTCuspNat_def,
      qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime k hp g,
      Nat.mul_dvd_mul_iff_left hd0, Nat.mul_div_cancel_left t hd0, Nat.mul_div_mul_left t p hd0]
    split_ifs <;> ring
  · -- `d ∤ m`: every term vanishes, since `d` is prime to `p`
    have hdpm : ¬ d * p ∣ m := fun h ↦ hdm ((dvd_mul_right d p).trans h)
    have hdpm' : ¬ d ∣ p * m := by
      rwa [hpd.symm.dvd_mul_left]
    simp [hdm, hdpm, hdpm']

end HeckeRing.GL2
