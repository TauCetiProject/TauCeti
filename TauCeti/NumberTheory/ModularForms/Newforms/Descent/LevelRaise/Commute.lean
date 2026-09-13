/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.Sum
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Diagonal.QExpansion
import TauCeti.Data.ZMod.OnePoint
import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Periodic
import TauCeti.NumberTheory.ModularForms.Newforms.Descent.LevelCommute

/-!
# The descent commutes with the level-raise

Miyake's Lemma 4.6.6 (2): for a prime `p ∣ N` and `l` coprime to `p`, the descent slash sum at
level `l N` of the level-raise `V_l f` of `f ∈ S_k(Γ₁(N), χ)` is the level-raise of the descent
slash sum of `f` at level `N`, provided `χ` is the pull-back of a character modulo `N / p`. The
upper-triangular members `!![1, b; 0, p]` of the two families are
matched by the permutation `b ↦ l b mod p` of the residues, and the extra members (present when
`p² ∤ N`) by conjugating the level-`l N` one back to level `N`, where the nebentypus shows the
two candidates give the same slash.

The identity is what lets the descent be computed piece by piece on the squarefree decomposition
(`Newforms/SquarefreeDecomposition.lean`): the pieces are level-raises `V_q F_q`, and the descent
of each is `V_q` of the descent of `F_q`, a form supported on the multiples of `q`. That is how
the coefficient formula of the descent, the core of Miyake's Lemma 4.6.14, is proved.

## Main results

* `TauCeti.descendSlash_coe_levelRaise_mul_left_of_comp_of_mem_modFormCharSpace`, and its cusp-form
  case `TauCeti.descendSlash_coe_levelRaise_mul_left_of_comp_of_mem_cuspFormCharSpace`:
  `descendSlash k p (l N) (V_l f) =
  l ^ (1 - k) • (descendSlash k p N f ∣[k] diag(l, 1))`, that is, `V_l` of the descent.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `eb9621e7bcb0ce220ad53983ec45d987cb5b9002`),
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/LevelCommute.lean`
(`level_commute_delta` and its `delta_*` helpers, `descendCosetList_slash_sum_rep_invariance`,
`extra_rep_levelRaise_bridge`). The source's `modularFormLevelRaise` is this repository's
`ModularForm.levelRaise`, its `levelRaiseConjOfDvd` is `conjScale`, and its explicit coset list is
the family `descendMatrix`; the statements are re-proved on those. The source's
`level_commute_delta` also assumes `l ∣ N / p`, which the argument does not use, so it is
dropped here.

## References

* [T. Miyake, *Modular forms*][miyake1989], Lemma 4.6.6.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GL2

open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti

variable {p l : ℕ} (k : ℤ)

/-- **An upper-triangular member of the family, after the level-raise.** For `f` of level `Γ₁(M)`,
`(V_l f) ∣[k] !![1, b; 0, p]` is `V_l` of `f ∣[k] !![1, l b mod p; 0, p]`: `diag(l, 1)` moves past
`!![1, b; 0, p]` at the cost of the shift `T ^ (l b div p)` (`scaleRep_mul_upperTriRep`), which
`f` absorbs. -/
private theorem coe_levelRaise_slash_upperTriRep_eq_smul_slash {M : ℕ} (hp : p.Prime)
    [NeZero l] (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (b : Fin p) :
    ⇑(ModularForm.levelRaise l (Gamma1_map_le_conjAct_scaleGL M l) f) ∣[k]
        (upperTriRep p b : GL (Fin 2) ℚ) =
      (l : ℂ) ^ (1 - k) •
        ((⇑f ∣[k] (upperTriRep p ⟨l * b % p, Nat.mod_lt _ hp.pos⟩ : GL (Fin 2) ℚ)) ∣[k]
          scaleGL l) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hqr : l * (b : ℕ) = l * b / p * p + l * b % p := (Nat.div_add_mod' (l * b) p).symm
  have hT : ⇑f ∣[k] mapGL ℝ (ModularGroup.T ^ (l * b / p)) = ⇑f :=
    SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _
      (zpow_natCast ModularGroup.T (l * b / p) ▸ T_zpow_mem_Gamma1 M (l * b / p)))
  rw [ModularForm.coe_levelRaise, ModularForm.rat_smul_slash_of_det_pos k (det_upperTriRep_pos p b),
    ModularForm.rat_slash, ModularForm.rat_slash, ← SlashAction.slash_mul,
    ← map_natDiagGL_d_one_eq_scaleGL, ← scaleRep_def, ← map_mul,
    scaleRep_mul_upperTriRep p (NeZero.pos l) b (Nat.mod_lt _ hp.pos) hqr, map_mul, map_mul,
    Matrix.SpecialLinearGroup.map_mapGL, SlashAction.slash_mul, hT, SlashAction.slash_mul]

/-- The level-`l N` extra matrix modulo `N / p`: its diagonal entries are `1`, and `c`, the
lower-left entry divided by `l`, is `0`. -/
private theorem descendExtraGamma_mul_left_mod_div {N : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) [NeZero l] (hpl : Nat.Coprime p l) {c : ℤ}
    (hc : descendExtraGamma p (l * N) 1 0 = l * c) :
    ((descendExtraGamma p (l * N) 0 0 : ℤ) : ZMod (N / p)) = 1 ∧
      ((descendExtraGamma p (l * N) 1 1 : ℤ) : ZMod (N / p)) = 1 ∧
        ((c : ℤ) : ZMod (N / p)) = 0 := by
  have hplN : p ∣ l * N := dvd_mul_of_dvd_right hpN l
  have hpsq' : ¬ p ^ 2 ∣ l * N := fun h ↦
    hpsq ((Nat.Coprime.pow_left 2 hpl).dvd_of_dvd_mul_left h)
  have hNlN : N / p ∣ l * N / p := by
    rw [Nat.mul_div_assoc l hpN]
    exact dvd_mul_left _ _
  have m₁ (i j : Fin 2) : ((descendExtraGamma p (l * N) i j : ℤ) : ZMod (l * N / p)) =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod (l * N / p))) i j := by
    simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast,
      Matrix.SpecialLinearGroup.coe_one] using
      congr_fun₂ (congrArg Subtype.val
        (descendExtraGamma_map_intCast_zmod_div_eq_one hp hplN hpsq')) i j
  have m₁' (i j : Fin 2) : ((descendExtraGamma p (l * N) i j : ℤ) : ZMod (N / p)) =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod (N / p))) i j := by
    have := congrArg (ZMod.castHom hNlN (ZMod (N / p))) (m₁ i j)
    rw [map_intCast] at this
    rw [this]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]
  refine ⟨by rw [m₁' 0 0, Matrix.one_apply_eq], by rw [m₁' 1 1, Matrix.one_apply_eq], ?_⟩
  have h10 : ((l * N / p : ℕ) : ℤ) ∣ l * c := by
    rw [← hc]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      (by rw [m₁ 1 0]; exact Matrix.one_apply_ne (by decide))
  rw [Nat.mul_div_assoc l hpN] at h10
  push_cast at h10
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    ((mul_dvd_mul_iff_left (Nat.cast_ne_zero.mpr (NeZero.ne l))).mp h10)

/-- The entries of the quotient of the conjugated level-`l N` extra matrix by the level-`N` one
that the residue computations read. -/
private theorem conjScale_descendExtraGamma_mul_inv_apply {N : ℕ} {c : ℤ}
    (hc : descendExtraGamma p (l * N) 1 0 = l * c) :
    (conjScale l (descendExtraGamma p (l * N)) c hc * (descendExtraGamma p N)⁻¹) 0 1 =
        descendExtraGamma p (l * N) 0 0 * (-descendExtraGamma p N 0 1) +
          (l : ℤ) * descendExtraGamma p (l * N) 0 1 * descendExtraGamma p N 0 0 ∧
      (conjScale l (descendExtraGamma p (l * N)) c hc * (descendExtraGamma p N)⁻¹) 1 0 =
        c * descendExtraGamma p N 1 1 +
          descendExtraGamma p (l * N) 1 1 * (-descendExtraGamma p N 1 0) ∧
      (conjScale l (descendExtraGamma p (l * N)) c hc * (descendExtraGamma p N)⁻¹) 1 1 =
        c * (-descendExtraGamma p N 0 1) +
          descendExtraGamma p (l * N) 1 1 * descendExtraGamma p N 0 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, coe_conjScale, Matrix.mul_apply, Fin.sum_univ_two]

/-- The quotient of the conjugated level-`l N` extra matrix by the level-`N` one has upper-right
entry `0` modulo `p`, and lower row `(0, 1)` modulo `N / p`. -/
private theorem conjScale_descendExtraGamma_mul_inv_mod {N : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) [NeZero l] (hpl : Nat.Coprime p l) {c : ℤ}
    (hc : descendExtraGamma p (l * N) 1 0 = l * c) :
    (((conjScale l (descendExtraGamma p (l * N)) c hc * (descendExtraGamma p N)⁻¹) 0 1 : ℤ) :
        ZMod p) = 0 ∧
      (((conjScale l (descendExtraGamma p (l * N)) c hc * (descendExtraGamma p N)⁻¹) 1 0 : ℤ) :
        ZMod (N / p)) = 0 ∧
      (((conjScale l (descendExtraGamma p (l * N)) c hc * (descendExtraGamma p N)⁻¹) 1 1 : ℤ) :
        ZMod (N / p)) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hplN : p ∣ l * N := dvd_mul_of_dvd_right hpN l
  have hpsq' : ¬ p ^ 2 ∣ l * N := fun h ↦
    hpsq ((Nat.Coprime.pow_left 2 hpl).dvd_of_dvd_mul_left h)
  obtain ⟨h00, h11, hcN⟩ := descendExtraGamma_mul_left_mod_div hp hpN hpsq hpl hc
  have e₁ (i j : Fin 2) : ((descendExtraGamma p (l * N) i j : ℤ) : ZMod p) =
      ((ModularGroup.S i j : ℤ) : ZMod p) := by
    simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast] using
      congr_fun₂ (congrArg Subtype.val (descendExtraGamma_map_intCast_zmod_eq_S hp hplN hpsq'))
        i j
  have e₂ (i j : Fin 2) : ((descendExtraGamma p N i j : ℤ) : ZMod p) =
      ((ModularGroup.S i j : ℤ) : ZMod p) := by
    simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast] using
      congr_fun₂ (congrArg Subtype.val (descendExtraGamma_map_intCast_zmod_eq_S hp hpN hpsq)) i j
  have m₂ (i j : Fin 2) : ((descendExtraGamma p N i j : ℤ) : ZMod (N / p)) =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod (N / p))) i j := by
    simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast,
      Matrix.SpecialLinearGroup.coe_one] using
      congr_fun₂ (congrArg Subtype.val (descendExtraGamma_map_intCast_zmod_div_eq_one hp hpN hpsq))
        i j
  obtain ⟨d01, d10, d11⟩ := conjScale_descendExtraGamma_mul_inv_apply (N := N) hc
  refine ⟨?_, ?_, ?_⟩
  · rw [d01]
    push_cast
    rw [e₁ 0 0, e₂ 0 0]
    simp [ModularGroup.coe_S]
  · rw [d10]
    push_cast
    rw [hcN, h11, m₂ 1 0, Matrix.one_apply_ne (by decide)]
    ring
  · rw [d11]
    push_cast
    rw [hcN, h11, m₂ 0 0, Matrix.one_apply_eq]
    ring

/-- **The two extra members give the same slash.** For `p ∥ N`, `l` coprime to `p`, and
`f ∈ S_k(Γ₁(N), χ)` with `χ` pulled back from `χ₀` modulo `N / p`: conjugating the level-`l N`
extra matrix `descendExtraGamma p (l N)` back to level `N` by `diag(l, 1)`, then slashing `f` by
`!![1, 0; 0, p]` times it, is the same as with the level-`N` extra matrix `descendExtraGamma p N`.
The quotient `δ` of the two candidates has upper-right entry `0` modulo `p` and lower row
`(0, 1)` modulo `N / p` (`conjScale_descendExtraGamma_mul_inv_mod`), so
`!![1, 0; 0, p] δ = β !![1, 0; 0, p]` with `β ∈ Γ₀(N)` of lower-right entry `1` modulo `N / p`, on
which the nebentypus is trivial. -/
private theorem slash_map_upperTriRep_zero_mul_mapGL_conjScale_eq {N : ℕ} (hp : p.Prime)
    (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N) [NeZero l] (hpl : Nat.Coprime p l)
    {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) {c : ℤ}
    (hc : descendExtraGamma p (l * N) 1 0 = l * c) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    ⇑f ∣[k] (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p ⟨0, NeZero.pos p⟩) *
        mapGL ℝ (conjScale l (descendExtraGamma p (l * N)) c hc)) =
      ⇑f ∣[k] (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p ⟨0, NeZero.pos p⟩) *
        mapGL ℝ (descendExtraGamma p N)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨hδ01, hδ10, hδ11⟩ := conjScale_descendExtraGamma_mul_inv_mod hp hpN hpsq hpl hc
  set δ : SL(2, ℤ) := conjScale l (descendExtraGamma p (l * N)) c hc * (descendExtraGamma p N)⁻¹
    with hδ
  clear_value δ
  -- `δ 0 0` is a unit modulo `p`, since `det δ = 1` and `δ 0 1 ≡ 0`
  have hA : IsUnit ((δ 0 0 : ℤ) : ZMod p) := by
    have hdet := congrArg (Int.cast : ℤ → ZMod p)
      (Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one δ)
    push_cast at hdet
    rw [hδ01, zero_mul, sub_zero] at hdet
    exact IsUnit.of_mul_eq_one _ hdet
  have hpc : (((p : ℤ) * δ 1 0 : ℤ) : ZMod N) = 0 := by
    obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hδ10
    have hpN' : ((p : ℤ) * ((N / p : ℕ) : ℤ)) = (N : ℤ) := by
      exact_mod_cast Nat.mul_div_cancel' hpN
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ht, ← mul_assoc, hpN']
    exact dvd_mul_right _ _
  -- `!![1, 0; 0, p] δ = β !![1, 0; 0, p]` with `β ∈ Γ₀(N)`: the offset stays `0` as `p ∣ δ 0 1`
  obtain ⟨β, hβ, hβ11, hfac⟩ :=
    exists_mem_Gamma0_upperTriRep_mul_of_isUnit (j := ⟨0, NeZero.pos p⟩) (by simpa using hA) hpc
  have hshift : upperTriShift p δ ⟨0, NeZero.pos p⟩ = ⟨0, NeZero.pos p⟩ :=
    (upperTriShift_eq_iff (by simpa using hA)).mpr (by simp [hδ01])
  rw [hshift] at hβ11 hfac
  have hfβ : ⇑f ∣[k] mapGL ℝ β = ⇑f :=
    slash_mapGL_eq_self_of_comp_of_mem_modFormCharSpace (Nat.div_dvd_of_dvd hpN) hcomp hf hβ
      (by rw [hβ11]; simpa using hδ11)
  have hfacR := congrArg (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)) hfac
  rw [map_mul, map_mul, map_mapGL, map_mapGL] at hfacR
  have hδγ : conjScale l (descendExtraGamma p (l * N)) c hc = δ * descendExtraGamma p N := by
    rw [hδ, inv_mul_cancel_right]
  rw [hδγ, map_mul, ← mul_assoc, hfacR, mul_assoc, SlashAction.slash_mul, hfβ]

/-- **Multiplication by `l` on the descent's index set.** On the `p` upper-triangular members it
is the permutation `mulModEquiv` of the residues modulo `p`; the extra member, when there is
one, is fixed — read through `descendIndexEquiv`, it is the permutation of `OnePoint (ZMod p)`
fixing `∞`, which for the prime `p` here is the projective line over `ZMod p`. -/
private noncomputable def descendIndexMulPerm (hp : p.Prime) (hpl : Nat.Coprime p l) (N : ℕ) :
    Equiv.Perm (Fin (descendMatrixCount p N)) :=
  haveI : NeZero p := ⟨hp.ne_zero⟩
  if h : p ^ 2 ∣ N then
    (finCongr (descendMatrixCount_of_sq_dvd h)).trans
      ((mulModEquiv p hpl.symm).trans (finCongr (descendMatrixCount_of_sq_dvd h).symm))
  else
    (descendIndexEquiv p N h).symm.permCongr (onePointMulPerm p hpl.symm)

/-- **The index map between the two descent families**: the two families have the same size
(`descendMatrixCount_mul_left_of_coprime`), and the level-`l N` member at an index is the
level-`N` member at `l` times it. -/
private noncomputable def descendIndexMulEquiv (hp : p.Prime) (hpl : Nat.Coprime p l) (N : ℕ) :
    Fin (descendMatrixCount p (l * N)) ≃ Fin (descendMatrixCount p N) :=
  (finCongr (descendMatrixCount_mul_left_of_coprime hpl N)).trans (descendIndexMulPerm hp hpl N)

private theorem val_descendIndexMulPerm_of_lt (hp : p.Prime) (hpl : Nat.Coprime p l) (N : ℕ)
    {w : Fin (descendMatrixCount p N)} (hw : w.val < p) :
    (descendIndexMulPerm hp hpl N w).val = l * w % p := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcount : p ≤ descendMatrixCount p N := by
    by_cases h' : p ^ 2 ∣ N
    · exact le_of_eq (descendMatrixCount_of_sq_dvd h').symm
    · exact (descendMatrixCount_of_not_sq_dvd h') ▸ Nat.le_succ p
  have hmod : l * (w : ℕ) % p < descendMatrixCount p N :=
    lt_of_lt_of_le (Nat.mod_lt _ hp.pos) hcount
  rw [descendIndexMulPerm]
  split
  · simp
  · rename_i h
    rw [Equiv.permCongr_apply, Equiv.symm_symm, descendIndexEquiv_apply_of_lt h hw,
      onePointMulPerm_coe, descendIndexEquiv_symm_coe_val]
    rw [← Nat.cast_mul, ZMod.val_natCast]

private theorem val_descendIndexMulPerm_of_le (hp : p.Prime) (hpl : Nat.Coprime p l) (N : ℕ)
    {w : Fin (descendMatrixCount p N)} (hw : p ≤ w.val) :
    (descendIndexMulPerm hp hpl N w).val = w.val := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hlt := w.isLt
  have h : ¬ p ^ 2 ∣ N := by
    intro hd
    have := descendMatrixCount_of_sq_dvd (p := p) (N := N) hd
    omega
  have hcntN := descendMatrixCount_of_not_sq_dvd (p := p) (N := N) h
  have hwp : (w : ℕ) = p := by omega
  rw [descendIndexMulPerm]
  split
  · rename_i hsq
    exact absurd hsq h
  · rw [Equiv.permCongr_apply, Equiv.symm_symm, descendIndexEquiv_apply_of_le h hw,
      onePointMulPerm_infty, descendIndexEquiv_symm_infty_val, hwp]

private theorem val_descendIndexMulEquiv_of_lt (hp : p.Prime) (hpl : Nat.Coprime p l) (N : ℕ)
    {v : Fin (descendMatrixCount p (l * N))} (hv : v.val < p) :
    (descendIndexMulEquiv hp hpl N v).val = l * v % p :=
  val_descendIndexMulPerm_of_lt hp hpl N (w := finCongr _ v) hv

private theorem val_descendIndexMulEquiv_of_le (hp : p.Prime) (hpl : Nat.Coprime p l) (N : ℕ)
    {v : Fin (descendMatrixCount p (l * N))} (hv : p ≤ v.val) :
    (descendIndexMulEquiv hp hpl N v).val = v.val :=
  val_descendIndexMulPerm_of_le hp hpl N (w := finCongr _ v) hv

/-- An upper-triangular member of the level-`l N` family, on `V_l f`, is `V_l` of the matching
member of the level-`N` family on `f`. -/
private theorem coe_levelRaise_slash_descendMatrix_of_lt {N : ℕ} (hp : p.Prime)
    (hpl : Nat.Coprime p l) [NeZero l] (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    {v : Fin (descendMatrixCount p (l * N))} (hv : v.val < p) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    ⇑(ModularForm.levelRaise l (Gamma1_map_le_conjAct_scaleGL N l) f) ∣[k]
        descendMatrix p (l * N) v =
      (l : ℂ) ^ (1 - k) •
        ((⇑f ∣[k] descendMatrix p N (descendIndexMulEquiv hp hpl N v)) ∣[k] scaleGL l) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hσ : (descendIndexMulEquiv hp hpl N v).val < p :=
    (val_descendIndexMulEquiv_of_lt hp hpl N hv).symm ▸ Nat.mod_lt _ hp.pos
  rw [descendMatrix_of_lt hv, descendMatrix_of_lt hσ, ← ModularForm.rat_slash,
    ← ModularForm.rat_slash, coe_levelRaise_slash_upperTriRep_eq_smul_slash k hp f ⟨v.val, hv⟩]
  congr 4
  exact Fin.ext (val_descendIndexMulEquiv_of_lt hp hpl N hv).symm

/-- The extra member of the level-`l N` family, on `V_l f`, is `V_l` of the extra member of the
level-`N` family on `f`. -/
private theorem coe_levelRaise_slash_descendMatrix_of_le {N : ℕ} (hp : p.Prime)
    (hpN : p ∣ N) [NeZero l] (hpl : Nat.Coprime p l) {χ : (ZMod N)ˣ →* ℂˣ}
    {χ₀ : (ZMod (N / p))ˣ →* ℂˣ} (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ)
    {v : Fin (descendMatrixCount p (l * N))} (hv : p ≤ v.val) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    ⇑(ModularForm.levelRaise l (Gamma1_map_le_conjAct_scaleGL N l) f) ∣[k]
        descendMatrix p (l * N) v =
      (l : ℂ) ^ (1 - k) •
        ((⇑f ∣[k] descendMatrix p N (descendIndexMulEquiv hp hpl N v)) ∣[k] scaleGL l) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hpsq : ¬ p ^ 2 ∣ N := fun h ↦ by
    have h1 := descendMatrixCount_of_sq_dvd h
    have h2 := lt_of_lt_of_eq v.isLt (descendMatrixCount_mul_left_of_coprime hpl N)
    omega
  have hplN : p ∣ l * N := dvd_mul_of_dvd_right hpN l
  have hpsq' : ¬ p ^ 2 ∣ l * N := fun h ↦
    hpsq ((Nat.Coprime.pow_left 2 hpl).dvd_of_dvd_mul_left h)
  -- `diag(l, 1)` and `!![1, 0; 0, p]` commute: the index-`0` case of `scaleRep_mul_upperTriRep`
  have hcomm : scaleGL l *
      Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p ⟨0, NeZero.pos p⟩) =
      Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p ⟨0, NeZero.pos p⟩) *
        scaleGL l := by
    rw [← map_natDiagGL_d_one_eq_scaleGL, ← scaleRep_def, ← map_mul, ← map_mul,
      scaleRep_mul_upperTriRep p (NeZero.pos l) _ (NeZero.pos p)
        (by simp : l * ((⟨0, NeZero.pos p⟩ : Fin p) : ℕ) = 0 * p + 0),
      pow_zero, map_one, one_mul]
  obtain ⟨c, hc⟩ : (l : ℤ) ∣ descendExtraGamma p (l * N) 1 0 := by
    refine (Int.natCast_dvd_natCast.mpr ?_ : (l : ℤ) ∣ ((l * N / p : ℕ) : ℤ)).trans
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
        (Gamma0_mem.mp (descendExtraGamma_mem_Gamma0 hp hplN hpsq')))
    rw [Nat.mul_div_assoc l hpN]
    exact dvd_mul_right l _
  rw [ModularForm.coe_levelRaise,
    ModularForm.smul_slash_of_det_pos k (descendMatrix_det_pos p (l * N) v),
    descendMatrix_eq_map, descendMatrixRat_of_le hv, descendMatrix_eq_map,
    descendMatrixRat_of_le ((val_descendIndexMulEquiv_of_le hp hpl N hv).symm ▸ hv), map_mul,
    map_mul,
    map_mapGL, map_mapGL, ← SlashAction.slash_mul, ← mul_assoc, hcomm,
    mul_assoc, mul_inv_eq_iff_eq_mul.mp (mapGL_conjScale (descendExtraGamma p (l * N)) c hc),
    ← mul_assoc, SlashAction.slash_mul,
    slash_map_upperTriRep_zero_mul_mapGL_conjScale_eq k hp hpN hpsq hpl hcomp hf hc]

/-- **The descent commutes with the level-raise** (Miyake, Lemma 4.6.6 (2)). For a prime `p ∣ N`,
`l` coprime to `p`, and `f ∈ M_k(Γ₁(N), χ)` with `χ` the pull-back of a character modulo `N / p`,
the descent slash sum at level `l N` of `V_l f` is `V_l` of the descent slash sum of `f` at level
`N`: `descendSlash k p (l N) (V_l f) = l ^ (1 - k) • (descendSlash k p N f ∣[k] diag(l, 1))`. -/
theorem descendSlash_coe_levelRaise_mul_left_of_comp_of_mem_modFormCharSpace {N : ℕ} (hp : p.Prime)
    (hpN : p ∣ N)
    (hpl : Nat.Coprime p l) {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : NeZero l := ⟨fun h ↦ hp.coprime_iff_not_dvd.mp hpl (h ▸ dvd_zero p)⟩
    descendSlash k p (l * N) ⇑(ModularForm.levelRaise l (Gamma1_map_le_conjAct_scaleGL N l) f) =
      (l : ℂ) ^ (1 - k) • (descendSlash k p N ⇑f ∣[k] scaleGL l) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero l := ⟨fun h ↦ hp.coprime_iff_not_dvd.mp hpl (h ▸ dvd_zero p)⟩
  rw [descendSlash_def, descendSlash_def, SlashAction.sum_slash, Finset.smul_sum]
  refine Fintype.sum_bijective _ ((descendIndexMulEquiv hp hpl N).bijective) _ _ fun v ↦ ?_
  rcases lt_or_ge v.val p with hv | hv
  · exact coe_levelRaise_slash_descendMatrix_of_lt k hp hpl f hv
  · exact coe_levelRaise_slash_descendMatrix_of_le k hp hpN hpl hcomp hf hv

/-- **The descent commutes with the level-raise, on cusp forms.** For a prime `p ∣ N`, `l`
coprime to `p`, and `f ∈ S_k(Γ₁(N), χ)` with `χ` the pull-back of a character modulo `N / p`,
`descendSlash k p (l N) (V_l f) = l ^ (1 - k) • (descendSlash k p N f ∣[k] diag(l, 1))`. -/
theorem descendSlash_coe_levelRaise_mul_left_of_comp_of_mem_cuspFormCharSpace {N : ℕ} (hp : p.Prime)
    (hpN : p ∣ N) (hpl : Nat.Coprime p l) {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : NeZero l := ⟨fun h ↦ hp.coprime_iff_not_dvd.mp hpl (h ▸ dvd_zero p)⟩
    descendSlash k p (l * N) ⇑(CuspForm.levelRaise l (Gamma1_map_le_conjAct_scaleGL N l) f) =
      (l : ℂ) ^ (1 - k) • (descendSlash k p N ⇑f ∣[k] scaleGL l) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero l := ⟨fun h ↦ hp.coprime_iff_not_dvd.mp hpl (h ▸ dvd_zero p)⟩
  have h := descendSlash_coe_levelRaise_mul_left_of_comp_of_mem_modFormCharSpace k hp hpN hpl hcomp
    ((coe_mem_modFormCharSpace_iff k χ f).mpr hf)
  rw [ModularForm.coe_levelRaise] at h
  rw [CuspForm.coe_levelRaise]
  exact h

end TauCeti
