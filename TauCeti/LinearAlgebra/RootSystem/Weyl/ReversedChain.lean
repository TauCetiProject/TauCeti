/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Combinatorics
public import TauCeti.LinearAlgebra.RootSystem.Opposition
public import TauCeti.LinearAlgebra.RootSystem.Weyl.ChainBond

/-!
# Reversing saturated chains of `W / W_λ` by the longest element

Let `P` be a finite crystallographic reduced root pairing with base `b`, and write `w₀` for the
longest element of its Weyl group (`TauCeti.longestElement`). The opposition involution `-w₀`
permutes the simple roots (`TauCeti.oppositionPerm`) and carries `RootPairing.wallIndices b λ`
onto `RootPairing.wallIndices b (-w₀ λ)`, so conjugating by `w₀` carries `W_λ` onto `W_{-w₀ λ}`.

Specializing `CoxeterSystem.MinimalCosetRepChain.reverseMul` to `TauCeti.weylCoxeterSystem` gives:
* `u ↦ minimalCosetRep K (u * w₀)` sends `u λ` to `-u λ` (`v (-w₀ λ) = -(u λ)`);
* `b(-y, -x) = b(x, y)` (`RootPairing.reflectionBond_neg_neg`), so reversing a cover of `W / W_λ`
  gives a cover of `W / W_{-w₀ λ}` with the same bond;
* reversing a saturated chain of `W / W_λ` by `w₀` preserves its bond gcd and identifies
  `a`-chains of `W / W_λ` with `(1 - a)`-chains of `W / W_{-w₀ λ}`, without requiring `λ` to be
  dominant or the roots to span.

## Main results

* `TauCeti.conj_longestElement_simple` and
  `TauCeti.conj_longestElement_mem_parabolic_wallIndices_iff`.
* `TauCeti.minimalCosetRep_mul_longestElement_smul`, `RootPairing.reflectionBond_neg_neg`, and
  `TauCeti.reflectionBond_minimalCosetRep_mul_longestElement`.
* `CoxeterSystem.MinimalCosetRepChain.bondGcd_reverseMul_longestElement`,
  `CoxeterSystem.MinimalCosetRepChain.isAChain_reverseMul_longestElement_iff`, and
  `CoxeterSystem.MinimalCosetRepChain.isAChain_one_sub_reverseMul_longestElement_iff`.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Section 4.
* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005), §§2.3, 2.5.
-/

public section

universe u v w x

namespace RootPairing

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [CharZero R] [NoZeroDivisors R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N) {b : P.Base} [P.IsReduced]

/-- **Negating two weights and reversing their order preserves their reflection bond.** -/
theorem reflectionBond_neg_neg (x y : M) :
    P.reflectionBond b (-y) (-x) = P.reflectionBond b x y := by
  rcases eq_or_ne y x with rfl | hxy
  · simp
  by_cases h : ∃ β, b.IsPos β ∧ P.reflection β x = y
  · obtain ⟨β, hβ, h⟩ := h
    have h' : P.reflection β (-y) = -x := by rw [map_neg, ← h, reflection_same]
    rw [reflectionBond_eq_coroot' hβ h' (by simpa [eq_comm] using hxy), map_neg,
      reflectionBond_eq_neg_coroot' hβ h hxy]
  · rw [reflectionBond_eq_zero_of_not_exists h, reflectionBond_eq_zero_of_not_exists]
    rintro ⟨β, hβ, h'⟩
    exact h ⟨β, hβ, neg_injective (by rw [← map_neg, ← h', reflection_same])⟩

end RootPairing

namespace TauCeti

open RootPairing CoxeterSystem

section CommRing

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [CharZero R] [IsDomain R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} {b : P.Base}
  [Finite ι] [P.IsCrystallographic] [P.IsReduced]

/-- **Conjugating a simple reflection by `w₀` applies the opposition involution.** -/
theorem conj_longestElement_simple (i : b.support) :
    longestElement P b * (weylCoxeterSystem P b).simple i * longestElement P b =
      (weylCoxeterSystem P b).simple (oppositionPerm P b i) := by
  nth_rw 2 [← longestElement_inv P b]
  rw [weylCoxeterSystem_simple, weylCoxeterSystem_simple, coe_oppositionPerm,
    ← weylGroup.ofIdx_weylGroupToPerm_eq_conj]
  refine weylGroup.ext fun x ↦ ?_
  rw [weylGroup.ofIdx_smul, weylGroup.ofIdx_smul, Equiv.reflection_smul, Equiv.reflection_smul,
    reflection_apply, reflection_apply, coroot'_opposition, ← coroot'_smul_longestElement,
    root_opposition, ← P.weylGroup_apply_root, neg_smul_neg]

/-- The opposition permutation carries the simple walls through `λ` onto those through
`-(w₀ • λ)`. -/
theorem oppositionPerm_mem_wallIndices_neg_longestElement_smul_iff (lam : M) (i : b.support) :
    oppositionPerm P b i ∈ P.wallIndices b (-(longestElement P b • lam)) ↔
      i ∈ P.wallIndices b lam := by
  rw [mem_wallIndices, mem_wallIndices, coe_oppositionPerm, coroot'_opposition, smul_neg, map_neg,
    smul_smul_longestElement, neg_neg]

private theorem conj_longestElement_mem_parabolic_wallIndices (lam : M) {p : P.weylGroup}
    (hp : p ∈ (weylCoxeterSystem P b).parabolic (P.wallIndices b lam)) :
    longestElement P b * p * longestElement P b ∈
      (weylCoxeterSystem P b).parabolic (P.wallIndices b (-(longestElement P b • lam))) := by
  simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, longestElement_inv]
    using (CoxeterSystem.parabolic_le_iff
      (H := ((weylCoxeterSystem P b).parabolic
        (P.wallIndices b (-(longestElement P b • lam)))).comap
        (MulAut.conj (longestElement P b)).toMonoidHom) _).mpr (fun i hi ↦ by
      simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        longestElement_inv, conj_longestElement_simple]
      exact (weylCoxeterSystem P b).simple_mem_parabolic
        ((oppositionPerm_mem_wallIndices_neg_longestElement_smul_iff lam i).mpr hi)) hp

/-- **Conjugation by `w₀` exchanges the wall parabolic subgroups of `λ` and `-(w₀ • λ)`.** -/
theorem conj_longestElement_mem_parabolic_wallIndices_iff (lam : M) (p : P.weylGroup) :
    longestElement P b * p * longestElement P b ∈
        (weylCoxeterSystem P b).parabolic (P.wallIndices b (-(longestElement P b • lam))) ↔
      p ∈ (weylCoxeterSystem P b).parabolic (P.wallIndices b lam) := by
  refine ⟨fun h ↦ ?_, conj_longestElement_mem_parabolic_wallIndices lam⟩
  have h' := conj_longestElement_mem_parabolic_wallIndices (-(longestElement P b • lam)) h
  have hmul := (P.isLongest_longestElement b).mul_self
  have hp : longestElement P b * (longestElement P b * p * longestElement P b) *
      longestElement P b = p := by
    rw [← mul_assoc, ← mul_assoc, hmul, one_mul, mul_assoc, hmul, mul_one]
  simpa [smul_neg, neg_neg, smul_smul_longestElement, hp] using h'

/-- Every element of the wall parabolic subgroup of a weight fixes that weight. -/
theorem parabolic_wallIndices_le_stabilizer (lam : M) :
    (weylCoxeterSystem P b).parabolic (P.wallIndices b lam) ≤
      MulAction.stabilizer P.weylGroup lam :=
  (CoxeterSystem.parabolic_le_iff _).mpr fun i hi ↦ by
    rw [MulAction.mem_stabilizer_iff, weylCoxeterSystem_simple]
    exact ofIdx_smul_eq_self_of_coroot'_eq_zero (mem_wallIndices.mp hi)

/-- **The minimal coset representative of `u * w₀` for `-(w₀ • λ)` sends `-(w₀ • λ)` to
`-(u • λ)`.** -/
theorem minimalCosetRep_mul_longestElement_smul (lam : M) (u : P.weylGroup) :
    (weylCoxeterSystem P b).minimalCosetRep
        (P.wallIndices b (-(longestElement P b • lam))) (u * longestElement P b) •
        (-(longestElement P b • lam)) = -(u • lam) := by
  set lam' := -(longestElement P b • lam)
  have hfix : ((u * longestElement P b)⁻¹ *
      (weylCoxeterSystem P b).minimalCosetRep (P.wallIndices b lam') (u * longestElement P b)) •
      lam' = lam' :=
    MulAction.mem_stabilizer_iff.mp (parabolic_wallIndices_le_stabilizer lam'
      ((weylCoxeterSystem P b).inv_mul_minimalCosetRep_mem _ _))
  rw [← mul_inv_cancel_left (u * longestElement P b)
    ((weylCoxeterSystem P b).minimalCosetRep _ _), mul_smul, hfix]
  simp [lam', mul_smul, smul_neg, smul_smul_longestElement]

/-- **Reversing minimal coset representatives by `w₀` preserves reflection bonds.** -/
theorem reflectionBond_minimalCosetRep_mul_longestElement (lam : M) (x y : P.weylGroup) :
    P.reflectionBond b
        ((weylCoxeterSystem P b).minimalCosetRep
          (P.wallIndices b (-(longestElement P b • lam))) (y * longestElement P b) •
          (-(longestElement P b • lam)))
        ((weylCoxeterSystem P b).minimalCosetRep
          (P.wallIndices b (-(longestElement P b • lam))) (x * longestElement P b) •
          (-(longestElement P b • lam))) =
      P.reflectionBond b (x • lam) (y • lam) := by
  rw [minimalCosetRep_mul_longestElement_smul, minimalCosetRep_mul_longestElement_smul,
    P.reflectionBond_neg_neg]

end CommRing

end TauCeti

namespace CoxeterSystem.MinimalCosetRepChain

variable {ι : Type u} {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced]
  {lam : M} {a : ℚ}
  (C : (TauCeti.weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam))

/-- **Reversing a saturated chain of `W / W_λ` by `w₀` preserves its bond gcd.** -/
@[simp]
theorem bondGcd_reverseMul_longestElement :
    TauCeti.bondGcd (-(TauCeti.longestElement P b • lam))
        (C.reverseMul (P.isLongest_longestElement b)
          (TauCeti.conj_longestElement_mem_parabolic_wallIndices_iff lam)) =
      TauCeti.bondGcd lam C := by
  set D := C.reverseMul (P.isLongest_longestElement b)
    (TauCeti.conj_longestElement_mem_parabolic_wallIndices_iff lam)
  have hlen : D.length = C.length :=
    CoxeterSystem.MinimalCosetRepChain.length_reverseMul _ _ C
  have hbond (k : Fin D.length) :
      P.reflectionBond b ((D k.castSucc).1 • -(TauCeti.longestElement P b • lam))
          ((D k.succ).1 • -(TauCeti.longestElement P b • lam)) =
        P.reflectionBond b ((C (k.cast hlen).rev.castSucc).1 • lam)
          ((C (k.cast hlen).rev.succ).1 • lam) := by
    have h₁ : (D k.castSucc).1 =
        (TauCeti.weylCoxeterSystem P b).minimalCosetRep
          (P.wallIndices b (-(TauCeti.longestElement P b • lam)))
          ((C (k.cast hlen).rev.succ).1 * TauCeti.longestElement P b) := by
      rw [CoxeterSystem.MinimalCosetRepChain.reverseMul_apply]
      exact congrArg (fun j : Fin (C.length + 1) ↦
        (TauCeti.weylCoxeterSystem P b).minimalCosetRep
          (P.wallIndices b (-(TauCeti.longestElement P b • lam)))
          ((C j).1 * TauCeti.longestElement P b))
        (Fin.ext (by simp [Fin.val_rev]; omega))
    have h₂ : (D k.succ).1 =
        (TauCeti.weylCoxeterSystem P b).minimalCosetRep
          (P.wallIndices b (-(TauCeti.longestElement P b • lam)))
          ((C (k.cast hlen).rev.castSucc).1 * TauCeti.longestElement P b) := by
      rw [CoxeterSystem.MinimalCosetRepChain.reverseMul_apply]
      exact congrArg (fun j : Fin (C.length + 1) ↦
        (TauCeti.weylCoxeterSystem P b).minimalCosetRep
          (P.wallIndices b (-(TauCeti.longestElement P b • lam)))
          ((C j).1 * TauCeti.longestElement P b))
        (Fin.ext (by simp [Fin.val_rev]))
    rw [h₁, h₂, TauCeti.reflectionBond_minimalCosetRep_mul_longestElement]
  refine Nat.dvd_antisymm
    (TauCeti.dvd_bondGcd_iff.mpr fun j ↦ ?_)
    (TauCeti.dvd_bondGcd_iff.mpr fun k ↦ ?_)
  · set k : Fin D.length := j.rev.cast hlen.symm
    have hk := TauCeti.bondGcd_dvd (C := D) k
    have hk' : (k.cast hlen).rev = j := by simp [k]
    rwa [hbond k, hk'] at hk
  · have hk := TauCeti.bondGcd_dvd (C := C) (k.cast hlen).rev
    rwa [← hbond k] at hk

/-- **Reversing a saturated chain by `w₀` preserves the `a`-chain condition.** -/
@[simp]
theorem isAChain_reverseMul_longestElement_iff :
    TauCeti.IsAChain a (-(TauCeti.longestElement P b • lam))
        (C.reverseMul (P.isLongest_longestElement b)
          (TauCeti.conj_longestElement_mem_parabolic_wallIndices_iff lam)) ↔
      TauCeti.IsAChain a lam C := by
  rw [TauCeti.isAChain_iff_den_dvd_bondGcd, TauCeti.isAChain_iff_den_dvd_bondGcd,
    bondGcd_reverseMul_longestElement]

/-- **Reversing a saturated chain by `w₀` identifies `a`-chains of `W / W_λ` with `(1 - a)`-chains
of `W / W_{-(w₀ • λ)}`.** Since `1 - a` and `a` have the same denominator, this is the chain
condition for Littelmann's dual Lakshmibai–Seshadri path `π^*`. -/
theorem isAChain_one_sub_reverseMul_longestElement_iff :
    TauCeti.IsAChain (1 - a) (-(TauCeti.longestElement P b • lam))
        (C.reverseMul (P.isLongest_longestElement b)
          (TauCeti.conj_longestElement_mem_parabolic_wallIndices_iff lam)) ↔
      TauCeti.IsAChain a lam C := by
  rw [TauCeti.isAChain_iff_den_dvd_bondGcd, TauCeti.isAChain_iff_den_dvd_bondGcd,
    bondGcd_reverseMul_longestElement, show (1 - a).den = a.den by simp]

end CoxeterSystem.MinimalCosetRepChain
