/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Combinatorics
public import TauCeti.LinearAlgebra.RootSystem.Weyl.ChainBond

/-!
# Reversing saturated chains of `W / W_λ` by the longest element

For a finite crystallographic reduced root pairing `P` with base `b` and longest element `w₀`, the
opposition permutation `-w₀` carries `wallIndices b λ` onto `wallIndices b (-w₀ λ)`, so conjugating
by `w₀` exchanges `W_λ` and `W_{-w₀ λ}`. Specializing `MinimalCosetRepChain.reverseMul` to
`TauCeti.weylCoxeterSystem` preserves reflection bonds and bond gcds, identifying `a`-chains of
`W / W_λ` with `(1 - a)`-chains of `W / W_{-w₀ λ}`.

## Main results

* `TauCeti.conj_longestElement_mem_parabolic_wallIndices_iff`,
  `TauCeti.minimalCosetRep_mul_longestElement_smul`,
  `TauCeti.reflectionBond_minimalCosetRep_mul_longestElement`.
* `CoxeterSystem.MinimalCosetRepChain.bondGcd_reverseMul_longestElement`,
  `CoxeterSystem.MinimalCosetRepChain.isAChain_reverseMul_longestElement_iff`,
  `CoxeterSystem.MinimalCosetRepChain.isAChain_one_sub_reverseMul_longestElement_iff`.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Section 4.
* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005), §§2.3, 2.5.
-/

public section

universe u v w x

namespace TauCeti

open RootPairing CoxeterSystem

section CommRing

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [CharZero R] [IsDomain R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} {b : P.Base}
  [Finite ι] [P.IsCrystallographic] [P.IsReduced]

/-- The opposition permutation carries the simple walls through `λ` onto those through `-(w₀ • λ)`.
-/
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
    using (CoxeterSystem.parabolic_le_iff (H := ((weylCoxeterSystem P b).parabolic
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
  have hmul := (P.isLongest_longestElement b).mul_self
  have hp : longestElement P b * (longestElement P b * p * longestElement P b) *
      longestElement P b = p := by
    rw [← mul_assoc, ← mul_assoc, hmul, one_mul, mul_assoc, hmul, mul_one]
  simpa [smul_neg, neg_neg, smul_smul_longestElement, hp] using
    conj_longestElement_mem_parabolic_wallIndices (-(longestElement P b • lam)) h

/-- **The minimal coset rep of `u * w₀` for `-(w₀ • λ)` sends `-(w₀ • λ)` to `-(u • λ)`.** -/
theorem minimalCosetRep_mul_longestElement_smul (lam : M) (u : P.weylGroup) :
    (weylCoxeterSystem P b).minimalCosetRep
        (P.wallIndices b (-(longestElement P b • lam))) (u * longestElement P b) •
        (-(longestElement P b • lam)) = -(u • lam) := by
  set lam' := -(longestElement P b • lam)
  have hfix : ((u * longestElement P b)⁻¹ *
      (weylCoxeterSystem P b).minimalCosetRep (P.wallIndices b lam') (u * longestElement P b)) •
      lam' = lam' :=
    MulAction.mem_stabilizer_iff.mp (P.parabolic_wallIndices_le_stabilizer b lam'
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

open TauCeti

variable {ι : Type u} {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M} {a : ℚ}
  (C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam))

/-- **Reversing a saturated chain of `W / W_λ` by `w₀` preserves its bond gcd.** -/
@[simp]
theorem bondGcd_reverseMul_longestElement :
    bondGcd (-(longestElement P b • lam)) (C.reverseMul (P.isLongest_longestElement b)
      (conj_longestElement_mem_parabolic_wallIndices_iff lam)) = bondGcd lam C := by
  set D := C.reverseMul (P.isLongest_longestElement b)
    (conj_longestElement_mem_parabolic_wallIndices_iff lam)
  have hlen : D.length = C.length := length_reverseMul _ _ C
  have hbond (k : Fin D.length) :
      P.reflectionBond b ((D k.castSucc).val • -(longestElement P b • lam))
          ((D k.succ).val • -(longestElement P b • lam)) =
        P.reflectionBond b ((C (k.cast hlen).rev.castSucc).val • lam)
          ((C (k.cast hlen).rev.succ).val • lam) := by
    rw [reverseMul_castSucc, reverseMul_succ, reflectionBond_minimalCosetRep_mul_longestElement]
  refine Nat.dvd_antisymm (dvd_bondGcd_iff.mpr fun j ↦ ?_) (dvd_bondGcd_iff.mpr fun k ↦ ?_)
  · simpa only [hbond (j.rev.cast hlen.symm), Fin.cast_cast, Fin.cast_refl, id_eq, Fin.rev_rev]
      using bondGcd_dvd (C := D) (j.rev.cast hlen.symm)
  · simpa only [← hbond k] using bondGcd_dvd (C := C) (k.cast hlen).rev

/-- **Reversing a saturated chain by `w₀` preserves the `a`-chain condition.** -/
@[simp]
theorem isAChain_reverseMul_longestElement_iff :
    IsAChain a (-(longestElement P b • lam)) (C.reverseMul (P.isLongest_longestElement b)
      (conj_longestElement_mem_parabolic_wallIndices_iff lam)) ↔ IsAChain a lam C := by
  simp [isAChain_iff_den_dvd_bondGcd]

/-- **Reversing a saturated chain by `w₀` identifies `a`-chains of `W / W_λ` with `(1 - a)`-chains
of `W / W_{-(w₀ • λ)}`.** -/
theorem isAChain_one_sub_reverseMul_longestElement_iff :
    IsAChain (1 - a) (-(longestElement P b • lam)) (C.reverseMul (P.isLongest_longestElement b)
      (conj_longestElement_mem_parabolic_wallIndices_iff lam)) ↔ IsAChain a lam C := by
  simp [isAChain_iff_den_dvd_bondGcd]

end CoxeterSystem.MinimalCosetRepChain
