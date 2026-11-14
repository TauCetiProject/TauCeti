/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Combinatorics
public import TauCeti.LinearAlgebra.RootSystem.Weyl.ChainBond
import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# Reversal of parabolic cosets and `a`-chains by the longest element

For a dominant weight `λ` of a finite reduced root pairing with base `b`, the longest element `w₀`
of the Weyl group maps `λ` into the antidominant chamber, so `λ* = -w₀ λ` is again dominant
(`TauCeti.neg_smul_mem_dominantChamber_longestElement`). Because the parabolic subgroups generated
by the simple walls through `λ` and `λ*` are their Weyl stabilizers
(`RootPairing.parabolic_wallIndices_eq_stabilizer`), conjugation by `w₀` maps `W_{λ*}` onto `W_λ`.

Right multiplication by `w₀` followed by taking minimal coset representatives therefore reverses
minimal coset representatives and saturated chains between `W / W_λ` and `W / W_{λ*}`
(`CoxeterSystem.MinimalCosetRepChain.reverseMul`), sending the orbit weight `x λ` to `-x λ`. Since
reversing and negating two weights preserves their reflection bond
(`RootPairing.reflectionBond_neg_swap`), this reversal preserves bond gcds
(`TauCeti.bondGcd_reverseMul`) and carries `a`-chains of shape `λ` onto `(1 - a)`-chains of shape
`-w₀ λ` (`TauCeti.isAChain_one_sub_reverseMul_iff`).

## Main results

* `TauCeti.conj_longestElement_mem_parabolic_wallIndices_iff`: conjugation by `w₀` carries the wall
  parabolic of `-w₀ λ` onto that of `λ`.
* `TauCeti.minimalCosetRep_mul_longestElement_smul`: the minimal coset representative of `x w₀` in
  `W / W_{-w₀ λ}` acts on `-w₀ λ` with orbit weight `-(x λ)`.
* `TauCeti.bondGcd_reverseMul`: reversing a saturated chain of `W / W_λ` by `w₀` preserves its bond
  gcd for shape `-w₀ λ`.
* `TauCeti.isAChain_one_sub_reverseMul_iff`: the reversed chain is a `(1 - a)`-chain of shape
  `-w₀ λ` if and only if the original chain is an `a`-chain of shape `λ`.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §§1–2, 4.
-/

public section

universe u v w x

namespace TauCeti

open RootPairing

section OrderedRing

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} {b : P.Base} [Finite ι]
  [P.IsCrystallographic] [P.IsReduced] [P.flip.IsReduced]

/-- **Conjugation by the longest element carries the wall parabolic of `-w₀ λ` onto that of `λ`.**
For dominant `λ`, both parabolics are Weyl stabilizers, and `w₀ p w₀ (-w₀ λ) = -w₀ (p λ)`. -/
theorem conj_longestElement_mem_parabolic_wallIndices_iff {lam : M}
    (hlam : lam ∈ dominantChamber P b) (p : P.weylGroup) :
    longestElement P b * p * longestElement P b ∈
        (weylCoxeterSystem P b).parabolic (P.wallIndices b (-(longestElement P b • lam))) ↔
      p ∈ (weylCoxeterSystem P b).parabolic (P.wallIndices b lam) := by
  have hlam' : -(longestElement P b • lam) ∈ dominantChamber P b :=
    neg_smul_mem_dominantChamber_longestElement hlam
  rw [P.parabolic_wallIndices_eq_stabilizer b hlam', P.parabolic_wallIndices_eq_stabilizer b hlam,
    MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  simp only [smul_neg, mul_smul, smul_smul_longestElement, neg_inj]
  exact ⟨fun h ↦ by simpa [smul_smul_longestElement] using congrArg (longestElement P b • ·) h,
    fun h ↦ by rw [h]⟩

/-- **The minimal coset representative of `x w₀` in `W / W_{-w₀ λ}` has orbit weight `-(x λ)`.** -/
theorem minimalCosetRep_mul_longestElement_smul {lam : M}
    (hlam : lam ∈ dominantChamber P b) (x : P.weylGroup) :
    (weylCoxeterSystem P b).minimalCosetRep (P.wallIndices b (-(longestElement P b • lam)))
        (x * longestElement P b) • (-(longestElement P b • lam)) = -(x • lam) := by
  have hlam' : -(longestElement P b • lam) ∈ dominantChamber P b :=
    neg_smul_mem_dominantChamber_longestElement hlam
  have hmem := (weylCoxeterSystem P b).inv_mul_minimalCosetRep_mem
    (P.wallIndices b (-(longestElement P b • lam))) (x * longestElement P b)
  rw [inv_mul_mem_parabolic_wallIndices_iff hlam'] at hmem
  rw [hmem, smul_neg, mul_smul, smul_smul_longestElement]

end OrderedRing

section Int

variable {ι : Type u} {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced]

/-- Integral specialization of `TauCeti.neg_smul_mem_dominantChamber_longestElement` without an
explicit `[P.flip.IsReduced]` hypothesis. -/
theorem neg_smul_mem_dominantChamber_longestElement_int {lam : M}
    (hlam : lam ∈ dominantChamber P b) :
    -(longestElement P b • lam) ∈ dominantChamber P b := by
  have := P.flip_isReduced
  exact neg_smul_mem_dominantChamber_longestElement hlam

/-- Integral specialization of `TauCeti.conj_longestElement_mem_parabolic_wallIndices_iff` without
an explicit `[P.flip.IsReduced]` hypothesis. -/
theorem conj_longestElement_mem_parabolic_wallIndices_int_iff {lam : M}
    (hlam : lam ∈ dominantChamber P b) (p : P.weylGroup) :
    longestElement P b * p * longestElement P b ∈
        (weylCoxeterSystem P b).parabolic (P.wallIndices b (-(longestElement P b • lam))) ↔
      p ∈ (weylCoxeterSystem P b).parabolic (P.wallIndices b lam) := by
  have := P.flip_isReduced
  exact conj_longestElement_mem_parabolic_wallIndices_iff hlam p

/-- **Reversing a saturated chain of `W / W_λ` by `w₀` preserves its bond gcd.** Each reversed cover
pairs `-(x_h λ)` with `-(x_{h-1} λ)`, whose bond equals `b_λ(x_{h-1}, x_h)` by
`RootPairing.reflectionBond_neg_swap`. -/
@[simp]
theorem bondGcd_reverseMul {lam : M} (hlam : lam ∈ dominantChamber P b)
    (C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)) :
    bondGcd (-(longestElement P b • lam))
      (C.reverseMul (P.isLongest_longestElement b)
        (conj_longestElement_mem_parabolic_wallIndices_int_iff hlam)) =
      bondGcd lam C := by
  have := P.flip_isReduced
  have hlen : (C.reverseMul (P.isLongest_longestElement b)
      (conj_longestElement_mem_parabolic_wallIndices_int_iff hlam)).length = C.length := by
    simp
  refine dvd_antisymm (dvd_bondGcd_iff.mpr fun i ↦ ?_) (dvd_bondGcd_iff.mpr fun i ↦ ?_)
  · let j : Fin (C.reverseMul (P.isLongest_longestElement b)
      (conj_longestElement_mem_parabolic_wallIndices_int_iff hlam)).length :=
      ⟨i.rev.1, by omega⟩
    have hcast : Fin.rev ⟨j.castSucc.1, by simpa using j.castSucc.2⟩ = i.succ := by
      ext; simp [j, Fin.val_rev]; omega
    have hsucc : Fin.rev ⟨j.succ.1, by simpa using j.succ.2⟩ = i.castSucc := by
      ext; simp [j, Fin.val_rev]; omega
    simpa only [CoxeterSystem.MinimalCosetRepChain.reverseMul_apply, hcast, hsucc,
      minimalCosetRep_mul_longestElement_smul hlam, reflectionBond_neg_swap] using
      bondGcd_dvd j
  · let j : Fin C.length := ⟨i.rev.1, by omega⟩
    have hcast : Fin.rev ⟨i.castSucc.1, by simpa using i.castSucc.2⟩ = j.succ := by
      ext; simp [j, Fin.val_rev]; omega
    have hsucc : Fin.rev ⟨i.succ.1, by simpa using i.succ.2⟩ = j.castSucc := by
      ext; simp [j, Fin.val_rev]
    simpa only [CoxeterSystem.MinimalCosetRepChain.reverseMul_apply, hcast, hsucc,
      minimalCosetRep_mul_longestElement_smul hlam, reflectionBond_neg_swap] using
      bondGcd_dvd (C := C) j

/-- Reversing a saturated chain of `W / W_λ` by `w₀` preserves the `a`-chain condition at the
same rational parameter `a`. -/
@[simp]
theorem isAChain_reverseMul_iff {lam : M} (hlam : lam ∈ dominantChamber P b) {a : ℚ}
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)} :
    IsAChain a (-(longestElement P b • lam))
      (C.reverseMul (P.isLongest_longestElement b)
        (conj_longestElement_mem_parabolic_wallIndices_int_iff hlam)) ↔
      IsAChain a lam C := by
  rw [isAChain_iff_den_dvd_bondGcd, isAChain_iff_den_dvd_bondGcd, bondGcd_reverseMul hlam]

/-- **Reversing a saturated chain of `W / W_λ` by `w₀` carries `a`-chains to `(1 - a)`-chains of
shape `-w₀ λ`.** -/
theorem isAChain_one_sub_reverseMul_iff {lam : M} (hlam : lam ∈ dominantChamber P b) {a : ℚ}
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)} :
    IsAChain (1 - a) (-(longestElement P b • lam))
      (C.reverseMul (P.isLongest_longestElement b)
        (conj_longestElement_mem_parabolic_wallIndices_int_iff hlam)) ↔
      IsAChain a lam C := by
  rw [isAChain_reverseMul_iff hlam, isAChain_iff_forall_reflectionBond,
    isAChain_iff_forall_reflectionBond]
  refine ⟨fun h i ↦ ?_, fun h i ↦ ?_⟩
  · obtain ⟨z, hz⟩ := h i
    refine ⟨P.reflectionBond b ((C i.castSucc).1 • lam) ((C i.succ).1 • lam) - z, ?_⟩
    push_cast
    linear_combination -hz
  · obtain ⟨z, hz⟩ := h i
    refine ⟨P.reflectionBond b ((C i.castSucc).1 • lam) ((C i.succ).1 • lam) - z, ?_⟩
    push_cast
    linear_combination -hz

end Int

end TauCeti
