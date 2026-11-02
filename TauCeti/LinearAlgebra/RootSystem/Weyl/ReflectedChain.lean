/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.ChainProperty
public import TauCeti.LinearAlgebra.RootSystem.Weyl.ChainBond

/-!
# Reflecting saturated chains of `W / W_λ` in a simple root

Let `λ` be a dominant weight for a base of a finite reduced root system, let `αᵢ` be a simple root
and write `H(x) = ⟨x λ, αᵢ^∨⟩` for a minimal coset representative `x` of `W / W_λ`. Littelmann's
root operators `f_αᵢ` and `e_αᵢ` change a Lakshmibai–Seshadri path of shape `λ` by reflecting one
piece of it in `sᵢ`, so the directions `τ` of that piece become `sᵢ τ`. Whether the result is again
a Lakshmibai–Seshadri path is a question about saturated chains of `W / W_λ`, their bonds and the
simple reflection `sᵢ`. This file proves the statements about chains that this needs.

**Single cosets and covers.** These statements are proved upstream, in
`TauCeti.LinearAlgebra.RootSystem.Weyl.ParabolicQuotient` and
`TauCeti.LinearAlgebra.RootSystem.Weyl.CoverBond`. If `H(u) ≠ 0` then `sᵢ u` is again a minimal
coset representative, and if `H(u) > 0` then `u ⋖ sᵢ u`, with bond `H(u)`. If `y ⋖ x` and `H(x)`,
`H(y)` are both positive, or both negative, then `sᵢ y ⋖ sᵢ x` with the same bond: the positive
root label `β` becomes `sᵢ β`, which is positive because `β ≠ αᵢ`. A cover crossing the wall from
`H(x) ≤ 0` to `H(y) > 0` is `y ⋖ sᵢ y`, that is `x = sᵢ y`; the opposite crossing
`H(x) < 0 ≤ H(y)` is `TauCeti.reflection_smul_eq_of_minimalCosetRepCovBy_of_coroot'_neg`.

**Chains.** A saturated chain `x₀ ⋗ ⋯ ⋗ x_l` lying strictly on one side of the wall `H = 0` is
carried by `sᵢ` to the saturated chain `sᵢ x₀ ⋗ ⋯ ⋗ sᵢ x_l`
(`CoxeterSystem.MinimalCosetRepChain.simpleMul`), with the same bonds, so with the same bond gcd;
it is an `a`-chain exactly when the original chain is. For an `a`-chain `C` from `x` down to `y`:

* if `H(x) ≤ 0 < H(y)`, then `a H(y)` is an integer, and there is an `a`-chain from `x` down to
  `sᵢ y`: the last cover of `C` leaving the side `H ≤ 0` is `x_{k+1} ⋖ sᵢ x_{k+1}`, and the rest
  of the chain is reflected;
* if `H(x) < 0 ≤ H(y)`, there is an `a`-chain from `sᵢ x` down to `y`, symmetrically; the
  integrality of `a H(x)` is `TauCeti.IsAChain.exists_mul_coroot'_eq_intCast`;
* if `H(y) > 0` and `a H(y)` is not an integer, then all of `C` lies on the side `H > 0`; if
  `H(x) < 0` and `a H(x)` is not an integer, all of `C` lies on the side `H < 0`. In both cases
  `C` reflects to an `a`-chain from `sᵢ x` down to `sᵢ y`.

These are the chain conditions in Littelmann's proof that `f_αᵢ` and `e_αᵢ` preserve
Lakshmibai–Seshadri paths. For `f_αᵢ`, the reflected piece runs from the last time `t₀` at which
the height `⟨π(t), αᵢ^∨⟩` is minimal to the first later time `t₁` at which it has risen by one.
The height increases on that piece, and it is nonintegral strictly inside, so at the internal
breaks of the piece the last two items apply. At `t₀` the height has a local minimum: the
directions there pass from `H ≤ 0` to `H > 0`, and the first item supplies the new chain. At `t₁`
the direction `τ` splits into `sᵢ τ ⋗ τ`, a cover with bond `H(τ)`.

## Main definitions

* `CoxeterSystem.MinimalCosetRepChain.simpleMul`: the reflection `sᵢ x₀ ⋗ ⋯ ⋗ sᵢ x_l` of a
  saturated chain of `W / W_λ` lying strictly on one side of the wall of `αᵢ`.

## Main results

* `CoxeterSystem.MinimalCosetRepChain.bondGcd_simpleMul` and
  `CoxeterSystem.MinimalCosetRepChain.isAChain_simpleMul_iff`: the reflected chain has the same
  bond gcd and the same `a`-chain condition.
* `TauCeti.IsAChain.exists_mul_coroot'_last_eq_intCast`: **along an `a`-chain from `H ≤ 0` to
  `H > 0`, `a H` is an integer at the end**.
* `TauCeti.IsAChain.coroot'_smul_pos` and `TauCeti.IsAChain.coroot'_smul_neg`: an `a`-chain
  ending at a positive nonintegral `a H`, or starting at a negative one, stays on that side.
* `TauCeti.IsAChain.exists_isAChain_simple_mul_last` and
  `TauCeti.IsAChain.exists_isAChain_simple_mul_head`: **Littelmann's chains at the ends of a
  reflected piece**.
* `TauCeti.exists_isAChain_simple_mul_of_coroot'_pos`: the cover `u ⋖ sᵢ u` is an `a`-chain
  exactly when `a H(u)` is an integer.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329--346, Section 4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Section 4.
* V. V. Deodhar, *Some characterizations of Bruhat ordering on a Coxeter group and determination
  of the relative Möbius function*, Invent. Math. 39 (1977), 187--198.
-/

public section

universe u v w x

namespace TauCeti

open RootPairing CoxeterSystem

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}

/-! ### Reflecting a saturated chain -/

namespace _root_.CoxeterSystem.MinimalCosetRepChain

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : _root_.RootPairing ι R M N} {b : P.Base} [Finite ι]
  [P.IsCrystallographic] [P.IsReduced] [P.flip.IsReduced] {lam : M}

/-- The **reflection** `sᵢ x₀ ⋗ sᵢ x₁ ⋗ ⋯ ⋗ sᵢ x_l` of a saturated chain `x₀ ⋗ ⋯ ⋗ x_l` of
`W / W_λ` lying strictly on one side of the wall of the simple root `αᵢ`: either
`⟨x_k λ, αᵢ^∨⟩ > 0` for all `k`, or `⟨x_k λ, αᵢ^∨⟩ < 0` for all `k`. It is again a saturated chain,
by `TauCeti.minimalCosetRepCovBy_simple_mul_simple_mul_of_coroot'_pos` and
`TauCeti.minimalCosetRepCovBy_simple_mul_simple_mul_of_coroot'_neg`. -/
noncomputable def simpleMul (hlam : lam ∈ dominantChamber P b)
    (C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)) (i : b.support)
    (hC : (∀ k, 0 < P.coroot' i ((C k).1 • lam)) ∨ ∀ k, P.coroot' i ((C k).1 • lam) < 0) :
    (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam) where
  length := C.length
  toFun k := ⟨(weylCoxeterSystem P b).simple i * (C k).1,
    TauCeti.isMinimalCosetRep_simple_mul_of_coroot'_ne_zero (C k).2
      (hC.elim (fun h ↦ (h k).ne') fun h ↦ (h k).ne)⟩
  step k := hC.elim
    (fun h ↦ TauCeti.minimalCosetRepCovBy_simple_mul_simple_mul_of_coroot'_pos hlam
      (C.minimalCosetRepCovBy k) (h _) (h _))
    fun h ↦ TauCeti.minimalCosetRepCovBy_simple_mul_simple_mul_of_coroot'_neg hlam
      (C.minimalCosetRepCovBy k) (h _) (h _)

variable {hlam : lam ∈ dominantChamber P b}
  {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)} {i : b.support}
  {hC : (∀ k, 0 < P.coroot' i ((C k).1 • lam)) ∨ ∀ k, P.coroot' i ((C k).1 • lam) < 0}

@[simp]
theorem length_simpleMul : (simpleMul hlam C i hC).length = C.length :=
  (rfl)

@[simp]
theorem simpleMul_apply (k : Fin ((simpleMul hlam C i hC).length + 1)) :
    ((simpleMul hlam C i hC) k).1 =
      (weylCoxeterSystem P b).simple i * (C ⟨k, by simpa using k.2⟩).1 :=
  (rfl)

@[simp]
theorem head_simpleMul :
    (simpleMul hlam C i hC).head.1 = (weylCoxeterSystem P b).simple i * C.head.1 :=
  (rfl)

@[simp]
theorem last_simpleMul :
    (simpleMul hlam C i hC).last.1 = (weylCoxeterSystem P b).simple i * C.last.1 :=
  (rfl)

end _root_.CoxeterSystem.MinimalCosetRepChain

/-! ### `a`-chains of a root datum -/

section RootDatum

variable [AddCommGroup M] [AddCommGroup N] {P : _root_.RootPairing ι ℤ M N} {b : P.Base}
  [Finite ι] [P.IsReduced] [P.flip.IsReduced] {lam : M} {a : ℚ}

namespace _root_.CoxeterSystem.MinimalCosetRepChain

variable {hlam : lam ∈ dominantChamber P b}
  {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)} {i : b.support}
  {hC : (∀ k, 0 < P.coroot' i ((C k).1 • lam)) ∨ ∀ k, P.coroot' i ((C k).1 • lam) < 0}

/-- **Reflecting a saturated chain in a simple root keeps its bonds**, hence its bond gcd. -/
@[simp]
theorem bondGcd_simpleMul :
    TauCeti.bondGcd lam (simpleMul hlam C i hC) = TauCeti.bondGcd lam C := by
  -- The bonds of corresponding covers agree.
  have hbond (k : Fin C.length) :
      P.reflectionBond b (((simpleMul hlam C i hC) k.castSucc).1 • lam)
          (((simpleMul hlam C i hC) k.succ).1 • lam) =
        P.reflectionBond b ((C k.castSucc).1 • lam) ((C k.succ).1 • lam) := by
    refine TauCeti.reflectionBond_simple_mul_smul_simple_mul_smul hlam (C.minimalCosetRepCovBy k)
      fun h ↦ ?_
    -- A cover on one side of the wall is not the simple reflection `sᵢ`.
    have hpair := congrArg (P.coroot' i) h
    rw [TauCeti.simple_mul_smul_eq_reflection, coroot'_reflection_self] at hpair
    rcases hC with hC | hC
    · linarith [hC k.succ, hC k.castSucc]
    · linarith [hC k.succ, hC k.castSucc]
  refine Nat.dvd_antisymm (TauCeti.dvd_bondGcd_iff.mpr fun k ↦ ?_)
    (TauCeti.dvd_bondGcd_iff.mpr fun k ↦ ?_)
  · convert TauCeti.bondGcd_dvd (C := simpleMul hlam C i hC) k using 2
    exact (hbond k).symm
  · convert TauCeti.bondGcd_dvd (C := C) k using 2
    exact hbond k

/-- **Reflecting a saturated chain in a simple root preserves the `a`-chain condition.** -/
@[simp]
theorem isAChain_simpleMul_iff :
    TauCeti.IsAChain a lam (simpleMul hlam C i hC) ↔ TauCeti.IsAChain a lam C := by
  rw [TauCeti.isAChain_iff_den_dvd_bondGcd, TauCeti.isAChain_iff_den_dvd_bondGcd,
    bondGcd_simpleMul]

end _root_.CoxeterSystem.MinimalCosetRepChain

/-- **The cover `u ⋖ sᵢ u` is an `a`-chain when `a ⟨u λ, αᵢ^∨⟩` is an integer.** For a minimal coset
representative `u` of `W / W_λ` with `⟨u λ, αᵢ^∨⟩ > 0`, the saturated chain `sᵢ u ⋗ u` has the
single bond `⟨u λ, αᵢ^∨⟩`. -/
theorem exists_isAChain_simple_mul_of_coroot'_pos (hlam : lam ∈ dominantChamber P b)
    {u : P.weylGroup}
    (hu : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) u) {i : b.support}
    (hi : 0 < P.coroot' i (u • lam)) (ha : ∃ z : ℤ, a * P.coroot' i (u • lam) = z) :
    ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
      C.head.1 = (weylCoxeterSystem P b).simple i * u ∧ C.last.1 = u ∧ IsAChain a lam C := by
  have h := minimalCosetRepCovBy_simple_mul_of_coroot'_pos hlam hu hi
  refine ⟨(RelSeries.singleton _ ⟨_, h.isMinimalCosetRep_right⟩ :
    (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)).snoc ⟨u, hu⟩ h,
    by simp, by simp, (isAChain_snoc_iff h).mpr ⟨isAChain_singleton _, ?_⟩⟩
  rwa [RelSeries.last_singleton, reflectionBond_simple_mul_smul_smul]

/-- **Integrality where an `a`-chain enters the positive side of a simple wall.** Let
`C : x₀ ⋗ ⋯ ⋗ x_l` be an `a`-chain of `W / W_λ` and `αᵢ` a simple root with
`⟨x₀ λ, αᵢ^∨⟩ ≤ 0 < ⟨x_l λ, αᵢ^∨⟩`. Then `a ⟨x_l λ, αᵢ^∨⟩` is an integer. This is the mirror
image of `TauCeti.IsAChain.exists_mul_coroot'_eq_intCast`. -/
theorem IsAChain.exists_mul_coroot'_last_eq_intCast (hlam : lam ∈ dominantChamber P b)
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)}
    (hC : IsAChain a lam C) (i : b.support) (hhead : P.coroot' i (C.head.1 • lam) ≤ 0)
    (hlast : 0 < P.coroot' i (C.last.1 • lam)) :
    ∃ z : ℤ, a * P.coroot' i (C.last.1 • lam) = z := by
  -- `a ⟨x₀ λ, αᵢ^∨⟩` is an integer: it vanishes, or the chain starts on the negative side.
  obtain ⟨z₁, hz₁⟩ : ∃ z : ℤ, a * P.coroot' i (C.head.1 • lam) = z := by
    rcases hhead.lt_or_eq with hneg | hzero
    · exact hC.exists_mul_coroot'_eq_intCast hlam i hneg hlast.le
    · exact ⟨0, by simp [hzero]⟩
  -- The chain changes the pairing by an `a`-integral amount.
  obtain ⟨z₂, hz₂⟩ := hC.exists_mul_sub_eq_intCast hlam (P.coroot' i)
  refine ⟨z₁ - z₂, ?_⟩
  push_cast at hz₁ hz₂ ⊢
  linear_combination hz₁ - hz₂

/-- **An `a`-chain ending at a nonintegral positive pairing stays on the positive side.** If
`C : x₀ ⋗ ⋯ ⋗ x_l` is an `a`-chain of `W / W_λ` with `⟨x_l λ, αᵢ^∨⟩ > 0` and `a ⟨x_l λ, αᵢ^∨⟩` not
an integer, then `⟨x_k λ, αᵢ^∨⟩ > 0` for all `k`; so `C` reflects in `sᵢ`
(`CoxeterSystem.MinimalCosetRepChain.simpleMul`). -/
theorem IsAChain.coroot'_smul_pos (hlam : lam ∈ dominantChamber P b)
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)}
    (hC : IsAChain a lam C) (i : b.support) (hlast : 0 < P.coroot' i (C.last.1 • lam))
    (hint : ¬∃ z : ℤ, a * P.coroot' i (C.last.1 • lam) = z) (k : Fin (C.length + 1)) :
    0 < P.coroot' i ((C k).1 • lam) := by
  refine lt_of_not_ge fun hk ↦ hint ?_
  simpa using (hC.drop k).exists_mul_coroot'_last_eq_intCast hlam i (by simpa using hk)
    (by simpa using hlast)

/-- **An `a`-chain starting at a nonintegral negative pairing stays on the negative side.** If
`C : x₀ ⋗ ⋯ ⋗ x_l` is an `a`-chain of `W / W_λ` with `⟨x₀ λ, αᵢ^∨⟩ < 0` and `a ⟨x₀ λ, αᵢ^∨⟩` not
an integer, then `⟨x_k λ, αᵢ^∨⟩ < 0` for all `k`; so `C` reflects in `sᵢ`
(`CoxeterSystem.MinimalCosetRepChain.simpleMul`). -/
theorem IsAChain.coroot'_smul_neg (hlam : lam ∈ dominantChamber P b)
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)}
    (hC : IsAChain a lam C) (i : b.support) (hhead : P.coroot' i (C.head.1 • lam) < 0)
    (hint : ¬∃ z : ℤ, a * P.coroot' i (C.head.1 • lam) = z) (k : Fin (C.length + 1)) :
    P.coroot' i ((C k).1 • lam) < 0 := by
  refine lt_of_not_ge fun hk ↦ hint ?_
  simpa using (hC.take k).exists_mul_coroot'_eq_intCast hlam i (by simpa using hhead)
    (by simpa using hk)

/-- **Littelmann's chain at the start of a reflected piece of `f_αᵢ`.** If `C` is an `a`-chain of
`W / W_λ` from `x` down to `y` with `⟨x λ, αᵢ^∨⟩ ≤ 0 < ⟨y λ, αᵢ^∨⟩`, then there is an `a`-chain
from `x` down to `sᵢ y`. If `x_{k+1} ⋖ x_k` is the last cover of `C` leaving the side `≤ 0`, then
`x_k = sᵢ x_{k+1}`, and the chain is `x ⋗ ⋯ ⋗ x_k = sᵢ x_{k+1} ⋗ ⋯ ⋗ sᵢ y`, reflecting the end of
`C` (all on the positive side) in `sᵢ`. -/
theorem IsAChain.exists_isAChain_simple_mul_last (hlam : lam ∈ dominantChamber P b)
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)}
    (hC : IsAChain a lam C) (i : b.support) (hhead : P.coroot' i (C.head.1 • lam) ≤ 0)
    (hlast : 0 < P.coroot' i (C.last.1 • lam)) :
    ∃ D : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
      D.head = C.head ∧ D.last.1 = (weylCoxeterSystem P b).simple i * C.last.1 ∧
        IsAChain a lam D := by
  -- The least `k` from which on the chain stays on the positive side.
  have hex : ∃ k, ∀ j (hj : j ≤ C.length), k ≤ j →
      0 < P.coroot' i ((C ⟨j, Nat.lt_succ_of_le hj⟩).1 • lam) :=
    ⟨C.length, fun j hj hkj ↦ by
      obtain rfl : j = C.length := le_antisymm hj hkj
      exact hlast⟩
  classical
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := Nat.exists_eq_succ_of_ne_zero fun h0 ↦
    (hhead.trans_lt (Nat.find_spec hex 0 (Nat.zero_le _) (h0 ▸ le_rfl))).false
  have hpos := Nat.find_spec hex
  rw [hk] at hpos
  have hkl : k + 1 ≤ C.length := by
    by_contra hkl
    refine Nat.find_min hex (m := k) (by omega) fun j hj hkj ↦ ?_
    obtain rfl : j = C.length := by omega
    exact hlast
  -- The pairing at `x_k` is nonpositive, by minimality.
  have hnonpos : P.coroot' i ((C ⟨k, by omega⟩).1 • lam) ≤ 0 := by
    refine not_lt.mp fun hk' ↦ Nat.find_min hex (m := k) (by omega) fun j hj hkj ↦ ?_
    rcases hkj.eq_or_lt with rfl | hkj
    · exact hk'
    · exact hpos j hj hkj
  have hcov := C.minimalCosetRepCovBy ⟨k, hkl⟩
  simp only [Fin.castSucc_mk, Fin.succ_mk] at hcov
  have heq := eq_simple_mul_of_minimalCosetRepCovBy_of_coroot'_nonpos hlam hcov i hnonpos
    (hpos (k + 1) hkl le_rfl)
  -- Reflect the end `x_{k+1} ⋗ ⋯ ⋗ x_l` of the chain.
  set E := C.drop ⟨k + 1, by omega⟩
  have hE : (∀ j, 0 < P.coroot' i ((E j).1 • lam)) ∨ ∀ j, P.coroot' i ((E j).1 • lam) < 0 :=
    Or.inl fun j ↦ by
      have hj : (j : ℕ) < C.length - (k + 1) + 1 := j.2
      exact hpos (j + (k + 1)) (by omega) (Nat.le_add_left _ _)
  set D := _root_.CoxeterSystem.MinimalCosetRepChain.simpleMul hlam E i hE
  have hjoin : (C.take ⟨k, by omega⟩).last = D.head :=
    Subtype.ext (by simpa [D, E] using heq)
  refine ⟨(C.take ⟨k, by omega⟩).smash D hjoin, by simp, by simp [D, E],
    (isAChain_smash_iff hjoin).mpr ⟨hC.take _, ?_⟩⟩
  exact _root_.CoxeterSystem.MinimalCosetRepChain.isAChain_simpleMul_iff.mpr (hC.drop _)

/-- **Littelmann's chain at the end of a reflected piece of `e_αᵢ`.** If `C` is an `a`-chain of
`W / W_λ` from `x` down to `y` with `⟨x λ, αᵢ^∨⟩ < 0 ≤ ⟨y λ, αᵢ^∨⟩`, then there is an `a`-chain
from `sᵢ x` down to `y`. If `x_{k+1} ⋖ x_k` is the first cover of `C` leaving the negative side,
then `x_{k+1} = sᵢ x_k`, and the chain is `sᵢ x ⋗ ⋯ ⋗ sᵢ x_k = x_{k+1} ⋗ ⋯ ⋗ y`, reflecting the
start of `C` (all on the negative side) in `sᵢ`. -/
theorem IsAChain.exists_isAChain_simple_mul_head (hlam : lam ∈ dominantChamber P b)
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)}
    (hC : IsAChain a lam C) (i : b.support) (hhead : P.coroot' i (C.head.1 • lam) < 0)
    (hlast : 0 ≤ P.coroot' i (C.last.1 • lam)) :
    ∃ D : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
      D.head.1 = (weylCoxeterSystem P b).simple i * C.head.1 ∧ D.last = C.last ∧
        IsAChain a lam D := by
  -- The first index `k + 1` at which the pairing is nonnegative.
  have hex : ∃ k, ∃ hk : k ≤ C.length,
      0 ≤ P.coroot' i ((C ⟨k, Nat.lt_succ_of_le hk⟩).1 • lam) := ⟨C.length, le_rfl, hlast⟩
  classical
  obtain ⟨hle, hnonneg⟩ := Nat.find_spec hex
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := Nat.exists_eq_succ_of_ne_zero fun h0 ↦ by
    simp only [h0] at hnonneg
    exact (hhead.trans_le hnonneg).false
  simp only [hk] at hle hnonneg
  have hneg (j : ℕ) (hj : j ≤ k) : P.coroot' i ((C ⟨j, by omega⟩).1 • lam) < 0 :=
    lt_of_not_ge fun hj' ↦ Nat.find_min hex (by omega) ⟨by omega, hj'⟩
  -- The cover `x_{k+1} ⋖ x_k` is `sᵢ x_k ⋖ x_k`.
  have hcov := C.minimalCosetRepCovBy ⟨k, hle⟩
  simp only [Fin.castSucc_mk, Fin.succ_mk] at hcov
  have hrefl := reflection_smul_eq_of_minimalCosetRepCovBy_of_coroot'_neg hlam hcov i
    (hneg k le_rfl) hnonneg
  have heq : (C ⟨k + 1, by omega⟩).1 = (weylCoxeterSystem P b).simple i * (C ⟨k, by omega⟩).1 :=
    eq_of_isMinimalCosetRep_of_smul_eq hlam hcov.isMinimalCosetRep_left
      (isMinimalCosetRep_simple_mul_of_coroot'_ne_zero hcov.isMinimalCosetRep_right
        (hneg k le_rfl).ne)
      (by rw [simple_mul_smul_eq_reflection, hrefl])
  -- Reflect the start `x₀ ⋗ ⋯ ⋗ x_k` of the chain.
  set E := C.take ⟨k, by omega⟩
  have hE : (∀ j, 0 < P.coroot' i ((E j).1 • lam)) ∨ ∀ j, P.coroot' i ((E j).1 • lam) < 0 :=
    Or.inr fun j ↦ hneg j (by have : (j : ℕ) < k + 1 := j.2; omega)
  set D := _root_.CoxeterSystem.MinimalCosetRepChain.simpleMul hlam E i hE
  have hjoin : D.last = (C.drop ⟨k + 1, by omega⟩).head :=
    Subtype.ext (by simpa [D, E] using heq.symm)
  refine ⟨D.smash (C.drop ⟨k + 1, by omega⟩) hjoin, by simp [D, E], by simp,
    (isAChain_smash_iff hjoin).mpr ⟨?_, hC.drop _⟩⟩
  exact _root_.CoxeterSystem.MinimalCosetRepChain.isAChain_simpleMul_iff.mpr (hC.take _)

end RootDatum

end TauCeti
