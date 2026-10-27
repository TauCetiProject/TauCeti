/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.CoverBond

import TauCeti.Data.Rat.NumDenDvd

/-!
# Bond gcds and `a`-chains of saturated chains in `W / W_λ`

Let `λ` be a dominant weight for a base of a finite reduced root datum, so that the weights and the
pairings with coroots are integers. Each cover `y ⋖ x` of the parabolic quotient `W / W_λ` has a
unique positive root label `β` with `y λ = s_β (x λ)`, and a positive integer **bond**
`b_λ(x, y) = ⟨y λ, β^∨⟩ = -⟨x λ, β^∨⟩`, by `TauCeti.LinearAlgebra.RootSystem.Weyl.CoverBond`. For a
saturated chain `C : x₀ ⋗ x₁ ⋗ ⋯ ⋗ x_l` of `W / W_λ` this file defines

* the **bond gcd** `d(C)`, the gcd of the bonds `b_λ(x_{h-1}, x_h)` of its covers, with the
  convention `d(C) = 0` for the chain of length `0`;
* for a rational number `a`, the **`a`-chain** condition of Littelmann: `a ⟨x_{h-1} λ, β_h^∨⟩` is
  an integer for every cover `x_h ⋖ x_{h-1}` of `C` with root label `β_h`.

The main result is the divisibility criterion: writing `a = p / q` in lowest terms with `q > 0`,
the chain `C` is an `a`-chain exactly when `q` divides `d(C)`. Since `p` and `q` are coprime,
`a b` is an integer exactly when `q ∣ b`, and `q` divides every bond exactly when it divides their
gcd. The bond gcd of a concatenation of two chains is the gcd of their bond gcds, so being an
`a`-chain is checked piece by piece.

In Littelmann's description of the Lakshmibai–Seshadri paths of shape `λ`, a pair of cosets
`τ > σ` can follow each other at a rational break `a` exactly when there is an `a`-chain for
`(τ, σ)`; the bond gcd turns that condition into a divisibility. The gcd turns out not to depend
on the saturated chain from `τ` to `σ`; that independence is not proved here.

The weights live in a root datum (a root pairing over `ℤ`) so that bonds are integers by
construction and their gcd is defined.

## Main definitions

* `TauCeti.bondGcd`: the gcd `d(C)` of the bonds of a saturated chain of `W / W_λ`.
* `TauCeti.IsAChain`: the `a`-chain condition on a saturated chain of `W / W_λ`.

## Main results

* `TauCeti.isAChain_iff_den_dvd_bondGcd`: **a saturated chain is an `a`-chain exactly when the
  denominator of `a` divides its bond gcd**.
* `TauCeti.isAChain_iff_forall_coroot'`: the `a`-chain condition in Littelmann's form,
  `a ⟨x_{h-1} λ, β_h^∨⟩ ∈ ℤ` for the positive root label `β_h` of each cover.
* `TauCeti.bondGcd_eq_zero_iff`: the bond gcd is positive exactly when the chain is nonempty.
* `TauCeti.bondGcd_smash` and `TauCeti.isAChain_smash_iff`: the bond gcd and the `a`-chain
  condition of a concatenation of two chains.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329--346, Section 4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Section 4.
* R. Chirivì, X. Fang and P. Littelmann, *LS algebras, valuations and Schubert varieties*,
  arXiv:2203.12992, Section 2.
-/

public section

universe u w x

namespace TauCeti

open RootPairing

variable {ι : Type u} {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced]

/-- The **bond gcd** `d(C)` of a saturated chain `C : x₀ ⋗ x₁ ⋗ ⋯ ⋗ x_l` of the parabolic quotient
`W / W_λ`: the gcd of the bonds `b_λ(x_{h-1}, x_h)` of its covers, where the bond of `y ⋖ x` is
`⟨y λ, β^∨⟩` for the positive root `β` with `y λ = s_β (x λ)`. The chain of length `0` has bond gcd
`0`. -/
noncomputable def bondGcd (lam : M)
    (C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)) : ℕ :=
  Finset.univ.gcd fun i : Fin C.length ↦
    (P.reflectionBond b ((C i.castSucc).1 • lam) ((C i.succ).1 • lam)).natAbs

/-- A saturated chain `C : x₀ ⋗ x₁ ⋗ ⋯ ⋗ x_l` of the parabolic quotient `W / W_λ` is an
**`a`-chain**, for a rational number `a`, when `a` times the bond `b_λ(x_{h-1}, x_h)` of each of its
covers is an integer. With the positive root label `β_h` of the cover `x_h ⋖ x_{h-1}` this is
Littelmann's condition that `a ⟨x_{h-1} λ, β_h^∨⟩` is an integer
(`TauCeti.isAChain_iff_forall_coroot'`). -/
def IsAChain (a : ℚ) (lam : M)
    (C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)) : Prop :=
  ∀ i : Fin C.length,
    ∃ z : ℤ, a * P.reflectionBond b ((C i.castSucc).1 • lam) ((C i.succ).1 • lam) = z

variable {a : ℚ} {lam : M}

/-- **A saturated chain is an `a`-chain exactly when the denominator of `a` divides its bond
gcd.** Writing `a = p / q` in lowest terms with `q > 0`, the integrality of `a` times every bond of
the chain `C` is the divisibility `q ∣ d(C)`. -/
theorem isAChain_iff_den_dvd_bondGcd
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)} :
    IsAChain a lam C ↔ a.den ∣ bondGcd lam C := by
  simp only [IsAChain, bondGcd, Finset.dvd_gcd_iff, Finset.mem_univ, true_imp_iff,
    ← Int.natCast_dvd, Rat.den_dvd_iff_exists_mul_intCast_eq]

/-- The chain of length `0` has bond gcd `0`. -/
@[simp]
theorem bondGcd_singleton
    (y : {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}) :
    bondGcd lam (RelSeries.singleton _ y) = 0 :=
  Finset.gcd_empty

/-- The bond gcd of the concatenation of two saturated chains, the second starting where the first
ends, is the gcd of their bond gcds. -/
@[simp]
theorem bondGcd_smash
    {C D : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)}
    (h : C.last = D.head) : bondGcd lam (C.smash D h) = (bondGcd lam C).gcd (bondGcd lam D) := by
  -- The covers of the concatenation are those of `C`, followed by those of `D`.
  have hC (i : Fin C.length) :
      (P.reflectionBond b (((C.smash D h) (i.castAdd D.length).castSucc).1 • lam)
        (((C.smash D h) (i.castAdd D.length).succ).1 • lam)).natAbs =
      (P.reflectionBond b ((C i.castSucc).1 • lam) ((C i.succ).1 • lam)).natAbs := by
    rw [RelSeries.smash_castAdd, RelSeries.smash_succ_castAdd]
  have hD (i : Fin D.length) :
      (P.reflectionBond b (((C.smash D h) (i.natAdd C.length).castSucc).1 • lam)
        (((C.smash D h) (i.natAdd C.length).succ).1 • lam)).natAbs =
      (P.reflectionBond b ((D i.castSucc).1 • lam) ((D i.succ).1 • lam)).natAbs := by
    rw [RelSeries.smash_natAdd, RelSeries.smash_succ_natAdd]
  refine Nat.dvd_antisymm (Nat.dvd_gcd (Finset.dvd_gcd fun i _ ↦ ?_)
    (Finset.dvd_gcd fun i _ ↦ ?_)) (Finset.dvd_gcd fun i _ ↦ ?_)
  · exact (Finset.gcd_dvd (Finset.mem_univ (i.castAdd D.length))).trans (hC i).dvd
  · exact (Finset.gcd_dvd (Finset.mem_univ (i.natAdd C.length))).trans (hD i).dvd
  · induction i using Fin.addCases with
    | left i =>
      exact (Nat.gcd_dvd_left _ _).trans
        ((Finset.gcd_dvd (Finset.mem_univ i)).trans (hC i).symm.dvd)
    | right i =>
      exact (Nat.gcd_dvd_right _ _).trans
        ((Finset.gcd_dvd (Finset.mem_univ i)).trans (hD i).symm.dvd)

/-- The bond gcd of a saturated chain extended by one more cover `y ⋖ x_l` at its end is the gcd of
its bond gcd and the bond `b_λ(x_l, y)` of the new cover. -/
@[simp]
theorem bondGcd_snoc {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)}
    {y : {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    (h : (weylCoxeterSystem P b).MinimalCosetRepCovBy (P.wallIndices b lam) y C.last) :
    bondGcd lam (C.snoc y h) =
      (bondGcd lam C).gcd (P.reflectionBond b (C.last.1 • lam) (y.1 • lam)).natAbs := by
  -- The covers of the extended chain are those of `C`, followed by `y ⋖ x_l`. The index types
  -- `Fin (C.length + 1 + 1)` and `Fin ((C.snoc y h).length + 1)` agree only up to unfolding
  -- `RelSeries.snoc`, so `rw` cannot use `RelSeries.snoc_castSucc` here; `congrArg₂` can.
  have hC (i : Fin C.length) :
      (P.reflectionBond b ((C.snoc y h (i.castSucc.castSucc : Fin (C.length + 1 + 1))).1 • lam)
        ((C.snoc y h (i.castSucc.succ : Fin (C.length + 1 + 1))).1 • lam)).natAbs =
      (P.reflectionBond b ((C i.castSucc).1 • lam) ((C i.succ).1 • lam)).natAbs :=
    congrArg₂ (fun x z ↦ (P.reflectionBond b (x.1 • lam) (z.1 • lam)).natAbs)
      (RelSeries.snoc_castSucc C y h i.castSucc) (RelSeries.snoc_castSucc C y h i.succ)
  have hy : (P.reflectionBond b
      ((C.snoc y h ((Fin.last C.length).castSucc : Fin (C.length + 1 + 1))).1 • lam)
        ((C.snoc y h (Fin.last (C.length + 1))).1 • lam)).natAbs =
      (P.reflectionBond b (C.last.1 • lam) (y.1 • lam)).natAbs :=
    congrArg₂ (fun x z ↦ (P.reflectionBond b (x.1 • lam) (z.1 • lam)).natAbs)
      (RelSeries.snoc_castSucc C y h (Fin.last C.length)) (RelSeries.last_snoc' C y h)
  have key (j : Fin (C.length + 1)) :
      (bondGcd lam C).gcd (P.reflectionBond b (C.last.1 • lam) (y.1 • lam)).natAbs ∣
        (P.reflectionBond b ((C.snoc y h (j.castSucc : Fin (C.length + 1 + 1))).1 • lam)
          ((C.snoc y h (j.succ : Fin (C.length + 1 + 1))).1 • lam)).natAbs := by
    induction j using Fin.lastCases with
    | last => exact (Nat.gcd_dvd_right _ _).trans hy.symm.dvd
    | cast i =>
      exact (Nat.gcd_dvd_left _ _).trans
        ((Finset.gcd_dvd (Finset.mem_univ i)).trans (hC i).symm.dvd)
  refine Nat.dvd_antisymm (Nat.dvd_gcd (Finset.dvd_gcd fun i _ ↦ ?_) ?_)
    (Finset.dvd_gcd fun j _ ↦ key j)
  · exact (Finset.gcd_dvd (Finset.mem_univ (i.castSucc : Fin (C.length + 1)))).trans (hC i).dvd
  · exact (Finset.gcd_dvd (Finset.mem_univ (Fin.last C.length))).trans hy.dvd

/-- The concatenation of two saturated chains, the second starting where the first ends, is an
`a`-chain exactly when both pieces are. -/
@[simp]
theorem isAChain_smash_iff
    {C D : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)}
    (h : C.last = D.head) : IsAChain a lam (C.smash D h) ↔ IsAChain a lam C ∧ IsAChain a lam D := by
  simp only [isAChain_iff_den_dvd_bondGcd, bondGcd_smash, Nat.dvd_gcd_iff]

variable [P.flip.IsReduced]

/-- **The `a`-chain condition in Littelmann's form.** A saturated chain `x₀ ⋗ x₁ ⋗ ⋯ ⋗ x_l` of
`W / W_λ` is an `a`-chain exactly when `a ⟨x_{h-1} λ, β^∨⟩` is an integer for every cover
`x_h ⋖ x_{h-1}` and every positive root `β` with `x_h λ = s_β (x_{h-1} λ)`. Such a root exists and
is unique (`TauCeti.existsUnique_isPos_reflection_smul_eq_of_minimalCosetRepCovBy`), and
`⟨x_{h-1} λ, β^∨⟩ < 0`. -/
theorem isAChain_iff_forall_coroot' (hlam : lam ∈ dominantChamber P b)
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)} :
    IsAChain a lam C ↔ ∀ i : Fin C.length, ∀ β, b.IsPos β →
      P.reflection β ((C i.castSucc).1 • lam) = (C i.succ).1 • lam →
        ∃ z : ℤ, a * P.coroot' β ((C i.castSucc).1 • lam) = z := by
  refine ⟨fun hC i β hβ hβx ↦ ?_, fun hC i ↦ ?_⟩
  · obtain ⟨z, hz⟩ := hC i
    refine ⟨-z, ?_⟩
    rw [reflectionBond_eq_neg_coroot' hβ hβx
      (smul_ne_smul_of_minimalCosetRepCovBy hlam (C.minimalCosetRepCovBy i))] at hz
    push_cast at hz ⊢
    linarith
  · obtain ⟨β, ⟨hβ, hβx⟩, -⟩ :=
      existsUnique_isPos_reflection_smul_eq_of_minimalCosetRepCovBy hlam (C.minimalCosetRepCovBy i)
    obtain ⟨z, hz⟩ := hC i β hβ hβx
    refine ⟨-z, ?_⟩
    rw [reflectionBond_eq_neg_coroot' hβ hβx
      (smul_ne_smul_of_minimalCosetRepCovBy hlam (C.minimalCosetRepCovBy i))]
    push_cast at hz ⊢
    linarith

/-- The bond gcd of a saturated chain of `W / W_λ` vanishes exactly when the chain has length `0`:
the bonds of covers are positive. -/
theorem bondGcd_eq_zero_iff (hlam : lam ∈ dominantChamber P b)
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)} :
    bondGcd lam C = 0 ↔ C.length = 0 := by
  rw [bondGcd, Finset.gcd_eq_zero_iff]
  refine ⟨fun h ↦ ?_, fun h i ↦ (Fin.cast h i).elim0⟩
  by_contra hC
  have hpos := reflectionBond_pos_of_minimalCosetRepCovBy hlam
    (C.minimalCosetRepCovBy ⟨0, Nat.pos_of_ne_zero hC⟩)
  have := h ⟨0, Nat.pos_of_ne_zero hC⟩ (Finset.mem_univ _)
  omega

/-- **The bond gcd of the chain `sᵢ ⋗ 1`.** For a simple root `αᵢ` with `⟨λ, αᵢ^∨⟩ ≠ 0`, the
simple reflection `sᵢ` covers the identity in `W / W_λ`, and the saturated chain `sᵢ ⋗ 1` has bond
gcd `|⟨λ, αᵢ^∨⟩|`. So it is an `a`-chain exactly when the denominator of `a` divides
`⟨λ, αᵢ^∨⟩`. -/
theorem bondGcd_snoc_singleton_simple_one (hlam : lam ∈ dominantChamber P b) {i : b.support}
    (hi : P.coroot' i lam ≠ 0) :
    bondGcd lam ((RelSeries.singleton _ ⟨(weylCoxeterSystem P b).simple i,
      (minimalCosetRepCovBy_one_simple_of_coroot'_ne_zero hlam hi).isMinimalCosetRep_right⟩ :
        (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)).snoc
      ⟨1, (minimalCosetRepCovBy_one_simple_of_coroot'_ne_zero hlam hi).isMinimalCosetRep_left⟩
      (minimalCosetRepCovBy_one_simple_of_coroot'_ne_zero hlam hi)) =
      (P.coroot' i lam).natAbs := by
  refine (bondGcd_snoc _).trans ?_
  rw [bondGcd_singleton, Nat.gcd_zero_left, RelSeries.last_singleton,
    reflectionBond_simple_smul_one_smul hlam hi]

end TauCeti
