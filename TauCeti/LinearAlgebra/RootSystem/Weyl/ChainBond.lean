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

The `a`-chain condition makes the corresponding Lakshmibai–Seshadri paths integral where it
matters. Along an `a`-chain from `x` to `y` every integral pairing changes by an `a`-integral
amount: `a (f (x λ) - f (y λ)) ∈ ℤ`. If moreover the chain crosses a simple wall,
`⟨x λ, αᵢ^∨⟩ < 0 ≤ ⟨y λ, αᵢ^∨⟩`, then its first crossing cover is the simple reflection `sᵢ`, by the
lifting property, and so `a ⟨x λ, αᵢ^∨⟩ ∈ ℤ`. For a path running along orbit weights `τ_k λ`
between breaks `t_k` linked by `t_{k+1}`-chains, this makes the running height
`⟨π(t), αᵢ^∨⟩` integral at every break where it stops decreasing, and at the endpoint; hence its
minimum is an integer. These are the integrality properties under which Littelmann's root
operators on such paths have the string lengths `ε_i = -min H_i` and `φ_i = H_i(1) - min H_i`.

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
* `TauCeti.dvd_bondGcd_iff` and `TauCeti.bondGcd_dvd`: the bond gcd is the gcd of the bonds, as a
  divisibility characterization.
* `TauCeti.bondGcd_eq_zero_iff`: the bond gcd is positive exactly when the chain is nonempty.
* `TauCeti.bondGcd_smash` and `TauCeti.isAChain_smash_iff`: the bond gcd and the `a`-chain
  condition of a concatenation of two chains; `TauCeti.bondGcd_snoc` and
  `TauCeti.isAChain_snoc_iff` for the extension of a chain by one cover.
* `TauCeti.IsAChain.exists_mul_sub_eq_intCast`: along an `a`-chain from `x` to `y`,
  `a (f (x λ) - f (y λ))` is an integer for every integral linear form `f`.
* `TauCeti.IsAChain.exists_mul_coroot'_eq_intCast`: **an `a`-chain from `x` to `y` with
  `⟨x λ, αᵢ^∨⟩ < 0 ≤ ⟨y λ, αᵢ^∨⟩` has `a ⟨x λ, αᵢ^∨⟩ ∈ ℤ`**.
* `TauCeti.exists_sum_coroot'_eq_intCast_of_isAChain`,
  `TauCeti.exists_sum_eq_intCast_of_isAChain` and
  `TauCeti.exists_isLeast_sum_coroot'_eq_intCast_of_isAChain`: **the heights of a path along
  `a`-chains are integral at the breaks where they stop decreasing and at the endpoint, and their
  minimum is an integer**.

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

/-- A natural number divides the bond gcd `d(C)` of a saturated chain exactly when it divides the
bond of every cover of the chain. -/
theorem dvd_bondGcd_iff {n : ℕ}
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)} :
    n ∣ bondGcd lam C ↔ ∀ i : Fin C.length,
      n ∣ (P.reflectionBond b ((C i.castSucc).1 • lam) ((C i.succ).1 • lam)).natAbs := by
  simp only [bondGcd, Finset.dvd_gcd_iff, Finset.mem_univ, true_imp_iff]

/-- The bond gcd `d(C)` of a saturated chain divides the bond of each cover of the chain. -/
theorem bondGcd_dvd
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)} (i : Fin C.length) :
    bondGcd lam C ∣ (P.reflectionBond b ((C i.castSucc).1 • lam) ((C i.succ).1 • lam)).natAbs :=
  Finset.gcd_dvd (Finset.mem_univ i)

/-- **A saturated chain is an `a`-chain exactly when the denominator of `a` divides its bond
gcd.** Writing `a = p / q` in lowest terms with `q > 0`, the integrality of `a` times every bond of
the chain `C` is the divisibility `q ∣ d(C)`. -/
theorem isAChain_iff_den_dvd_bondGcd
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)} :
    IsAChain a lam C ↔ a.den ∣ bondGcd lam C := by
  simp only [IsAChain, dvd_bondGcd_iff, ← Int.natCast_dvd, Rat.den_dvd_iff_exists_mul_intCast_eq]

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

/-- The chain of length `0` is an `a`-chain for every `a`. -/
@[simp]
theorem isAChain_singleton
    (y : {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}) :
    IsAChain a lam (RelSeries.singleton _ y) :=
  fun i ↦ i.elim0

/-- A saturated chain extended by one more cover `y ⋖ x_l` at its end is an `a`-chain exactly when
the chain is an `a`-chain and `a` times the bond `b_λ(x_l, y)` of the new cover is an integer. -/
@[simp]
theorem isAChain_snoc_iff
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)}
    {y : {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    (h : (weylCoxeterSystem P b).MinimalCosetRepCovBy (P.wallIndices b lam) y C.last) :
    IsAChain a lam (C.snoc y h) ↔ IsAChain a lam C ∧
      ∃ z : ℤ, a * P.reflectionBond b (C.last.1 • lam) (y.1 • lam) = z := by
  simp only [isAChain_iff_den_dvd_bondGcd, bondGcd_snoc, Nat.dvd_gcd_iff, ← Int.natCast_dvd,
    Rat.den_dvd_iff_exists_mul_intCast_eq]

/-- An initial segment `x₀ ⋗ ⋯ ⋗ x_k` of an `a`-chain is an `a`-chain. -/
theorem IsAChain.take
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)}
    (hC : IsAChain a lam C) (k : Fin (C.length + 1)) : IsAChain a lam (C.take k) :=
  fun j ↦ hC ⟨j, Nat.lt_of_lt_of_le j.2 (Nat.lt_succ_iff.mp k.2)⟩

/-- **The bond gcd of the chain `sᵢ ⋗ 1`.** For a simple root `αᵢ` with `⟨λ, αᵢ^∨⟩ ≠ 0`, the
simple reflection `sᵢ` covers the identity in `W / W_λ`, and the saturated chain `sᵢ ⋗ 1` has bond
gcd `|⟨λ, αᵢ^∨⟩|`. So it is an `a`-chain exactly when the denominator of `a` divides
`⟨λ, αᵢ^∨⟩`. -/
theorem bondGcd_snoc_singleton_simple_one {i : b.support} (hi : P.coroot' i lam ≠ 0) :
    bondGcd lam ((RelSeries.singleton _ ⟨(weylCoxeterSystem P b).simple i,
      (minimalCosetRepCovBy_one_simple_of_coroot'_ne_zero hi).isMinimalCosetRep_right⟩ :
        (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)).snoc
      ⟨1, (minimalCosetRepCovBy_one_simple_of_coroot'_ne_zero hi).isMinimalCosetRep_left⟩
      (minimalCosetRepCovBy_one_simple_of_coroot'_ne_zero hi)) =
      (P.coroot' i lam).natAbs := by
  refine (bondGcd_snoc _).trans ?_
  rw [bondGcd_singleton, Nat.gcd_zero_left, RelSeries.last_singleton,
    reflectionBond_simple_smul_one_smul i]

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

/-! ### Integrality along `a`-chains -/

/-- **Integral linear forms on the two ends of an `a`-chain differ by an `a`-integral amount.** If
`C : x₀ ⋗ x₁ ⋗ ⋯ ⋗ x_l` is an `a`-chain of `W / W_λ`, then `a (f (x₀ λ) - f (x_l λ))` is an
integer for every integral linear form `f` on the weight lattice, for instance for the pairing
`⟨-, β^∨⟩` with any coroot. -/
theorem IsAChain.exists_mul_sub_eq_intCast (hlam : lam ∈ dominantChamber P b)
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)}
    (hC : IsAChain a lam C) (f : Module.Dual ℤ M) :
    ∃ z : ℤ, a * (f (C.head.1 • lam) - f (C.last.1 • lam) : ℤ) = z := by
  -- Telescope along the chain, one cover at a time.
  suffices key : ∀ k (hk : k ≤ C.length),
      ∃ z : ℤ, a * (f ((C 0).1 • lam) - f ((C ⟨k, Nat.lt_succ_of_le hk⟩).1 • lam) : ℤ) = z from
    key C.length le_rfl
  intro k hk
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨z₁, hz₁⟩ := ih (Nat.le_of_succ_le hk)
    obtain ⟨z₂, hz₂⟩ := exists_mul_sub_eq_intCast_of_minimalCosetRepCovBy hlam
      (C.minimalCosetRepCovBy ⟨k, hk⟩) (hC ⟨k, hk⟩) f
    simp only [Fin.castSucc_mk, Fin.succ_mk] at hz₂
    refine ⟨z₁ + z₂, ?_⟩
    rw [Int.cast_add, ← hz₁, ← hz₂]
    simp only [Int.cast_sub]
    ring

/-- **Littelmann's integrality at a simple wall.** Let `C : x₀ ⋗ ⋯ ⋗ x_l` be an `a`-chain of
`W / W_λ` and `αᵢ` a simple root with `⟨x₀ λ, αᵢ^∨⟩ < 0 ≤ ⟨x_l λ, αᵢ^∨⟩`. Then `a ⟨x₀ λ, αᵢ^∨⟩`
is an integer. At the first cover `x_h ⋖ x_{h-1}` crossing the wall, the root label is `αᵢ`
(`TauCeti.reflection_smul_eq_of_minimalCosetRepCovBy_of_coroot'_neg`), so `a ⟨x_{h-1} λ, αᵢ^∨⟩`
is an integer, and the part of `C` before it changes the pairing by an `a`-integral amount. -/
theorem IsAChain.exists_mul_coroot'_eq_intCast (hlam : lam ∈ dominantChamber P b)
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)}
    (hC : IsAChain a lam C) (i : b.support) (hhead : P.coroot' i (C.head.1 • lam) < 0)
    (hlast : 0 ≤ P.coroot' i (C.last.1 • lam)) :
    ∃ z : ℤ, a * P.coroot' i (C.head.1 • lam) = z := by
  -- The first index `h` at which the pairing is nonnegative.
  have hex : ∃ k, ∃ hk : k ≤ C.length,
      0 ≤ P.coroot' i ((C ⟨k, Nat.lt_succ_of_le hk⟩).1 • lam) := ⟨C.length, le_rfl, hlast⟩
  classical
  obtain ⟨hle, hnonneg⟩ := Nat.find_spec hex
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := Nat.exists_eq_succ_of_ne_zero fun h0 ↦ by
    simp only [h0] at hnonneg
    exact (hhead.trans_le hnonneg).false
  simp only [hk] at hle hnonneg
  have hneg : P.coroot' i ((C ⟨k, by omega⟩).1 • lam) < 0 :=
    lt_of_not_ge fun hk' ↦ Nat.find_min hex (hk ▸ Nat.lt_succ_self k) ⟨by omega, hk'⟩
  -- The cover `x_{k+1} ⋖ x_k` is the simple reflection, so its bond is `-⟨x_k λ, αᵢ^∨⟩`.
  have hcov := C.minimalCosetRepCovBy ⟨k, hle⟩
  have hrefl := reflection_smul_eq_of_minimalCosetRepCovBy_of_coroot'_neg hlam hcov i hneg
    hnonneg
  obtain ⟨z₁, hz₁⟩ := hC ⟨k, hle⟩
  rw [reflectionBond_eq_neg_coroot' (b.isPos_of_mem_support i.2) hrefl
    (smul_ne_smul_of_minimalCosetRepCovBy hlam hcov)] at hz₁
  -- The initial segment `x₀ ⋗ ⋯ ⋗ x_k` of `C` is again an `a`-chain.
  obtain ⟨z₂, hz₂⟩ := (hC.take ⟨k, by omega⟩).exists_mul_sub_eq_intCast hlam (P.coroot' i)
  refine ⟨z₂ - z₁, ?_⟩
  simp only [RelSeries.head_take, RelSeries.last_take] at hz₂
  simp only [Fin.castSucc_mk] at hz₁
  push_cast at hz₁ hz₂ ⊢
  linear_combination hz₂ - hz₁

/-! ### Heights of Lakshmibai–Seshadri paths at their breaks

A Lakshmibai–Seshadri path of shape `λ` runs, for `0 ≤ k < s`, along the orbit weight `τ_k λ`
during the time interval `[t_k, t_{k+1}]`, starting at time `t_0 = 0`, and each break `t_{k+1}`
between `τ_k` and `τ_{k+1}` carries a `t_{k+1}`-chain from `τ_k` down to `τ_{k+1}`. Its value at
the `j`-th break, paired with an integral linear form `f`, is the vertex height
`∑_{k < j} (t_{k+1} - t_k) f (τ_k λ)`. The results below need only the chains, not the order of
the cosets or of the times, except where stated. -/

/-- **Heights at breaks, up to integers.** If consecutive orbit weights `τ_k λ` and `τ_{k+1} λ` are
joined by `t_{k+1}`-chains for `k + 1 < s` and `t_0 = 0`, then for `j < s` the height
`∑_{k ≤ j} (t_{k+1} - t_k) f (τ_k λ)` at the break `t_{j+1}` differs from `t_{j+1} f (τ_j λ)` by
an integer, for every integral linear form `f`. -/
theorem exists_sum_sub_mul_eq_intCast_of_isAChain (hlam : lam ∈ dominantChamber P b)
    {s : ℕ} {τ : ℕ → P.weylGroup} {t : ℕ → ℚ} (ht : t 0 = 0)
    (hchain : ∀ k, k + 1 < s → ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain
      (P.wallIndices b lam), C.head.1 = τ k ∧ C.last.1 = τ (k + 1) ∧ IsAChain (t (k + 1)) lam C)
    (f : Module.Dual ℤ M) {j : ℕ} (hj : j < s) :
    ∃ z : ℤ, ∑ k ∈ Finset.range (j + 1), (t (k + 1) - t k) * f (τ k • lam) -
      t (j + 1) * f (τ j • lam) = z := by
  induction j with
  | zero => exact ⟨0, by simp [ht]⟩
  | succ j ih =>
    obtain ⟨z₁, hz₁⟩ := ih (by omega)
    obtain ⟨C, hhead, hlast, hC⟩ := hchain j hj
    obtain ⟨z₂, hz₂⟩ := hC.exists_mul_sub_eq_intCast hlam f
    rw [hhead, hlast] at hz₂
    refine ⟨z₁ + z₂, ?_⟩
    rw [Finset.sum_range_succ, Int.cast_add, ← hz₁, ← hz₂]
    push_cast
    ring

/-- **Littelmann's integrality of Lakshmibai–Seshadri paths at local minima.** With the chains of
`TauCeti.exists_sum_sub_mul_eq_intCast_of_isAChain`, let `αᵢ` be a simple root such that the
height `⟨-, αᵢ^∨⟩` stops decreasing at the break `t_{j+1}`: `⟨τ_j λ, αᵢ^∨⟩ < 0 ≤
⟨τ_{j+1} λ, αᵢ^∨⟩`. Then the height `∑_{k ≤ j} (t_{k+1} - t_k) ⟨τ_k λ, αᵢ^∨⟩` there is an
integer. -/
theorem exists_sum_coroot'_eq_intCast_of_isAChain (hlam : lam ∈ dominantChamber P b)
    {s : ℕ} {τ : ℕ → P.weylGroup} {t : ℕ → ℚ} (ht : t 0 = 0)
    (hchain : ∀ k, k + 1 < s → ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain
      (P.wallIndices b lam), C.head.1 = τ k ∧ C.last.1 = τ (k + 1) ∧ IsAChain (t (k + 1)) lam C)
    (i : b.support) {j : ℕ} (hj : j + 1 < s) (hneg : P.coroot' i (τ j • lam) < 0)
    (hnonneg : 0 ≤ P.coroot' i (τ (j + 1) • lam)) :
    ∃ z : ℤ, ∑ k ∈ Finset.range (j + 1), (t (k + 1) - t k) * P.coroot' i (τ k • lam) = z := by
  obtain ⟨z₁, hz₁⟩ :=
    exists_sum_sub_mul_eq_intCast_of_isAChain hlam ht hchain (P.coroot' i) (by omega : j < s)
  obtain ⟨C, hhead, hlast, hC⟩ := hchain j hj
  obtain ⟨z₂, hz₂⟩ := hC.exists_mul_coroot'_eq_intCast hlam i (hhead ▸ hneg) (hlast ▸ hnonneg)
  rw [hhead] at hz₂
  exact ⟨z₁ + z₂, by push_cast; linear_combination hz₁ + hz₂⟩

/-- **The endpoint of a Lakshmibai–Seshadri path is integral.** With the chains of
`TauCeti.exists_sum_sub_mul_eq_intCast_of_isAChain`, if the final time `t_s` is an integer (for a
Lakshmibai–Seshadri path, `t_s = 1`), then the final height `∑_{k < s} (t_{k+1} - t_k) f (τ_k λ)`
is an integer for every integral linear form `f`. -/
theorem exists_sum_eq_intCast_of_isAChain (hlam : lam ∈ dominantChamber P b)
    {s : ℕ} {τ : ℕ → P.weylGroup} {t : ℕ → ℚ} (ht : t 0 = 0)
    (hchain : ∀ k, k + 1 < s → ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain
      (P.wallIndices b lam), C.head.1 = τ k ∧ C.last.1 = τ (k + 1) ∧ IsAChain (t (k + 1)) lam C)
    (hs : ∃ z : ℤ, t s = z) (f : Module.Dual ℤ M) :
    ∃ z : ℤ, ∑ k ∈ Finset.range s, (t (k + 1) - t k) * f (τ k • lam) = z := by
  obtain ⟨n, rfl | rfl⟩ : ∃ n, s = 0 ∨ s = n + 1 := ⟨s - 1, by omega⟩
  · exact ⟨0, by simp⟩
  obtain ⟨z₁, hz₁⟩ :=
    exists_sum_sub_mul_eq_intCast_of_isAChain hlam ht hchain f (Nat.lt_succ_self n)
  obtain ⟨z₂, hz₂⟩ := hs
  exact ⟨z₁ + z₂ * f (τ n • lam), by rw [hz₂] at hz₁; push_cast; linear_combination hz₁⟩

/-- **The minimal height of a Lakshmibai–Seshadri path is integral.** With the chains of
`TauCeti.exists_sum_sub_mul_eq_intCast_of_isAChain`, suppose the times increase strictly,
`t_0 < t_1 < ⋯ < t_s`, and the final time `t_s` is an integer. Then for each simple root `αᵢ`
the least vertex height `∑_{k < j} (t_{k+1} - t_k) ⟨τ_k λ, αᵢ^∨⟩`, `j ≤ s`, is an integer. Since
the height is affine between breaks, this least vertex height is the minimum of the height along
the whole path. -/
theorem exists_isLeast_sum_coroot'_eq_intCast_of_isAChain (hlam : lam ∈ dominantChamber P b)
    {s : ℕ} {τ : ℕ → P.weylGroup} {t : ℕ → ℚ} (ht : t 0 = 0)
    (hchain : ∀ k, k + 1 < s → ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain
      (P.wallIndices b lam), C.head.1 = τ k ∧ C.last.1 = τ (k + 1) ∧ IsAChain (t (k + 1)) lam C)
    (hmono : ∀ k < s, t k < t (k + 1)) (hs : ∃ z : ℤ, t s = z) (i : b.support) :
    ∃ z : ℤ, IsLeast ((fun j ↦ ∑ k ∈ Finset.range j, (t (k + 1) - t k) *
      (P.coroot' i (τ k • lam) : ℚ)) '' Set.Iic s) z := by
  set H : ℕ → ℚ := fun j ↦ ∑ k ∈ Finset.range j, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ)
  -- The least index `j ≤ s` at which `H` attains its minimum on `{0, …, s}`.
  obtain ⟨m, hm, hmin⟩ := (Finset.range (s + 1)).exists_min_image H ⟨0, by simp⟩
  have hex : ∃ j, j ≤ s ∧ H j = H m := ⟨m, Nat.lt_succ_iff.mp (Finset.mem_range.mp hm), rfl⟩
  classical
  obtain ⟨hjs, hjm⟩ := Nat.find_spec hex
  have hleast : IsLeast (H '' Set.Iic s) (H (Nat.find hex)) := by
    refine ⟨⟨_, hjs, rfl⟩, ?_⟩
    rintro _ ⟨k, hk, rfl⟩
    rw [hjm]
    exact hmin k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  suffices hint : ∃ z : ℤ, H (Nat.find hex) = z by
    obtain ⟨z, hz⟩ := hint
    exact ⟨z, hz ▸ hleast⟩
  -- Either the minimum is attained at an end of the path, or the height stops decreasing there.
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · exact ⟨0, by rw [h0]; simp [H]⟩
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_one_of_ne_zero hpos.ne'
  rcases hjs.lt_or_eq with hlt | heq
  · rw [hj] at hjs hjm hlt ⊢
    -- The height decreases strictly into `j + 1`, by minimality of the index.
    have hdec : H (j + 1) < H j := lt_of_not_ge fun hge ↦
      Nat.find_min hex (by omega : j < Nat.find hex)
        ⟨by omega, le_antisymm (hge.trans hjm.le) (hmin j (Finset.mem_range.mpr (by omega)))⟩
    have hinc : H (j + 1) ≤ H (j + 2) := by
      rw [hjm]
      exact hmin (j + 2) (Finset.mem_range.mpr (by omega))
    simp only [H, Finset.sum_range_succ] at hdec hinc
    have hneg : P.coroot' i (τ j • lam) < 0 := by
      have := hmono j (by omega)
      by_contra! hnn
      have : 0 ≤ (t (j + 1) - t j) * (P.coroot' i (τ j • lam) : ℚ) :=
        mul_nonneg (by linarith) (by exact_mod_cast hnn)
      linarith
    have hnonneg : 0 ≤ P.coroot' i (τ (j + 1) • lam) := by
      have := hmono (j + 1) (by omega)
      by_contra! hn
      have : (t (j + 1 + 1) - t (j + 1)) * (P.coroot' i (τ (j + 1) • lam) : ℚ) < 0 :=
        mul_neg_of_pos_of_neg (by linarith) (by exact_mod_cast hn)
      linarith
    exact exists_sum_coroot'_eq_intCast_of_isAChain hlam ht hchain i (by omega) hneg hnonneg
  · rw [heq]
    exact exists_sum_eq_intCast_of_isAChain hlam ht hchain hs (P.coroot' i)

end TauCeti
