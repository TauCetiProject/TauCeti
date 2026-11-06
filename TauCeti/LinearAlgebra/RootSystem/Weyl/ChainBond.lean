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
`(τ, σ)`; the bond gcd turns that condition into a divisibility. The gcd does not depend on the
saturated chain from `τ` to `σ`, by `TauCeti.bondGcd_eq_intervalBondGcd` in
`TauCeti.LinearAlgebra.RootSystem.Weyl.IntervalBondGcd`.

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
* `TauCeti.bondGcd_eq_zero_iff`: the bond gcd is positive exactly when the chain is nonempty;
  `TauCeti.bondGcd_eq_zero_of_length_eq_zero` says a chain of length `0` has bond gcd `0`.
* `TauCeti.bondGcd_smash` and `TauCeti.isAChain_smash_iff`: the bond gcd and the `a`-chain
  condition of a concatenation of two chains; `TauCeti.bondGcd_snoc` and
  `TauCeti.isAChain_snoc_iff` for the extension of a chain by one cover, and
  `TauCeti.bondGcd_cons` and `TauCeti.bondGcd_eq_gcd_bondGcd_tail` at its start.
* `TauCeti.bondGcd_dvd_sub`: the bond gcd of a chain from `x` to `y` divides
  `f (x λ) - f (y λ)` for every integral linear form `f`.
* `TauCeti.IsAChain.exists_mul_sub_eq_intCast`: along an `a`-chain from `x` to `y`,
  `a (f (x λ) - f (y λ))` is an integer for every integral linear form `f`.
* `TauCeti.IsAChain.exists_mul_coroot'_eq_intCast`: **an `a`-chain from `x` to `y` with
  `⟨x λ, αᵢ^∨⟩ < 0 ≤ ⟨y λ, αᵢ^∨⟩` has `a ⟨x λ, αᵢ^∨⟩ ∈ ℤ`**.
* `TauCeti.exists_sum_coroot'_eq_intCast_of_isAChain`,
  `TauCeti.exists_sum_eq_intCast_of_isAChain` and
  `TauCeti.exists_isLeast_sum_coroot'_eq_intCast_of_isAChain`: **the heights of a path along
  `a`-chains are integral at the breaks where they stop decreasing and at the endpoint, and their
  minimum is an integer**.
* `TauCeti.exists_isLeast_sum_coroot'_Icc_of_isAChain`: the least height on a final piece of such a
  path is the height at its start or an integer.
* `TauCeti.sum_coroot'_lt_sum_coroot'_succ_of_isAChain`,
  `TauCeti.add_one_le_sum_coroot'_of_isAChain` and `TauCeti.exists_strictly_rising_of_isAChain`:
  **after its last minimum `h`, the height of such a path rises strictly until it reaches `h + 1`,
  and it stays at least `h + 1` afterwards**.

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

/-- The `a`-chain condition is integrality of `a` times each reflection bond. -/
theorem isAChain_iff_forall_reflectionBond
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)} :
    IsAChain a lam C ↔ ∀ i : Fin C.length,
      ∃ z : ℤ, a * P.reflectionBond b ((C i.castSucc).1 • lam) ((C i.succ).1 • lam) = z :=
  Iff.rfl

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

/-- The bond gcd of a saturated chain extended by one more cover `x₀ ⋖ x` at its start is the gcd
of the bond `b_λ(x, x₀)` of the new cover and the bond gcd of the chain. -/
@[simp]
theorem bondGcd_cons {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)}
    {x : {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    (h : (weylCoxeterSystem P b).MinimalCosetRepCovBy (P.wallIndices b lam) C.head x) :
    bondGcd lam (C.cons x h) =
      (P.reflectionBond b (x.1 • lam) (C.head.1 • lam)).natAbs.gcd (bondGcd lam C) := by
  -- The entries of the extended chain are `x`, followed by those of `C`.
  have hlen : (C.cons x h).length = C.length + 1 := RelSeries.cons_length C x h
  have h₀ (hk : 0 < (C.cons x h).length + 1) : C.cons x h ⟨0, hk⟩ = x :=
    (congrArg (C.cons x h) (Fin.ext (by simp))).trans (RelSeries.head_cons C x h)
  have hs (j : ℕ) (hj : j < C.length + 1) (hk : j + 1 < (C.cons x h).length + 1) :
      C.cons x h ⟨j + 1, hk⟩ = C ⟨j, hj⟩ :=
    (congrArg (C.cons x h) (Fin.ext (by simp))).trans (RelSeries.cons_cast_succ C x h ⟨j, hj⟩)
  have hC₀ : C ⟨0, Nat.succ_pos _⟩ = C.head := congrArg C (Fin.ext (by simp))
  refine Nat.dvd_antisymm (Nat.dvd_gcd ?_ (dvd_bondGcd_iff.mpr fun i ↦ ?_))
    (dvd_bondGcd_iff.mpr fun ⟨k, hk⟩ ↦ ?_)
  · have := bondGcd_dvd (C := C.cons x h) ⟨0, by omega⟩
    rwa [Fin.castSucc_mk, Fin.succ_mk, h₀, hs 0 (Nat.succ_pos _), hC₀] at this
  · have := bondGcd_dvd (C := C.cons x h) ⟨i + 1, by omega⟩
    rwa [Fin.castSucc_mk, Fin.succ_mk, hs i (by omega), hs (i + 1) (by omega)] at this
  · cases k with
    | zero =>
      rw [Fin.castSucc_mk, Fin.succ_mk, h₀, hs 0 (Nat.succ_pos _), hC₀]
      exact Nat.gcd_dvd_left _ _
    | succ j =>
      rw [Fin.castSucc_mk, Fin.succ_mk, hs j (by omega), hs (j + 1) (by omega)]
      exact (Nat.gcd_dvd_right _ _).trans (bondGcd_dvd ⟨j, by omega⟩)

/-- The bond gcd of a saturated chain `x₀ ⋗ x₁ ⋗ ⋯ ⋗ x_l` of positive length is the gcd of the
bond `b_λ(x₀, x₁)` of its first cover and the bond gcd of its tail `x₁ ⋗ ⋯ ⋗ x_l`. -/
theorem bondGcd_eq_gcd_bondGcd_tail
    (C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)) (h : C.length ≠ 0) :
    bondGcd lam C = (P.reflectionBond b (C.head.1 • lam) ((C.tail h).head.1 • lam)).natAbs.gcd
      (bondGcd lam (C.tail h)) := by
  have hcov : (weylCoxeterSystem P b).MinimalCosetRepCovBy (P.wallIndices b lam)
      (C.tail h).head C.head := C.step ⟨0, Nat.pos_of_ne_zero h⟩
  have hC : (C.tail h).cons C.head hcov = C := RelSeries.cons_self_tail h
  rw [← bondGcd_cons hcov, hC]

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

/-- A final segment `x_k ⋗ ⋯ ⋗ x_l` of an `a`-chain is an `a`-chain. -/
theorem IsAChain.drop
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)}
    (hC : IsAChain a lam C) (k : Fin (C.length + 1)) : IsAChain a lam (C.drop k) := fun j ↦ by
  have hj : (j : ℕ) + k < C.length := by
    have : (j : ℕ) < C.length - k := j.2
    omega
  obtain ⟨z, hz⟩ := hC ⟨j + k, hj⟩
  refine ⟨z, ?_⟩
  convert hz using 6
  · rfl
  · -- The entries of `C.drop k` are those of `C`, shifted by `k`, by definition.
    change C.toFun _ = C.toFun _
    congr 1
    simp only [Fin.ext_iff, Fin.val_succ]
    omega

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

omit [P.flip.IsReduced] in
/-- A saturated chain of `W / W_λ` of length `0` has bond gcd `0`, the gcd of no bonds. -/
theorem bondGcd_eq_zero_of_length_eq_zero
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)} (h : C.length = 0) :
    bondGcd lam C = 0 :=
  Finset.gcd_eq_zero_iff.mpr fun i _ ↦ (Fin.cast h i).elim0

/-- The bond gcd of a saturated chain of `W / W_λ` vanishes exactly when the chain has length `0`:
the bonds of covers are positive. -/
theorem bondGcd_eq_zero_iff (hlam : lam ∈ dominantChamber P b)
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)} :
    bondGcd lam C = 0 ↔ C.length = 0 := by
  refine ⟨fun h ↦ ?_, bondGcd_eq_zero_of_length_eq_zero⟩
  rw [bondGcd, Finset.gcd_eq_zero_iff] at h
  by_contra hC
  have hpos := reflectionBond_pos_of_minimalCosetRepCovBy hlam
    (C.minimalCosetRepCovBy ⟨0, Nat.pos_of_ne_zero hC⟩)
  have := h ⟨0, Nat.pos_of_ne_zero hC⟩ (Finset.mem_univ _)
  omega

/-- **The bond gcd divides the change of every integral linear form along the chain.** If
`C : x₀ ⋗ x₁ ⋗ ⋯ ⋗ x_l` is a saturated chain of `W / W_λ`, then `d(C)` divides
`f (x₀ λ) - f (x_l λ)` for every integral linear form `f` on the weight lattice: each cover changes
the weight by its bond times a root. -/
theorem bondGcd_dvd_sub (hlam : lam ∈ dominantChamber P b)
    (C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam))
    (f : Module.Dual ℤ M) : (bondGcd lam C : ℤ) ∣ f (C.head.1 • lam) - f (C.last.1 • lam) := by
  induction C using RelSeries.inductionOn with
  | singleton y => simp
  | cons C x hx ih =>
    rw [bondGcd_cons, RelSeries.head_cons, RelSeries.last_cons,
      ← sub_add_sub_cancel _ (f (C.head.1 • lam))]
    obtain ⟨β, ⟨hβ, hβx⟩, -⟩ :=
      existsUnique_isPos_reflection_smul_eq_of_minimalCosetRepCovBy hlam hx
    exact dvd_add ((Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)).trans
        (Int.natAbs_dvd.mpr (reflectionBond_dvd_sub hβ hβx f)))
      ((Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)).trans ih)

/-! ### Integrality along `a`-chains -/

/-- **Integral linear forms on the two ends of an `a`-chain differ by an `a`-integral amount.** If
`C : x₀ ⋗ x₁ ⋗ ⋯ ⋗ x_l` is an `a`-chain of `W / W_λ`, then `a (f (x₀ λ) - f (x_l λ))` is an
integer for every integral linear form `f` on the weight lattice, for instance for the pairing
`⟨-, β^∨⟩` with any coroot. -/
theorem IsAChain.exists_mul_sub_eq_intCast (hlam : lam ∈ dominantChamber P b)
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)}
    (hC : IsAChain a lam C) (f : Module.Dual ℤ M) :
    ∃ z : ℤ, a * (f (C.head.1 • lam) - f (C.last.1 • lam) : ℤ) = z :=
  (Rat.den_dvd_iff_exists_mul_intCast_eq a _).mp
    ((Int.natCast_dvd_natCast.mpr (isAChain_iff_den_dvd_bondGcd.mp hC)).trans
      (bondGcd_dvd_sub hlam C f))

/-- Along an `a`-chain, the scaled difference of its endpoint weights is an actual root-lattice
vector, in every characteristic-zero linear realization. This retains the lattice information,
not only its values under integral linear forms. -/
theorem IsAChain.exists_mem_rootSpan_smul_sub_eq
    (hlam : lam ∈ dominantChamber P b)
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)}
    (hC : IsAChain a lam C) {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V] (f : M →+ V) :
    ∃ m ∈ P.rootSpan ℤ, (a : 𝕜) • (f (C.head.1 • lam) - f (C.last.1 • lam)) = f m := by
  induction C using RelSeries.inductionOn' with
  | singleton y => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | snoc C y hy ih =>
    obtain ⟨hC, z, hz⟩ := (isAChain_snoc_iff hy).mp hC
    obtain ⟨m, hm, heq⟩ := ih hC
    obtain ⟨β, ⟨hβ, hβx⟩, -⟩ :=
      existsUnique_isPos_reflection_smul_eq_of_minimalCosetRepCovBy hlam hy
    have hb := reflectionBond_eq_neg_coroot' hβ hβx
      (smul_ne_smul_of_minimalCosetRepCovBy hlam hy)
    have hz' : (a : 𝕜) * (P.coroot' β (C.last.1 • lam) : 𝕜) = (-z : ℤ) := by
      rw [hb] at hz
      exact_mod_cast (by push_cast at hz ⊢; linarith :
        a * (P.coroot' β (C.last.1 • lam) : ℚ) = (-z : ℤ))
    have hdiff : C.last.1 • lam - y.1 • lam =
        P.coroot' β (C.last.1 • lam) • P.root β := by
      rw [← hβx, RootPairing.reflection_apply]
      abel
    have hedge : (a : 𝕜) • (f (C.last.1 • lam) - f (y.1 • lam)) =
        f ((-z) • P.root β) := by
      rw [← map_sub, hdiff, map_zsmul]
      simpa only [map_zsmul, ← Int.cast_smul_eq_zsmul 𝕜, smul_smul] using
        congrArg (fun t : 𝕜 ↦ t • f (P.root β)) hz'
    refine ⟨m + (-z) • P.root β, Submodule.add_mem _ hm
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨β, rfl⟩)), ?_⟩
    simp only [RelSeries.head_snoc, RelSeries.last_snoc]
    calc
      (a : 𝕜) • (f (C.head.1 • lam) - f (y.1 • lam)) =
          (a : 𝕜) • (f (C.head.1 • lam) - f (C.last.1 • lam)) +
          (a : 𝕜) • (f (C.last.1 • lam) - f (y.1 • lam)) := by
            rw [← smul_add, sub_add_sub_cancel]
      _ = f m + f ((-z) • P.root β) := by rw [heq, hedge]
      _ = f (m + (-z) • P.root β) := (map_add f _ _).symm

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

/-- **Least heights of a Lakshmibai–Seshadri path on a final piece.** With the chains of
`TauCeti.exists_sum_sub_mul_eq_intCast_of_isAChain`, suppose the times increase strictly,
`t_0 < t_1 < ⋯ < t_s`, and the final time `t_s` is an integer. Then for each simple root `αᵢ` and
each `m ≤ s`, the least vertex height `∑_{k < j} (t_{k+1} - t_k) ⟨τ_k λ, αᵢ^∨⟩`, `m ≤ j ≤ s`, is
either the height at `m` or an integer: away from `m`, it is attained at a break where the height
stops decreasing or at the endpoint. -/
theorem exists_isLeast_sum_coroot'_Icc_of_isAChain (hlam : lam ∈ dominantChamber P b)
    {s : ℕ} {τ : ℕ → P.weylGroup} {t : ℕ → ℚ} (ht : t 0 = 0)
    (hchain : ∀ k, k + 1 < s → ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain
      (P.wallIndices b lam), C.head.1 = τ k ∧ C.last.1 = τ (k + 1) ∧ IsAChain (t (k + 1)) lam C)
    (hmono : ∀ k < s, t k < t (k + 1)) (hs : ∃ z : ℤ, t s = z) (i : b.support) {m : ℕ}
    (hm : m ≤ s) :
    ∃ z : ℚ, IsLeast ((fun j ↦ ∑ k ∈ Finset.range j, (t (k + 1) - t k) *
      (P.coroot' i (τ k • lam) : ℚ)) '' Set.Icc m s) z ∧
      (z = ∑ k ∈ Finset.range m, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ) ∨
        ∃ n : ℤ, z = n) := by
  set H : ℕ → ℚ := fun j ↦ ∑ k ∈ Finset.range j, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ)
  -- The least index `j ∈ [m, s]` at which `H` attains its minimum on `{m, …, s}`.
  obtain ⟨n, hn, hmin⟩ := (Finset.Icc m s).exists_min_image H ⟨m, by simp [hm]⟩
  have hex : ∃ j, m ≤ j ∧ j ≤ s ∧ H j = H n := ⟨n, (Finset.mem_Icc.mp hn).1,
    (Finset.mem_Icc.mp hn).2, rfl⟩
  classical
  obtain ⟨hmj, hjs, hjn⟩ := Nat.find_spec hex
  set j := Nat.find hex
  refine ⟨H j, ⟨⟨j, ⟨hmj, hjs⟩, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    rw [hjn]
    exact hmin k (Finset.mem_Icc.mpr hk)
  -- Either the minimum is attained at `m` or at the end of the path, or the height stops
  -- decreasing there.
  rcases hmj.eq_or_lt with hmj' | hmj'
  · exact Or.inl (by rw [← hmj'])
  right
  obtain ⟨j', hj'⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : j ≠ 0)
  rcases hjs.lt_or_eq with hlt | heq
  · rw [hj'] at hjs hjn hlt hmj' ⊢
    -- The height decreases strictly into `j' + 1`, by minimality of the index.
    have hdec : H (j' + 1) < H j' := lt_of_not_ge fun hge ↦
      Nat.find_min hex (by omega : j' < j)
        ⟨by omega, by omega, le_antisymm (hge.trans hjn.le) (hmin j' (Finset.mem_Icc.mpr
          ⟨by omega, by omega⟩))⟩
    have hinc : H (j' + 1) ≤ H (j' + 2) := by
      rw [hjn]
      exact hmin (j' + 2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    simp only [H, Finset.sum_range_succ] at hdec hinc
    have hneg : P.coroot' i (τ j' • lam) < 0 := by
      have := hmono j' (by omega)
      by_contra! hnn
      have : 0 ≤ (t (j' + 1) - t j') * (P.coroot' i (τ j' • lam) : ℚ) :=
        mul_nonneg (by linarith) (by exact_mod_cast hnn)
      linarith
    have hnonneg : 0 ≤ P.coroot' i (τ (j' + 1) • lam) := by
      have := hmono (j' + 1) (by omega)
      by_contra! hn
      have : (t (j' + 1 + 1) - t (j' + 1)) * (P.coroot' i (τ (j' + 1) • lam) : ℚ) < 0 :=
        mul_neg_of_pos_of_neg (by linarith) (by exact_mod_cast hn)
      linarith
    exact exists_sum_coroot'_eq_intCast_of_isAChain hlam ht hchain i (by omega) hneg hnonneg
  · rw [heq]
    exact exists_sum_eq_intCast_of_isAChain hlam ht hchain hs (P.coroot' i)

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
  obtain ⟨z, hz, h0 | ⟨n, rfl⟩⟩ :=
    exists_isLeast_sum_coroot'_Icc_of_isAChain hlam ht hchain hmono hs i (Nat.zero_le s)
  · have hIcc : Set.Icc 0 s = Set.Iic s := Set.Icc_bot
    exact ⟨0, by simpa [h0, hIcc] using hz⟩
  · have hIcc : Set.Icc 0 s = Set.Iic s := Set.Icc_bot
    exact ⟨n, by simpa [hIcc] using hz⟩

/-! ### The height of a Lakshmibai–Seshadri path after a minimum

Littelmann's lowering operator `f_αᵢ` reflects the piece of a path between the last time `t₀` at
which the height `⟨π(t), αᵢ^∨⟩` is minimal and the first later time `t₁` at which it has risen by
one. For a Lakshmibai–Seshadri path this piece is as simple as possible: the height rises
strictly from `t₀` to `t₁`, and it stays at least the minimum plus one after `t₁`. Both statements
hold more generally after any vertex at which the height is an integer, provided the height stays
strictly above that integer afterwards. -/

/-- **The height of a Lakshmibai–Seshadri path rises strictly after a minimum, up to the next
integer.** With the chains of `TauCeti.exists_sum_sub_mul_eq_intCast_of_isAChain`, strictly
increasing times and an integral final time, write
`H j = ∑_{k < j} (t_{k+1} - t_k) ⟨τ_k λ, αᵢ^∨⟩`. Suppose that the height `H k₀` is an integer and
that `H k > H k₀` for `k₀ < k ≤ s`. Then `H j < H (j + 1)` for every `k₀ ≤ j < s` with
`H j < H k₀ + 1`: a stationary height would be integral, and a decreasing one would lead to a
local minimum strictly between the integers `H k₀` and `H k₀ + 1`. -/
theorem sum_coroot'_lt_sum_coroot'_succ_of_isAChain (hlam : lam ∈ dominantChamber P b)
    {s : ℕ} {τ : ℕ → P.weylGroup} {t : ℕ → ℚ} (ht : t 0 = 0)
    (hchain : ∀ k, k + 1 < s → ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain
      (P.wallIndices b lam), C.head.1 = τ k ∧ C.last.1 = τ (k + 1) ∧ IsAChain (t (k + 1)) lam C)
    (hmono : ∀ k < s, t k < t (k + 1)) (hs : ∃ z : ℤ, t s = z) (i : b.support) {k₀ j : ℕ}
    (hk₀ : ∃ z : ℤ,
      ∑ k ∈ Finset.range k₀, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ) = z)
    (habove : ∀ k, k₀ < k → k ≤ s →
      ∑ k ∈ Finset.range k₀, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ) <
        ∑ k ∈ Finset.range k, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ))
    (hk₀j : k₀ ≤ j) (hjs : j < s)
    (hj : ∑ k ∈ Finset.range j, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ) <
      ∑ k ∈ Finset.range k₀, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ) + 1) :
    ∑ k ∈ Finset.range j, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ) <
      ∑ k ∈ Finset.range (j + 1), (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ) := by
  set H : ℕ → ℚ := fun j ↦ ∑ k ∈ Finset.range j, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ)
  obtain ⟨z, hz⟩ := hk₀
  rcases hk₀j.eq_or_lt with rfl | hk₀j
  · exact habove _ (Nat.lt_succ_self _) hjs
  have hjabove := habove j hk₀j hjs.le
  by_contra! hle
  rcases hle.eq_or_lt with heq | hlt
  · -- A stationary segment: its height is an integer.
    have hzero : P.coroot' i (τ j • lam) = 0 := by
      have hstep : H (j + 1) = H j + (t (j + 1) - t j) * (P.coroot' i (τ j • lam) : ℚ) :=
        Finset.sum_range_succ _ _
      have hpos : 0 < t (j + 1) - t j := sub_pos.mpr (hmono j hjs)
      have : (t (j + 1) - t j) * (P.coroot' i (τ j • lam) : ℚ) = 0 := by linarith
      exact_mod_cast (mul_eq_zero.mp this).resolve_left hpos.ne'
    obtain ⟨n, hn⟩ := exists_sum_sub_mul_eq_intCast_of_isAChain hlam ht hchain (P.coroot' i) hjs
    rw [hzero, Int.cast_zero, mul_zero, sub_zero] at hn
    have hHn : H j = n := heq.symm.trans hn
    have h₁ : (z : ℚ) < n := by rw [← hz, ← hHn]; exact hjabove
    have h₂ : (n : ℚ) < z + 1 := by rw [← hz, ← hHn]; exact hj
    have : z < n := by exact_mod_cast h₁
    have : n < z + 1 := by exact_mod_cast h₂
    omega
  · -- A decreasing segment: the least height after `j` is an integer strictly between `H k₀` and
    -- `H k₀ + 1`.
    obtain ⟨q, hq, hqj | ⟨n, hn⟩⟩ :=
      exists_isLeast_sum_coroot'_Icc_of_isAChain hlam ht hchain hmono hs i hjs.le
    · have hqle : q ≤ H (j + 1) := hq.2 ⟨j + 1, ⟨by omega, by omega⟩, rfl⟩
      have hqj' : q = H j := hqj
      linarith
    · obtain ⟨k, ⟨hjk, hks⟩, hkq⟩ := hq.1
      have hqle : q ≤ H (j + 1) := hq.2 ⟨j + 1, ⟨by omega, by omega⟩, rfl⟩
      have hkq' : H k = q := hkq
      have hk := habove k (by omega) hks
      have h₁ : (z : ℚ) < n := by rw [← hz, ← hn, ← hkq']; exact hk
      have h₂ : (n : ℚ) < z + 1 := by rw [← hz, ← hn]; linarith
      have : z < n := by exact_mod_cast h₁
      have : n < z + 1 := by exact_mod_cast h₂
      omega

/-- **The height of a Lakshmibai–Seshadri path stays up after rising by one from a minimum.** With
the chains of `TauCeti.exists_sum_sub_mul_eq_intCast_of_isAChain`, strictly increasing times and an
integral final time, write `H j = ∑_{k < j} (t_{k+1} - t_k) ⟨τ_k λ, αᵢ^∨⟩`. Suppose that the height
`H k₀` is an integer and that `H k > H k₀` for `k₀ < k ≤ s`. If `H k₁ ≥ H k₀ + 1` for some
`k₁ > k₀`, then `H j ≥ H k₀ + 1` for every `k₁ ≤ j ≤ s`: the least height after `k₁` is attained at
`k₁` or is an integer greater than `H k₀`. -/
theorem add_one_le_sum_coroot'_of_isAChain (hlam : lam ∈ dominantChamber P b)
    {s : ℕ} {τ : ℕ → P.weylGroup} {t : ℕ → ℚ} (ht : t 0 = 0)
    (hchain : ∀ k, k + 1 < s → ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain
      (P.wallIndices b lam), C.head.1 = τ k ∧ C.last.1 = τ (k + 1) ∧ IsAChain (t (k + 1)) lam C)
    (hmono : ∀ k < s, t k < t (k + 1)) (hs : ∃ z : ℤ, t s = z) (i : b.support) {k₀ k₁ j : ℕ}
    (hk₀ : ∃ z : ℤ,
      ∑ k ∈ Finset.range k₀, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ) = z)
    (habove : ∀ k, k₀ < k → k ≤ s →
      ∑ k ∈ Finset.range k₀, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ) <
        ∑ k ∈ Finset.range k, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ))
    (hk₀₁ : k₀ < k₁)
    (hk₁ : ∑ k ∈ Finset.range k₀, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ) + 1 ≤
      ∑ k ∈ Finset.range k₁, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ))
    (hk₁j : k₁ ≤ j) (hjs : j ≤ s) :
    ∑ k ∈ Finset.range k₀, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ) + 1 ≤
      ∑ k ∈ Finset.range j, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ) := by
  set H : ℕ → ℚ := fun j ↦ ∑ k ∈ Finset.range j, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ)
  obtain ⟨z, hz⟩ := hk₀
  obtain ⟨q, hq, hqk | ⟨n, hn⟩⟩ :=
    exists_isLeast_sum_coroot'_Icc_of_isAChain hlam ht hchain hmono hs i (hk₁j.trans hjs)
  · have hqj : q ≤ H j := hq.2 ⟨j, ⟨hk₁j, hjs⟩, rfl⟩
    have hqk' : q = H k₁ := hqk
    linarith
  · obtain ⟨k, ⟨hk₁k, hks⟩, hkq⟩ := hq.1
    have hqj : q ≤ H j := hq.2 ⟨j, ⟨hk₁j, hjs⟩, rfl⟩
    have hkq' : H k = q := hkq
    have hk := habove k (by omega) hks
    have hlt : z < n := by
      have : (z : ℚ) < n := by rw [← hz, ← hn, ← hkq']; exact hk
      exact_mod_cast this
    have hle : (z : ℚ) + 1 ≤ n := by exact_mod_cast hlt
    rw [hz]
    linarith

/-- **The rising piece of a Lakshmibai–Seshadri path at a lowering step.** With the chains of
`TauCeti.exists_sum_sub_mul_eq_intCast_of_isAChain`, strictly increasing times and an integral final
time, write `H j = ∑_{k < j} (t_{k+1} - t_k) ⟨τ_k λ, αᵢ^∨⟩` and suppose that the final height `H s`
exceeds some height `H j`, `j ≤ s`, by at least one. Then there are vertices `k₀ < k₁ ≤ s` such
that `H k₀` is the minimal height, an integer, the height rises strictly from `k₀` to `k₁` while
staying below `H k₀ + 1` before `k₁`, and it is at least `H k₀ + 1` from `k₁` on. One may take
for `k₀` the last vertex of minimal height and for `k₁` the first later vertex of height at least
`H k₀ + 1`. -/
theorem exists_strictly_rising_of_isAChain (hlam : lam ∈ dominantChamber P b)
    {s : ℕ} {τ : ℕ → P.weylGroup} {t : ℕ → ℚ} (ht : t 0 = 0)
    (hchain : ∀ k, k + 1 < s → ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain
      (P.wallIndices b lam), C.head.1 = τ k ∧ C.last.1 = τ (k + 1) ∧ IsAChain (t (k + 1)) lam C)
    (hmono : ∀ k < s, t k < t (k + 1)) (hs : ∃ z : ℤ, t s = z) (i : b.support)
    (hgap : ∃ j ≤ s,
      ∑ k ∈ Finset.range j, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ) + 1 ≤
        ∑ k ∈ Finset.range s, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ)) :
    ∃ k₀ k₁, k₀ < k₁ ∧ k₁ ≤ s ∧
      IsLeast ((fun j ↦ ∑ k ∈ Finset.range j, (t (k + 1) - t k) *
        (P.coroot' i (τ k • lam) : ℚ)) '' Set.Iic s)
        (∑ k ∈ Finset.range k₀, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ)) ∧
      (∀ j, k₀ ≤ j → j < k₁ →
        ∑ k ∈ Finset.range j, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ) <
          ∑ k ∈ Finset.range (j + 1), (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ) ∧
        ∑ k ∈ Finset.range j, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ) <
          ∑ k ∈ Finset.range k₀, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ) + 1) ∧
      ∀ j, k₁ ≤ j → j ≤ s →
        ∑ k ∈ Finset.range k₀, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ) + 1 ≤
          ∑ k ∈ Finset.range j, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ) := by
  set H : ℕ → ℚ := fun j ↦ ∑ k ∈ Finset.range j, (t (k + 1) - t k) * (P.coroot' i (τ k • lam) : ℚ)
  -- The integral minimum `z` of `H`, and the last vertex `k₀` where it is attained.
  obtain ⟨z, hz⟩ := exists_isLeast_sum_coroot'_eq_intCast_of_isAChain hlam ht hchain hmono hs i
  obtain ⟨k, hk, hkz⟩ := hz.1
  classical
  set k₀ := Nat.findGreatest (fun k ↦ H k = z) s
  have hk₀s : k₀ ≤ s := Nat.findGreatest_le s
  have hk₀z : H k₀ = z := Nat.findGreatest_spec (P := fun k ↦ H k = z) (Set.mem_Iic.mp hk) hkz
  have habove : ∀ k, k₀ < k → k ≤ s → H k₀ < H k := by
    intro k hk₀k hks
    rw [hk₀z]
    exact lt_of_le_of_ne (hz.2 ⟨k, hks, rfl⟩) (Ne.symm (Nat.findGreatest_is_greatest hk₀k hks))
  -- The first vertex `k₁` after `k₀` at which the height is at least `H k₀ + 1`.
  have hHs : H k₀ + 1 ≤ H s := by
    obtain ⟨j, hj, hjs⟩ := hgap
    rw [hk₀z]
    linarith [hz.2 ⟨j, hj, rfl⟩]
  have hk₀lt : k₀ < s := lt_of_le_of_ne hk₀s fun he ↦ by
    rw [← he] at hHs
    linarith
  have hex : ∃ k, k₀ < k ∧ k ≤ s ∧ H k₀ + 1 ≤ H k := ⟨s, hk₀lt, le_rfl, hHs⟩
  obtain ⟨hk₀₁, hk₁s, hk₁z⟩ := Nat.find_spec hex
  have hbelow : ∀ j, k₀ ≤ j → j < Nat.find hex → H j < H k₀ + 1 := by
    intro j hk₀j hjk₁
    rcases hk₀j.eq_or_lt with rfl | hk₀j
    · linarith
    · exact lt_of_not_ge fun hj ↦ Nat.find_min hex hjk₁ ⟨hk₀j, by omega, hj⟩
  refine ⟨k₀, Nat.find hex, hk₀₁, hk₁s, ⟨⟨k₀, hk₀s, rfl⟩, fun y hy ↦ hk₀z.le.trans (hz.2 hy)⟩,
    fun j hk₀j hjk₁ ↦ ⟨?_, hbelow j hk₀j hjk₁⟩, fun j hk₁j hjs ↦ ?_⟩
  · exact sum_coroot'_lt_sum_coroot'_succ_of_isAChain hlam ht hchain hmono hs i ⟨z, hk₀z⟩
      habove hk₀j (by omega) (hbelow j hk₀j hjk₁)
  · exact add_one_le_sum_coroot'_of_isAChain hlam ht hchain hmono hs i ⟨z, hk₀z⟩ habove hk₀₁
      hk₁z hk₁j hjs

end TauCeti
