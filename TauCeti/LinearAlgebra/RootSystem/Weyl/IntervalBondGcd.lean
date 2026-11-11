/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.ChainProperty
public import TauCeti.LinearAlgebra.RootSystem.Weyl.ChainBond

/-!
# The interval bond gcd `d_λ(x, y)` of `W / W_λ`

Let `λ` be a dominant weight for a base of a finite reduced root datum, and let `y ≤ x` be minimal
coset representatives of the stabilizer `W_λ`. Each saturated chain `C : x = x₀ ⋗ x₁ ⋗ ⋯ ⋗ x_l = y`
of the parabolic quotient `W / W_λ` has a bond gcd `d(C)`, the gcd of the bonds `b_λ(x_{h-1}, x_h)`
of its covers (`TauCeti.bondGcd`). The main result of this file is that **`d(C)` does not depend on
the chain `C`**, only on its ends. This defines the **interval bond gcd** `d_λ(x, y)` of
Chirivì–Fang–Littelmann, with `d_λ(x, x) = 0`.

With it, Littelmann's `a`-chain condition becomes a condition on the pair `(x, y)` alone: writing
`a = p / q` in lowest terms with `q > 0`, one saturated chain from `x` down to `y` is an `a`-chain
exactly when `q ∣ d_λ(x, y)`, exactly when every saturated chain from `x` down to `y` is an
`a`-chain. So in the description of the Lakshmibai–Seshadri paths of shape `λ`, the existence of an
`a`-chain at a break does not depend on which saturated chain is tested.

The proof is a chain-sorting induction on the length of `x`, along a left descent `sᵢ` of `x`.
Two kinds of local moves compare chains. If `z ⋖ x` is a cover with `z ≠ sᵢ x`, then `sᵢ` is also
a left descent of `z` and `sᵢ z ⋖ sᵢ x`, so the length-two interval from `sᵢ z` to `x` has the two
intermediate elements `z` and `sᵢ x`. Its two chains have the same bond gcd: the bonds of `z ⋖ x`
and `sᵢ z ⋖ sᵢ x` agree, since `sᵢ` carries the root label of one to that of the other, and the
bonds `|⟨x λ, αᵢ^∨⟩|` and `|⟨z λ, αᵢ^∨⟩|` of `sᵢ x ⋖ x` and `sᵢ z ⋖ z` are congruent modulo it.
Second, a chain `x ⋗ sᵢ x ⋗ ⋯ ⋗ y` with `sᵢ y < y` is compared with the chain obtained from its
tail by appending `sᵢ y ⋖ y`: the two simple bonds `|⟨x λ, αᵢ^∨⟩|` and `|⟨y λ, αᵢ^∨⟩|` are
congruent modulo the bond gcd of the tail, which divides `⟨sᵢ x λ - y λ, αᵢ^∨⟩`
(`TauCeti.bondGcd_dvd_sub`). Every chain is moved by these steps onto one from `sᵢ x` to `sᵢ y`
when `sᵢ` is a left descent of `y`, and onto one through `sᵢ x` when it is not; the lifting
property of the Bruhat order provides the required comparisons.

## Main definitions

* `TauCeti.intervalBondGcd`: the interval bond gcd `d_λ(x, y)`, the bond gcd of any saturated
  chain of `W / W_λ` from `x` down to `y`, and `0` when there is none.

## Main results

* `TauCeti.bondGcd_eq_of_head_eq_of_last_eq` and `TauCeti.bondGcd_eq_intervalBondGcd`: **the bond
  gcd of a saturated chain of `W / W_λ` depends only on its ends**.
* `TauCeti.isAChain_iff_den_dvd_intervalBondGcd`,
  `TauCeti.exists_isAChain_iff_den_dvd_intervalBondGcd` and
  `TauCeti.forall_isAChain_iff_den_dvd_intervalBondGcd`: **some saturated chain from `x` down to
  `y` is an `a`-chain exactly when the denominator of `a` divides `d_λ(x, y)`, exactly when every
  such chain is an `a`-chain**.
* `TauCeti.intervalBondGcd_self`, `TauCeti.intervalBondGcd_of_minimalCosetRepCovBy` and
  `TauCeti.intervalBondGcd_eq_gcd`: `d_λ(x, x) = 0`, the interval gcd of a cover is its bond, and
  `d_λ(x, z) = gcd(d_λ(x, y), d_λ(y, z))` for `z ≤ y ≤ x`.
* `TauCeti.intervalBondGcd_eq_zero_iff` and `TauCeti.intervalBondGcd_eq_zero_of_not_bruhatLE`:
  for minimal coset representatives `y ≤ x`, `d_λ(x, y) = 0` exactly when `x = y`, and
  `d_λ(x, y) = 0` unless `y ≤ x`; `TauCeti.intervalBondGcd_eq_zero_of_not_isMinimalCosetRep_left`
  and `TauCeti.intervalBondGcd_eq_zero_of_not_isMinimalCosetRep_right`: `d_λ(x, y) = 0` unless
  both `x` and `y` are minimal coset representatives.

## References

* R. Chirivì, X. Fang and P. Littelmann, *LS algebras, valuations and Schubert varieties*,
  arXiv:2203.12992, Definition 2.1 and Section 7.1.
* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329--346, Section 4.
* V. V. Deodhar, *Some characterizations of Bruhat ordering on a Coxeter group and determination
  of the relative Möbius function*, Invent. Math. 39 (1977), 187--198.
-/

public section

universe u w x

namespace TauCeti

open RootPairing

variable {ι : Type u} {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] [P.flip.IsReduced] {lam : M}

/-! ### Chain independence of the bond gcd -/

variable (b) in
/-- The bond gcd of the saturated chains of `W / W_λ` starting at `x` depends only on their last
element. -/
private def ChainIndep (lam : M) (x : P.weylGroup) : Prop :=
  ∀ C C' : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
    C.head.1 = x → C'.head.1 = x → C.last.1 = C'.last.1 → bondGcd lam C = bondGcd lam C'

variable (b) in
/-- A left descent `sᵢ` of `x` that is also a left descent of `y` moves the saturated chains of
`W / W_λ` from `x` down to `y` to those from `sᵢ x` down to `sᵢ y` without changing the bond gcd. -/
private def DescentTransport (lam : M) (x : P.weylGroup) : Prop :=
  ∀ i : b.support, (weylCoxeterSystem P b).IsLeftDescent x i →
    ∀ C D : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
      C.head.1 = x → (weylCoxeterSystem P b).IsLeftDescent C.last.1 i →
      D.head.1 = (weylCoxeterSystem P b).simple i * x →
      D.last.1 = (weylCoxeterSystem P b).simple i * C.last.1 → bondGcd lam C = bondGcd lam D

/-- **The local move across a length-two interval.** Let `z ⋖ x` be a cover with `z ≠ sᵢ x`, for a
left descent `sᵢ` of `x`. If the bond gcd is chain independent below `x`, then
`d(D) = gcd(b_λ(x, z), d(E))` for saturated chains `D` from `sᵢ x` and `E` from `sᵢ z` with the
same last element: `D` may be replaced by `E` preceded by `sᵢ z ⋖ sᵢ x`, whose bond is that of
`z ⋖ x`. -/
private theorem bondGcd_eq_gcd_of_ne_simple_mul (hlam : lam ∈ dominantChamber P b)
    {x : P.weylGroup} (hCI : ∀ x', (weylCoxeterSystem P b).length x' <
      (weylCoxeterSystem P b).length x → ChainIndep b lam x')
    {i : b.support} (hi : (weylCoxeterSystem P b).IsLeftDescent x i) {z : P.weylGroup}
    (hcov : (weylCoxeterSystem P b).MinimalCosetRepCovBy (P.wallIndices b lam) z x)
    (hc : z ≠ (weylCoxeterSystem P b).simple i * x)
    (D E : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam))
    (hD : D.head.1 = (weylCoxeterSystem P b).simple i * x)
    (hE : E.head.1 = (weylCoxeterSystem P b).simple i * z) (hl : D.last.1 = E.last.1) :
    bondGcd lam D = (P.reflectionBond b (x • lam) (z • lam)).natAbs.gcd (bondGcd lam E) := by
  have hix := (weylCoxeterSystem P b).isLeftDescent_iff.mp hi
  have hcovx := hcov.simple_mul_of_isLeftDescent (hcov.isLeftDescent_of_ne hi hc) hi
  have hE' : E.head = ⟨_, hcovx.isMinimalCosetRep_left⟩ := Subtype.ext hE
  rw [hCI _ (by omega) D (E.cons ⟨_, hcovx.isMinimalCosetRep_right⟩ (by rw [hE']; exact hcovx))
    hD rfl (by rw [RelSeries.last_cons, hl]), bondGcd_cons, hE,
    natAbs_reflectionBond_mul_smul_mul_smul hlam hcov]

/-- **A chain whose last element does not have the left descent `sᵢ` of its first element.** Let
`C` run from `x` down to `y`, where `sᵢ` is a left descent of `x` but not of `y`. If the bond gcd
is chain independent below `x`, then `d(C) = gcd(|⟨x λ, αᵢ^∨⟩|, d(D))` for every saturated chain
`D` from `sᵢ x` down to `y`. -/
private theorem bondGcd_eq_gcd_of_not_isLeftDescent (hlam : lam ∈ dominantChamber P b)
    {x : P.weylGroup} (hCI : ∀ x', (weylCoxeterSystem P b).length x' <
      (weylCoxeterSystem P b).length x → ChainIndep b lam x')
    {i : b.support} (hi : (weylCoxeterSystem P b).IsLeftDescent x i)
    (C D : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)) (hC : C.head.1 = x)
    (hy : ¬(weylCoxeterSystem P b).IsLeftDescent C.last.1 i)
    (hD : D.head.1 = (weylCoxeterSystem P b).simple i * x) (hDl : D.last.1 = C.last.1) :
    bondGcd lam C = (P.coroot' i (x • lam)).natAbs.gcd (bondGcd lam D) := by
  have hix := (weylCoxeterSystem P b).isLeftDescent_iff.mp hi
  induction C using RelSeries.inductionOn with
  | singleton y =>
    rw [RelSeries.head_singleton] at hC
    rw [RelSeries.last_singleton, hC] at hy
    exact absurd hi hy
  | cons C c hcov _ =>
    -- The chain is a first cover `C.head ⋖ x` followed by a chain `C` down to `y`.
    simp only [Set.mem_ofPred_eq] at hcov
    rw [RelSeries.head_cons] at hC
    rw [RelSeries.last_cons] at hy hDl
    subst hC
    have hclen := hcov.length_add_one_eq
    rw [bondGcd_cons]
    by_cases hc : C.head.1 = (weylCoxeterSystem P b).simple i * c.1
    · -- The chain passes through `sᵢ x`.
      rw [hc, reflectionBond_smul_simple_mul_smul, Int.natAbs_neg,
        hCI _ (by omega) C D hc hD hDl.symm]
    -- Otherwise `sᵢ C.head ⋖ C.head` and `sᵢ C.head ⋖ sᵢ x`; compare both sides with a chain `E`
    -- from `sᵢ C.head` down to `y`.
    have hcovc := CoxeterSystem.minimalCosetRepCovBy_simple_mul_of_isLeftDescent C.head.2
      (hcov.isLeftDescent_of_ne hi hc)
    obtain ⟨E, hEh, hEl⟩ := CoxeterSystem.exists_minimalCosetRepChain C.last.2
      hcovc.isMinimalCosetRep_left
      ((CoxeterSystem.MinimalCosetRepChain.bruhatLE_last_head C).bruhatLE_simple_mul hy)
    have hEh' : E.head.1 = (weylCoxeterSystem P b).simple i * C.head.1 := by rw [hEh]
    have h₁ := hCI _ (by omega) C (E.cons C.head (by rw [hEh]; exact hcovc)) rfl rfl
      (by rw [RelSeries.last_cons, hEl])
    -- `⟨C.head λ, αᵢ^∨⟩` and `⟨x λ, αᵢ^∨⟩` are congruent modulo the bond of `C.head ⋖ x`.
    obtain ⟨β, ⟨hβ, hβx⟩, -⟩ :=
      existsUnique_isPos_reflection_smul_eq_of_minimalCosetRepCovBy hlam hcov
    have key := gcd_eq_of_dvd_sub_left (reflectionBond_dvd_sub hβ hβx (P.coroot' i))
    simp only [← Int.coe_gcd, Int.natCast_inj, Int.gcd_eq_natAbs_gcd_natAbs] at key
    rw [h₁, bondGcd_cons, hEh', bondGcd_eq_gcd_of_ne_simple_mul hlam hCI hi hcov hc D E hD hEh'
      (by rw [hEl, hDl]), reflectionBond_smul_simple_mul_smul, Int.natAbs_neg, ← Nat.gcd_assoc,
      ← Nat.gcd_assoc, Nat.gcd_comm _ (P.coroot' i (C.head.1 • lam)).natAbs, ← key]

/-- **Transport of chains along a common left descent.** If the bond gcd is chain independent below
`x`, and its transport along common left descents holds below `x`, then it holds at `x`. -/
private theorem descentTransport (hlam : lam ∈ dominantChamber P b) {x : P.weylGroup}
    (hCI : ∀ x', (weylCoxeterSystem P b).length x' <
      (weylCoxeterSystem P b).length x → ChainIndep b lam x')
    (hB : ∀ x', (weylCoxeterSystem P b).length x' <
      (weylCoxeterSystem P b).length x → DescentTransport b lam x') :
    DescentTransport b lam x := by
  intro i hi C D hC hy hD hDl
  have hix := (weylCoxeterSystem P b).isLeftDescent_iff.mp hi
  induction C using RelSeries.inductionOn with
  | singleton y =>
    -- Both chains have length `0`.
    rw [RelSeries.head_singleton] at hC
    rw [RelSeries.last_singleton] at hDl
    have hDlen : D.length = 0 := by
      have := D.length_last_add_length
      rw [hDl, hD, hC] at this
      omega
    rw [bondGcd_eq_zero_of_length_eq_zero rfl, bondGcd_eq_zero_of_length_eq_zero hDlen]
  | cons C c hcov _ =>
    -- The chain is a first cover `C.head ⋖ x` followed by a chain `C` down to `y`.
    simp only [Set.mem_ofPred_eq] at hcov
    rw [RelSeries.head_cons] at hC
    rw [RelSeries.last_cons] at hy hDl
    subst hC
    have hclen := hcov.length_add_one_eq
    have hcovy := CoxeterSystem.minimalCosetRepCovBy_simple_mul_of_isLeftDescent C.last.2 hy
    rw [bondGcd_cons]
    by_cases hc : C.head.1 = (weylCoxeterSystem P b).simple i * c.1
    · -- The chain passes through `sᵢ x`: compare `D` with `C` followed by `sᵢ y ⋖ y`.
      have hD₀ := hCI _ (by omega) D (C.snoc ⟨_, hcovy.isMinimalCosetRep_left⟩ hcovy) hD
        (by rw [RelSeries.head_snoc, hc]) (by rw [RelSeries.last_snoc, hDl])
      -- `d(C)` divides `⟨sᵢ x λ - y λ, αᵢ^∨⟩ = -⟨x λ, αᵢ^∨⟩ - ⟨y λ, αᵢ^∨⟩`.
      have hd := bondGcd_dvd_sub hlam C (P.coroot' i)
      rw [hc, coroot'_simple_mul_smul_eq_neg] at hd
      have key := gcd_eq_of_dvd_sub_left hd
      simp only [← Int.coe_gcd, Int.natCast_inj, Int.gcd_eq_natAbs_gcd_natAbs] at key
      rw [Int.natAbs_neg, Int.natAbs_natCast] at key
      rw [hD₀, bondGcd_snoc, hc, reflectionBond_smul_simple_mul_smul,
        reflectionBond_smul_simple_mul_smul, Int.natAbs_neg, Int.natAbs_neg, key, Nat.gcd_comm]
    -- Otherwise `sᵢ C.head ⋖ C.head` and `sᵢ C.head ⋖ sᵢ x`; transport `C` to a chain `E` from
    -- `sᵢ C.head` down to `sᵢ y`.
    have hci := hcov.isLeftDescent_of_ne hi hc
    have hcovx := hcov.simple_mul_of_isLeftDescent hci hi
    obtain ⟨E, hEh, hEl⟩ := CoxeterSystem.exists_minimalCosetRepChain
      hcovy.isMinimalCosetRep_left hcovx.isMinimalCosetRep_left
      (CoxeterSystem.BruhatLE.simple_mul_simple_mul_of_isLeftDescent
        (CoxeterSystem.MinimalCosetRepChain.bruhatLE_last_head C) hy)
    have hEh' : E.head.1 = (weylCoxeterSystem P b).simple i * C.head.1 := by rw [hEh]
    rw [hB _ (by omega) i hci C E rfl hy hEh' (by rw [hEl]),
      bondGcd_eq_gcd_of_ne_simple_mul hlam hCI hi hcov hc D E hD hEh' (by rw [hEl, hDl])]

/-- **Chain independence at `x`**, from chain independence below `x` and the transport of chains
along common left descents at `x`. -/
private theorem chainIndep (hlam : lam ∈ dominantChamber P b) {x : P.weylGroup}
    (hCI : ∀ x', (weylCoxeterSystem P b).length x' <
      (weylCoxeterSystem P b).length x → ChainIndep b lam x')
    (hB : DescentTransport b lam x) : ChainIndep b lam x := by
  intro C C' hC hC' hl
  rcases eq_or_ne x 1 with rfl | hx1
  · -- Every saturated chain starting at `1` has length `0`.
    have h₀ (E : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam))
        (hE : E.head.1 = 1) : bondGcd lam E = 0 := by
      have := E.length_last_add_length
      rw [hE, CoxeterSystem.length_one] at this
      exact bondGcd_eq_zero_of_length_eq_zero (by omega)
    rw [h₀ C hC, h₀ C' hC']
  obtain ⟨i, hi⟩ := (weylCoxeterSystem P b).exists_leftDescent_of_ne_one hx1
  have hx : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) x := hC ▸ C.head.2
  have hyx : (weylCoxeterSystem P b).BruhatLE C.last.1 x :=
    hC ▸ CoxeterSystem.MinimalCosetRepChain.bruhatLE_last_head C
  by_cases hy : (weylCoxeterSystem P b).IsLeftDescent C.last.1 i
  · -- Both chains transport to a chain from `sᵢ x` down to `sᵢ y`.
    obtain ⟨E, hEh, hEl⟩ := CoxeterSystem.exists_minimalCosetRepChain
      (C.last.2.simple_mul_of_isLeftDescent _ hy) (hx.simple_mul_of_isLeftDescent _ hi)
      (hyx.simple_mul_simple_mul_of_isLeftDescent hy)
    rw [hB i hi C E hC hy (by rw [hEh]) (by rw [hEl]),
      hB i hi C' E hC' (by rwa [← hl]) (by rw [hEh])
        (by rw [hEl]; exact congrArg ((weylCoxeterSystem P b).simple i * ·) hl)]
  · -- Both chains have bond gcd `gcd(|⟨x λ, αᵢ^∨⟩|, d(E))` for a chain `E` from `sᵢ x` to `y`.
    obtain ⟨E, hEh, hEl⟩ := CoxeterSystem.exists_minimalCosetRepChain C.last.2
      (hx.simple_mul_of_isLeftDescent _ hi) (hyx.bruhatLE_simple_mul hy)
    rw [bondGcd_eq_gcd_of_not_isLeftDescent hlam hCI hi C E hC hy (by rw [hEh]) (by rw [hEl]),
      bondGcd_eq_gcd_of_not_isLeftDescent hlam hCI hi C' E hC' (by rwa [← hl]) (by rw [hEh])
        (by rw [hEl]; exact hl)]

/-- Chain independence and the transport along common left descents hold for every `x`, by strong
induction on the length of `x`. -/
private theorem chainIndep_and_descentTransport (hlam : lam ∈ dominantChamber P b) (n : ℕ) :
    ∀ x : P.weylGroup, (weylCoxeterSystem P b).length x < n →
      ChainIndep b lam x ∧ DescentTransport b lam x := by
  induction n with
  | zero => exact fun _ h ↦ absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro x hx
    have hCI x' (h : (weylCoxeterSystem P b).length x' < (weylCoxeterSystem P b).length x) :=
      (ih x' (by omega)).1
    have hB := descentTransport hlam hCI fun x' h ↦ (ih x' (by omega)).2
    exact ⟨chainIndep hlam hCI hB, hB⟩

/-- **The bond gcd of a saturated chain of `W / W_λ` depends only on its ends.** Two saturated
chains from `x` down to `y` have the same bond gcd. -/
theorem bondGcd_eq_of_head_eq_of_last_eq (hlam : lam ∈ dominantChamber P b)
    {C C' : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)}
    (hhead : C.head = C'.head) (hlast : C.last = C'.last) : bondGcd lam C = bondGcd lam C' :=
  (chainIndep_and_descentTransport hlam _ C.head.1 (Nat.lt_succ_self _)).1 C C' rfl
    (by rw [hhead]) (by rw [hlast])

/-! ### The interval bond gcd -/

open Classical in
variable (b) in
/-- The **interval bond gcd** `d_λ(x, y)` of minimal coset representatives `y ≤ x` of the
stabilizer of `λ`: the bond gcd of any saturated chain of `W / W_λ` from `x` down to `y`. It does
not depend on the chain (`TauCeti.bondGcd_eq_intervalBondGcd`), and `d_λ(x, x) = 0`. It is `0`
unless `y ≤ x` are both minimal coset representatives of `W_λ`, that is when there is no saturated
chain from `x` down to `y`. -/
noncomputable def intervalBondGcd (lam : M) (x y : P.weylGroup) : ℕ :=
  if h : ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
      C.head.1 = x ∧ C.last.1 = y then bondGcd lam h.choose else 0

/-- **The bond gcd of a saturated chain of `W / W_λ` is the interval bond gcd of its ends.** -/
theorem bondGcd_eq_intervalBondGcd (hlam : lam ∈ dominantChamber P b)
    (C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)) :
    bondGcd lam C = intervalBondGcd b lam C.head.1 C.last.1 := by
  have h : ∃ C' : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
      C'.head.1 = C.head.1 ∧ C'.last.1 = C.last.1 := ⟨C, rfl, rfl⟩
  rw [intervalBondGcd, dite_eq_left h]
  exact bondGcd_eq_of_head_eq_of_last_eq hlam (Subtype.ext h.choose_spec.1.symm)
    (Subtype.ext h.choose_spec.2.symm)

omit [P.flip.IsReduced] in
/-- The interval bond gcd `d_λ(x, x)` vanishes. -/
@[simp]
theorem intervalBondGcd_self (x : P.weylGroup) : intervalBondGcd b lam x x = 0 := by
  rw [intervalBondGcd]
  split_ifs with h
  · obtain ⟨hhead, hlast⟩ := h.choose_spec
    have := h.choose.length_last_add_length
    rw [hhead, hlast] at this
    exact bondGcd_eq_zero_of_length_eq_zero (by omega)
  · rfl

omit [P.flip.IsReduced] in
/-- The interval bond gcd `d_λ(x, y)` vanishes unless `y ≤ x`: then no saturated chain runs from `x`
down to `y`. -/
theorem intervalBondGcd_eq_zero_of_not_bruhatLE {x y : P.weylGroup}
    (h : ¬(weylCoxeterSystem P b).BruhatLE y x) : intervalBondGcd b lam x y = 0 := by
  rw [intervalBondGcd]
  split_ifs with hC
  · obtain ⟨C, rfl, rfl⟩ := hC
    exact (h (CoxeterSystem.MinimalCosetRepChain.bruhatLE_last_head C)).elim
  · rfl

omit [P.flip.IsReduced] in
/-- The interval bond gcd `d_λ(x, y)` vanishes unless `x` is a minimal coset representative of
`W_λ`: then no saturated chain of `W / W_λ` starts at `x`. -/
theorem intervalBondGcd_eq_zero_of_not_isMinimalCosetRep_left {x y : P.weylGroup}
    (hx : ¬(weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) x) :
    intervalBondGcd b lam x y = 0 := by
  rw [intervalBondGcd]
  split_ifs with hC
  · obtain ⟨C, rfl, -⟩ := hC
    exact (hx C.head.2).elim
  · rfl

omit [P.flip.IsReduced] in
/-- The interval bond gcd `d_λ(x, y)` vanishes unless `y` is a minimal coset representative of
`W_λ`: then no saturated chain of `W / W_λ` ends at `y`. -/
theorem intervalBondGcd_eq_zero_of_not_isMinimalCosetRep_right {x y : P.weylGroup}
    (hy : ¬(weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) y) :
    intervalBondGcd b lam x y = 0 := by
  rw [intervalBondGcd]
  split_ifs with hC
  · obtain ⟨C, -, rfl⟩ := hC
    exact (hy C.last.2).elim
  · rfl

/-- For minimal coset representatives `y ≤ x`, the interval bond gcd `d_λ(x, y)` vanishes exactly
when `x = y`: the bonds of covers are positive. -/
theorem intervalBondGcd_eq_zero_iff (hlam : lam ∈ dominantChamber P b) {x y : P.weylGroup}
    (hx : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) x)
    (hy : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) y)
    (hyx : (weylCoxeterSystem P b).BruhatLE y x) : intervalBondGcd b lam x y = 0 ↔ x = y := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ intervalBondGcd_self x⟩
  obtain ⟨C, hCh, hCl⟩ := CoxeterSystem.exists_minimalCosetRepChain hy hx hyx
  have hCx : C.head.1 = x := by rw [hCh]
  have hCy : C.last.1 = y := by rw [hCl]
  rw [← hCx, ← hCy, ← bondGcd_eq_intervalBondGcd hlam, bondGcd_eq_zero_iff hlam] at h
  rw [← hCx, ← hCy, RelSeries.subsingleton_of_length_eq_zero h C.head_mem C.last_mem]

/-- The interval bond gcd of a cover `y ⋖ x` of `W / W_λ` is its bond `b_λ(x, y)`. -/
theorem intervalBondGcd_of_minimalCosetRepCovBy (hlam : lam ∈ dominantChamber P b)
    {x y : P.weylGroup}
    (h : (weylCoxeterSystem P b).MinimalCosetRepCovBy (P.wallIndices b lam) y x) :
    intervalBondGcd b lam x y = (P.reflectionBond b (x • lam) (y • lam)).natAbs := by
  -- A saturated chain from `x` down to `y` has length `1`, and its tail has length `0`.
  obtain ⟨C, hCh, hCl⟩ := CoxeterSystem.exists_minimalCosetRepChain h.isMinimalCosetRep_left
    h.isMinimalCosetRep_right h.bruhatLE
  have hx : C.head.1 = x := by rw [hCh]
  have hy : C.last.1 = y := by rw [hCl]
  have hlen : C.length = 1 := by
    have := C.length_last_add_length
    rw [hx, hy] at this
    have := h.length_add_one_eq
    omega
  have ht : (C.tail (by omega)).length = 0 := by rw [RelSeries.tail_length, hlen]
  have hth : (C.tail (by omega)).head = C.last := by
    rw [← RelSeries.last_tail C (by omega)]
    exact RelSeries.subsingleton_of_length_eq_zero ht (RelSeries.head_mem _) (RelSeries.last_mem _)
  rw [← hx, ← hy, ← bondGcd_eq_intervalBondGcd hlam, bondGcd_eq_gcd_bondGcd_tail C (by omega),
    bondGcd_eq_zero_of_length_eq_zero ht, Nat.gcd_zero_right, hth]

/-- **The interval bond gcd of a concatenation.** For minimal coset representatives `z ≤ y ≤ x`,
`d_λ(x, z) = gcd(d_λ(x, y), d_λ(y, z))`. -/
theorem intervalBondGcd_eq_gcd (hlam : lam ∈ dominantChamber P b) {x y z : P.weylGroup}
    (hx : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) x)
    (hy : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) y)
    (hz : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) z)
    (hyx : (weylCoxeterSystem P b).BruhatLE y x) (hzy : (weylCoxeterSystem P b).BruhatLE z y) :
    intervalBondGcd b lam x z = (intervalBondGcd b lam x y).gcd (intervalBondGcd b lam y z) := by
  obtain ⟨C, hCh, hCl⟩ := CoxeterSystem.exists_minimalCosetRepChain hy hx hyx
  obtain ⟨D, hDh, hDl⟩ := CoxeterSystem.exists_minimalCosetRepChain hz hy hzy
  have := bondGcd_eq_intervalBondGcd hlam (C.smash D (hCl.trans hDh.symm))
  rw [bondGcd_smash, bondGcd_eq_intervalBondGcd hlam, bondGcd_eq_intervalBondGcd hlam,
    RelSeries.head_smash, RelSeries.last_smash, hCh, hCl, hDh, hDl] at this
  exact this.symm

/-! ### The `a`-chain criterion -/

variable {a : ℚ}

/-- **A saturated chain is an `a`-chain exactly when the denominator of `a` divides the interval
bond gcd of its ends.** -/
theorem isAChain_iff_den_dvd_intervalBondGcd (hlam : lam ∈ dominantChamber P b)
    {C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)} :
    IsAChain a lam C ↔ a.den ∣ intervalBondGcd b lam C.head.1 C.last.1 := by
  rw [isAChain_iff_den_dvd_bondGcd, bondGcd_eq_intervalBondGcd hlam]

/-- **Littelmann's `a`-chain condition depends only on the ends.** For minimal coset
representatives `y ≤ x`, there is an `a`-chain from `x` down to `y` exactly when the denominator
of `a` divides `d_λ(x, y)`. -/
theorem exists_isAChain_iff_den_dvd_intervalBondGcd (hlam : lam ∈ dominantChamber P b)
    {x y : P.weylGroup} (hx : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) x)
    (hy : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) y)
    (hyx : (weylCoxeterSystem P b).BruhatLE y x) :
    (∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
      C.head.1 = x ∧ C.last.1 = y ∧ IsAChain a lam C) ↔ a.den ∣ intervalBondGcd b lam x y := by
  refine ⟨fun ⟨C, hCh, hCl, hC⟩ ↦ ?_, fun h ↦ ?_⟩
  · rwa [isAChain_iff_den_dvd_intervalBondGcd hlam, hCh, hCl] at hC
  · obtain ⟨C, hCh, hCl⟩ := CoxeterSystem.exists_minimalCosetRepChain hy hx hyx
    refine ⟨C, by rw [hCh], by rw [hCl], ?_⟩
    rwa [isAChain_iff_den_dvd_intervalBondGcd hlam, hCh, hCl]

/-- **Every saturated chain is an `a`-chain as soon as one is.** For minimal coset representatives
`y ≤ x`, every saturated chain from `x` down to `y` is an `a`-chain exactly when the denominator of
`a` divides `d_λ(x, y)`. -/
theorem forall_isAChain_iff_den_dvd_intervalBondGcd (hlam : lam ∈ dominantChamber P b)
    {x y : P.weylGroup} (hx : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) x)
    (hy : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) y)
    (hyx : (weylCoxeterSystem P b).BruhatLE y x) :
    (∀ C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
      C.head.1 = x → C.last.1 = y → IsAChain a lam C) ↔ a.den ∣ intervalBondGcd b lam x y := by
  refine ⟨fun h ↦ ?_, fun h C hCh hCl ↦ ?_⟩
  · obtain ⟨C, hCh, hCl⟩ := CoxeterSystem.exists_minimalCosetRepChain hy hx hyx
    have hC := h C (by rw [hCh]) (by rw [hCl])
    rwa [isAChain_iff_den_dvd_intervalBondGcd hlam, hCh, hCl] at hC
  · rwa [isAChain_iff_den_dvd_intervalBondGcd hlam, hCh, hCl]

end TauCeti
