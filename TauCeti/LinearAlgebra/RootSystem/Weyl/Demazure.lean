/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Invariant
import TauCeti.Algebra.MonoidAlgebra.Eigenvector
import TauCeti.Algebra.MonoidAlgebra.Telescope

/-!
# The integral Demazure operator of a root

Let `P` be a root datum with weight lattice `M`, and write `e^x` for the basis element of the
integral group algebra `ℤ[M]` at a weight `x`. For a root `α = αᵢ` with coroot `α^∨`, the
**Demazure operator** `Dᵢ : ℤ[M] → ℤ[M]` is the `ℤ`-linear map sending `e^x`, where
`m = ⟨x, α^∨⟩`, to the signed `α`-string

* `e^x + e^{x - α} + ⋯ + e^{x - m α}` when `m ≥ 0`,
* `0` when `m = -1`,
* `-(e^{x + α} + e^{x + 2α} + ⋯ + e^{x + (-m - 1) α})` when `m ≤ -2`.

Geometrically, these strings are the torus characters of `H⁰ - H¹` of the degree-`m` line bundle
on the projective line `Pᵢ/B`, which is the role `Dᵢ` plays in computing Euler characteristics of
line bundles on Bott–Samelson and Schubert varieties; this file treats only the combinatorial
operator. Every case is the single **localization identity**

`(1 - e^{-α}) Dᵢ(f) = f - e^{-α} sᵢ(f)`,

where `sᵢ` acts on `ℤ[M]` by reindexing along the reflection of `M`; that is,
`Dᵢ(e^x) = (e^x - e^{-α} e^{sᵢ x}) / (1 - e^{-α})`.

Since `1 - e^{-α}` is not a zero divisor in `ℤ[M]`, the localization identity characterizes
`Dᵢ`, and the remaining results follow from it algebraically: the image of `Dᵢ` is fixed by `sᵢ`,
`Dᵢ` fixes exactly the `sᵢ`-invariant elements, so `Dᵢ² = Dᵢ`, and `Dᵢ` is linear over the
`sᵢ`-invariant elements. In particular `Dᵢ` fixes every Weyl-invariant element.

## Main definitions

* `RootPairing.demazureOperator`: the integral Demazure operator `Dᵢ` of the root `αᵢ`.

## Main results

* `RootPairing.demazureOperator_single_of_coroot'_eq_natCast`,
  `RootPairing.demazureOperator_single_of_coroot'_eq_neg_natCast_sub_one` and
  `RootPairing.demazureOperator_single_of_coroot'_eq_neg_one`: the root strings above.
* `RootPairing.one_sub_single_neg_root_mul_demazureOperator`: the localization identity, and
  `RootPairing.demazureOperator_eq_iff`: it characterizes `Dᵢ`.
* `RootPairing.demazureOperator_eq_self_iff`: `Dᵢ f = f` exactly when `sᵢ f = f`.
* `RootPairing.demazureOperator_demazureOperator`: `Dᵢ² = Dᵢ`.
* `RootPairing.demazureOperator_mul_of_reflection_eq`: `Dᵢ` is linear over `sᵢ`-invariants.
* `RootPairing.demazureOperator_eq_self_of_isWeylInvariant`: `Dᵢ` fixes Weyl-invariant elements.

## References

* M. Demazure, *Désingularisation des variétés de Schubert généralisées*, Ann. Sci. École
  Norm. Sup. (4) 7 (1974), §2.
* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Part II, §14.
* S. Kumar, *Kac–Moody Groups, their Flag Varieties and Representation Theory*, §8.1.
-/

public section

noncomputable section

namespace RootPairing

open AddMonoidAlgebra

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] (P : RootPairing ι ℤ M N) (i : ι)

/-- **The integral Demazure operator** `Dᵢ` of the root `αᵢ`: the `ℤ`-linear endomorphism of
`ℤ[M]` sending `e^x`, with `m = ⟨x, αᵢ^∨⟩`, to `e^x + e^{x - αᵢ} + ⋯ + e^{x - m αᵢ}` when
`m ≥ 0` and to `-(e^{x + αᵢ} + ⋯ + e^{x + (-m - 1) αᵢ})` when `m < 0`. At most one of the two
sums in the defining formula is nonempty. -/
def demazureOperator : AddMonoidAlgebra ℤ M →ₗ[ℤ] AddMonoidAlgebra ℤ M :=
  (AddMonoidAlgebra.basis M ℤ).constr ℤ fun x ↦
    ∑ j ∈ Finset.range (P.coroot' i x + 1).toNat, single (x - j • P.root i) 1 -
      ∑ j ∈ Finset.range (-P.coroot' i x - 1).toNat, single (x + (j + 1) • P.root i) 1

/-- The defining formula of `RootPairing.demazureOperator` on a basis element. -/
theorem demazureOperator_single (x : M) (c : ℤ) :
    P.demazureOperator i (single x c) =
      c • (∑ j ∈ Finset.range (P.coroot' i x + 1).toNat, single (x - j • P.root i) 1 -
        ∑ j ∈ Finset.range (-P.coroot' i x - 1).toNat, single (x + (j + 1) • P.root i) 1) := by
  have hc : single x c = c • single x (1 : ℤ) := by rw [smul_single', mul_one]
  rw [hc, map_smul, demazureOperator, ← AddMonoidAlgebra.basis_apply, Module.Basis.constr_basis]

/-- On a weight `x` with `⟨x, αᵢ^∨⟩ = n ≥ 0`, the Demazure operator is the root string
`e^x + e^{x - αᵢ} + ⋯ + e^{x - n αᵢ}` from `x` down to `sᵢ x`. -/
theorem demazureOperator_single_of_coroot'_eq_natCast {x : M} {n : ℕ}
    (h : P.coroot' i x = n) :
    P.demazureOperator i (single x 1) =
      ∑ j ∈ Finset.range (n + 1), single (x - j • P.root i) 1 := by
  have hneg : (-(n : ℤ) - 1).toNat = 0 := by omega
  have hpos : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [demazureOperator_single, h, one_smul, hneg, hpos, Finset.range_zero, Finset.sum_empty,
    sub_zero]

/-- On a weight `x` with `⟨x, αᵢ^∨⟩ = -n - 1 < 0`, the Demazure operator is the negative of the
root string `e^{x + αᵢ} + ⋯ + e^{x + n αᵢ}` strictly between `x` and `sᵢ x`. -/
theorem demazureOperator_single_of_coroot'_eq_neg_natCast_sub_one {x : M} {n : ℕ}
    (h : P.coroot' i x = -n - 1) :
    P.demazureOperator i (single x 1) =
      -∑ j ∈ Finset.range n, single (x + (j + 1) • P.root i) 1 := by
  have hpos : (-(n : ℤ) - 1 + 1).toNat = 0 := by omega
  have hneg : (-(-(n : ℤ) - 1) - 1).toNat = n := by omega
  rw [demazureOperator_single, h, one_smul, hpos, hneg, Finset.range_zero, Finset.sum_empty,
    zero_sub]

/-- On a weight `x` with `⟨x, αᵢ^∨⟩ = -1`, the Demazure operator vanishes. -/
@[simp]
theorem demazureOperator_single_of_coroot'_eq_neg_one {x : M} (h : P.coroot' i x = -1) :
    P.demazureOperator i (single x 1) = 0 := by
  rw [P.demazureOperator_single_of_coroot'_eq_neg_natCast_sub_one i (n := 0) (by simpa using h),
    Finset.range_zero, Finset.sum_empty, neg_zero]

/-- The Demazure operator fixes the unit `e^0`. -/
@[simp]
theorem demazureOperator_one : P.demazureOperator i 1 = 1 := by
  rw [AddMonoidAlgebra.one_def,
    P.demazureOperator_single_of_coroot'_eq_natCast i (n := 0) (by simp)]
  simp

/-! ### The localization identity -/

/-- The localization identity on a basis element. -/
private lemma one_sub_single_neg_root_mul_demazureOperator_single (x : M) :
    (1 - single (-P.root i) 1) * P.demazureOperator i (single x 1) =
      single x 1 - single (-P.root i) 1 * single (P.reflection i x) 1 := by
  rw [single_mul_single, mul_one, reflection_apply]
  obtain ⟨n, hn | hn⟩ : ∃ n : ℕ, P.coroot' i x = n ∨ P.coroot' i x = -n - 1 := by
    rcases le_or_gt 0 (P.coroot' i x) with h | h
    · exact ⟨(P.coroot' i x).toNat, .inl (by omega)⟩
    · exact ⟨(-P.coroot' i x - 1).toNat, .inr (by omega)⟩
  · have hx : -P.root i + (x - (n : ℤ) • P.root i) = x - (n + 1) • P.root i := by
      rw [natCast_zsmul, succ_nsmul]; abel
    rw [P.demazureOperator_single_of_coroot'_eq_natCast i hn,
      TauCeti.one_sub_single_neg_mul_sum_sub, hn, hx]
  · have hx : -P.root i + (x - (-(n : ℤ) - 1) • P.root i) = x + n • P.root i := by
      rw [sub_smul, neg_smul, natCast_zsmul, one_smul]; abel
    rw [P.demazureOperator_single_of_coroot'_eq_neg_natCast_sub_one i hn, mul_neg,
      TauCeti.one_sub_single_neg_mul_sum_add, neg_sub, hn, hx]

/-- **The localization identity** of the Demazure operator:
`(1 - e^{-αᵢ}) Dᵢ(f) = f - e^{-αᵢ} sᵢ(f)`, where `sᵢ` reindexes `ℤ[M]` along the reflection of
`M`. Equivalently, `Dᵢ(e^x) = (e^x - e^{-αᵢ} e^{sᵢ x}) / (1 - e^{-αᵢ})`. -/
theorem one_sub_single_neg_root_mul_demazureOperator (f : AddMonoidAlgebra ℤ M) :
    (1 - single (-P.root i) 1) * P.demazureOperator i f =
      f - single (-P.root i) 1 * mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, mul_add, hf, hg, map_add, mul_add]; abel
  | single x c =>
    have hc : single x c = c • single x (1 : ℤ) := by rw [smul_single', mul_one]
    rw [hc, map_smul, mul_smul_comm, one_sub_single_neg_root_mul_demazureOperator_single,
      map_zsmul, mul_smul_comm, smul_sub]
    simp

/-- Multiplication by `1 - e^{-αᵢ}` is injective on `ℤ[M]`, since `-αᵢ` has infinite order. -/
private lemma eq_of_one_sub_single_neg_root_mul_eq {f g : AddMonoidAlgebra ℤ M}
    (h : (1 - single (-P.root i) 1) * f = (1 - single (-P.root i) 1) * g) : f = g := by
  have hα : ¬IsOfFinAddOrder (-P.root i) := by
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    rintro ⟨n, hn, hnα⟩
    have := congrArg (P.coroot' i) hnα
    simp only [smul_neg, map_neg, map_nsmul, root_coroot'_eq_pairing, pairing_same, map_zero,
      nsmul_eq_mul, neg_eq_zero] at this
    omega
  rw [← sub_eq_zero]
  refine TauCeti.eq_zero_of_mul_single_eq_self_of_not_isOfFinAddOrder hα ?_
  linear_combination -h

/-- The localization identity characterizes the Demazure operator: `Dᵢ f` is the unique `g` with
`(1 - e^{-αᵢ}) g = f - e^{-αᵢ} sᵢ(f)`. -/
theorem demazureOperator_eq_iff {f g : AddMonoidAlgebra ℤ M} :
    P.demazureOperator i f = g ↔
      (1 - single (-P.root i) 1) * g =
        f - single (-P.root i) 1 * mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv f := by
  refine ⟨fun h ↦ h ▸ P.one_sub_single_neg_root_mul_demazureOperator i f, fun h ↦ ?_⟩
  exact P.eq_of_one_sub_single_neg_root_mul_eq i
    ((P.one_sub_single_neg_root_mul_demazureOperator i f).trans h.symm)

/-! ### Consequences of the localization identity -/

/-- The image of the Demazure operator is fixed by the reflection `sᵢ`. -/
@[simp]
theorem mapDomainRingEquiv_reflection_demazureOperator (f : AddMonoidAlgebra ℤ M) :
    mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv (P.demazureOperator i f) =
      P.demazureOperator i f := by
  have hs : mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv (single (-P.root i) 1) =
      single (P.root i) 1 := by
    simp
  have hss (g : AddMonoidAlgebra ℤ M) : mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv
      (mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv g) = g :=
    AddMonoidAlgebra.ext (Finsupp.ext fun x ↦ by simp [← LinearEquiv.coe_inv])
  have hα : single (-P.root i) (1 : ℤ) * single (P.root i) 1 = 1 := by
    rw [single_mul_single, neg_add_cancel, mul_one, one_def]
  -- Apply `sᵢ` to the localization identity, which exchanges `e^{-αᵢ}` and `e^{αᵢ}`, and
  -- multiply by `e^{-αᵢ}`.
  have key := congr(single (-P.root i) (1 : ℤ) * mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv
    $(P.one_sub_single_neg_root_mul_demazureOperator i f))
  simp only [map_mul, map_sub, map_one, hs, hss] at key
  refine ((P.demazureOperator_eq_iff i).mpr ?_).symm
  linear_combination -key -
    (mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv (P.demazureOperator i f) - f) * hα

/-- The Demazure operator fixes `f` exactly when `f` is fixed by the reflection `sᵢ`. -/
theorem demazureOperator_eq_self_iff {f : AddMonoidAlgebra ℤ M} :
    P.demazureOperator i f = f ↔ mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv f = f := by
  refine ⟨fun h ↦ h ▸ P.mapDomainRingEquiv_reflection_demazureOperator i f, fun h ↦ ?_⟩
  rw [demazureOperator_eq_iff, h, sub_mul, one_mul]

/-- **The Demazure operator is idempotent**, `Dᵢ² = Dᵢ`. -/
@[simp]
theorem demazureOperator_demazureOperator (f : AddMonoidAlgebra ℤ M) :
    P.demazureOperator i (P.demazureOperator i f) = P.demazureOperator i f :=
  (P.demazureOperator_eq_self_iff i).mpr (P.mapDomainRingEquiv_reflection_demazureOperator i f)

/-- The Demazure operator is linear over the elements fixed by the reflection `sᵢ`. -/
theorem demazureOperator_mul_of_reflection_eq {g : AddMonoidAlgebra ℤ M}
    (hg : mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv g = g) (f : AddMonoidAlgebra ℤ M) :
    P.demazureOperator i (g * f) = g * P.demazureOperator i f := by
  rw [demazureOperator_eq_iff, map_mul, hg, mul_left_comm,
    P.one_sub_single_neg_root_mul_demazureOperator i f]
  ring

/-- The Demazure operator fixes every Weyl-invariant element. -/
theorem demazureOperator_eq_self_of_isWeylInvariant {f : AddMonoidAlgebra ℤ M}
    (hf : TauCeti.IsWeylInvariant P f) : P.demazureOperator i f = f := by
  refine (P.demazureOperator_eq_self_iff i).mpr (AddMonoidAlgebra.ext (Finsupp.ext fun x ↦ ?_))
  simpa [← LinearEquiv.coe_inv] using hf.coeff_smul (weylGroup.ofIdx P i) x

end RootPairing
