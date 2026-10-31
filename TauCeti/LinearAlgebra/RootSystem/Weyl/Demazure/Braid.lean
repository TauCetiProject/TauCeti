/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Matsumoto
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Demazure.Basic

/-!
# Braid relations for the Demazure operators

Let `P` be a root datum with weight lattice `M`, and let `Dᵢ` be the integral Demazure operator
of the root `αᵢ` on `ℤ[M]` (`RootPairing.demazureOperator`). This file proves that the Demazure
operators of two roots satisfy the braid relation of the dihedral group they generate: for roots
`αᵢ`, `αⱼ` with Cartan entries `⟨αᵢ, αⱼ^∨⟩ = -1` and `⟨αⱼ, αᵢ^∨⟩ = -k` (`k = 1, 2, 3`), the two
alternating products of `Dᵢ` and `Dⱼ` of length `3`, `4`, `6` agree, and orthogonal roots give
commuting operators. For the simple roots of a base these are exactly the braid relations of the
Coxeter matrix of the base, so by Matsumoto's theorem the product `D_{i₁} ⋯ D_{iᵣ}` along a
reduced word depends only on the Weyl group element `s_{i₁} ⋯ s_{iᵣ}`. This word independence
is what makes `D_w = D_{i₁} ⋯ D_{iᵣ}` a well-defined operator for each Weyl group element `w`, the
operator in the Demazure character formula `char H⁰(X(w), L_λ) = D_w(e^λ)`.

## Method

Write `a = e^{-αᵢ}`, `b = e^{-αⱼ}` and `sᵢ`, `sⱼ` for the reindexing of `ℤ[M]` along the two
reflections. Let `w₀` be the longest element of the rank-two Weyl group `⟨sᵢ, sⱼ⟩` and `Δ` the
product of the factors `1 - e^{-β}` over its positive roots `β` (those of the rank-two subsystem
with simple roots `αᵢ`, `αⱼ`). For either reduced word of `w₀` the operator `D_{w₀}` satisfies
Demazure's formula

`Δ · D_{w₀}(f) = ∑_{w ∈ ⟨sᵢ, sⱼ⟩} (-1)^{ℓ(w)} e^{w ρ - ρ} w(f)`,

where `ρ` is the half sum of those positive roots; only the differences `w ρ - ρ`, which lie in
the root lattice, occur. The right-hand side does not depend on the word. Each instance is
derived from the localization identity `(1 - e^{-αₖ}) Dₖ(g) = g - e^{-αₖ} sₖ(g)` of
`TauCeti.LinearAlgebra.RootSystem.Weyl.Demazure.Basic`, transported by the reflections already
applied, and from the invariance `sₖ(Dₖ g) = Dₖ g`: peeling off the operators from the outside
in, the coefficient of each term `w(Dₖ g)` is divisible by `1 - e^{-w αₖ}` with `w αₖ` positive,
and the resulting `linear_combination` certificate is checked by `ring`. Since multiplication by
`1 - e^{-β}` is injective (`RootPairing.isLeftRegular_one_sub_single_neg_root`), the two words
give the same operator. No rank-two root system needs to be classified: the computation only uses
the two Cartan entries.

## Main results

* `RootPairing.commute_demazureOperator_of_isOrthogonal`: the Demazure operators of orthogonal
  roots commute.
* `RootPairing.demazureOperator_braid_three`, `RootPairing.demazureOperator_braid_four` and
  `RootPairing.demazureOperator_braid_six`: the braid relations of types `A₂`, `B₂` and `G₂`.
* `RootPairing.prod_map_demazureOperator_braidWord`: the braid relations of the Coxeter matrix of
  a base.
* `RootPairing.prod_map_demazureOperator_eq_of_wordProd_eq`: **word independence**, the product
  of the Demazure operators along a reduced word depends only on the Weyl group element it spells.

## References

* M. Demazure, *Désingularisation des variétés de Schubert généralisées*, Ann. Sci. École
  Norm. Sup. (4) 7 (1974).
* S. Kumar, *Kac–Moody Groups, their Flag Varieties and Representation Theory*, Progress in
  Mathematics 204, Birkhäuser (2002), Chapter 8.
* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Part II, Chapter 14.

Matsumoto's theorem is `TauCeti.matsumoto`.
-/

public section

noncomputable section

namespace RootPairing

open AddMonoidAlgebra CoxeterSystem

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] (P : RootPairing ι ℤ M N) {i j : ι}

/-! ### The localization identity transported by a ring automorphism -/

/-- The localization identity `(1 - e^{-αₖ}) Dₖ(X) = X - e^{-αₖ} sₖ(X)`, transported by a ring
automorphism `σ` of `ℤ[M]` (in practice, the reindexing along a Weyl group element `w`, which
sends `e^{-αₖ}` to `c = e^{-w αₖ}`). -/
private lemma one_sub_mul_map_demazureOperator (σ : AddMonoidAlgebra ℤ M ≃+* AddMonoidAlgebra ℤ M)
    {k : ι} {S : AddMonoidAlgebra ℤ M ≃+* AddMonoidAlgebra ℤ M}
    (hS : mapDomainRingEquiv ℤ (P.reflection k).toAddEquiv = S) (X : AddMonoidAlgebra ℤ M)
    {c : AddMonoidAlgebra ℤ M} (hc : σ (single (-P.root k) 1) = c) :
    (1 - c) * σ (P.demazureOperator k X) = σ X - c * σ (S X) := by
  have := congr(σ $(P.one_sub_single_neg_root_mul_demazureOperator k X))
  simpa [hc, hS] using this

/-- Multiplication by `1 - c` is injective when `c` is the image of `e^{-αₖ}` under a ring
automorphism of `ℤ[M]`. -/
private lemma isLeftRegular_one_sub_map (σ : AddMonoidAlgebra ℤ M ≃+* AddMonoidAlgebra ℤ M)
    (k : ι) {c : AddMonoidAlgebra ℤ M} (hc : σ (single (-P.root k) 1) = c) :
    IsLeftRegular (1 - c) := by
  intro X Y h
  have h' := congr(σ.symm $h)
  simp only [map_mul, map_sub, map_one, ← hc, RingEquiv.symm_apply_apply] at h'
  exact σ.symm.injective (P.isLeftRegular_one_sub_single_neg_root k h')

/-- The reindexings `sᵢ`, `sⱼ` of `ℤ[M]` satisfy the braid relation of length `2`: orthogonal
reflections commute (`RootPairing.isOrthogonal_comm`). -/
private lemma map_braid_A1A1 (hij : P.pairing i j = 0) (hji : P.pairing j i = 0)
    {S T : AddMonoidAlgebra ℤ M ≃+* AddMonoidAlgebra ℤ M}
    (hS : mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv = S)
    (hT : mapDomainRingEquiv ℤ (P.reflection j).toAddEquiv = T) (f : AddMonoidAlgebra ℤ M) :
    S (T f) = T (S f) := by
  have g := (P.isOrthogonal_comm i j ⟨hij, hji⟩).eq
  subst hS hT
  simp only [← RingEquiv.trans_apply, ← mapDomainRingEquiv_trans]
  congr 2
  ext x
  simpa using congr($g x)

/-- The reindexings `sᵢ`, `sⱼ` of `ℤ[M]` satisfy the braid relation of length `3`, transported from
the Weyl group (`RootPairing.weylGroup.pow_three_ofIdx_mul_ofIdx_eq_one`). -/
private lemma map_braid_A2 (hij : P.pairing i j = -1) (hji : P.pairing j i = -1)
    {S T : AddMonoidAlgebra ℤ M ≃+* AddMonoidAlgebra ℤ M}
    (hS : mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv = S)
    (hT : mapDomainRingEquiv ℤ (P.reflection j).toAddEquiv = T) (f : AddMonoidAlgebra ℤ M) :
    S (T (S f)) = T (S (T f)) := by
  have g : weylGroup.ofIdx P i * weylGroup.ofIdx P j * weylGroup.ofIdx P i =
      weylGroup.ofIdx P j * weylGroup.ofIdx P i * weylGroup.ofIdx P j := by
    rw [← mul_inv_eq_one]
    simpa [mul_assoc, pow_succ] using
      weylGroup.pow_three_ofIdx_mul_ofIdx_eq_one P i j (by rw [hij, hji]; norm_num)
  subst hS hT
  simp only [← RingEquiv.trans_apply, ← mapDomainRingEquiv_trans]
  congr 2
  ext x
  simpa [mul_smul] using congr($g • x)

/-- The reindexings `sᵢ`, `sⱼ` of `ℤ[M]` satisfy the braid relation of length `4`, transported from
the Weyl group (`RootPairing.weylGroup.pow_four_ofIdx_mul_ofIdx_eq_one`). -/
private lemma map_braid_B2 (hij : P.pairing i j = -1) (hji : P.pairing j i = -2)
    {S T : AddMonoidAlgebra ℤ M ≃+* AddMonoidAlgebra ℤ M}
    (hS : mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv = S)
    (hT : mapDomainRingEquiv ℤ (P.reflection j).toAddEquiv = T) (f : AddMonoidAlgebra ℤ M) :
    S (T (S (T f))) = T (S (T (S f))) := by
  have g : weylGroup.ofIdx P i * weylGroup.ofIdx P j * weylGroup.ofIdx P i *
      weylGroup.ofIdx P j = weylGroup.ofIdx P j * weylGroup.ofIdx P i * weylGroup.ofIdx P j *
      weylGroup.ofIdx P i := by
    rw [← mul_inv_eq_one]
    simpa [mul_assoc, pow_succ] using
      weylGroup.pow_four_ofIdx_mul_ofIdx_eq_one P i j (by rw [hij, hji]; norm_num)
  subst hS hT
  simp only [← RingEquiv.trans_apply, ← mapDomainRingEquiv_trans]
  congr 2
  ext x
  simpa [mul_smul] using congr($g • x)

/-- The reindexings `sᵢ`, `sⱼ` of `ℤ[M]` satisfy the braid relation of length `6`, transported from
the Weyl group (`RootPairing.weylGroup.pow_six_ofIdx_mul_ofIdx_eq_one`). -/
private lemma map_braid_G2 (hij : P.pairing i j = -1) (hji : P.pairing j i = -3)
    {S T : AddMonoidAlgebra ℤ M ≃+* AddMonoidAlgebra ℤ M}
    (hS : mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv = S)
    (hT : mapDomainRingEquiv ℤ (P.reflection j).toAddEquiv = T) (f : AddMonoidAlgebra ℤ M) :
    S (T (S (T (S (T f))))) = T (S (T (S (T (S f))))) := by
  have g : weylGroup.ofIdx P i * weylGroup.ofIdx P j * weylGroup.ofIdx P i *
      weylGroup.ofIdx P j * weylGroup.ofIdx P i * weylGroup.ofIdx P j =
      weylGroup.ofIdx P j * weylGroup.ofIdx P i * weylGroup.ofIdx P j * weylGroup.ofIdx P i *
      weylGroup.ofIdx P j * weylGroup.ofIdx P i := by
    rw [← mul_inv_eq_one]
    simpa [mul_assoc, pow_succ] using
      weylGroup.pow_six_ofIdx_mul_ofIdx_eq_one P i j (by rw [hij, hji]; norm_num)
  subst hS hT
  simp only [← RingEquiv.trans_apply, ← mapDomainRingEquiv_trans]
  congr 2
  ext x
  simpa [mul_smul] using congr($g • x)

/-! ### Demazure's formula for the longest element of a rank-two subsystem

Each lemma below proves `Δ · D_{w₀}(f) = ∑ (-1)^{ℓ(w)} e^{w ρ - ρ} w(f)` for one reduced word of
`w₀`, with `a = e^{-αᵢ}`, `b = e^{-αⱼ}`, `S = sᵢ`, `T = sⱼ`. Writing the word as
`D_{k₁}(D_{k₂}(⋯ D_{k_m}(f)))`, the hypothesis `hₙ` is the localization identity of one operator
`D_{k_l}`, transported by the product `w` of reflections that multiplies it after the outer
operators have been expanded:
`(1 - e^{-w α_{k_l}}) w(D_{k_l} g) = w(g) - e^{-w α_{k_l}} w(s_{k_l} g)`.
The `linear_combination` coefficient of `hₙ` is the coefficient of `w(D_{k_l} g)` at that stage
divided by `1 - e^{-w α_{k_l}}`; the `simp only [iS, iT]` step uses `sₖ(Dₖ g) = Dₖ g` to merge the
terms `w sₖ(Dₖ g)` and `w(Dₖ g)`. -/

/-- The expansion of `Dᵢ Dⱼ` in type `A₁ × A₁`, cleared of the denominators
`1 - e^{-β}` for the positive roots `β` of the rank-two subsystem. -/
private lemma mul_demazureOperator_ij_A1A1 (hji : P.pairing j i = 0) {a b : AddMonoidAlgebra ℤ M}
    (ha : single (-P.root i) 1 = a) (hb : single (-P.root j) 1 = b)
    {S T : AddMonoidAlgebra ℤ M ≃+* AddMonoidAlgebra ℤ M}
    (hS : mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv = S)
    (hT : mapDomainRingEquiv ℤ (P.reflection j).toAddEquiv = T) (f : AddMonoidAlgebra ℤ M) :
    (1 - b) * (1 - a) * P.demazureOperator i (P.demazureOperator j f) =
      f - a * S f - b * T f + a * b * S (T f) := by
  have iS (Y) : S (P.demazureOperator i Y) = P.demazureOperator i Y :=
    hS ▸ P.mapDomainRingEquiv_reflection_demazureOperator i Y
  have iT (Y) : T (P.demazureOperator j Y) = P.demazureOperator j Y :=
    hT ▸ P.mapDomainRingEquiv_reflection_demazureOperator j Y
  have h1 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hS
      (P.demazureOperator j f) (c := a)
    (by subst ha hb hS hT; simp)
  have h2 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hT f (c := b)
    (by subst ha hb hS hT; simp)
  have h3 := P.one_sub_mul_map_demazureOperator S hT f (c := b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hji])
  simp only [RingEquiv.refl_apply, iS, iT] at *
  linear_combination (1 - b) * h1 + h2 + (-a) * h3

/-- The expansion of `Dⱼ Dᵢ` in type `A₁ × A₁`, cleared of the denominators
`1 - e^{-β}` for the positive roots `β` of the rank-two subsystem: the expansion of `Dᵢ Dⱼ` with
the two roots exchanged. -/
private lemma mul_demazureOperator_ji_A1A1 (hij : P.pairing i j = 0) {a b : AddMonoidAlgebra ℤ M}
    (ha : single (-P.root i) 1 = a) (hb : single (-P.root j) 1 = b)
    {S T : AddMonoidAlgebra ℤ M ≃+* AddMonoidAlgebra ℤ M}
    (hS : mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv = S)
    (hT : mapDomainRingEquiv ℤ (P.reflection j).toAddEquiv = T) (f : AddMonoidAlgebra ℤ M) :
    (1 - b) * (1 - a) * P.demazureOperator j (P.demazureOperator i f) =
      f - a * S f - b * T f + a * b * T (S f) := by
  linear_combination P.mul_demazureOperator_ij_A1A1 (i := j) (j := i) hij hb ha hT hS f

/-- The expansion of `Dᵢ Dⱼ Dᵢ` in type `A₂`, cleared of the denominators
`1 - e^{-β}` for the positive roots `β` of the rank-two subsystem. -/
private lemma mul_demazureOperator_ij_A2 (hij : P.pairing i j = -1) (hji : P.pairing j i = -1)
    {a b : AddMonoidAlgebra ℤ M} (ha : single (-P.root i) 1 = a)
    (hb : single (-P.root j) 1 = b) {S T : AddMonoidAlgebra ℤ M ≃+* AddMonoidAlgebra ℤ M}
    (hS : mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv = S)
    (hT : mapDomainRingEquiv ℤ (P.reflection j).toAddEquiv = T) (f : AddMonoidAlgebra ℤ M) :
    (1 - b) * (1 - a) * (1 - a * b) * P.demazureOperator i (P.demazureOperator j
      (P.demazureOperator i f)) =
      f - a * S f - b * T f + a ^ 2 * b * S (T f) + a * b ^ 2 * T (S f)
        - a ^ 2 * b ^ 2 * S (T (S f)) := by
  have iS (Y) : S (P.demazureOperator i Y) = P.demazureOperator i Y :=
    hS ▸ P.mapDomainRingEquiv_reflection_demazureOperator i Y
  have iT (Y) : T (P.demazureOperator j Y) = P.demazureOperator j Y :=
    hT ▸ P.mapDomainRingEquiv_reflection_demazureOperator j Y
  have h1 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hS (P.demazureOperator j
      (P.demazureOperator i f)) (c := a)
    (by subst ha hb hS hT; simp)
  have h2 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hT
      (P.demazureOperator i f) (c := b)
    (by subst ha hb hS hT; simp)
  have h3 := P.one_sub_mul_map_demazureOperator S hT (P.demazureOperator i f) (c := a * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hji])
  have h4 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hS f (c := a)
    (by subst ha hb hS hT; simp)
  have h5 := P.one_sub_mul_map_demazureOperator T hS f (c := a * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij]; congr 1; module)
  have h6 := P.one_sub_mul_map_demazureOperator (T.trans S) hS f (c := b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji])
  simp only [RingEquiv.refl_apply, RingEquiv.trans_apply, iS, iT] at *
  linear_combination ((1 - b) * (1 - a * b)) * h1 + (1 - a * b) * h2 + (-a * (1 - b)) * h3 + h4 +
    (-b) * h5 + (a ^ 2 * b) * h6

/-- The expansion of `Dⱼ Dᵢ Dⱼ` in type `A₂`, cleared of the denominators
`1 - e^{-β}` for the positive roots `β` of the rank-two subsystem: the expansion of `Dᵢ Dⱼ Dᵢ` with
the two roots exchanged. -/
private lemma mul_demazureOperator_ji_A2 (hij : P.pairing i j = -1) (hji : P.pairing j i = -1)
    {a b : AddMonoidAlgebra ℤ M} (ha : single (-P.root i) 1 = a)
    (hb : single (-P.root j) 1 = b) {S T : AddMonoidAlgebra ℤ M ≃+* AddMonoidAlgebra ℤ M}
    (hS : mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv = S)
    (hT : mapDomainRingEquiv ℤ (P.reflection j).toAddEquiv = T) (f : AddMonoidAlgebra ℤ M) :
    (1 - b) * (1 - a) * (1 - a * b) * P.demazureOperator j (P.demazureOperator i
      (P.demazureOperator j f)) =
      f - a * S f - b * T f + a ^ 2 * b * S (T f) + a * b ^ 2 * T (S f)
        - a ^ 2 * b ^ 2 * T (S (T f)) := by
  linear_combination P.mul_demazureOperator_ij_A2 (i := j) (j := i) hji hij hb ha hT hS f

/-- The expansion of `Dᵢ Dⱼ Dᵢ Dⱼ` in type `B₂`, cleared of the denominators
`1 - e^{-β}` for the positive roots `β` of the rank-two subsystem. -/
private lemma mul_demazureOperator_ij_B2 (hij : P.pairing i j = -1) (hji : P.pairing j i = -2)
    {a b : AddMonoidAlgebra ℤ M} (ha : single (-P.root i) 1 = a)
    (hb : single (-P.root j) 1 = b) {S T : AddMonoidAlgebra ℤ M ≃+* AddMonoidAlgebra ℤ M}
    (hS : mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv = S)
    (hT : mapDomainRingEquiv ℤ (P.reflection j).toAddEquiv = T) (f : AddMonoidAlgebra ℤ M) :
    (1 - b) * (1 - a) * (1 - a * b) * (1 - a ^ 2 * b) * P.demazureOperator i (P.demazureOperator j
      (P.demazureOperator i (P.demazureOperator j f))) =
      f - a * S f - b * T f + a ^ 3 * b * S (T f) + a * b ^ 2 * T (S f)
        - a ^ 4 * b ^ 2 * S (T (S f)) - a ^ 3 * b ^ 3 * T (S (T f))
        + a ^ 4 * b ^ 3 * S (T (S (T f))) := by
  have iS (Y) : S (P.demazureOperator i Y) = P.demazureOperator i Y :=
    hS ▸ P.mapDomainRingEquiv_reflection_demazureOperator i Y
  have iT (Y) : T (P.demazureOperator j Y) = P.demazureOperator j Y :=
    hT ▸ P.mapDomainRingEquiv_reflection_demazureOperator j Y
  have h1 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hS (P.demazureOperator j
      (P.demazureOperator i (P.demazureOperator j f))) (c := a)
    (by subst ha hb hS hT; simp)
  have h2 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hT (P.demazureOperator i
      (P.demazureOperator j f)) (c := b)
    (by subst ha hb hS hT; simp)
  have h3 := P.one_sub_mul_map_demazureOperator S hT (P.demazureOperator i
      (P.demazureOperator j f)) (c := a ^ 2 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hji]; congr 1; module)
  have h4 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hS
      (P.demazureOperator j f) (c := a)
    (by subst ha hb hS hT; simp)
  have h5 := P.one_sub_mul_map_demazureOperator T hS (P.demazureOperator j f) (c := a * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij]; congr 1; module)
  have h6 := P.one_sub_mul_map_demazureOperator (T.trans S) hS (P.demazureOperator j f) (c := a * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h7 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hT f (c := b)
    (by subst ha hb hS hT; simp)
  have h8 := P.one_sub_mul_map_demazureOperator S hT f (c := a ^ 2 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hji]; congr 1; module)
  have h9 := P.one_sub_mul_map_demazureOperator (S.trans T) hT f (c := a ^ 2 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h10 := P.one_sub_mul_map_demazureOperator ((S.trans T).trans S) hT f (c := b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  simp only [RingEquiv.refl_apply, RingEquiv.trans_apply, iS, iT] at *
  linear_combination ((1 - b) * (1 - a * b) * (1 - a ^ 2 * b)) * h1 +
    ((1 - a * b) * (1 - a ^ 2 * b)) * h2 + (-a * (1 - b) * (1 - a * b)) * h3 +
    ((1 + a * b) * (1 - a * b)) * h4 + (-b * (1 - a ^ 2 * b)) * h5 + (a ^ 3 * b * (1 - b)) * h6 +
    h7 + (-a) * h8 + (a * b ^ 2) * h9 + (-a ^ 4 * b ^ 2) * h10

/-- The expansion of `Dⱼ Dᵢ Dⱼ Dᵢ` in type `B₂`, cleared of the denominators
`1 - e^{-β}` for the positive roots `β` of the rank-two subsystem. -/
private lemma mul_demazureOperator_ji_B2 (hij : P.pairing i j = -1) (hji : P.pairing j i = -2)
    {a b : AddMonoidAlgebra ℤ M} (ha : single (-P.root i) 1 = a)
    (hb : single (-P.root j) 1 = b) {S T : AddMonoidAlgebra ℤ M ≃+* AddMonoidAlgebra ℤ M}
    (hS : mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv = S)
    (hT : mapDomainRingEquiv ℤ (P.reflection j).toAddEquiv = T) (f : AddMonoidAlgebra ℤ M) :
    (1 - b) * (1 - a) * (1 - a * b) * (1 - a ^ 2 * b) * P.demazureOperator j (P.demazureOperator i
      (P.demazureOperator j (P.demazureOperator i f))) =
      f - a * S f - b * T f + a ^ 3 * b * S (T f) + a * b ^ 2 * T (S f)
        - a ^ 4 * b ^ 2 * S (T (S f)) - a ^ 3 * b ^ 3 * T (S (T f))
        + a ^ 4 * b ^ 3 * T (S (T (S f))) := by
  have iS (Y) : S (P.demazureOperator i Y) = P.demazureOperator i Y :=
    hS ▸ P.mapDomainRingEquiv_reflection_demazureOperator i Y
  have iT (Y) : T (P.demazureOperator j Y) = P.demazureOperator j Y :=
    hT ▸ P.mapDomainRingEquiv_reflection_demazureOperator j Y
  have h1 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hT (P.demazureOperator i
      (P.demazureOperator j (P.demazureOperator i f))) (c := b)
    (by subst ha hb hS hT; simp)
  have h2 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hS (P.demazureOperator j
      (P.demazureOperator i f)) (c := a)
    (by subst ha hb hS hT; simp)
  have h3 := P.one_sub_mul_map_demazureOperator T hS (P.demazureOperator j
      (P.demazureOperator i f)) (c := a * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij]; congr 1; module)
  have h4 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hT
      (P.demazureOperator i f) (c := b)
    (by subst ha hb hS hT; simp)
  have h5 := P.one_sub_mul_map_demazureOperator S hT (P.demazureOperator i f) (c := a ^ 2 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hji]; congr 1; module)
  have h6 := P.one_sub_mul_map_demazureOperator (S.trans T) hT
      (P.demazureOperator i f) (c := a ^ 2 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h7 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hS f (c := a)
    (by subst ha hb hS hT; simp)
  have h8 := P.one_sub_mul_map_demazureOperator T hS f (c := a * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij]; congr 1; module)
  have h9 := P.one_sub_mul_map_demazureOperator (T.trans S) hS f (c := a * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h10 := P.one_sub_mul_map_demazureOperator ((T.trans S).trans T) hS f (c := a)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  simp only [RingEquiv.refl_apply, RingEquiv.trans_apply, iS, iT] at *
  linear_combination ((1 - a) * (1 - a * b) * (1 - a ^ 2 * b)) * h1 +
    ((1 - a * b) * (1 - a ^ 2 * b)) * h2 + (-b * (1 - a) * (1 - a ^ 2 * b)) * h3 +
    (1 - a ^ 2 * b) * h4 + (-a * (1 - a * b)) * h5 + (a * b ^ 2 * (1 - a)) * h6 + h7 + (-b) * h8 +
    (a ^ 3 * b) * h9 + (-a ^ 3 * b ^ 3) * h10

/-- The expansion of `Dᵢ Dⱼ Dᵢ Dⱼ Dᵢ Dⱼ` in type `G₂`, cleared of the denominators
`1 - e^{-β}` for the positive roots `β` of the rank-two subsystem. -/
private lemma mul_demazureOperator_ij_G2 (hij : P.pairing i j = -1) (hji : P.pairing j i = -3)
    {a b : AddMonoidAlgebra ℤ M} (ha : single (-P.root i) 1 = a)
    (hb : single (-P.root j) 1 = b) {S T : AddMonoidAlgebra ℤ M ≃+* AddMonoidAlgebra ℤ M}
    (hS : mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv = S)
    (hT : mapDomainRingEquiv ℤ (P.reflection j).toAddEquiv = T) (f : AddMonoidAlgebra ℤ M) :
    (1 - b) * (1 - a) * (1 - a * b) * (1 - a ^ 2 * b) * (1 - a ^ 3 * b) * (1 - a ^ 3 * b ^ 2) *
      P.demazureOperator i (P.demazureOperator j (P.demazureOperator i (P.demazureOperator j
      (P.demazureOperator i (P.demazureOperator j f))))) =
      f - a * S f - b * T f + a ^ 4 * b * S (T f) + a * b ^ 2 * T (S f)
        - a ^ 6 * b ^ 2 * S (T (S f)) - a ^ 4 * b ^ 4 * T (S (T f))
        + a ^ 9 * b ^ 4 * S (T (S (T f))) + a ^ 6 * b ^ 5 * T (S (T (S f)))
        - a ^ 10 * b ^ 5 * S (T (S (T (S f)))) - a ^ 9 * b ^ 6 * T (S (T (S (T f))))
        + a ^ 10 * b ^ 6 * S (T (S (T (S (T f))))) := by
  have iS (Y) : S (P.demazureOperator i Y) = P.demazureOperator i Y :=
    hS ▸ P.mapDomainRingEquiv_reflection_demazureOperator i Y
  have iT (Y) : T (P.demazureOperator j Y) = P.demazureOperator j Y :=
    hT ▸ P.mapDomainRingEquiv_reflection_demazureOperator j Y
  have h1 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hS (P.demazureOperator j
      (P.demazureOperator i (P.demazureOperator j (P.demazureOperator i
      (P.demazureOperator j f))))) (c := a)
    (by subst ha hb hS hT; simp)
  have h2 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hT (P.demazureOperator i
      (P.demazureOperator j (P.demazureOperator i (P.demazureOperator j f)))) (c := b)
    (by subst ha hb hS hT; simp)
  have h3 := P.one_sub_mul_map_demazureOperator S hT (P.demazureOperator i (P.demazureOperator j
      (P.demazureOperator i (P.demazureOperator j f)))) (c := a ^ 3 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hji]; congr 1; module)
  have h4 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hS (P.demazureOperator j
      (P.demazureOperator i (P.demazureOperator j f))) (c := a)
    (by subst ha hb hS hT; simp)
  have h5 := P.one_sub_mul_map_demazureOperator T hS (P.demazureOperator j (P.demazureOperator i
      (P.demazureOperator j f))) (c := a * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij]; congr 1; module)
  have h6 := P.one_sub_mul_map_demazureOperator (T.trans S) hS (P.demazureOperator j
      (P.demazureOperator i (P.demazureOperator j f))) (c := a ^ 2 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h7 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hT (P.demazureOperator i
      (P.demazureOperator j f)) (c := b)
    (by subst ha hb hS hT; simp)
  have h8 := P.one_sub_mul_map_demazureOperator S hT (P.demazureOperator i
      (P.demazureOperator j f)) (c := a ^ 3 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hji]; congr 1; module)
  have h9 := P.one_sub_mul_map_demazureOperator (S.trans T) hT (P.demazureOperator i
      (P.demazureOperator j f)) (c := a ^ 3 * b ^ 2)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h10 := P.one_sub_mul_map_demazureOperator ((S.trans T).trans S) hT (P.demazureOperator i
      (P.demazureOperator j f)) (c := a ^ 3 * b ^ 2)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h11 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hS
      (P.demazureOperator j f) (c := a)
    (by subst ha hb hS hT; simp)
  have h12 := P.one_sub_mul_map_demazureOperator T hS (P.demazureOperator j f) (c := a * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij]; congr 1; module)
  have h13 := P.one_sub_mul_map_demazureOperator (T.trans S) hS
      (P.demazureOperator j f) (c := a ^ 2 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h14 := P.one_sub_mul_map_demazureOperator ((T.trans S).trans T) hS
      (P.demazureOperator j f) (c := a ^ 2 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h15 := P.one_sub_mul_map_demazureOperator (((T.trans S).trans T).trans S) hS
      (P.demazureOperator j f) (c := a * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h16 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hT f (c := b)
    (by subst ha hb hS hT; simp)
  have h17 := P.one_sub_mul_map_demazureOperator S hT f (c := a ^ 3 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hji]; congr 1; module)
  have h18 := P.one_sub_mul_map_demazureOperator (S.trans T) hT f (c := a ^ 3 * b ^ 2)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h19 := P.one_sub_mul_map_demazureOperator ((S.trans T).trans S) hT f (c := a ^ 3 * b ^ 2)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h20 := P.one_sub_mul_map_demazureOperator (((S.trans T).trans S).trans T) hT
      f (c := a ^ 3 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h21 := P.one_sub_mul_map_demazureOperator ((((S.trans T).trans S).trans T).trans S) hT
      f (c := b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  simp only [RingEquiv.refl_apply, RingEquiv.trans_apply, iS, iT] at *
  linear_combination
    ((1 - b) * (1 - a * b) * (1 - a ^ 2 * b) * (1 - a ^ 3 * b) * (1 - a ^ 3 * b ^ 2)) * h1 +
    ((1 - a * b) * (1 - a ^ 2 * b) * (1 - a ^ 3 * b) * (1 - a ^ 3 * b ^ 2)) * h2 +
    (-a * (1 - b) * (1 - a * b) * (1 - a ^ 2 * b) * (1 - a ^ 3 * b ^ 2)) * h3 +
    ((1 + a * b + a ^ 2 * b) * (1 - a * b) * (1 - a ^ 2 * b) * (1 - a ^ 3 * b ^ 2)) * h4 +
    (-b * (1 - a ^ 2 * b) * (1 - a ^ 3 * b) * (1 - a ^ 3 * b ^ 2)) * h5 +
    (a ^ 4 * b * (1 - b) * (1 - a * b) * (1 - a ^ 3 * b ^ 2)) * h6 +
    ((1 + a ^ 2 * b) * (1 - a ^ 2 * b) * (1 - a ^ 3 * b ^ 2)) * h7 +
    ((-a - a ^ 2 * b) * (1 - a * b) * (1 - a ^ 3 * b ^ 2)) * h8 +
    (a * b ^ 2 * (1 - a ^ 2 * b) * (1 - a ^ 3 * b)) * h9 +
    (-a ^ 6 * b ^ 2 * (1 - b) * (1 - a * b)) * h10 +
    ((1 + a ^ 3 * b ^ 2) * (1 - a ^ 3 * b ^ 2)) * h11 +
    ((-b - a ^ 2 * b ^ 2 - a ^ 4 * b ^ 3) * (1 - a ^ 2 * b)) * h12 +
    ((a ^ 4 * b + a ^ 5 * b ^ 2 + a ^ 6 * b ^ 3) * (1 - a * b)) * h13 +
    (-a ^ 4 * b ^ 4 * (1 - a ^ 3 * b)) * h14 + (a ^ 9 * b ^ 4 * (1 - b)) * h15 + h16 + (-a) * h17 +
    (a * b ^ 2) * h18 + (-a ^ 6 * b ^ 2) * h19 + (a ^ 6 * b ^ 5) * h20 + (-a ^ 10 * b ^ 5) * h21

/-- The expansion of `Dⱼ Dᵢ Dⱼ Dᵢ Dⱼ Dᵢ` in type `G₂`, cleared of the denominators
`1 - e^{-β}` for the positive roots `β` of the rank-two subsystem. -/
private lemma mul_demazureOperator_ji_G2 (hij : P.pairing i j = -1) (hji : P.pairing j i = -3)
    {a b : AddMonoidAlgebra ℤ M} (ha : single (-P.root i) 1 = a)
    (hb : single (-P.root j) 1 = b) {S T : AddMonoidAlgebra ℤ M ≃+* AddMonoidAlgebra ℤ M}
    (hS : mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv = S)
    (hT : mapDomainRingEquiv ℤ (P.reflection j).toAddEquiv = T) (f : AddMonoidAlgebra ℤ M) :
    (1 - b) * (1 - a) * (1 - a * b) * (1 - a ^ 2 * b) * (1 - a ^ 3 * b) * (1 - a ^ 3 * b ^ 2) *
      P.demazureOperator j (P.demazureOperator i (P.demazureOperator j (P.demazureOperator i
      (P.demazureOperator j (P.demazureOperator i f))))) =
      f - a * S f - b * T f + a ^ 4 * b * S (T f) + a * b ^ 2 * T (S f)
        - a ^ 6 * b ^ 2 * S (T (S f)) - a ^ 4 * b ^ 4 * T (S (T f))
        + a ^ 9 * b ^ 4 * S (T (S (T f))) + a ^ 6 * b ^ 5 * T (S (T (S f)))
        - a ^ 10 * b ^ 5 * S (T (S (T (S f)))) - a ^ 9 * b ^ 6 * T (S (T (S (T f))))
        + a ^ 10 * b ^ 6 * T (S (T (S (T (S f))))) := by
  have iS (Y) : S (P.demazureOperator i Y) = P.demazureOperator i Y :=
    hS ▸ P.mapDomainRingEquiv_reflection_demazureOperator i Y
  have iT (Y) : T (P.demazureOperator j Y) = P.demazureOperator j Y :=
    hT ▸ P.mapDomainRingEquiv_reflection_demazureOperator j Y
  have h1 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hT (P.demazureOperator i
      (P.demazureOperator j (P.demazureOperator i (P.demazureOperator j
      (P.demazureOperator i f))))) (c := b)
    (by subst ha hb hS hT; simp)
  have h2 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hS (P.demazureOperator j
      (P.demazureOperator i (P.demazureOperator j (P.demazureOperator i f)))) (c := a)
    (by subst ha hb hS hT; simp)
  have h3 := P.one_sub_mul_map_demazureOperator T hS (P.demazureOperator j (P.demazureOperator i
      (P.demazureOperator j (P.demazureOperator i f)))) (c := a * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij]; congr 1; module)
  have h4 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hT (P.demazureOperator i
      (P.demazureOperator j (P.demazureOperator i f))) (c := b)
    (by subst ha hb hS hT; simp)
  have h5 := P.one_sub_mul_map_demazureOperator S hT (P.demazureOperator i (P.demazureOperator j
      (P.demazureOperator i f))) (c := a ^ 3 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hji]; congr 1; module)
  have h6 := P.one_sub_mul_map_demazureOperator (S.trans T) hT (P.demazureOperator i
      (P.demazureOperator j (P.demazureOperator i f))) (c := a ^ 3 * b ^ 2)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h7 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hS (P.demazureOperator j
      (P.demazureOperator i f)) (c := a)
    (by subst ha hb hS hT; simp)
  have h8 := P.one_sub_mul_map_demazureOperator T hS (P.demazureOperator j
      (P.demazureOperator i f)) (c := a * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij]; congr 1; module)
  have h9 := P.one_sub_mul_map_demazureOperator (T.trans S) hS (P.demazureOperator j
      (P.demazureOperator i f)) (c := a ^ 2 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h10 := P.one_sub_mul_map_demazureOperator ((T.trans S).trans T) hS (P.demazureOperator j
      (P.demazureOperator i f)) (c := a ^ 2 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h11 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hT
      (P.demazureOperator i f) (c := b)
    (by subst ha hb hS hT; simp)
  have h12 := P.one_sub_mul_map_demazureOperator S hT (P.demazureOperator i f) (c := a ^ 3 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hji]; congr 1; module)
  have h13 := P.one_sub_mul_map_demazureOperator (S.trans T) hT
      (P.demazureOperator i f) (c := a ^ 3 * b ^ 2)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h14 := P.one_sub_mul_map_demazureOperator ((S.trans T).trans S) hT
      (P.demazureOperator i f) (c := a ^ 3 * b ^ 2)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h15 := P.one_sub_mul_map_demazureOperator (((S.trans T).trans S).trans T) hT
      (P.demazureOperator i f) (c := a ^ 3 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h16 := P.one_sub_mul_map_demazureOperator (RingEquiv.refl _) hS f (c := a)
    (by subst ha hb hS hT; simp)
  have h17 := P.one_sub_mul_map_demazureOperator T hS f (c := a * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij]; congr 1; module)
  have h18 := P.one_sub_mul_map_demazureOperator (T.trans S) hS f (c := a ^ 2 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h19 := P.one_sub_mul_map_demazureOperator ((T.trans S).trans T) hS f (c := a ^ 2 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h20 := P.one_sub_mul_map_demazureOperator (((T.trans S).trans T).trans S) hS f (c := a * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have h21 := P.one_sub_mul_map_demazureOperator ((((T.trans S).trans T).trans S).trans T) hS
      f (c := a)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  simp only [RingEquiv.refl_apply, RingEquiv.trans_apply, iS, iT] at *
  linear_combination
    ((1 - a) * (1 - a * b) * (1 - a ^ 2 * b) * (1 - a ^ 3 * b) * (1 - a ^ 3 * b ^ 2)) * h1 +
    ((1 - a * b) * (1 - a ^ 2 * b) * (1 - a ^ 3 * b) * (1 - a ^ 3 * b ^ 2)) * h2 +
    (-b * (1 - a) * (1 - a ^ 2 * b) * (1 - a ^ 3 * b) * (1 - a ^ 3 * b ^ 2)) * h3 +
    ((1 - a ^ 2 * b) * (1 - a ^ 3 * b) * (1 - a ^ 3 * b ^ 2)) * h4 +
    (-a * (1 - a * b) * (1 - a ^ 2 * b) * (1 - a ^ 3 * b ^ 2)) * h5 +
    (a * b ^ 2 * (1 - a) * (1 - a ^ 2 * b) * (1 - a ^ 3 * b)) * h6 +
    ((1 + a ^ 2 * b) * (1 - a ^ 2 * b) * (1 - a ^ 3 * b ^ 2)) * h7 +
    ((-b - a ^ 2 * b ^ 2) * (1 - a ^ 2 * b) * (1 - a ^ 3 * b)) * h8 +
    (a ^ 4 * b * (1 - a * b) * (1 - a ^ 3 * b ^ 2)) * h9 +
    (-a ^ 4 * b ^ 4 * (1 - a) * (1 - a ^ 3 * b)) * h10 + ((1 + a ^ 2 * b) * (1 - a ^ 2 * b)) * h11 +
    (-a * (1 - a ^ 3 * b ^ 2)) * h12 + (a * b ^ 2 * (1 - a ^ 3 * b)) * h13 +
    (-a ^ 6 * b ^ 2 * (1 - a * b)) * h14 + (a ^ 6 * b ^ 5 * (1 - a)) * h15 + h16 + (-b) * h17 +
    (a ^ 4 * b) * h18 + (-a ^ 4 * b ^ 4) * h19 + (a ^ 9 * b ^ 4) * h20 + (-a ^ 9 * b ^ 6) * h21

/-! ### The braid relations -/

/-- The product of the factors `1 - e^{-β}` over the positive roots `β` of the rank-two
subsystem of type `A₁ × A₁` is not a zero divisor. -/
private lemma isLeftRegular_A1A1 {a b : AddMonoidAlgebra ℤ M} (ha : single (-P.root i) 1 = a)
    (hb : single (-P.root j) 1 = b) : IsLeftRegular ((1 - b) * (1 - a)) := by
  subst ha hb
  exact (P.isLeftRegular_one_sub_single_neg_root j).mul (P.isLeftRegular_one_sub_single_neg_root i)

/-- The product of the factors `1 - e^{-β}` over the positive roots `β` of the rank-two
subsystem of type `A₂` is not a zero divisor. -/
private lemma isLeftRegular_A2 (hji : P.pairing j i = -1) {a b : AddMonoidAlgebra ℤ M}
    (ha : single (-P.root i) 1 = a) (hb : single (-P.root j) 1 = b) :
    IsLeftRegular ((1 - b) * (1 - a) * (1 - a * b)) := by
  obtain ⟨S, hS⟩ : ∃ S, mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv = S := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, mapDomainRingEquiv ℤ (P.reflection j).toAddEquiv = T := ⟨_, rfl⟩
  have r1 := P.isLeftRegular_one_sub_map (RingEquiv.refl _) j (c := b)
    (by subst ha hb hS hT; simp)
  have r2 := P.isLeftRegular_one_sub_map (RingEquiv.refl _) i (c := a)
    (by subst ha hb hS hT; simp)
  have r3 := P.isLeftRegular_one_sub_map S j (c := a * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hji])
  exact (r1.mul r2).mul r3

/-- The product of the factors `1 - e^{-β}` over the positive roots `β` of the rank-two
subsystem of type `B₂` is not a zero divisor. -/
private lemma isLeftRegular_B2 (hij : P.pairing i j = -1) (hji : P.pairing j i = -2)
    {a b : AddMonoidAlgebra ℤ M} (ha : single (-P.root i) 1 = a)
    (hb : single (-P.root j) 1 = b) :
    IsLeftRegular ((1 - b) * (1 - a) * (1 - a * b) * (1 - a ^ 2 * b)) := by
  obtain ⟨S, hS⟩ : ∃ S, mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv = S := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, mapDomainRingEquiv ℤ (P.reflection j).toAddEquiv = T := ⟨_, rfl⟩
  have r1 := P.isLeftRegular_one_sub_map (RingEquiv.refl _) j (c := b)
    (by subst ha hb hS hT; simp)
  have r2 := P.isLeftRegular_one_sub_map (RingEquiv.refl _) i (c := a)
    (by subst ha hb hS hT; simp)
  have r3 := P.isLeftRegular_one_sub_map T i (c := a * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij]; congr 1; module)
  have r4 := P.isLeftRegular_one_sub_map S j (c := a ^ 2 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hji]; congr 1; module)
  exact ((r1.mul r2).mul r3).mul r4

/-- The product of the factors `1 - e^{-β}` over the positive roots `β` of the rank-two
subsystem of type `G₂` is not a zero divisor. -/
private lemma isLeftRegular_G2 (hij : P.pairing i j = -1) (hji : P.pairing j i = -3)
    {a b : AddMonoidAlgebra ℤ M} (ha : single (-P.root i) 1 = a)
    (hb : single (-P.root j) 1 = b) : IsLeftRegular
      ((1 - b) * (1 - a) * (1 - a * b) * (1 - a ^ 2 * b) * (1 - a ^ 3 * b) *
        (1 - a ^ 3 * b ^ 2)) := by
  obtain ⟨S, hS⟩ : ∃ S, mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv = S := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, mapDomainRingEquiv ℤ (P.reflection j).toAddEquiv = T := ⟨_, rfl⟩
  have r1 := P.isLeftRegular_one_sub_map (RingEquiv.refl _) j (c := b)
    (by subst ha hb hS hT; simp)
  have r2 := P.isLeftRegular_one_sub_map (RingEquiv.refl _) i (c := a)
    (by subst ha hb hS hT; simp)
  have r3 := P.isLeftRegular_one_sub_map T i (c := a * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij]; congr 1; module)
  have r4 := P.isLeftRegular_one_sub_map (T.trans S) i (c := a ^ 2 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  have r5 := P.isLeftRegular_one_sub_map S j (c := a ^ 3 * b)
    (by subst ha hb hS hT; simp [reflection_apply_root, hji]; congr 1; module)
  have r6 := P.isLeftRegular_one_sub_map (S.trans T) j (c := a ^ 3 * b ^ 2)
    (by subst ha hb hS hT; simp [reflection_apply_root, hij, hji]; congr 1; module)
  exact ((((r1.mul r2).mul r3).mul r4).mul r5).mul r6

/-- **The Demazure operators of orthogonal roots commute.** -/
theorem commute_demazureOperator_of_isOrthogonal (h : P.IsOrthogonal i j) :
    Commute (P.demazureOperator i) (P.demazureOperator j) := by
  obtain ⟨hij, hji⟩ := h
  refine LinearMap.ext fun f ↦ P.isLeftRegular_A1A1 (i := i) (j := j) rfl rfl ?_
  simp only [Module.End.mul_apply]
  rw [P.mul_demazureOperator_ij_A1A1 hji rfl rfl rfl rfl,
    P.mul_demazureOperator_ji_A1A1 hij rfl rfl rfl rfl,
    P.map_braid_A1A1 hij hji rfl rfl]

/-- **The braid relation of length three** for the Demazure operators of two roots with Cartan
entries `-1` and `-1`, the `A₂` configuration: `Dᵢ Dⱼ Dᵢ = Dⱼ Dᵢ Dⱼ`. -/
theorem demazureOperator_braid_three (hij : P.pairing i j = -1) (hji : P.pairing j i = -1) :
    P.demazureOperator i * P.demazureOperator j * P.demazureOperator i =
      P.demazureOperator j * P.demazureOperator i * P.demazureOperator j := by
  refine LinearMap.ext fun f ↦ P.isLeftRegular_A2 hji rfl rfl ?_
  simp only [Module.End.mul_apply]
  rw [P.mul_demazureOperator_ij_A2 hij hji rfl rfl rfl rfl,
    P.mul_demazureOperator_ji_A2 hij hji rfl rfl rfl rfl,
    P.map_braid_A2 hij hji rfl rfl]

/-- **The braid relation of length four** for the Demazure operators of two roots with Cartan
entries `⟨αᵢ, αⱼ^∨⟩ = -1` and `⟨αⱼ, αᵢ^∨⟩ = -2`, the `B₂` configuration:
`Dᵢ Dⱼ Dᵢ Dⱼ = Dⱼ Dᵢ Dⱼ Dᵢ`. -/
theorem demazureOperator_braid_four (hij : P.pairing i j = -1) (hji : P.pairing j i = -2) :
    P.demazureOperator i * P.demazureOperator j * P.demazureOperator i * P.demazureOperator j =
      P.demazureOperator j * P.demazureOperator i * P.demazureOperator j *
        P.demazureOperator i := by
  refine LinearMap.ext fun f ↦ P.isLeftRegular_B2 hij hji rfl rfl ?_
  simp only [Module.End.mul_apply]
  rw [P.mul_demazureOperator_ij_B2 hij hji rfl rfl rfl rfl,
    P.mul_demazureOperator_ji_B2 hij hji rfl rfl rfl rfl,
    P.map_braid_B2 hij hji rfl rfl]

/-- **The braid relation of length six** for the Demazure operators of two roots with Cartan
entries `⟨αᵢ, αⱼ^∨⟩ = -1` and `⟨αⱼ, αᵢ^∨⟩ = -3`, the `G₂` configuration:
`(Dᵢ Dⱼ)³ = (Dⱼ Dᵢ)³`. -/
theorem demazureOperator_braid_six (hij : P.pairing i j = -1) (hji : P.pairing j i = -3) :
    P.demazureOperator i * P.demazureOperator j * P.demazureOperator i * P.demazureOperator j *
        P.demazureOperator i * P.demazureOperator j =
      P.demazureOperator j * P.demazureOperator i * P.demazureOperator j * P.demazureOperator i *
        P.demazureOperator j * P.demazureOperator i := by
  refine LinearMap.ext fun f ↦ P.isLeftRegular_G2 hij hji rfl rfl ?_
  simp only [Module.End.mul_apply]
  rw [P.mul_demazureOperator_ij_G2 hij hji rfl rfl rfl rfl,
    P.mul_demazureOperator_ji_G2 hij hji rfl rfl rfl rfl,
    P.map_braid_G2 hij hji rfl rfl]

/-! ### The braid relations of a base and word independence -/

section Base

variable [Finite ι] (b : P.Base)

/-- **The Demazure operators of the simple roots of a base satisfy the braid relations of its
Coxeter matrix**: for simple roots `αₖ`, `αₗ` with Coxeter entry `m`, the two alternating
products of `Dₖ` and `Dₗ` of length `m` agree. -/
theorem prod_map_demazureOperator_braidWord (k l : b.support) :
    ((braidWord (TauCeti.coxeterMatrixOfBase P b) k l).map
        fun m : b.support ↦ P.demazureOperator m).prod =
      ((braidWord (TauCeti.coxeterMatrixOfBase P b) l k).map
        fun m : b.support ↦ P.demazureOperator m).prod := by
  rcases eq_or_ne k l with rfl | hkl
  · rfl
  have hc (k l : b.support) : b.cartanMatrix k l = P.pairing k l := by
    simpa using b.algebraMap_cartanMatrixIn_apply ℤ k l
  have hmem := TauCeti.cartanMatrix_mul_cartanMatrix_mem_of_ne P b hkl
  have hsymm := b.cartanMatrix_apply_eq_zero_iff_symm (i := k) (j := l)
  have hkl' := b.cartanMatrix_mem_of_ne hkl
  have hlk' := b.cartanMatrix_mem_of_ne hkl.symm
  simp only [hc, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem hsymm hkl' hlk'
  -- The two Cartan entries form one of the four rank-two configurations, in either order.
  have key : P.pairing k l = 0 ∧ P.pairing l k = 0 ∨ P.pairing k l = -1 ∧ P.pairing l k = -1 ∨
      P.pairing k l = -1 ∧ P.pairing l k = -2 ∨ P.pairing k l = -2 ∧ P.pairing l k = -1 ∨
      P.pairing k l = -1 ∧ P.pairing l k = -3 ∨ P.pairing k l = -3 ∧ P.pairing l k = -1 := by
    rcases hkl' with h₁ | h₁ | h₁ | h₁ <;> rcases hlk' with h₂ | h₂ | h₂ | h₂ <;> simp_all
  simp only [braidWord, TauCeti.coxeterMatrixOfBase_apply, hc]
  rcases key with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
    simp only [h₁, h₂] <;> norm_num [alternatingWord, ← mul_assoc,
      TauCeti.coxeterOrder_zero, TauCeti.coxeterOrder_one, TauCeti.coxeterOrder_two,
      TauCeti.coxeterOrder_three]
  · exact (P.commute_demazureOperator_of_isOrthogonal ⟨h₁, h₂⟩).eq
  · exact (P.demazureOperator_braid_three h₁ h₂).symm
  · exact P.demazureOperator_braid_four h₁ h₂
  · exact (P.demazureOperator_braid_four h₂ h₁).symm
  · exact P.demazureOperator_braid_six h₁ h₂
  · exact (P.demazureOperator_braid_six h₂ h₁).symm

/-- **Word independence of the Demazure operators**: the product `D_{k₁} ⋯ D_{kᵣ}` of the Demazure
operators along a reduced word in the simple reflections of a base depends only on the element
`s_{k₁} ⋯ s_{kᵣ}` of the Weyl group that the word spells. -/
theorem prod_map_demazureOperator_eq_of_wordProd_eq [P.IsReduced] {ω ω' : List b.support}
    (hω : (TauCeti.weylCoxeterSystem P b).IsReduced ω)
    (hω' : (TauCeti.weylCoxeterSystem P b).IsReduced ω')
    (h : (TauCeti.weylCoxeterSystem P b).wordProd ω = (TauCeti.weylCoxeterSystem P b).wordProd ω') :
    (ω.map fun m : b.support ↦ P.demazureOperator m).prod =
      (ω'.map fun m : b.support ↦ P.demazureOperator m).prod :=
  TauCeti.matsumoto (TauCeti.weylCoxeterSystem P b) _ (P.prod_map_demazureOperator_braidWord b)
    hω hω' h

end Base

end RootPairing
