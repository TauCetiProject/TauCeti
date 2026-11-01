/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.LongestElement
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Demazure.Parabolic
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Sign
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Vector

/-!
# The Demazure operator of the longest element

Let `P` be a root datum with weight lattice `M`, base `b` and finite Weyl group `W`, and let
`Dᵢ` be the integral Demazure operator of the simple root `αᵢ` on `ℤ[M]`
(`RootPairing.demazureOperator`). For a reduced word `ω = k₁ ⋯ kᵣ` of the longest element `w₀`
write `D_{w₀} = D_{k₁} ⋯ D_{kᵣ}`. This file proves Demazure's formula for `D_{w₀}`:

`J(1) · D_{w₀}(f) = J(f)`,

where `J` is the **`ρ`-shifted alternation** (`RootPairing.weylAlternation`)

`J(f) = ∑_{w ∈ W} sgn(w) e^{w ρ - ρ} w(f)`.

Applied to `f = e^λ` this is the Weyl character formula in Weyl's original form
`A_ρ · D_{w₀}(e^λ) = A_{λ + ρ}`, with `A_μ = ∑_{w ∈ W} sgn(w) e^{w μ}`, multiplied through by
`e^{-ρ}`: indeed `J(e^λ) = e^{-ρ} A_{λ + ρ}` and `J(1) = e^{-ρ} A_ρ`. The operators `D_w` are the
right-hand sides of the Demazure character formula `char H⁰(X(w), L_λ) = D_w(e^λ)`, and `w₀` is
the case in which the Schubert variety `X(w₀)` is the whole flag variety; no geometry is used
here.

The Weyl vector `ρ` need not be a weight of an integral root datum, but `w ρ - ρ` always is: it is
`-∑_{α > 0, w⁻¹ α < 0} α`, the negative of the sum of the positive roots that `w⁻¹` makes negative
(`TauCeti.smul_weylVector_sub_weylVector`). That inversion sum is how the shift is written here,
so no division by `2` occurs.

## The argument

Write `σ_w` for the action of `w` on `ℤ[M]` by reindexing.

* **`J` absorbs every simple Demazure operator**, `J(Dᵢ f) = J(f)`
  (`RootPairing.weylAlternation_demazureOperator`). Reindexing the sum over `W` along
  `w ↦ w sᵢ`, which changes the shift by `-w αᵢ` (`TauCeti.sum_inversionsFinset_mul_ofIdx_inv`)
  and the sign by `-1`, gives
  `J(e^{-αᵢ} σ_{sᵢ}(f)) = -J(f)`. The localization identity
  `(1 - e^{-αᵢ}) Dᵢ(f) = f - e^{-αᵢ} σ_{sᵢ}(f)` and the invariance `σ_{sᵢ}(Dᵢ f) = Dᵢ f` then give
  `2 J(Dᵢ f) = 2 J(f)`.
* **`J` is linear over the Weyl-invariant elements**, since every `σ_w` is a ring homomorphism.
* **`D_{w₀}(f)` is Weyl-invariant.** Every simple reflection is a left descent of `w₀`, so
  `Dᵢ D_{w₀} = D_{w₀}`, and `D_{w₀}(f)` is fixed by every simple reflection, hence by `W`
  (`RootPairing.isWeylInvariant_of_forall_demazureOperator_eq_self`).

Together, `J(f) = J(D_{w₀} f) = D_{w₀}(f) · J(1)`.

The Weyl denominator identity says that `J(1)` is the Weyl denominator
`Δ = ∏_{α > 0} (1 - e^{-α})` (`TauCeti.weylDenominator_eq_weylNumerator_zero`, proved for root
pairings over a linearly ordered ring in which `2` is invertible), which turns the formula into
`Δ · D_{w₀}(e^λ) = N(λ)`, the form of
`TauCeti.formalCharacter_mul_weylDenominator_eq_weylNumerator`.
That identity is not transferred to integral root data here; the formula above does not need it.

## Main definitions

* `RootPairing.weylAlternation`: the `ρ`-shifted alternation
  `J(f) = ∑_{w ∈ W} sgn(w) e^{w ρ - ρ} w(f)`.

## Main results

* `RootPairing.weylAlternation_single` and `RootPairing.weylAlternation_one`: the values
  `J(e^λ) = ∑_{w ∈ W} sgn(w) e^{w λ + w ρ - ρ}` and `J(1) = ∑_{w ∈ W} sgn(w) e^{w ρ - ρ}`.
* `RootPairing.weylAlternation_demazureOperator`: `J(Dᵢ f) = J(f)` for every simple root.
* `RootPairing.weylAlternation_mul_of_isWeylInvariant`: `J(g f) = g J(f)` for Weyl-invariant `g`.
* `RootPairing.isWeylInvariant_of_forall_demazureOperator_eq_self`: an element fixed by every
  simple Demazure operator is Weyl-invariant.
* `RootPairing.isWeylInvariant_prod_map_demazureOperator`: `D_{w₀}(f)` is Weyl-invariant.
* `RootPairing.weylAlternation_one_mul_prod_map_demazureOperator`: **Demazure's formula**
  `J(1) · D_{w₀}(f) = J(f)`.
* `RootPairing.weylAlternation_one_mul_prod_map_demazureOperator_single`: **the Weyl character
  formula** `J(1) · D_{w₀}(e^λ) = ∑_{w ∈ W} sgn(w) e^{w λ + w ρ - ρ}`.

## References

* M. Demazure, *Une nouvelle formule des caractères*, Bull. Sci. Math. (2) 98 (1974), 163–172.
* S. Kumar, *Kac–Moody Groups, their Flag Varieties and Representation Theory*, Progress in
  Mathematics 204, Birkhäuser (2002), Chapter 8.
* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Part II, Chapter 14.
-/

public section

noncomputable section

namespace RootPairing

open AddMonoidAlgebra CoxeterSystem TauCeti

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] (P : RootPairing ι ℤ M N)

/-! ### The Weyl group acting on `ℤ[M]` -/

/-- The reindexing of `ℤ[M]` along `x ↦ w x`, as a ring homomorphism; its underlying function is
`AddMonoidAlgebra.mapDomain (w • ·)`. -/
private abbrev weylAct (w : P.weylGroup) : AddMonoidAlgebra ℤ M →+* AddMonoidAlgebra ℤ M :=
  mapDomainRingHom ℤ (DistribSMul.toAddMonoidHom M w)

private lemma weylAct_apply (w : P.weylGroup) (f : AddMonoidAlgebra ℤ M) :
    P.weylAct w f = mapDomain (w • ·) f := rfl

private lemma weylAct_single (w : P.weylGroup) (x : M) (c : ℤ) :
    P.weylAct w (single x c) = single (w • x) c :=
  mapDomain_single

private lemma weylAct_mul (v w : P.weylGroup) (f : AddMonoidAlgebra ℤ M) :
    P.weylAct (v * w) f = P.weylAct v (P.weylAct w f) := by
  have h : DistribSMul.toAddMonoidHom M (v * w) =
      (DistribSMul.toAddMonoidHom M v).comp (DistribSMul.toAddMonoidHom M w) :=
    AddMonoidHom.ext fun x ↦ mul_smul v w x
  rw [weylAct, h, mapDomainRingHom_comp, RingHom.comp_apply]

/-- The coefficient of `σ_w f` at `w x` is the coefficient of `f` at `x`. -/
private lemma coeff_mapDomain_smul_smul (w : P.weylGroup) (f : AddMonoidAlgebra ℤ M) (x : M) :
    (mapDomain (w • ·) f).coeff (w • x) = f.coeff x := by
  -- Expose `Finsupp.mapDomain` on the coefficients, which has the injectivity lemma.
  change (Finsupp.mapDomain (w • ·) f.coeff) (w • x) = _
  exact Finsupp.mapDomain_apply_of_injective (MulAction.injective w) _ x

/-- The reflection of a simple Demazure operator, as a reindexing along a Weyl-group element. -/
private lemma mapDomainRingEquiv_reflection_eq (i : ι) (f : AddMonoidAlgebra ℤ M) :
    mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv f = P.weylAct (weylGroup.ofIdx P i) f := by
  have h : ((P.reflection i).toAddEquiv : M →+ M) =
      DistribSMul.toAddMonoidHom M (weylGroup.ofIdx P i) :=
    AddMonoidHom.ext fun x ↦ by simp
  rw [weylAct, ← h, ← toRingHom_mapDomainRingEquiv, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]

variable [Finite ι] [P.IsReduced] (b : P.Base)

/-! ### Simple reflections generate the Weyl-invariant elements -/

/-- **An element fixed by every simple Demazure operator is Weyl-invariant.** By
`RootPairing.demazureOperator_eq_self_iff` it is fixed by every simple reflection, and the simple
reflections generate the Weyl group. This is the converse of
`RootPairing.demazureOperator_eq_self_of_isWeylInvariant`. -/
theorem isWeylInvariant_of_forall_demazureOperator_eq_self {f : AddMonoidAlgebra ℤ M}
    (hf : ∀ i ∈ b.support, P.demazureOperator i f = f) : IsWeylInvariant P f := by
  have hs (i : b.support) (y : M) : f.coeff (weylGroup.ofIdx P (i : ι) • y) = f.coeff y := by
    have h := (P.demazureOperator_eq_self_iff i).mp (hf i i.2)
    rw [mapDomainRingEquiv_reflection_eq, weylAct_apply] at h
    rw [← coeff_mapDomain_smul_smul P (weylGroup.ofIdx P (i : ι)) f y, h]
  refine (isWeylInvariant_iff P f).mpr fun w ↦ ?_
  obtain ⟨l, rfl⟩ := (weylCoxeterSystem P b).wordProd_surjective w
  induction l with
  | nil => simp
  | cons a l ih =>
    intro x
    rw [(weylCoxeterSystem P b).wordProd_cons, weylCoxeterSystem_simple, mul_smul, hs, ih]

variable {P b} in
/-- **The Demazure operator of the longest element has Weyl-invariant values.** If `ω` is a
reduced word of the element `w₀` inverting every positive root, then every simple reflection is a
left descent of `w₀`, so `Dᵢ D_{w₀} = D_{w₀}`, and `D_{w₀}(f)` is fixed by every simple Demazure
operator. -/
theorem isWeylInvariant_prod_map_demazureOperator {ω : List b.support}
    (hω : (weylCoxeterSystem P b).IsReduced ω)
    (hω₀ : inversions P b ((weylCoxeterSystem P b).wordProd ω) = posRoots P b)
    (f : AddMonoidAlgebra ℤ M) :
    IsWeylInvariant P ((ω.map fun m : b.support ↦ P.demazureOperator m).prod f) := by
  refine P.isWeylInvariant_of_forall_demazureOperator_eq_self b fun i hi ↦ ?_
  have hdesc : (weylCoxeterSystem P b).IsLeftDescent ((weylCoxeterSystem P b).wordProd ω)
      ⟨i, hi⟩ := by
    rw [CoxeterSystem.IsLeftDescent, weylCoxeterSystem_simple, length_weylCoxeterSystem_eq,
      length_weylCoxeterSystem_eq,
      ncard_inversions_ofIdx_mul_lt_iff P b _ (b.isPos_of_mem_support hi),
      inversions_inv_eq_posRoots hω₀]
    exact (mem_posRoots P b i).mpr (b.isPos_of_mem_support hi)
  rw [← Module.End.mul_apply,
    P.demazureOperator_mul_prod_map_demazureOperator_of_isLeftDescent b hω hdesc]

/-! ### The `ρ`-shifted alternation -/

variable [Fintype P.weylGroup]

/-- **The `ρ`-shifted alternation** `J(f) = ∑_{w ∈ W} sgn(w) e^{w ρ - ρ} w(f)` on `ℤ[M]`, where
`w(f)` reindexes `f` along `x ↦ w x` and the shift `w ρ - ρ` is written as the weight
`-∑_{α > 0, w⁻¹ α < 0} α`, which needs no Weyl vector `ρ` in `M`.

On a basis element, `J(e^λ) = ∑_{w ∈ W} sgn(w) e^{w λ + w ρ - ρ}` is `e^{-ρ}` times Weyl's
alternating sum `A_{λ + ρ} = ∑_{w ∈ W} sgn(w) e^{w (λ + ρ)}`
(`RootPairing.weylAlternation_single`). -/
def weylAlternation : AddMonoidAlgebra ℤ M →ₗ[ℤ] AddMonoidAlgebra ℤ M :=
  ∑ w : P.weylGroup, (weylSign P b w : ℤ) •
    (LinearMap.mulLeft ℤ (single (-∑ i ∈ inversionsFinset P b w⁻¹, P.root i) (1 : ℤ)) ∘ₗ
      (P.weylAct w).toAddMonoidHom.toIntLinearMap)

/-- The defining formula of `RootPairing.weylAlternation`. -/
theorem weylAlternation_apply (f : AddMonoidAlgebra ℤ M) :
    P.weylAlternation b f = ∑ w : P.weylGroup, (weylSign P b w : ℤ) •
      (single (-∑ i ∈ inversionsFinset P b w⁻¹, P.root i) 1 * mapDomain (w • ·) f) := by
  simp only [weylAlternation, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    AddMonoidHom.coe_toIntLinearMap, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass,
    weylAct_apply]

/-- **The `ρ`-shifted alternation of a basis element** is
`J(e^λ) = ∑_{w ∈ W} sgn(w) e^{w λ + w ρ - ρ}`, with `w ρ - ρ = -∑_{α > 0, w⁻¹ α < 0} α`. -/
theorem weylAlternation_single (lam : M) :
    P.weylAlternation b (single lam 1) = ∑ w : P.weylGroup, (weylSign P b w : ℤ) •
      single (w • lam - ∑ i ∈ inversionsFinset P b w⁻¹, P.root i) 1 := by
  rw [weylAlternation_apply]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [mapDomain_single, single_mul_single, mul_one, neg_add_eq_sub]

/-- **The `ρ`-shifted alternation of `1`** is `J(1) = ∑_{w ∈ W} sgn(w) e^{w ρ - ρ}`, which is
`e^{-ρ}` times Weyl's denominator `A_ρ = ∑_{w ∈ W} sgn(w) e^{w ρ}`. -/
theorem weylAlternation_one :
    P.weylAlternation b 1 = ∑ w : P.weylGroup, (weylSign P b w : ℤ) •
      single (-∑ i ∈ inversionsFinset P b w⁻¹, P.root i) 1 := by
  rw [one_def, weylAlternation_single]
  simp only [smul_zero, zero_sub]

/-- Reindexing the sum along `w ↦ w sᵢ`: `J(e^{-αᵢ} sᵢ(f)) = -J(f)` for a simple root `αᵢ`. -/
private lemma weylAlternation_single_neg_root_mul {i : ι} (hi : i ∈ b.support)
    (f : AddMonoidAlgebra ℤ M) :
    P.weylAlternation b
        (single (-P.root i) 1 * mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv f) =
      -P.weylAlternation b f := by
  rw [weylAlternation_apply, weylAlternation_apply, ← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv (Equiv.mulRight (weylGroup.ofIdx P i)) _ _ fun w ↦ ?_
  -- The shift moves by `-w αᵢ`: the weight lattice of a root pairing over `ℤ` is reflexive,
  -- hence torsion free, so the cocycle identity for the inversion sum applies.
  have h2 : IsSMulRegular M (2 : ℤ) :=
    have : Module.IsReflexive ℤ M := .of_isPerfPair P.toLinearMap
    smul_right_injective M two_ne_zero
  have hsplit : single (-(∑ j ∈ inversionsFinset P b w⁻¹, P.root j + w • P.root i)) (1 : ℤ) =
      single (-∑ j ∈ inversionsFinset P b w⁻¹, P.root j) 1 * single (-(w • P.root i)) 1 := by
    rw [single_mul_single, mul_one, neg_add]
  rw [Equiv.coe_mulRight, map_mul, weylSign_ofIdx, Units.val_mul, Units.val_neg, Units.val_one,
    sum_inversionsFinset_mul_ofIdx_inv P b hi h2, hsplit, mapDomainRingEquiv_reflection_eq,
    ← weylAct_apply, ← weylAct_apply, map_mul, weylAct_single, weylAct_mul, smul_neg, mul_neg_one,
    neg_smul, neg_neg, mul_assoc]

/-- **The `ρ`-shifted alternation absorbs every simple Demazure operator**: `J(Dᵢ f) = J(f)`. -/
@[simp]
theorem weylAlternation_demazureOperator {i : ι} (hi : i ∈ b.support)
    (f : AddMonoidAlgebra ℤ M) :
    P.weylAlternation b (P.demazureOperator i f) = P.weylAlternation b f := by
  have key := congrArg (P.weylAlternation b) (P.one_sub_single_neg_root_mul_demazureOperator i f)
  have hg : P.weylAlternation b (single (-P.root i) 1 * P.demazureOperator i f) =
      -P.weylAlternation b (P.demazureOperator i f) := by
    conv_lhs => rw [← P.mapDomainRingEquiv_reflection_demazureOperator i f]
    exact P.weylAlternation_single_neg_root_mul b hi _
  rw [sub_mul, one_mul, map_sub, map_sub, hg, P.weylAlternation_single_neg_root_mul b hi] at key
  -- `key` says `2 J(Dᵢ f) = 2 J(f)`, and `ℤ[M]` has no torsion.
  refine AddMonoidAlgebra.ext (Finsupp.ext fun x ↦ ?_)
  have hx := congrArg (fun F : AddMonoidAlgebra ℤ M ↦ F.coeff x) key
  simp only [sub_neg_eq_add, coeff_add, Finsupp.coe_add, Pi.add_apply] at hx
  omega

/-- The `ρ`-shifted alternation absorbs the Demazure operator along any word of simple roots. -/
theorem weylAlternation_prod_map_demazureOperator (ω : List b.support)
    (f : AddMonoidAlgebra ℤ M) :
    P.weylAlternation b ((ω.map fun m : b.support ↦ P.demazureOperator m).prod f) =
      P.weylAlternation b f := by
  induction ω generalizing f with
  | nil => simp
  | cons a ω ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply,
      P.weylAlternation_demazureOperator b a.2, ih]

/-- **The `ρ`-shifted alternation is linear over the Weyl-invariant elements**:
`J(g f) = g J(f)` when `g` is Weyl-invariant, since each `w` acts on `ℤ[M]` by a ring
homomorphism fixing `g`. -/
theorem weylAlternation_mul_of_isWeylInvariant {g : AddMonoidAlgebra ℤ M}
    (hg : IsWeylInvariant P g) (f : AddMonoidAlgebra ℤ M) :
    P.weylAlternation b (g * f) = g * P.weylAlternation b f := by
  have hfix (w : P.weylGroup) : mapDomain (w • ·) g = g := by
    refine AddMonoidAlgebra.ext (Finsupp.ext fun x ↦ ?_)
    calc (mapDomain (w • ·) g).coeff x = (mapDomain (w • ·) g).coeff (w • w⁻¹ • x) := by
          rw [smul_inv_smul]
      _ = g.coeff x := by rw [coeff_mapDomain_smul_smul, hg.coeff_smul]
  rw [weylAlternation_apply, weylAlternation_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [← weylAct_apply, map_mul, weylAct_apply, hfix, mul_smul_comm, mul_left_comm, weylAct_apply]

/-! ### Demazure's formula for the longest element -/

variable {P b}

/-- **Demazure's formula for the longest element**: for a reduced word `ω` of the element `w₀`
inverting every positive root, `J(1) · D_{w₀}(f) = J(f)`, where
`J(f) = ∑_{w ∈ W} sgn(w) e^{w ρ - ρ} w(f)` is the `ρ`-shifted alternation. -/
theorem weylAlternation_one_mul_prod_map_demazureOperator {ω : List b.support}
    (hω : (weylCoxeterSystem P b).IsReduced ω)
    (hω₀ : inversions P b ((weylCoxeterSystem P b).wordProd ω) = posRoots P b)
    (f : AddMonoidAlgebra ℤ M) :
    P.weylAlternation b 1 * (ω.map fun m : b.support ↦ P.demazureOperator m).prod f =
      P.weylAlternation b f := by
  rw [mul_comm, ← P.weylAlternation_mul_of_isWeylInvariant b
      (isWeylInvariant_prod_map_demazureOperator hω hω₀ f), mul_one,
    weylAlternation_prod_map_demazureOperator]

/-- **The Weyl character formula, as the longest-word case of the Demazure character formula.**
For a reduced word `ω` of the element `w₀` inverting every positive root and any weight `λ`,

`(∑_{w ∈ W} sgn(w) e^{w ρ - ρ}) · D_{w₀}(e^λ) = ∑_{w ∈ W} sgn(w) e^{w λ + w ρ - ρ}`,

that is, `A_ρ · D_{w₀}(e^λ) = A_{λ + ρ}` multiplied by `e^{-ρ}`, with
`w ρ - ρ = -∑_{α > 0, w⁻¹ α < 0} α`. -/
theorem weylAlternation_one_mul_prod_map_demazureOperator_single {ω : List b.support}
    (hω : (weylCoxeterSystem P b).IsReduced ω)
    (hω₀ : inversions P b ((weylCoxeterSystem P b).wordProd ω) = posRoots P b) (lam : M) :
    (∑ w : P.weylGroup, (weylSign P b w : ℤ) •
        single (-∑ i ∈ inversionsFinset P b w⁻¹, P.root i) (1 : ℤ)) *
      (ω.map fun m : b.support ↦ P.demazureOperator m).prod (single lam 1) =
    ∑ w : P.weylGroup, (weylSign P b w : ℤ) •
      single (w • lam - ∑ i ∈ inversionsFinset P b w⁻¹, P.root i) 1 := by
  rw [← weylAlternation_one, weylAlternation_one_mul_prod_map_demazureOperator hω hω₀,
    weylAlternation_single]

end RootPairing
