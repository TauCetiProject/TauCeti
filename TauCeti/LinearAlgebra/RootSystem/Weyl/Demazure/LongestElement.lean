/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Length
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Demazure.Braid
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Denominator.Integral

/-!
# Demazure's character formula for the longest element

Let `P` be a root datum with a base, weight lattice `M` and Weyl group `W`, and let `Dᵢ` be the
integral Demazure operator of the simple root `αᵢ` on `ℤ[M]` (`RootPairing.demazureOperator`). For
a reduced word `ω = (i₁, …, iᵣ)` of the longest element `w₀` of `W` write
`D_{w₀} = D_{i₁} ⋯ D_{iᵣ}`; by word independence
(`RootPairing.prod_map_demazureOperator_eq_of_wordProd_eq`) it does not depend on `ω`. This file
proves **Demazure's formula**

`Δ · D_{w₀}(f) = ∑_{w ∈ W} sgn(w) e^{-(ρ - w ρ)} w(f)`,

where `Δ = ∏_{α > 0} (1 - e^{-α})` is the Weyl denominator and the right-hand side is the dot
alternatization `J(f)` of `TauCeti.LinearAlgebra.RootSystem.Weyl.Denominator.Integral`. For
`f = e^λ` the right-hand side is `∑_w sgn(w) e^{w ⬝ λ}`, so `D_{w₀}(e^λ)` is Weyl's quotient: for
dominant `λ` this is the Weyl character formula, the longest-word case of the Demazure character
formula `char H⁰(X(w), L_λ) = D_w(e^λ)` on the full flag variety.

## The argument

Three facts combine.

* `J ∘ Dᵢ = J`. Put `u = Dᵢ f`. The localization identity
  `(1 - e^{-αᵢ}) u = f - e^{-αᵢ} sᵢ(f)` and the invariance `sᵢ(u) = u` give
  `u - e^{-αᵢ} sᵢ(u) = f - e^{-αᵢ} sᵢ(f)`. Since `J(e^{-αᵢ} sᵢ(g)) = -J(g)`, applying `J` gives
  `2 J(u) = 2 J(f)`.
* `D_{w₀}(f)` is Weyl-invariant. Each simple reflection `sᵢ` is a left descent of `w₀`, so `w₀` has
  a reduced word beginning with `i`, and `D_{w₀} = Dᵢ D_{w'}` has image fixed by `sᵢ`.
* `J` is linear over the Weyl-invariant elements and `J(1) = Δ`
  (`RootPairing.dotAlternatization_one`).

Hence `J(f) = J(D_{w₀} f) = D_{w₀}(f) · J(1) = Δ · D_{w₀}(f)`.

The longest element is described by the property used, that every simple reflection is a left
descent; a reduced word with this property exists
(`RootPairing.exists_isReduced_forall_isLeftDescent`).

## Main results

* `RootPairing.dotAlternatization_demazureOperator`: `J(Dᵢ f) = J(f)`.
* `RootPairing.dotAlternatization_prod_map_demazureOperator`: `J(D_{i₁} ⋯ D_{iᵣ} f) = J(f)` for
  every word.
* `RootPairing.isWeylInvariant_prod_map_demazureOperator`: `D_{w₀}(f)` is Weyl-invariant.
* `RootPairing.weylDenominator_mul_prod_map_demazureOperator`: **Demazure's formula**
  `Δ · D_{w₀}(f) = J(f)`, and `RootPairing.weylDenominator_mul_prod_map_demazureOperator_single`,
  its value on `e^λ`.

## References

* M. Demazure, *Désingularisation des variétés de Schubert généralisées*, Ann. Sci. École
  Norm. Sup. (4) 7 (1974), §2.
* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Part II, §14.
* S. Kumar, *Kac–Moody Groups, their Flag Varieties and Representation Theory*, §8.2.
-/

public section

noncomputable section

namespace RootPairing

open AddMonoidAlgebra TauCeti

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] (P : RootPairing ι ℤ M N) [Finite ι]
  (b : P.Base) [P.IsReduced]

/-- **A reduced word for the longest element**: some reduced word in the simple reflections spells
an element of which every simple reflection is a left descent. -/
theorem exists_isReduced_forall_isLeftDescent :
    ∃ ω : List b.support, (weylCoxeterSystem P b).IsReduced ω ∧
      ∀ i, (weylCoxeterSystem P b).IsLeftDescent ((weylCoxeterSystem P b).wordProd ω) i := by
  have := P.finite_weylGroup_of_base b
  obtain ⟨w, hw⟩ := exists_forall_isLeftDescent (weylCoxeterSystem P b)
  obtain ⟨ω, hω, rfl⟩ := (weylCoxeterSystem P b).exists_isReduced w
  exact ⟨ω, hω, hw⟩

/-- **The longest-element Demazure operator has Weyl-invariant image**: the product of the Demazure
operators along a reduced word of the longest element `w₀` (an element of which every simple
reflection is a left descent) sends every element of `ℤ[M]` to a Weyl-invariant one. -/
theorem isWeylInvariant_prod_map_demazureOperator {ω : List b.support}
    (hω : (weylCoxeterSystem P b).IsReduced ω)
    (hdesc : ∀ i, (weylCoxeterSystem P b).IsLeftDescent ((weylCoxeterSystem P b).wordProd ω) i)
    (f : AddMonoidAlgebra ℤ M) :
    IsWeylInvariant P ((ω.map fun m : b.support ↦ P.demazureOperator m).prod f) := by
  set cs := weylCoxeterSystem P b
  refine isWeylInvariant_of_forall_coeff_reflection P b fun i hi x ↦ ?_
  -- Some reduced word for `π ω` starts with `sᵢ`, so `D_ω = Dᵢ D_{ω'}` has image fixed by `sᵢ`.
  obtain ⟨ω', hω', hw'⟩ := cs.exists_isReduced (cs.simple ⟨i, hi⟩ * cs.wordProd ω)
  have hred := cs.isReduced_cons_of_isLeftDescent (hdesc ⟨i, hi⟩) hω' hw'.symm
  have heq := prod_map_demazureOperator_eq_of_wordProd_eq P b hω hred
    (by rw [cs.wordProd_cons, ← hw', cs.simple_mul_simple_cancel_left])
  rw [heq, List.map_cons, List.prod_cons, Module.End.mul_apply]
  nth_rewrite 2 [← P.mapDomainRingEquiv_reflection_demazureOperator i]
  rw [coeff_mapDomainRingEquiv, Finsupp.equivMapDomain_apply]
  simp [← LinearEquiv.coe_inv]

variable [Fintype P.weylGroup]

/-- **The dot alternatization absorbs the Demazure operators**: `J(Dᵢ f) = J(f)` for a simple root
`αᵢ`. -/
@[simp]
theorem dotAlternatization_demazureOperator {i : ι} (hi : i ∈ b.support)
    (f : AddMonoidAlgebra ℤ M) :
    dotAlternatization P b (P.demazureOperator i f) = dotAlternatization P b f := by
  set u := P.demazureOperator i f
  have hu : u - single (-P.root i) 1 * mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv u =
      f - single (-P.root i) 1 * mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv f := by
    rw [mapDomainRingEquiv_reflection_demazureOperator, ← one_sub_mul,
      one_sub_single_neg_root_mul_demazureOperator]
  have h2 := congrArg (dotAlternatization P b) hu
  simp only [map_sub, dotAlternatization_single_neg_root_mul P b hi, sub_neg_eq_add,
    ← two_smul ℤ] at h2
  exact smul_right_injective _ two_ne_zero h2

/-- The dot alternatization absorbs every product of Demazure operators of simple roots,
`J(D_{i₁} ⋯ D_{iᵣ} f) = J(f)`, whether or not the word is reduced. -/
theorem dotAlternatization_prod_map_demazureOperator (ω : List b.support)
    (f : AddMonoidAlgebra ℤ M) :
    dotAlternatization P b ((ω.map fun m : b.support ↦ P.demazureOperator m).prod f) =
      dotAlternatization P b f := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply,
      dotAlternatization_demazureOperator P b i.2, ih]

/-- **Demazure's formula for the longest element**: for a reduced word `ω` of the longest element
`w₀` (an element of which every simple reflection is a left descent),

`Δ · D_{w₀}(f) = ∑_{w ∈ W} sgn(w) e^{-(ρ - w ρ)} w(f)`,

where `D_{w₀}` is the product of the Demazure operators along `ω`, `Δ` is the Weyl denominator and
the right-hand side is the dot alternatization (`RootPairing.dotAlternatization_apply`). Since `Δ`
is not a zero divisor, this determines `D_{w₀}(f)`. -/
theorem weylDenominator_mul_prod_map_demazureOperator {ω : List b.support}
    (hω : (weylCoxeterSystem P b).IsReduced ω)
    (hdesc : ∀ i, (weylCoxeterSystem P b).IsLeftDescent ((weylCoxeterSystem P b).wordProd ω) i)
    (f : AddMonoidAlgebra ℤ M) :
    weylDenominator P b * (ω.map fun m : b.support ↦ P.demazureOperator m).prod f =
      dotAlternatization P b f := by
  rw [← dotAlternatization_prod_map_demazureOperator P b ω f, ← dotAlternatization_one,
    mul_comm, ← dotAlternatization_mul_of_isWeylInvariant P b
      (isWeylInvariant_prod_map_demazureOperator P b hω hdesc f), mul_one]

/-- **The Weyl character formula in Demazure's form**: for a reduced word `ω` of the longest element
`w₀` and a weight `λ`,

`Δ · D_{w₀}(e^λ) = ∑_{w ∈ W} sgn(w) e^{w λ - (ρ - w ρ)}`,

the alternating sum over the dot orbit `w ⬝ λ = w(λ + ρ) - ρ`. -/
theorem weylDenominator_mul_prod_map_demazureOperator_single {ω : List b.support}
    (hω : (weylCoxeterSystem P b).IsReduced ω)
    (hdesc : ∀ i, (weylCoxeterSystem P b).IsLeftDescent ((weylCoxeterSystem P b).wordProd ω) i)
    (lam : M) :
    weylDenominator P b * (ω.map fun m : b.support ↦ P.demazureOperator m).prod (single lam 1) =
      ∑ w : P.weylGroup, (weylSign P b w : ℤ) •
        single (w • lam - ∑ i ∈ inversionsFinset P b w⁻¹, P.root i) 1 := by
  rw [weylDenominator_mul_prod_map_demazureOperator P b hω hdesc, dotAlternatization_single]

end RootPairing
