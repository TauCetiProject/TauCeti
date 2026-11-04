/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Principal
public import TauCeti.RingTheory.Ideal.Quotient.Frobenius
public import TauCeti.RingTheory.Perfect.Basic
public import TauCeti.RingTheory.Perfectoid.FontaineTheta

/-!
# Integral perfectoid rings

Fix a prime `p`. A commutative ring `A` is *integral perfectoid* (Bhatt–Morrow–Scholze,
*Integral p-adic Hodge theory*, Definition 3.5) if

* some `π ∈ A` with `π ^ p ∣ p` makes `A` `π`-adically complete and separated;
* Frobenius `A ⧸ p → A ⧸ p`, `x ↦ x ^ p`, is surjective; and
* the kernel of Fontaine's map `θ : W(A♭) → A` is principal, where `A♭ = lim_{x ↦ x ^ p} A ⧸ p`
  is the tilt (Mathlib's `PreTilt` and `WittVector.fontaineTheta`).

This is the integral counterpart of a perfectoid Tate ring: no topology is given, and the
definition does not depend on a choice of `π`. Integral perfectoid rings may have `p`-torsion and
need not be domains. Perfect rings of characteristic `p` are examples, with `π = 0`
(`of_perfectRing`).

Mathlib's `PreTilt` and `fontaineTheta` need `p` to be a nonunit, as an instance argument. The
completeness clause makes `A` `p`-adically complete, since `π ∣ p`, and then `p` lies in the
Jacobson radical; so `p` is a nonunit unless `A` is the zero ring. The kernel clause is therefore
stated for every proof that `p` is a nonunit, which makes it vacuous for the zero ring, where the
unique map to `A` has principal kernel anyway.

## Main definitions

* `TauCeti.Perfectoid.IsIntegralPerfectoid p A`: `A` is an integral perfectoid ring.

## Main results

* `TauCeti.Perfectoid.IsIntegralPerfectoid.isAdicComplete_span_natCast`: an integral perfectoid
  ring is `p`-adically complete and separated.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.not_isUnit_natCast`: in a nonzero integral perfectoid
  ring, `p` is not a unit.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.isPrincipal_ker_fontaineTheta`: the kernel of
  Mathlib's Fontaine map is principal.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.surjective_fontaineTheta`: Fontaine's map
  `θ : W(A♭) → A` is surjective.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.exists_natCast_dvd_sub_pow`: every element is a
  `p`-th power modulo `p`.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.frobeniusModPow_surjective`: for every `π` with
  `π ^ p ∣ p`, Frobenius `A ⧸ π → A ⧸ π ^ p` is surjective.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.exists_associated_untilt`: for every `π` with
  `π ^ p ∣ p` and `[IsAdicComplete (span {π}) A]`, `π` is associated to `ϖ.untilt` for some
  `ϖ : PreTilt A p` with `π * p ∣ π - ϖ.untilt` (Bhatt–Morrow–Scholze, Lemma 3.9).
* `TauCeti.Perfectoid.IsIntegralPerfectoid.of_bijective_frobeniusModPow`: if `A` is `π`-adically
  complete for a nonzerodivisor `π` with `π ^ p ∣ p` and bijective relative Frobenius
  `A ⧸ (π) → A ⧸ (π ^ p)`, then `A` is integral perfectoid (Bhatt–Morrow–Scholze, Lemma 3.10(ii)).
* `TauCeti.Perfectoid.IsIntegralPerfectoid.of_perfectRing`: a perfect ring of characteristic `p`
  is integral perfectoid; the kernel of `θ` is `(p)` (`WittVector.ker_fontaineTheta_eq_span_p`).
* `TauCeti.Perfectoid.IsIntegralPerfectoid.of_subsingleton`: so is the zero ring.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, §3.2, Definition 3.5 and
  Lemmas 3.9–3.10.
-/

public section

open Ideal
open scoped nonZeroDivisors

namespace TauCeti.Perfectoid

variable (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A]

/-- A commutative ring `A` is *integral perfectoid* if some `π` with `π ^ p ∣ p` makes `A`
`π`-adically complete and separated, Frobenius on `A ⧸ p` is surjective, and the kernel of
Fontaine's map `θ : W(A♭) → A` is principal (Bhatt–Morrow–Scholze, *Integral p-adic Hodge theory*,
Definition 3.5). Mathlib's `θ` is only defined when `p` is a nonunit and `A` is `p`-adically
complete, so the kernel condition is stated for every proof of these two facts; the second
always follows from the first clause (`isAdicComplete_span_natCast`), and the first fails only for
the zero ring (`not_isUnit_natCast`). -/
class IsIntegralPerfectoid : Prop where
  /-- Some `π` with `π ^ p ∣ p` makes `A` `π`-adically complete and separated. -/
  exists_adic_element : ∃ π : A, π ^ p ∣ (p : A) ∧ IsAdicComplete (span {π}) A
  /-- Frobenius on `A ⧸ p` is surjective. -/
  frobenius_surjective : Function.Surjective fun x : ModP A p ↦ x ^ p
  /-- The kernel of Fontaine's map `θ : W(A♭) → A` is principal. -/
  theta_kernel_principal : ∀ (hp : ¬IsUnit (p : A)) (hc : IsAdicComplete (span {(p : A)}) A),
    letI : Fact (¬IsUnit (p : A)) := ⟨hp⟩
    letI := hc
    (RingHom.ker (WittVector.fontaineTheta A p)).IsPrincipal

namespace IsIntegralPerfectoid

section Basic

variable {p A} [IsIntegralPerfectoid p A]

/-- An integral perfectoid ring is `p`-adically complete and separated: it is complete for some
`π` with `π ^ p ∣ p`, and `π ∣ p`. -/
instance isAdicComplete_span_natCast : IsAdicComplete (span {(p : A)}) A := by
  obtain ⟨π, hπ, hc⟩ := exists_adic_element (p := p) (A := A)
  exact .span_singleton_of_dvd ((dvd_pow_self π (Fact.out : p.Prime).ne_zero).trans hπ)

/-- In a nonzero integral perfectoid ring, `p` is not a unit: by completeness, `p` lies in the
Jacobson radical. This supplies the standing hypothesis of Mathlib's `PreTilt` and
`WittVector.fontaineTheta`. -/
theorem not_isUnit_natCast [Nontrivial A] : ¬IsUnit (p : A) :=
  IsAdicComplete.not_isUnit_of_mem (mem_span_singleton_self (p : A))

/-- The kernel of Fontaine's map `θ : W(A♭) → A` of an integral perfectoid ring is principal. -/
theorem isPrincipal_ker_fontaineTheta [Fact ¬IsUnit (p : A)] :
    (RingHom.ker (WittVector.fontaineTheta A p)).IsPrincipal :=
  theta_kernel_principal Fact.out inferInstance

/-- In an integral perfectoid ring, every element is a `p`-th power modulo `p`. -/
theorem exists_natCast_dvd_sub_pow (x : A) : ∃ y, (p : A) ∣ x - y ^ p := by
  obtain ⟨y, hy⟩ := frobenius_surjective (p := p) (Ideal.Quotient.mk (span {(p : A)}) x)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨y, mem_span_singleton.mp (Ideal.Quotient.eq.mp ?_)⟩
  rw [map_pow]
  exact hy.symm

/-- Fontaine's map `θ : W(A♭) → A` of an integral perfectoid ring is surjective. -/
theorem surjective_fontaineTheta [Fact ¬IsUnit (p : A)] :
    Function.Surjective (WittVector.fontaineTheta A p) :=
  _root_.surjective_fontaineTheta ((surjective_frobenius_modP_iff A).mpr exists_natCast_dvd_sub_pow)

/-- In an integral perfectoid ring, Frobenius `A ⧸ π → A ⧸ π ^ p` is surjective for every `π`
with `π ^ p ∣ p`, with no completeness assumption on `π`. This is the surjectivity half of
Bhatt–Morrow–Scholze, *Integral p-adic Hodge theory*, Lemma 3.10(i). -/
theorem frobeniusModPow_surjective {π : A} (h : π ^ p ∣ (p : A)) :
    Function.Surjective (frobeniusModPow p h) :=
  (frobeniusModPow_surjective_iff h).mpr fun x ↦
    (exists_natCast_dvd_sub_pow x).imp fun _ ↦ h.trans

/-- **Existence of compatible `p`-power roots up to a unit** (Bhatt–Morrow–Scholze, *Integral
`p`-adic Hodge theory*, Lemma 3.9). If an integral perfectoid ring `A` is `π`-adically complete for
an element `π` with `π ^ p ∣ p`, then some `ϖ : PreTilt A p` satisfies `π * p ∣ π - ϖ.untilt` and
`Associated π ϖ.untilt`. -/
theorem exists_associated_untilt [Fact ¬IsUnit (p : A)] {π : A} (hdvd : π ^ p ∣ (p : A))
    [IsAdicComplete (span {π}) A] :
    ∃ ϖ : PreTilt A p, π * (p : A) ∣ π - ϖ.untilt ∧ Associated π ϖ.untilt :=
  PreTilt.exists_associated_untilt hdvd
    ((frobeniusModPow_surjective_iff hdvd).mp (frobeniusModPow_surjective hdvd))

end Basic

/-- **Perfect rings of characteristic `p` are integral perfectoid**, with `π = 0`: the ring is
`0`-adically complete, Frobenius is bijective, and the kernel of `θ` is `(p)`
(`WittVector.ker_fontaineTheta_eq_span_p`). -/
instance of_perfectRing [CharP A p] [PerfectRing A p] : IsIntegralPerfectoid p A where
  exists_adic_element := ⟨0, by simp, inferInstance⟩
  frobenius_surjective x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨Ideal.Quotient.mk _ ((frobeniusEquiv A p).symm x), ?_⟩
    dsimp only
    rw [← map_pow, frobeniusEquiv_symm_pow_p]
  theta_kernel_principal hp hc := by
    let : Fact (¬IsUnit (p : A)) := ⟨hp⟩
    have := isReduced_of_perfectRing A p
    exact ⟨⟨p, WittVector.ker_fontaineTheta_eq_span_p⟩⟩

/-- The zero ring is integral perfectoid. -/
theorem of_subsingleton [Subsingleton A] : IsIntegralPerfectoid p A where
  exists_adic_element := ⟨0, ⟨0, Subsingleton.elim _ _⟩, inferInstance⟩
  frobenius_surjective x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨Ideal.Quotient.mk _ x, ?_⟩
    dsimp only
    rw [← map_pow, Subsingleton.elim (x ^ p) x]
  theta_kernel_principal hp := (hp (isUnit_of_subsingleton _)).elim

variable {p A} in
/-- **Relative Frobenius criterion for integral perfectoid rings** (Bhatt–Morrow–Scholze,
*Integral `p`-adic Hodge theory*, Lemma 3.10(ii)). Let `A` be `π`-adically complete for a
nonzerodivisor `π` with `π ^ p ∣ p`. If relative Frobenius `A ⧸ (π) → A ⧸ (π ^ p)` is bijective,
then `A` is an integral perfectoid ring. -/
theorem of_bijective_frobeniusModPow {π : A} {hdvd : π ^ p ∣ (p : A)}
    [IsAdicComplete (span {π}) A] (hreg : π ∈ A⁰)
    (hbij : Function.Bijective (frobeniusModPow p hdvd)) : IsIntegralPerfectoid p A where
  exists_adic_element := ⟨π, hdvd, inferInstance⟩
  frobenius_surjective := by
    have hs := exists_mul_dvd_sub_pow ((frobeniusModPow_surjective_iff hdvd).mp hbij.2)
    exact (surjective_pow_modP_iff A).mpr fun a ↦
      (hs a).imp fun _ ↦ (dvd_mul_left (p : A) π).trans
  theta_kernel_principal hp hc := by
    let : Fact (¬IsUnit (p : A)) := ⟨hp⟩
    obtain ⟨ξ, -, -, hker⟩ :=
      WittVector.exists_isDistinguished_mem_nonZeroDivisors_ker_fontaineTheta hreg hbij
    exact ⟨⟨ξ, hker⟩⟩

end IsIntegralPerfectoid

end TauCeti.Perfectoid
