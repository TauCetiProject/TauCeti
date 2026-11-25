/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Perfectoid.Untilt
public import TauCeti.RingTheory.WittVector.Cyclotomic

/-!
# The residue map of a tilt and the Witt residue specialization

Let `A` be a local ring with residue field `k` in which the prime `p` is not a unit, and let
`A♭ = PreTilt A p` be its tilt. The residue map `PreTilt.residue A p : A♭ → k` takes the zeroth
coordinate `A♭ → A ⧸ p` of a compatible system of `p`-th roots and reduces it to `k`, which is
possible because `p` lies in the maximal ideal. When `A` is `p`-adically complete it is the
reduction of the sharp map: the residue of `x` is the residue of `x♯ ∈ A`.

Applying the Witt vector functor gives the Witt residue specialization
`W(PreTilt.residue A p) : W(A♭) → W(k)`, which commutes with the Witt vector Frobenius
(`WittVector.map_frobenius`). In the main example `A = O_C` is the ring of integers of a complete
algebraically closed extension `C` of `ℚ_p`, so `W(A♭) = A_inf`, and this is the coefficient map
`A_inf → W(k)` of the crystalline cohomology of the special fibre. For a compatible system
`ε = (1, ζ_p, ζ_{p²}, …)` of `p`-power roots of unity, it sends the cyclotomic period elements
`μ = [ε] - 1`, `ξ = ∑_{j < p} [ε ^ (1 / p)] ^ j` and `ξ' = φ(ξ)` to `0`, `p` and `p`. By contrast
Fontaine's map `θ : A_inf → O_C` sends `ξ` to `0`
(`TauCeti.WittVector.cyclotomicXi_mem_ker_fontaineTheta`).

## Main definitions

* `PreTilt.residue A p : PreTilt A p →+* IsLocalRing.ResidueField A`: the residue map of the tilt.

## Main results

* `PreTilt.residue_eq_of_mk_eq_coeff_zero`: the residue of `x` is the residue of any lift to `A` of
  its zeroth coordinate.
* `PreTilt.residue_eq_residue_untilt`: for `p`-adically complete `A`, the residue of `x` is that of
  `x♯`.
* `TauCeti.WittVector.map_residue_cyclotomicMu_eq_zero`,
  `TauCeti.WittVector.map_residue_cyclotomicXi_eq_natCast`,
  `TauCeti.WittVector.map_residue_cyclotomicXiTilde_eq_natCast`: if `ε♯ = 1`, the Witt residue
  specialization sends `μ`, `ξ` and `ξ'` to `0`, `p` and `p`.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Introduction (p. 4) and
  §4.2.
-/

public section

open Ideal IsLocalRing _root_.WittVector

namespace PreTilt

variable (A : Type*) [CommRing A] [IsLocalRing A] (p : ℕ) [Fact p.Prime] [Fact ¬IsUnit (p : A)]

/-- The residue map `A♭ → k` of the tilt of a local ring `A` with residue field `k` in which `p` is
not a unit: the zeroth coordinate `A♭ → A ⧸ p`, followed by the reduction `A ⧸ p → k`. -/
noncomputable def residue : PreTilt A p →+* ResidueField A :=
  (Ideal.Quotient.lift _ (IsLocalRing.residue A) fun a ha ↦ by
    obtain ⟨b, rfl⟩ := mem_span_singleton'.mp ha
    rw [residue_eq_zero_iff]
    exact mul_mem_left _ b ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr Fact.out))).comp
    (coeff 0)

variable {A p}

/-- The residue of `x : A♭` is the residue of any lift `a ∈ A` of its zeroth coordinate. -/
theorem residue_eq_of_mk_eq_coeff_zero {x : PreTilt A p} {a : A}
    (h : Ideal.Quotient.mk (span {(p : A)}) a = coeff 0 x) :
    residue A p x = IsLocalRing.residue A a := by
  rw [residue, RingHom.comp_apply, ← h, Ideal.Quotient.lift_mk]

section Complete

variable [IsAdicComplete (span {(p : A)}) A]

/-- For a `p`-adically complete local ring `A`, the residue of `x : A♭` is the residue of its
untilt `x♯ ∈ A`. -/
theorem residue_eq_residue_untilt (x : PreTilt A p) :
    residue A p x = IsLocalRing.residue A x.untilt :=
  residue_eq_of_mk_eq_coeff_zero (mk_untilt_eq_coeff_zero x)

end Complete

end PreTilt

namespace TauCeti.WittVector

open PreTilt

variable {A : Type*} [CommRing A] [IsLocalRing A] {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : A)]
  [IsAdicComplete (span {(p : A)}) A]

/-- If `ε♯ = 1`, the Witt residue specialization `W(A♭) → W(k)` kills `μ = [ε] - 1`. -/
theorem map_residue_cyclotomicMu_eq_zero {ε : PreTilt A p} (hε : ε.untilt = 1) :
    map (residue A p) (cyclotomicMu p ε) = 0 := by
  rw [map_cyclotomicMu, residue_eq_residue_untilt, hε, map_one, cyclotomicMu_one]

/-- If `ε♯ = 1`, the Witt residue specialization `W(A♭) → W(k)` sends
`ξ = ∑_{j < p} [ε ^ (1 / p)] ^ j` to `p`. -/
theorem map_residue_cyclotomicXi_eq_natCast {ε : PreTilt A p} (hε : ε.untilt = 1) :
    map (residue A p) (cyclotomicXi p ε) = p :=
  map_cyclotomicXi_eq_natCast p (by rw [residue_eq_residue_untilt, hε, map_one])

/-- If `ε♯ = 1`, the Witt residue specialization `W(A♭) → W(k)` sends `ξ' = ∑_{j < p} [ε] ^ j` to
`p`. -/
theorem map_residue_cyclotomicXiTilde_eq_natCast {ε : PreTilt A p} (hε : ε.untilt = 1) :
    map (residue A p) (cyclotomicXiTilde p ε) = p :=
  map_cyclotomicXiTilde_eq_natCast p (by rw [residue_eq_residue_untilt, hε, map_one])

end TauCeti.WittVector
