/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Perfectoid.FontaineTheta
public import TauCeti.RingTheory.WittVector.AdicLift

import TauCeti.RingTheory.Perfectoid.Untilt
import TauCeti.RingTheory.WittVector.Teichmuller.Coeff

/-!
# Ring homomorphisms from a perfect ring into a tilt

Let `A` be a `p`-adically complete ring in which `p` is not a unit, with tilt
`A♭ = PreTilt A p` and Fontaine's map `θ_A : W(A♭) → A`, and let `k` be a perfect ring of
characteristic `p`. Then `f ↦ θ_A ∘ W(f)` is a bijection from ring homomorphisms `k → A♭` to ring
homomorphisms `W(k) → A` (`PreTilt.wittVectorHomEquiv`).

Both sides are ring homomorphisms `k → A ⧸ p` in disguise. A ring homomorphism from the perfect ring
`k` to `A ⧸ p` lifts uniquely to the perfection `A♭` of `A ⧸ p` (`Perfection.lift`), and to a ring
homomorphism `W(k) → A` (`TauCeti.WittVector.adicLiftEquiv`). The two lifts are matched by `θ_A`,
since `θ_A ∘ W(f)` reduces modulo `p` to the zeroth coordinate of `f`, applied to the zeroth Witt
coordinate. The inverse sends `g : W(k) → A` to the map `x ↦ f x` whose sharp is `g [x]`
(`PreTilt.untilt_wittVectorHomEquiv_symm_apply`).

In other words, `k ↦ W(k)` from perfect rings of characteristic `p` is left adjoint to
`A ↦ A♭` on `p`-adically complete rings. For integral perfectoid rings this is what makes
tilting fully faithful.

## Main definitions

* `PreTilt.wittVectorHomEquiv p k A`: the bijection `(k →+* A♭) ≃ (W(k) →+* A)`,
  `f ↦ θ_A ∘ W(f)`.

## Main results

* `PreTilt.wittVectorHomEquiv_apply`: the bijection is `f ↦ θ_A ∘ W(f)`.
* `PreTilt.untilt_wittVectorHomEquiv_symm_apply`,
  `PreTilt.coeff_zero_wittVectorHomEquiv_symm_apply`: the inverse sends `g` to the map whose
  values have sharp `g [x]`, and zeroth coordinate `g [x]` modulo `p`.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, Lemma 3.2 and §3.2.
* P. Scholze, *Perfectoid spaces*, Theorem 5.2.
* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/PadicComparison/Descent/TestCovers.lean` (declaration
  `New.Variety.theta_comp_bijective`, the same bijection for the rings of `p`-adic tests);
  Apache 2.0, Copyright 2026 Anthropic, PBC.
-/

public section

open Ideal _root_.WittVector

namespace PreTilt

variable {p : ℕ} [hp : Fact p.Prime] {k : Type*} [CommRing k] [CharP k p] [PerfectRing k p]
  {A : Type*} [CommRing A] [Fact ¬IsUnit (p : A)]

local notation "𝕎" => WittVector p

variable [IsAdicComplete (span {(p : A)}) A]

/-- The ring homomorphism `k →+* A♭` lifting `g [x]` modulo `p`: the perfection lift of the
reduction modulo `p` of `g : W(k) →+* A`. -/
private noncomputable def wittVectorHomInv (g : 𝕎 k →+* A) : k →+* PreTilt A p :=
  (equivPerfection : PreTilt A p ≃+* _).symm.toRingHom.comp <|
    Perfection.lift p k (ModP A p)
      ((TauCeti.WittVector.adicLiftEquiv _ (mem_span_singleton_self (p : A))).symm g)

private theorem coeff_zero_wittVectorHomInv (g : 𝕎 k →+* A) (x : k) :
    coeff 0 (wittVectorHomInv g x) = Ideal.Quotient.mk _ (g (teichmuller p x)) := by
  set φ := (TauCeti.WittVector.adicLiftEquiv _ (mem_span_singleton_self (p : A))).symm g
  -- the zeroth coordinate of the perfection lift of `φ` is `φ`
  have hφ := RingHom.congr_fun ((Perfection.lift p k (ModP A p)).symm_apply_apply φ) x
  rw [Perfection.lift_symm_apply, RingHom.comp_apply] at hφ
  rw [wittVectorHomInv, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    coeff_equivPerfection_symm, hφ, TauCeti.WittVector.adicLiftEquiv_symm_apply]

private theorem untilt_wittVectorHomInv (g : 𝕎 k →+* A) (x : k) :
    (wittVectorHomInv g x).untilt = g (teichmuller p x) := by
  set φ := (TauCeti.WittVector.adicLiftEquiv _ (mem_span_singleton_self (p : A))).symm g
  have hg : g = TauCeti.WittVector.adicLift _ φ := by
    rw [← TauCeti.WittVector.adicLiftEquiv_apply (mem_span_singleton_self (p : A)),
      Equiv.apply_symm_apply]
  rw [wittVectorHomInv, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    untilt_equivPerfection_symm]
  conv_rhs => rw [hg, TauCeti.WittVector.adicLift_teichmuller]

variable (p k A) in
/-- **The universal property of the tilt** with respect to perfect rings: for a perfect ring `k`
of characteristic `p` and a `p`-adically complete ring `A` in which `p` is not a unit, ring
homomorphisms `f : k →+* A♭` correspond to ring homomorphisms `W(k) →+* A` by `f ↦ θ_A ∘ W(f)`
(`wittVectorHomEquiv_apply`). The inverse sends `g` to the map whose values have sharp `g [x]`
(`untilt_wittVectorHomEquiv_symm_apply`). -/
noncomputable def wittVectorHomEquiv : (k →+* PreTilt A p) ≃ (𝕎 k →+* A) where
  toFun f := (fontaineTheta A p).comp (WittVector.map f)
  invFun := wittVectorHomInv
  left_inv f := Perfection.hom_ext p fun x ↦ (by
    rw [coeff_zero_wittVectorHomInv, RingHom.comp_apply, map_teichmuller,
      fontaineTheta_teichmuller, mk_untilt_eq_coeff_zero] :
    coeff 0 (wittVectorHomInv ((fontaineTheta A p).comp (WittVector.map f)) x) = coeff 0 (f x))
  right_inv g := ringHom_ext_teichmuller fun x ↦ by
    rw [RingHom.comp_apply, map_teichmuller, fontaineTheta_teichmuller, untilt_wittVectorHomInv]

@[simp]
theorem wittVectorHomEquiv_apply (f : k →+* PreTilt A p) :
    wittVectorHomEquiv p k A f = (fontaineTheta A p).comp (WittVector.map f) :=
  (rfl)

/-- The inverse of `wittVectorHomEquiv` sends `g : W(k) →+* A` to the map `k →+* A♭` whose value
at `x` has sharp `g [x]`. -/
@[simp]
theorem untilt_wittVectorHomEquiv_symm_apply (g : 𝕎 k →+* A) (x : k) :
    ((wittVectorHomEquiv p k A).symm g x).untilt = g (teichmuller p x) :=
  untilt_wittVectorHomInv g x

/-- The inverse of `wittVectorHomEquiv` sends `g : W(k) →+* A` to the map `k →+* A♭` whose value
at `x` has zeroth coordinate `g [x]` modulo `p`. -/
@[simp]
theorem coeff_zero_wittVectorHomEquiv_symm_apply (g : 𝕎 k →+* A) (x : k) :
    coeff 0 ((wittVectorHomEquiv p k A).symm g x) = Ideal.Quotient.mk _ (g (teichmuller p x)) :=
  coeff_zero_wittVectorHomInv g x

end PreTilt
