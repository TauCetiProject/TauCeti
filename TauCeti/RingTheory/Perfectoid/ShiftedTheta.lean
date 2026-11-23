/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Perfectoid.FontaineTheta

import TauCeti.RingTheory.WittVector.Frobenius

/-!
# Frobenius-shifted Fontaine map

Precomposing Fontaine's map `θ : W(A♭) → A` with inverse Witt Frobenius gives
the shifted Fontaine map. Its kernel is the Frobenius image of `ker θ`, so a
generator of `ker θ` gives a Frobenius-translated generator of the shifted kernel.

## References

* Bhatt, Morrow and Scholze, *Integral p-adic Hodge theory*, arXiv:1602.03148v3,
  §3, following Lemma 3.2.
-/

public section

namespace WittVector

variable {A : Type*} [CommRing A] {p : ℕ} [Fact p.Prime]
  [Fact (¬IsUnit (p : A))] [IsAdicComplete (Ideal.span {(p : A)}) A]

variable (A p) in
/-- Fontaine's map precomposed with inverse Witt Frobenius. -/
noncomputable def fontaineThetaShifted : WittVector p (PreTilt A p) →+* A :=
  (fontaineTheta A p).comp (frobeniusEquiv p (PreTilt A p)).symm.toRingHom

/-- The shifted Fontaine map evaluates `θ` on the inverse Frobenius translate. -/
theorem fontaineThetaShifted_apply (x : WittVector p (PreTilt A p)) :
    fontaineThetaShifted A p x = fontaineTheta A p ((frobeniusEquiv p (PreTilt A p)).symm x) :=
  (rfl)

/-- On a Teichmüller representative, the shifted map takes the sharp of the `p`-th root. -/
@[simp]
theorem fontaineThetaShifted_teichmuller (x : PreTilt A p) :
    fontaineThetaShifted A p (teichmuller p x) =
      PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm x) := by
  rw [fontaineThetaShifted_apply, frobeniusEquiv_symm_teichmuller, fontaineTheta_teichmuller]

/-- Surjectivity of Frobenius modulo `p` makes the shifted Fontaine map surjective. -/
theorem surjective_fontaineThetaShifted
    (hF : Function.Surjective (_root_.frobenius (ModP A p) p)) :
    Function.Surjective (fontaineThetaShifted A p) :=
  (surjective_fontaineTheta hF).comp (frobeniusEquiv p (PreTilt A p)).symm.surjective

/-- The shifted kernel is the Frobenius image of the kernel of `θ`. -/
theorem ker_fontaineThetaShifted_eq_map :
    RingHom.ker (fontaineThetaShifted A p) =
      (RingHom.ker (fontaineTheta A p)).map (frobeniusEquiv p (PreTilt A p)).toRingHom := by
  rw [fontaineThetaShifted, ← RingHom.comap_ker]
  exact Ideal.comap_symm (frobeniusEquiv p (PreTilt A p))

/-- Frobenius sends a generator of `ker θ` to a generator of the shifted kernel. -/
theorem ker_fontaineThetaShifted_eq_span {ξ : WittVector p (PreTilt A p)}
    (hξ : RingHom.ker (fontaineTheta A p) = Ideal.span {ξ}) :
    RingHom.ker (fontaineThetaShifted A p) =
      Ideal.span {(frobeniusEquiv p (PreTilt A p)) ξ} := by
  rw [ker_fontaineThetaShifted_eq_map, hξ, Ideal.map_span]
  simp

end WittVector
