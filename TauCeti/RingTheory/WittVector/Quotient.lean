/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Complete

/-!
# Reduction modulo `p` of quotients of Witt vectors

For a perfect ring `S` of characteristic `p` and an ideal `I` of `W(S)`, the zeroth Witt
coordinate induces an isomorphism
`(W(S) / I) / p ≃ S / constantCoeff(I)`.
In particular, for `I = (ξ)` the right side is `S / (ξ.coeff 0)`. Frobenius on this
reduction is surjective. These are the reduction and Frobenius calculations used to
recover the integral tilt of a quotient by a primitive Witt vector.

The construction composes Mathlib's `DoubleQuot.quotQuotEquivComm`,
`WittVector.quotientPEquiv`, and `Ideal.quotientEquiv`.
It does not require `I` to be primitive or principal.

## References

* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, Arizona Winter School 2017 notes,
  https://kskedlaya.org/papers/aws-notes.pdf, §2.3, Definition 2.3.14 and Remark 2.3.16, p. 56.
* K. S. Kedlaya, R. Liu, *Relative p-adic Hodge theory II: Imperfect period rings*,
  arXiv:1602.06899, Lemma 3.3.7.
-/

public section

namespace Ideal

open WittVector

variable {p : ℕ} [Fact p.Prime] {S : Type*} [CommRing S] [CharP S p] [PerfectRing S p]

/-- **Reduction modulo `p` of a Witt quotient.** For perfect `S` of characteristic `p`,
`(W(S) / I) / p` is canonically `S / constantCoeff(I)`. -/
noncomputable def wittVectorQuotientPEquiv (I : Ideal (WittVector p S)) :
    (WittVector p S ⧸ I) ⧸ span {(p : WittVector p S ⧸ I)} ≃+*
      S ⧸ I.map constantCoeff :=
  (Ideal.quotEquivOfEq (by simp [Ideal.map_span])).trans
    ((DoubleQuot.quotQuotEquivComm I (span {(p : WittVector p S)})).trans
      (Ideal.quotientEquiv _ _ WittVector.quotientPEquiv (by
        rw [Ideal.map_map]
        exact congrArg (fun f : WittVector p S →+* S ↦ I.map f)
          (RingHom.ext fun x ↦ (WittVector.quotientPEquiv_mk x).symm))))

/-- The reduction isomorphism sends a Witt vector to its zeroth coordinate. -/
@[simp]
theorem wittVectorQuotientPEquiv_mk_mk (I : Ideal (WittVector p S)) (x : WittVector p S) :
    I.wittVectorQuotientPEquiv (Ideal.Quotient.mk _ (Ideal.Quotient.mk I x)) =
      Ideal.Quotient.mk _ (x.coeff 0) := by
  have h := WittVector.quotientPEquiv_mk x
  simp only [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk,
    constantCoeff_apply] at h
  simpa [wittVectorQuotientPEquiv] using
    congrArg (Ideal.Quotient.mk (I.map constantCoeff)) h

/-- The inverse reduction isomorphism sends a scalar to its Teichmüller representative. -/
@[simp]
theorem wittVectorQuotientPEquiv_symm_mk (I : Ideal (WittVector p S)) (s : S) :
    I.wittVectorQuotientPEquiv.symm (Ideal.Quotient.mk _ s) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk I (teichmuller p s)) := by
  apply I.wittVectorQuotientPEquiv.injective
  simp

/-- **Frobenius on the reduction of a Witt quotient is surjective.** This applies, in
particular, to the quotient by any primitive ideal used to construct an untilt. -/
theorem surjective_pow_wittVector_quotient_span_natCast (I : Ideal (WittVector p S)) :
    Function.Surjective (fun x : (WittVector p S ⧸ I) ⧸ span {(p : WittVector p S ⧸ I)} ↦
      x ^ p) := by
  intro x
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (I.wittVectorQuotientPEquiv x)
  refine ⟨I.wittVectorQuotientPEquiv.symm
    (Ideal.Quotient.mk _ ((_root_.frobeniusEquiv S p).symm s)), ?_⟩
  apply I.wittVectorQuotientPEquiv.injective
  rw [map_pow, RingEquiv.apply_symm_apply, ← map_pow,
    _root_.frobeniusEquiv_symm_pow_p, hs]

end Ideal
