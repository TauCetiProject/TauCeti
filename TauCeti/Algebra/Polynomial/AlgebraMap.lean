/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Group.Irreducible.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Algebra.Polynomial.Div

/-!
# Irreducibility under algebra isomorphisms, evaluation modulo an ideal and faithfulness

Irreducibility of a polynomial after extending its coefficients is invariant under an
isomorphism of algebras over the coefficient ring.

Since `x - c` divides `p(x) - p(c)`, a congruence `(x - c) e ≡ 0` modulo an ideal gives
`(p(x) - p(c)) e ≡ 0` for every polynomial `p` (`Polynomial.aeval_sub_algebraMap_eval_mul_mem`).

A monic polynomial of positive degree dividing every polynomial that vanishes at `f : B` forces
`A` to act faithfully on `B` (`Polynomial.Monic.faithfulSMul_of_dvd`).
-/

public section

namespace TauCeti

open Polynomial

/-- Extending coefficients to isomorphic algebras preserves irreducibility. -/
theorem irreducible_map_iff_of_algEquiv {F K K' : Type*} [CommSemiring F] [Semiring K]
    [Semiring K'] [Algebra F K] [Algebra F K'] (ψ : K ≃ₐ[F] K') (g : F[X]) :
    Irreducible (g.map (algebraMap F K)) ↔ Irreducible (g.map (algebraMap F K')) := by
  have hψ : (ψ.toRingEquiv : K →+* K').comp (algebraMap F K) = algebraMap F K' :=
    RingHom.ext ψ.commutes
  rw [← MulEquiv.irreducible_iff (mapEquiv ψ.toRingEquiv), mapEquiv_apply, Polynomial.map_map,
    hψ]

end TauCeti

namespace Polynomial

/-- If `(x - c) e` lies in an ideal `K`, then so does `(p(x) - p(c)) e` for every polynomial `p`,
since `x - c` divides `p(x) - p(c)`. -/
theorem aeval_sub_algebraMap_eval_mul_mem {R S : Type*} [CommSemiring R] [CommRing S]
    [Algebra R S] {K : Ideal S} {x e : S} {c : R} (he : (x - algebraMap R S c) * e ∈ K)
    (p : R[X]) : (aeval x p - algebraMap R S (p.eval c)) * e ∈ K := by
  obtain ⟨w, hw⟩ := sub_dvd_eval_sub x (algebraMap R S c) (p.map (algebraMap R S))
  rw [eval_map_algebraMap, eval_map_algebraMap, aeval_algebraMap_apply_eq_algebraMap_eval] at hw
  rw [hw, mul_right_comm]
  exact K.mul_mem_right w he

/-- If a monic polynomial `p` over `A` of positive degree divides every polynomial over `A`
that vanishes at `f : B`, then `A` acts faithfully on `B`: a nonzero constant is not divisible
by `p`. -/
theorem Monic.faithfulSMul_of_dvd {A B : Type*} [CommRing A] [Ring B] [Algebra A B] {p : A[X]}
    (hp : p.Monic) (hpos : 0 < p.natDegree) {f : B} (hdvd : ∀ q : A[X], aeval f q = 0 → p ∣ q) :
    FaithfulSMul A B := by
  rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  exact hp.not_dvd_of_natDegree_lt (C_ne_zero.mpr ha0) (by rwa [natDegree_C])
    (hdvd _ (by rwa [aeval_C]))

end Polynomial
