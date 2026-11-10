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
# Irreducibility under algebra isomorphisms and polynomials in intertwined endomorphisms

Irreducibility of a polynomial after extending its coefficients is invariant under an
isomorphism of algebras over the coefficient ring.

If a linear map `σ : M → F` intertwines endomorphisms `f` of `M` and `g` of `F`, that is
`g ∘ σ = σ ∘ f`, then it intertwines `p(f)` and `p(g)` for every polynomial `p`
(`Polynomial.aeval_comp_eq_comp_aeval`).

Since `x - c` divides `p(x) - p(c)`, a congruence `(x - c) e ≡ 0` modulo an ideal gives
`(p(x) - p(c)) e ≡ 0` for every polynomial `p` (`Polynomial.aeval_sub_algebraMap_eval_mul_mem`).
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

/-- If `σ : M → F` intertwines the endomorphisms `f` of `M` and `g` of `F`, that is
`g ∘ σ = σ ∘ f`, then `p(g) ∘ σ = σ ∘ p(f)` for every polynomial `p`. -/
theorem aeval_comp_eq_comp_aeval {R M F : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid F] [Module R F] {f : Module.End R M} {g : Module.End R F} {σ : M →ₗ[R] F}
    (hg : g ∘ₗ σ = σ ∘ₗ f) (p : R[X]) : aeval g p ∘ₗ σ = σ ∘ₗ aeval f p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, LinearMap.add_comp, LinearMap.comp_add, hp, hq]
  | monomial k a =>
    ext x
    have hx := congr($(Module.End.commute_pow_left_of_commute hg k) x)
    simp only [LinearMap.comp_apply] at hx
    simp [aeval_monomial, hx]

/-- If `(x - c) e` lies in an ideal `K`, then so does `(p(x) - p(c)) e` for every polynomial `p`,
since `x - c` divides `p(x) - p(c)`. -/
theorem aeval_sub_algebraMap_eval_mul_mem {R S : Type*} [CommSemiring R] [CommRing S]
    [Algebra R S] {K : Ideal S} {x e : S} {c : R} (he : (x - algebraMap R S c) * e ∈ K)
    (p : R[X]) : (aeval x p - algebraMap R S (p.eval c)) * e ∈ K := by
  obtain ⟨w, hw⟩ := sub_dvd_eval_sub x (algebraMap R S c) (p.map (algebraMap R S))
  rw [eval_map_algebraMap, eval_map_algebraMap, aeval_algebraMap_apply_eq_algebraMap_eval] at hw
  rw [hw, mul_right_comm]
  exact K.mul_mem_right w he

end Polynomial
