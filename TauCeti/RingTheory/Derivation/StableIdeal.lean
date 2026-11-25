/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Colon
import TauCeti.Algebra.MvPolynomial.PDeriv
import TauCeti.RingTheory.MvPolynomial.Ideal.Derivative

/-!
# Ideals stable under derivations

An ideal `I` of a commutative ring `R` is stable under a derivation `δ` of `R` when `δ I ⊆ I`.
This file records a source of stable ideals and a consequence of stability under derivations dual
to a family of elements.

*Annihilators.* Let `M` be an `R`-module with an operator `L : M → M` obeying the Leibniz rule
`L (s • m) = δ s • m + s • L m` along `δ`, such as the Lie derivative on Kähler differentials, and
let `N` be a submodule with `L N ⊆ N`. Then the annihilator of `M ⧸ N` is `δ`-stable: if
`a • M ⊆ N`, then `δ a • m = L (a • m) - a • L m ∈ N` for every `m`.

*Dual coordinates.* Let `k` be a field, `R` a `k`-algebra, and `xⱼ ∈ R`, `δᵢ` `k`-derivations of
`R` with `δᵢ xⱼ = δᵢⱼ` (Kronecker delta). Then `δᵢ (p(x)) = (∂p/∂Xᵢ)(x)` for every polynomial `p`
over `k` (`Derivation.map_aeval_eq_aeval_pderiv`), so the preimage of a `δᵢ`-stable ideal `P`
under `p ↦ p(x)` is stable under every partial derivative. In characteristic zero such an ideal
of the polynomial ring is `⊥` or `⊤` (`Ideal.derivativeIdeal_le_self_iff`); so if `P` is proper,
the images of the `xⱼ` in `R ⧸ P` are algebraically independent over `k`. Characteristic zero is
needed: in `𝔽_p[x]` the ideal `(xᵖ)` is stable under `d/dx`, while `x` is algebraic modulo it.

Together with the stability of minimal primes over a stable ideal in characteristic zero
(`Derivation.apply_mem_of_mem_minimalPrimes`), these give the transcendence-degree bound in the
differential smoothness criterion: a prime minimal over the annihilator of the differentials
modulo coordinate differentials has residue field of transcendence degree at least the number of
coordinates.

## Main results

* `Derivation.apply_mem_annihilator_quotient`: the annihilator of `M ⧸ N` is stable under `δ`
  when `N` is stable under an operator obeying the Leibniz rule along `δ`.
* `TauCeti.algebraicIndependent_mk_of_forall_apply_mem`: in characteristic zero, elements with
  dual derivations stay algebraically independent modulo every proper stable ideal.

## References

* E. Hamann, *A question about differential ideals*, arXiv:math/0311006, proof of Lemma 0.1: the
  computation showing that annihilators are stable.
* A. Nobile, *Notes on Nash modification*, arXiv:2404.09102, Section 2, proof of Proposition 2.3:
  the use of coordinates and dual derivations to bound the dimension of a stable prime.
-/

public section

open MvPolynomial

namespace Derivation

/-- **Annihilators of quotients by stable submodules are stable.** Let `L : M → M` obey the
Leibniz rule `L (s • m) = δ s • m + s • L m` along a derivation `δ` of `S`, and let `N` be a
submodule with `L N ⊆ N`. Then `δ` maps the annihilator of `M ⧸ N` into itself. -/
theorem apply_mem_annihilator_quotient {k S M : Type*} [CommSemiring k] [CommRing S] [Algebra k S]
    [AddCommGroup M] [Module S M] (δ : Derivation k S S) {L : M → M}
    (hL : ∀ (s : S) (m : M), L (s • m) = δ s • m + s • L m) {N : Submodule S M}
    (hN : ∀ m ∈ N, L m ∈ N) {a : S} (ha : a ∈ Module.annihilator S (M ⧸ N)) :
    δ a ∈ Module.annihilator S (M ⧸ N) := by
  rw [Submodule.annihilator_quotient, Submodule.mem_colon] at ha ⊢
  intro m _
  rw [eq_sub_of_add_eq (hL a m).symm]
  exact N.sub_mem (hN _ (ha m trivial)) (ha _ trivial)

end Derivation

namespace TauCeti

/-- **Elements with dual derivations stay algebraically independent modulo a stable ideal**, in
characteristic zero. Let `R` be an algebra over a field `k` of characteristic zero, and let
`xⱼ ∈ R` and `k`-derivations `δᵢ` of `R` satisfy `δᵢ xⱼ = δᵢⱼ`. If a proper ideal `P` is stable
under every `δᵢ`, then the images of the `xⱼ` in `R ⧸ P` are algebraically independent over `k`.
-/
theorem algebraicIndependent_mk_of_forall_apply_mem {k R ι : Type*} [Field k] [CharZero k]
    [CommRing R] [DecidableEq ι] [Algebra k R] {x : ι → R} {δ : ι → Derivation k R R}
    (hδ : ∀ i j, δ i (x j) = if i = j then 1 else 0) {P : Ideal R} (hP : P ≠ ⊤)
    (hPδ : ∀ i, ∀ a ∈ P, δ i a ∈ P) :
    AlgebraicIndependent k (Ideal.Quotient.mk P ∘ x) := by
  -- The preimage of `P` in the polynomial ring is stable under every partial derivative, hence
  -- `⊥` or `⊤`; it is not `⊤` because `P` is proper.
  have hJ : (P.comap (aeval x)).derivativeIdeal ≤ P.comap (aeval x) :=
    Ideal.derivativeIdeal_le_iff.mpr ⟨le_rfl, fun i f hf ↦ by
      rw [Ideal.mem_comap, ← (δ i).map_aeval_eq_aeval_pderiv (hδ i)]
      exact hPδ i _ hf⟩
  have hJ' : P.comap (aeval (R := k) x) ≠ ⊤ := Ideal.comap_ne_top _ hP
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro p hp
  have hp' : p ∈ P.comap (aeval x) := by
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, ← hp]
    simpa [Ideal.Quotient.mkₐ_eq_mk, Function.comp_def] using
      comp_aeval_apply (f := x) (Ideal.Quotient.mkₐ k P) p
  simpa [(Ideal.derivativeIdeal_le_self_iff.mp hJ).resolve_right hJ'] using hp'

end TauCeti
