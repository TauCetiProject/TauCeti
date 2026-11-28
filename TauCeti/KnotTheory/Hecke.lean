/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Hecke.Trace
public import TauCeti.KnotTheory.Markov.Skein

/-!
# Skein characterization of normalized Hecke traces

The normalized braid trace `MarkovBraid.heckeTrace` and its Markov invariance are defined in
`TauCeti.KnotTheory.Hecke.Trace` for any Hecke Markov trace, together with its split-unknot
factor and skein relations. This file proves its characterization by the skein relation and
normalization.

After importing `TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace.Basic`, the canonical
specialization is obtained by taking `τ = ocneanuTrace R q z` and
`hτ = isMarkovTrace_ocneanuTrace z`. In this case the invariant is the braid-closure invariant
Jones constructs from the Ocneanu trace; its comparison with the finite-colour Jimbo traces and the
HOMFLY polynomial is proved in `TauCeti.KnotTheory.Hecke.Homfly`, its regular Laurent
polynomial extension across the zero-factor specializations is constructed in
`TauCeti.KnotTheory.Hecke.Regular`, and its hyperbolic `(α, θ)` specialization is proved in
`TauCeti.KnotTheory.Hecke.Hyperbolic`. The skein relation itself needs only linearity of `τ`.

## Main results

* `TauCeti.MarkovBraid.eq_heckeTrace_of_skein`: the skein characterization.
* `TauCeti.MarkovBraid.heckeTrace_eq_pow_componentCount_of_sub_inv_eq_zero`: closed-form evaluation
  of any normalized Hecke Markov trace at `(q : R) - ↑q⁻¹ = 0` as `C ^ (β.componentCount - 1)`.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 6.
* C. Kassel and V. Turaev, *Braid Groups*, Springer GTM 247 (2008), Section 4.2.
-/

public section

namespace TauCeti

open BraidGroup MarkovBraid InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ} {z : R}
  {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} {l : Rˣ} {C : R}

/-- **The skein characterization of the normalized Hecke trace.** A Markov invariant `F`
satisfying the skein relation `l⁻¹ * F(σᵢ c) - l * F(σᵢ⁻¹ c) = (q - q⁻¹) * F(c)`, multiplied by
`C` when an uncrossed strand is added, and with value `1` on the unknot, is the normalized Hecke
trace. In particular this applies to the Ocneanu trace. -/
theorem MarkovBraid.eq_heckeTrace_of_skein (hτ : IsMarkovTrace z τ)
    (hpos : C * l * z = 1)
    (hneg : C * ↑l⁻¹ * (z - ((q : R) - ↑q⁻¹)) = 1) {F : MarkovBraid → R}
    (hF : ∀ β γ, MarkovEquiv β γ → F β = F γ)
    (hs : ∀ n (c : BraidGroup (n + 1)) (i : Fin n),
      ↑l⁻¹ * F ⟨n, sigma (n := n + 1) i * c⟩ - l * F ⟨n, (sigma (n := n + 1) i)⁻¹ * c⟩ =
        ((q : R) - ↑q⁻¹) * F ⟨n, c⟩)
    (hι : ∀ n (b : BraidGroup (n + 1)), F ⟨n + 1, strandIncl b⟩ = C * F ⟨n, b⟩)
    (h₁ : F ⟨0, 1⟩ = 1) :
    F = fun β ↦ β.heckeTrace τ C l :=
  eq_of_skein l⁻¹ ((q : R) - ↑q⁻¹) C hF
    (fun _ _ h ↦ h.heckeTrace_eq hτ C l hpos hneg)
    (by simpa only [smul_eq_mul, inv_inv] using hs)
    (fun n c i ↦ by simpa only [smul_eq_mul, inv_inv, one_mul] using
      heckeTrace_skein (τ := τ) C l 1 c i)
    (by simpa only [smul_eq_mul] using hι)
    (fun n b ↦ by rw [smul_eq_mul, τ.heckeTrace_strandIncl])
    (by rw [h₁, heckeTrace_one_strand hτ.map_one])

/-- **Zero-factor evaluation of a normalized Hecke trace.** When `(q : R) - ↑q⁻¹ = 0`, any
normalized Markov trace with normalization parameters `(C, l)` evaluates on every braid closure `β`
to `C ^ (β.componentCount - 1)`. -/
theorem MarkovBraid.heckeTrace_eq_pow_componentCount_of_sub_inv_eq_zero (β : MarkovBraid)
    (hτ : IsMarkovTrace z τ) (hpos : C * l * z = 1)
    (hneg : C * ↑l⁻¹ * (z - ((q : R) - ↑q⁻¹)) = 1) (hq : (q : R) - ↑q⁻¹ = 0) :
    β.heckeTrace τ C l = C ^ (β.componentCount - 1) := by
  have hl : (↑l⁻¹ : R) = (l : R) := by
    have h := (IsHeckeNormalization.mk hpos hneg).mul_sub_inv_eq_inv_sub
    rw [hq, mul_zero] at h
    exact sub_eq_zero.mp h.symm
  symm
  refine congrFun (eq_heckeTrace_of_skein hτ hpos hneg
    (F := fun γ ↦ C ^ (γ.componentCount - 1))
    (fun _ _ h ↦ by rw [h.componentCount_eq]) ?_ ?_ ?_) β
  · intro n c i
    have hc := componentCount_mul_sigma_inv_mul 1 c i
    simp only [one_mul] at hc
    rw [hc, hl, hq, sub_self, zero_mul]
  · intro n b
    have hpos' : 1 ≤ componentCount ⟨n, b⟩ := componentCount_pos ⟨n, b⟩
    have he : componentCount ⟨n, b⟩ + 1 - 1 = (componentCount ⟨n, b⟩ - 1) + 1 := by omega
    rw [componentCount_strandIncl, he, pow_succ']
  · simp

end TauCeti
