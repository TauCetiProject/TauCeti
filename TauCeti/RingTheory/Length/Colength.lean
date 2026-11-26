/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.RingTheory.Length
import TauCeti.RingTheory.Length

/-!
# The colength of a scaled module

Let `M, Θ` be submodules of a module `V` over a commutative ring and `c` a scalar. This file
bounds the colength `length ((cM + Θ) ⧸ Θ)` of `Θ` in `cM + Θ`, the length of the image
`(c • M).map Θ.mkQ` of `cM` in `V ⧸ Θ`, by four colengths (the descent lemma). For submodules
`X, Y` the quotient `X ⧸ Y` is written `↥X ⧸ Y.comap X.subtype`, that is `X ⧸ (X ⊓ Y)`, which is
`X ⧸ Y` when `Y ≤ X`. All lengths are `Module.length`, valued in `ℕ∞`; no finiteness is assumed.

The proof filters the image of `cM` by the image of `cM ⊓ U` (the colength identity
`TauCeti.length_map_mkQ_eq_add_length_quotient`), bounds the latter through a submodule `N`
containing `cM ⊓ U` and a linear map `ρ` on `N` (the colength inequality
`TauCeti.length_map_mkQ_le_length_quotient`, then `TauCeti.length_quotient_sup_le` and
`TauCeti.length_quotient_sup_le_of_ker_le`), and bounds the rest by a quotient of `M`
(`TauCeti.length_quotient_smul_le`).

## Main results

* `TauCeti.length_map_mkQ_smul_le_add`: the descent lemma. Let `c` be a scalar, `M, Θ, U, N,
  N₁, Z, Z'` submodules of `V`, and `ρ : N → W` a linear map with kernel in `Z'` and image in a
  submodule `A'` of `W`; let `A` be any submodule of `W`. If
  `length (M ⧸ (M ⊓ U + M ⊓ Θ)) ≤ q`, `cM ⊓ U ≤ N` and `N₁, Z ≤ Θ`, then
  `length ((cM + Θ) ⧸ Θ) ≤ length (A' ⧸ A) + length (A ⧸ ρ(N₁)) + length (Z' ⧸ Z) + q`.
* `TauCeti.length_map_mkQ_pow_smul_le_add`: the same for `c = ϖ ^ e`, with the hypothesis on `M`
  given by a submodule `M_U ≤ M ⊓ U` and elements `t₁, …, t_p` of `M ⊓ Θ` with
  `length (M ⧸ (M_U + Σ R tᵢ)) ≤ q`.

## References

The descent lemma, with `c = ϖ ^ e` for a uniformiser `ϖ` of a discrete valuation ring and `M, Θ`
lattices, is the form in which L. Alpöge's Lean formalization of the Riemann hypothesis for
Dirichlet L-functions (https://github.com/leanprover-community/riemann-hypothesis) bounds the
index of two lattices.
-/

public section

open scoped Pointwise

namespace TauCeti

section CommRing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

variable {W : Type*} [AddCommGroup W] [Module R W]

/-- **The descent lemma.** Let `c` be a scalar and `M, Θ, U` submodules of `V` with
`length (M ⧸ (M ⊓ U + M ⊓ Θ)) ≤ q`. Let `N₁, Z ≤ Θ` and `Z'` be submodules, `N` a submodule
containing `cM ⊓ U`, and `ρ : N → W` a linear map whose kernel lies in `Z'` and whose image lies
in a submodule `A'` of `W`; let `A` be any submodule of `W`. Then, in `ℕ∞`,
`length ((cM + Θ) ⧸ Θ) ≤ length (A' ⧸ A) + length (A ⧸ ρ(N₁)) + length (Z' ⧸ Z) + q`, where
`ρ(N₁)` is the image of `N ⊓ N₁` and each quotient `X ⧸ Y` is `X ⧸ (X ⊓ Y)`. When `N₁, Z' ≤ N`,
`Z ≤ Z'` and `ρ(N₁) ≤ A ≤ A'`, these are the quotients `A' ⧸ A`, `A ⧸ ρ(N₁)` and `Z' ⧸ Z`. -/
theorem length_map_mkQ_smul_le_add {M Θ U N N₁ Z Z' : Submodule R V} {c : R} {q : ℕ∞}
    {ρ : ↥N →ₗ[R] W} {A A' : Submodule R W}
    (hq : Module.length R (↥M ⧸ (M ⊓ U ⊔ M ⊓ Θ).comap M.subtype) ≤ q)
    (hU : c • M ⊓ U ≤ N) (hN₁ : N₁ ≤ Θ) (hZ : Z ≤ Θ)
    (hker : LinearMap.ker ρ ≤ Z'.comap N.subtype) (hρ : LinearMap.range ρ ≤ A') :
    Module.length R ((c • M).map Θ.mkQ) ≤
      Module.length R (↥A' ⧸ A.comap A'.subtype) +
        Module.length R (↥A ⧸ ((N₁.comap N.subtype).map ρ).comap A.subtype) +
        Module.length R (↥Z' ⧸ Z.comap Z'.subtype) + q := by
  rw [length_map_mkQ_eq_add_length_quotient Θ (inf_le_left : c • M ⊓ U ≤ c • M)]
  calc _ ≤ Module.length R (↥Z' ⧸ Z.comap Z'.subtype) +
        (Module.length R (↥A' ⧸ A.comap A'.subtype) +
          Module.length R (↥A ⧸ ((N₁.comap N.subtype).map ρ).comap A.subtype)) + q := by
        gcongr
        · exact (length_map_mkQ_le_length_quotient (sup_le hN₁ hZ) hU).trans
            ((length_quotient_sup_le N N₁ Z Z').trans
              (add_le_add le_rfl (length_quotient_sup_le_of_ker_le hker hρ)))
        · exact (length_quotient_smul_le c M U Θ).trans hq
    _ = _ := by ring

/-- **The descent lemma for `ϖ ^ e`.** Let `M, Θ, U` be submodules of `V`, `M_U ≤ M ⊓ U` a
submodule and `t₁, …, t_p` elements of `M ⊓ Θ` with `length (M ⧸ (M_U + Σ R tᵢ)) ≤ q`. Let
`N₁, Z ≤ Θ` and `Z'` be submodules, `N` a submodule containing `ϖ ^ e M ⊓ U`, and `ρ : N → W` a
linear map whose kernel lies in `Z'` (for instance equals it) and whose image lies in a submodule
`A'` of `W`; let `A` be any submodule of `W`. Then, in `ℕ∞`,
`length ((ϖ ^ e M + Θ) ⧸ Θ) ≤ length (A' ⧸ A) + length (A ⧸ ρ(N₁)) + length (Z' ⧸ Z) + q`, with
the quotients read as in `TauCeti.length_map_mkQ_smul_le_add`, of which this is the case
`c = ϖ ^ e`. Here `ϖ` is any scalar, for instance a uniformiser of a discrete valuation ring. -/
theorem length_map_mkQ_pow_smul_le_add {M Θ U M_U N N₁ Z Z' : Submodule R V} {ϖ : R} {e p : ℕ}
    {t : Fin p → V} {q : ℕ∞} {ρ : ↥N →ₗ[R] W} {A A' : Submodule R W} (hMU : M_U ≤ M ⊓ U)
    (ht : ∀ i, t i ∈ M ⊓ Θ)
    (hq : Module.length R (↥M ⧸ (M_U ⊔ Submodule.span R (Set.range t)).comap M.subtype) ≤ q)
    (hU : ϖ ^ e • M ⊓ U ≤ N) (hN₁ : N₁ ≤ Θ) (hZ : Z ≤ Θ)
    (hker : LinearMap.ker ρ ≤ Z'.comap N.subtype) (hρ : LinearMap.range ρ ≤ A') :
    Module.length R ((ϖ ^ e • M).map Θ.mkQ) ≤
      Module.length R (↥A' ⧸ A.comap A'.subtype) +
        Module.length R (↥A ⧸ ((N₁.comap N.subtype).map ρ).comap A.subtype) +
        Module.length R (↥Z' ⧸ Z.comap Z'.subtype) + q :=
  length_map_mkQ_smul_le_add ((length_quotient_anti (Submodule.comap_mono (sup_le_sup hMU
    (Submodule.span_le.2 (Set.range_subset_iff.2 ht))))).trans hq) hU hN₁ hZ hker hρ

end CommRing

end TauCeti
