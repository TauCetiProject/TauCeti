/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Kaehler.Presentation
import Mathlib.RingTheory.AdjoinRoot

/-!
# Kähler differentials do not commute with inseparable base change

Over a nontrivial ring `k` of characteristic `p ≠ 0` and for `t : k`, let
`K = k[y] ⧸ (y ^ p - t)` and `X' = k[τ, y] ⧸ (τ ^ p - t, y ^ p - t)`. Then `Ω[K⁄k] = K dy`, while
`Ω[X'⁄k]` is free on `dτ, dy` (`TauCeti.kaehlerDifferentialBasisPowSubC`), so the image `dy` of
the generator of `Ω[K⁄k]` does not span `Ω[X'⁄k]`.
-/

public section

open KaehlerDifferential MvPolynomial

namespace TauCeti.Examples

/-- Over a nontrivial ring `k`, with `p ≠ 0`, the ring `k[Xᵢ] ⧸ (Xᵢ ^ p - t)` is nontrivial: it
maps to `k[X] ⧸ (X ^ p - t)` by `Xᵢ ↦ X`. -/
private theorem nontrivial_powSubCQuotient {k : Type*} [CommRing k] [Nontrivial k] {p : ℕ}
    (hp : p ≠ 0) (σ : Type*) (t : k) : Nontrivial (PowSubCQuotient k p fun _ : σ ↦ t) := by
  have hdeg : 0 < (Polynomial.X ^ p - Polynomial.C t).degree := by
    rw [Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero hp)]
    exact_mod_cast Nat.pos_of_ne_zero hp
  have := (AdjoinRoot.nontrivial_iff_of_monic (Polynomial.monic_X_pow_sub_C t hp)).2 hdeg
  let f : MvPolynomial σ k →ₐ[k] AdjoinRoot (Polynomial.X ^ p - Polynomial.C t) :=
    aeval fun _ ↦ AdjoinRoot.root _
  refine (Ideal.Quotient.lift _ f.toRingHom ?_).domain_nontrivial
  intro a ha
  refine (Ideal.span_le (I := RingHom.ker f.toRingHom)).2 ?_ ha
  rintro _ ⟨i, rfl⟩
  have hroot := AdjoinRoot.eval₂_root (Polynomial.X ^ p - Polynomial.C t)
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at hroot
  simpa [f, ← AdjoinRoot.algebraMap_eq] using hroot

/-- **Ω does not commute with inseparable base change.** Over a nontrivial ring `k` of
characteristic `p ≠ 0` and for `t : k`, the differentials of
`X' = k[τ, y] ⧸ (τ ^ p - t, y ^ p - t)` are free on `dτ, dy`
(`kaehlerDifferentialBasisPowSubC`), so the single differential `dy`, the image of the generator
of `Ω[K⁄k]` for `K = k[y] ⧸ (y ^ p - t)`, does not span `Ω[X'⁄k]`. -/
theorem span_D_ne_top_powSubCQuotient {k : Type*} [CommRing k] [Nontrivial k] {p : ℕ}
    [CharP k p] (hp : p ≠ 0) (t : k) :
    Submodule.span (PowSubCQuotient k p fun _ : Fin 2 ↦ t)
        {D k (PowSubCQuotient k p fun _ : Fin 2 ↦ t) (Ideal.Quotient.mk _ (X 1))} ≠ ⊤ := by
  have := nontrivial_powSubCQuotient hp (Fin 2) t
  set b := kaehlerDifferentialBasisPowSubC k p fun _ : Fin 2 ↦ t
  intro htop
  have hmem : b 0 ∈ Submodule.span (PowSubCQuotient k p fun _ : Fin 2 ↦ t) {b 1} := by
    rw [kaehlerDifferentialBasisPowSubC_apply k p _ 1]
    exact htop ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  have := congr(b.repr $hc 0)
  simp at this

end TauCeti.Examples
