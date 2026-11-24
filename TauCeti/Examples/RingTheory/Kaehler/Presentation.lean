/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Kaehler.Presentation

/-!
# The pullback of `Ω[K⁄k]` does not generate `Ω[X'⁄k]` for an inseparable extension

Over a nontrivial ring `k` of characteristic `p ≠ 0` and for `t : k`, let
`K = k[y] ⧸ (y ^ p - t)` and `X' = k[τ, y] ⧸ (τ ^ p - t, y ^ p - t)`. Then `Ω[K⁄k] = K dy`, while
`Ω[X'⁄k]` is free on `dτ, dy` (`TauCeti.kaehlerDifferentialBasisPowSubC`), so the image `dy` of
the generator of `Ω[K⁄k]` does not span `Ω[X'⁄k]`. Base change itself is still an isomorphism:
for `k' = k[τ] ⧸ (τ ^ p - t)`, Mathlib's `KaehlerDifferential.tensorKaehlerEquiv` identifies
`X' ⊗[K] Ω[K⁄k]` with `Ω[X'⁄k']`.
-/

public section

open KaehlerDifferential MvPolynomial

namespace TauCeti.Examples

/-- **`dy` does not span `Ω[X'⁄k]`.** Over a nontrivial ring `k` of
characteristic `p ≠ 0` and for `t : k`, the differentials of
`X' = k[τ, y] ⧸ (τ ^ p - t, y ^ p - t)` are free on `dτ, dy`
(`kaehlerDifferentialBasisPowSubC`), so the single differential `dy`, the image of the generator
of `Ω[K⁄k]` for `K = k[y] ⧸ (y ^ p - t)`, does not span `Ω[X'⁄k]`. -/
theorem span_D_ne_top_powSubCQuotient {k : Type*} [CommRing k] [Nontrivial k] {p : ℕ}
    [CharP k p] (hp : p ≠ 0) (t : k) :
    Submodule.span (PowSubCQuotient k p fun _ : Fin 2 ↦ t)
        {D k (PowSubCQuotient k p fun _ : Fin 2 ↦ t) (Ideal.Quotient.mk _ (X 1))} ≠ ⊤ := by
  have : Nontrivial (PowSubCQuotient k p fun _ : Fin 2 ↦ t) := PowSubCQuotient.nontrivial hp
  set b := kaehlerDifferentialBasisPowSubC k p fun _ : Fin 2 ↦ t
  intro htop
  have hmem : b 0 ∈ Submodule.span (PowSubCQuotient k p fun _ : Fin 2 ↦ t) {b 1} := by
    rw [kaehlerDifferentialBasisPowSubC_apply k p _ 1]
    exact htop ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  have := congr(b.repr $hc 0)
  simp at this

end TauCeti.Examples
