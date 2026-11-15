/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Coleman.Entire

/-!
# Coefficient base change for the entire Coleman transform

Coleman's entire transform commutes with continuous coefficient homomorphisms. In particular,
this applies to bounded homomorphisms of Banach coefficient rings, without injectivity,
reducedness, or multiplicativity of the norms. The finite resultant identity passes to the
independently indexed coefficient limits defining the entire transform.

Only the source ring needs the completeness and ultrametric hypotheses used to construct
those limits. Their images converge in the target ring without any completeness assumption
on that ring.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A3.
-/

public section

namespace PowerSeries

variable {R S : Type*} [NormedCommRing R] [CompleteSpace R] [NormOneClass R]
  [IsUltrametricDist R] [NormedCommRing S] {B F : R⟦X⟧}

/-- The entire Coleman transform commutes with continuous coefficient homomorphisms.
A bounded coefficient homomorphism is continuous by `AddMonoidHomClass.continuous_of_bound`.
No completeness or ultrametric hypothesis on the target ring is needed for this identity. -/
@[simp]
theorem map_colemanDEntire (hB : B.IsEntire) (hF : F.IsEntire)
    (hB₀ : coeff 0 B = 0) (hF₀ : coeff 0 F = 1) (φ : R →+* S) (hφ : Continuous φ) :
    map φ (colemanDEntire B F) = colemanDEntire (map φ B) (map φ F) := by
  symm
  apply colemanDEntire_eq_of_tendsto_coeff
  intro k
  have hlim := hφ.continuousAt.tendsto.comp
    (tendsto_coeff_colemanDBounded_trunc hB hF hB₀ hF₀ k)
  simpa only [Function.comp_def, coeff_map, trunc_map, ← Polynomial.colemanDBounded_map,
    Polynomial.coeff_map] using hlim

end PowerSeries
