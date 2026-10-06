/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.ProP.Inflation
public import TauCeti.NumberTheory.LocalField.ProP.Rank
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.CupForm

/-!
# Local maximal pro-`p` Galois groups are Demushkin groups

Let `K` be a nonarchimedean local field containing a primitive `p`th root of unity, for a prime
`p`. Then the maximal pro-`p` quotient `G_K(p)` of its absolute Galois group is a Demushkin group:
it is pro-`p`, `H¹(G_K(p), 𝔽_p)` is finite, `H²(G_K(p), 𝔽_p)` is one-dimensional, and the
cup-product pairing on `H¹(G_K(p), 𝔽_p)` is perfect. All four clauses are read off from `G_K`
through inflation, which is an isomorphism in degrees one and two.

When moreover `K` is a finite extension of `ℚ_[p]`, the rank of this Demushkin group, its number
of topological generators, is `[K : ℚ_[p]] + 2`; this is the rank at which Labute's classification
of Demushkin groups is applied to `G_K(p)`.

## Main results

* `TauCeti.isDemushkin_absoluteGaloisGroupProP_of_mu`: `G_K(p)` is a Demushkin group when `K`
  contains a primitive `p`th root of unity.
* `TauCeti.demushkinRank_absoluteGaloisGroupProP`: its rank is `[K : ℚ_[p]] + 2`.

## References

* S. P. Demushkin, *The group of a maximal `p`-extension of a local field*, Izv. Akad. Nauk SSSR
  Ser. Mat. 25 (1961), 329–346.
* J.-P. Serre, *Galois Cohomology*, Chapter II, §5.6, Theorem 4.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.5.11).
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Demushkin's theorem**: the maximal pro-`p` quotient `G_K(p)` of the absolute Galois group of
a nonarchimedean local field `K` containing a primitive `p`th root of unity is a Demushkin group. -/
theorem isDemushkin_absoluteGaloisGroupProP_of_mu (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    IsDemushkin p (absoluteGaloisGroupProP p K) :=
  let ⟨_, hζ⟩ := hmu
  have : NeZero (p : K) := hζ.neZero'
  .of_cupFp_injective (isProP_absoluteGaloisGroupProP p K) Module.Finite.of_finite
    (finrank_cohomFp_two_absoluteGaloisGroupProP_of_mu p K hmu)
    (cupFp_bijective_absoluteGaloisGroupProP_of_mu p K hmu).injective

/-- **The rank of the Demushkin group `G_K(p)`** is `[K : ℚ_[p]] + 2` for a finite extension `K`
of `ℚ_[p]` containing a primitive `p`th root of unity. -/
theorem demushkinRank_absoluteGaloisGroupProP [Algebra ℚ_[p] K] [ValuativeExtension ℚ_[p] K]
    (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    demushkinRank (isDemushkin_absoluteGaloisGroupProP_of_mu p K hmu) =
      Module.finrank ℚ_[p] K + 2 :=
  (isDemushkin_absoluteGaloisGroupProP_of_mu p K hmu).finrank_cohomFp_one.symm.trans
    (finrank_cohomFp_one_absoluteGaloisGroupProP_of_exists_isPrimitiveRoot p K hmu)

end TauCeti
