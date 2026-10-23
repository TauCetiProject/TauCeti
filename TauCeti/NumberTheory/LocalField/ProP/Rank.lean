/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Inflation
public import TauCeti.NumberTheory.LocalField.Cohomology
public import TauCeti.NumberTheory.LocalField.RootsOfUnity.Cyclotomic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.CohomFp

/-!
# Finite generation and rank of local maximal pro-`p` Galois groups

For a nonarchimedean local field `K` of characteristic different from the prime `p`, its
maximal pro-`p` Galois group is topologically finitely generated. Degree-one inflation
identifies its continuous cohomology with that of the absolute Galois group, whose finiteness
then gives finite generation by the pro-`p` Burnside basis theorem.

For a compatible extension of `ℚ_[p]` containing a primitive `p`th root of unity, the
generator rank is `[K : ℚ_[p]] + 2`. This is the rank used in Demushkin presentations; its
computation needs only degree-one cohomology, independently of degree-two local duality.
In particular `ℚ_p(μ_p)` has generator rank `p + 1`.

## References

* J.-P. Serre, *Galois Cohomology*, I §4.2 and II §5.2.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  (3.9.1) and (7.5.11).
-/

public section

namespace TauCeti

universe u

variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Degree-one cohomology of the maximal pro-`p` Galois group of a local field is finite
when `p` is nonzero in the field. In particular it is finite-dimensional over `𝔽_p`. -/
instance finite_cohomFp_one_absoluteGaloisGroupProP [NeZero (p : K)] :
    Finite (cohomFp p (absoluteGaloisGroupProP p K) 1) :=
  Finite.of_equiv (cohomFp p (Field.absoluteGaloisGroup K) 1)
    (inflH1AbsoluteGaloisProP p K).symm.toEquiv

/-- The maximal pro-`p` Galois group of a local field of characteristic different from `p`
is topologically finitely generated. -/
theorem isTopologicallyFinitelyGenerated_absoluteGaloisGroupProP [NeZero (p : K)] :
    IsTopologicallyFinitelyGenerated (absoluteGaloisGroupProP p K) :=
  (isProP_absoluteGaloisGroupProP p K).finite_cohomFp_one_iff.mp inferInstance

variable [Algebra ℚ_[p] K] [ValuativeExtension ℚ_[p] K]

/-- If a compatible extension of `ℚ_[p]` contains `μ_p`, the first cohomology of its
maximal pro-`p` Galois group has dimension `[K : ℚ_[p]] + 2`. -/
theorem finrank_cohomFp_one_absoluteGaloisGroupProP_of_exists_isPrimitiveRoot
    (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    Module.finrank (ZMod p) (cohomFp p (absoluteGaloisGroupProP p K) 1) =
      Module.finrank ℚ_[p] K + 2 :=
  (inflH1AbsoluteGaloisProP p K).finrank_eq.trans
    (finrank_cohomFp_one_absoluteGaloisGroup_of_exists_isPrimitiveRoot p K hmu)

/-- If a compatible extension of `ℚ_[p]` contains `μ_p`, its maximal pro-`p` Galois group
has exactly `[K : ℚ_[p]] + 2` topological generators. The finite-generation witness is
explicit, so the natural-valued rank is never applied to an infinitely generated group. -/
theorem topologicalGeneratorRankNat_absoluteGaloisGroupProP_of_mu
    (hfg : IsTopologicallyFinitelyGenerated (absoluteGaloisGroupProP p K))
    (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    topologicalGeneratorRankNat (absoluteGaloisGroupProP p K) hfg =
      Module.finrank ℚ_[p] K + 2 :=
  ((isProP_absoluteGaloisGroupProP p K).finrank_cohomFp_one hfg).symm.trans
    (finrank_cohomFp_one_absoluteGaloisGroupProP_of_exists_isPrimitiveRoot p K hmu)

/-- The maximal pro-`p` Galois group of `ℚ_p(μ_p)` has generator rank `p + 1`.
The statement applies to any compatible local-field model of the cyclotomic extension. -/
theorem topologicalGeneratorRankNat_cyclotomic_prime_ratPadic
    [IsCyclotomicExtension {p} ℚ_[p] K]
    (hfg : IsTopologicallyFinitelyGenerated (absoluteGaloisGroupProP p K)) :
    topologicalGeneratorRankNat (absoluteGaloisGroupProP p K) hfg = p + 1 := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ_[p] K := by
    simpa using (inferInstance : IsCyclotomicExtension {p} ℚ_[p] K)
  have hdegree : Module.finrank ℚ_[p] K = p - 1 := by
    simpa using finrank_cyclotomic_prime_pow_ratPadic p K 0
  rw [topologicalGeneratorRankNat_absoluteGaloisGroupProP_of_mu p K hfg
    ⟨IsCyclotomicExtension.zeta p ℚ_[p] K, IsCyclotomicExtension.zeta_spec p ℚ_[p] K⟩, hdegree]
  have hp := (Fact.out : p.Prime).two_le
  omega

end TauCeti
