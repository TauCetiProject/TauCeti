/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.CohomFp
public import TauCeti.NumberTheory.LocalField.ProP.Inflation
public import TauCeti.NumberTheory.LocalField.ProP.Rank
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Serre
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.CohomologicalDimension

/-!
# Local maximal pro-`p` Galois groups without `μ_p` are free

Let `K` be a nonarchimedean local field not containing a primitive `p`th root of unity, for a
prime `p` invertible in `K`. By local duality `H²(G_K, 𝔽_p)` is dual to `H⁰(G_K, μ_p) = μ_p(K)`,
so it vanishes. Inflation from the maximal pro-`p` quotient `G_K(p)` is injective in degree two,
so `H²(G_K(p), 𝔽_p)` vanishes too, which for a pro-`p` group says `cd_p G_K(p) ≤ 1`. By Serre's
theorem a finitely generated pro-`p` group of cohomological dimension at most one is free.

When moreover `K` is a finite extension of `ℚ_[p]`, local duality and Kummer theory give
`#H¹(G_K, 𝔽_p) = #(Kˣ/(Kˣ)^p) = p ^ ([K : ℚ_[p]] + 1)`. So `G_K(p)` has `[K : ℚ_[p]] + 1`
generators, and it is the free pro-`p` group of that rank. This is Shafarevich's theorem; together
with Demushkin's theorem for `K ∋ μ_p` it is the dichotomy of the local maximal pro-`p` Galois
groups.

## Main results

* `TauCeti.subsingleton_cohomFp_two_absoluteGaloisGroupProP_of_not_mu` and
  `TauCeti.finrank_cohomFp_two_absoluteGaloisGroupProP_of_not_mu`: `H²(G_K(p), 𝔽_p) = 0`.
* `TauCeti.cohomologicalDimensionAt_absoluteGaloisGroupProP_le_one_of_not_mu`:
  `cd_p G_K(p) ≤ 1`.
* `TauCeti.finrank_cohomFp_one_absoluteGaloisGroupProP_of_not_mu`:
  `dim H¹(G_K(p), 𝔽_p) = [K : ℚ_[p]] + 1`.
* `TauCeti.finrank_cohomFp_one_absoluteGaloisGroupProP` and
  `TauCeti.topologicalGeneratorRankNat_absoluteGaloisGroupProP`: the Euler-characteristic
  identities `dim H¹(G_K(p), 𝔽_p) = 1 + dim H²(G_K(p), 𝔽_p) + [K : ℚ_[p]]` and
  `d(G_K(p)) = 1 + dim H²(G_K(p), 𝔽_p) + [K : ℚ_[p]]`.
* `TauCeti.topologicalGeneratorRankNat_absoluteGaloisGroupProP_of_not_mu`: `G_K(p)` has
  `[K : ℚ_[p]] + 1` topological generators.
* `TauCeti.nonempty_continuousMulEquiv_freeProP_of_not_mu`: `G_K(p)` is the free pro-`p` group
  on `[K : ℚ_[p]] + 1` generators.

## References

* I. R. Shafarevich, *On `p`-extensions*, Mat. Sb. 20 (1947), 351–363.
* J.-P. Serre, *Galois Cohomology*, Chapter II, §5.6, Theorem 3.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.5.11).
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

section NeZero

variable [NeZero (p : K)]

/-- **`H²(G_K(p), 𝔽_p)` vanishes** for a nonarchimedean local field `K` containing no primitive
`p`th root of unity, `p` being invertible in `K`: it injects into `H²(G_K, 𝔽_p)` by inflation. -/
theorem subsingleton_cohomFp_two_absoluteGaloisGroupProP_of_not_mu
    (hmu : ¬ ∃ ζ : K, IsPrimitiveRoot ζ p) :
    Subsingleton (cohomFp p (absoluteGaloisGroupProP p K) 2) :=
  have := subsingleton_cohomFp_two_absoluteGaloisGroup_of_not_mu p K hmu
  (inflH2AbsoluteGaloisProP_injective p K).subsingleton

/-- If a nonarchimedean local field `K` contains no primitive `p`th root of unity, with `p`
invertible in `K`, then `dim H²(G_K(p), 𝔽_p) = 0`. -/
theorem finrank_cohomFp_two_absoluteGaloisGroupProP_of_not_mu
    (hmu : ¬ ∃ ζ : K, IsPrimitiveRoot ζ p) :
    Module.finrank (ZMod p) (cohomFp p (absoluteGaloisGroupProP p K) 2) = 0 := by
  have := subsingleton_cohomFp_two_absoluteGaloisGroupProP_of_not_mu p K hmu
  exact Module.finrank_zero_of_subsingleton

/-- Degree-two cohomology of the maximal pro-`p` Galois group of a local field is finite
when `p` is nonzero in the field, as it injects into `H²(G_K, 𝔽_p)` by inflation. -/
instance finite_cohomFp_two_absoluteGaloisGroupProP :
    Finite (cohomFp p (absoluteGaloisGroupProP p K) 2) :=
  Finite.of_injective _ (inflH2AbsoluteGaloisProP_injective p K)

/-- For a nonarchimedean local field `K` in which `p` is invertible, `H²(G_K(p), 𝔽_p)` and
`H²(G_K, 𝔽_p)` have the same `𝔽_p`-dimension: both are `1` when `μ_p ⊆ K` and `0` when
`μ_p ⊄ K`. -/
theorem finrank_cohomFp_two_absoluteGaloisGroupProP :
    Module.finrank (ZMod p) (cohomFp p (absoluteGaloisGroupProP p K) 2) =
      Module.finrank (ZMod p) (cohomFp p (Field.absoluteGaloisGroup K) 2) := by
  by_cases hmu : ∃ ζ : K, IsPrimitiveRoot ζ p
  · exact (inflH2AbsoluteGaloisProP p K hmu).finrank_eq
  · rw [finrank_cohomFp_two_absoluteGaloisGroupProP_of_not_mu p K hmu,
      finrank_cohomFp_two_absoluteGaloisGroup_of_not_mu p K hmu]

/-- **`cd_p G_K(p) ≤ 1`** for a nonarchimedean local field `K` containing no primitive `p`th root
of unity, `p` being invertible in `K`: for the pro-`p` group `G_K(p)` this is the vanishing of
`H²(G_K(p), 𝔽_p)`. -/
theorem cohomologicalDimensionAt_absoluteGaloisGroupProP_le_one_of_not_mu
    (hmu : ¬ ∃ ζ : K, IsPrimitiveRoot ζ p) :
    cohomologicalDimensionAt.{0} p (absoluteGaloisGroupProP p K) ≤ 1 := by
  exact_mod_cast
    ((isProP_absoluteGaloisGroupProP p K).cohomologicalDimensionAt_le_iff_subsingleton_cohomFp
      1).2 (subsingleton_cohomFp_two_absoluteGaloisGroupProP_of_not_mu p K hmu)

end NeZero

variable [Algebra ℚ_[p] K] [ValuativeExtension ℚ_[p] K]

/-- If a finite compatible extension `K` of `ℚ_[p]` contains no primitive `p`th root of unity,
then `dim H¹(G_K(p), 𝔽_p) = [K : ℚ_[p]] + 1`. -/
theorem finrank_cohomFp_one_absoluteGaloisGroupProP_of_not_mu
    (hmu : ¬ ∃ ζ : K, IsPrimitiveRoot ζ p) :
    Module.finrank (ZMod p) (cohomFp p (absoluteGaloisGroupProP p K) 1) =
      Module.finrank ℚ_[p] K + 1 :=
  (inflH1AbsoluteGaloisProP p K).finrank_eq.trans
    (finrank_cohomFp_one_absoluteGaloisGroup_of_not_mu p K hmu)

/-- **The Euler-characteristic identity for `G_K(p)`** over a finite compatible extension `K` of
`ℚ_[p]`: `dim H¹(G_K(p), 𝔽_p) = 1 + dim H²(G_K(p), 𝔽_p) + [K : ℚ_[p]]`. -/
theorem finrank_cohomFp_one_absoluteGaloisGroupProP :
    Module.finrank (ZMod p) (cohomFp p (absoluteGaloisGroupProP p K) 1) =
      1 + Module.finrank (ZMod p) (cohomFp p (absoluteGaloisGroupProP p K) 2) +
        Module.finrank ℚ_[p] K := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  have : NeZero (p : K) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  rw [(inflH1AbsoluteGaloisProP p K).finrank_eq, finrank_cohomFp_two_absoluteGaloisGroupProP p K,
    finrank_cohomFp_one_absoluteGaloisGroup p K]

/-- For a finite compatible extension `K` of `ℚ_[p]`, the topological generator rank of `G_K(p)`
is `1 + dim H²(G_K(p), 𝔽_p) + [K : ℚ_[p]]`: `[K : ℚ_[p]] + 2` when `μ_p ⊆ K` and
`[K : ℚ_[p]] + 1` when `μ_p ⊄ K`. -/
theorem topologicalGeneratorRankNat_absoluteGaloisGroupProP
    (hfg : IsTopologicallyFinitelyGenerated (absoluteGaloisGroupProP p K)) :
    topologicalGeneratorRankNat (absoluteGaloisGroupProP p K) hfg =
      1 + Module.finrank (ZMod p) (cohomFp p (absoluteGaloisGroupProP p K) 2) +
        Module.finrank ℚ_[p] K :=
  ((isProP_absoluteGaloisGroupProP p K).finrank_cohomFp_one hfg).symm.trans
    (finrank_cohomFp_one_absoluteGaloisGroupProP p K)

/-- If a finite compatible extension `K` of `ℚ_[p]` contains no primitive `p`th root of unity, its
maximal pro-`p` Galois group has exactly `[K : ℚ_[p]] + 1` topological generators. -/
theorem topologicalGeneratorRankNat_absoluteGaloisGroupProP_of_not_mu
    (hfg : IsTopologicallyFinitelyGenerated (absoluteGaloisGroupProP p K))
    (hmu : ¬ ∃ ζ : K, IsPrimitiveRoot ζ p) :
    topologicalGeneratorRankNat (absoluteGaloisGroupProP p K) hfg =
      Module.finrank ℚ_[p] K + 1 :=
  ((isProP_absoluteGaloisGroupProP p K).finrank_cohomFp_one hfg).symm.trans
    (finrank_cohomFp_one_absoluteGaloisGroupProP_of_not_mu p K hmu)

/-- **Shafarevich's theorem.** If a finite compatible extension `K` of `ℚ_[p]` contains no
primitive `p`th root of unity, its maximal pro-`p` Galois group `G_K(p)` is the free pro-`p` group
on `[K : ℚ_[p]] + 1` generators. -/
theorem nonempty_continuousMulEquiv_freeProP_of_not_mu
    (hmu : ¬ ∃ ζ : K, IsPrimitiveRoot ζ p) :
    Nonempty (absoluteGaloisGroupProP p K ≃ₜ* freeProP p (Fin (Module.finrank ℚ_[p] K + 1))) := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  have : NeZero (p : K) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  have hfg := isTopologicallyFinitelyGenerated_absoluteGaloisGroupProP p K
  exact IsProP.nonempty_continuousMulEquiv_freeProP_of_cohomologicalDimensionAt_le_one
    (isProP_absoluteGaloisGroupProP p K) hfg
    (cohomologicalDimensionAt_absoluteGaloisGroupProP_le_one_of_not_mu p K hmu) _
    ((Nat.card_fin _).trans
      (topologicalGeneratorRankNat_absoluteGaloisGroupProP_of_not_mu p K hfg hmu).symm)

end TauCeti
