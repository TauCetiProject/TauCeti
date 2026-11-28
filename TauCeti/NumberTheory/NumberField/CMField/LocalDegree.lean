/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.NumberTheory.NumberField.CMField.FinitePlace
public import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension
public import TauCeti.RingTheory.DedekindDomain.PrimesAbove
import TauCeti.NumberTheory.NumberField.CMField.ResidueField
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Semilocal

/-!
# Local degrees of a CM field over its maximal real subfield

Let `K` be a CM field with maximal real subfield `K⁺`, and let `u` be a finite place of `K` above
the place `v` of `K⁺`. If `u` is not fixed by complex conjugation, then `u` and its conjugate
`conj u` are two distinct places above `v`. The local degrees above `v` add up to `[K : K⁺] = 2`,
so the completion `K_u` has degree `1` over `K⁺_v`, and the canonical map `K⁺_v → K_u` is an
isomorphism
(`IsDedekindDomain.HeightOneSpectrum.adicCompletionExtension_bijective_of_conjPlace_ne`).

When `K` contains a primitive fourth and a primitive seventh root of unity (for instance a
primitive `5040`-th root of unity), the places fixed by conjugation do not lie over `2`
(`NumberField.IsCMField.two_notMem_and_exists_sub_notMem_of_isPrimitiveRoot`). So every place of
`K⁺` above `2` splits in `K`, and the fourth root of unity of `K` gives a square root of `-1` in
`K⁺_v` (`NumberField.IsCMField.isSquare_neg_one_adicCompletion_of_isPrimitiveRoot`). At the other
finite places of `K⁺` every local unit is a sum of two squares, so this is the condition at `2`
under which totally positive elements of `K⁺` are sums of two squares in the quadratic algebras
of `NumberField.IsTotallyPositive.exists_sq_add_sq_quadraticAlgebra`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.finrank_adicCompletion_eq_one_of_conjPlace_ne` and
  `IsDedekindDomain.HeightOneSpectrum.adicCompletionExtension_bijective_of_conjPlace_ne`: at a
  place not fixed by conjugation, `K_u` has degree `1` over `K⁺_v`, and `K⁺_v → K_u` is bijective.
* `NumberField.IsCMField.isSquare_neg_one_adicCompletion_of_isPrimitiveRoot`: if `K` contains a
  primitive fourth and a primitive seventh root of unity, `-1` is a square in `K⁺_v` at every
  place `v` of `K⁺` above `2`.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.IsCMField
open scoped AdicCompletionExtension

variable {K : Type*} [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => maximalRealSubfield K

namespace IsDedekindDomain.HeightOneSpectrum

/-- **Local degree one at a place not fixed by conjugation.** If a finite place `u` of a CM field
`K` is not fixed by complex conjugation, then the completion `K_u` has degree `1` over the
completion of the maximal real subfield `K⁺` at the place below `u`. -/
theorem finrank_adicCompletion_eq_one_of_conjPlace_ne {u : HeightOneSpectrum (𝓞 K)}
    (hu : u.conjPlace ≠ u) :
    Module.finrank ((under (𝓞 K⁺) u).adicCompletion K⁺) (u.adicCompletion K) = 1 := by
  have : Fintype {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver (under (𝓞 K⁺) u).asIdeal} :=
    Fintype.ofFinite _
  -- `u` and `conj u` are two places above `v`, and the local degrees above `v` add up to `2`
  let d (w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver (under (𝓞 K⁺) u).asIdeal}) : ℕ :=
    Module.finrank ((under (𝓞 K⁺) u).adicCompletion K⁺) (w.val.adicCompletion K)
  have hsum : ∑ w, d w = 2 := by
    rw [(under (𝓞 K⁺) u).sum_finrank_adicCompletion_of_finite (K := K⁺) (B := 𝓞 K) (L := K),
      Algebra.IsQuadraticExtension.finrank_eq_two]
  let U : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver (under (𝓞 K⁺) u).asIdeal} :=
    ⟨u, inferInstance⟩
  let U' : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver (under (𝓞 K⁺) u).asIdeal} :=
    ⟨u.conjPlace, under_eq_iff_liesOver.1 (under_conjPlace u)⟩
  have hle : d U + d U' ≤ ∑ w, d w := Finset.add_le_sum (fun _ _ ↦ Nat.zero_le _)
    (Finset.mem_univ U) (Finset.mem_univ U') fun h ↦ hu (congrArg Subtype.val h).symm
  have hpos (w) : 0 < d w := Module.finrank_pos
  have hU := hpos U
  have hU' := hpos U'
  -- the goal is `d U = 1`, with the local abbreviations `d` and `U` unfolded
  change d U = 1
  omega

/-- At a finite place `u` of a CM field `K` not fixed by complex conjugation, the canonical map
from the completion of `K⁺` at the place below `u` to `K_u` is bijective. -/
theorem adicCompletionExtension_bijective_of_conjPlace_ne {u : HeightOneSpectrum (𝓞 K)}
    (hu : u.conjPlace ≠ u) :
    Function.Bijective ((under (𝓞 K⁺) u).adicCompletionExtension K⁺ K u) :=
  adicCompletionExtension_bijective_of_finrank_eq_one _ u
    (finrank_adicCompletion_eq_one_of_conjPlace_ne hu)

end IsDedekindDomain.HeightOneSpectrum

namespace NumberField.IsCMField

/-- **`-1` is a square at the places of `K⁺` above `2`.** Let `K` be a CM field containing a
primitive fourth and a primitive seventh root of unity. At every finite place `v` of the maximal
real subfield `K⁺` above `2`, `-1` is a square in the completion `K⁺_v`. -/
theorem isSquare_neg_one_adicCompletion_of_isPrimitiveRoot {ζ₄ ζ₇ : K}
    (h₄ : IsPrimitiveRoot ζ₄ 4) (h₇ : IsPrimitiveRoot ζ₇ 7) (v : HeightOneSpectrum (𝓞 K⁺))
    (hv : v.valuation K⁺ 2 ≠ 1) :
    IsSquare (-1 : v.adicCompletion K⁺) := by
  obtain ⟨u, rfl⟩ := under_surjective (𝓞 K⁺) (𝓞 K) v
  -- `2` lies in `u`, so `u` is not fixed by conjugation
  have h2v : (2 : 𝓞 K⁺) ∈ (under (𝓞 K⁺) u).asIdeal := by
    by_contra h
    apply hv
    rw [← map_ofNat (algebraMap (𝓞 K⁺) K⁺) 2, valuation_of_algebraMap]
    exact intValuation_eq_one_iff.2 h
  have h2u : (2 : 𝓞 K) ∈ u.asIdeal := by
    simpa only [under_asIdeal, Ideal.mem_comap, map_ofNat] using h2v
  have hne : u.conjPlace ≠ u := fun h ↦
    (two_notMem_and_exists_sub_notMem_of_isPrimitiveRoot h₄ h₇ u.asIdeal
      (map_asIdeal_of_conjPlace_eq h)).1 h2u
  -- so `K⁺_v ≅ K_u`, and the fourth root of unity of `K` gives a square root of `-1` in `K⁺_v`
  have hbij := adicCompletionExtension_bijective_of_conjPlace_ne hne
  obtain ⟨i, hi⟩ := hbij.2 (algebraMap K (u.adicCompletion K) ζ₄)
  refine ⟨i, hbij.1 ?_⟩
  have hζ : ζ₄ ^ 2 = -1 := (h₄.pow (by norm_num) (by norm_num : 4 = 2 * 2)).eq_neg_one_of_two_right
  rw [map_mul, hi, ← map_mul, ← sq, hζ, map_neg, map_neg, map_one, map_one]

end NumberField.IsCMField
