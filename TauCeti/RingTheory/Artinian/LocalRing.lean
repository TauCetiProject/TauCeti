/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Artinian modules over commutative local rings

Let `R` be a commutative local ring with maximal ideal `𝔪`. Every element `x` of an Artinian
`R`-module `M` is killed by a power of `𝔪`, so `M` equals its maximal-ideal primary component
(`TauCeti.primaryComponent_maximalIdeal_eq_top_of_isArtinian`). Indeed, `R ⧸ Ann(x)` embeds
`R`-linearly into `M`, hence is a commutative Artinian ring whose Jacobson radical is nilpotent;
since `R` is local, `𝔪` maps into that Jacobson radical, so a power of `𝔪` annihilates `x`.
No Noetherian hypothesis on `R` is needed, and `M` carries the canonical action of the `𝔪`-adic
completion `R̂`.

## Main results

* `TauCeti.primaryComponent_maximalIdeal_eq_top_of_isArtinian`: over a local ring, every Artinian
  module is maximal-ideal-power torsion.
* `TauCeti.mem_primaryComponent_maximalIdeal_of_isArtinian`: every element of an Artinian module
  over a local ring is annihilated by a power of the maximal ideal.

## References

* [Stacks Project, Section 47.7](https://stacks.math.columbia.edu/tag/08Z1) and
  [Proposition 47.7.8](https://stacks.math.columbia.edu/tag/08Z9).
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

noncomputable section

open IsLocalRing Submodule

namespace TauCeti

universe u w

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {M : Type w} [AddCommGroup M] [Module R M] [IsArtinian R M]

/-- Every element of an Artinian module over a local ring is annihilated by a power of the
maximal ideal. -/
theorem mem_primaryComponent_maximalIdeal_of_isArtinian (x : M) :
    x ∈ (maximalIdeal R).primaryComponent M := by
  let f := LinearMap.toSpanSingleton R M x
  let I : Ideal R := LinearMap.ker f
  have : IsArtinian R (R ⧸ I) :=
    isArtinian_of_injective ((LinearMap.range f).subtype.comp f.quotKerEquivRange.toLinearMap)
      (Subtype.val_injective.comp f.quotKerEquivRange.injective)
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_tower R ‹IsArtinian R (R ⧸ I)›
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson (R ⧸ I)
  have hle : (maximalIdeal R).map (Ideal.Quotient.mk I) ≤ Ring.jacobson (R ⧸ I) := by
    rw [Ideal.map_le_iff_le_comap, ← ringJacobson_eq_maximalIdeal]
    exact Ring.le_comap_jacobson (Ideal.Quotient.mk I)
  refine ((maximalIdeal R).primaryComponent_mem M x).mpr ⟨n, ?_⟩
  rw [mem_torsionBySet_iff]
  rintro ⟨r, hr⟩
  have hr' : Ideal.Quotient.mk I r ∈ Ring.jacobson (R ⧸ I) ^ n :=
    pow_le_pow_left' hle n
      (Ideal.map_pow (Ideal.Quotient.mk I) (maximalIdeal R) n ▸ Ideal.mem_map_of_mem _ hr)
  rw [hn, Ideal.zero_eq_bot, mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hr'
  simpa [I, f] using hr'

variable (R M) in
/-- Over a local ring, every Artinian module equals its maximal-ideal primary component: each
element is annihilated by some power of the maximal ideal. -/
theorem primaryComponent_maximalIdeal_eq_top_of_isArtinian :
    (maximalIdeal R).primaryComponent M = ⊤ :=
  eq_top_iff.mpr fun x _ ↦ mem_primaryComponent_maximalIdeal_of_isArtinian x

end TauCeti
