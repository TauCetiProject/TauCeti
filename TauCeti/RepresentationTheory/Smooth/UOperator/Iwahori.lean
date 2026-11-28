/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Dominant
public import TauCeti.RepresentationTheory.Smooth.UOperator.Basic
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Iwahori

/-!
# Multiplicativity of the `U_t` operators at pro-`p` Iwahori level

Let `K` be a valued field with valuation subring `A` and let `I₁ ⊆ GL_m(K)` be the image of the
pro-`p` Iwahori subgroup `TauCeti.iwahoriOne m A`. A diagonal matrix `diagGL t` (`t : m → Kˣ`) is
*dominant* if its diagonal entries have weakly increasing multiplicative valuations along the index
order: `i ≤ j → A.valuation (t i) ≤ A.valuation (t j)`. These form the submonoid
`A.valuation.dominantDiagSubmonoid m ⊆ GL_m(K)`.

By `ValuationSubring.exists_map_iwahoriOne_split`, `I₁` splits uniformly along all pairs of
dominant diagonal matrices. For a smooth `R`-linear representation `ρ` of `GL_m(K)` on an
`R`-module `V` over any commutative ring `R` in which the pro-order of the compact subgroup `I₁` is
invertible, specializing `Representation.uOperatorHom` yields a monoid homomorphism
`A.valuation.dominantDiagSubmonoid m →* Module.End R (V^{I₁})` sending `t` to `U_t`, and in
particular `U_{diag t} (U_{diag t'} v) = U_{diag (t * t')} v` on `V^{I₁}`.

## Main results

* `Representation.iwahoriUOperatorHom`: the monoid homomorphism from
  `A.valuation.dominantDiagSubmonoid m` to `Module.End R (V^{I₁})` sending each dominant diagonal
  matrix to its pro-`p` Iwahori `U`-operator.
* `Representation.iwahoriUOperatorHom_apply`: identifies `ρ.iwahoriUOperatorHom hI t` with
  `ρ.invariantsUOperator _ hI t`.
* `Representation.coe_iwahoriUOperatorHom_apply`: identifies the coerced value of
  `ρ.iwahoriUOperatorHom hI t` on an invariant vector with `ρ.uOperator _ hI t`.
* `Representation.uOperator_diagGL_uOperator_diagGL_apply`:
  `U_{diag t} ∘ U_{diag t'} = U_{diag (t * t')}` on `I₁`-invariants for dominant `t`, `t'`.

## References

* W. Casselman, *Introduction to the theory of admissible representations of `p`-adic reductive
  groups* (unpublished notes, 1995).
* Adapted from `src/Lib/LocalGL/Iwahori/ParahoricStructure.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC):
  `New.compactMean_diagGL_compactMean_diagGL`.
-/

public section

open Matrix

namespace Representation

variable {R K Γ₀ V : Type*} [CommRing R] [Field K] [LinearOrderedCommGroupWithZero Γ₀]
  [Valued K Γ₀] [AddCommGroup V] [Module R V]
  {m : Type*} [Fintype m] [LinearOrder m]

/-- For a smooth `R`-linear representation `ρ` of `GL_m(K)` such that the pro-`p` Iwahori
subgroup `I₁` is compact with pro-order invertible in `R`, this is the monoid homomorphism from
dominant diagonal matrices (those `diagGL t` with weakly increasing multiplicative valuations
`i ≤ j → A.valuation (t i) ≤ A.valuation (t j)`) to `R`-linear endomorphisms of `V^{I₁}`, sending
`t` to `U_t`. -/
noncomputable def iwahoriUOperatorHom (ρ : Representation R (GL m K) V) [IsSmooth ρ]
    [CompactSpace ((TauCeti.iwahoriOne m (Valued.v (R := K)).valuationSubring).map
      (GeneralLinearGroup.map (algebraMap _ K)))]
    (hI : TauCeti.HasUnitProOrder R
      ((TauCeti.iwahoriOne m (Valued.v (R := K)).valuationSubring).map
        (GeneralLinearGroup.map (algebraMap _ K)))) :
    (Valued.v (R := K)).valuationSubring.valuation.dominantDiagSubmonoid m →*
      Module.End R (invariants (ρ.comp
        ((TauCeti.iwahoriOne m (Valued.v (R := K)).valuationSubring).map
          (GeneralLinearGroup.map (algebraMap _ K))).subtype)) :=
  ρ.uOperatorHom _ hI ((Valued.v (R := K)).valuationSubring.valuation.dominantDiagSubmonoid m) (by
    intro _ hg₁ _ hg₂ c hc
    obtain ⟨t, ht, rfl⟩ :=
      ((Valued.v (R := K)).valuationSubring.valuation.mem_dominantDiagSubmonoid_iff).mp hg₁
    obtain ⟨t', ht', rfl⟩ :=
      ((Valued.v (R := K)).valuationSubring.valuation.mem_dominantDiagSubmonoid_iff).mp hg₂
    obtain ⟨a, b, hcab, ha, hb⟩ :=
      (Valued.v (R := K)).valuationSubring.exists_map_iwahoriOne_split hc
    exact ⟨a, b, hcab, ha t ht, hb t' ht'⟩)

/-- The endomorphism `ρ.iwahoriUOperatorHom hI t` on `V^{I₁}` equals `ρ.invariantsUOperator _ hI t`.
-/
@[simp]
theorem iwahoriUOperatorHom_apply (ρ : Representation R (GL m K) V) [IsSmooth ρ]
    [CompactSpace ((TauCeti.iwahoriOne m (Valued.v (R := K)).valuationSubring).map
      (GeneralLinearGroup.map (algebraMap _ K)))]
    (hI : TauCeti.HasUnitProOrder R
      ((TauCeti.iwahoriOne m (Valued.v (R := K)).valuationSubring).map
        (GeneralLinearGroup.map (algebraMap _ K))))
    (t : (Valued.v (R := K)).valuationSubring.valuation.dominantDiagSubmonoid m) :
    ρ.iwahoriUOperatorHom hI t = ρ.invariantsUOperator _ hI t := by
  simp [iwahoriUOperatorHom]

/-- Coercing the value of `ρ.iwahoriUOperatorHom hI t` on an `I₁`-invariant vector back to `V`
gives the ambient operator `ρ.uOperator _ hI t` applied to the same vector. -/
@[simp]
theorem coe_iwahoriUOperatorHom_apply (ρ : Representation R (GL m K) V) [IsSmooth ρ]
    [CompactSpace ((TauCeti.iwahoriOne m (Valued.v (R := K)).valuationSubring).map
      (GeneralLinearGroup.map (algebraMap _ K)))]
    (hI : TauCeti.HasUnitProOrder R
      ((TauCeti.iwahoriOne m (Valued.v (R := K)).valuationSubring).map
        (GeneralLinearGroup.map (algebraMap _ K))))
    (t : (Valued.v (R := K)).valuationSubring.valuation.dominantDiagSubmonoid m)
    (v : invariants (ρ.comp
      ((TauCeti.iwahoriOne m (Valued.v (R := K)).valuationSubring).map
        (GeneralLinearGroup.map (algebraMap _ K))).subtype)) :
    (ρ.iwahoriUOperatorHom hI t v : V) = ρ.uOperator _ hI t v := by
  simp [iwahoriUOperatorHom]

/-- For a smooth `R`-linear representation `ρ` of `GL_m(K)` such that the pro-`p` Iwahori
subgroup `I₁` is compact with pro-order invertible in `R`, and dominant diagonal matrices `t`, `t'`
(those with weakly increasing multiplicative valuations along `m`), the pro-`p` Iwahori
`U`-operators multiply on `I₁`-invariants:
`U_{diag t} (U_{diag t'} v) = U_{diag (t * t')} v`. -/
theorem uOperator_diagGL_uOperator_diagGL_apply (ρ : Representation R (GL m K) V) [IsSmooth ρ]
    [CompactSpace ((TauCeti.iwahoriOne m (Valued.v (R := K)).valuationSubring).map
      (GeneralLinearGroup.map (algebraMap _ K)))]
    (hI : TauCeti.HasUnitProOrder R
      ((TauCeti.iwahoriOne m (Valued.v (R := K)).valuationSubring).map
        (GeneralLinearGroup.map (algebraMap _ K))))
    {t t' : m → Kˣ}
    (ht : Monotone fun i ↦ (Valued.v (R := K)).valuationSubring.valuation (t i : K))
    (ht' : Monotone fun i ↦ (Valued.v (R := K)).valuationSubring.valuation (t' i : K))
    {v : V} (hv : v ∈ invariants (ρ.comp
      ((TauCeti.iwahoriOne m (Valued.v (R := K)).valuationSubring).map
        (GeneralLinearGroup.map (algebraMap _ K))).subtype)) :
    ρ.uOperator _ hI (TauCeti.diagGL t) (ρ.uOperator _ hI (TauCeti.diagGL t') v) =
      ρ.uOperator _ hI (TauCeti.diagGL (t * t')) v := by
  rw [map_mul TauCeti.diagGL]
  exact ρ.uOperator_uOperator_apply _ hI (fun c hc ↦ by
    obtain ⟨a, b, hcab, ha, hb⟩ :=
      (Valued.v (R := K)).valuationSubring.exists_map_iwahoriOne_split hc
    exact ⟨a, b, hcab, ha t ht, hb t' ht'⟩) hv

end Representation
