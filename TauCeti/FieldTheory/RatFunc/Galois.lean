/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.FieldTheory.Galois.Infinite
public import TauCeti.FieldTheory.RatFunc.NumDenom

/-!
# Descent of rational functions under coefficient automorphisms

For a Galois extension `K/F`, a rational function in `K(X)` comes from `F(X)` exactly when it is
fixed by every coefficient automorphism in `Gal(K/F)`. The extension may be infinite. In
particular, the result applies to the separable closure of an arbitrary field.

The normalized numerator and monic denominator turn descent of a rational function into descent
of their coefficients. This is the rational-function input to descent of functions on curves.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
-/

public section

open Polynomial
open scoped nonZeroDivisors

namespace RatFunc

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [IsGalois F K]

/-- A rational function over a Galois extension comes from the ground field exactly when all
coefficient automorphisms fix it. No finite-dimensionality assumption is needed. -/
theorem mem_range_mapRingHom_iff_fixed (z : RatFunc K) :
    z ∈ Set.range (mapRingHom (Polynomial.mapRingHom (algebraMap F K))
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (Polynomial.map_injective _ (algebraMap F K).injective))) ↔
      ∀ σ : K ≃ₐ[F] K,
        mapRingHom (Polynomial.mapRingHom σ.toRingHom)
          (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
            (Polynomial.map_injective _ σ.injective)) z = z := by
  constructor
  · rintro ⟨w, rfl⟩ σ
    have fixed (p : F[X]) : (p.map (algebraMap F K)).map σ.toRingHom =
        p.map (algebraMap F K) := by
      ext n
      simp
    rw [coe_mapRingHom_eq_coe_map, map_apply]
    simp only [Polynomial.coe_mapRingHom, num_mapRingHom, denom_mapRingHom]
    rw [fixed, fixed]
    simpa only [num_mapRingHom, denom_mapRingHom] using num_div_denom
      (mapRingHom (Polynomial.mapRingHom (algebraMap F K))
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (Polynomial.map_injective _ (algebraMap F K).injective)) w)
  · intro hz
    have lift (p : K[X])
        (hp : ∀ σ : K ≃ₐ[F] K, p.map σ.toRingHom = p) :
        ∃ q : F[X], q.map (algebraMap F K) = p := by
      apply (Polynomial.mem_lifts p).mp
      apply (Polynomial.lifts_iff_coeff_lifts p).mpr
      intro n
      apply (InfiniteGalois.mem_range_algebraMap_iff_fixed (p.coeff n)).mpr
      intro σ
      simpa using congrArg (fun q : K[X] ↦ q.coeff n) (hp σ)
    obtain ⟨p, hp⟩ := lift z.num fun σ ↦ by
      simpa only [num_mapRingHom] using congrArg num (hz σ)
    obtain ⟨q, hq⟩ := lift z.denom fun σ ↦ by
      simpa only [denom_mapRingHom] using congrArg denom (hz σ)
    refine ⟨algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q, ?_⟩
    rw [coe_mapRingHom_eq_coe_map, map_apply_div]
    simpa only [Polynomial.coe_mapRingHom, hp, hq] using num_div_denom z

end RatFunc

end
