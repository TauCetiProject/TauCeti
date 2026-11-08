/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import TauCeti.Algebra.Polynomial.Lifts
public import TauCeti.FieldTheory.RatFunc.Map
public import TauCeti.FieldTheory.RatFunc.NumDenom

/-!
# Descent of rational functions under coefficient automorphisms

Let `S` be a set of automorphisms of a field `K`, and `F → K` a field extension whose image is
exactly the set of elements of `K` fixed by every member of `S`. Then a rational function in
`K(X)` comes from `F(X)` exactly when it is fixed by the coefficient map of every member of `S`,
and likewise a polynomial with coefficients in `K(X)` comes from one with coefficients in `F(X)`
exactly when the coefficient maps fix it. No algebraicity of `K / F` is assumed. This matters for
the automorphism groups of `ℂ`: for a subgroup `U` of `Aut(ℂ)` the extension `ℂ / ℂ ^ U` is in
general transcendental, as it is for every subgroup of finite index. A minimal polynomial over
`ℂ(X)` fixed by such a `U` thus descends to `ℂ ^ U (X)`, which is how a function field over
`ℂ(X)` is shown to be defined over a smaller field of constants.

For a Galois extension `K/F`, which may be infinite, `S` can be taken to be all of `Gal(K/F)`. In
particular, the result applies to the separable closure of an arbitrary field.

The normalized numerator and monic denominator turn descent of a rational function into descent
of their coefficients. This is the rational-function input to descent of functions on curves.

## Main results

* `TauCeti.RatFunc.mem_range_of_forall_mapRingEquiv_eq` and
  `TauCeti.RatFunc.forall_mapRingEquiv_eq_iff_mem_range`: a rational function is fixed by the
  coefficient maps of `S` exactly when it comes from `F(X)`.
* `TauCeti.RatFunc.mem_lifts_of_forall_map_mapRingEquiv_eq` and
  `TauCeti.RatFunc.forall_map_mapRingEquiv_eq_iff_mem_lifts`: the same for polynomials over
  `K(X)`.
* `RatFunc.mem_range_mapRingHom_iff_fixed`: the case of a Galois extension `K / F`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  proof of (2.2) Theorem, for the descent of a minimal polynomial along a subgroup of `Aut(ℂ)`.
-/

public section

open Polynomial
open scoped nonZeroDivisors

namespace TauCeti.RatFunc

open _root_.RatFunc

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

variable [Algebra (RatFunc F) (RatFunc K)] [IsScalarTower F (RatFunc F) (RatFunc K)]

/-- **Descent of a rational function along a set of automorphisms.** Let `S` be a set of
automorphisms of `K` whose common fixed points are the image of `F`. A rational function over `K`
fixed by the coefficient map of every `σ ∈ S` comes from `F(X)`, for any `F`-algebra map
`F(X) → K(X)` sending `X` to `X`. No algebraicity of `K / F` is needed. -/
theorem mem_range_of_forall_mapRingEquiv_eq
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X)
    {S : Set (K ≃+* K)} (hS : ∀ c : K, (∀ σ ∈ S, σ c = c) → c ∈ Set.range (algebraMap F K))
    {z : RatFunc K} (hz : ∀ σ ∈ S, mapRingEquiv σ z = z) :
    z ∈ Set.range (algebraMap (RatFunc F) (RatFunc K)) := by
  -- The coefficient maps preserve the normalized numerator and denominator, so these are fixed.
  obtain ⟨p, hp⟩ := (Polynomial.mem_lifts _).mp <|
    Polynomial.mem_lifts_of_forall_map_eq hS (p := z.num) fun σ hσ ↦ by
      simpa only [coe_mapRingEquiv, num_mapRingHom] using congr(num $(hz σ hσ))
  obtain ⟨q, hq⟩ := (Polynomial.mem_lifts _).mp <|
    Polynomial.mem_lifts_of_forall_map_eq hS (p := z.denom) fun σ hσ ↦ by
      simpa only [coe_mapRingEquiv, denom_mapRingHom] using congr(denom $(hz σ hσ))
  refine ⟨algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q, ?_⟩
  rw [map_div₀, algebraMap_ratFunc_algebraMap_polynomial hX,
    algebraMap_ratFunc_algebraMap_polynomial hX, hp, hq, num_div_denom]

/-- **Rational functions fixed by a set of automorphisms.** Let `S` be a set of automorphisms of
`K` whose common fixed points are exactly the image of `F`. A rational function over `K` is fixed
by the coefficient map of every `σ ∈ S` exactly when it comes from `F(X)`, for any `F`-algebra map
`F(X) → K(X)` sending `X` to `X`. -/
theorem forall_mapRingEquiv_eq_iff_mem_range
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X)
    {S : Set (K ≃+* K)} (hS : ∀ c : K, (∀ σ ∈ S, σ c = c) ↔ c ∈ Set.range (algebraMap F K))
    {z : RatFunc K} :
    (∀ σ ∈ S, mapRingEquiv σ z = z) ↔ z ∈ Set.range (algebraMap (RatFunc F) (RatFunc K)) := by
  refine ⟨mem_range_of_forall_mapRingEquiv_eq hX fun c ↦ (hS c).mp, ?_⟩
  rintro ⟨w, rfl⟩ σ hσ
  exact mapRingEquiv_algebraMap_ratFunc hX (fun c ↦ (hS _).mpr ⟨c, rfl⟩ σ hσ) w

/-- **Descent of a polynomial over `K(X)` along a set of automorphisms.** Let `S` be a set of
automorphisms of `K` whose common fixed points are the image of `F`. A polynomial with
coefficients in `K(X)` fixed by the coefficient map of every `σ ∈ S` comes from a polynomial with
coefficients in `F(X)`, for any `F`-algebra map `F(X) → K(X)` sending `X` to `X`. -/
theorem mem_lifts_of_forall_map_mapRingEquiv_eq
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X)
    {S : Set (K ≃+* K)} (hS : ∀ c : K, (∀ σ ∈ S, σ c = c) → c ∈ Set.range (algebraMap F K))
    {μ : (RatFunc K)[X]} (hμ : ∀ σ ∈ S, μ.map (mapRingEquiv σ : RatFunc K →+* RatFunc K) = μ) :
    μ ∈ Polynomial.lifts (algebraMap (RatFunc F) (RatFunc K)) :=
  (Polynomial.lifts_iff_coeff_lifts μ).mpr fun n ↦ mem_range_of_forall_mapRingEquiv_eq hX hS
    fun σ hσ ↦ by simpa using congr(Polynomial.coeff $(hμ σ hσ) n)

/-- **Polynomials over `K(X)` fixed by a set of automorphisms.** Let `S` be a set of automorphisms
of `K` whose common fixed points are exactly the image of `F`. A polynomial with coefficients in
`K(X)` is fixed by the coefficient map of every `σ ∈ S` exactly when it comes from a polynomial
with coefficients in `F(X)`, for any `F`-algebra map `F(X) → K(X)` sending `X` to `X`. -/
theorem forall_map_mapRingEquiv_eq_iff_mem_lifts
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X)
    {S : Set (K ≃+* K)} (hS : ∀ c : K, (∀ σ ∈ S, σ c = c) ↔ c ∈ Set.range (algebraMap F K))
    {μ : (RatFunc K)[X]} :
    (∀ σ ∈ S, μ.map (mapRingEquiv σ : RatFunc K →+* RatFunc K) = μ) ↔
      μ ∈ Polynomial.lifts (algebraMap (RatFunc F) (RatFunc K)) := by
  refine ⟨mem_lifts_of_forall_map_mapRingEquiv_eq hX fun c ↦ (hS c).mp, ?_⟩
  rintro ⟨ν, rfl⟩ σ hσ
  rw [Polynomial.coe_mapRingHom, Polynomial.map_map]
  congr 1
  exact RingHom.ext <| mapRingEquiv_algebraMap_ratFunc hX fun c ↦ (hS _).mpr ⟨c, rfl⟩ σ hσ

end TauCeti.RatFunc

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
  -- Specialize the general descent theorem to `S = Gal(K/F)` and the map induced by `F → K`.
  let : Algebra (RatFunc F) (RatFunc K) :=
    (mapRingHom (Polynomial.mapRingHom (algebraMap F K))
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (Polynomial.map_injective _ (algebraMap F K).injective))).toAlgebra
  have hpoly (p : F[X]) : algebraMap (RatFunc F) (RatFunc K) (algebraMap F[X] _ p) =
      algebraMap K[X] _ (p.map (algebraMap F K)) := by
    rw [RingHom.algebraMap_toAlgebra, coe_mapRingHom_eq_coe_map]
    simpa using map_apply_div (Polynomial.mapRingHom (algebraMap F K)) _ p 1
  have := TauCeti.RatFunc.isScalarTower_of_algebraMap_C (F := F) (K := K) fun c ↦ by
    rw [← algebraMap_C, ← algebraMap_C, hpoly, Polynomial.map_C]
  have hX : algebraMap (RatFunc F) (RatFunc K) X = X := by
    rw [← algebraMap_X, hpoly, Polynomial.map_X, algebraMap_X]
  rw [← RingHom.algebraMap_toAlgebra (mapRingHom _ _),
    ← TauCeti.RatFunc.forall_mapRingEquiv_eq_iff_mem_range hX (S := Set.range AlgEquiv.toRingEquiv)
      fun c ↦ by simpa using (InfiniteGalois.mem_range_algebraMap_iff_fixed c).symm]
  simp [TauCeti.RatFunc.coe_mapRingEquiv]

end RatFunc

end
