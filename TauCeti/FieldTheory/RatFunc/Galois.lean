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
-- Proof-only: `isIntegrallyClosedIn_ratFunc` shows `F(X)`-automorphisms of `K(X)` preserve `K`.
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Descent and Galois theory of rational functions under coefficient automorphisms

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

When `K / F` is algebraic, `K` and `F(X)` generate `K(X)`, so `K(X) / F(X)` inherits algebraicity,
separability, normality, and the Galois property from `K / F`. Moreover, because `K` is integrally
closed in `K(X)`, every `F(X)`-automorphism of `K(X)` preserves the constants `K`, and the
coefficient-map homomorphism `Gal(K/F) →* Gal(K(X)/F(X))` is an isomorphism of topological groups
for the Krull topologies (`TauCeti.RatFunc.mapAlgEquivContinuousMulEquiv`).

## Main definitions

* `TauCeti.RatFunc.mapAlgebra`: the `F(X)`-algebra structure on `K(X)` induced by `F → K` fixing
  `X`.
* `TauCeti.RatFunc.mapAlgEquiv`, `TauCeti.RatFunc.mapAlgEquivHom`: the `F(X)`-automorphism of
  `K(X)` induced by `σ ∈ Gal(K/F)`, and the resulting homomorphism `Gal(K/F) →* Gal(K(X)/F(X))`.
* `TauCeti.RatFunc.mapAlgEquivContinuousMulEquiv`: for algebraic `K / F`, the topological group
  isomorphism `Gal(K/F) ≃ₜ* Gal(K(X)/F(X))`.

## Main results

* `TauCeti.RatFunc.mem_range_of_forall_mapRingEquiv_eq` and
  `TauCeti.RatFunc.forall_mapRingEquiv_eq_iff_mem_range`: a rational function is fixed by the
  coefficient maps of `S` exactly when it comes from `F(X)`.
* `TauCeti.RatFunc.mem_lifts_of_forall_map_mapRingEquiv_eq` and
  `TauCeti.RatFunc.forall_map_mapRingEquiv_eq_iff_mem_lifts`: the same for polynomials over
  `K(X)`.
* `TauCeti.RatFunc.isAlgebraic_of_isAlgebraic`, `TauCeti.RatFunc.isSeparable_of_isSeparable`,
  `TauCeti.RatFunc.normal_of_normal`, `TauCeti.RatFunc.isGalois_of_isGalois`: transfer of field
  extension properties from `K / F` to `K(X) / F(X)`.
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
    fun σ hσ ↦ by simpa using congr($(hμ σ hσ).coeff n)

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

/-! ### Algebraic extensions of constants and the Krull-topological Galois isomorphism -/

/-- The `RatFunc F`-algebra structure on `RatFunc K` induced by `algebraMap F K` on coefficients
and fixing `X`. This is not a global instance because for `K = F` it would compete with
`Algebra.id (RatFunc F)`; install it locally together with `isScalarTower_mapAlgebra` and
`algebraMap_mapAlgebra_X`. -/
@[instance_reducible]
noncomputable def mapAlgebra (F K : Type*) [Field F] [Field K] [Algebra F K] :
    Algebra (RatFunc F) (RatFunc K) :=
  (mapRingHom (Polynomial.mapRingHom (algebraMap F K))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (algebraMap F K).injective))).toAlgebra

theorem algebraMap_mapAlgebra_algebraMap (F K : Type*) [Field F] [Field K] [Algebra F K]
    (p : F[X]) :
    letI := mapAlgebra F K
    algebraMap (RatFunc F) (RatFunc K) (algebraMap F[X] (RatFunc F) p) =
      algebraMap K[X] (RatFunc K) (p.map (algebraMap F K)) := by
  let _ := mapAlgebra F K
  rw [mapAlgebra, RingHom.algebraMap_toAlgebra, mapRingHom_algebraMap, Polynomial.coe_mapRingHom]

theorem isScalarTower_mapAlgebra (F K : Type*) [Field F] [Field K] [Algebra F K] :
    letI := mapAlgebra F K
    IsScalarTower F (RatFunc F) (RatFunc K) := by
  let _ := mapAlgebra F K
  refine isScalarTower_of_algebraMap_C (F := F) (K := K) fun c ↦ ?_
  rw [← algebraMap_C, ← algebraMap_C, algebraMap_mapAlgebra_algebraMap, Polynomial.map_C]

theorem algebraMap_mapAlgebra_X (F K : Type*) [Field F] [Field K] [Algebra F K] :
    letI := mapAlgebra F K
    algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X := by
  let _ := mapAlgebra F K
  rw [← algebraMap_X, algebraMap_mapAlgebra_algebraMap, Polynomial.map_X, algebraMap_X]

omit [Algebra F K] [IsScalarTower F (RatFunc F) (RatFunc K)] in
/-- For any `F(X)`-algebra structure on `K(X)` fixing `X`, the constants `K` generate `K(X)` over
`F(X)`. -/
theorem adjoin_range_algebraMap_eq_top
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) :
    IntermediateField.adjoin (RatFunc F) (Set.range (algebraMap K (RatFunc K))) = ⊤ := by
  set S := IntermediateField.adjoin (RatFunc F) (Set.range (algebraMap K (RatFunc K)))
  have hpoly (r : K[X]) : algebraMap K[X] (RatFunc K) r ∈ S := by
    induction r using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add]
      exact S.add_mem hp hq
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, algebraMap_C, algebraMap_X,
        ← algebraMap_eq_C, ← hX]
      exact S.mul_mem (IntermediateField.subset_adjoin _ _ ⟨a, rfl⟩)
        (S.pow_mem (S.algebraMap_mem _) n)
  refine eq_top_iff.mpr fun z _ ↦ ?_
  induction z using RatFunc.induction_on with
  | f p q _ => exact S.div_mem (hpoly p) (hpoly q)

/-- If `K / F` is algebraic, then `K(X) / F(X)` is algebraic. -/
theorem isAlgebraic_of_isAlgebraic
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) [Algebra.IsAlgebraic F K] :
    Algebra.IsAlgebraic (RatFunc F) (RatFunc K) := by
  have hS : ∀ x ∈ Set.range (algebraMap K (RatFunc K)), IsIntegral (RatFunc F) x := by
    rintro _ ⟨c, rfl⟩
    exact ((Algebra.IsIntegral.isIntegral (R := F) c).map
      (IsScalarTower.toAlgHom F K (RatFunc K))).tower_top
  have hadj : Algebra.IsAlgebraic (RatFunc F)
      (IntermediateField.adjoin (RatFunc F) (Set.range (algebraMap K (RatFunc K)))) :=
    IntermediateField.isAlgebraic_adjoin hS
  refine ⟨fun z ↦ ?_⟩
  have hz : z ∈ IntermediateField.adjoin (RatFunc F) (Set.range (algebraMap K (RatFunc K))) := by
    rw [adjoin_range_algebraMap_eq_top hX]
    trivial
  exact ((Algebra.IsIntegral.isIntegral (R := RatFunc F)
    (⟨z, hz⟩ : IntermediateField.adjoin (RatFunc F) (Set.range (algebraMap K (RatFunc K))))).map
      (IntermediateField.val _)).isAlgebraic

/-- If `K / F` is separable, then `K(X) / F(X)` is separable. -/
theorem isSeparable_of_isSeparable
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) [Algebra.IsSeparable F K] :
    Algebra.IsSeparable (RatFunc F) (RatFunc K) := by
  have hS : ∀ x ∈ Set.range (algebraMap K (RatFunc K)), IsSeparable (RatFunc F) x := by
    rintro _ ⟨c, rfl⟩
    have hc : IsSeparable F (algebraMap K (RatFunc K) c) := by
      change (minpoly F ((IsScalarTower.toAlgHom F K (RatFunc K)) c)).Separable
      rw [minpoly.algHom_eq _ (algebraMap K (RatFunc K)).injective]
      exact Algebra.IsSeparable.isSeparable F c
    exact hc.tower_top (RatFunc F)
  have hadj : Algebra.IsSeparable (RatFunc F)
      (IntermediateField.adjoin (RatFunc F) (Set.range (algebraMap K (RatFunc K)))) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable _ _).mpr hS
  exact AlgEquiv.Algebra.isSeparable
    ((IntermediateField.equivOfEq (adjoin_range_algebraMap_eq_top hX)).trans
      IntermediateField.topEquiv)

/-- If `K / F` is normal, then `K(X) / F(X)` is normal. -/
theorem normal_of_normal
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) [hN : Normal F K] :
    Normal (RatFunc F) (RatFunc K) := by
  have := isAlgebraic_of_isAlgebraic hX
  refine ⟨fun z ↦ IntermediateField.splits_of_mem_adjoin (RatFunc F) (RatFunc K)
    (L := RatFunc K) (S := Set.range (algebraMap K (RatFunc K))) ?_ ?_⟩
  · rintro _ ⟨c, rfl⟩
    refine ⟨Algebra.IsIntegral.isIntegral _, ?_⟩
    have hdvd : minpoly (RatFunc F) (algebraMap K (RatFunc K) c) ∣
        (minpoly F c).map (algebraMap F (RatFunc F)) := by
      refine minpoly.dvd (RatFunc F) _ ?_
      rw [aeval_map_algebraMap, aeval_algebraMap_apply, minpoly.aeval, map_zero]
    have hsp : (((minpoly F c).map (algebraMap F (RatFunc F))).map
        (algebraMap (RatFunc F) (RatFunc K))).Splits := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq F (RatFunc F) (RatFunc K),
        IsScalarTower.algebraMap_eq F K (RatFunc K), ← Polynomial.map_map]
      exact (hN.splits c).map (algebraMap K (RatFunc K))
    exact Polynomial.Splits.of_dvd hsp
      (Polynomial.map_monic_ne_zero ((minpoly.monic (hN.isIntegral c)).map _))
      (Polynomial.map_dvd _ hdvd)
  · rw [adjoin_range_algebraMap_eq_top hX]
    trivial

/-- If `K / F` is Galois, then `K(X) / F(X)` is Galois. -/
theorem isGalois_of_isGalois
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) [IsGalois F K] :
    IsGalois (RatFunc F) (RatFunc K) :=
  letI := isSeparable_of_isSeparable hX
  letI := normal_of_normal hX
  ⟨⟩

/-- The `F(X)`-automorphism of `K(X)` induced by `σ ∈ Gal(K/F)` on coefficients, fixing `X`. -/
noncomputable def mapAlgEquiv
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) (σ : Gal(K/F)) :
    Gal(RatFunc K/RatFunc F) :=
  AlgEquiv.ofRingEquiv (f := mapRingEquiv σ.toRingEquiv)
    (mapRingEquiv_algebraMap_ratFunc hX σ.commutes)

@[simp]
theorem coe_mapAlgEquiv
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) (σ : Gal(K/F)) :
    ⇑(mapAlgEquiv hX σ) = mapRingEquiv σ.toRingEquiv :=
  (rfl)

@[simp]
theorem toRingEquiv_mapAlgEquiv
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) (σ : Gal(K/F)) :
    (mapAlgEquiv hX σ).toRingEquiv = mapRingEquiv σ.toRingEquiv :=
  (rfl)

@[simp]
theorem mapAlgEquiv_X
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) (σ : Gal(K/F)) :
    mapAlgEquiv hX σ RatFunc.X = RatFunc.X :=
  mapRingEquiv_X σ.toRingEquiv

@[simp]
theorem mapAlgEquiv_C
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) (σ : Gal(K/F)) (c : K) :
    mapAlgEquiv hX σ (RatFunc.C c) = RatFunc.C (σ c) :=
  mapRingEquiv_C σ.toRingEquiv c

theorem mapAlgEquiv_algebraMap_const
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) (σ : Gal(K/F)) (c : K) :
    mapAlgEquiv hX σ (algebraMap K (RatFunc K) c) = algebraMap K (RatFunc K) (σ c) :=
  mapRingEquiv_algebraMap_const σ.toRingEquiv c

/-- Coefficient automorphisms as a group homomorphism `Gal(K/F) →* Gal(K(X)/F(X))`. -/
noncomputable def mapAlgEquivHom
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) :
    Gal(K/F) →* Gal(RatFunc K/RatFunc F) where
  toFun := mapAlgEquiv hX
  map_one' := AlgEquiv.ext fun z ↦ by
    change mapRingEquiv (RingEquiv.refl K) z = z
    simp
  map_mul' σ τ := AlgEquiv.ext fun z ↦ by
    change mapRingEquiv (τ.toRingEquiv.trans σ.toRingEquiv) z =
      mapRingEquiv σ.toRingEquiv (mapRingEquiv τ.toRingEquiv z)
    rw [mapRingEquiv_trans]
    rfl

@[simp]
theorem mapAlgEquivHom_apply
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) (σ : Gal(K/F)) :
    mapAlgEquivHom hX σ = mapAlgEquiv hX σ :=
  (rfl)

@[simp]
theorem mapAlgEquiv_symm
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) (σ : Gal(K/F)) :
    (mapAlgEquiv hX σ).symm = mapAlgEquiv hX σ.symm :=
  (map_inv (mapAlgEquivHom hX) σ).symm

theorem mapAlgEquivHom_injective
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) :
    Function.Injective (mapAlgEquivHom hX) := fun σ τ h ↦
  AlgEquiv.ext fun c ↦ (algebraMap K (RatFunc K)).injective <| by
    simpa only [mapAlgEquivHom_apply, mapAlgEquiv_algebraMap_const] using
      congr($(h) (algebraMap K (RatFunc K) c))

section IsAlgebraic

variable [Algebra.IsAlgebraic F K]

/-- When `K / F` is algebraic, every `F(X)`-automorphism of `K(X)` comes from an `F`-automorphism
of `K`, because `K` is integrally closed in `K(X)`. -/
theorem mapAlgEquivHom_surjective
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) :
    Function.Surjective (mapAlgEquivHom hX) := by
  have hmem (ψ : Gal(RatFunc K/RatFunc F)) (c : K) :
      ∃ d : K, algebraMap K (RatFunc K) d = ψ (algebraMap K (RatFunc K) c) := by
    have hintF : IsIntegral F (algebraMap K (RatFunc K) c) :=
      (Algebra.IsIntegral.isIntegral (R := F) c).map (IsScalarTower.toAlgHom F K (RatFunc K))
    have hint : IsIntegral K (ψ (algebraMap K (RatFunc K) c)) :=
      (hintF.map (ψ.restrictScalars F)).tower_top
    exact TauCeti.isIntegrallyClosedIn_ratFunc.isIntegral_iff.mp hint
  let f (ψ : Gal(RatFunc K/RatFunc F)) (c : K) : K := (hmem ψ c).choose
  have hf (ψ : Gal(RatFunc K/RatFunc F)) (c : K) :
      algebraMap K (RatFunc K) (f ψ c) = ψ (algebraMap K (RatFunc K) c) :=
    (hmem ψ c).choose_spec
  intro ψ
  have hinj := (algebraMap K (RatFunc K)).injective
  let σ : Gal(K/F) :=
    { toFun := f ψ
      invFun := f ψ.symm
      left_inv := fun c ↦ hinj <| by rw [hf, hf, AlgEquiv.symm_apply_apply]
      right_inv := fun c ↦ hinj <| by rw [hf, hf, AlgEquiv.apply_symm_apply]
      map_mul' := fun a b ↦ hinj <| by rw [hf, map_mul, map_mul, map_mul, hf, hf]
      map_add' := fun a b ↦ hinj <| by rw [hf, map_add, map_add, map_add, hf, hf]
      commutes' := fun r ↦ hinj <| by
        rw [hf, ← IsScalarTower.algebraMap_apply F K (RatFunc K),
          IsScalarTower.algebraMap_apply F (RatFunc F) (RatFunc K), AlgEquiv.commutes] }
  refine ⟨σ, AlgEquiv.ext ?_⟩
  have hpoly :
      (mapAlgEquivHom hX σ : RatFunc K →+* RatFunc K).comp (algebraMap K[X] (RatFunc K)) =
        (ψ : RatFunc K →+* RatFunc K).comp (algebraMap K[X] (RatFunc K)) := by
    refine Polynomial.ringHom_ext' ?_ ?_
    · ext c
      simp only [RingHom.comp_apply, RingHom.coe_coe, algebraMap_C, ← algebraMap_eq_C,
        mapAlgEquivHom_apply, mapAlgEquiv_algebraMap_const]
      exact hf ψ c
    · simp only [RingHom.comp_apply, RingHom.coe_coe, algebraMap_X, mapAlgEquivHom_apply,
        mapAlgEquiv_X]
      rw [← hX, AlgEquiv.commutes]
  have hhom : (mapAlgEquivHom hX σ : RatFunc K →+* RatFunc K) = (ψ : RatFunc K →+* RatFunc K) :=
    IsFractionRing.ringHom_ext (A := K[X]) fun p ↦ congr($hpoly p)
  exact fun z ↦ congr($hhom z)

theorem mapAlgEquivHom_bijective
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) :
    Function.Bijective (mapAlgEquivHom hX) :=
  ⟨mapAlgEquivHom_injective hX, mapAlgEquivHom_surjective hX⟩

private noncomputable def mapAlgEquivMulEquiv
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) :
    Gal(K/F) ≃* Gal(RatFunc K/RatFunc F) :=
  MulEquiv.ofBijective (mapAlgEquivHom hX) (mapAlgEquivHom_bijective hX)

/-- For algebraic `K / F`, the coefficient-map homomorphism `Gal(K/F) →* Gal(K(X)/F(X))` is
continuous for the Krull topologies. -/
theorem continuous_mapAlgEquivHom
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) :
    Continuous (mapAlgEquivHom hX) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro U hU
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨E, _, hEU⟩ := hU
  rw [krullTopology_mem_nhds_one_iff]
  classical
  let b := Module.finBasis (RatFunc F) E
  let S : Finset K := Finset.univ.biUnion fun i ↦
    (Finset.range (((b i : RatFunc K).num).natDegree + 1)).image ((b i : RatFunc K).num.coeff) ∪
      (Finset.range (((b i : RatFunc K).denom).natDegree + 1)).image
        ((b i : RatFunc K).denom.coeff)
  let E₀ := IntermediateField.adjoin F (S : Set K)
  refine ⟨E₀, inferInstance, fun σ hσ ↦ hEU ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  have hbi (i : Fin (Module.finrank (RatFunc F) E)) :
      mapAlgEquivHom hX σ (b i : RatFunc K) = b i := by
    have hnum : ((b i : RatFunc K).num).map σ.toRingHom = (b i : RatFunc K).num := by
      ext m
      rw [Polynomial.coeff_map]
      rcases le_or_gt m ((b i : RatFunc K).num).natDegree with hm | hm
      · refine hσ _ (IntermediateField.subset_adjoin F (S : Set K) ?_)
        exact Finset.mem_coe.mpr <| Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
          Finset.mem_union_left _ <| Finset.mem_image.mpr
            ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le hm), rfl⟩⟩
      · simp [Polynomial.coeff_eq_zero_of_natDegree_lt hm]
    have hden : ((b i : RatFunc K).denom).map σ.toRingHom = (b i : RatFunc K).denom := by
      ext m
      rw [Polynomial.coeff_map]
      rcases le_or_gt m ((b i : RatFunc K).denom).natDegree with hm | hm
      · refine hσ _ (IntermediateField.subset_adjoin F (S : Set K) ?_)
        exact Finset.mem_coe.mpr <| Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
          Finset.mem_union_right _ <| Finset.mem_image.mpr
            ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le hm), rfl⟩⟩
      · simp [Polynomial.coeff_eq_zero_of_natDegree_lt hm]
    conv_lhs => rw [← num_div_denom (b i : RatFunc K)]
    rw [mapAlgEquivHom_apply, coe_mapAlgEquiv, map_div₀, mapRingEquiv_algebraMap,
      mapRingEquiv_algebraMap, show ((b i : RatFunc K).num.map σ.toRingEquiv) =
        (b i : RatFunc K).num.map σ.toRingHom from rfl,
      show ((b i : RatFunc K).denom.map σ.toRingEquiv) =
        (b i : RatFunc K).denom.map σ.toRingHom from rfl,
      hnum, hden, num_div_denom]
  intro y hy
  have hy' := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩).symm
  push_cast at hy'
  rw [hy', map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, hbi]

private theorem continuous_mapAlgEquivMulEquiv_symm
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) :
    Continuous (mapAlgEquivMulEquiv hX).symm := by
  have := isAlgebraic_of_isAlgebraic hX
  apply continuous_of_continuousAt_one (mapAlgEquivMulEquiv hX).symm.toMonoidHom
    (continuousAt_def.mpr _)
  intro U hU
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨E₀, _, hE₀U⟩ := hU
  rw [krullTopology_mem_nhds_one_iff]
  let b₀ := Module.finBasis F E₀
  let S : Set (RatFunc K) := Set.range fun i ↦ algebraMap K (RatFunc K) (b₀ i)
  let E := IntermediateField.adjoin (RatFunc F) S
  refine ⟨E, inferInstance, fun ψ hψ ↦ hE₀U ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hψ ⊢
  set σ := (mapAlgEquivMulEquiv hX).symm ψ
  have hσψ : mapAlgEquivHom hX σ = ψ := (mapAlgEquivMulEquiv hX).apply_symm_apply ψ
  have hbi (i : Fin (Module.finrank F E₀)) : σ (b₀ i : K) = b₀ i := by
    apply (algebraMap K (RatFunc K)).injective
    rw [← mapAlgEquiv_algebraMap_const hX, ← mapAlgEquivHom_apply, hσψ]
    exact hψ _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  intro c hc
  have hc' := congrArg Subtype.val (b₀.sum_repr ⟨c, hc⟩).symm
  push_cast at hc'
  change σ c = c
  rw [hc', map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, hbi]

/-- **Galois group of a rational function field over an algebraic extension of constants**: for any
algebraic extension `K / F` and any `F`-algebra map `F(X) → K(X)` fixing `X`, coefficientwise
action is an isomorphism of topological groups `Gal(K/F) ≃ₜ* Gal(K(X)/F(X))` for the Krull
topologies. -/
noncomputable def mapAlgEquivContinuousMulEquiv
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) :
    Gal(K/F) ≃ₜ* Gal(RatFunc K/RatFunc F) where
  __ := mapAlgEquivMulEquiv hX
  continuous_toFun := continuous_mapAlgEquivHom hX
  continuous_invFun := continuous_mapAlgEquivMulEquiv_symm hX

@[simp]
theorem mapAlgEquivContinuousMulEquiv_apply
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X) (σ : Gal(K/F)) :
    mapAlgEquivContinuousMulEquiv hX σ = mapAlgEquiv hX σ :=
  (rfl)

theorem mapAlgEquivContinuousMulEquiv_symm_algebraMap_const
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X)
    (ψ : Gal(RatFunc K/RatFunc F)) (c : K) :
    algebraMap K (RatFunc K) ((mapAlgEquivContinuousMulEquiv hX).symm ψ c) =
      ψ (algebraMap K (RatFunc K) c) := by
  have h := (mapAlgEquivContinuousMulEquiv hX).apply_symm_apply ψ
  exact (mapAlgEquiv_algebraMap_const hX _ c).symm.trans congr($(h) (algebraMap K (RatFunc K) c))

@[simp]
theorem mapAlgEquivContinuousMulEquiv_symm_C
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X)
    (ψ : Gal(RatFunc K/RatFunc F)) (c : K) :
    RatFunc.C ((mapAlgEquivContinuousMulEquiv hX).symm ψ c) = ψ (RatFunc.C c) := by
  simpa only [algebraMap_eq_C] using mapAlgEquivContinuousMulEquiv_symm_algebraMap_const hX ψ c

end IsAlgebraic

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
  let := TauCeti.RatFunc.mapAlgebra F K
  have := TauCeti.RatFunc.isScalarTower_mapAlgebra F K
  have hX := TauCeti.RatFunc.algebraMap_mapAlgebra_X F K
  rw [← show algebraMap (RatFunc F) (RatFunc K) = mapRingHom _ _ from rfl,
    ← TauCeti.RatFunc.forall_mapRingEquiv_eq_iff_mem_range hX (S := Set.range AlgEquiv.toRingEquiv)
      fun c ↦ by simpa using (InfiniteGalois.mem_range_algebraMap_iff_fixed c).symm]
  simp [TauCeti.RatFunc.coe_mapRingEquiv]

end RatFunc

end
