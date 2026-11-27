/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Invariant.Defs

/-!
# Integral elements fixed by a Galois group

Let `R` be integrally closed in a field `K` and let `L / K` be a Galois extension, possibly
infinite. An element of `L` lies in the image of `R` exactly when it is integral over `R` and
fixed by every `K`-automorphism of `L`. This combines the fixed-field theorem for infinite Galois
extensions with the integral closedness of `R` in `K`. For instance, an algebraic integer in an
algebraic closure of `ℚ` fixed by the absolute Galois group is a rational integer.

Mathlib's `Algebra.isInvariant_of_isGalois` records the analogous fact for a finite Galois
extension of the fraction field of an integrally closed domain, phrased through the integral
closure of that domain in `L`.

## Main results

* `TauCeti.InfiniteGalois.mem_range_algebraMap_iff_isIntegral_and_fixed`: an element of a Galois
  extension `L / K` comes from `R` if and only if it is integral over `R` and fixed by `Gal(L/K)`.
* `TauCeti.InfiniteGalois.isInvariant_integralClosure`: the elements of the integral closure of
  `R` in `L` fixed by `Gal(L/K)` are those of `R`.
* `TauCeti.InfiniteGalois.continuousSMul_integralClosure`: `Gal(L/K)` acts continuously on the
  integral closure of `R` in `L`, with the discrete topology on the latter.
-/

public section

namespace TauCeti.InfiniteGalois

variable {R K L : Type*} [CommRing R] [Field K] [Field L] [Algebra R K] [Algebra K L]
  [Algebra R L] [IsScalarTower R K L] [IsIntegrallyClosedIn R K] [IsGalois K L]

variable (K) in
/-- For `R` integrally closed in `K` and a Galois extension `L / K`, an element of `L` comes from
`R` if and only if it is integral over `R` and fixed by every `K`-automorphism of `L`. -/
theorem mem_range_algebraMap_iff_isIntegral_and_fixed (x : L) :
    x ∈ Set.range (algebraMap R L) ↔ IsIntegral R x ∧ ∀ τ : Gal(L/K), τ x = x := by
  refine ⟨?_, fun ⟨hx, hfix⟩ ↦ ?_⟩
  · rintro ⟨r, rfl⟩
    refine ⟨isIntegral_algebraMap, fun τ ↦ ?_⟩
    rw [IsScalarTower.algebraMap_apply R K L, τ.commutes]
  obtain ⟨q, rfl⟩ := (_root_.InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr hfix
  obtain ⟨r, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp <|
    (isIntegral_algHom_iff ((Algebra.ofId K L).restrictScalars R)
      (algebraMap K L).injective).mp hx
  exact ⟨r, IsScalarTower.algebraMap_apply R K L r⟩

variable (R K L) in
/-- For `R` integrally closed in `K` and a Galois extension `L / K`, the elements of the integral
closure of `R` in `L` fixed by `Gal(L/K)` are those of `R`. -/
theorem isInvariant_integralClosure : Algebra.IsInvariant R (integralClosure R L) Gal(L/K) where
  isInvariant x hx := by
    obtain ⟨r, hr⟩ := (mem_range_algebraMap_iff_isIntegral_and_fixed K (x : L)).mpr
      ⟨x.property, fun σ ↦ congrArg Subtype.val (hx σ)⟩
    exact ⟨r, Subtype.ext hr⟩

omit [IsIntegrallyClosedIn R K] [IsGalois K L] in
variable (R K L) in
/-- For an algebraic extension `L / K`, `Gal(L/K)` acts continuously on the integral closure of a
ring `R` below `K` in `L`, with the discrete topology on the latter: stabilizers of algebraic
elements are open in the Krull topology. -/
theorem continuousSMul_integralClosure [Algebra.IsAlgebraic K L]
    [TopologicalSpace (integralClosure R L)] [DiscreteTopology (integralClosure R L)] :
    ContinuousSMul Gal(L/K) (integralClosure R L) := by
  refine continuousSMul_iff_stabilizer_isOpen.2 fun x ↦ ?_
  have h : (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K)) =
      MulAction.stabilizer Gal(L/K) (x : L) :=
    Set.ext fun σ ↦ MulAction.mem_stabilizer_iff.trans <| by
      rw [Subtype.ext_iff, integralClosure.coe_smul, SetLike.mem_coe,
        MulAction.mem_stabilizer_iff]
  rw [h]
  exact stabilizer_isOpen_of_isIntegral (x : L)

end TauCeti.InfiniteGalois

end
