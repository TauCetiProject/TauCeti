/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.WeightedEval.UniversalProperty
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Polynomial
public import TauCeti.Topology.Algebra.Nonarchimedean.LinearTopology

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded

/-!
# The universal property of Gauss-normed Tate algebras at power-bounded arguments

Let `R` be an ultrametric normed commutative ring and `S` a complete Hausdorff nonarchimedean
commutative ring, for instance a complete ultrametric normed ring. Let `φ : R →+* S` be
continuous, and let `b₁, …, bₖ ∈ S` be power-bounded. Then there is exactly one continuous ring
homomorphism `ψ : R⟨X₁, …, Xₖ⟩ → S` on the Gauss-normed ring of unit-radius restricted series
with `ψ (C r) = φ r` and `ψ (Xᵢ) = bᵢ`.

This is Wedhorn's Proposition 5.50,
`TauCeti.Huber.existsUnique_continuous_ringHom_weightedRestrictedSubring`, carried along the
identity comparison `TauCeti.Huber.restrictedMvPowerSeriesGaussEquiv` between the Huber model and
the Gauss-normed model, which is continuous in both directions. Unlike
`MvPowerSeries.restrictedEval₂`, neither `‖φ r‖ ≤ ‖r‖` nor `‖bᵢ‖ ≤ 1` is assumed. Power-boundedness
is `TauCeti.Huber.IsPowerBounded` for the topology of `S`: for a normed `S` the powers of `bᵢ`
stay bounded, while `bᵢ` itself may have norm larger than one. When `S` is linearly topologised
(`IsLinearTopology S S`), every subset is bounded, so arbitrary `b₁, …, bₖ ∈ S` are admissible.

## Main definitions

* `TauCeti.MvPowerSeries.restrictedLift`: the continuous ring homomorphism
  `R⟨X₁, …, Xₖ⟩ →+* S` extending `φ` and sending `Xᵢ` to `bᵢ`.
* `TauCeti.MvPowerSeries.restrictedLiftLinear` and `TauCeti.MvPowerSeries.restrictedAlgLiftLinear`:
  evaluation into a complete Hausdorff linearly topologised ring or `R`-algebra at arbitrary
  `b₁, …, bₖ ∈ S`.
* `TauCeti.MvPowerSeries.restrictedRename`: for complete `R` and `f : Fin m → Fin k`, the
  `R`-algebra map `R⟨X₁, …, Xₘ⟩ →ₐ[R] R⟨X₁, …, Xₖ⟩` sending `Xᵢ` to `X_{f i}`.

## Main results

* `TauCeti.MvPowerSeries.isPowerBounded_X`: each variable `Xᵢ` is power-bounded.
* `TauCeti.MvPowerSeries.isRestricted_subring_ringHom_ext_of_continuous`: continuous ring
  homomorphisms out of `R⟨X₁, …, Xₖ⟩` agreeing on constants and variables are equal.
* `TauCeti.MvPowerSeries.restrictedLift_unique` and
  `TauCeti.MvPowerSeries.existsUnique_continuous_ringHom_isRestricted_subring`: the universal
  property at power-bounded arguments.
* `TauCeti.MvPowerSeries.restrictedLift_restrictedMap` and
  `TauCeti.MvPowerSeries.map_restrictedLift`: naturality in source coefficients and target rings.
* `TauCeti.MvPowerSeries.existsUnique_continuous_ringHom_isRestricted_subring_of_isLinearTopology`
  and
  `TauCeti.MvPowerSeries.existsUnique_continuous_algHom_isRestricted_subring_of_isLinearTopology`:
  the universal property into linearly topologised targets with no bound on `b`.
* `TauCeti.MvPowerSeries.restrictedRename_id`, `TauCeti.MvPowerSeries.restrictedRename_comp`:
  renaming along the identity is the identity, and successive renamings compose.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Proposition 5.50.
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.5.3.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §1.4.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries TauCeti.Huber

variable {k : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- **Continuous ring homomorphisms out of `R⟨X₁, …, Xₖ⟩` are determined by the constants and the
variables.** Two continuous ring homomorphisms into a Hausdorff ring that agree on every constant
and on every `Xᵢ` are equal. -/
theorem isRestricted_subring_ringHom_ext_of_continuous {T : Type*} [Semiring T]
    [TopologicalSpace T] [T2Space T]
    {ψ₁ ψ₂ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* T} (h₁ : Continuous ψ₁)
    (h₂ : Continuous ψ₂) (hC : ∀ r, ψ₁ (algebraMap R _ r) = ψ₂ (algebraMap R _ r))
    (hX : ∀ i, ψ₁ ⟨X i, isRestricted_X _ i⟩ = ψ₂ ⟨X i, isRestricted_X _ i⟩) : ψ₁ = ψ₂ := by
  let e := restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)
  have h := weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
    (f := ψ₁.comp e.toRingHom) (g := ψ₂.comp e.toRingHom)
    (h₁.comp continuous_restrictedMvPowerSeriesGaussEquiv)
    (h₂.comp continuous_restrictedMvPowerSeriesGaussEquiv)
    (fun r ↦ by simp [e, hC])
    (fun i ↦ by simp [e, hX])
  ext f
  simpa using congr($h (e.symm f))

/-- Each variable `Xᵢ` of the Gauss-normed algebra `R⟨X₁, …, Xₖ⟩` is power-bounded. -/
theorem isPowerBounded_X (i : Fin k) :
    IsPowerBounded
      (⟨X i, isRestricted_X _ i⟩ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) := by
  -- Transport weighted-variable power-boundedness along the Gauss comparison.
  rw [← restrictedMvPowerSeriesGaussEquiv_weightedX, isPowerBounded_ringEquiv_iff _
    continuous_restrictedMvPowerSeriesGaussEquiv continuous_restrictedMvPowerSeriesGaussEquiv_symm]
  exact isPowerBounded_weightedX_one_weight i

section PowerBounded

variable {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [NonarchimedeanRing S]
  [CompleteSpace S] [T3Space S] {φ : R →+* S} (hφ : Continuous φ) {b : Fin k → S}
  (hb : ∀ i, IsPowerBounded (b i))

/-- **The extension of `φ` to `R⟨X₁, …, Xₖ⟩` sending each `Xᵢ` to `bᵢ`**, for a continuous ring
homomorphism `φ : R →+* S` into a complete Hausdorff nonarchimedean ring and power-bounded
`b₁, …, bₖ ∈ S`. It is Wedhorn's evaluation homomorphism `TauCeti.Huber.weightedEvalHom`, carried
along the Gauss comparison `TauCeti.Huber.restrictedMvPowerSeriesGaussEquiv`. -/
noncomputable def restrictedLift : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* S :=
  (weightedEvalHom isWeightFamily_one_weight hφ.continuousAt
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded φ b).mpr hb)).comp
    (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm.toRingHom

/-- `restrictedLift` computes `TauCeti.Huber.weightedEval` on the underlying formal series. -/
theorem restrictedLift_apply (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    restrictedLift hφ hb f = weightedEval φ b f := by
  simp [restrictedLift]

/-- The monomial series `weightedEvalTerm φ b f` sums to `restrictedLift hφ hb f`. -/
theorem hasSum_restrictedLift (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    HasSum (weightedEvalTerm φ b f) (restrictedLift hφ hb f) := by
  rw [restrictedLift_apply]
  have hf := mem_weightedRestrictedSubring.mp
    ((restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm f).2
  simpa only [coe_restrictedMvPowerSeriesGaussEquiv_symm] using
    hasSum_weightedEval hφ.continuousAt
      ((isWeightBounded_one_weight_iff_forall_isPowerBounded φ b).mpr hb) hf

/-- `restrictedLift` is continuous. -/
theorem continuous_restrictedLift : Continuous (restrictedLift hφ hb) :=
  (continuous_weightedEvalHom _ _ _).comp continuous_restrictedMvPowerSeriesGaussEquiv_symm

/-- `restrictedLift` extends `φ` on constants. -/
@[simp]
theorem restrictedLift_algebraMap (r : R) : restrictedLift hφ hb (algebraMap R _ r) = φ r := by
  simp [restrictedLift, ← restrictedMvPowerSeriesGaussEquiv_weightedC]

/-- `restrictedLift` sends each variable `Xᵢ` to `bᵢ`. -/
@[simp]
theorem restrictedLift_X (i : Fin k) : restrictedLift hφ hb ⟨X i, isRestricted_X _ i⟩ = b i := by
  simp [restrictedLift, ← restrictedMvPowerSeriesGaussEquiv_weightedX]

/-- On polynomials, `restrictedLift` agrees with `MvPolynomial.eval₂`. -/
@[simp]
theorem restrictedLift_polynomialToRestricted (p : MvPolynomial (Fin k) R) :
    restrictedLift hφ hb (polynomialToRestricted (fun _ : Fin k ↦ 1) p) =
      MvPolynomial.eval₂ φ b p := by
  rw [← restrictedMvPowerSeriesGaussEquiv_weightedPolynomialHom, restrictedLift,
    RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply, weightedEvalHom_weightedPolynomialHom]

/-- **Source base-change naturality**: evaluating after `restrictedMap θ` along a bounded
coefficient homomorphism `θ : T →+* R` agrees with evaluating along `φ.comp θ`. -/
theorem restrictedLift_restrictedMap {T : Type*} [NormedCommRing T] [IsUltrametricDist T]
    {θ : T →+* R} {C : ℝ} (hθ : ∀ t, ‖θ t‖ ≤ C * ‖t‖)
    (hφθ : Continuous (φ.comp θ)) (hb' : ∀ i, IsPowerBounded (b i))
    (f : IsRestricted.subring (R := T) (fun _ : Fin k ↦ 1)) :
    restrictedLift hφ hb (restrictedMap θ hθ f) = restrictedLift hφθ hb' f := by
  simp only [restrictedLift_apply, coe_restrictedMap, weightedEval_def, weightedEvalTerm_def,
    coeff_map, RingHom.comp_apply]

/-- **Target naturality**: applying a continuous ring homomorphism `ψ : S →+* D` into a complete
Hausdorff nonarchimedean ring to `restrictedLift` agrees with `restrictedLift` along `ψ.comp φ` at
`ψ ∘ b`. -/
theorem map_restrictedLift {D : Type*} [CommRing D] [UniformSpace D] [IsUniformAddGroup D]
    [NonarchimedeanRing D] [CompleteSpace D] [T3Space D] {ψ : S →+* D} (hψ : Continuous ψ)
    (hψφ : Continuous (ψ.comp φ)) (hb' : ∀ i, IsPowerBounded (ψ (b i)))
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    ψ (restrictedLift hφ hb f) = restrictedLift (b := ψ ∘ b) hψφ hb' f := by
  simp only [restrictedLift, RingHom.comp_apply]
  exact map_weightedEvalHom hψ isWeightFamily_one_weight hφ.continuousAt _ hψφ.continuousAt _ _

/-- `restrictedLift` is the only continuous ring homomorphism extending `φ` on constants and
sending each `Xᵢ` to `bᵢ`. -/
theorem restrictedLift_unique {ψ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* S}
    (hψ : Continuous ψ) (hC : ∀ r, ψ (algebraMap R _ r) = φ r)
    (hX : ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i) : ψ = restrictedLift hφ hb :=
  isRestricted_subring_ringHom_ext_of_continuous hψ (continuous_restrictedLift hφ hb)
    (fun r ↦ by rw [hC, restrictedLift_algebraMap]) (fun i ↦ by rw [hX, restrictedLift_X])

include hφ hb in
/-- **The universal property of `R⟨X₁, …, Xₖ⟩` at power-bounded arguments.** For a continuous
ring homomorphism `φ : R →+* S` into a complete Hausdorff nonarchimedean ring and power-bounded
`b₁, …, bₖ ∈ S`, there is exactly one continuous ring homomorphism out of the Gauss-normed
unit-radius restricted series that extends `φ` on constants and sends each `Xᵢ` to `bᵢ`, namely
`TauCeti.MvPowerSeries.restrictedLift`. -/
theorem existsUnique_continuous_ringHom_isRestricted_subring :
    ∃! ψ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* S,
      Continuous ψ ∧ (∀ r, ψ (algebraMap R _ r) = φ r) ∧
        ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i :=
  ⟨restrictedLift hφ hb, ⟨continuous_restrictedLift hφ hb, restrictedLift_algebraMap hφ hb,
    restrictedLift_X hφ hb⟩, fun _ ⟨hψ, hC, hX⟩ ↦ restrictedLift_unique hφ hb hψ hC hX⟩

end PowerBounded

section LinearTopology

variable {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
  [IsLinearTopology S S] [CompleteSpace S] [T2Space S]

/-- **Evaluation of `R⟨X₁, …, Xₖ⟩` into a complete Hausdorff linearly topologised ring**, for a
continuous coefficient homomorphism `φ : R →+* S` and *arbitrary* values `b₁, …, bₖ ∈ S`. -/
noncomputable def restrictedLiftLinear {φ : R →+* S} (hφ : Continuous φ) (b : Fin k → S) :
    IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* S :=
  letI := IsLinearTopology.isTopologicalRing (R := S)
  letI := IsLinearTopology.nonarchimedeanRing S
  restrictedLift (b := b) hφ
    (fun i ↦ (isPowerBounded_iff (a := b i)).mpr (isBounded_of_isLinearTopology _))

/-- `restrictedLiftLinear` is `restrictedLift` with the linear-topology power-boundedness
witness. -/
theorem restrictedLiftLinear_eq_restrictedLift [NonarchimedeanRing S] {φ : R →+* S}
    (hφ : Continuous φ) (b : Fin k → S) :
    restrictedLiftLinear hφ b =
      restrictedLift (b := b) hφ
        (fun i ↦ (isPowerBounded_iff (a := b i)).mpr (isBounded_of_isLinearTopology _)) :=
  (rfl)

/-- `restrictedLiftLinear` computes `weightedEval` on the underlying formal power series. -/
theorem restrictedLiftLinear_apply {φ : R →+* S} (hφ : Continuous φ) (b : Fin k → S)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    restrictedLiftLinear hφ b f = weightedEval φ b f := by
  let _ := IsLinearTopology.isTopologicalRing (R := S)
  let _ := IsLinearTopology.nonarchimedeanRing S
  exact restrictedLift_apply (b := b) hφ _ f

/-- `restrictedLiftLinear` is continuous. -/
theorem continuous_restrictedLiftLinear {φ : R →+* S} (hφ : Continuous φ) (b : Fin k → S) :
    Continuous (restrictedLiftLinear hφ b) := by
  let _ := IsLinearTopology.isTopologicalRing (R := S)
  let _ := IsLinearTopology.nonarchimedeanRing S
  exact continuous_restrictedLift (b := b) hφ _

/-- `restrictedLiftLinear` extends `φ` on constants. -/
@[simp]
theorem restrictedLiftLinear_algebraMap {φ : R →+* S} (hφ : Continuous φ) (b : Fin k → S)
    (r : R) : restrictedLiftLinear hφ b (algebraMap R _ r) = φ r := by
  let _ := IsLinearTopology.isTopologicalRing (R := S)
  let _ := IsLinearTopology.nonarchimedeanRing S
  exact restrictedLift_algebraMap (b := b) hφ _ r

/-- `restrictedLiftLinear` sends each variable `Xᵢ` to `bᵢ`. -/
@[simp]
theorem restrictedLiftLinear_X {φ : R →+* S} (hφ : Continuous φ) (b : Fin k → S) (i : Fin k) :
    restrictedLiftLinear hφ b ⟨X i, isRestricted_X _ i⟩ = b i := by
  let _ := IsLinearTopology.isTopologicalRing (R := S)
  let _ := IsLinearTopology.nonarchimedeanRing S
  exact restrictedLift_X (b := b) hφ _ i

/-- `restrictedLiftLinear` is the unique continuous ring homomorphism extending `φ` and sending
each `Xᵢ` to `bᵢ`. -/
theorem restrictedLiftLinear_unique {φ : R →+* S} (hφ : Continuous φ) (b : Fin k → S)
    {ψ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* S} (hψ : Continuous ψ)
    (hC : ∀ r, ψ (algebraMap R _ r) = φ r)
    (hX : ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i) : ψ = restrictedLiftLinear hφ b :=
  isRestricted_subring_ringHom_ext_of_continuous hψ (continuous_restrictedLiftLinear hφ b)
    (fun r ↦ by rw [hC, restrictedLiftLinear_algebraMap])
    (fun i ↦ by rw [hX, restrictedLiftLinear_X])

/-- **The universal property of `R⟨X₁, …, Xₖ⟩` for linearly topologised targets.** A continuous
ring homomorphism `φ : R →+* S` into a complete Hausdorff linearly topologised ring extends to
exactly one continuous ring homomorphism `R⟨X₁, …, Xₖ⟩ →+* S` sending each `Xᵢ` to `bᵢ`, with no
condition on `b`. -/
theorem existsUnique_continuous_ringHom_isRestricted_subring_of_isLinearTopology
    {φ : R →+* S} (hφ : Continuous φ) (b : Fin k → S) :
    ∃! ψ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* S,
      Continuous ψ ∧ (∀ r, ψ (algebraMap R _ r) = φ r) ∧
        ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i :=
  ⟨restrictedLiftLinear hφ b,
    ⟨continuous_restrictedLiftLinear hφ b, restrictedLiftLinear_algebraMap hφ b,
      restrictedLiftLinear_X hφ b⟩,
    fun _ ⟨hψ, hC, hX⟩ ↦ restrictedLiftLinear_unique hφ b hψ hC hX⟩

/-- **The `R`-algebra lift out of `R⟨X₁, …, Xₖ⟩` into a linearly topologised `R`-algebra** with a
continuous structure map, at arbitrary `b₁, …, bₖ ∈ S`. -/
noncomputable def restrictedAlgLiftLinear [Algebra R S] (hR : Continuous (algebraMap R S))
    (b : Fin k → S) : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →ₐ[R] S :=
  { restrictedLiftLinear hR b with
    commutes' := restrictedLiftLinear_algebraMap hR b }

/-- `restrictedAlgLiftLinear` has the same underlying map as `restrictedLiftLinear`. -/
@[simp]
theorem coe_restrictedAlgLiftLinear [Algebra R S] (hR : Continuous (algebraMap R S))
    (b : Fin k → S) :
    ⇑(restrictedAlgLiftLinear hR b) = ⇑(restrictedLiftLinear hR b) :=
  (rfl)

/-- `restrictedAlgLiftLinear` is continuous. -/
theorem continuous_restrictedAlgLiftLinear [Algebra R S] (hR : Continuous (algebraMap R S))
    (b : Fin k → S) : Continuous (restrictedAlgLiftLinear hR b) :=
  continuous_restrictedLiftLinear hR b

/-- `restrictedAlgLiftLinear` sends each variable `Xᵢ` to `bᵢ`. -/
theorem restrictedAlgLiftLinear_X [Algebra R S] (hR : Continuous (algebraMap R S))
    (b : Fin k → S) (i : Fin k) :
    restrictedAlgLiftLinear hR b ⟨X i, isRestricted_X _ i⟩ = b i :=
  restrictedLiftLinear_X hR b i

/-- `restrictedAlgLiftLinear` is the unique continuous `R`-algebra homomorphism sending each `Xᵢ`
to `bᵢ`. -/
theorem restrictedAlgLiftLinear_unique [Algebra R S] (hR : Continuous (algebraMap R S))
    (b : Fin k → S) {ψ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →ₐ[R] S}
    (hψ : Continuous ψ) (hX : ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i) :
    ψ = restrictedAlgLiftLinear hR b :=
  AlgHom.toRingHom_injective <| restrictedLiftLinear_unique hR b hψ ψ.commutes hX

/-- **The `R`-algebra universal property of `R⟨X₁, …, Xₖ⟩` for linearly topologised targets**
(EGA I, Ch. 0, §7.5.3). -/
theorem existsUnique_continuous_algHom_isRestricted_subring_of_isLinearTopology
    [Algebra R S] (hR : Continuous (algebraMap R S)) (b : Fin k → S) :
    ∃! ψ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →ₐ[R] S,
      Continuous ψ ∧ ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i :=
  ⟨restrictedAlgLiftLinear hR b,
    ⟨continuous_restrictedAlgLiftLinear hR b, restrictedAlgLiftLinear_X hR b⟩,
    fun _ ⟨hψ, hX⟩ ↦ restrictedAlgLiftLinear_unique hR b hψ hX⟩

end LinearTopology

section Rename

variable [CompleteSpace R] {m : ℕ}

/-- **Renaming the variables of restricted series.** For a complete ultrametric normed ring `R`
and `f : Fin m → Fin k`, this is the `R`-algebra map `R⟨X₁, …, Xₘ⟩ → R⟨X₁, …, Xₖ⟩` sending each
`Xᵢ` to `X_{f i}`, the extension `TauCeti.MvPowerSeries.restrictedLift` of the constant-series
embedding. The map `f` need not be injective. -/
noncomputable def restrictedRename (f : Fin m → Fin k) :
    IsRestricted.subring (R := R) (fun _ : Fin m ↦ 1) →ₐ[R]
      IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) :=
  { restrictedLift (φ := algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))
      isometry_algebraMap_isRestrictedSubring.continuous
      (fun i ↦ isPowerBounded_X (f i)) with
    commutes' := restrictedLift_algebraMap _ _ }

/-- `restrictedRename f` sends each variable `Xᵢ` to `X_{f i}`. -/
@[simp]
theorem restrictedRename_X (f : Fin m → Fin k) (i : Fin m) :
    restrictedRename (R := R) f ⟨X i, isRestricted_X _ i⟩ = ⟨X (f i), isRestricted_X _ (f i)⟩ :=
  restrictedLift_X (φ := algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))
    isometry_algebraMap_isRestrictedSubring.continuous (fun i ↦ isPowerBounded_X (f i)) i

/-- `restrictedRename f` is continuous. -/
theorem continuous_restrictedRename (f : Fin m → Fin k) :
    Continuous (restrictedRename (R := R) f) :=
  continuous_restrictedLift (φ := algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))
    isometry_algebraMap_isRestrictedSubring.continuous (fun i ↦ isPowerBounded_X (f i))

/-- Renaming along the identity is the identity. -/
@[simp]
theorem restrictedRename_id :
    restrictedRename (R := R) (id : Fin k → Fin k) = AlgHom.id R _ :=
  AlgHom.toRingHom_injective <| isRestricted_subring_ringHom_ext_of_continuous
    (continuous_restrictedRename id) continuous_id (fun r ↦ by simp)
    (fun i ↦ restrictedRename_X id i)

/-- Successive renamings compose: renaming along `f` and then `g` is renaming along `g ∘ f`. -/
@[simp]
theorem restrictedRename_comp {n : ℕ} (g : Fin k → Fin n) (f : Fin m → Fin k) :
    (restrictedRename (R := R) g).comp (restrictedRename f) = restrictedRename (g ∘ f) :=
  AlgHom.toRingHom_injective <| isRestricted_subring_ringHom_ext_of_continuous
    ((continuous_restrictedRename g).comp (continuous_restrictedRename f))
    (continuous_restrictedRename (g ∘ f)) (fun r ↦ by simp)
    (fun i ↦ by simp)

/-- Applying `restrictedRename f` and then `restrictedRename g` is renaming along `g ∘ f`. -/
@[simp]
theorem restrictedRename_restrictedRename {n : ℕ} (g : Fin k → Fin n) (f : Fin m → Fin k)
    (x : IsRestricted.subring (R := R) (fun _ : Fin m ↦ 1)) :
    restrictedRename g (restrictedRename f x) = restrictedRename (g ∘ f) x :=
  congr($(restrictedRename_comp g f) x)

end Rename

end TauCeti.MvPowerSeries
