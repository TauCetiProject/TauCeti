/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.WeightedEval.UniversalProperty

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded
import TauCeti.Topology.Algebra.Nonarchimedean.LinearTopology

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
stay bounded, while `bᵢ` itself may have norm larger than one.

When `S` is linearly topologized (`IsLinearTopology S S`), for example an adic ring or formal power
series ring, every element of `S` is power-bounded, so `TauCeti.MvPowerSeries.restrictedLiftLinear`
evaluates at arbitrary `b₁, …, bₖ ∈ S` with no boundedness hypothesis. Conversely, when `R` admits
a pseudouniformiser — in particular when `R` is a nontrivially normed nonarchimedean field — every
continuous ring homomorphism out of `R⟨X₁, …, Xₖ⟩` sends each `Xᵢ` to a power-bounded element, so
power-boundedness of the `bᵢ` is both necessary and sufficient for a continuous extension to exist,
and reduces to `‖bᵢ‖ ≤ 1` when the target is a complete nonarchimedean normed field.

## Main definitions

* `TauCeti.MvPowerSeries.restrictedLift`: the continuous ring homomorphism
  `R⟨X₁, …, Xₖ⟩ →+* S` extending `φ` and sending `Xᵢ` to power-bounded `bᵢ`.
* `TauCeti.MvPowerSeries.restrictedLiftLinear` and
  `TauCeti.MvPowerSeries.restrictedLiftLinearAlgHom`: the continuous ring and `R`-algebra
  homomorphisms `R⟨X₁, …, Xₖ⟩ → S` into a linearly topologized target at arbitrary `bᵢ ∈ S`.
* `TauCeti.MvPowerSeries.restrictedRename`: for complete `R` and `f : Fin m → Fin k`, the
  `R`-algebra map `R⟨X₁, …, Xₘ⟩ →ₐ[R] R⟨X₁, …, Xₖ⟩` sending `Xᵢ` to `X_{f i}`.

## Main results

* `TauCeti.MvPowerSeries.isPowerBounded_X`: each variable `Xᵢ` is power-bounded.
* `TauCeti.MvPowerSeries.isRestricted_subring_ringHom_ext_of_continuous`: continuous ring
  homomorphisms out of `R⟨X₁, …, Xₖ⟩` agreeing on constants and variables are equal.
* `TauCeti.MvPowerSeries.restrictedLift_unique` and
  `TauCeti.MvPowerSeries.existsUnique_continuous_ringHom_isRestricted_subring`: the universal
  property at power-bounded arguments.
* `TauCeti.MvPowerSeries.existsUnique_continuous_ringHom_isRestricted_subring_of_isLinearTopology`:
  the universal property into linearly topologized targets at arbitrary arguments.
* `TauCeti.MvPowerSeries.isPowerBounded_apply_X_of_isPseudoUniformizer` and
  `TauCeti.MvPowerSeries.exists_continuous_ringHom_isRestricted_subring_iff_forall_isPowerBounded`:
  when `R` has a pseudouniformiser, power-boundedness of the images of `Xᵢ` is necessary and
  sufficient for a continuous extension.
* `TauCeti.MvPowerSeries.exists_continuous_ringHom_isRestricted_subring_iff_forall_norm_le_one`:
  between nonarchimedean normed fields with complete target, a continuous extension exists if and
  only if `∀ i, ‖bᵢ‖ ≤ 1`.
* `TauCeti.MvPowerSeries.restrictedRename_id`, `TauCeti.MvPowerSeries.restrictedRename_comp`:
  renaming along the identity is the identity, and successive renamings compose.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Proposition 5.50.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §1.4.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries TauCeti.Huber Topology

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

/-- **Evaluation of `R⟨X₁, …, Xₖ⟩` into a linearly topologized ring.** Because `S` has a basis of
open ideals around zero, every element of `S` is power-bounded, so any continuous `φ : R →+* S` and
arbitrary `b₁, …, bₖ ∈ S` induce a continuous ring homomorphism `R⟨X₁, …, Xₖ⟩ →+* S`. -/
noncomputable def restrictedLiftLinear {φ : R →+* S} (hφ : Continuous φ) (b : Fin k → S) :
    IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* S :=
  haveI := IsLinearTopology.isTopologicalRing (R := S)
  haveI := IsLinearTopology.nonarchimedeanRing S
  restrictedLift (b := b) hφ fun _ ↦ isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)

/-- `restrictedLiftLinear` is continuous. -/
theorem continuous_restrictedLiftLinear {φ : R →+* S} (hφ : Continuous φ) (b : Fin k → S) :
    Continuous (restrictedLiftLinear hφ b) := by
  have := IsLinearTopology.isTopologicalRing (R := S)
  have := IsLinearTopology.nonarchimedeanRing S
  exact continuous_restrictedLift (b := b) hφ _

/-- `restrictedLiftLinear` extends `φ` on constants. -/
@[simp]
theorem restrictedLiftLinear_algebraMap {φ : R →+* S} (hφ : Continuous φ) (b : Fin k → S)
    (r : R) :
    restrictedLiftLinear hφ b (algebraMap R _ r) = φ r := by
  have := IsLinearTopology.isTopologicalRing (R := S)
  have := IsLinearTopology.nonarchimedeanRing S
  exact restrictedLift_algebraMap (b := b) hφ _ r

/-- `restrictedLiftLinear` sends each coordinate variable `Xᵢ` to `bᵢ`. -/
@[simp]
theorem restrictedLiftLinear_X {φ : R →+* S} (hφ : Continuous φ) (b : Fin k → S) (i : Fin k) :
    restrictedLiftLinear hφ b ⟨X i, isRestricted_X _ i⟩ = b i := by
  have := IsLinearTopology.isTopologicalRing (R := S)
  have := IsLinearTopology.nonarchimedeanRing S
  exact restrictedLift_X (b := b) hφ _ i

/-- `restrictedLiftLinear` is the unique continuous ring homomorphism extending `φ` and sending
each `Xᵢ` to `bᵢ`. -/
theorem restrictedLiftLinear_unique {φ : R →+* S} (hφ : Continuous φ) (b : Fin k → S)
    {ψ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* S} (hψ : Continuous ψ)
    (hC : ∀ r, ψ (algebraMap R _ r) = φ r) (hX : ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i) :
    ψ = restrictedLiftLinear hφ b := by
  have := IsLinearTopology.isTopologicalRing (R := S)
  have := IsLinearTopology.nonarchimedeanRing S
  exact restrictedLift_unique (b := b) hφ _ hψ hC hX

/-- **The universal property of `R⟨X₁, …, Xₖ⟩` into linearly topologized rings.** A continuous ring
homomorphism `φ : R →+* S` into a complete Hausdorff linearly topologized ring extends uniquely to
a continuous ring homomorphism `R⟨X₁, …, Xₖ⟩ →+* S` sending each `Xᵢ` to an arbitrary `bᵢ ∈ S`. -/
theorem existsUnique_continuous_ringHom_isRestricted_subring_of_isLinearTopology
    {φ : R →+* S} (hφ : Continuous φ) (b : Fin k → S) :
    ∃! ψ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* S,
      Continuous ψ ∧ (∀ r, ψ (algebraMap R _ r) = φ r) ∧
        ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i :=
  ⟨restrictedLiftLinear hφ b, ⟨continuous_restrictedLiftLinear hφ b,
    restrictedLiftLinear_algebraMap hφ b, restrictedLiftLinear_X hφ b⟩,
    fun _ ⟨hψ, hC, hX⟩ ↦ restrictedLiftLinear_unique hφ b hψ hC hX⟩

/-- `R`-algebra form of `restrictedLiftLinear` when `algebraMap R S` is continuous. -/
noncomputable def restrictedLiftLinearAlgHom [Algebra R S] (hφ : Continuous (algebraMap R S))
    (b : Fin k → S) :
    IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →ₐ[R] S :=
  { restrictedLiftLinear hφ b with
    commutes' := restrictedLiftLinear_algebraMap hφ b }

/-- `restrictedLiftLinearAlgHom` sends each `Xᵢ` to `bᵢ`. -/
@[simp]
theorem restrictedLiftLinearAlgHom_X [Algebra R S] (hφ : Continuous (algebraMap R S))
    (b : Fin k → S) (i : Fin k) :
    restrictedLiftLinearAlgHom hφ b ⟨X i, isRestricted_X _ i⟩ = b i :=
  restrictedLiftLinear_X hφ b i

/-- `restrictedLiftLinearAlgHom` is continuous. -/
theorem continuous_restrictedLiftLinearAlgHom [Algebra R S] (hφ : Continuous (algebraMap R S))
    (b : Fin k → S) :
    Continuous (restrictedLiftLinearAlgHom hφ b) :=
  continuous_restrictedLiftLinear hφ b

end LinearTopology

section Characterization

/-- A pseudouniformiser of `R` remains a pseudouniformiser in `R⟨X₁, …, Xₖ⟩`, since the constant
series embedding is isometric. -/
theorem isPseudoUniformizer_algebraMap_isRestricted_subring {ϖ : R} (hϖ : IsPseudoUniformizer ϖ) :
    IsPseudoUniformizer
      (algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) ϖ) := by
  rw [isPseudoUniformizer_iff] at hϖ ⊢
  refine ⟨hϖ.1.map _, ?_⟩
  let ι := algebraMap R (IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))
  have hcont : Filter.Tendsto ι (𝓝 0) (𝓝 0) :=
    map_zero ι ▸ isometry_algebraMap_isRestrictedSubring.continuous.continuousAt.tendsto
  rw [IsTopologicallyNilpotent]
  simpa [ι, Function.comp_def, map_pow] using hcont.comp hϖ.2

/-- If a topological ring `A` has a pseudouniformiser, any ring homomorphism `f : A →+* T` into a
topological ring that is continuous at zero preserves power-boundedness. -/
private theorem isPowerBounded_map_of_isPseudoUniformizer {A T : Type*} [Ring A]
    [TopologicalSpace A] [Ring T] [TopologicalSpace T] [IsTopologicalRing T] {ϖ : A}
    (hϖ : IsPseudoUniformizer ϖ) {f : A →+* T} (hf : ContinuousAt f 0) {a : A}
    (ha : IsPowerBounded a) : IsPowerBounded (f a) := by
  refine isPowerBounded_iff.mpr (isBounded_iff.mpr fun U hU ↦ ?_)
  have hmul : Filter.Tendsto (fun p : T × T ↦ p.1 * p.2) (𝓝 0 ×ˢ 𝓝 0) (𝓝 0) := by
    simpa [nhds_prod_eq] using (continuous_mul (M := T)).tendsto ((0 : T), (0 : T))
  obtain ⟨W₁, hW₁, W₂, hW₂, hW⟩ := Filter.mem_prod_iff.mp (hmul hU)
  have hfW₂ : f ⁻¹' W₂ ∈ 𝓝 (0 : A) := hf (map_zero f ▸ hW₂)
  obtain ⟨m, hm⟩ := (isPowerBounded_iff.mp ha).exists_pow_mul_subset hϖ.isTopologicallyNilpotent
    hfW₂
  obtain ⟨u, hu⟩ := hϖ.isUnit.pow m
  let v : Tˣ := Units.map f.toMonoidHom u
  have hv : (v : T) = f (ϖ ^ m) := by simp [v, hu]
  have hV : (fun s : T ↦ s * (↑v⁻¹ : T)) ⁻¹' W₁ ∈ 𝓝 (0 : T) := by
    refine ContinuousAt.preimage_mem_nhds ?_ (by simpa using hW₁)
    exact (continuous_id.mul continuous_const).continuousAt
  refine ⟨(fun s : T ↦ s * (↑v⁻¹ : T)) ⁻¹' W₁, hV, ?_⟩
  rintro _ ⟨s, hs, _, ⟨n, rfl⟩, rfl⟩
  have hmem₂ : (v : T) * f a ^ n ∈ W₂ := by
    rw [hv, ← map_pow, ← map_mul]
    exact hm (Set.mul_mem_mul (Set.mem_singleton _) ⟨n, rfl⟩)
  have hident : (s * (↑v⁻¹ : T)) * ((v : T) * f a ^ n) = s * f a ^ n := by
    rw [mul_assoc, ← mul_assoc (↑v⁻¹ : T), Units.inv_mul, one_mul]
  dsimp only
  rw [← hident]
  exact hW (Set.mk_mem_prod hs hmem₂)

/-- When `R` admits a pseudouniformiser `ϖ`, every ring homomorphism out of `R⟨X₁, …, Xₖ⟩` that is
continuous at zero sends each coordinate variable `Xᵢ` to a power-bounded element. The
pseudouniformiser hypothesis is needed: if `R` carries the discrete norm, `R⟨X⟩ = R[X]` is discrete
and every ring homomorphism out of it is continuous. -/
theorem isPowerBounded_apply_X_of_isPseudoUniformizer {T : Type*} [Ring T] [TopologicalSpace T]
    [IsTopologicalRing T] {ϖ : R} (hϖ : IsPseudoUniformizer ϖ)
    {ψ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* T} (hψ : ContinuousAt ψ 0)
    (i : Fin k) :
    IsPowerBounded (ψ ⟨X i, isRestricted_X _ i⟩) :=
  isPowerBounded_map_of_isPseudoUniformizer
    (isPseudoUniformizer_algebraMap_isRestricted_subring hϖ) hψ (isPowerBounded_X i)

/-- **Characterization of continuous extensions when `R` has a pseudouniformiser.** Given a
continuous homomorphism `φ : R →+* S` into a complete Hausdorff nonarchimedean ring, a continuous
extension `R⟨X₁, …, Xₖ⟩ →+* S` sending `Xᵢ` to `bᵢ` exists if and only if every `bᵢ` is
power-bounded. -/
theorem exists_continuous_ringHom_isRestricted_subring_iff_forall_isPowerBounded
    {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [NonarchimedeanRing S]
    [CompleteSpace S] [T3Space S] {ϖ : R} (hϖ : IsPseudoUniformizer ϖ)
    {φ : R →+* S} (hφ : Continuous φ) (b : Fin k → S) :
    (∃ ψ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* S,
      Continuous ψ ∧ (∀ r, ψ (algebraMap R _ r) = φ r) ∧
        ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i) ↔
      ∀ i, IsPowerBounded (b i) := by
  refine ⟨fun ⟨ψ, hψ, _, hX⟩ i ↦ hX i ▸
    isPowerBounded_apply_X_of_isPseudoUniformizer hϖ hψ.continuousAt i,
    fun hb ↦ ⟨restrictedLift hφ hb, continuous_restrictedLift hφ hb,
      restrictedLift_algebraMap hφ hb, restrictedLift_X hφ hb⟩⟩

section NormedField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- Over a nontrivially normed nonarchimedean field `K`, every continuous ring homomorphism out of
`K⟨X₁, …, Xₖ⟩` sends each coordinate variable `Xᵢ` to a power-bounded element. -/
theorem isPowerBounded_apply_X_of_continuous {T : Type*} [Ring T] [TopologicalSpace T]
    [IsTopologicalRing T] {ψ : IsRestricted.subring (R := K) (fun _ : Fin k ↦ 1) →+* T}
    (hψ : Continuous ψ) (i : Fin k) :
    IsPowerBounded (ψ ⟨X i, isRestricted_X _ i⟩) := by
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt K one_pos
  exact isPowerBounded_apply_X_of_isPseudoUniformizer
    (isPseudoUniformizer_iff_norm_lt_one.mpr ⟨norm_pos_iff.mp hϖ0, hϖ1⟩) hψ.continuousAt i

/-- **Norm criterion for continuous evaluation over a nonarchimedean field.** For a continuous ring
homomorphism `φ : K →+* L` from a nontrivially normed nonarchimedean field into a complete
nonarchimedean normed field `L`, a continuous extension `K⟨X₁, …, Xₖ⟩ →+* L` sending `Xᵢ` to `bᵢ`
exists if and only if `‖bᵢ‖ ≤ 1` for every `i`. -/
theorem exists_continuous_ringHom_isRestricted_subring_iff_forall_norm_le_one
    {L : Type*} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    {φ : K →+* L} (hφ : Continuous φ) (b : Fin k → L) :
    (∃ ψ : IsRestricted.subring (R := K) (fun _ : Fin k ↦ 1) →+* L,
      Continuous ψ ∧ (∀ c, ψ (algebraMap K _ c) = φ c) ∧
        ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i) ↔
      ∀ i, ‖b i‖ ≤ 1 := by
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt K one_pos
  have hϖ : IsPseudoUniformizer ϖ :=
    isPseudoUniformizer_iff_norm_lt_one.mpr ⟨norm_pos_iff.mp hϖ0, hϖ1⟩
  rw [exists_continuous_ringHom_isRestricted_subring_iff_forall_isPowerBounded hϖ hφ b]
  exact forall_congr' fun _ ↦ isPowerBounded_iff_norm_le_one

/-- Over a nontrivially normed nonarchimedean field, any continuous `φ : K →+* L` into a complete
nonarchimedean normed field and tuple `b` with `∀ i, ‖b i‖ ≤ 1` extend uniquely to a continuous
ring homomorphism `K⟨X₁, …, Xₖ⟩ →+* L` (without assuming `φ` is contractive). -/
theorem existsUnique_continuous_ringHom_isRestricted_subring_of_norm_le_one
    {L : Type*} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    {φ : K →+* L} (hφ : Continuous φ) {b : Fin k → L} (hb : ∀ i, ‖b i‖ ≤ 1) :
    ∃! ψ : IsRestricted.subring (R := K) (fun _ : Fin k ↦ 1) →+* L,
      Continuous ψ ∧ (∀ c, ψ (algebraMap K _ c) = φ c) ∧
        ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i :=
  existsUnique_continuous_ringHom_isRestricted_subring hφ
    fun i ↦ isPowerBounded_iff_norm_le_one.mpr (hb i)

end NormedField

end Characterization

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
