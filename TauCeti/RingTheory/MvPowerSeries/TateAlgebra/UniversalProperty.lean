/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.Gauss.Norm
public import TauCeti.RingTheory.Huber.WeightedEval.UniversalProperty
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Reduction

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded
import TauCeti.Topology.Algebra.Nonarchimedean.LinearTopology
import TauCeti.Topology.Algebra.Module.Quotient

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
stay bounded, while `bᵢ` itself may have norm larger than one. When `S` is a complete Hausdorff
linearly topologised `R`-algebra with continuous structure map, open-ideal neighbourhoods make every
element of `S` power-bounded, so arbitrary variable images `b : Fin k → S` extend uniquely
(`TauCeti.MvPowerSeries.restrictedLiftAlgHomOfIsLinearTopology`).

When `S` is a complete Hausdorff linearly topologized ring (`IsLinearTopology S S`), for example an
adic ring or formal power series ring, every element of `S` is power-bounded, so
`TauCeti.MvPowerSeries.existsUnique_continuous_ringHom_isRestricted_subring_of_isLinearTopology`
evaluates at arbitrary `b₁, …, bₖ ∈ S` with no boundedness hypothesis. Conversely, when `R` admits
a pseudouniformiser — in particular when `R` is a nontrivially normed nonarchimedean field — every
continuous ring homomorphism out of `R⟨X₁, …, Xₖ⟩` sends each `Xᵢ` to a power-bounded element, so
power-boundedness of the `bᵢ` is both necessary and sufficient for a continuous extension to exist,
and reduces to `‖bᵢ‖ ≤ 1` when the target is a complete nonarchimedean normed field.

## Main definitions

* `TauCeti.MvPowerSeries.restrictedLift`: the continuous ring homomorphism
  `R⟨X₁, …, Xₖ⟩ →+* S` extending `φ` and sending `Xᵢ` to power-bounded `bᵢ`.
* `TauCeti.MvPowerSeries.restrictedRename`: for complete `R` and `f : Fin m → Fin k`, the
  `R`-algebra map `R⟨X₁, …, Xₘ⟩ →ₐ[R] R⟨X₁, …, Xₖ⟩` sending `Xᵢ` to `X_{f i}`.
* `TauCeti.MvPowerSeries.restrictedLiftAlgHomOfIsLinearTopology`: continuous `R`-algebra evaluation
  of `R⟨X₁, …, Xₖ⟩` at arbitrary points of a complete Hausdorff linearly topologised `R`-algebra.

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
  from a nontrivially normed nonarchimedean field into a complete nonarchimedean normed field, a
  continuous extension exists if and only if `∀ i, ‖bᵢ‖ ≤ 1`.
* `TauCeti.MvPowerSeries.restrictedRename_id`, `TauCeti.MvPowerSeries.restrictedRename_comp`:
  renaming along the identity is the identity, and successive renamings compose.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Proposition 5.50.
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §§7.5.2–7.5.3.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §§1.4, 5.1.3, 6.1.1.
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

/-- `restrictedLift` evaluates through `weightedEvalHom` along the inverse Gauss comparison. -/
theorem restrictedLift_apply (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    restrictedLift hφ hb f =
      weightedEvalHom isWeightFamily_one_weight hφ.continuousAt
        ((isWeightBounded_one_weight_iff_forall_isPowerBounded φ b).mpr hb)
        (restrictedMvPowerSeriesGaussEquiv.symm f) := (rfl)

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
  induction p using MvPolynomial.induction_on with
  | C a => simp [← MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp => simp [map_mul, hp]

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

local notation:max "Tate" k':max R':max => IsRestricted.subring (R := R') (fun _ : Fin k' ↦ 1)

section LinearTopology

variable {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
  [IsLinearTopology S S] [CompleteSpace S] [T2Space S]

/-- **Universal property of `R⟨X₁, …, Xₖ⟩` into linearly topologized rings.** A continuous ring
homomorphism `φ : R →+* S` into a complete Hausdorff linearly topologized ring, such as an adic
ring, extends to exactly one continuous ring homomorphism `R⟨X₁, …, Xₖ⟩ →+* S` sending each `Xᵢ`
to a prescribed `bᵢ`, with no boundedness hypothesis on the `bᵢ`. -/
theorem existsUnique_continuous_ringHom_isRestricted_subring_of_isLinearTopology
    {φ : R →+* S} (hφ : Continuous φ) (b : Fin k → S) :
    ∃! ψ : Tate k R →+* S, Continuous ψ ∧ (∀ r, ψ (algebraMap R _ r) = φ r) ∧
      ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i := by
  have := IsLinearTopology.isTopologicalRing (R := S)
  have := IsLinearTopology.nonarchimedeanRing S
  exact existsUnique_continuous_ringHom_isRestricted_subring hφ fun _ ↦
    isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)

end LinearTopology

section Characterization

/-- A pseudouniformiser of `R` remains a pseudouniformiser in `R{X/c}` at positive polyradii. -/
theorem isPseudoUniformizer_algebraMap_isRestricted_subring {σ : Type*} {c : σ → ℝ}
    [∀ i, Fact (0 < c i)] {ϖ : R} (hϖ : IsPseudoUniformizer ϖ) :
    IsPseudoUniformizer (algebraMap R (IsRestricted.subring (R := R) c) ϖ) :=
  hϖ.map isometry_algebraMap_isRestrictedSubring.continuous

/-- When `R` has a pseudouniformiser, any morphism of monoids with zero out of `R⟨X₁, …, Xₖ⟩`
continuous at `0` sends each `Xᵢ` to a power-bounded element. -/
theorem isPowerBounded_apply_X_of_isPseudoUniformizer {T F : Type*} [MonoidWithZero T]
    [TopologicalSpace T] [ContinuousMul T] [FunLike F (Tate k R) T]
    [MonoidWithZeroHomClass F (Tate k R) T] {ϖ : R} (hϖ : IsPseudoUniformizer ϖ) {ψ : F}
    (hψ : ContinuousAt ψ 0) (i : Fin k) : IsPowerBounded (ψ ⟨X i, isRestricted_X _ i⟩) :=
  (isPowerBounded_X i).map_of_isPseudoUniformizer
    (isPseudoUniformizer_algebraMap_isRestricted_subring hϖ) hψ

/-- **Characterization of continuous extensions when `R` has a pseudouniformiser**: a continuous
extension sending `Xᵢ` to `bᵢ` exists iff every `bᵢ` is power-bounded. -/
theorem exists_continuous_ringHom_isRestricted_subring_iff_forall_isPowerBounded
    {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [NonarchimedeanRing S]
    [CompleteSpace S] [T3Space S] {ϖ : R} (hϖ : IsPseudoUniformizer ϖ)
    {φ : R →+* S} (hφ : Continuous φ) (b : Fin k → S) :
    (∃ ψ : Tate k R →+* S, Continuous ψ ∧ (∀ r, ψ (algebraMap R _ r) = φ r) ∧
      ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i) ↔ ∀ i, IsPowerBounded (b i) :=
  ⟨fun ⟨_, hψ, _, hX⟩ i ↦ hX i ▸ isPowerBounded_apply_X_of_isPseudoUniformizer hϖ hψ.continuousAt i,
    fun hb ↦ ⟨restrictedLift hφ hb, continuous_restrictedLift hφ hb,
      restrictedLift_algebraMap hφ hb, restrictedLift_X hφ hb⟩⟩

section NormedField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- Over a nontrivially normed nonarchimedean field `K`, any morphism of monoids with zero out of
`K⟨X₁, …, Xₖ⟩` continuous at `0` sends each `Xᵢ` to a power-bounded element. -/
theorem isPowerBounded_apply_X_of_continuousAt_zero {T F : Type*} [MonoidWithZero T]
    [TopologicalSpace T] [ContinuousMul T] [FunLike F (Tate k K) T]
    [MonoidWithZeroHomClass F (Tate k K) T] {ψ : F} (hψ : ContinuousAt ψ 0) (i : Fin k) :
    IsPowerBounded (ψ ⟨X i, isRestricted_X _ i⟩) := by
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := K)
  exact isPowerBounded_apply_X_of_isPseudoUniformizer hϖ hψ i

/-- **Norm criterion over a nonarchimedean field**: a continuous extension `K⟨X₁, …, Xₖ⟩ →+* L`
into a complete nonarchimedean normed field exists iff `‖bᵢ‖ ≤ 1` for all `i`. -/
theorem exists_continuous_ringHom_isRestricted_subring_iff_forall_norm_le_one
    {L : Type*} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    {φ : K →+* L} (hφ : Continuous φ) (b : Fin k → L) :
    (∃ ψ : Tate k K →+* L, Continuous ψ ∧ (∀ c, ψ (algebraMap K _ c) = φ c) ∧
      ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i) ↔ ∀ i, ‖b i‖ ≤ 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := K)
  rw [exists_continuous_ringHom_isRestricted_subring_iff_forall_isPowerBounded hϖ hφ b]
  exact forall_congr' fun _ ↦ isPowerBounded_iff_norm_le_one

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

section LinearTopology

variable {T : Type*} [CommRing T] [UniformSpace T] [IsUniformAddGroup T] [CompleteSpace T]
  [T2Space T]

/-- **Evaluation of `restrictedLift` commutes with open-ideal polynomial reduction.** -/
theorem mk_restrictedLift_eq_eval₂_isRestrictedReduction [NonarchimedeanRing T] {φ : R →+* T}
    (hφ : Continuous φ) {b : Fin k → T} (hb : ∀ i, IsPowerBounded (b i))
    (I : Ideal R) (hI : IsOpen (I : Set R)) (J : Ideal T) (hJ : IsOpen (J : Set T))
    (hIJ : I ≤ J.comap φ) (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    Ideal.Quotient.mk J (restrictedLift hφ hb f) =
      (I.isRestrictedReduction hI f).eval₂ (Ideal.quotientMap J φ hIJ)
        (Ideal.Quotient.mk J ∘ b) := by
  let : DiscreteTopology (T ⧸ J) := Submodule.Quotient.discreteTopology_of_isOpen J hJ
  have h := isRestricted_subring_ringHom_ext_of_continuous
    (ψ₁ := (Ideal.Quotient.mk J).comp (restrictedLift hφ hb))
    (ψ₂ := (MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ)
      (Ideal.Quotient.mk J ∘ b)).comp (I.isRestrictedReduction (σ := Fin k) hI))
    (continuous_quot_mk.comp (continuous_restrictedLift hφ hb))
    (I.continuous_comp_isRestrictedReduction hI
      (MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ) (Ideal.Quotient.mk J ∘ b)))
    (fun r ↦ by simp)
    (fun i ↦ by simp)
  exact RingHom.congr_fun h f

variable [IsLinearTopology T T] [Algebra R T]

/-- **Continuous `R`-algebra evaluation of Gauss-normed restricted series in a complete Hausdorff
linearly topologised `R`-algebra** (EGA I, Ch. 0, §7.5.3). When `T` is complete and Hausdorff with
continuous `algebraMap R T`, open-ideal neighbourhoods make every element power-bounded
(`isBounded_of_isLinearTopology`), so arbitrary `b : Fin k → T` determine a continuous `R`-algebra
homomorphism. -/
noncomputable def restrictedLiftAlgHomOfIsLinearTopology (hR : Continuous (algebraMap R T))
    (b : Fin k → T) :
    IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →ₐ[R] T :=
  haveI := IsLinearTopology.isTopologicalRing (R := T)
  haveI := IsLinearTopology.nonarchimedeanRing T
  let φ := restrictedLift hR (b := b) fun _ ↦
    isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)
  { __ := φ, toFun := φ, commutes' := restrictedLift_algebraMap hR _ }

/-- Underlying ring homomorphism of `restrictedLiftAlgHomOfIsLinearTopology`. -/
@[simp]
theorem coe_restrictedLiftAlgHomOfIsLinearTopology (hR : Continuous (algebraMap R T))
    (b : Fin k → T) :
    (restrictedLiftAlgHomOfIsLinearTopology hR b :
      IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* T) =
      letI := IsLinearTopology.isTopologicalRing (R := T)
      letI := IsLinearTopology.nonarchimedeanRing T
      restrictedLift hR (b := b) fun _ ↦
        isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _) :=
  RingHom.ext fun _ ↦ rfl

/-- `restrictedLiftAlgHomOfIsLinearTopology` sends each variable `Xᵢ` to `bᵢ`. -/
@[simp]
theorem restrictedLiftAlgHomOfIsLinearTopology_X (hR : Continuous (algebraMap R T))
    (b : Fin k → T) (i : Fin k) :
    restrictedLiftAlgHomOfIsLinearTopology hR b ⟨X i, isRestricted_X _ i⟩ = b i :=
  letI := IsLinearTopology.isTopologicalRing (R := T)
  letI := IsLinearTopology.nonarchimedeanRing T
  restrictedLift_X hR (b := b) (fun _ ↦ isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)) i

/-- `restrictedLiftAlgHomOfIsLinearTopology` is continuous for the Gauss norm topology. -/
theorem continuous_restrictedLiftAlgHomOfIsLinearTopology (hR : Continuous (algebraMap R T))
    (b : Fin k → T) :
    Continuous (restrictedLiftAlgHomOfIsLinearTopology hR b) :=
  letI := IsLinearTopology.isTopologicalRing (R := T)
  letI := IsLinearTopology.nonarchimedeanRing T
  continuous_restrictedLift hR (b := b) fun _ ↦
    isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)

/-- **Universal property of Gauss-normed restricted series for complete Hausdorff linearly
topologised `R`-algebras.** When `T` is complete and Hausdorff with continuous `algebraMap R T`,
unlike `existsUnique_continuous_ringHom_isRestricted_subring` (`IsPowerBounded (b i)`) and
`RingHom.restrictedEval₂OfBound` (`‖b i‖ ≤ 1`), open-ideal neighbourhoods make every element
power-bounded, so arbitrary `b : Fin k → T` extend uniquely. -/
theorem existsUnique_continuous_algHom_isRestricted_subring_of_isLinearTopology
    (hR : Continuous (algebraMap R T)) (b : Fin k → T) :
    ∃! ψ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →ₐ[R] T,
      Continuous ψ ∧ ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i :=
  letI := IsLinearTopology.isTopologicalRing (R := T)
  letI := IsLinearTopology.nonarchimedeanRing T
  ⟨restrictedLiftAlgHomOfIsLinearTopology hR b,
    ⟨continuous_restrictedLiftAlgHomOfIsLinearTopology hR b,
      restrictedLiftAlgHomOfIsLinearTopology_X hR b⟩,
    fun ψ ⟨hψ, hX⟩ ↦ AlgHom.toRingHom_injective <| isRestricted_subring_ringHom_ext_of_continuous
      hψ (continuous_restrictedLiftAlgHomOfIsLinearTopology hR b)
      (fun r ↦ (ψ.commutes r).trans ((restrictedLiftAlgHomOfIsLinearTopology hR b).commutes r).symm)
      fun i ↦ (hX i).trans (restrictedLiftAlgHomOfIsLinearTopology_X hR b i).symm⟩

end LinearTopology

end TauCeti.MvPowerSeries
