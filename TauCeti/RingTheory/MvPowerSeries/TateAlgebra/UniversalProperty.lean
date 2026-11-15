/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.WeightedEval.UniversalProperty
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
stay bounded, while `bᵢ` itself may have norm larger than one. Into a complete Hausdorff linearly
topologised ring or `R`-algebra, open ideals absorb multiplication by arbitrary elements of `S`
(`isBounded_of_isLinearTopology`), so every element is power-bounded and evaluation applies at
arbitrary tuples `b : Fin k → S`.

## Main definitions

* `TauCeti.MvPowerSeries.restrictedLift`: the continuous ring homomorphism
  `R⟨X₁, …, Xₖ⟩ →+* S` extending `φ` and sending `Xᵢ` to `bᵢ`.
* `TauCeti.MvPowerSeries.restrictedLiftOfIsLinearTopology` and
  `TauCeti.MvPowerSeries.restrictedLiftAlgHomOfIsLinearTopology`: continuous evaluation into a
  complete Hausdorff linearly topologised ring or `R`-algebra at arbitrary points.
* `TauCeti.MvPowerSeries.restrictedRename`: for complete `R` and `f : Fin m → Fin k`, the
  `R`-algebra map `R⟨X₁, …, Xₘ⟩ →ₐ[R] R⟨X₁, …, Xₖ⟩` sending `Xᵢ` to `X_{f i}`.

## Main results

* `TauCeti.MvPowerSeries.isPowerBounded_X`: each variable `Xᵢ` is power-bounded.
* `TauCeti.MvPowerSeries.isRestricted_subring_ringHom_ext_of_continuous`: continuous ring
  homomorphisms out of `R⟨X₁, …, Xₖ⟩` agreeing on constants and variables are equal.
* `TauCeti.MvPowerSeries.restrictedLift_unique`: `restrictedLift` is the only such continuous
  extension.
* `TauCeti.MvPowerSeries.existsUnique_continuous_ringHom_isRestricted_subring`: the universal
  property.
* `TauCeti.MvPowerSeries.existsUnique_continuous_ringHom_isRestricted_subring_of_isLinearTopology`
  and
  `TauCeti.MvPowerSeries.existsUnique_continuous_algHom_isRestricted_subring_of_isLinearTopology`:
  the universal property into complete Hausdorff linearly topologised rings and `R`-algebras.
* `TauCeti.MvPowerSeries.restrictedRename_id`, `TauCeti.MvPowerSeries.restrictedRename_comp`:
  renaming along the identity is the identity, and successive renamings compose.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Proposition 5.50.
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

section Lift

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

/-- `restrictedLift` evaluates a restricted series by applying `weightedEvalHom` along
`restrictedMvPowerSeriesGaussEquiv.symm`. -/
theorem restrictedLift_apply (g : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    restrictedLift hφ hb g =
      weightedEvalHom isWeightFamily_one_weight hφ.continuousAt
        ((isWeightBounded_one_weight_iff_forall_isPowerBounded φ b).mpr hb)
        (restrictedMvPowerSeriesGaussEquiv.symm g) := by
  rfl

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

end Lift

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

/-! ### Universal property into linearly topologised rings and algebras

When `S` is linearly topologised (`[IsLinearTopology S S]`), zero admits a neighbourhood basis of
open ideals. Since an ideal `J` absorbs multiplication by arbitrary elements of `S` (`J · S ⊆ J`,
so `J · T ⊆ J` for every `T ⊆ S`), every subset of `S` is bounded, and
`isPowerBounded_of_isLinearTopology b` holds unconditionally for all `b : S`. Specialising
`restrictedLift` therefore removes the power-boundedness hypothesis on the evaluation point
`b : Fin k → S`. -/

variable {T : Type*} [CommRing T] [UniformSpace T] [IsUniformAddGroup T]
  [IsLinearTopology T T] [CompleteSpace T] [T2Space T]

/-- **Continuous evaluation of `R⟨X₁, …, Xₖ⟩` into a complete Hausdorff linearly topologised
ring**, at an arbitrary tuple `b : Fin k → T` with no norm or power-boundedness condition on `b`. -/
noncomputable def restrictedLiftOfIsLinearTopology {φ : R →+* T} (hφ : Continuous φ)
    (b : Fin k → T) :
    IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* T :=
  letI := IsLinearTopology.isTopologicalRing (R := T)
  letI := IsLinearTopology.nonarchimedeanRing T
  restrictedLift (b := b) hφ fun _ ↦ isPowerBounded_of_isLinearTopology _

/-- `restrictedLiftOfIsLinearTopology` is `restrictedLift` supplied with the nonarchimedean
topological-ring instances and linear-topology power-boundedness witness. -/
theorem restrictedLiftOfIsLinearTopology_eq_restrictedLift {φ : R →+* T} (hφ : Continuous φ)
    (b : Fin k → T) :
    restrictedLiftOfIsLinearTopology hφ b =
      letI := IsLinearTopology.isTopologicalRing (R := T)
      letI := IsLinearTopology.nonarchimedeanRing T
      restrictedLift (b := b) hφ fun _ ↦ isPowerBounded_of_isLinearTopology _ := by
  rfl

/-- `restrictedLiftOfIsLinearTopology` is continuous. -/
theorem continuous_restrictedLiftOfIsLinearTopology {φ : R →+* T} (hφ : Continuous φ)
    (b : Fin k → T) :
    Continuous (restrictedLiftOfIsLinearTopology hφ b) := by
  have := IsLinearTopology.isTopologicalRing (R := T)
  have := IsLinearTopology.nonarchimedeanRing T
  exact continuous_restrictedLift hφ _

/-- `restrictedLiftOfIsLinearTopology` extends `φ` on constants. -/
@[simp]
theorem restrictedLiftOfIsLinearTopology_algebraMap {φ : R →+* T} (hφ : Continuous φ)
    (b : Fin k → T) (r : R) :
    restrictedLiftOfIsLinearTopology hφ b (algebraMap R _ r) = φ r := by
  have := IsLinearTopology.isTopologicalRing (R := T)
  have := IsLinearTopology.nonarchimedeanRing T
  exact restrictedLift_algebraMap hφ _ r

/-- `restrictedLiftOfIsLinearTopology` sends each coordinate variable `Xᵢ` to `bᵢ`. -/
@[simp]
theorem restrictedLiftOfIsLinearTopology_X {φ : R →+* T} (hφ : Continuous φ)
    (b : Fin k → T) (i : Fin k) :
    restrictedLiftOfIsLinearTopology hφ b ⟨X i, isRestricted_X _ i⟩ = b i := by
  have := IsLinearTopology.isTopologicalRing (R := T)
  have := IsLinearTopology.nonarchimedeanRing T
  exact restrictedLift_X hφ _ i

/-- **Universal property of `R⟨X₁, …, Xₖ⟩` into complete Hausdorff linearly topologised rings.**
A continuous ring homomorphism `φ : R →+* T` extends uniquely to a continuous ring homomorphism
`R⟨X₁, …, Xₖ⟩ →+* T` sending each `Xᵢ` to an arbitrary `bᵢ ∈ T`. -/
theorem existsUnique_continuous_ringHom_isRestricted_subring_of_isLinearTopology
    {φ : R →+* T} (hφ : Continuous φ) (b : Fin k → T) :
    ∃! ψ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* T,
      Continuous ψ ∧ (∀ r, ψ (algebraMap R _ r) = φ r) ∧
        ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i := by
  have := IsLinearTopology.isTopologicalRing (R := T)
  have := IsLinearTopology.nonarchimedeanRing T
  exact existsUnique_continuous_ringHom_isRestricted_subring (b := b) hφ
    fun _ ↦ isPowerBounded_of_isLinearTopology _

/-- **Continuous `R`-algebra evaluation of `R⟨X₁, …, Xₖ⟩` into a complete Hausdorff linearly
topologised `R`-algebra**, at an arbitrary point `b : Fin k → T`. -/
noncomputable def restrictedLiftAlgHomOfIsLinearTopology [Algebra R T]
    (hφ : Continuous (algebraMap R T)) (b : Fin k → T) :
    IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →ₐ[R] T :=
  { restrictedLiftOfIsLinearTopology hφ b with
    commutes' := restrictedLiftOfIsLinearTopology_algebraMap hφ b }

/-- Underlying ring map of `restrictedLiftAlgHomOfIsLinearTopology`. -/
@[simp]
theorem coe_restrictedLiftAlgHomOfIsLinearTopology [Algebra R T]
    (hφ : Continuous (algebraMap R T)) (b : Fin k → T) :
    ⇑(restrictedLiftAlgHomOfIsLinearTopology hφ b) = ⇑(restrictedLiftOfIsLinearTopology hφ b) := by
  rfl

/-- `restrictedLiftAlgHomOfIsLinearTopology` is continuous. -/
theorem continuous_restrictedLiftAlgHomOfIsLinearTopology [Algebra R T]
    (hφ : Continuous (algebraMap R T)) (b : Fin k → T) :
    Continuous (restrictedLiftAlgHomOfIsLinearTopology hφ b) :=
  continuous_restrictedLiftOfIsLinearTopology hφ b

/-- `restrictedLiftAlgHomOfIsLinearTopology` sends each `Xᵢ` to `bᵢ`. -/
@[simp]
theorem restrictedLiftAlgHomOfIsLinearTopology_X [Algebra R T]
    (hφ : Continuous (algebraMap R T)) (b : Fin k → T) (i : Fin k) :
    restrictedLiftAlgHomOfIsLinearTopology hφ b ⟨X i, isRestricted_X _ i⟩ = b i :=
  restrictedLiftOfIsLinearTopology_X hφ b i

/-- **Universal property of `R⟨X₁, …, Xₖ⟩` for continuous `R`-algebra maps into a complete
Hausdorff linearly topologised `R`-algebra.** -/
theorem existsUnique_continuous_algHom_isRestricted_subring_of_isLinearTopology [Algebra R T]
    (hφ : Continuous (algebraMap R T)) (b : Fin k → T) :
    ∃! ψ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →ₐ[R] T,
      Continuous ψ ∧ ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i := by
  refine ⟨restrictedLiftAlgHomOfIsLinearTopology hφ b,
    ⟨continuous_restrictedLiftAlgHomOfIsLinearTopology hφ b,
      restrictedLiftAlgHomOfIsLinearTopology_X hφ b⟩, fun ψ ⟨hψ, hX⟩ ↦ ?_⟩
  apply AlgHom.toRingHom_injective
  have := IsLinearTopology.isTopologicalRing (R := T)
  have := IsLinearTopology.nonarchimedeanRing T
  exact restrictedLift_unique (b := b) hφ (fun _ ↦ isPowerBounded_of_isLinearTopology _) hψ
    ψ.commutes hX

end LinearTopology

end TauCeti.MvPowerSeries
