/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Topology.Algebra.UniformRing
public import TauCeti.RingTheory.AdicCompletion.Algebra
public import TauCeti.RingTheory.AdicCompletion.Noetherian
public import TauCeti.RingTheory.AdicRing.Basic

/-!
# The completed localisation of an adic ring

Let `A` be an adic ring of finite ideal type with ideal of definition `I`, and let `f ∈ A`. The
*completed localisation* `A_{f}` is the `I`-adic completion of the localisation `A_f` of `A` away
from `f`, with its `I A_{f}`-adic topology. It is the ring of sections of the formal spectrum
`Spf A` over the basic open set `D(f)`, and these rings are the building blocks of the structure
sheaf of `Spf A`.

The ring `A_{f}` is an adic ring of finite ideal type with ideal of definition `I A_{f}`. The
canonical map `A → A_{f}` is continuous and sends `f` to a unit, and it is universal with this
property among continuous ring homomorphisms into complete Hausdorff linearly topologised rings.
When `A` is noetherian, `A_{f}` is noetherian and flat over `A`.

The completion is formed with the chosen ideal of definition `TauCeti.IsAdicRing.ideal A`. The
image of `A` in `A_{f}` is not dense in general; the image of `A_f` is, and a continuous ring
homomorphism out of `A_{f}` is determined by its restriction to `A` because it preserves the
inverse of `f`.

## Main definitions

* `TauCeti.AdicRing.CompletedAway A f`: the completed localisation `A_{f}`, with the adic
  topology of `I A_{f}`.
* `TauCeti.AdicRing.CompletedAway.lift`: the continuous ring homomorphism `A_{f} → B` extending a
  continuous ring homomorphism `A → B` that sends `f` to a unit.

## Main results

* `TauCeti.AdicRing.CompletedAway.isAdicRing`: `A_{f}` is an adic ring of finite ideal type.
* `TauCeti.AdicRing.CompletedAway.continuous_algebraMap`,
  `TauCeti.AdicRing.CompletedAway.isUnit_algebraMap_self`: the canonical map `A → A_{f}` is
  continuous and sends `f` to a unit.
* `TauCeti.AdicRing.CompletedAway.denseRange_algebraMap`: the image of `A_f` is dense.
* `TauCeti.AdicRing.CompletedAway.ringHom_ext`: continuous ring homomorphisms out of `A_{f}` into
  a Hausdorff ring agreeing on `A` are equal.
* `TauCeti.AdicRing.CompletedAway.existsUnique_lift`: the universal property of `A_{f}`.
* `TauCeti.AdicRing.CompletedAway.isNoetherianRing`, `TauCeti.AdicRing.CompletedAway.flat`: for
  noetherian `A`, the ring `A_{f}` is noetherian and flat over `A`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.6
  (7.6.1, 7.6.2, 7.6.6, 7.6.11, 7.6.13 and 7.6.15).
-/

public section

namespace TauCeti.AdicRing

open Filter Topology

variable (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  (f : A)

/-- The **completed localisation** `A_{f}` of an adic ring `A` at `f`: the completion of the
localisation `A_f` along the extension of the chosen ideal of definition of `A`. -/
def CompletedAway : Type _ :=
  AdicCompletion ((IsAdicRing.ideal A).map (algebraMap A (Localization.Away f)))
    (Localization.Away f)

namespace CompletedAway

noncomputable instance : CommRing (CompletedAway A f) :=
  inferInstanceAs (CommRing
    (AdicCompletion ((IsAdicRing.ideal A).map (algebraMap A (Localization.Away f)))
      (Localization.Away f)))

noncomputable instance : Algebra (Localization.Away f) (CompletedAway A f) :=
  inferInstanceAs (Algebra (Localization.Away f)
    (AdicCompletion ((IsAdicRing.ideal A).map (algebraMap A (Localization.Away f)))
      (Localization.Away f)))

noncomputable instance : Algebra A (CompletedAway A f) :=
  inferInstanceAs (Algebra A
    (AdicCompletion ((IsAdicRing.ideal A).map (algebraMap A (Localization.Away f)))
      (Localization.Away f)))

instance : IsScalarTower A (Localization.Away f) (CompletedAway A f) :=
  inferInstanceAs (IsScalarTower A (Localization.Away f)
    (AdicCompletion ((IsAdicRing.ideal A).map (algebraMap A (Localization.Away f)))
      (Localization.Away f)))

/-- The completed localisation carries the adic topology of the extension `I A_{f}` of the chosen
ideal of definition `I` of `A`. -/
noncomputable instance : WithIdeal (CompletedAway A f) :=
  ⟨(IsAdicRing.ideal A).map (algebraMap A (CompletedAway A f))⟩

/-- The topology of `A_{f}` is the adic topology of the extension of the chosen ideal of
definition of `A`. -/
theorem isAdic : IsAdic ((IsAdicRing.ideal A).map (algebraMap A (CompletedAway A f))) :=
  rfl

/-- The ideal of definition `I A_{f}` is also the extension of `I A_f` along `A_f → A_{f}`. -/
private theorem map_algebraMap_eq :
    (IsAdicRing.ideal A).map (algebraMap A (CompletedAway A f)) =
      ((IsAdicRing.ideal A).map (algebraMap A (Localization.Away f))).map
        (algebraMap (Localization.Away f) (CompletedAway A f)) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

private theorem fg_map : ((IsAdicRing.ideal A).map (algebraMap A (Localization.Away f))).FG :=
  (IsAdicRing.ideal_spec A).1.map _

/-- The completed localisation of an adic ring of finite ideal type is again an adic ring of
finite ideal type, with ideal of definition `I A_{f}`. -/
instance isAdicRing : IsAdicRing (CompletedAway A f) := by
  refine ⟨⟨_, (IsAdicRing.ideal_spec A).1.map _, isAdic A f, ?_⟩⟩
  rw [map_algebraMap_eq]
  exact AdicCompletion.isAdicComplete_self _ (fg_map A f)

/-- The canonical map from an adic ring to its completed localisation is continuous. -/
theorem continuous_algebraMap : Continuous (algebraMap A (CompletedAway A f)) :=
  IsAdic.continuous_of_map_le_radical (IsAdicRing.ideal_spec A).2.1 (isAdic A f)
    (IsAdicRing.ideal_spec A).1 Ideal.le_radical

/-- The canonical map from an adic ring to its completed localisation at `f` sends `f` to a
unit. -/
theorem isUnit_algebraMap_self : IsUnit (algebraMap A (CompletedAway A f) f) := by
  rw [IsScalarTower.algebraMap_apply A (Localization.Away f)]
  exact (IsLocalization.Away.algebraMap_isUnit f).map _

/-- An element of `A_f` maps into the `n`-th power of the ideal of definition of `A_{f}` if and
only if it lies in the `n`-th power of `I A_f`. -/
theorem algebraMap_mem_pow_iff (n : ℕ) {x : Localization.Away f} :
    algebraMap (Localization.Away f) (CompletedAway A f) x ∈
        (IsAdicRing.ideal A).map (algebraMap A (CompletedAway A f)) ^ n ↔
      x ∈ (IsAdicRing.ideal A).map (algebraMap A (Localization.Away f)) ^ n := by
  rw [map_algebraMap_eq, ← Ideal.map_pow]
  exact AdicCompletion.algebraMap_mem_map_pow_iff (fg_map A f) n

/-- The image of `A_f` in the completed localisation `A_{f}` is dense. -/
theorem denseRange_algebraMap :
    DenseRange (algebraMap (Localization.Away f) (CompletedAway A f)) := by
  refine fun x ↦ mem_closure_iff_nhds.mpr fun U hU ↦ ?_
  obtain ⟨n, -, hn⟩ := ((isAdic A f).hasBasis_nhds x).mem_iff.mp hU
  obtain ⟨y, hy⟩ : ∃ y, x - algebraMap (Localization.Away f) (CompletedAway A f) y ∈
      (IsAdicRing.ideal A).map (algebraMap A (CompletedAway A f)) ^ n := by
    rw [map_algebraMap_eq, ← Ideal.map_pow]
    exact AdicCompletion.exists_sub_algebraMap_mem_map_pow (fg_map A f) n x
  refine ⟨_, hn ⟨_, neg_mem hy, ?_⟩, y, rfl⟩
  simp only [neg_sub, add_sub_cancel]

/-- Two continuous ring homomorphisms out of the completed localisation `A_{f}` into a Hausdorff
ring are equal as soon as they agree on the image of `A`. -/
theorem ringHom_ext {B : Type*} [Semiring B] [TopologicalSpace B] [T2Space B]
    {g₁ g₂ : CompletedAway A f →+* B} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (h : g₁.comp (algebraMap A (CompletedAway A f)) =
      g₂.comp (algebraMap A (CompletedAway A f))) :
    g₁ = g₂ := by
  have hloc : g₁.comp (algebraMap (Localization.Away f) (CompletedAway A f)) =
      g₂.comp (algebraMap (Localization.Away f) (CompletedAway A f)) :=
    IsLocalization.ringHom_ext (Submonoid.powers f) <| by
      simpa only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq] using h
  exact RingHom.ext <| congrFun <|
    (denseRange_algebraMap A f).equalizer hg₁ hg₂ (congrArg DFunLike.coe hloc)

variable {A f}
variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [IsLinearTopology B B] [CompleteSpace B] [T2Space B]

/-- The uniform structure on `A_f` induced from the completed localisation; it is the
`I A_f`-adic uniform structure. -/
private noncomputable abbrev uniformSpaceAway : UniformSpace (Localization.Away f) :=
  UniformSpace.comap (algebraMap (Localization.Away f) (CompletedAway A f)) inferInstance

private theorem isUniformInducing_algebraMap :
    letI := uniformSpaceAway (A := A) (f := f)
    IsUniformInducing (algebraMap (Localization.Away f) (CompletedAway A f)) :=
  letI := uniformSpaceAway (A := A) (f := f)
  ⟨rfl⟩

omit [IsTopologicalRing B] [CompleteSpace B] [T2Space B] in
/-- The extension `A_f → B` of a continuous ring homomorphism `u : A → B` with `u f` a unit is
uniformly continuous for the uniform structure induced from `A_{f}`. -/
private theorem uniformContinuous_awayLift {u : A →+* B} (hu : Continuous u)
    (hf : IsUnit (u f)) :
    letI := uniformSpaceAway (A := A) (f := f)
    UniformContinuous (IsLocalization.Away.lift f hf : Localization.Away f →+* B) := by
  let := uniformSpaceAway (A := A) (f := f)
  have : IsUniformAddGroup (Localization.Away f) := IsUniformAddGroup.comap _
  refine uniformContinuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, isUniformInducing_algebraMap.isInducing.nhds_eq_comap, map_zero,
    ((isAdic A f).hasBasis_nhds_zero.comap _).tendsto_iff IsLinearTopology.hasBasis_ideal]
  intro V hV
  -- some power of `I` is carried into the open ideal `V` by `u`
  obtain ⟨n, -, hn⟩ := (IsAdicRing.ideal_spec A).2.1.hasBasis_nhds_zero.mem_iff.mp
    (hu.continuousAt.preimage_mem_nhds (by simpa using hV))
  refine ⟨n, trivial, fun x hx ↦ ?_⟩
  have hx : x ∈ ((IsAdicRing.ideal A) ^ n).map (algebraMap A (Localization.Away f)) := by
    rw [Ideal.map_pow]
    exact (algebraMap_mem_pow_iff A f n).mp hx
  have hle : ((IsAdicRing.ideal A) ^ n).map (algebraMap A (Localization.Away f)) ≤
      V.comap (IsLocalization.Away.lift f hf) :=
    Ideal.map_le_iff_le_comap.mpr fun a ha ↦ by simpa [IsLocalization.Away.lift_eq] using hn ha
  exact hle hx

/-- The **universal property of the completed localisation**: a continuous ring homomorphism
`u : A → B` into a complete Hausdorff linearly topologised ring with `u f` a unit extends to a
continuous ring homomorphism `A_{f} → B`. -/
noncomputable def lift (u : A →+* B) (hu : Continuous u) (hf : IsUnit (u f)) :
    CompletedAway A f →+* B :=
  letI := uniformSpaceAway (A := A) (f := f)
  IsDenseInducing.extendRingHom isUniformInducing_algebraMap (denseRange_algebraMap A f)
    (uniformContinuous_awayLift hu hf)

/-- The extension `CompletedAway.lift u` of `u` is continuous. -/
theorem continuous_lift (u : A →+* B) (hu : Continuous u) (hf : IsUnit (u f)) :
    Continuous (lift u hu hf) :=
  letI := uniformSpaceAway (A := A) (f := f)
  (uniformContinuous_uniformly_extend isUniformInducing_algebraMap (denseRange_algebraMap A f)
    (uniformContinuous_awayLift hu hf)).continuous

/-- On the image of `A_f`, the extension `CompletedAway.lift u` is the extension of `u` to the
localisation `A_f`. -/
@[simp]
theorem lift_algebraMap_away (u : A →+* B) (hu : Continuous u) (hf : IsUnit (u f))
    (x : Localization.Away f) :
    lift u hu hf (algebraMap (Localization.Away f) (CompletedAway A f) x) =
      IsLocalization.Away.lift f hf x :=
  letI := uniformSpaceAway (A := A) (f := f)
  (isUniformInducing_algebraMap.isDenseInducing (denseRange_algebraMap A f)).extend_eq
    (uniformContinuous_awayLift hu hf).continuous x

/-- The extension `CompletedAway.lift u` restricts to `u` on `A`. -/
@[simp]
theorem lift_algebraMap (u : A →+* B) (hu : Continuous u) (hf : IsUnit (u f)) (a : A) :
    lift u hu hf (algebraMap A (CompletedAway A f) a) = u a := by
  rw [IsScalarTower.algebraMap_apply A (Localization.Away f), lift_algebraMap_away,
    IsLocalization.Away.lift_eq]

/-- The extension `CompletedAway.lift u` composed with `A → A_{f}` is `u`. -/
theorem lift_comp_algebraMap (u : A →+* B) (hu : Continuous u) (hf : IsUnit (u f)) :
    (lift u hu hf).comp (algebraMap A (CompletedAway A f)) = u :=
  RingHom.ext (lift_algebraMap u hu hf)

/-- The **universal property of the completed localisation**: a continuous ring homomorphism
`u : A → B` into a complete Hausdorff linearly topologised ring with `u f` a unit factors
uniquely through a continuous ring homomorphism `A_{f} → B`. -/
theorem existsUnique_lift (u : A →+* B) (hu : Continuous u) (hf : IsUnit (u f)) :
    ∃! g : CompletedAway A f →+* B,
      Continuous g ∧ g.comp (algebraMap A (CompletedAway A f)) = u :=
  ⟨lift u hu hf, ⟨continuous_lift u hu hf, lift_comp_algebraMap u hu hf⟩,
    fun _ hg ↦ ringHom_ext A f hg.1 (continuous_lift u hu hf)
      (hg.2.trans (lift_comp_algebraMap u hu hf).symm)⟩

variable (A f)

/-- The completed localisation of a noetherian adic ring is noetherian. -/
instance isNoetherianRing [IsNoetherianRing A] : IsNoetherianRing (CompletedAway A f) :=
  Ideal.isNoetherianRing_adicCompletion
    (I := (IsAdicRing.ideal A).map (algebraMap A (Localization.Away f)))

/-- The completed localisation of a noetherian adic ring is flat over it. -/
instance flat [IsNoetherianRing A] : Module.Flat A (CompletedAway A f) :=
  have : Module.Flat (Localization.Away f) (CompletedAway A f) :=
    AdicCompletion.flat_of_isNoetherian
      (I := (IsAdicRing.ideal A).map (algebraMap A (Localization.Away f)))
  have : Module.Flat A (Localization.Away f) := IsLocalization.flat _ (Submonoid.powers f)
  Module.Flat.trans A (Localization.Away f) (CompletedAway A f)

end CompletedAway

end TauCeti.AdicRing
