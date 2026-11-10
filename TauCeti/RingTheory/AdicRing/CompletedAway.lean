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
public import TauCeti.RingTheory.AdicCompletion.IdealIndependence
public import TauCeti.RingTheory.AdicCompletion.Noetherian
public import TauCeti.RingTheory.AdicRing.Basic

import TauCeti.RingTheory.Ideal.Maps
import TauCeti.RingTheory.Localization.Away.Quotient

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
When `A` is noetherian, `A_{f}` is noetherian and flat over `A`. Modulo `I ^ n` nothing is
completed: `A_{f} ⧸ I ^ n A_{f}` is the localisation of `A ⧸ I ^ n` away from the image of `f`,
the ring of sections over `D(f)` of the thickening `Spec (A ⧸ I ^ n)`. This identifies the
reductions of `A_{f}` with the sections of the thickenings that define the formal spectrum.

For `g` in the radical of `f A + I`, that is, when `f` divides a power of `g` modulo `I` (so that
`D(g) ⊆ D(f)` in the formal spectrum), the image of `f` in `A_{g}` is a unit, and the universal
property gives the restriction map `A_{f} → A_{g}`. Conversely `f` becomes a unit in `A_{g}` only
for such `g`, so there is no `A`-algebra homomorphism `A_{f} → A_{g}` otherwise. The restriction
maps are the restriction maps of the structure sheaf of `Spf A` on basic open sets.

The completion is formed with the chosen ideal of definition `TauCeti.IsAdicRing.ideal A`. The
image of `A` in `A_{f}` is not dense in general; the image of `A_f` is, and a continuous ring
homomorphism out of `A_{f}` is determined by its restriction to `A` because it preserves the
inverse of `f`. The comparison `CompletedAway.idealEquiv` identifies it bicontinuously with
the completion formed using any other finitely generated ideal of definition, fixing every
element of the ordinary localisation. Thus the basic-open section rings depend only on the
topology, not on the chosen ideal of definition.

## Main definitions

* `TauCeti.AdicRing.CompletedAway A f`: the completed localisation `A_{f}`, with the adic
  topology of `I A_{f}`.
* `TauCeti.AdicRing.CompletedAway.lift`: the continuous ring homomorphism `A_{f} → B` extending a
  continuous ring homomorphism `A → B` that sends `f` to a unit.
* `TauCeti.AdicRing.CompletedAway.quotientPowEquiv`: the isomorphism of `A`-algebras
  `A_{f} ⧸ I ^ n A_{f} ≃ (A ⧸ I ^ n)_f`.
* `TauCeti.AdicRing.CompletedAway.restrict`: the restriction map `A_{f} → A_{g}` for `g` in the
  radical of `f A + I`.

## Main results

* `TauCeti.AdicRing.CompletedAway.isAdicRing`: `A_{f}` is an adic ring of finite ideal type.
* `TauCeti.AdicRing.CompletedAway.continuous_algebraMap`,
  `TauCeti.AdicRing.CompletedAway.isUnit_algebraMap_self`: the canonical map `A → A_{f}` is
  continuous and sends `f` to a unit.
* `TauCeti.AdicRing.CompletedAway.denseRange_algebraMap`: the image of `A_f` is dense.
* `TauCeti.AdicRing.CompletedAway.exists_sub_mem_map`: every element of `A_{f}` is congruent
  modulo `I A_{f}` to an element of `A_f`.
* `TauCeti.AdicRing.CompletedAway.ringHom_ext`: continuous ring homomorphisms out of `A_{f}` into
  a Hausdorff ring agreeing on `A` are equal.
* `TauCeti.AdicRing.CompletedAway.existsUnique_lift`: the universal property of `A_{f}`.
* `TauCeti.AdicRing.CompletedAway.isNoetherianRing`, `TauCeti.AdicRing.CompletedAway.flat`: for
  noetherian `A`, the ring `A_{f}` is noetherian and flat over `A`.
* `TauCeti.AdicRing.CompletedAway.quotientPowEquiv_algebraMap`: the isomorphism
  `quotientPowEquiv` is induced by the reduction `A_f → (A ⧸ I ^ n)_f`.
* `TauCeti.AdicRing.CompletedAway.quotient_algHom_subsingleton`: there is at most one
  `A`-algebra homomorphism out of `A_{f} ⧸ I ^ n A_{f}`, so `quotientPowEquiv` is the unique
  isomorphism and, for `m ≤ n`, is compatible with the reduction from `I ^ n` to `I ^ m`.
* `TauCeti.AdicRing.CompletedAway.algHom_ext_of_map_pow_eq_bot`,
  `TauCeti.AdicRing.CompletedAway.algHom_ext_adicCompletion`: an `A`-algebra homomorphism out of
  `A_{f}` is unique if its target is killed by a power of `I`, or is the adic completion of an
  `A`-algebra `B` along an ideal containing `I B`; no continuity is required.
* `TauCeti.AdicRing.CompletedAway.isUnit_algebraMap_iff`: `f` is a unit in `A_{g}` if and only if
  `g` lies in the radical of `f A + I`.
* `TauCeti.AdicRing.CompletedAway.subsingleton_iff`: `A_{f}` is the zero ring if and only if `f`
  is nilpotent modulo `I`.
* `TauCeti.AdicRing.CompletedAway.restrict_unique`, `TauCeti.AdicRing.CompletedAway.restrict_self`,
  `TauCeti.AdicRing.CompletedAway.restrict_comp_restrict`: the restriction map is the unique
  continuous `A`-algebra homomorphism, and restriction maps satisfy the identity and composition
  laws.
* `TauCeti.AdicRing.CompletedAway.nonempty_algHom_iff`: there is an `A`-algebra homomorphism
  `A_{f} → A_{g}` if and only if `g` lies in the radical of `f A + I`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0,
  §§7.1.8–7.1.9 and §7.6 (7.6.1, 7.6.2, 7.6.6, 7.6.11, 7.6.13 and 7.6.15).
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

/-- The completed localisation `A_{f}` is, by definition, the adic completion of `A_f` along
`I A_f`; this is that identification as an isomorphism of `A_f`-algebras. -/
noncomputable def equivAdicCompletion :
    CompletedAway A f ≃ₐ[Localization.Away f]
      AdicCompletion ((IsAdicRing.ideal A).map (algebraMap A (Localization.Away f)))
        (Localization.Away f) :=
  AlgEquiv.refl

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
@[simp]
theorem algebraMap_mem_pow_iff (n : ℕ) {x : Localization.Away f} :
    algebraMap (Localization.Away f) (CompletedAway A f) x ∈
        (IsAdicRing.ideal A).map (algebraMap A (CompletedAway A f)) ^ n ↔
      x ∈ (IsAdicRing.ideal A).map (algebraMap A (Localization.Away f)) ^ n := by
  rw [map_algebraMap_eq, ← Ideal.map_pow]
  exact AdicCompletion.algebraMap_mem_map_pow_iff n

/-- The image of `A_f` in the completed localisation `A_{f}` is dense. -/
theorem denseRange_algebraMap :
    DenseRange (algebraMap (Localization.Away f) (CompletedAway A f)) :=
  letI : TopologicalSpace (AdicCompletion ((IsAdicRing.ideal A).map
      (algebraMap A (Localization.Away f))) (Localization.Away f)) :=
    inferInstanceAs (TopologicalSpace (CompletedAway A f))
  AdicCompletion.denseRange_algebraMap (fg_map A f) (map_algebraMap_eq A f ▸ isAdic A f)

/-- Every element of the completed localisation `A_{f}` is congruent modulo `I A_{f}` to the image
of an element of `A_f`. -/
theorem exists_sub_mem_map (x : CompletedAway A f) :
    ∃ y : Localization.Away f, x - algebraMap (Localization.Away f) (CompletedAway A f) y ∈
      (IsAdicRing.ideal A).map (algebraMap A (CompletedAway A f)) := by
  rw [map_algebraMap_eq, ← pow_one (Ideal.map _ (IsAdicRing.ideal A))]
  exact AdicCompletion.exists_sub_algebraMap_mem_map_pow (fg_map A f) 1 x

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

omit [IsTopologicalRing B] in
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
@[simp]
theorem lift_comp_algebraMap (u : A →+* B) (hu : Continuous u) (hf : IsUnit (u f)) :
    (lift u hu hf).comp (algebraMap A (CompletedAway A f)) = u :=
  RingHom.ext (lift_algebraMap u hu hf)

/-- The **universal property of the completed localisation**: a continuous ring homomorphism
`u : A → B` into a complete Hausdorff linearly topologised ring with `u f` a unit factors
uniquely through a continuous ring homomorphism `A_{f} → B`. -/
theorem existsUnique_lift (u : A →+* B) (hu : Continuous u) (hf : IsUnit (u f)) :
    ∃! g : CompletedAway A f →+* B,
      Continuous g ∧ g.comp (algebraMap A (CompletedAway A f)) = u := by
  -- A linearly topologised commutative ring with a topological additive group has continuous
  -- multiplication.
  have hl (x₀ : B) : Tendsto (fun x : B ↦ x₀ * x) (𝓝 0) (𝓝 0) :=
    IsLinearTopology.tendsto_mul_zero_of_right (R := B) (f := 𝓝 0) (fun _ ↦ x₀) id tendsto_id
  have : IsTopologicalRing B := IsTopologicalRing.of_addGroup_of_nhds_zero
    (IsLinearTopology.tendsto_mul_zero_of_right (R := B) (f := 𝓝 0 ×ˢ 𝓝 0) Prod.fst Prod.snd
      tendsto_snd)
    hl fun x₀ ↦ (hl x₀).congr fun x ↦ mul_comm _ _
  exact ⟨lift u hu hf, ⟨continuous_lift u hu hf, lift_comp_algebraMap u hu hf⟩,
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

section Quotient

/-- Modulo `I ^ n`, the completed localisation is the ordinary localisation:
`A_{f} ⧸ I ^ n A_{f}` is isomorphic as an `A`-algebra to the localisation of `A ⧸ I ^ n` away from
the image of `f` (EGA I, Ch. 0, 7.6.2 and 7.6.15). -/
noncomputable def quotientPowEquiv (n : ℕ) :
    (CompletedAway A f ⧸ (IsAdicRing.ideal A).map (algebraMap A (CompletedAway A f)) ^ n) ≃ₐ[A]
      Localization.Away (Ideal.Quotient.mk (IsAdicRing.ideal A ^ n) f) :=
  (((Ideal.quotientEquivAlgOfEq (Localization.Away f)
    (J := ((IsAdicRing.ideal A).map (algebraMap A (Localization.Away f)) ^ n).map
      (algebraMap (Localization.Away f) (CompletedAway A f)))
    (by rw [map_algebraMap_eq, ← Ideal.map_pow])).trans
    ((AdicCompletion.quotientMapPowAlgEquiv (fg_map A f) n).trans
      (Ideal.quotientEquivAlgOfEq (Localization.Away f)
        (Ideal.map_pow _ _ _).symm))).restrictScalars A).trans
    ((IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk (IsAdicRing.ideal A ^ n) f))
      (Localization.Away f ⧸ (IsAdicRing.ideal A ^ n).map (algebraMap A (Localization.Away f)))
      (Localization.Away (Ideal.Quotient.mk (IsAdicRing.ideal A ^ n) f))).restrictScalars A)

/-- On the image of `A_f`, the isomorphism `A_{f} ⧸ I ^ n A_{f} ≃ (A ⧸ I ^ n)_f` is the map
`A_f → (A ⧸ I ^ n)_f` induced by the reduction `A → A ⧸ I ^ n`. -/
@[simp]
theorem quotientPowEquiv_algebraMap (n : ℕ) (x : Localization.Away f) :
    quotientPowEquiv A f n (algebraMap (Localization.Away f)
        (CompletedAway A f ⧸ (IsAdicRing.ideal A).map (algebraMap A (CompletedAway A f)) ^ n) x) =
      Localization.awayMap (Ideal.Quotient.mk (IsAdicRing.ideal A ^ n)) f x := by
  -- both sides are ring homomorphisms out of `A_f` agreeing on `A`
  have h := IsLocalization.ringHom_ext (Submonoid.powers f)
    (j := (quotientPowEquiv A f n).toRingHom.comp (algebraMap (Localization.Away f)
      (CompletedAway A f ⧸ (IsAdicRing.ideal A).map (algebraMap A (CompletedAway A f)) ^ n)))
    (k := Localization.awayMap (Ideal.Quotient.mk (IsAdicRing.ideal A ^ n)) f)
    (RingHom.ext fun a ↦ ?_)
  · exact congr($h x)
  · simp [← IsScalarTower.algebraMap_apply, IsLocalization.Away.map,
      IsScalarTower.algebraMap_apply A (A ⧸ IsAdicRing.ideal A ^ n)]

/-- There is at most one `A`-algebra homomorphism out of `A_{f} ⧸ I ^ n A_{f}`: it is a
localisation of a quotient of `A`. In particular `quotientPowEquiv` is the only `A`-algebra
isomorphism `A_{f} ⧸ I ^ n A_{f} ≃ (A ⧸ I ^ n)_f`, and these isomorphisms are compatible with the
reductions from `I ^ n` to `I ^ m` for `m ≤ n`. -/
instance quotient_algHom_subsingleton (n : ℕ) {B : Type*} [Semiring B] [Algebra A B] :
    Subsingleton ((CompletedAway A f ⧸
      (IsAdicRing.ideal A).map (algebraMap A (CompletedAway A f)) ^ n) →ₐ[A] B) := by
  refine ⟨fun g₁ g₂ ↦ AlgHom.ext fun x ↦ ?_⟩
  obtain ⟨y, rfl⟩ := (quotientPowEquiv A f n).symm.surjective x
  -- transported to `(A ⧸ I ^ n)_f`, both maps are ring homomorphisms agreeing on `A`
  have h := IsLocalization.ringHom_ext
    (Submonoid.powers (Ideal.Quotient.mk (IsAdicRing.ideal A ^ n) f))
    (j := (g₁.comp (quotientPowEquiv A f n).symm.toAlgHom).toRingHom)
    (k := (g₂.comp (quotientPowEquiv A f n).symm.toAlgHom).toRingHom)
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ ?_))
  · exact congr($h y)
  · simp [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

variable {A f} in
/-- An `A`-algebra homomorphism out of `A_{f}` into an `A`-algebra in which `I ^ n` vanishes is
unique: it factors through `A_{f} ⧸ I ^ n A_{f}`, out of which there is at most one `A`-algebra
homomorphism. No topology on the target is needed. -/
theorem algHom_ext_of_map_pow_eq_bot {B : Type*} [Semiring B] [Algebra A B] {n : ℕ}
    (h : (IsAdicRing.ideal A ^ n).map (algebraMap A B) = ⊥) (g₁ g₂ : CompletedAway A f →ₐ[A] B) :
    g₁ = g₂ := by
  have hker (g : CompletedAway A f →ₐ[A] B) (x : CompletedAway A f)
      (hx : x ∈ (IsAdicRing.ideal A).map (algebraMap A (CompletedAway A f)) ^ n) : g x = 0 := by
    rw [← Ideal.map_pow] at hx
    exact (Ideal.map_eq_bot_iff_le_ker g).mp ((Ideal.map_map_algebraMap g _).trans h) hx
  ext x
  exact congr($(Subsingleton.elim (Ideal.Quotient.liftₐ _ g₁ (hker g₁))
    (Ideal.Quotient.liftₐ _ g₂ (hker g₂))) (Ideal.Quotient.mk _ x))

variable {A f} in
/-- An `A`-algebra homomorphism out of `A_{f}` into the adic completion of an `A`-algebra `B` along
an ideal containing `I B` is unique. -/
theorem algHom_ext_adicCompletion {B : Type*} [CommRing B] [Algebra A B] {K : Ideal B}
    (hK : (IsAdicRing.ideal A).map (algebraMap A B) ≤ K)
    (g₁ g₂ : CompletedAway A f →ₐ[A] AdicCompletion K B) : g₁ = g₂ := by
  -- modulo `K ^ n`, the two homomorphisms land in a ring in which `I ^ n` vanishes
  refine AlgHom.ext fun x ↦ AdicCompletion.ext_evalₐ fun n ↦ ?_
  have h : (IsAdicRing.ideal A ^ n).map (algebraMap A (B ⧸ K ^ n)) = ⊥ := by
    rw [IsScalarTower.algebraMap_eq A B, ← Ideal.map_map, Ideal.Quotient.algebraMap_eq,
      eq_bot_iff, ← Ideal.map_quotient_self (K ^ n), Ideal.map_pow]
    exact Ideal.map_mono (Ideal.pow_right_mono hK n)
  exact congr($(algHom_ext_of_map_pow_eq_bot h (((AdicCompletion.evalₐ K n).restrictScalars A).comp
    g₁) (((AdicCompletion.evalₐ K n).restrictScalars A).comp g₂)) x)

end Quotient

section Restriction

variable {A f} {g k : A}

/-- If `g` lies in the radical of `f A + I`, that is if `f` divides a power of `g` modulo the
ideal of definition `I`, then `f` becomes a unit in the completed localisation `A_{g}`. -/
theorem isUnit_algebraMap_of_mem_radical
    (h : g ∈ (Ideal.span {f} ⊔ IsAdicRing.ideal A).radical) :
    IsUnit (algebraMap A (CompletedAway A g) f) := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨a, i, hi, hai⟩ := Ideal.mem_span_singleton_sup.mp hn
  have := (isAdic A g).isAdicComplete
  -- the image of `i` lies in the ideal of definition of `A_{g}`, hence in its Jacobson radical
  have hi' :=
    IsAdicComplete.le_jacobson _ (Ideal.mem_map_of_mem (algebraMap A (CompletedAway A g)) hi)
  obtain ⟨u, hu⟩ := (isUnit_algebraMap_self A g).pow n
  have hunit := Ring.mem_jacobson_iff.mp (neg_mem hi') ↑u⁻¹
  have hai' := congrArg (algebraMap A (CompletedAway A g)) hai
  rw [map_add, map_mul, map_pow, ← hu] at hai'
  refine isUnit_of_mul_isUnit_right (x := algebraMap A (CompletedAway A g) a) ?_
  have : algebraMap A (CompletedAway A g) a * algebraMap A (CompletedAway A g) f =
      u * (-algebraMap A (CompletedAway A g) i * ↑u⁻¹ + 1) := by
    linear_combination hai' + algebraMap A (CompletedAway A g) i * u.mul_inv
  rw [this]
  exact u.isUnit.mul hunit

/-- If `f` becomes a unit in the completed localisation `A_{g}`, then `g` lies in the radical of
`f A + I`. -/
theorem mem_radical_of_isUnit_algebraMap
    (h : IsUnit (algebraMap A (CompletedAway A g) f)) :
    g ∈ (Ideal.span {f} ⊔ IsAdicRing.ideal A).radical := by
  set J := (IsAdicRing.ideal A).map (algebraMap A (Localization.Away g))
  set K := Ideal.span {f} ⊔ IsAdicRing.ideal A
  -- approximate the inverse `v` of `f` in `A_{g}` modulo `I A_{g}` by some `y ∈ A_g`
  obtain ⟨v, hv⟩ := h.exists_right_inv
  obtain ⟨y, hy⟩ := exists_sub_mem_map A g v
  -- then `f y - 1` lies in `I A_g`
  have hfy : algebraMap A (Localization.Away g) f * y - 1 ∈ J := by
    rw [← pow_one J, ← algebraMap_mem_pow_iff A g 1, pow_one]
    have : algebraMap (Localization.Away g) (CompletedAway A g)
        (algebraMap A (Localization.Away g) f * y - 1) =
          -algebraMap A (CompletedAway A g) f *
            (v - algebraMap (Localization.Away g) (CompletedAway A g) y) := by
      rw [map_sub, map_mul, map_one, ← IsScalarTower.algebraMap_apply]
      linear_combination hv
    exact this ▸ Ideal.mul_mem_left _ _ hy
  -- hence `f A + I` generates the unit ideal of `A_g`
  have htop : K.map (algebraMap A (Localization.Away g)) = ⊤ := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.eq_top_iff_one]
    exact Ideal.mem_span_singleton_sup.mpr ⟨y, _, neg_mem hfy, by ring⟩
  by_contra hg
  refine (IsLocalization.map_algebraMap_ne_top_iff_disjoint (Submonoid.powers g)
    (Localization.Away g) K.radical).mpr
    ((Ideal.disjoint_powers_iff_notMem g K.radical_isRadical).mpr hg) (top_unique ?_)
  exact htop ▸ Ideal.map_mono Ideal.le_radical

/-- The image of `f` in the completed localisation `A_{g}` is a unit if and only if `g` lies in
the radical of `f A + I`. -/
theorem isUnit_algebraMap_iff :
    IsUnit (algebraMap A (CompletedAway A g) f) ↔
      g ∈ (Ideal.span {f} ⊔ IsAdicRing.ideal A).radical :=
  ⟨mem_radical_of_isUnit_algebraMap, isUnit_algebraMap_of_mem_radical⟩

/-- The completed localisation `A_{f}` is the zero ring if and only if `f` lies in the radical of
the ideal of definition, that is, if and only if `f` is nilpotent modulo `I`. -/
theorem subsingleton_iff :
    Subsingleton (CompletedAway A f) ↔ f ∈ (IsAdicRing.ideal A).radical := by
  rw [← subsingleton_iff_zero_eq_one, ← isUnit_zero_iff, ← map_zero (algebraMap A _),
    isUnit_algebraMap_iff, Ideal.span_singleton_eq_bot.mpr rfl, bot_sup_eq]

/-- Two continuous `A`-algebra homomorphisms out of the completed localisation `A_{f}` into a
Hausdorff topological `A`-algebra are equal. -/
theorem algHom_ext {B : Type*} [Semiring B] [Algebra A B] [TopologicalSpace B]
    [T2Space B] {g₁ g₂ : CompletedAway A f →ₐ[A] B} (hg₁ : Continuous g₁)
    (hg₂ : Continuous g₂) :
    g₁ = g₂ :=
  AlgHom.toRingHom_injective <| ringHom_ext A f hg₁ hg₂ <| by
    rw [AlgHom.comp_algebraMap, AlgHom.comp_algebraMap]

/-- The **restriction map** `A_{f} → A_{g}` of completed localisations, for `g` in the radical of
`f A + I`, that is, for `D(g) ⊆ D(f)` in the formal spectrum. It is the unique continuous
`A`-algebra homomorphism `A_{f} → A_{g}`, see `CompletedAway.restrict_unique`. -/
noncomputable def restrict (h : g ∈ (Ideal.span {f} ⊔ IsAdicRing.ideal A).radical) :
    CompletedAway A f →ₐ[A] CompletedAway A g where
  toRingHom := lift (algebraMap A (CompletedAway A g)) (continuous_algebraMap A g)
    (isUnit_algebraMap_of_mem_radical h)
  commutes' := lift_algebraMap _ _ _

/-- The restriction map of completed localisations is continuous. -/
theorem continuous_restrict (h : g ∈ (Ideal.span {f} ⊔ IsAdicRing.ideal A).radical) :
    Continuous (restrict h) :=
  continuous_lift _ (continuous_algebraMap A g) _

/-- The restriction map of completed localisations is the unique continuous `A`-algebra
homomorphism `A_{f} → A_{g}`. -/
theorem restrict_unique (h : g ∈ (Ideal.span {f} ⊔ IsAdicRing.ideal A).radical)
    {φ : CompletedAway A f →ₐ[A] CompletedAway A g} (hφ : Continuous φ) :
    φ = restrict h :=
  algHom_ext hφ (continuous_restrict h)

/-- There is an `A`-algebra homomorphism `A_{f} → A_{g}` if and only if `g` lies in the radical
of `f A + I`, so restriction maps exist only in the direction `D(g) ⊆ D(f)`. -/
theorem nonempty_algHom_iff :
    Nonempty (CompletedAway A f →ₐ[A] CompletedAway A g) ↔
      g ∈ (Ideal.span {f} ⊔ IsAdicRing.ideal A).radical :=
  ⟨fun ⟨φ⟩ ↦ mem_radical_of_isUnit_algebraMap <| by
    simpa using (isUnit_algebraMap_self A f).map φ, fun h ↦ ⟨restrict h⟩⟩

/-- The restriction map from `A_{f}` to itself is the identity. -/
@[simp]
theorem restrict_self (h : f ∈ (Ideal.span {f} ⊔ IsAdicRing.ideal A).radical) :
    restrict h = AlgHom.id A (CompletedAway A f) :=
  (restrict_unique h continuous_id).symm

/-- Restriction maps of completed localisations compose: for `D(k) ⊆ D(g) ⊆ D(f)`, restricting
from `A_{f}` to `A_{g}` and then to `A_{k}` is restricting from `A_{f}` to `A_{k}`. -/
theorem restrict_comp_restrict
    (hfg : g ∈ (Ideal.span {f} ⊔ IsAdicRing.ideal A).radical)
    (hgk : k ∈ (Ideal.span {g} ⊔ IsAdicRing.ideal A).radical)
    (hfk : k ∈ (Ideal.span {f} ⊔ IsAdicRing.ideal A).radical) :
    (restrict hgk).comp (restrict hfg) = restrict hfk :=
  restrict_unique hfk ((continuous_restrict hgk).comp (continuous_restrict hfg))

/-- Restriction maps of completed localisations compose, evaluated at an element. -/
theorem restrict_restrict
    (hfg : g ∈ (Ideal.span {f} ⊔ IsAdicRing.ideal A).radical)
    (hgk : k ∈ (Ideal.span {g} ⊔ IsAdicRing.ideal A).radical)
    (hfk : k ∈ (Ideal.span {f} ⊔ IsAdicRing.ideal A).radical) (x : CompletedAway A f) :
    restrict hgk (restrict hfg x) = restrict hfk x :=
  DFunLike.congr_fun (restrict_comp_restrict hfg hgk hfk) x

end Restriction

section IdealIndependence

variable {A} (f : A) (J : Ideal A) (hJ : IsAdic J) (hJfg : J.FG)

include hJ hJfg

/-- The extension of another ideal of definition defines the same topology on the ordinary
localisation as the extension of the chosen ideal. -/
private theorem isAdic_map :
    letI := ((IsAdicRing.ideal A).map (algebraMap A (Localization.Away f))).adicTopology
    IsAdic (J.map (algebraMap A (Localization.Away f))) := by
  let := ((IsAdicRing.ideal A).map (algebraMap A (Localization.Away f))).adicTopology
  apply IsAdic.of_radical_eq (I := (IsAdicRing.ideal A).map
    (algebraMap A (Localization.Away f))) rfl ((IsAdicRing.ideal_spec A).1.map _) (hJfg.map _)
  simp only [← IsLocalization.map_radical (Submonoid.powers f),
    (IsAdicRing.ideal_spec A).2.1.radical_eq hJ]

/-- The canonical comparison from the completed localisation formed with the chosen ideal
to the completion formed with another finitely generated ideal of definition. -/
noncomputable def idealEquiv :
    CompletedAway A f ≃ₐ[A]
      AdicCompletion (J.map (algebraMap A (Localization.Away f))) (Localization.Away f) := by
  letI : WithIdeal (Localization.Away f) :=
    ⟨(IsAdicRing.ideal A).map (algebraMap A (Localization.Away f))⟩
  exact (IsAdic.adicCompletionEquiv (I := (IsAdicRing.ideal A).map
    (algebraMap A (Localization.Away f))) rfl (isAdic_map f J hJ hJfg)
    ((IsAdicRing.ideal_spec A).1.map _) (hJfg.map _)).restrictScalars A

/-- The change of ideal fixes every element of the ordinary localisation. -/
@[simp]
theorem idealEquiv_algebraMap_away (x : Localization.Away f) :
    idealEquiv f J hJ hJfg (algebraMap (Localization.Away f) (CompletedAway A f) x) =
      algebraMap (Localization.Away f)
        (AdicCompletion (J.map (algebraMap A (Localization.Away f))) (Localization.Away f)) x := by
  let : WithIdeal (Localization.Away f) :=
    ⟨(IsAdicRing.ideal A).map (algebraMap A (Localization.Away f))⟩
  exact (IsAdic.adicCompletionEquiv (I := (IsAdicRing.ideal A).map
    (algebraMap A (Localization.Away f))) rfl (isAdic_map f J hJ hJfg)
    ((IsAdicRing.ideal_spec A).1.map _) (hJfg.map _)).commutes x

/-- The inverse comparison also fixes every element of the ordinary localisation. -/
@[simp]
theorem idealEquiv_symm_algebraMap_away (x : Localization.Away f) :
    (idealEquiv f J hJ hJfg).symm (algebraMap (Localization.Away f)
      (AdicCompletion (J.map (algebraMap A (Localization.Away f))) (Localization.Away f)) x) =
        algebraMap (Localization.Away f) (CompletedAway A f) x := by
  apply (idealEquiv f J hJ hJfg).injective
  simp

/-- The change of ideal is bicontinuous for the extended-ideal adic topologies. -/
theorem isHomeomorph_idealEquiv :
    @IsHomeomorph _ _ _
      ((J.map (algebraMap A (Localization.Away f))).map
        (algebraMap (Localization.Away f)
          (AdicCompletion (J.map (algebraMap A (Localization.Away f)))
            (Localization.Away f)))).adicTopology
      (idealEquiv f J hJ hJfg) := by
  let : WithIdeal (Localization.Away f) :=
    ⟨(IsAdicRing.ideal A).map (algebraMap A (Localization.Away f))⟩
  have htop : (inferInstance : TopologicalSpace (CompletedAway A f)) =
      (((IsAdicRing.ideal A).map (algebraMap A (Localization.Away f))).map
        (algebraMap (Localization.Away f) (CompletedAway A f))).adicTopology := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact isAdic A f
  -- The source is the `CompletedAway` wrapper, whose topology uses the composite map from `A`.
  convert (IsAdic.isHomeomorph_adicCompletionEquiv (I := (IsAdicRing.ideal A).map
    (algebraMap A (Localization.Away f))) rfl (isAdic_map f J hJ hJfg)
    ((IsAdicRing.ideal_spec A).1.map _) (hJfg.map _)) using 1
  · rfl
  · exact heq_of_eq htop
  · rfl

end IdealIndependence

end CompletedAway

end TauCeti.AdicRing
