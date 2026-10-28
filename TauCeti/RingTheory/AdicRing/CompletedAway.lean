/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Topology.Algebra.UniformRing
public import TauCeti.RingTheory.AdicCompletion.AlgHom
public import TauCeti.RingTheory.AdicCompletion.Noetherian
public import TauCeti.RingTheory.AdicRing.Basic

/-!
# Completed localisations of adic rings

Let `A` be an adic ring of finite ideal type with chosen ideal of definition `I` and let
`f ∈ A`. The completed localisation `A_{f}` is the `I·A_f`-adic completion of the
localisation `A_f = Localization.Away f`, with the `I·A_{f}`-adic topology. These rings are
the rings of sections of the structure sheaf of the formal spectrum `Spf A` over the basic
open sets `D(f)`.

## Main definitions and results

* `TauCeti.AdicRing.CompletedAway A f`: the completed localisation `A_{f}`, an `A`-algebra and
  an `A_f`-algebra whose topology is the `I·A_{f}`-adic one (`CompletedAway.isAdic`).
* `CompletedAway.isAdicRing`: `A_{f}` is an adic ring of finite ideal type.
* `CompletedAway.evalₐ` and `CompletedAway.ker_evalₐ`: the projection
  `A_{f} → A_f ⧸ (I·A_f)^n`, whose kernel is `(I·A_{f})^n`.
* `CompletedAway.continuous_algebraMap` and `CompletedAway.isUnit_algebraMap`: the canonical
  map `A → A_{f}` is continuous and sends `f` to a unit.
* `CompletedAway.isNoetherianRing` and `CompletedAway.flat`: if `A` is noetherian, then `A_{f}`
  is noetherian and flat over `A`.
* `CompletedAway.lift` and `CompletedAway.existsUnique_lift`: the universal property. A
  continuous ring homomorphism `u : A → B` into a complete Hausdorff linearly topologised ring
  with `u f` a unit factors uniquely through a continuous ring homomorphism `A_{f} → B`.
  Uniqueness (`CompletedAway.ringHom_ext`) holds for every Hausdorff target: although the image
  of `A` need not be dense in `A_{f}`, ring homomorphisms preserve the inverse of `f`, so two
  maps agreeing on `A` agree on the dense image of `A_f`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.6.1–7.6.2,
  7.6.6, 7.6.11 and 7.6.13.
-/

public section

open Topology Filter

namespace TauCeti

namespace AdicRing

open IsAdicRing

variable (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]

/-- The **completed localisation** `A_{f}` of an adic ring `A` of finite ideal type at `f ∈ A`:
the adic completion of `Localization.Away f` along the extension of the chosen ideal of
definition of `A`. Its topology is the adic topology of that extended ideal. -/
@[expose] def CompletedAway (f : A) : Type _ :=
  AdicCompletion ((ideal A).map (algebraMap A (Localization.Away f))) (Localization.Away f)

namespace CompletedAway

variable (f : A)

noncomputable instance : CommRing (CompletedAway A f) :=
  inferInstanceAs <| CommRing <|
    AdicCompletion ((ideal A).map (algebraMap A (Localization.Away f))) (Localization.Away f)

noncomputable instance : Algebra (Localization.Away f) (CompletedAway A f) :=
  inferInstanceAs <| Algebra (Localization.Away f) <|
    AdicCompletion ((ideal A).map (algebraMap A (Localization.Away f))) (Localization.Away f)

noncomputable instance : Algebra A (CompletedAway A f) :=
  inferInstanceAs <| Algebra A <|
    AdicCompletion ((ideal A).map (algebraMap A (Localization.Away f))) (Localization.Away f)

instance : IsScalarTower A (Localization.Away f) (CompletedAway A f) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The topology of `A_{f}` is the adic topology of the extension of the chosen ideal of
definition of `A`; the `WithIdeal` structure supplies it together with the compatible
uniformity. -/
noncomputable instance : WithIdeal (CompletedAway A f) :=
  ⟨(ideal A).map (algebraMap A (CompletedAway A f))⟩

/-- The topology of `A_{f}` is the `I·A_{f}`-adic topology, for the chosen ideal of
definition `I` of `A`. -/
theorem isAdic : IsAdic ((ideal A).map (algebraMap A (CompletedAway A f))) :=
  rfl

/-- The extension of `I` to `A_{f}` agrees with the extension of `I·A_f`. -/
theorem map_ideal_eq :
    (ideal A).map (algebraMap A (CompletedAway A f)) =
      ((ideal A).map (algebraMap A (Localization.Away f))).map
        (algebraMap (Localization.Away f) (CompletedAway A f)) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- The projection `A_{f} → A_f ⧸ (I·A_f)^n` to the `n`-th level of the completion. -/
noncomputable def evalₐ (n : ℕ) :
    CompletedAway A f →ₐ[Localization.Away f]
      Localization.Away f ⧸ (ideal A).map (algebraMap A (Localization.Away f)) ^ n :=
  AdicCompletion.evalₐ _ n

/-- The projection `A_{f} → A_f ⧸ (I·A_f)^n` is surjective. -/
theorem surjective_evalₐ (n : ℕ) : Function.Surjective (evalₐ A f n) :=
  AdicCompletion.surjective_evalₐ _ n

/-- The kernel of the projection `A_{f} → A_f ⧸ (I·A_f)^n` is the `n`-th power of `I·A_{f}`. -/
theorem ker_evalₐ (n : ℕ) :
    RingHom.ker (evalₐ A f n) = (ideal A).map (algebraMap A (CompletedAway A f)) ^ n := by
  rw [map_ideal_eq]
  exact AdicCompletion.ker_evalₐ ((ideal_spec A).1.map _) n

/-- `A_f` meets the `n`-th power of `I·A_{f}` exactly in `(I·A_f)^n`. -/
theorem comap_pow (n : ℕ) :
    ((ideal A).map (algebraMap A (CompletedAway A f)) ^ n).comap
        (algebraMap (Localization.Away f) (CompletedAway A f)) =
      (ideal A).map (algebraMap A (Localization.Away f)) ^ n := by
  ext x
  rw [Ideal.mem_comap, ← ker_evalₐ, RingHom.mem_ker, AlgHom.commutes,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]

/-- `A_{f}` is complete and separated for `I·A_{f}`. -/
theorem isAdicComplete :
    IsAdicComplete ((ideal A).map (algebraMap A (CompletedAway A f))) (CompletedAway A f) := by
  rw [map_ideal_eq]
  exact AdicCompletion.isAdicComplete_self _ ((ideal_spec A).1.map _)

/-- The completed localisation of an adic ring of finite ideal type is again an adic ring of
finite ideal type, with ideal of definition `I·A_{f}`. -/
instance isAdicRing : IsAdicRing (CompletedAway A f) :=
  ⟨_, (ideal_spec A).1.map _, isAdic A f, isAdicComplete A f⟩

/-- The canonical map `A → A_{f}` is continuous. -/
@[fun_prop]
theorem continuous_algebraMap : Continuous (algebraMap A (CompletedAway A f)) :=
  (ideal_spec A).2.1.continuous_of_map_le_radical (isAdic A f) (ideal_spec A).1 Ideal.le_radical

/-- The canonical map `A → A_{f}` sends `f` to a unit. -/
theorem isUnit_algebraMap : IsUnit (algebraMap A (CompletedAway A f) f) := by
  rw [IsScalarTower.algebraMap_apply A (Localization.Away f)]
  exact (IsLocalization.Away.algebraMap_isUnit f).map _

/-- The image of `A_f` is dense in `A_{f}`. -/
theorem denseRange_algebraMap :
    DenseRange (algebraMap (Localization.Away f) (CompletedAway A f)) := by
  intro x
  rw [mem_closure_iff_nhds_basis ((isAdic A f).hasBasis_nhds x)]
  intro n _
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (evalₐ A f n x)
  refine ⟨_, ⟨s, rfl⟩, algebraMap (Localization.Away f) (CompletedAway A f) s - x, ?_,
    add_sub_cancel x _⟩
  rw [SetLike.mem_coe, ← ker_evalₐ, RingHom.mem_ker, map_sub, AlgHom.commutes,
    Ideal.Quotient.algebraMap_eq, hs, sub_self]

section Noetherian

variable [IsNoetherianRing A]

/-- The completed localisation of an adic noetherian ring is noetherian. -/
instance isNoetherianRing : IsNoetherianRing (CompletedAway A f) :=
  inferInstanceAs <| IsNoetherianRing <|
    AdicCompletion ((ideal A).map (algebraMap A (Localization.Away f))) (Localization.Away f)

/-- The completed localisation of an adic noetherian ring is flat over it. -/
instance flat : Module.Flat A (CompletedAway A f) :=
  have : Module.Flat (Localization.Away f) (CompletedAway A f) :=
    inferInstanceAs <| Module.Flat (Localization.Away f) <|
      AdicCompletion ((ideal A).map (algebraMap A (Localization.Away f))) (Localization.Away f)
  Module.Flat.trans A (Localization.Away f) (CompletedAway A f)

end Noetherian

section Lift

/-- Continuous ring homomorphisms out of `A_{f}` into a Hausdorff ring are determined by their
restriction to `A`. -/
theorem ringHom_ext {B : Type*} [CommRing B] [TopologicalSpace B] [T2Space B]
    {g g' : CompletedAway A f →+* B} (hg : Continuous g) (hg' : Continuous g')
    (h : g.comp (algebraMap A (CompletedAway A f)) = g'.comp (algebraMap A (CompletedAway A f))) :
    g = g' := by
  have hloc : g.comp (algebraMap (Localization.Away f) (CompletedAway A f)) =
      g'.comp (algebraMap (Localization.Away f) (CompletedAway A f)) :=
    IsLocalization.ringHom_ext (Submonoid.powers f) <| by
      simpa only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq] using h
  exact DFunLike.coe_injective <|
    (denseRange_algebraMap A f).equalizer hg hg' (congrArg DFunLike.coe hloc)

/-- The `I·A_f`-adic structure on `A_f`, used to extend maps out of `A_f` to its completion. -/
private noncomputable abbrev localizationWithIdeal : WithIdeal (Localization.Away f) :=
  ⟨(ideal A).map (algebraMap A (Localization.Away f))⟩

attribute [local instance] localizationWithIdeal

private theorem isUniformInducing_algebraMap :
    IsUniformInducing (algebraMap (Localization.Away f) (CompletedAway A f)) := by
  refine AddMonoidHom.isUniformInducing_of_isInducing
    (f := (algebraMap (Localization.Away f) (CompletedAway A f)).toAddMonoidHom) ?_
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  refine (Ideal.hasBasis_nhds_zero_adic _).eq_of_same_basis ?_
  convert ((isAdic A f).hasBasis_nhds_zero.comap
    (algebraMap (Localization.Away f) (CompletedAway A f))) using 2 with n
  exact congrArg SetLike.coe (comap_pow A f n).symm

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [IsLinearTopology B B] {f} {u : A →+* B}

private theorem uniformContinuous_awayLift (hu : Continuous u) (hf : IsUnit (u f)) :
    UniformContinuous (IsLocalization.Away.lift (S := Localization.Away f) f hf) := by
  refine uniformContinuous_addMonoidHom_of_continuous
    (f := (IsLocalization.Away.lift (S := Localization.Away f) f hf).toAddMonoidHom) ?_
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (Ideal.hasBasis_nhds_zero_adic
    ((ideal A).map (algebraMap A (Localization.Away f)))).tendsto_iff
    IsLinearTopology.hasBasis_ideal]
  intro U hU
  have hpre : u ⁻¹' (U : Set B) ∈ 𝓝 0 := hu.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨n, -, hn⟩ := (ideal_spec A).2.1.hasBasis_nhds_zero.mem_iff.mp hpre
  refine ⟨n, trivial, fun x hx ↦ ?_⟩
  rw [← Ideal.map_pow] at hx
  have hle : (ideal A ^ n).map (algebraMap A (Localization.Away f)) ≤
      U.comap (IsLocalization.Away.lift (S := Localization.Away f) f hf) := by
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, IsLocalization.Away.lift_comp]
    exact hn
  exact hle hx

variable [CompleteSpace B] [T2Space B]

/-- The universal property of the completed localisation: a continuous ring homomorphism
`u : A → B` into a complete Hausdorff linearly topologised ring with `u f` a unit extends to a
continuous ring homomorphism `A_{f} → B`. -/
noncomputable def lift (u : A →+* B) (hu : Continuous u) (hf : IsUnit (u f)) :
    CompletedAway A f →+* B :=
  IsDenseInducing.extendRingHom (isUniformInducing_algebraMap A f) (denseRange_algebraMap A f)
    (uniformContinuous_awayLift A hu hf)

/-- The lift of `u` is continuous. -/
@[fun_prop]
theorem continuous_lift (hu : Continuous u) (hf : IsUnit (u f)) : Continuous (lift A u hu hf) :=
  (uniformContinuous_uniformly_extend (isUniformInducing_algebraMap A f)
    (denseRange_algebraMap A f) (uniformContinuous_awayLift A hu hf)).continuous

/-- The lift of `u` restricts to `u` on `A`. -/
@[simp]
theorem lift_algebraMap (hu : Continuous u) (hf : IsUnit (u f)) (a : A) :
    lift A u hu hf (algebraMap A (CompletedAway A f) a) = u a := by
  rw [IsScalarTower.algebraMap_apply A (Localization.Away f)]
  -- `IsDenseInducing.extendRingHom` has no evaluation lemma; its underlying function is
  -- `IsDenseInducing.extend` by definition
  change ((isUniformInducing_algebraMap A f).isDenseInducing
    (denseRange_algebraMap A f)).extend _ _ = _
  rw [IsDenseInducing.extend_eq _ (uniformContinuous_awayLift A hu hf).continuous,
    IsLocalization.Away.lift_eq]

/-- The lift of `u` restricts to `u` on `A`, as an equality of ring homomorphisms. -/
theorem lift_comp_algebraMap (hu : Continuous u) (hf : IsUnit (u f)) :
    (lift A u hu hf).comp (algebraMap A (CompletedAway A f)) = u :=
  RingHom.ext (lift_algebraMap A hu hf)

/-- A continuous ring homomorphism out of `A_{f}` is the lift of its restriction to `A`. -/
theorem eq_lift {g : CompletedAway A f →+* B} (hg : Continuous g) (hu : Continuous u)
    (hf : IsUnit (u f)) (h : g.comp (algebraMap A (CompletedAway A f)) = u) :
    g = lift A u hu hf :=
  ringHom_ext A f hg (continuous_lift A hu hf) (by rw [h, lift_comp_algebraMap])

/-- **Universal property of the completed localisation.** A continuous ring homomorphism
`u : A → B` into a complete Hausdorff linearly topologised ring with `u f` a unit factors
uniquely through a continuous ring homomorphism `A_{f} → B`. -/
theorem existsUnique_lift (hu : Continuous u) (hf : IsUnit (u f)) :
    ∃! g : CompletedAway A f →+* B,
      Continuous g ∧ g.comp (algebraMap A (CompletedAway A f)) = u :=
  ⟨lift A u hu hf, ⟨continuous_lift A hu hf, lift_comp_algebraMap A hu hf⟩,
    fun _ hg ↦ eq_lift A hg.1 hu hf hg.2⟩

end Lift

end CompletedAway

end AdicRing

end TauCeti
