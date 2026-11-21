/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Basic
public import TauCeti.Topology.Algebra.Group.UCB.Discrete
import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# Discrete invariant means

On a discrete group, means on `TauCeti.UCB G` correspond bijectively to positive real linear
functionals on all bounded functions which take the value one at the constant one. The
correspondence preserves left invariance. This gives a bounded-function characterization of
amenability suitable for constructing finitely additive probabilities from indicator functions.
Amenability with the discrete topology also implies amenability with any group topology.

A mean on a discrete group `G` also pushes forward along an arbitrary map `r : G → H`, by
`f ↦ m (f ∘ r)` (`TauCeti.Mean.mapOfDiscrete`). When `r (φ h * x) = h * r x` for a homomorphism
`φ : H →* G`, the pushforward of a left-invariant mean is left invariant. Both the bounded-function
equivalence and discrete pushforwards have additive counterparts
(`TauCeti.AddMean.boundedContinuousFunctionEquiv`, `TauCeti.AddMean.mapOfDiscrete`, and
`TauCeti.AddAmenable` permanence) generated via `to_additive`.

The function-space identification is `TauCeti.UCB.discreteAlgEquiv` (and
`TauCeti.AddUCB.discreteAlgEquiv`); the normalization and positivity use Mathlib's
`PositiveLinearMap`, without an additional continuity assumption.

## References

* A. Garrido, *An introduction to amenable groups*, Definitions 1.12–1.13 and Theorem 1.15
  (for discrete groups).
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.1.
-/

public section

noncomputable section

open scoped BoundedContinuousFunction

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G]

section Discrete

variable [DiscreteTopology G]

namespace Mean

variable (G) in
/-- Means on a discrete group correspond to normalized positive linear functionals on all
bounded functions. -/
def boundedContinuousFunctionEquiv :
    Mean G ≃ {m : (G →ᵇ ℝ) →ₚ[ℝ] ℝ // m 1 = 1} where
  toFun m := ⟨{
    toLinearMap :=
      m.toPositiveLinearMap.toLinearMap ∘ₗ (UCB.discreteAlgEquiv G).symm.toLinearMap
    monotone' := fun _ _ h => OrderHomClass.mono m
      (UCB.discreteAlgEquiv_symm_le_discreteAlgEquiv_symm_iff.2 h) },
    (congrArg m ((UCB.discreteAlgEquiv G).symm.map_one)).trans m.map_one⟩
  invFun m := mk₀ (m.val.toLinearMap ∘ₗ (UCB.discreteAlgEquiv G).toLinearMap)
    (fun f hf => by
      simp only [LinearMap.comp_apply, PositiveLinearMap.coe_toLinearMap,
        AlgEquiv.toLinearMap_apply]
      exact map_nonneg m.val (by
        simpa only [UCB.discreteAlgEquiv_apply, ZeroMemClass.coe_zero] using
          (Subtype.coe_le_coe.2 hf)))
    (by simpa using m.property)
  left_inv m := by
    ext f
    rw [mk₀_apply]
    exact congrArg m ((UCB.discreteAlgEquiv G).symm_apply_apply f)
  right_inv m := by
    apply Subtype.ext
    apply PositiveLinearMap.toLinearMap_injective
    ext f
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      PositiveLinearMap.coe_toLinearMap, coe_toPositiveLinearMap, mk₀_apply,
      AlgEquiv.apply_symm_apply]

@[simp]
theorem boundedContinuousFunctionEquiv_apply (m : Mean G) (f : G →ᵇ ℝ) :
    (boundedContinuousFunctionEquiv G m).val f = m ((UCB.discreteAlgEquiv G).symm f) :=
  (rfl)

@[simp]
theorem boundedContinuousFunctionEquiv_symm_apply
    (m : {m : (G →ᵇ ℝ) →ₚ[ℝ] ℝ // m 1 = 1}) (f : UCB G) :
    (boundedContinuousFunctionEquiv G).symm m f = m.val (f : G →ᵇ ℝ) := by
  simp [boundedContinuousFunctionEquiv]

/-- The correspondence of means preserves and reflects left invariance. -/
theorem isLeftInvariant_iff_boundedContinuousFunction (m : Mean G) :
    m.IsLeftInvariant ↔ ∀ (g : G) (f : G →ᵇ ℝ),
      (boundedContinuousFunctionEquiv G m).val
          (f.compContinuous (ContinuousMap.mulLeft g⁻¹)) =
        (boundedContinuousFunctionEquiv G m).val f := by
  rw [isLeftInvariant_iff_leftTranslationEquiv]
  constructor
  · intro hm g f
    simpa only [boundedContinuousFunctionEquiv_apply,
      UCB.discreteAlgEquiv_symm_compContinuous_mulLeftEquiv] using
      hm g ((UCB.discreteAlgEquiv G).symm f)
  · intro hm g f
    simpa only [boundedContinuousFunctionEquiv_apply,
      UCB.discreteAlgEquiv_symm_compContinuous_mulLeftEquiv, AlgEquiv.symm_apply_apply] using
      hm g (UCB.discreteAlgEquiv G f)

section MapOfDiscrete

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The pushforward `f ↦ m (f ∘ r)` of a mean `m` on a discrete group `G` along an arbitrary map
`r : G → H` into a topological group, as a mean on `UCB H`. -/
@[to_additive
  /-- The pushforward `f ↦ m (f ∘ r)` of an additive mean `m` on a discrete additive group `G`
  along an arbitrary map `r : G → H` into an additive topological group, as an additive mean on
  `AddUCB H`. -/]
def mapOfDiscrete (r : G → H) (m : Mean G) : Mean H :=
  mk₀ (m.toPositiveLinearMap.toLinearMap ∘ₗ (UCB.compRightAlgHomOfDiscrete r).toLinearMap)
    (fun f hf => map_nonneg m (by simpa using UCB.monotone_compRightAlgHomOfDiscrete r hf))
    (by simp)

@[to_additive (attr := simp)]
theorem mapOfDiscrete_apply (r : G → H) (m : Mean G) (f : UCB H) :
    m.mapOfDiscrete r f = m (UCB.compRightAlgHomOfDiscrete r f) :=
  mk₀_apply _ _ _ f

/-- Along a continuous homomorphism, the pushforward out of a discrete group is the pushforward
`TauCeti.Mean.map`. -/
@[to_additive
  /-- Along a continuous additive homomorphism, the pushforward out of a discrete additive group
  is the pushforward `TauCeti.AddMean.map`. -/]
theorem mapOfDiscrete_coe (φ : G →ₜ* H) (m : Mean G) : m.mapOfDiscrete (φ : G → H) = m.map φ :=
  ext fun f => by simp [UCB.compRightAlgHomOfDiscrete_coe]

/-- Pushing forward a mean on a discrete group along the identity map is the identity. -/
@[to_additive (attr := simp)
  /-- Pushing forward an additive mean on a discrete additive group along the identity map is the
  identity. -/]
theorem mapOfDiscrete_id (m : Mean G) : m.mapOfDiscrete id = m :=
  ext fun _ => by simp only [mapOfDiscrete_apply]; exact congrArg m (UCB.ext fun _ => by simp)

/-- If `r (φ h * x) = h * r x` for a homomorphism `φ : H →* G`, then the pushforward of a
left-invariant mean along `r` is left invariant. -/
@[to_additive
  /-- If `r (φ h + x) = h + r x` for an additive homomorphism `φ : H →+ G`, then the pushforward
  of a left-invariant additive mean along `r` is left invariant. -/]
theorem IsLeftInvariant.mapOfDiscrete {m : Mean G} (hm : m.IsLeftInvariant) (φ : H →* G)
    {r : G → H} (hr : ∀ h x, r (φ h * x) = h * r x) : (m.mapOfDiscrete r).IsLeftInvariant := by
  refine isLeftInvariant_iff_leftTranslationEquiv.2 fun h f => ?_
  rw [mapOfDiscrete_apply, mapOfDiscrete_apply,
    UCB.compRightAlgHomOfDiscrete_leftTranslationEquiv φ hr, hm.apply_leftTranslationEquiv]

end MapOfDiscrete

/-- Pushing forward a mean along `r` and then along `s` is pushing forward along `s ∘ r`. -/
@[to_additive (attr := simp)
  /-- Pushing forward an additive mean along `r` and then along `s` is pushing forward along
  `s ∘ r`. -/]
theorem mapOfDiscrete_mapOfDiscrete {H K : Type*} [Group H] [TopologicalSpace H]
    [DiscreteTopology H] [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (s : H → K) (r : G → H) (m : Mean G) :
    (m.mapOfDiscrete r).mapOfDiscrete s = m.mapOfDiscrete (s ∘ r) :=
  ext fun _ => by simp only [mapOfDiscrete_apply]; exact congrArg m (UCB.ext fun _ => by simp)

/-- Pushing forward a mean on a discrete group along the quotient-by-kernel isomorphism agrees with
pushing forward directly to the range. -/
@[to_additive
  /-- Pushing forward an additive mean on a discrete additive group along the quotient-by-kernel
  isomorphism agrees with pushing forward directly to the range. -/]
theorem mapOfDiscrete_quotientKerEquivRange {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (φ : G →* H) (m : Mean G) :
    letI := QuotientGroup.discreteTopology (isOpen_discrete (φ.ker : Set G))
    (m.mapOfDiscrete (QuotientGroup.mk' φ.ker)).mapOfDiscrete
        (QuotientGroup.quotientKerEquivRange φ) =
      m.mapOfDiscrete φ.rangeRestrict := by
  have := QuotientGroup.discreteTopology (isOpen_discrete (φ.ker : Set G))
  rw [mapOfDiscrete_mapOfDiscrete]
  exact congrArg (m.mapOfDiscrete ·)
    (funext (TauCeti.QuotientGroup.quotientKerEquivRange_apply_mk φ))

end Mean

namespace AddMean

variable {A : Type*} [AddGroup A] [TopologicalSpace A] [DiscreteTopology A]

variable (A) in
/-- Additive means on a discrete additive group correspond to normalized positive linear
functionals on all bounded functions. -/
def boundedContinuousFunctionEquiv :
    AddMean A ≃ {m : (A →ᵇ ℝ) →ₚ[ℝ] ℝ // m 1 = 1} where
  toFun m := ⟨{
    toLinearMap :=
      m.toPositiveLinearMap.toLinearMap ∘ₗ (AddUCB.discreteAlgEquiv A).symm.toLinearMap
    monotone' := fun _ _ h => OrderHomClass.mono m
      (AddUCB.discreteAlgEquiv_symm_le_discreteAlgEquiv_symm_iff.2 h) },
    (congrArg m ((AddUCB.discreteAlgEquiv A).symm.map_one)).trans m.map_one⟩
  invFun m := mk₀ (m.val.toLinearMap ∘ₗ (AddUCB.discreteAlgEquiv A).toLinearMap)
    (fun f hf => by
      simp only [LinearMap.comp_apply, PositiveLinearMap.coe_toLinearMap,
        AlgEquiv.toLinearMap_apply]
      exact map_nonneg m.val (by
        simpa only [AddUCB.discreteAlgEquiv_apply, ZeroMemClass.coe_zero] using
          (Subtype.coe_le_coe.2 hf)))
    (by simpa using m.property)
  left_inv m := by
    ext f
    rw [mk₀_apply]
    exact congrArg m ((AddUCB.discreteAlgEquiv A).symm_apply_apply f)
  right_inv m := by
    apply Subtype.ext
    apply PositiveLinearMap.toLinearMap_injective
    ext f
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      PositiveLinearMap.coe_toLinearMap, coe_toPositiveLinearMap, mk₀_apply,
      AlgEquiv.apply_symm_apply]

@[simp]
theorem boundedContinuousFunctionEquiv_apply (m : AddMean A) (f : A →ᵇ ℝ) :
    (boundedContinuousFunctionEquiv A m).val f = m ((AddUCB.discreteAlgEquiv A).symm f) :=
  (rfl)

@[simp]
theorem boundedContinuousFunctionEquiv_symm_apply
    (m : {m : (A →ᵇ ℝ) →ₚ[ℝ] ℝ // m 1 = 1}) (f : AddUCB A) :
    (boundedContinuousFunctionEquiv A).symm m f = m.val (f : A →ᵇ ℝ) := by
  simp [boundedContinuousFunctionEquiv]

/-- The correspondence of additive means preserves and reflects left invariance. -/
theorem isLeftInvariant_iff_boundedContinuousFunction (m : AddMean A) :
    m.IsLeftInvariant ↔ ∀ (a : A) (f : A →ᵇ ℝ),
      (boundedContinuousFunctionEquiv A m).val
          (f.compContinuous (ContinuousMap.addLeft (-a))) =
        (boundedContinuousFunctionEquiv A m).val f := by
  rw [isLeftInvariant_iff]
  constructor
  · intro hm a f
    simpa only [boundedContinuousFunctionEquiv_apply,
      AddUCB.discreteAlgEquiv_symm_compContinuous_addLeft] using
      hm a ((AddUCB.discreteAlgEquiv A).symm f)
  · intro hm a f
    simpa only [boundedContinuousFunctionEquiv_apply,
      AddUCB.discreteAlgEquiv_symm_compContinuous_addLeft, AlgEquiv.symm_apply_apply] using
      hm a (AddUCB.discreteAlgEquiv A f)

end AddMean

variable (G) in
/-- A discrete group is amenable exactly when all bounded functions admit a normalized positive
left-invariant real linear functional. -/
theorem amenable_iff_exists_boundedContinuousFunction_mean :
    Amenable G ↔ ∃ m : (G →ᵇ ℝ) →ₚ[ℝ] ℝ, m 1 = 1 ∧
      ∀ (g : G) (f : G →ᵇ ℝ),
        m (f.compContinuous (ContinuousMap.mulLeft g⁻¹)) = m f := by
  rw [amenable_iff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨(Mean.boundedContinuousFunctionEquiv G m).val,
      (Mean.boundedContinuousFunctionEquiv G m).property,
      (m.isLeftInvariant_iff_boundedContinuousFunction).1 hm⟩
  · rintro ⟨m, h₁, hm⟩
    refine ⟨(Mean.boundedContinuousFunctionEquiv G).symm ⟨m, h₁⟩, ?_⟩
    rw [Mean.isLeftInvariant_iff_boundedContinuousFunction]
    simpa using hm

/-- A discrete additive group is amenable exactly when all bounded functions admit a normalized
positive translation-invariant real linear functional. -/
theorem addAmenable_iff_exists_boundedContinuousFunction_mean {A : Type*} [AddGroup A]
    [TopologicalSpace A] [DiscreteTopology A] :
    AddAmenable A ↔ ∃ m : (A →ᵇ ℝ) →ₚ[ℝ] ℝ, m 1 = 1 ∧
      ∀ (a : A) (f : A →ᵇ ℝ),
        m (f.compContinuous (ContinuousMap.addLeft (-a))) = m f := by
  rw [addAmenable_iff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨(AddMean.boundedContinuousFunctionEquiv A m).val,
      (AddMean.boundedContinuousFunctionEquiv A m).property,
      (m.isLeftInvariant_iff_boundedContinuousFunction).1 hm⟩
  · rintro ⟨m, h₁, hm⟩
    refine ⟨(AddMean.boundedContinuousFunctionEquiv A).symm ⟨m, h₁⟩, ?_⟩
    rw [AddMean.isLeftInvariant_iff_boundedContinuousFunction]
    simpa using hm

/-- A topological group which is a homomorphic image of an amenable discrete group is amenable,
for every group topology on the target. -/
theorem Amenable.of_surjective [Amenable G] {H : Type*} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (φ : G →* H) (hφ : Function.Surjective φ) :
    Amenable H :=
  .of_denseRange ⟨φ, continuous_of_discreteTopology⟩ hφ.denseRange

/-- The range of a homomorphism out of an amenable discrete group into a topological group is
amenable. -/
instance Amenable.range [Amenable G] {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (φ : G →* H) : Amenable φ.range :=
  .range_of_continuous continuous_of_discreteTopology

end Discrete

/-- An abstract group which is amenable with the discrete topology is amenable with any
group topology. -/
theorem Amenable.of_discrete [IsTopologicalGroup G]
    (h : letI : TopologicalSpace G := ⊥;
      letI := discreteTopology_bot G; Amenable G) :
    Amenable G := by
  let : @DiscreteTopology G ⊥ := discreteTopology_bot G
  exact Amenable.of_le (t₁ := ⊥) bot_le h

end TauCeti

namespace MulEquiv

open TauCeti

/-- Amenability of discrete groups is invariant under group isomorphisms. -/
theorem amenable_iff_of_discreteTopology {G H : Type*} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] [Group H] [TopologicalSpace H] [DiscreteTopology H] (e : G ≃* H) :
    Amenable G ↔ Amenable H :=
  ⟨fun _ => .of_surjective e.toMonoidHom e.surjective,
    fun _ => .of_surjective e.symm.toMonoidHom e.symm.surjective⟩

end MulEquiv

namespace MonoidHom

open TauCeti

/-- For a homomorphism `φ : G →* H` of discrete groups, `G ⧸ φ.ker` is amenable if and only if
`φ.range` is amenable, via `QuotientGroup.quotientKerEquivRange`. -/
theorem amenable_quotient_ker_iff_range {G H : Type*} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] [Group H] [TopologicalSpace H] [DiscreteTopology H] (φ : G →* H) :
    Amenable (G ⧸ φ.ker) ↔ Amenable φ.range := by
  have := QuotientGroup.discreteTopology (isOpen_discrete (φ.ker : Set G))
  exact (QuotientGroup.quotientKerEquivRange φ).amenable_iff_of_discreteTopology

end MonoidHom

namespace TauCeti

section AddDiscrete

variable {A : Type*} [AddGroup A] [TopologicalSpace A]

section DiscreteTopology

variable [DiscreteTopology A]

/-- An additive topological group which is a homomorphic image of an amenable discrete additive
group is amenable, for every additive-group topology on the target. -/
theorem AddAmenable.of_surjective [AddAmenable A] {B : Type*} [AddGroup B]
    [TopologicalSpace B] [IsTopologicalAddGroup B] (φ : A →+ B) (hφ : Function.Surjective φ) :
    AddAmenable B :=
  .of_denseRange ⟨φ, continuous_of_discreteTopology⟩ hφ.denseRange

attribute [to_additive existing] Amenable.of_surjective

/-- The range of an additive homomorphism out of an amenable discrete additive group into an
additive topological group is amenable. -/
instance AddAmenable.range [AddAmenable A] {B : Type*} [AddGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] (φ : A →+ B) : AddAmenable φ.range :=
  .range_of_continuous continuous_of_discreteTopology

attribute [to_additive existing] Amenable.range

end DiscreteTopology

/-- An abstract additive group which is amenable with the discrete topology is amenable with any
additive-group topology. -/
theorem AddAmenable.of_discrete [IsTopologicalAddGroup A]
    (h : letI : TopologicalSpace A := ⊥;
      letI := discreteTopology_bot A; AddAmenable A) :
    AddAmenable A := by
  let : @DiscreteTopology A ⊥ := discreteTopology_bot A
  exact AddAmenable.of_le (t₁ := ⊥) bot_le h

attribute [to_additive existing] Amenable.of_discrete

end AddDiscrete

end TauCeti

namespace AddEquiv

open TauCeti

/-- Additive amenability of discrete additive groups is invariant under additive group
isomorphisms. -/
theorem addAmenable_iff_of_discreteTopology {A B : Type*} [AddGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [AddGroup B] [TopologicalSpace B] [DiscreteTopology B] (e : A ≃+ B) :
    AddAmenable A ↔ AddAmenable B :=
  ⟨fun _ => .of_surjective e.toAddMonoidHom e.surjective,
    fun _ => .of_surjective e.symm.toAddMonoidHom e.symm.surjective⟩

attribute [to_additive existing AddEquiv.addAmenable_iff_of_discreteTopology]
  MulEquiv.amenable_iff_of_discreteTopology

end AddEquiv

namespace AddMonoidHom

open TauCeti

/-- For an additive homomorphism `φ : A →+ B` of discrete additive groups, `A ⧸ φ.ker` is
amenable if and only if `φ.range` is amenable, via `QuotientAddGroup.quotientKerEquivRange`. -/
theorem addAmenable_quotient_ker_iff_range {A B : Type*} [AddGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [AddGroup B] [TopologicalSpace B] [DiscreteTopology B] (φ : A →+ B) :
    AddAmenable (A ⧸ φ.ker) ↔ AddAmenable φ.range := by
  have := QuotientAddGroup.discreteTopology (isOpen_discrete (φ.ker : Set A))
  exact (QuotientAddGroup.quotientKerEquivRange φ).addAmenable_iff_of_discreteTopology

attribute [to_additive existing AddMonoidHom.addAmenable_quotient_ker_iff_range]
  MonoidHom.amenable_quotient_ker_iff_range

end AddMonoidHom
