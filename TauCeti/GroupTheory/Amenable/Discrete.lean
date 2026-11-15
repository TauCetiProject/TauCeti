/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Multiplicative
public import TauCeti.Topology.Algebra.Group.UCB.Discrete

/-!
# Discrete invariant means

On a discrete group, means on `TauCeti.UCB G` correspond bijectively to positive real linear
functionals on all bounded functions which take the value one at the constant one. The
correspondence preserves left invariance. This gives a bounded-function characterization of
amenability suitable for constructing finitely additive probabilities from indicator functions.
Amenability with the discrete topology also implies amenability with any group topology, and every
homomorphism out of an amenable discrete group has amenable range (and amenable target when
surjective).

A mean on a discrete group `G` also pushes forward along an arbitrary map `r : G → H`, by
`f ↦ m (f ∘ r)` (`TauCeti.Mean.mapOfDiscrete`). When `r (φ h * x) = h * r x` for a homomorphism
`φ : H →* G`, the pushforward of a left-invariant mean is left invariant.

The function-space identification is `TauCeti.UCB.discreteAlgEquiv`; the normalization and
positivity use Mathlib's `PositiveLinearMap`, without an additional continuity assumption. Additive
counterparts are provided for `TauCeti.AddMean` and `TauCeti.AddAmenable`.

## References

* A. Garrido, *An introduction to amenable groups*, Definitions 1.12–1.13, Theorem 1.15, and
  Proposition 2.2 (for discrete groups).
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.1 and
  Proposition G.2.2.
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
  invFun m := mk₀ (m.1.toLinearMap ∘ₗ (UCB.discreteAlgEquiv G).toLinearMap)
    (fun f hf => by
      simp only [LinearMap.comp_apply, PositiveLinearMap.coe_toLinearMap,
        AlgEquiv.toLinearMap_apply]
      exact map_nonneg m.1 (by
        simpa only [UCB.discreteAlgEquiv_apply, ZeroMemClass.coe_zero] using
          (Subtype.coe_le_coe.2 hf)))
    (by simpa using m.2)
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
    (boundedContinuousFunctionEquiv G m).1 f = m ((UCB.discreteAlgEquiv G).symm f) :=
  (rfl)

@[simp]
theorem boundedContinuousFunctionEquiv_symm_apply
    (m : {m : (G →ᵇ ℝ) →ₚ[ℝ] ℝ // m 1 = 1}) (f : UCB G) :
    (boundedContinuousFunctionEquiv G).symm m f = m.1 (f : G →ᵇ ℝ) := by
  simp [boundedContinuousFunctionEquiv]

/-- The correspondence of means preserves and reflects left invariance. -/
theorem isLeftInvariant_iff_boundedContinuousFunction (m : Mean G) :
    m.IsLeftInvariant ↔ ∀ (g : G) (f : G →ᵇ ℝ),
      (boundedContinuousFunctionEquiv G m).1
          (f.compContinuous (ContinuousMap.mulLeft g⁻¹)) =
        (boundedContinuousFunctionEquiv G m).1 f := by
  rw [isLeftInvariant_iff]
  constructor
  · intro hm g f
    simpa only [boundedContinuousFunctionEquiv_apply,
      UCB.discreteAlgEquiv_symm_compContinuous_mulLeft] using
      hm g ((UCB.discreteAlgEquiv G).symm f)
  · intro hm g f
    simpa only [boundedContinuousFunctionEquiv_apply,
      UCB.discreteAlgEquiv_symm_compContinuous_mulLeft, AlgEquiv.symm_apply_apply] using
      hm g (UCB.discreteAlgEquiv G f)

section MapOfDiscrete

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The pushforward `f ↦ m (f ∘ r)` of a mean `m` on a discrete group `G` along an arbitrary map
`r : G → H` into a topological group, as a mean on `UCB H`. -/
def mapOfDiscrete (r : G → H) (m : Mean G) : Mean H :=
  mk₀ (m.toPositiveLinearMap.toLinearMap ∘ₗ (UCB.compRightAlgHomOfDiscrete r).toLinearMap)
    (fun f hf => map_nonneg m (by simpa using UCB.monotone_compRightAlgHomOfDiscrete r hf))
    (by simp)

@[simp]
theorem mapOfDiscrete_apply (r : G → H) (m : Mean G) (f : UCB H) :
    m.mapOfDiscrete r f = m (UCB.compRightAlgHomOfDiscrete r f) :=
  mk₀_apply _ _ _ f

/-- Along a continuous homomorphism, the pushforward out of a discrete group is the pushforward
`TauCeti.Mean.map`. -/
theorem mapOfDiscrete_coe (φ : G →ₜ* H) (m : Mean G) : m.mapOfDiscrete (φ : G → H) = m.map φ :=
  ext fun f => by simp [UCB.compRightAlgHomOfDiscrete_coe]

/-- If `r (φ h * x) = h * r x` for a homomorphism `φ : H →* G`, then the pushforward of a
left-invariant mean along `r` is left invariant. -/
theorem IsLeftInvariant.mapOfDiscrete {m : Mean G} (hm : m.IsLeftInvariant) (φ : H →* G)
    {r : G → H} (hr : ∀ h x, r (φ h * x) = h * r x) : (m.mapOfDiscrete r).IsLeftInvariant := by
  refine isLeftInvariant_iff.2 fun h f => ?_
  rw [mapOfDiscrete_apply, mapOfDiscrete_apply,
    UCB.compRightAlgHomOfDiscrete_leftTranslation φ hr, hm.apply_leftTranslation]

/-- Pushing forward a mean on a discrete group along the quotient-by-kernel isomorphism agrees with
pushing forward directly to the range. -/
theorem map_quotientKerEquivRange (φ : G →* H) (m : Mean G) :
    (m.map ⟨QuotientGroup.mk' φ.ker, QuotientGroup.continuous_mk⟩).map
      ⟨(QuotientGroup.quotientKerEquivRange φ).toMonoidHom,
        (QuotientGroup.isQuotientMap_mk φ.ker).continuous_iff.2
          (continuous_of_discreteTopology.subtype_mk _)⟩ =
      m.map ⟨φ.rangeRestrict, continuous_of_discreteTopology⟩ := by
  rw [map_map]
  rfl

end MapOfDiscrete

end Mean

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
    exact ⟨(Mean.boundedContinuousFunctionEquiv G m).1,
      (Mean.boundedContinuousFunctionEquiv G m).2,
      (m.isLeftInvariant_iff_boundedContinuousFunction).1 hm⟩
  · rintro ⟨m, h₁, hm⟩
    refine ⟨(Mean.boundedContinuousFunctionEquiv G).symm ⟨m, h₁⟩, ?_⟩
    rw [Mean.isLeftInvariant_iff_boundedContinuousFunction]
    simpa using hm

/-- Any homomorphic image of an amenable discrete group in a topological group is amenable. -/
theorem Amenable.of_surjective [Amenable G] {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (φ : G →* H) (hφ : Function.Surjective φ) : Amenable H :=
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

namespace TauCeti

/-- For a homomorphism `φ : G →* H` of discrete groups, `G ⧸ φ.ker` is amenable if and only if
`φ.range` is amenable, via `QuotientGroup.quotientKerEquivRange`. -/
theorem amenable_quotient_ker_iff_range {G H : Type*} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] [Group H] [TopologicalSpace H] [DiscreteTopology H] (φ : G →* H) :
    Amenable (G ⧸ φ.ker) ↔ Amenable φ.range := by
  have := QuotientGroup.discreteTopology (isOpen_discrete (φ.ker : Set G))
  exact (QuotientGroup.quotientKerEquivRange φ).amenable_iff_of_discreteTopology

/-! ### Additive discrete invariant means and images -/

section AddDiscrete

variable {A : Type*} [AddGroup A] [TopologicalSpace A]

section Discrete

variable [DiscreteTopology A]

namespace AddMean

variable (A) in
/-- Means on a discrete additive group correspond to normalized positive linear functionals on all
bounded functions. -/
def boundedContinuousFunctionEquiv :
    AddMean A ≃ {m : (A →ᵇ ℝ) →ₚ[ℝ] ℝ // m 1 = 1} where
  toFun m := ⟨{
    toLinearMap :=
      m.toPositiveLinearMap.toLinearMap ∘ₗ (AddUCB.discreteAlgEquiv A).symm.toLinearMap
    monotone' := fun _ _ h => OrderHomClass.mono m
      (AddUCB.discreteAlgEquiv_symm_le_discreteAlgEquiv_symm_iff.2 h) },
    (congrArg m ((AddUCB.discreteAlgEquiv A).symm.map_one)).trans m.map_one⟩
  invFun m := mk₀ (m.1.toLinearMap ∘ₗ (AddUCB.discreteAlgEquiv A).toLinearMap)
    (fun f hf => by
      simp only [LinearMap.comp_apply, PositiveLinearMap.coe_toLinearMap,
        AlgEquiv.toLinearMap_apply]
      exact map_nonneg m.1 (by
        simpa only [AddUCB.discreteAlgEquiv_apply, ZeroMemClass.coe_zero] using
          (Subtype.coe_le_coe.2 hf)))
    (by simpa using m.2)
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
    (boundedContinuousFunctionEquiv A m).1 f = m ((AddUCB.discreteAlgEquiv A).symm f) :=
  (rfl)

@[simp]
theorem boundedContinuousFunctionEquiv_symm_apply
    (m : {m : (A →ᵇ ℝ) →ₚ[ℝ] ℝ // m 1 = 1}) (f : AddUCB A) :
    (boundedContinuousFunctionEquiv A).symm m f = m.1 (f : A →ᵇ ℝ) := by
  simp [boundedContinuousFunctionEquiv]

/-- The correspondence of additive means preserves and reflects left invariance. -/
theorem isLeftInvariant_iff_boundedContinuousFunction (m : AddMean A) :
    m.IsLeftInvariant ↔ ∀ (a : A) (f : A →ᵇ ℝ),
      (boundedContinuousFunctionEquiv A m).1
          (f.compContinuous (ContinuousMap.addLeft (-a))) =
        (boundedContinuousFunctionEquiv A m).1 f := by
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

section MapOfDiscrete

variable {B : Type*} [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

/-- The pushforward `f ↦ m (f ∘ r)` of an additive mean `m` on a discrete additive group `A` along
an arbitrary map `r : A → B` into a topological additive group, as a mean on `AddUCB B`. -/
def mapOfDiscrete (r : A → B) (m : AddMean A) : AddMean B :=
  mk₀ (m.toPositiveLinearMap.toLinearMap ∘ₗ (AddUCB.compRightAlgHomOfDiscrete r).toLinearMap)
    (fun f hf => map_nonneg m (by simpa using AddUCB.monotone_compRightAlgHomOfDiscrete r hf))
    (by simp)

@[simp]
theorem mapOfDiscrete_apply (r : A → B) (m : AddMean A) (f : AddUCB B) :
    m.mapOfDiscrete r f = m (AddUCB.compRightAlgHomOfDiscrete r f) :=
  mk₀_apply _ _ _ f

/-- Along a continuous additive homomorphism, the pushforward out of a discrete additive group is
the pushforward `TauCeti.AddMean.map`. -/
theorem mapOfDiscrete_coe (φ : A →ₜ+ B) (m : AddMean A) : m.mapOfDiscrete (φ : A → B) = m.map φ :=
  ext fun f => by simp [AddUCB.compRightAlgHomOfDiscrete_coe]

/-- If `r (φ b + x) = b + r x` for an additive homomorphism `φ : B →+ A`, then the pushforward of a
left-invariant additive mean along `r` is left invariant. -/
theorem IsLeftInvariant.mapOfDiscrete {m : AddMean A} (hm : m.IsLeftInvariant) (φ : B →+ A)
    {r : A → B} (hr : ∀ b x, r (φ b + x) = b + r x) : (m.mapOfDiscrete r).IsLeftInvariant := by
  refine isLeftInvariant_iff.2 fun b f => ?_
  rw [mapOfDiscrete_apply, mapOfDiscrete_apply,
    AddUCB.compRightAlgHomOfDiscrete_leftTranslation φ hr, hm.apply_leftTranslation]

/-- Pushing forward an additive mean on a discrete additive group along the quotient-by-kernel
isomorphism agrees with pushing forward directly to the range. -/
theorem map_quotientKerEquivRange (φ : A →+ B) (m : AddMean A) :
    (m.map ⟨QuotientAddGroup.mk' φ.ker, QuotientAddGroup.continuous_mk⟩).map
      ⟨(QuotientAddGroup.quotientKerEquivRange φ).toAddMonoidHom,
        (QuotientAddGroup.isQuotientMap_mk φ.ker).continuous_iff.2
          (continuous_of_discreteTopology.subtype_mk _)⟩ =
      m.map ⟨φ.rangeRestrict, continuous_of_discreteTopology⟩ := by
  rw [map_map]
  rfl

end MapOfDiscrete

end AddMean

variable (A) in
/-- A discrete additive group is amenable exactly when all bounded functions admit a normalized
positive left-invariant real linear functional. -/
theorem addAmenable_iff_exists_boundedContinuousFunction_mean :
    AddAmenable A ↔ ∃ m : (A →ᵇ ℝ) →ₚ[ℝ] ℝ, m 1 = 1 ∧
      ∀ (a : A) (f : A →ᵇ ℝ),
        m (f.compContinuous (ContinuousMap.addLeft (-a))) = m f := by
  rw [addAmenable_iff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨(AddMean.boundedContinuousFunctionEquiv A m).1,
      (AddMean.boundedContinuousFunctionEquiv A m).2,
      (m.isLeftInvariant_iff_boundedContinuousFunction).1 hm⟩
  · rintro ⟨m, h₁, hm⟩
    refine ⟨(AddMean.boundedContinuousFunctionEquiv A).symm ⟨m, h₁⟩, ?_⟩
    rw [AddMean.isLeftInvariant_iff_boundedContinuousFunction]
    simpa using hm

/-- Any homomorphic image of an amenable discrete additive group in a topological additive group is
amenable. -/
theorem AddAmenable.of_surjective [AddAmenable A] {B : Type*} [AddGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] (φ : A →+ B) (hφ : Function.Surjective φ) : AddAmenable B :=
  .of_denseRange ⟨φ, continuous_of_discreteTopology⟩ hφ.denseRange

/-- The range of an additive homomorphism out of an amenable discrete additive group into a
topological additive group is amenable. -/
instance AddAmenable.range [AddAmenable A] {B : Type*} [AddGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] (φ : A →+ B) : AddAmenable φ.range :=
  .range_of_continuous continuous_of_discreteTopology

end Discrete

/-- An abstract additive group which is amenable with the discrete topology is amenable with any
additive group topology. -/
theorem AddAmenable.of_discrete [IsTopologicalAddGroup A]
    (h : letI : TopologicalSpace A := ⊥;
      letI := discreteTopology_bot A; AddAmenable A) :
    AddAmenable A := by
  let : @DiscreteTopology A ⊥ := discreteTopology_bot A
  exact AddAmenable.of_le (t₁ := ⊥) bot_le h

end AddDiscrete

end TauCeti

namespace AddEquiv

open TauCeti

/-- Amenability of discrete additive groups is invariant under additive group isomorphisms. -/
theorem addAmenable_iff_of_discreteTopology {A B : Type*} [AddGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [AddGroup B] [TopologicalSpace B] [DiscreteTopology B] (e : A ≃+ B) :
    AddAmenable A ↔ AddAmenable B :=
  ⟨fun _ => .of_surjective e.toAddMonoidHom e.surjective,
    fun _ => .of_surjective e.symm.toAddMonoidHom e.symm.surjective⟩

end AddEquiv

namespace TauCeti

/-- For an additive homomorphism `φ : A →+ B` of discrete additive groups, `A ⧸ φ.ker` is amenable
if and only if `φ.range` is amenable, via `QuotientAddGroup.quotientKerEquivRange`. -/
theorem addAmenable_quotient_ker_iff_range {A B : Type*} [AddGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [AddGroup B] [TopologicalSpace B] [DiscreteTopology B] (φ : A →+ B) :
    AddAmenable (A ⧸ φ.ker) ↔ AddAmenable φ.range := by
  have := QuotientAddGroup.discreteTopology (isOpen_discrete (φ.ker : Set A))
  exact (QuotientAddGroup.quotientKerEquivRange φ).addAmenable_iff_of_discreteTopology

end TauCeti
