/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Pullback.Coherence
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.StronglyNoetherian
public import TauCeti.RingTheory.Huber.Padic.Field
public import TauCeti.RingTheory.Huber.Pair.PowerBounded
public import TauCeti.RingTheory.Huber.Restricted.Noetherian
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Complete
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Pair.Polydisc

/-!
# Checks for the symmetry and unit of fibre products of affinoid adic spaces

Worked examples over `ℚ₂` of the symmetry and the right unitor of fibre products of affinoid adic
spaces, for the closed disc `Spa D` with `D = ℚ₂⟨X⟩`:

1. **Symmetry.** On `Spa D ×_{Spa ℚ₂} Spa D = Spa(ℚ₂⟨X⟩ ⊗̂_{ℚ₂} ℚ₂⟨Y⟩)`, the morphism `σ`, `Spa`
   of the completed tensor symmetry, is the comparison of the pullback square with its flip
   (`TauCeti.AdicSpace.affinoid_isoIsPullback_flip_hom`), so an isomorphism. It exchanges the two
   projections and is an involution. The points `y₀`, `y₁` of `Spa D` cut out by `X = 0` and
   `X = 1` are distinct and lie over the same point of `Spa ℚ₂`; a point `z` of the product with
   projections `(y₀, y₁)` (cut out by `X = 0, Y = 1`) goes to the distinct point `σ z` with
   projections `(y₁, y₀)` (cut out by `X = 1, Y = 0`), and back.
2. **Unit.** `Spa` of the left coprojection `ℚ₂⟨X⟩ → ℚ₂⟨X⟩ ⊗̂_{ℚ₂} ℚ₂` is an isomorphism of
   adic spaces, with inverse `Spa` of `b ⊗ a ↦ b·a` (`TauCeti.AdicSpace.rightUnitorAffinoid`).
-/

public section

open CategoryTheory TauCeti TauCeti.Huber TauCeti.PreAdicSpace TauCeti.ValuationSpectrum
  TauCeti.AdicSpace

namespace TauCeti.Examples.SymmetryOnChartsSpaChecks

/-- The Tate algebra `ℚ₂⟨X⟩` of the closed unit disc. -/
noncomputable abbrev D : Type := restrictedMvPowerSeriesCompletion 1 ℚ_[2]

/-- `ℚ₂ → ℚ₂⟨X⟩` is topologically of finite type. -/
theorem isTopologicallyFiniteType_algebraMap_D :
    IsTopologicallyFiniteType (algebraMap ℚ_[2] D) :=
  (isStrictlyTopologicallyFiniteType_algebraMap (A := ℚ_[2]) 1).isTopologicallyFiniteType

/-- `ℚ₂ → ℚ₂⟨X⟩` is adic. -/
theorem isAdicHom_algebraMap_D : IsAdicHom (algebraMap ℚ_[2] D) :=
  isTopologicallyFiniteType_algebraMap_D.isAdicHom

/-- `ℚ₂⟨X⟩` is a Tate ring. -/
theorem isTateRing_D : IsTateRing D := isTopologicallyFiniteType_algebraMap_D.isTateRing

attribute [local instance] isAdicHom_algebraMap_D isTateRing_D

/-- The Huber pair `(ℚ₂, ℤ₂)` of `Spa ℚ₂`. -/
noncomputable abbrev S : Pair ℚ_[2] := Pair.powerBounded ℚ_[2]

/-- The Huber pair `(ℚ₂⟨X⟩, ℤ₂⟨X⟩)` of the disc `Spa D`. -/
noncomputable abbrev T : Pair D := Pair.powerBounded D

/-- The structure morphism `(ℚ₂, ℤ₂) → (ℚ₂⟨X⟩, ℤ₂⟨X⟩)`. -/
noncomputable def f : S.Hom T :=
  Pair.powerBoundedHom (algebraMap ℚ_[2] D)
    (continuous_algebraMap_restrictedMvPowerSeriesCompletion 1 ℚ_[2])

private theorem f_toRingHom : f.toRingHom = algebraMap ℚ_[2] D :=
  Pair.Hom.toRingHom_powerBoundedHom _ _

/-- `ℚ₂ → ℚ₂⟨X⟩` carries `ℤ₂` into `ℤ₂⟨X⟩`. -/
private theorem algebraMap_mem_plus_T : ∀ a ∈ S.plus, algebraMap ℚ_[2] D a ∈ T.plus :=
  f_toRingHom ▸ f.map_mem_plus

/-- `(ℚ₂, ℤ₂)` is sheafy. -/
theorem isSheafyForEveryPresentation_S : IsSheafyForEveryPresentation S.plus :=
  isSheafyForEveryPresentation_of_isStronglyNoetherian S.isRingOfIntegralElements

/-- `(ℚ₂⟨X⟩, ℤ₂⟨X⟩)` is sheafy. -/
theorem isSheafyForEveryPresentation_T : IsSheafyForEveryPresentation T.plus :=
  isSheafyForEveryPresentation_of_isStronglyNoetherian T.isRingOfIntegralElements

/-- `ℚ₂⟨X⟩ ⊗̂_{ℚ₂} ℚ₂⟨Y⟩` is sheafy. -/
theorem isSheafyForEveryPresentation_completedTensor :
    IsSheafyForEveryPresentation (T.completedTensor ℚ_[2] T).plus :=
  isSheafyForEveryPresentation_completedTensor_of_isStablySheafyRing_left T T
    isStablySheafyRing_of_isStronglyNoetherian isTopologicallyFiniteType_algebraMap_D

/-- The first projection `Spa D ×_{Spa ℚ₂} Spa D ⟶ Spa D`. -/
noncomputable def pr₁ :
    ofPair _ isSheafyForEveryPresentation_completedTensor ⟶
      ofPair T isSheafyForEveryPresentation_T :=
  comapOfPair isSheafyForEveryPresentation_T isSheafyForEveryPresentation_completedTensor
    (Pair.completedTensor.inl ℚ_[2] T T)

/-- The second projection `Spa D ×_{Spa ℚ₂} Spa D ⟶ Spa D`. -/
noncomputable def pr₂ :
    ofPair _ isSheafyForEveryPresentation_completedTensor ⟶
      ofPair T isSheafyForEveryPresentation_T :=
  comapOfPair isSheafyForEveryPresentation_T isSheafyForEveryPresentation_completedTensor
    (Pair.completedTensor.inr ℚ_[2] T T)

/-- The symmetry `σ` of `Spa D ×_{Spa ℚ₂} Spa D`, `Spa` of the completed tensor symmetry. -/
noncomputable def σ :
    ofPair _ isSheafyForEveryPresentation_completedTensor ⟶
      ofPair _ isSheafyForEveryPresentation_completedTensor :=
  comapOfPair isSheafyForEveryPresentation_completedTensor
    isSheafyForEveryPresentation_completedTensor (Pair.completedTensor.commHom ℚ_[2] T T)

/-- `σ` is the comparison of the chart pullback square with its flip. -/
example : σ = ((affinoid_isPullback isSheafyForEveryPresentation_S isSheafyForEveryPresentation_T
    isSheafyForEveryPresentation_T isSheafyForEveryPresentation_completedTensor f f f_toRingHom
    f_toRingHom).isoIsPullback _ _
    (affinoid_isPullback isSheafyForEveryPresentation_S isSheafyForEveryPresentation_T
      isSheafyForEveryPresentation_T
      isSheafyForEveryPresentation_completedTensor.completedTensor_comm f f f_toRingHom
      f_toRingHom).flip).hom :=
  (affinoid_isoIsPullback_flip_hom isSheafyForEveryPresentation_S isSheafyForEveryPresentation_T
    isSheafyForEveryPresentation_T isSheafyForEveryPresentation_completedTensor f f f_toRingHom
    f_toRingHom).symm

/-- `σ` exchanges the projections. -/
theorem σ_comp_pr₁ : σ ≫ pr₁ = pr₂ := by
  rw [σ, pr₁, pr₂, ← comapOfPair_comp, Pair.completedTensor.commHom_comp_inl]

/-- `σ` exchanges the projections. -/
theorem σ_comp_pr₂ : σ ≫ pr₂ = pr₁ := by
  rw [σ, pr₁, pr₂, ← comapOfPair_comp, Pair.completedTensor.commHom_comp_inr]

/-- `σ` is an involution. -/
theorem σ_comp_σ : σ ≫ σ = 𝟙 _ := by
  rw [σ, ← comapOfPair_comp, Pair.completedTensor.commHom_comp_commHom, comapOfPair_id]

/-- `σ` is an isomorphism of adic spaces. -/
example : IsIso σ :=
  ⟨σ, σ_comp_σ, σ_comp_σ⟩

/-! ### The points `X = 0` and `X = 1` -/

/-- The evaluation `X ↦ a` at a power-bounded `a ∈ ℚ₂`, as a morphism out of the polydisc pair
`(ℚ₂⟨X⟩, ℤ₂⟨X⟩)` of `Pair.polydisc`. -/
private noncomputable def evalAt {a : ℚ_[2]} (ha : IsPowerBounded a) :
    Pair.Hom (S.polydisc 1) S :=
  Pair.polydisc.evalHom (Pair.Hom.id S) fun _ ↦
    ⟨a, by rw [Pair.powerBounded_plus]; exact mem_powerBoundedSubring.mpr ha⟩

/-- The evaluation `X ↦ a` at a power-bounded `a ∈ ℚ₂`, a morphism `(ℚ₂⟨X⟩, ℤ₂⟨X⟩) → (ℚ₂, ℤ₂)`:
the ring map of `evalAt`, which also preserves the plus ring `ℤ₂⟨X⟩` of `T`. -/
private noncomputable def ev {a : ℚ_[2]} (ha : IsPowerBounded a) : T.Hom S :=
  Pair.powerBoundedHom (evalAt ha).toRingHom (evalAt ha).continuous_toRingHom

private theorem ev_toRingHom {a : ℚ_[2]} (ha : IsPowerBounded a) :
    (ev ha).toRingHom = (evalAt ha).toRingHom :=
  Pair.Hom.toRingHom_powerBoundedHom _ _

private theorem ev_polydiscVar {a : ℚ_[2]} (ha : IsPowerBounded a) :
    (ev ha).toRingHom (Pair.polydiscVar 1 ℚ_[2] 0) = a := by
  rw [ev_toRingHom, evalAt, Pair.polydisc.toRingHom_evalHom_polydiscVar]

private theorem ev_comp_f {a : ℚ_[2]} (ha : IsPowerBounded a) :
    (ev ha).comp f = Pair.Hom.id S := by
  apply Pair.Hom.ext
  ext c
  rw [Pair.Hom.toRingHom_comp, RingHom.comp_apply, f_toRingHom, ev_toRingHom, evalAt,
    Pair.polydisc.toRingHom_evalHom_algebraMap]

/-- At the point of `Spa D` pulled back from `x` along the evaluation `X ↦ a`, comparing valuations
of `g, h ∈ ℚ₂⟨X⟩` is comparing valuations at `x` of their values at `a`. -/
private theorem vle_ofPairHomeomorph_symm_spaComap_ev {a : ℚ_[2]} (ha : IsPowerBounded a)
    (x : spa S.plus) (g h : D) :
    (ofPairHomeomorph T isSheafyForEveryPresentation_T
        ((ofPairHomeomorph T _).symm ((ev ha).spaComap x))).val.toValuativeRel.vle g h ↔
      x.val.toValuativeRel.vle ((ev ha).toRingHom g) ((ev ha).toRingHom h) := by
  rw [Homeomorph.apply_symm_apply, Pair.Hom.spaComap_val, comap_vle]

/-- **The symmetry moves the point `X = 0, Y = 1` to the point `X = 1, Y = 0`.** The points
`y₀`, `y₁` of the disc `Spa D` cut out by `X = 0` and `X = 1` are distinct and lie over the same
point of `Spa ℚ₂`; a point `z` of `Spa D ×_{Spa ℚ₂} Spa D` with projections `(y₀, y₁)` exists, and
`σ` sends it to the distinct point with projections `(y₁, y₀)`, and back. -/
theorem exists_symmetry_moves_point :
    ∃ (y₀ y₁ : (ofPair T isSheafyForEveryPresentation_T).obj)
      (z : (ofPair _ isSheafyForEveryPresentation_completedTensor).obj),
      (ofPairHomeomorph T _ y₀).val.toValuativeRel.vle (Pair.polydiscVar 1 ℚ_[2] 0) 0 ∧
      (ofPairHomeomorph T _ y₁).val.toValuativeRel.vle (Pair.polydiscVar 1 ℚ_[2] 0 - 1) 0 ∧
      y₀ ≠ y₁ ∧
      (comapOfPair isSheafyForEveryPresentation_S _ f).hom.base y₀ =
        (comapOfPair isSheafyForEveryPresentation_S _ f).hom.base y₁ ∧
      pr₁.hom.base z = y₀ ∧ pr₂.hom.base z = y₁ ∧
      pr₁.hom.base (σ.hom.base z) = y₁ ∧ pr₂.hom.base (σ.hom.base z) = y₀ ∧
      σ.hom.base z ≠ z ∧ σ.hom.base (σ.hom.base z) = z := by
  have hne : (spa S.plus).Nonempty := Set.ne_empty_iff_nonempty.mp fun h ↦
    not_subsingleton ℚ_[2] ((spa_eq_empty_iff_subsingleton _ S.isRingOfIntegralElements).mp h)
  let x₀ : spa S.plus := ⟨hne.some, hne.some_mem⟩
  have h0 : IsPowerBounded (0 : ℚ_[2]) := by simp
  have h1 : IsPowerBounded (1 : ℚ_[2]) := by simp
  let y₀ : (ofPair T isSheafyForEveryPresentation_T).obj :=
    (ofPairHomeomorph T _).symm ((ev h0).spaComap x₀)
  let y₁ : (ofPair T isSheafyForEveryPresentation_T).obj :=
    (ofPairHomeomorph T _).symm ((ev h1).spaComap x₀)
  have hy (p : T.Hom S) (hp : p.comp f = Pair.Hom.id S) :
      (comapOfPair isSheafyForEveryPresentation_S isSheafyForEveryPresentation_T f).hom.base
          ((ofPairHomeomorph T _).symm (p.spaComap x₀)) =
        (ofPairHomeomorph S isSheafyForEveryPresentation_S).symm x₀ := by
    rw [comapOfPair_base_ofPairHomeomorph_symm]
    exact congrArg (ofPairHomeomorph S _).symm <|
      (congrFun (Pair.Hom.spaComap_comp p f) x₀).symm.trans <| by
        rw [hp, Pair.Hom.spaComap_id, id_eq]
  have hv₀ : (ofPairHomeomorph T _ y₀).val.toValuativeRel.vle (Pair.polydiscVar 1 ℚ_[2] 0) 0 := by
    simp [y₀, vle_ofPairHomeomorph_symm_spaComap_ev, ev_polydiscVar]
  have hv₁ :
      (ofPairHomeomorph T _ y₁).val.toValuativeRel.vle (Pair.polydiscVar 1 ℚ_[2] 0 - 1) 0 := by
    simp [y₁, vle_ofPairHomeomorph_symm_spaComap_ev, ev_polydiscVar]
  have hy_ne : y₀ ≠ y₁ := fun h ↦ by
    have hv := hv₀
    rw [h] at hv
    simp [y₁, vle_ofPairHomeomorph_symm_spaComap_ev, ev_polydiscVar] at hv
  have hy₀₁ : (comapOfPair isSheafyForEveryPresentation_S _ f).hom.base y₀ =
      (comapOfPair isSheafyForEveryPresentation_S _ f).hom.base y₁ :=
    (hy _ (ev_comp_f h0)).trans (hy _ (ev_comp_f h1)).symm
  obtain ⟨z, hz₁, hz₂⟩ := exists_ofPair_completedTensor_point isSheafyForEveryPresentation_S
    isSheafyForEveryPresentation_T isSheafyForEveryPresentation_T
    isSheafyForEveryPresentation_completedTensor f f f_toRingHom f_toRingHom y₀ y₁ hy₀₁
  replace hz₁ : pr₁.hom.base z = y₀ := by rw [pr₁]; exact hz₁
  replace hz₂ : pr₂.hom.base z = y₁ := by rw [pr₂]; exact hz₂
  have hσ₁ : pr₁.hom.base (σ.hom.base z) = y₁ := by
    rw [← comp_base_apply, ← ObjectProperty.FullSubcategory.comp_hom, σ_comp_pr₁, hz₂]
  have hσ₂ : pr₂.hom.base (σ.hom.base z) = y₀ := by
    rw [← comp_base_apply, ← ObjectProperty.FullSubcategory.comp_hom, σ_comp_pr₂, hz₁]
  refine ⟨y₀, y₁, z, hv₀, hv₁, hy_ne, hy₀₁, hz₁, hz₂, hσ₁, hσ₂, fun h ↦ hy_ne ?_, ?_⟩
  · rw [← hz₁, ← hσ₁, h]
  · rw [← comp_base_apply, ← ObjectProperty.FullSubcategory.comp_hom, σ_comp_σ,
      ObjectProperty.FullSubcategory.id_hom, id_base_apply]

/-! ### The unit -/

/-- **The unit on charts.** `Spa` of the left coprojection `ℚ₂⟨X⟩ → ℚ₂⟨X⟩ ⊗̂_{ℚ₂} ℚ₂` is an
isomorphism of adic spaces, with inverse `Spa` of the multiplication `b ⊗ a ↦ b·a`. -/
example :
    IsIso (comapOfPair isSheafyForEveryPresentation_T
      (isSheafyForEveryPresentation_T.completedTensor_rightUnitor S algebraMap_mem_plus_T)
      (Pair.completedTensor.inl ℚ_[2] T S)) :=
  rightUnitorAffinoid_hom S isSheafyForEveryPresentation_T algebraMap_mem_plus_T ▸
    (rightUnitorAffinoid S isSheafyForEveryPresentation_T algebraMap_mem_plus_T).isIso_hom

end TauCeti.Examples.SymmetryOnChartsSpaChecks
