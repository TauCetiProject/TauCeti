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
public import TauCeti.RingTheory.Huber.Restricted.Noetherian
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Complete
public import TauCeti.RingTheory.Huber.WeightedEval.Completion

/-!
# Checks for the symmetry and unit of fibre products of affinoid adic spaces

AdicEtaleGeometry A0.7, *symmetry_and_unit_on_charts_spa* and *symmetry_and_unit_on_charts_unit*,
over `ℚ₂` with the closed disc `D = Spa ℚ₂⟨T⟩`:

1. **Symmetry.** On `D ×_{Spa ℚ₂} D = Spa(ℚ₂⟨T⟩ ⊗̂ ℚ₂⟨S⟩)`, the morphism `σ`, `Spa` of the
   completed tensor symmetry, is the comparison of the pullback square with its flip
   (`TauCeti.AdicSpace.affinoid_isoIsPullback_flip_hom`), so an isomorphism. It exchanges the two
   projections and is an involution. The points `y₀`, `y₁` of `D` cut out by `T = 0` and `T = 1`
   are distinct and lie over the same point of `Spa ℚ₂`; a point `z` of the product with
   projections `(y₀, y₁)` (cut out by `T = 0, S = 1`) goes to the distinct point `σ z` with
   projections `(y₁, y₀)` (cut out by `T = 1, S = 0`), and back.
2. **Unit.** `Spa` of the left coprojection `ℚ₂⟨T⟩ → ℚ₂⟨T⟩ ⊗̂_{ℚ₂} ℚ₂` is an isomorphism of
   adic spaces, with inverse `Spa` of `b ⊗ a ↦ b·a` (`TauCeti.AdicSpace.rightUnitorAffinoid`).
-/

public section

open CategoryTheory TauCeti TauCeti.Huber TauCeti.PreAdicSpace TauCeti.ValuationSpectrum
  TauCeti.AdicSpace

namespace SymmetryOnChartsSpaChecks

/-- The Tate algebra `ℚ₂⟨T⟩` of the closed unit disc. -/
noncomputable abbrev D : Type := restrictedMvPowerSeriesCompletion 1 ℚ_[2]

/-- `ℚ₂ → ℚ₂⟨T⟩` is topologically of finite type. -/
theorem htft : IsTopologicallyFiniteType (algebraMap ℚ_[2] D) :=
  (isStrictlyTopologicallyFiniteType_algebraMap (A := ℚ_[2]) 1).isTopologicallyFiniteType

/-- `ℚ₂ → ℚ₂⟨T⟩` is adic. -/
instance instIsAdicHomD : IsAdicHom (algebraMap ℚ_[2] D) := htft.isAdicHom
/-- `ℚ₂⟨T⟩` is a Tate ring. -/
instance instIsTateRingD : IsTateRing D := htft.isTateRing
/-- `ℚ₂⟨T⟩` is strongly noetherian. -/
instance instIsStronglyNoetherianD : IsStronglyNoetherian D := htft.isStronglyNoetherian

/-- The Huber pair of `Spa ℚ₂`. -/
noncomputable abbrev S : Pair ℚ_[2] := Pair.powerBounded ℚ_[2]

/-- The Huber pair of the disc `Spa ℚ₂⟨T⟩`. -/
noncomputable abbrev T : Pair D := Pair.powerBounded D

/-- The structure morphism `(ℚ₂, ℤ₂) → (ℚ₂⟨T⟩, ℤ₂⟨T⟩)`. -/
noncomputable def f : S.Hom T where
  toRingHom := algebraMap ℚ_[2] D
  continuous_toRingHom := continuous_algebraMap_restrictedMvPowerSeriesCompletion 1 ℚ_[2]
  map_mem_plus _ ha := by
    rw [Pair.powerBounded_plus] at ha ⊢
    exact mem_powerBoundedSubring.mpr <| (mem_powerBoundedSubring.mp ha).map_of_isTateRing
      (continuous_algebraMap_restrictedMvPowerSeriesCompletion 1 ℚ_[2]).continuousAt

/-- `(ℚ₂, ℤ₂)` is sheafy. -/
theorem hS : IsSheafyForEveryPresentation S.plus :=
  isSheafyForEveryPresentation_of_isStronglyNoetherian S.isRingOfIntegralElements

/-- `(ℚ₂⟨T⟩, ℤ₂⟨T⟩)` is sheafy. -/
theorem hT : IsSheafyForEveryPresentation T.plus :=
  isSheafyForEveryPresentation_of_isStronglyNoetherian T.isRingOfIntegralElements

/-- `ℚ₂⟨T⟩ ⊗̂_{ℚ₂} ℚ₂⟨S⟩` is sheafy. -/
theorem hTT : IsSheafyForEveryPresentation (T.completedTensor ℚ_[2] T).plus :=
  isSheafyForEveryPresentation_completedTensor_of_isStablySheafyRing_left T T
    isStablySheafyRing_of_isStronglyNoetherian htft

/-- The first projection `D ×_{Spa ℚ₂} D ⟶ D`. -/
noncomputable def pr₁ : ofPair _ hTT ⟶ ofPair T hT :=
  comapOfPair hT hTT (Pair.completedTensor.inl ℚ_[2] T T)

/-- The second projection `D ×_{Spa ℚ₂} D ⟶ D`. -/
noncomputable def pr₂ : ofPair _ hTT ⟶ ofPair T hT :=
  comapOfPair hT hTT (Pair.completedTensor.inr ℚ_[2] T T)

/-- The symmetry `σ` of `D ×_{Spa ℚ₂} D`, `Spa` of the completed tensor symmetry. -/
noncomputable def σ : ofPair _ hTT ⟶ ofPair _ hTT :=
  comapOfPair hTT hTT (Pair.completedTensor.commHom ℚ_[2] T T)

/-- `σ` is the comparison of the chart pullback square with its flip. -/
example : σ = ((affinoid_isPullback hS hT hT hTT f f rfl rfl).isoIsPullback _ _
    (affinoid_isPullback hS hT hT hTT.completedTensor_comm f f rfl rfl).flip).hom :=
  (affinoid_isoIsPullback_flip_hom hS hT hT hTT f f rfl rfl).symm

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

/-! ### The points `T = 0` and `T = 1` -/

theorem isWeightBounded_const {a : ℚ_[2]} (ha : IsPowerBounded a) :
    IsWeightBounded (RingHom.id ℚ_[2]) (fun _ : Fin 1 ↦ ({1} : Set ℚ_[2])) fun _ ↦ a :=
  (isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr fun _ ↦ ha

/-- The evaluation `T ↦ a` at a power-bounded `a ∈ ℚ₂`, a morphism `(ℚ₂⟨T⟩, ℤ₂⟨T⟩) → (ℚ₂, ℤ₂)`. -/
noncomputable def ev {a : ℚ_[2]} (ha : IsPowerBounded a) : T.Hom S where
  toRingHom := weightedEvalHomCompletion isWeightFamily_one_weight continuousAt_id
    (isWeightBounded_const ha)
  continuous_toRingHom := continuous_weightedEvalHomCompletion _ _ _
  map_mem_plus _ hx := by
    rw [Pair.powerBounded_plus] at hx ⊢
    exact mem_powerBoundedSubring.mpr <| (mem_powerBoundedSubring.mp hx).map_of_isTateRing
      (continuous_weightedEvalHomCompletion _ _ _).continuousAt

/-- The coordinate `T` of `ℚ₂⟨T⟩`. -/
noncomputable def X : D :=
  ((weightedX _ isWeightFamily_one_weight 0 :
    weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set ℚ_[2])) isWeightFamily_one_weight) : D)

theorem ev_X {a : ℚ_[2]} (ha : IsPowerBounded a) : (ev ha).toRingHom X = a := by
  rw [ev, X]
  dsimp only
  rw [weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]

theorem ev_comp_f {a : ℚ_[2]} (ha : IsPowerBounded a) : (ev ha).comp f = Pair.Hom.id S := by
  apply Pair.Hom.ext
  ext c
  simp only [Pair.Hom.toRingHom_comp, Pair.Hom.toRingHom_id, RingHom.comp_apply, RingHom.id_apply]
  rw [f, ev]
  dsimp only
  rw [algebraMap_completion_weightedRestrictedSubring_apply, weightedEvalHomCompletion_coe,
    weightedEvalHom_weightedC, RingHom.id_apply]

/-- The base map of a composite with a projection, on a point of `D ×_{Spa ℚ₂} D`. -/
theorem comp_base_apply (g : ofPair _ hTT ⟶ ofPair _ hTT) (h : ofPair _ hTT ⟶ ofPair T hT)
    (w : (ofPair _ hTT).obj) : (g ≫ h).hom.base w = h.hom.base (g.hom.base w) :=
  rfl

/-- The base map of a composite of endomorphisms of `D ×_{Spa ℚ₂} D`, on a point. -/
theorem comp_base_apply' (g h : ofPair _ hTT ⟶ ofPair _ hTT) (w : (ofPair _ hTT).obj) :
    (g ≫ h).hom.base w = h.hom.base (g.hom.base w) :=
  rfl

/-- **The symmetry moves the point `T = 0, S = 1` to the point `T = 1, S = 0`.** The points
`y₀`, `y₁` of the disc cut out by `T = 0` and `T = 1` are distinct and lie over the same point of
`Spa ℚ₂`; a point `z` of `D ×_{Spa ℚ₂} D` with projections `(y₀, y₁)` exists, and `σ` sends it to
the distinct point with projections `(y₁, y₀)`, and back. -/
theorem exists_symmetry_moves_point :
    ∃ (y₀ y₁ : (ofPair T hT).obj) (z : (ofPair _ hTT).obj),
      (ofPairHomeomorph T hT y₀).val.toValuativeRel.vle X 0 ∧
      (ofPairHomeomorph T hT y₁).val.toValuativeRel.vle (X - 1) 0 ∧ y₀ ≠ y₁ ∧
      (comapOfPair hS hT f).hom.base y₀ = (comapOfPair hS hT f).hom.base y₁ ∧
      pr₁.hom.base z = y₀ ∧ pr₂.hom.base z = y₁ ∧
      pr₁.hom.base (σ.hom.base z) = y₁ ∧ pr₂.hom.base (σ.hom.base z) = y₀ ∧
      σ.hom.base z ≠ z ∧ σ.hom.base (σ.hom.base z) = z := by
  have hne : (spa S.plus).Nonempty := Set.ne_empty_iff_nonempty.mp fun h ↦
    not_subsingleton ℚ_[2] ((spa_eq_empty_iff_subsingleton _ S.isRingOfIntegralElements).mp h)
  let x₀ : spa S.plus := ⟨hne.some, hne.some_mem⟩
  have h0 : IsPowerBounded (0 : ℚ_[2]) := by simp
  have h1 : IsPowerBounded (1 : ℚ_[2]) := by simp
  let y₀ : (ofPair T hT).obj := (ofPairHomeomorph T hT).symm ((ev h0).spaComap x₀)
  let y₁ : (ofPair T hT).obj := (ofPairHomeomorph T hT).symm ((ev h1).spaComap x₀)
  have hy {a : ℚ_[2]} (ha : IsPowerBounded a) :
      (comapOfPair hS hT f).hom.base ((ofPairHomeomorph T hT).symm ((ev ha).spaComap x₀)) =
        (ofPairHomeomorph S hS).symm x₀ := by
    rw [comapOfPair_base_ofPairHomeomorph_symm]
    exact congrArg (ofPairHomeomorph S hS).symm <|
      (congrFun (Pair.Hom.spaComap_comp (ev ha) f) x₀).symm.trans <| by
        rw [ev_comp_f, Pair.Hom.spaComap_id, id_eq]
  have hv₀ : (ofPairHomeomorph T hT y₀).val.toValuativeRel.vle X 0 := by
    rw [Homeomorph.apply_symm_apply, Pair.Hom.spaComap_val, comap_vle]
    simp [ev_X]
  have hv₁ : (ofPairHomeomorph T hT y₁).val.toValuativeRel.vle (X - 1) 0 := by
    rw [Homeomorph.apply_symm_apply, Pair.Hom.spaComap_val, comap_vle]
    simp [ev_X]
  have hy_ne : y₀ ≠ y₁ := fun h ↦ by
    have hv := hv₀
    rw [h, Homeomorph.apply_symm_apply, Pair.Hom.spaComap_val, comap_vle] at hv
    simp [ev_X] at hv
  obtain ⟨z, hz₁, hz₂⟩ := exists_ofPair_completedTensor_point hS hT hT hTT f f rfl rfl
    y₀ y₁ ((hy h0).trans (hy h1).symm)
  have hσ₁ : pr₁.hom.base (σ.hom.base z) = y₁ := by
    rw [← comp_base_apply, σ_comp_pr₁]
    exact hz₂
  have hσ₂ : pr₂.hom.base (σ.hom.base z) = y₀ := by
    rw [← comp_base_apply, σ_comp_pr₂]
    exact hz₁
  refine ⟨y₀, y₁, z, hv₀, hv₁, hy_ne, (hy h0).trans (hy h1).symm, hz₁, hz₂, hσ₁, hσ₂,
    fun h ↦ hy_ne ?_, ?_⟩
  · rw [← hz₁, ← hσ₁, h]
    rfl
  · rw [← comp_base_apply', σ_comp_σ]
    rfl

/-! ### The unit -/

/-- **The unit on charts.** `Spa` of the left coprojection `ℚ₂⟨T⟩ → ℚ₂⟨T⟩ ⊗̂_{ℚ₂} ℚ₂` is an
isomorphism of adic spaces, with inverse `Spa` of the multiplication `b ⊗ a ↦ b·a`. -/
example :
    IsIso (comapOfPair hT (hT.completedTensor_rightUnitor S f.map_mem_plus)
      (Pair.completedTensor.inl ℚ_[2] T S)) :=
  rightUnitorAffinoid_hom S hT f.map_mem_plus ▸
    (rightUnitorAffinoid S hT f.map_mem_plus).isIso_hom

end SymmetryOnChartsSpaChecks
