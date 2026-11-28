/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.Universal
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.Residual
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Representable
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

/-!
# Adding a point to an effective divisor

For a proper smooth relative curve, adding the graph of a point gives a morphism from
`Divᵈ ×_S X` to `Divᵈ⁺¹`, whenever these divisor functors are represented. The source identifies
with the universal divisor over `Divᵈ⁺¹`: the inverse removes the chosen point by colon
subtraction. Consequently addition is finite flat of degree `d + 1`.

## References

* The Stacks Project, Tags 0B9I and 0B9J.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  Opposite TauCeti.AlgebraicGeometry

universe u

namespace CategoryTheory.Functor.RepresentableBy

variable {X S : Scheme.{u}} {f : X ⟶ S} [IsProper f] [SmoothOfRelativeDimension 1 f]
  {d : ℕ} {H H' : Over S}

/-- Add the graph of a point to the universal degree-`d` divisor. -/
def effectiveCartierAddition
    (e : (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.RepresentableBy H)
    (e' : (relativeEffectiveCartierDegreeSubfunctor f (d + 1)).toFunctor.RepresentableBy H') :
    H ⊗ Over.mk f ⟶ H' :=
  e'.homEquiv.symm
    ⟨(e.homEquiv (fst H (Over.mk f))).val *
      ((graphDivisorDegreeOne f).app (op (H ⊗ Over.mk f)) (snd H (Over.mk f))).val,
      mul_mem_relativeEffectiveCartierDegreeSubfunctor_obj f
        (e.homEquiv (fst H (Over.mk f))).property
        ((graphDivisorDegreeOne f).app (op (H ⊗ Over.mk f))
          (snd H (Over.mk f))).property⟩

/-- On arbitrary test schemes, addition multiplies the ideal of the divisor by the graph ideal
of the chosen point. -/
-- Spell out the underlying relative-divisor carrier so this law matches ordinary simp goals.
@[simp↓]
theorem homEquiv_lift_comp_effectiveCartierAddition_val
    (e : (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.RepresentableBy H)
    (e' : (relativeEffectiveCartierDegreeSubfunctor f (d + 1)).toFunctor.RepresentableBy H')
    {T : Over S} (z : T ⟶ H) (x : T ⟶ Over.mk f) :
    Subtype.val (α := (relativeEffectiveCartierSubfunctor f).obj (op T))
      (e'.homEquiv (lift z x ≫ e.effectiveCartierAddition e')) =
      (e.homEquiv z).val * (graphDivisor f).app (op T) x := by
  rw [e'.homEquiv_comp_val, effectiveCartierAddition, Equiv.apply_symm_apply,
    relativeEffectiveCartier_map_mul]
  have hz := e.homEquiv_comp_val (lift z x) (fst H (Over.mk f))
  simp only [lift_fst] at hz
  rw [← hz, graphDivisorDegreeOne_app_apply_val,
    ← graphDivisor_app_eq_map_of_comp_eq (lift z x) (snd H (Over.mk f)) (lift_snd z x)]

variable (e : (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.RepresentableBy H)
  (e' : (relativeEffectiveCartierDegreeSubfunctor f (d + 1)).toFunctor.RepresentableBy H')

/-- The divisor classified by addition is the product of the divisor and the graph of its
marked point. -/
@[simp↓]
theorem homEquiv_effectiveCartierAddition_val :
    (e'.homEquiv (e.effectiveCartierAddition e')).val =
      (e.homEquiv (fst H (Over.mk f))).val *
        (graphDivisor f).app (op (H ⊗ Over.mk f)) (snd H (Over.mk f)) := by
  simpa only [lift_fst_snd, Category.id_comp] using
    e.homEquiv_lift_comp_effectiveCartierAddition_val e' (fst H (Over.mk f)) (snd H (Over.mk f))

/-- The point added to a divisor lies on the resulting universal divisor. -/
theorem effectiveCartierUniversalIdeal_le_ker_lift_effectiveCartierAddition :
    e'.effectiveCartierUniversalIdeal ≤
      (lift (e.effectiveCartierAddition e') (snd H (Over.mk f))).left.ker := by
  rw [← graphSection_comp_pullback_map_eq_lift]
  simp only [← Scheme.IdealSheafData.map_ker,
    Scheme.IdealSheafData.le_map_iff_comap_le, e'.effectiveCartierUniversalIdeal_comap,
    congrArg Subtype.val (e.homEquiv_effectiveCartierAddition_val e'),
    relativeEffectiveCartier_val_mul]
  rw [graphDivisor_app_apply_val]
  apply mul_le_of_le_one_left
  · simp only [Scheme.IdealSheafData.zero_eq_bot, bot_le]
  · simp only [Scheme.IdealSheafData.one_eq_top, le_top]

/-- The morphism from a divisor with a marked added point to the universal divisor. -/
def effectiveCartierAdditionToUniversal :
    H ⊗ Over.mk f ⟶ e'.effectiveCartierUniversalDivisor := by
  let φ := IsClosedImmersion.lift e'.effectiveCartierUniversalIdeal.subschemeι
    (lift (e.effectiveCartierAddition e') (snd H (Over.mk f))).left
    (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact e.effectiveCartierUniversalIdeal_le_ker_lift_effectiveCartierAddition e')
  have hφ : φ ≫ e'.effectiveCartierUniversalIdeal.subschemeι =
      (lift (e.effectiveCartierAddition e') (snd H (Over.mk f))).left :=
    IsClosedImmersion.lift_fac _ _ _
  refine Over.homMk φ ?_
  simp [reassoc_of% hφ]

/-- The comparison with the universal divisor remembers the sum and its marked point. -/
@[reassoc (attr := simp)]
theorem effectiveCartierAdditionToUniversal_subschemeι :
    (e.effectiveCartierAdditionToUniversal e').left ≫
        e'.effectiveCartierUniversalIdeal.subschemeι =
      (lift (e.effectiveCartierAddition e') (snd H (Over.mk f))).left :=
  IsClosedImmersion.lift_fac _ _ _

/-- The comparison to the universal divisor lies over the addition map. -/
@[reassoc (attr := simp)]
theorem effectiveCartierAdditionToUniversal_projection :
    e.effectiveCartierAdditionToUniversal e' ≫ e'.effectiveCartierUniversalProjection =
      e.effectiveCartierAddition e' := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, effectiveCartierUniversalProjection_left, ← Category.assoc,
    effectiveCartierAdditionToUniversal_subschemeι, Over.lift_left]
  exact pullback.lift_fst _ _ _

/-- The underlying addition morphism factors through its comparison with the universal divisor
and the universal divisor's projection. -/
theorem effectiveCartierAddition_left_eq :
    (e.effectiveCartierAddition e').left =
      (e.effectiveCartierAdditionToUniversal e').left ≫
        e'.effectiveCartierUniversalIdeal.subschemeι ≫ pullback.fst H'.hom f := by
  rw [← effectiveCartierAdditionToUniversal_projection, Over.comp_left,
    effectiveCartierUniversalProjection_left]

/-- The comparison to the universal divisor remembers the point that was added. -/
@[reassoc (attr := simp)]
theorem effectiveCartierAdditionToUniversal_point :
    e.effectiveCartierAdditionToUniversal e' ≫ e'.effectiveCartierUniversalPoint =
      snd H (Over.mk f) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, effectiveCartierUniversalPoint_left, ← Category.assoc,
    effectiveCartierAdditionToUniversal_subschemeι, Over.lift_left]
  exact pullback.lift_snd _ _ _

/-- The divisor classified by the universal projection contains the degree-one graph of its
marked point, with the reversed order on defining ideals. -/
theorem homEquiv_effectiveCartierUniversalProjection_le_graphDivisorDegreeOne
    {n : ℕ} {K : Over S}
    (r : (relativeEffectiveCartierDegreeSubfunctor f n).toFunctor.RepresentableBy K) :
    (r.homEquiv r.effectiveCartierUniversalProjection).val.val ≤
      ((graphDivisorDegreeOne f).app (op r.effectiveCartierUniversalDivisor)
        r.effectiveCartierUniversalPoint).val.val := by
  rw [graphDivisorDegreeOne_app_apply_val, graphDivisor_app_apply_val]
  exact r.homEquiv_effectiveCartierUniversalProjection_le_ker_graphSection

/-- Remove the marked point of the universal degree-`d+1` divisor. -/
def effectiveCartierUniversalResidual :
    (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.obj
      (op e'.effectiveCartierUniversalDivisor) :=
  relativeEffectiveCartierDegreeResidual f
    (e'.homEquiv e'.effectiveCartierUniversalProjection)
    ((graphDivisorDegreeOne f).app (op e'.effectiveCartierUniversalDivisor)
      e'.effectiveCartierUniversalPoint)
    e'.homEquiv_effectiveCartierUniversalProjection_le_graphDivisorDegreeOne

/-- The universal residual is the degree residual of the classified divisor and marked graph. -/
theorem effectiveCartierUniversalResidual_def :
    e'.effectiveCartierUniversalResidual =
      relativeEffectiveCartierDegreeResidual f
        (e'.homEquiv e'.effectiveCartierUniversalProjection)
        ((graphDivisorDegreeOne f).app (op e'.effectiveCartierUniversalDivisor)
          e'.effectiveCartierUniversalPoint)
        e'.homEquiv_effectiveCartierUniversalProjection_le_graphDivisorDegreeOne := (rfl)

/-- Adding back the universal marked point recovers its divisor. -/
@[simp↓]
theorem effectiveCartierUniversalResidual_mul :
    e'.effectiveCartierUniversalResidual.val *
        (graphDivisor f).app (op e'.effectiveCartierUniversalDivisor)
          e'.effectiveCartierUniversalPoint =
      (e'.homEquiv e'.effectiveCartierUniversalProjection).val := by
  rw [effectiveCartierUniversalResidual_def]
  rw [← graphDivisorDegreeOne_app_apply_val]
  exact relativeEffectiveCartierDegreeResidual_mul f
      (e'.homEquiv e'.effectiveCartierUniversalProjection)
      ((graphDivisorDegreeOne f).app (op e'.effectiveCartierUniversalDivisor)
        e'.effectiveCartierUniversalPoint)
      _

/-- The universal divisor maps to `Divᵈ ×_S X` by removing and remembering its marked point. -/
def effectiveCartierUniversalToAddition :
    e'.effectiveCartierUniversalDivisor ⟶ H ⊗ Over.mk f :=
  lift (e.homEquiv.symm e'.effectiveCartierUniversalResidual) e'.effectiveCartierUniversalPoint

/-- The first component of the inverse comparison classifies the residual divisor. -/
@[reassoc (attr := simp)]
theorem effectiveCartierUniversalToAddition_fst :
    e.effectiveCartierUniversalToAddition e' ≫ fst H (Over.mk f) =
      e.homEquiv.symm e'.effectiveCartierUniversalResidual :=
  lift_fst _ _

/-- The second component of the inverse comparison is the universal marked point. -/
@[reassoc (attr := simp)]
theorem effectiveCartierUniversalToAddition_snd :
    e.effectiveCartierUniversalToAddition e' ≫ snd H (Over.mk f) =
      e'.effectiveCartierUniversalPoint :=
  lift_snd _ _

/-- The residual divisor and its marked point add to the universal divisor. -/
@[reassoc (attr := simp)]
theorem effectiveCartierUniversalToAddition_addition :
    e.effectiveCartierUniversalToAddition e' ≫ e.effectiveCartierAddition e' =
      e'.effectiveCartierUniversalProjection := by
  apply e'.homEquiv.injective
  apply Subtype.ext
  rw [effectiveCartierUniversalToAddition, homEquiv_lift_comp_effectiveCartierAddition_val,
    Equiv.apply_symm_apply, effectiveCartierUniversalResidual_mul]

private theorem universalToAddition_comp_additionToUniversal :
    e.effectiveCartierUniversalToAddition e' ≫ e.effectiveCartierAdditionToUniversal e' =
      𝟙 e'.effectiveCartierUniversalDivisor := by
  apply Over.OverMorphism.ext
  apply (cancel_mono e'.effectiveCartierUniversalIdeal.subschemeι).mp
  have h : e.effectiveCartierUniversalToAddition e' ≫
      lift (e.effectiveCartierAddition e') (snd H (Over.mk f)) =
      lift e'.effectiveCartierUniversalProjection e'.effectiveCartierUniversalPoint := by
    simp [comp_lift]
  simpa only [Over.comp_left, Over.id_left, Category.assoc,
    effectiveCartierAdditionToUniversal_subschemeι, Category.id_comp,
    lift_effectiveCartierUniversalProjection_effectiveCartierUniversalPoint_left]
      using congrArg (fun g => g.left) h

private theorem additionToUniversal_residual :
    e.effectiveCartierAdditionToUniversal e' ≫
        e.homEquiv.symm e'.effectiveCartierUniversalResidual = fst H (Over.mk f) := by
  apply e.homEquiv.injective
  simp only [e.homEquiv_comp, Equiv.apply_symm_apply, effectiveCartierUniversalResidual_def,
    relativeEffectiveCartierDegreeResidual_map]
  apply (relativeEffectiveCartierDegreeResidual_eq_iff f _ _ _ _).mpr
  have h := e'.homEquiv_comp (e.effectiveCartierAdditionToUniversal e')
    e'.effectiveCartierUniversalProjection
  simp only [effectiveCartierAdditionToUniversal_projection] at h
  have hPoint := graphDivisor_app_eq_map_of_comp_eq (e.effectiveCartierAdditionToUniversal e')
    _ (e.effectiveCartierAdditionToUniversal_point e')
  simp only [← h, Subfunctor.toFunctor_map_val]
  rw [graphDivisorDegreeOne_app_apply_val]
  simpa only [← hPoint] using (e.homEquiv_effectiveCartierAddition_val e').symm

private theorem additionToUniversal_comp_universalToAddition :
    e.effectiveCartierAdditionToUniversal e' ≫ e.effectiveCartierUniversalToAddition e' =
      𝟙 (H ⊗ Over.mk f) := by
  rw [effectiveCartierUniversalToAddition, comp_lift, additionToUniversal_residual,
    effectiveCartierAdditionToUniversal_point, lift_fst_snd]

/-- Adding a point identifies `Divᵈ ×_S X` with the total space of the universal divisor over
`Divᵈ⁺¹`. Its inverse sends a marked divisor to its residual and its marked point. -/
def effectiveCartierAdditionUniversalIso :
    H ⊗ Over.mk f ≅ e'.effectiveCartierUniversalDivisor where
  hom := e.effectiveCartierAdditionToUniversal e'
  inv := e.effectiveCartierUniversalToAddition e'
  hom_inv_id := e.additionToUniversal_comp_universalToAddition e'
  inv_hom_id := e.universalToAddition_comp_additionToUniversal e'

/-- The forward universal-divisor comparison is the map that remembers the sum and point. -/
@[simp]
theorem effectiveCartierAdditionUniversalIso_hom :
    (e.effectiveCartierAdditionUniversalIso e').hom =
      e.effectiveCartierAdditionToUniversal e' := (rfl)

/-- The inverse universal-divisor comparison removes the marked point by colon subtraction. -/
@[simp]
theorem effectiveCartierAdditionUniversalIso_inv :
    (e.effectiveCartierAdditionUniversalIso e').inv =
      e.effectiveCartierUniversalToAddition e' := (rfl)

instance : IsIso (e.effectiveCartierAdditionToUniversal e').left := by
  rw [← effectiveCartierAdditionUniversalIso_hom]
  infer_instance

instance : IsFinite (e.effectiveCartierAddition e').left := by
  rw [effectiveCartierAddition_left_eq]
  infer_instance

instance : Flat (e.effectiveCartierAddition e').left := by
  rw [effectiveCartierAddition_left_eq]
  infer_instance

instance : LocallyOfFinitePresentation (e.effectiveCartierAddition e').left := by
  have := SmoothOfRelativeDimension.smooth 1 f
  rw [effectiveCartierAddition_left_eq]
  infer_instance

/-- The fiber of the addition map over each point of `H'` has rank `d + 1`. -/
@[simp]
theorem finrank_effectiveCartierAddition_left (t : H'.left) :
    (e.effectiveCartierAddition e').left.finrank t = d + 1 := by
  rw [effectiveCartierAddition_left_eq, Scheme.Hom.finrank_comp_left_of_isIso,
    finrank_effectiveCartierUniversalIdeal_subschemeι_comp_fst]

instance : Surjective (e.effectiveCartierAddition e').left :=
  (Scheme.Hom.one_le_finrank_iff_surjective _).mp fun t ↦ by simp

end CategoryTheory.Functor.RepresentableBy
