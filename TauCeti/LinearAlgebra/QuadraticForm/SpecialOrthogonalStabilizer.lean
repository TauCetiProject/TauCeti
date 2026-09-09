/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup

/-!
# The last-vector stabilizer in a special orthogonal group

Let `Q` be a quadratic form on a finite free module `M`. Extending an element of `SO(Q)` by the
identity on a rank-one summand embeds it into `SO(Q.prod QuadraticMap.sq)`. If two acts regularly on
the base ring, its image is exactly the stabilizer of the last basis vector `(0, 1)`.

The inverse map restricts a stabilizer element to the first summand. Orthogonality and fixation of
`(0, 1)` force that summand to be preserved: polarizing the image of `(m, 0)` against `(0, 1)`
shows that twice its last coordinate vanishes. The determinant-one condition then descends because
the original map is the product of its restriction with the identity of the last summand.

This calculation is useful for inductive comparisons of orthogonal and Spin groups: after applying
a Spin action, it turns fixation of the last vector into a lower-rank special orthogonal
transformation.

## Main definitions

* `specialOrthogonalGroupProdLastInclusion`: extend a special orthogonal transformation by the
  identity on the square line.
* `specialOrthogonalGroupProdLastInclusionToStabilizer`: the same extension, codrestricted to the
  last-vector stabilizer.
* `specialOrthogonalGroupProdLastStabilizer`: the subgroup fixing `(0, 1)`.
* `specialOrthogonalGroupEquivProdLastStabilizer`: the extension-restriction equivalence between
  `SO(Q)` and that stabilizer.
-/

public section

open QuadraticMap

universe u v

namespace QuadraticMap

open TauCeti.QuadraticMap

noncomputable section

variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]

private def specialOrthogonalProdLastExtension (Q : QuadraticForm R M)
    (f : specialOrthogonalGroup Q) : (M × R) ≃ₗ[R] (M × R) :=
  (f : M ≃ₗ[R] M).prodCongr (LinearEquiv.refl R R)

private theorem specialOrthogonalProdLastExtension_mem (Q : QuadraticForm R M)
    [Module.Free R M] [Module.Finite R M] (f : specialOrthogonalGroup Q) :
    specialOrthogonalProdLastExtension Q f ∈ specialOrthogonalGroup
      (Q.prod (QuadraticMap.sq (R := R) (A := R))) := by
  have hf := mem_specialOrthogonalGroup_iff.mp f.2
  apply mem_specialOrthogonalGroup_iff.mpr
  constructor
  · apply mem_orthogonalGroup_iff.mpr
    intro x
    let e := (orthogonalGroupEquivIsometryEquiv Q
      ⟨f, specialOrthogonalGroup_le_orthogonalGroup Q f.2⟩).prod
        (QuadraticMap.IsometryEquiv.refl (QuadraticMap.sq (R := R) (A := R)))
    have he : e x = specialOrthogonalProdLastExtension Q f x := by
      apply Prod.ext
      -- Expose the first component so the orthogonal-group/isometry coercion lemma applies.
      · change (orthogonalGroupEquivIsometryEquiv Q _ x.1) = f.1 x.1
        exact congrFun (coe_orthogonalGroupEquivIsometryEquiv Q _) x.1
      · rfl
    rw [← he]
    exact e.map_app x
  · apply Units.ext
    rw [LinearEquiv.coe_det, specialOrthogonalProdLastExtension,
      LinearEquiv.coe_prodCongr, LinearMap.det_prodMap]
    have hrefl :
        LinearMap.det ((LinearEquiv.refl R R : R ≃ₗ[R] R) : R →ₗ[R] R) = 1 := by
      simp
    rw [hrefl, mul_one]
    simpa only [LinearEquiv.coe_det] using congrArg Units.val hf.2

/-- Extend a special orthogonal transformation by the identity on the square line. -/
def specialOrthogonalGroupProdLastInclusion (Q : QuadraticForm R M)
    [Module.Free R M] [Module.Finite R M] :
    specialOrthogonalGroup Q →* specialOrthogonalGroup
      (Q.prod (QuadraticMap.sq (R := R) (A := R))) where
  toFun f :=
    ⟨specialOrthogonalProdLastExtension Q f, specialOrthogonalProdLastExtension_mem Q f⟩
  map_one' := by
    ext x <;> simp [specialOrthogonalProdLastExtension]
  map_mul' f g := by
    ext x <;> simp [specialOrthogonalProdLastExtension]

/-- Extending a special orthogonal transformation acts componentwise and fixes the square-line
coordinate. -/
@[simp]
theorem specialOrthogonalGroupProdLastInclusion_apply (Q : QuadraticForm R M)
    [Module.Free R M] [Module.Finite R M] (f : specialOrthogonalGroup Q) (x : M × R) :
    ((specialOrthogonalGroupProdLastInclusion Q f :
      specialOrthogonalGroup _) : (M × R) ≃ₗ[R] (M × R)) x =
      ((f : M ≃ₗ[R] M) x.1, x.2) := by
  rfl

/-- Extension by the identity on the square line is injective. -/
theorem specialOrthogonalGroupProdLastInclusion_injective (Q : QuadraticForm R M)
    [Module.Free R M] [Module.Finite R M] :
    Function.Injective (specialOrthogonalGroupProdLastInclusion Q) := by
  intro f g h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro m
  have h' := congrArg
    (fun k : specialOrthogonalGroup
        (Q.prod (QuadraticMap.sq (R := R) (A := R))) =>
      (((k : (M × R) ≃ₗ[R] (M × R)) (m, 0)).1)) h
  simpa using h'

/-- The stabilizer of the last basis vector `(0, 1)` in the special orthogonal group of
`Q.prod QuadraticMap.sq`. -/
def specialOrthogonalGroupProdLastStabilizer (Q : QuadraticForm R M) :
    Subgroup (specialOrthogonalGroup
      (Q.prod (QuadraticMap.sq (R := R) (A := R)))) :=
  MulAction.stabilizer
    (specialOrthogonalGroup (Q.prod (QuadraticMap.sq (R := R) (A := R))))
    ((0 : M), (1 : R))

/-- Membership in the last-vector stabilizer means exactly that the underlying linear
transformation fixes `(0, 1)`. -/
@[simp]
theorem mem_specialOrthogonalGroupProdLastStabilizer_iff
    (Q : QuadraticForm R M)
    {g : specialOrthogonalGroup (Q.prod (QuadraticMap.sq (R := R) (A := R)))} :
    g ∈ specialOrthogonalGroupProdLastStabilizer Q ↔
      (g : (M × R) ≃ₗ[R] (M × R)) ((0 : M), (1 : R)) = (0, 1) :=
  MulAction.mem_stabilizer_iff

/-- Extension by the identity on the square line fixes the last basis vector. -/
theorem specialOrthogonalGroupProdLastInclusion_mem_stabilizer
    (Q : QuadraticForm R M) [Module.Free R M] [Module.Finite R M]
    (f : specialOrthogonalGroup Q) :
    specialOrthogonalGroupProdLastInclusion Q f ∈
      specialOrthogonalGroupProdLastStabilizer Q := by
  rw [mem_specialOrthogonalGroupProdLastStabilizer_iff]
  exact Prod.ext (by simp) (by simp)

/-- A last-vector stabilizer element maps the first summand back into the first summand. -/
@[simp]
theorem specialOrthogonalGroupProdLastStabilizer_apply_snd
    (Q : QuadraticForm R M) (h2 : IsRegular (2 : R))
    (g : specialOrthogonalGroupProdLastStabilizer Q) (m : M) :
    (g.1.1 (m, 0)).2 = 0 := by
  have hfix : g.1.1 ((0 : M), (1 : R)) = ((0 : M), (1 : R)) :=
    mem_specialOrthogonalGroupProdLastStabilizer_iff Q |>.mp g.2
  have hg := mem_specialOrthogonalGroup_iff.mp g.1.2
  have hpolar := polar_apply_of_mem_orthogonalGroup hg.1 (m, 0) (0, 1)
  rw [hfix, QuadraticMap.polar_prod, QuadraticMap.polar_prod] at hpolar
  simp only [map_zero, add_zero, zero_add, QuadraticMap.sq_apply, QuadraticMap.polar,
    mul_one, sub_zero] at hpolar
  ring_nf at hpolar
  have htwo : (2 : R) * (g.1.1 (m, 0)).2 = 0 := by
    linear_combination hpolar
  exact (isRegular_iff_eq_zero_of_mul.mp h2).1 _ htwo

private def specialOrthogonalProdLastRestrictionLinearEquiv
    (Q : QuadraticForm R M) (h2 : IsRegular (2 : R))
    (g : specialOrthogonalGroupProdLastStabilizer Q) : M ≃ₗ[R] M where
  toFun m := (g.1.1 (m, 0)).1
  invFun m := ((g⁻¹).1.1 (m, 0)).1
  map_add' x y := by
    simpa using congrArg Prod.fst (g.1.1.map_add (x, 0) (y, 0))
  map_smul' c x := by
    simpa using congrArg Prod.fst (g.1.1.map_smul c (x, 0))
  left_inv m := by
    have hzero := specialOrthogonalGroupProdLastStabilizer_apply_snd Q h2 g m
    have hpair : g.1.1 (m, 0) = ((g.1.1 (m, 0)).1, 0) := Prod.ext rfl hzero
    -- Unfold the restriction's inverse to expose the ambient inverse action.
    change ((g⁻¹).1.1 ((g.1.1 (m, 0)).1, 0)).1 = m
    rw [← hpair]
    simpa only [Prod.fst, Subgroup.coe_inv, LinearEquiv.coe_inv] using
      congrArg Prod.fst (g.1.1.symm_apply_apply (m, 0))
  right_inv m := by
    have hzero := specialOrthogonalGroupProdLastStabilizer_apply_snd Q h2 g⁻¹ m
    have hpair : (g⁻¹).1.1 (m, 0) = (((g⁻¹).1.1 (m, 0)).1, 0) :=
      Prod.ext rfl hzero
    -- Unfold the restriction to expose the ambient forward action.
    change (g.1.1 (((g⁻¹).1.1 (m, 0)).1, 0)).1 = m
    rw [← hpair]
    simpa only [Prod.fst, Subgroup.coe_inv, LinearEquiv.coe_inv] using
      congrArg Prod.fst (g.1.1.apply_symm_apply (m, 0))

private theorem specialOrthogonalProdLast_eq_prodCongr_restriction
    (Q : QuadraticForm R M) (h2 : IsRegular (2 : R))
    (g : specialOrthogonalGroupProdLastStabilizer Q) :
    g.1.1 = (specialOrthogonalProdLastRestrictionLinearEquiv Q h2 g).prodCongr
      (LinearEquiv.refl R R) := by
  apply LinearEquiv.ext
  intro x
  have hzero := specialOrthogonalGroupProdLastStabilizer_apply_snd Q h2 g x.1
  have hfix : g.1.1 ((0 : M), (1 : R)) = ((0 : M), (1 : R)) :=
    mem_specialOrthogonalGroupProdLastStabilizer_iff Q |>.mp g.2
  have hline : g.1.1 (0, x.2) = (0, x.2) := by
    calc
      g.1.1 (0, x.2) = g.1.1 (x.2 • ((0 : M), (1 : R))) := by simp
      _ = x.2 • g.1.1 ((0 : M), (1 : R)) := g.1.1.map_smul _ _
      _ = (0, x.2) := by rw [hfix]; simp
  have hx : x = (x.1, 0) + (0, x.2) := by ext <;> simp
  rw [hx, map_add, hline]
  apply Prod.ext <;>
    simp [specialOrthogonalProdLastRestrictionLinearEquiv, hzero]

private theorem specialOrthogonalProdLastRestriction_mem
    (Q : QuadraticForm R M) (h2 : IsRegular (2 : R))
    [Module.Free R M] [Module.Finite R M]
    (g : specialOrthogonalGroupProdLastStabilizer Q) :
    specialOrthogonalProdLastRestrictionLinearEquiv Q h2 g ∈ specialOrthogonalGroup Q := by
  have hg := mem_specialOrthogonalGroup_iff.mp g.1.2
  apply mem_specialOrthogonalGroup_iff.mpr
  constructor
  · apply mem_orthogonalGroup_iff.mpr
    intro m
    have hzero := specialOrthogonalGroupProdLastStabilizer_apply_snd Q h2 g m
    have hmap := map_app_of_mem_orthogonalGroup hg.1 (m, 0)
    simpa [specialOrthogonalProdLastRestrictionLinearEquiv, QuadraticMap.prod_apply,
      hzero] using hmap
  · apply Units.ext
    have hdet := congrArg Units.val hg.2
    rw [LinearEquiv.coe_det, specialOrthogonalProdLast_eq_prodCongr_restriction Q h2 g,
      LinearEquiv.coe_prodCongr, LinearMap.det_prodMap] at hdet
    have hrefl :
        LinearMap.det ((LinearEquiv.refl R R : R ≃ₗ[R] R) : R →ₗ[R] R) = 1 := by
      simp
    rw [hrefl, mul_one] at hdet
    simpa only [LinearEquiv.coe_det] using hdet

private theorem specialOrthogonalProdLast_eq_extension_restriction
    (Q : QuadraticForm R M) (h2 : IsRegular (2 : R))
    [Module.Free R M] [Module.Finite R M]
    (g : specialOrthogonalGroupProdLastStabilizer Q) :
    g.1.1 = specialOrthogonalProdLastExtension Q
      ⟨specialOrthogonalProdLastRestrictionLinearEquiv Q h2 g,
        specialOrthogonalProdLastRestriction_mem Q h2 g⟩ := by
  simpa only [specialOrthogonalProdLastExtension] using
    specialOrthogonalProdLast_eq_prodCongr_restriction Q h2 g

/-- Extend a special orthogonal transformation by the identity, as an element of the last-vector
stabilizer. -/
def specialOrthogonalGroupProdLastInclusionToStabilizer
    (Q : QuadraticForm R M) [Module.Free R M] [Module.Finite R M] :
    specialOrthogonalGroup Q →* specialOrthogonalGroupProdLastStabilizer Q :=
  (specialOrthogonalGroupProdLastInclusion Q).codRestrict _
    (specialOrthogonalGroupProdLastInclusion_mem_stabilizer Q)

/-- The stabilizer-valued identity extension acts componentwise. -/
@[simp]
theorem specialOrthogonalGroupProdLastInclusionToStabilizer_apply
    (Q : QuadraticForm R M) [Module.Free R M] [Module.Finite R M]
    (f : specialOrthogonalGroup Q) (x : M × R) :
    (specialOrthogonalGroupProdLastInclusionToStabilizer Q f).1.1 x =
      ((f : M ≃ₗ[R] M) x.1, x.2) := by
  rfl

private def specialOrthogonalProdLastRestriction
    (Q : QuadraticForm R M) (h2 : IsRegular (2 : R))
    [Module.Free R M] [Module.Finite R M] :
    specialOrthogonalGroupProdLastStabilizer Q →* specialOrthogonalGroup Q where
  toFun g :=
    ⟨specialOrthogonalProdLastRestrictionLinearEquiv Q h2 g,
      specialOrthogonalProdLastRestriction_mem Q h2 g⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro m
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro m
    have hzero := specialOrthogonalGroupProdLastStabilizer_apply_snd Q h2 h m
    have hpair : h.1.1 (m, 0) = ((h.1.1 (m, 0)).1, 0) := Prod.ext rfl hzero
    -- Unfold multiplication of the restricted linear equivalences.
    change (g.1.1 (h.1.1 (m, 0))).1 = (g.1.1 ((h.1.1 (m, 0)).1, 0)).1
    rw [hpair]

/-- Extension by the identity identifies `SO(Q)` with the last-vector stabilizer in
`SO(Q.prod QuadraticMap.sq)`.

The inverse sends a stabilizer element `g` to its restriction `m ↦ (g (m, 0)).1`. Regularity of
`2` ensures that fixation of `(0, 1)` forces `g` to preserve the first summand. -/
def specialOrthogonalGroupEquivProdLastStabilizer
    (Q : QuadraticForm R M) (h2 : IsRegular (2 : R))
    [Module.Free R M] [Module.Finite R M] :
    specialOrthogonalGroup Q ≃* specialOrthogonalGroupProdLastStabilizer Q :=
  MonoidHom.toMulEquiv (specialOrthogonalGroupProdLastInclusionToStabilizer Q)
    (specialOrthogonalProdLastRestriction Q h2)
    (MonoidHom.ext fun f => by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro m
      rfl)
    (MonoidHom.ext fun g => by
      apply Subtype.ext
      apply Subtype.ext
      exact (specialOrthogonalProdLast_eq_extension_restriction Q h2 g).symm)

/-- The stabilizer equivalence sends `f` to its extension by the identity. -/
@[simp]
theorem coe_specialOrthogonalGroupEquivProdLastStabilizer_apply
    (Q : QuadraticForm R M) (h2 : IsRegular (2 : R))
    [Module.Free R M] [Module.Finite R M] (f : specialOrthogonalGroup Q) (x : M × R) :
    ((specialOrthogonalGroupEquivProdLastStabilizer Q h2 f).1.1 x) =
      ((f : M ≃ₗ[R] M) x.1, x.2) := by
  rfl

/-- The inverse stabilizer equivalence restricts to the first summand. -/
@[simp]
theorem coe_specialOrthogonalGroupEquivProdLastStabilizer_symm_apply
    (Q : QuadraticForm R M) (h2 : IsRegular (2 : R))
    [Module.Free R M] [Module.Finite R M]
    (g : specialOrthogonalGroupProdLastStabilizer Q) (m : M) :
    ((specialOrthogonalGroupEquivProdLastStabilizer Q h2).symm g : M ≃ₗ[R] M) m =
      (g.1.1 (m, 0)).1 := by
  rfl

end

end QuadraticMap
