/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MappingTorus.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The mapping torus of the identity

The mapping torus of the identity of a space `F` is the product `F × S¹`: the cylinder `F × ℝ`
modulo the translations `(x, t) ↦ (x, t + n)` is `F × (ℝ / ℤ)`. The homeomorphism
`TauCeti.MappingTorus.reflHomeomorph` sends the class of `(x, t)` to `(x, t mod 1)`. Its second
coordinate is the projection `TauCeti.MappingTorus.proj` to the circle, and it sends the fibre
inclusion `TauCeti.MappingTorus.incl` to the inclusion `x ↦ (x, 0)` of `F` at `0`. Reading the
circle as the unit circle `Circle` of `ℂ`, `TauCeti.MappingTorus.reflCircleHomeomorph` identifies
the mapping torus with `S¹ × F`, and the fibre inclusion with the inclusion `y ↦ (1, y)`.

Through it, the theory of mapping tori, in particular the Wang sequence, applies to products with
a circle.

## Main definitions

* `TauCeti.MappingTorus.reflHomeomorph`: the homeomorphism
  `MappingTorus (Homeomorph.refl F) ≃ₜ F × UnitAddCircle`.
* `TauCeti.MappingTorus.reflCircleHomeomorph`: the homeomorphism
  `MappingTorus (Homeomorph.refl F) ≃ₜ Circle × F`.
-/

public section

noncomputable section

namespace TauCeti.MappingTorus

variable {F : Type*} [TopologicalSpace F]

/-- The monodromy of the mapping torus of the identity has trivial powers. -/
private theorem refl_zpow_apply (n : ℤ) (x : F) : (Homeomorph.refl F ^ n) x = x := by
  -- The identity homeomorphism is the unit of the group `F ≃ₜ F`.
  rw [show Homeomorph.refl F = 1 from rfl, one_zpow, Homeomorph.one_apply]

/-- The fibre coordinate of the mapping torus of the identity. -/
private def reflFst : MappingTorus (Homeomorph.refl F) → F :=
  lift (Homeomorph.refl F) Prod.fst fun n x _ ↦ refl_zpow_apply n x

private theorem reflFst_mk (x : F) (t : ℝ) : reflFst (mk (Homeomorph.refl F) x t) = x :=
  lift_mk _ _ _ x t

private theorem continuous_reflFst : Continuous (reflFst (F := F)) :=
  continuous_lift _ _ continuous_fst

/-- The map `MappingTorus (Homeomorph.refl F) → F × UnitAddCircle`, `[x, t] ↦ (x, t mod 1)`. -/
private def reflToProd (z : MappingTorus (Homeomorph.refl F)) : F × UnitAddCircle :=
  (reflFst z, proj _ z)

private theorem reflToProd_mk (x : F) (t : ℝ) :
    reflToProd (mk (Homeomorph.refl F) x t) = (x, (t : UnitAddCircle)) := by
  simp [reflToProd, reflFst_mk]

private theorem bijective_reflToProd : Function.Bijective (reflToProd (F := F)) := by
  refine ⟨fun z w h ↦ ?_, fun p ↦ ?_⟩
  · obtain ⟨⟨x, t⟩, rfl⟩ := mk_surjective _ z
    obtain ⟨⟨y, s⟩, rfl⟩ := mk_surjective _ w
    simp only [reflToProd_mk, Prod.mk.injEq] at h
    obtain ⟨rfl, hts⟩ := h
    -- Two heights with the same class in `ℝ / ℤ` differ by an integer.
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 hts.symm)
    refine (mk_eq_iff _).2 ⟨n, refl_zpow_apply n x, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hn
    linarith
  · obtain ⟨x, θ⟩ := p
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    exact ⟨mk _ x t, reflToProd_mk x t⟩

private theorem isOpenMap_reflToProd : IsOpenMap (reflToProd (F := F)) := by
  intro U hU
  -- Through the quotient map from the cylinder, `reflToProd` is `id × (t ↦ t mod 1)`, an open
  -- map.
  have hcomp : (reflToProd ∘ fun p : F × ℝ ↦ mk (Homeomorph.refl F) p.1 p.2) =
      Prod.map id ((↑) : ℝ → UnitAddCircle) := by
    funext p
    exact reflToProd_mk p.1 p.2
  rw [← Set.image_preimage_eq U (mk_surjective (Homeomorph.refl F)), ← Set.image_comp, hcomp]
  exact (IsOpenMap.id.prodMap QuotientAddGroup.isOpenMap_coe) _
    (hU.preimage (continuous_mk (Homeomorph.refl F)))

/-- **The mapping torus of the identity is the product with the circle**: the homeomorphism
`MappingTorus (Homeomorph.refl F) ≃ₜ F × UnitAddCircle` sending the class of `(x, t)` to
`(x, t mod 1)`. -/
def reflHomeomorph : MappingTorus (Homeomorph.refl F) ≃ₜ F × UnitAddCircle :=
  (Equiv.ofBijective reflToProd bijective_reflToProd).toHomeomorphOfContinuousOpen
    (continuous_reflFst.prodMk (continuous_proj _)) isOpenMap_reflToProd

@[simp]
theorem reflHomeomorph_mk (x : F) (t : ℝ) :
    reflHomeomorph (mk (Homeomorph.refl F) x t) = (x, (t : UnitAddCircle)) :=
  reflToProd_mk x t

@[simp]
theorem reflHomeomorph_symm_apply (x : F) (t : ℝ) :
    reflHomeomorph.symm (x, (t : UnitAddCircle)) = mk (Homeomorph.refl F) x t := by
  rw [Homeomorph.symm_apply_eq, reflHomeomorph_mk]

/-- The second coordinate of `reflHomeomorph` is the projection of the mapping torus to the
circle. -/
@[simp]
theorem snd_reflHomeomorph (z : MappingTorus (Homeomorph.refl F)) :
    (reflHomeomorph z).2 = proj _ z := by
  obtain ⟨⟨x, t⟩, rfl⟩ := mk_surjective _ z
  simp

/-- `reflHomeomorph` sends the fibre inclusion to the inclusion of `F` at `0`. -/
theorem reflHomeomorph_incl (x : F) : reflHomeomorph (incl (Homeomorph.refl F) x) = (x, 0) := by
  simp

/-- The mapping torus of the identity of `F` is `S¹ × F`, with the circle the unit circle `Circle`
of `ℂ` and the fibre at `1`. -/
def reflCircleHomeomorph : MappingTorus (Homeomorph.refl F) ≃ₜ Circle × F :=
  reflHomeomorph.trans ((Homeomorph.prodComm F UnitAddCircle).trans
    ((AddCircle.homeomorphCircle one_ne_zero).prodCongr (Homeomorph.refl F)))

/-- `reflCircleHomeomorph` sends the fibre inclusion to the inclusion of `F` at `1`. -/
theorem reflCircleHomeomorph_incl (x : F) :
    reflCircleHomeomorph (incl (Homeomorph.refl F) x) = (1, x) := by
  rw [reflCircleHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply, reflHomeomorph_incl]
  simp [AddCircle.homeomorphCircle_apply]

/-- The fibre inclusion of the mapping torus of the identity is, through `reflCircleHomeomorph`,
the inclusion `y ↦ (1, y)` of `F` in `S¹ × F`. -/
theorem reflCircleHomeomorph_comp_incl :
    (reflCircleHomeomorph (F := F) : C(MappingTorus (Homeomorph.refl F), Circle × F)).comp
        (incl (Homeomorph.refl F)) =
      (ContinuousMap.const F (1 : Circle)).prodMk (ContinuousMap.id F) :=
  ContinuousMap.ext reflCircleHomeomorph_incl

end TauCeti.MappingTorus
