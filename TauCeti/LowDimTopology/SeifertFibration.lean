/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Geometry.Manifold.ChartedSpace
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Seifert fibrations

A *Seifert fibration* of a 3-manifold `M` is a decomposition of `M` into disjoint circles, the
fibres, such that every fibre has a neighbourhood which is a union of fibres and is isomorphic,
fibres to fibres, to a model fibred solid torus. Seifert-fibred pieces are, together with the
atoroidal ones, the pieces of the JSJ decomposition of a 3-manifold, and six of Thurston's eight
geometries are the geometries of Seifert-fibred spaces.

The model fibred solid torus `V(p, q)`, for an integer `q > 0` and an integer `p` coprime to `q`,
is the solid torus `D² × S¹` decomposed into the orbits of the circle action
`t • (z, w) = (t ^ p * z, t ^ q * w)`. The core `{0} × S¹` is one fibre; every other fibre winds
`q` times around the core direction. Cutting along a meridian disc presents `V(p, q)` as
`[0, 1] × D²`, decomposed into the segments `[0, 1] × {x}`, with its ends identified by the
rotation through `2πp/q`; this is the description of Hatcher and Scott.

The decomposition is recorded as a `Setoid M` whose classes are the fibres. The local condition is
stated with open partial homeomorphisms onto open subsets of the closed model `V(p, q)`, so that
fibres in the boundary of `M` (modelled on fibres in the boundary torus of `V(p, q)`) are allowed
and no separate model for boundary fibres is needed. Both the chart's source and its target are
required to be unions of fibres; it follows that every fibre is a circle
(`TauCeti.IsSeifertFibration.nonempty_homeomorph_circle`).

Only fibred solid tori occur as local models, as in Seifert's original definition. Scott also
allows fibred solid Klein bottles, which are nonorientable; in an orientable 3-manifold, the case
relevant to the JSJ decomposition and geometrization, the two definitions agree.

The predicate is a property of the decomposition alone. It forces `M` to be locally homeomorphic to
open subsets of `D² × S¹`, but separation and countability hypotheses are kept separate, as in
`TauCeti.IsCompactConnectedThreeManifold`.

## Main definitions

* `TauCeti.SolidTorus`: the closed solid torus `D² × S¹`.
* `TauCeti.SolidTorus.fiberSetoid p q`: the fibres of the model fibred solid torus `V(p, q)`.
* `TauCeti.IsSeifertChart r p q e`: the chart `e` carries the classes of `r` in its source onto the
  fibres of `V(p, q)` in its target.
* `TauCeti.IsSeifertFibration r`: the classes of `r` form a Seifert fibration.
* `TauCeti.IsSeifertFibered M`: `M` admits a Seifert fibration.

## Main results

* `TauCeti.IsSeifertFibration.nonempty_homeomorph_circle`: every fibre of a Seifert fibration is
  homeomorphic to a circle.
* `TauCeti.SolidTorus.isSeifertFibration_fiberSetoid`: the model `V(p, q)` is Seifert fibred.
* `TauCeti.isSeifertFibration_ker_fst`: for a boundaryless surface `F`, the circles `{x} × S¹`
  form a Seifert fibration of `F × S¹`.
* `Homeomorph.isSeifertFibered_iff`: being Seifert fibred is invariant under homeomorphism.

## References

* H. Seifert, *Topologie dreidimensionaler gefaserter Räume*, Acta Math. 60 (1933), 147–238.
* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983), 401–487,
  Section 3.
* A. Hatcher, *Notes on Basic 3-Manifold Topology*, Section 2.1.
-/

public section

open Set Metric Topology

namespace TauCeti

/-- The closed solid torus `D² × S¹`, where `D²` is the closed unit disc of `ℂ`. -/
abbrev SolidTorus : Type := closedBall (0 : ℂ) 1 × Circle

namespace SolidTorus

/-- The fibres of the model fibred solid torus `V(p, q)`: two points of `D² × S¹` lie in the same
fibre when they lie in the same orbit of the circle action `t • (z, w) = (t ^ p * z, t ^ q * w)`.
For `q ≠ 0` the core `{0} × S¹` is a single fibre. When moreover `p` is coprime to `q`, every
other fibre winds `q` times around the core direction and `p` times around the meridian of the
torus `{|z| = r} × S¹` containing it.
-/
def fiberSetoid (p q : ℤ) : Setoid SolidTorus where
  r a b := ∃ t : Circle, ((t ^ p : Circle) : ℂ) * a.1 = b.1 ∧ t ^ q * a.2 = b.2
  iseqv :=
    { refl _ := ⟨1, by simp⟩
      symm := by
        rintro a b ⟨t, h₁, h₂⟩
        refine ⟨t⁻¹, ?_, ?_⟩
        · rw [← h₁, ← mul_assoc, ← Circle.coe_mul, inv_zpow, inv_mul_cancel, Circle.coe_one,
            one_mul]
        · rw [← h₂, ← mul_assoc, inv_zpow, inv_mul_cancel, one_mul]
      trans := by
        rintro a b c ⟨t, h₁, h₂⟩ ⟨s, h₁', h₂'⟩
        refine ⟨s * t, ?_, ?_⟩
        · rw [← h₁', ← h₁, mul_zpow, Circle.coe_mul, mul_assoc]
        · rw [← h₂', ← h₂, mul_zpow, mul_assoc] }

/-- The defining orbit condition of the fibres of `V(p, q)`. -/
theorem fiberSetoid_iff {p q : ℤ} {a b : SolidTorus} :
    fiberSetoid p q a b ↔ ∃ t : Circle, ((t ^ p : Circle) : ℂ) * a.1 = b.1 ∧ t ^ q * a.2 = b.2 :=
  Iff.rfl

/-- The fibres of `V(0, 1)` are the circles `{z} × S¹` of the product fibration. -/
@[simp]
theorem fiberSetoid_zero_one {a b : SolidTorus} : fiberSetoid 0 1 a b ↔ a.1 = b.1 := by
  refine ⟨fun ⟨t, h, _⟩ ↦ Subtype.ext (by simpa using h), fun h ↦ ⟨b.2 * a.2⁻¹, ?_, ?_⟩⟩
  · simp [h]
  · rw [zpow_one, inv_mul_cancel_right]

/-- Every fibre of the model fibred solid torus `V(p, q)`, for `q ≠ 0` and `p` coprime to `q`, is
homeomorphic to a circle. -/
theorem nonempty_homeomorph_circle {p q : ℤ} (hq : q ≠ 0) (hpq : IsCoprime p q)
    (a : SolidTorus) : Nonempty ({b | fiberSetoid p q a b} ≃ₜ Circle) := by
  -- The core is the circle `{0} × S¹`; off the core the orbit map of the circle action is
  -- injective by coprimality.
  suffices ∃ f : Circle → SolidTorus, Continuous f ∧ Function.Injective f ∧
      range f = {b | fiberSetoid p q a b} by
    obtain ⟨f, hf, hinj, hrange⟩ := this
    exact ⟨(Homeomorph.setCongr hrange).symm.trans
      (hf.isClosedEmbedding hinj).isEmbedding.toHomeomorph.symm⟩
  by_cases ha : (a.1 : ℂ) = 0
  · refine ⟨fun w ↦ (⟨0, mem_closedBall_self zero_le_one⟩, w),
      continuous_const.prodMk continuous_id, fun w w' h ↦ (Prod.ext_iff.1 h).2, ?_⟩
    ext b
    simp only [mem_range, mem_ofPred_eq, fiberSetoid_iff, ha, mul_zero]
    constructor
    · rintro ⟨w, rfl⟩
      -- The core is a single fibre: `t ↦ t ^ q` is onto, as `q ≠ 0`.
      obtain ⟨θ, hθ⟩ := Circle.exp_surjective (w * a.2⁻¹)
      refine ⟨Circle.exp (θ / q), rfl, ?_⟩
      rw [← Circle.exp_intCast_mul, mul_div_cancel₀ _ (Int.cast_ne_zero.2 hq), hθ,
        inv_mul_cancel_right]
    · rintro ⟨-, h₁, -⟩
      exact ⟨b.2, Prod.ext (Subtype.ext h₁) rfl⟩
  · obtain ⟨u, v, huv⟩ := hpq
    have hmem (t : Circle) : ((t ^ p : Circle) : ℂ) * a.1 ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall_zero_iff, norm_mul, Circle.norm_coe, one_mul]
      exact mem_closedBall_zero_iff.1 a.1.2
    refine ⟨fun t ↦ (⟨_, hmem t⟩, t ^ q * a.2), ?_, fun t s h ↦ ?_, ?_⟩
    · have hcoe : Continuous fun t : Circle ↦ (t : ℂ) := continuous_subtype_val
      exact (((hcoe.comp (continuous_zpow p)).mul continuous_const).subtype_mk hmem).prodMk
        ((continuous_zpow q).mul continuous_const)
    · obtain ⟨h₁, h₂⟩ := Prod.ext_iff.1 h
      have hp : t ^ p = s ^ p :=
        Circle.coe_injective (mul_right_cancel₀ ha (congrArg Subtype.val h₁))
      have hq' : t ^ q = s ^ q := mul_right_cancel h₂
      have key (x : Circle) : x = (x ^ p) ^ u * (x ^ q) ^ v := by
        rw [← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm p u, mul_comm q v, huv, zpow_one]
      rw [key t, key s, hp, hq']
    · ext b
      exact ⟨fun ⟨t, ht⟩ ↦ ⟨t, by rw [← ht], by rw [← ht]⟩,
        fun ⟨t, h₁, h₂⟩ ↦ ⟨t, Prod.ext (Subtype.ext h₁) h₂⟩⟩

end SolidTorus

open SolidTorus

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]

/-- An open partial homeomorphism `e` from `M` to the solid torus is a **Seifert chart** of `r`
onto the model `V(p, q)` when its source is a union of classes of `r`, its target is a union of
fibres of `V(p, q)`, and on its source `e` carries the classes of `r` onto fibres of `V(p, q)`. -/
structure IsSeifertChart (r : Setoid M) (p q : ℤ) (e : OpenPartialHomeomorph M SolidTorus) :
    Prop where
  /-- The source of the chart is a union of classes of `r`. -/
  source_saturated : ∀ x ∈ e.source, ∀ y, r x y → y ∈ e.source
  /-- The target of the chart is a union of fibres of `V(p, q)`. -/
  target_saturated : ∀ a ∈ e.target, ∀ b, fiberSetoid p q a b → b ∈ e.target
  /-- On its source the chart carries the classes of `r` onto the fibres of `V(p, q)`. -/
  rel_iff : ∀ x ∈ e.source, ∀ y ∈ e.source, r x y ↔ fiberSetoid p q (e x) (e y)

/-- A Seifert chart maps the class of a point of its source onto the fibre of `V(p, q)` through its
image. -/
theorem IsSeifertChart.image_setOf_rel {r : Setoid M} {p q : ℤ}
    {e : OpenPartialHomeomorph M SolidTorus} (he : IsSeifertChart r p q e) {x : M}
    (hx : x ∈ e.source) : e '' {y | r x y} = {b | fiberSetoid p q (e x) b} := by
  ext b
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (he.rel_iff x hx y (he.source_saturated x hx y hy)).1 hy
  · intro hb
    have hbt : b ∈ e.target := he.target_saturated (e x) (e.map_source hx) b hb
    refine ⟨e.symm b, (he.rel_iff x hx _ (e.map_target hbt)).2 ?_, e.right_inv hbt⟩
    rwa [e.right_inv hbt]

/-- An equivalence relation on `M` is a **Seifert fibration** when every point of `M` lies in the
source of a Seifert chart of `r` onto a model fibred solid torus `V(p, q)`, with `q > 0` and `p`
coprime to `q`. Its classes, the fibres, are then circles. -/
def IsSeifertFibration (r : Setoid M) : Prop :=
  ∀ x : M, ∃ p q : ℤ, 0 < q ∧ IsCoprime p q ∧
    ∃ e : OpenPartialHomeomorph M SolidTorus, x ∈ e.source ∧ IsSeifertChart r p q e

/-- The defining local condition of a Seifert fibration. -/
theorem isSeifertFibration_iff {r : Setoid M} :
    IsSeifertFibration r ↔ ∀ x : M, ∃ p q : ℤ, 0 < q ∧ IsCoprime p q ∧
      ∃ e : OpenPartialHomeomorph M SolidTorus, x ∈ e.source ∧ IsSeifertChart r p q e :=
  Iff.rfl

variable (M) in
/-- A space is **Seifert fibred** when it admits a Seifert fibration. -/
def IsSeifertFibered : Prop :=
  ∃ r : Setoid M, IsSeifertFibration r

/-- The defining condition of a Seifert-fibred space. -/
theorem isSeifertFibered_iff : IsSeifertFibered M ↔ ∃ r : Setoid M, IsSeifertFibration r :=
  Iff.rfl

namespace IsSeifertFibration

variable {r : Setoid M}

/-- Every fibre of a Seifert fibration is homeomorphic to a circle. -/
theorem nonempty_homeomorph_circle (h : IsSeifertFibration r) (x : M) :
    Nonempty ({y | r x y} ≃ₜ Circle) := by
  obtain ⟨p, q, hq, hpq, e, hx, he⟩ := h x
  obtain ⟨φ⟩ := SolidTorus.nonempty_homeomorph_circle hq.ne' hpq (e x)
  exact ⟨(e.homeomorphOfImageSubsetSource (fun y hy ↦ he.source_saturated x hx y hy)
    (he.image_setOf_rel hx)).trans φ⟩

/-- A Seifert fibration pulls back along a homeomorphism. -/
theorem comap_homeomorph (h : IsSeifertFibration r) (φ : N ≃ₜ M) :
    IsSeifertFibration (r.comap φ) := by
  intro x
  obtain ⟨p, q, hq, hpq, e, hx, he⟩ := h (φ x)
  refine ⟨p, q, hq, hpq, φ.transOpenPartialHomeomorph e, hx, fun y hy z hyz ↦ ?_,
    he.target_saturated, fun y hy z hz ↦ he.rel_iff (φ y) hy (φ z) hz⟩
  exact he.source_saturated (φ y) hy (φ z) hyz

end IsSeifertFibration

/-- Being Seifert fibred is invariant under homeomorphism. -/
theorem _root_.Homeomorph.isSeifertFibered_iff (φ : N ≃ₜ M) :
    IsSeifertFibered N ↔ IsSeifertFibered M :=
  ⟨fun ⟨r, hr⟩ ↦ ⟨r.comap φ.symm, hr.comap_homeomorph φ.symm⟩,
    fun ⟨r, hr⟩ ↦ ⟨r.comap φ, hr.comap_homeomorph φ⟩⟩

namespace SolidTorus

/-- The model fibred solid torus `V(p, q)`, for `q > 0` and `p` coprime to `q`, is Seifert fibred.
-/
theorem isSeifertFibration_fiberSetoid {p q : ℤ} (hq : 0 < q) (hpq : IsCoprime p q) :
    IsSeifertFibration (fiberSetoid p q) := fun _ ↦
  ⟨p, q, hq, hpq, OpenPartialHomeomorph.refl _, mem_univ _,
    ⟨fun _ _ _ _ ↦ mem_univ _, fun _ _ _ _ ↦ mem_univ _, fun _ _ _ _ ↦ Iff.rfl⟩⟩

/-- The solid torus is Seifert fibred. -/
theorem isSeifertFibered : IsSeifertFibered SolidTorus :=
  ⟨_, isSeifertFibration_fiberSetoid (p := 0) one_pos isCoprime_one_right⟩

end SolidTorus

/-- For a boundaryless surface `F`, the circles `{x} × S¹` form a Seifert fibration of `F × S¹`:
near each fibre, a chart of `F` identifies it with the product fibration `V(0, 1)`. -/
theorem isSeifertFibration_ker_fst {F : Type*} [TopologicalSpace F]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F] :
    IsSeifertFibration (Setoid.ker (Prod.fst : F × Circle → F)) := by
  intro x
  -- Identify the plane with `ℂ`, then embed `ℂ` openly in the closed unit disc.
  have hd := isOpenEmbedding_inclusion_comp_unitBall.comp
    Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.isOpenEmbedding
  let c := (chartAt (EuclideanSpace ℝ (Fin 2)) x.1).trans (hd.toOpenPartialHomeomorph _)
  have hc : c.source = (chartAt (EuclideanSpace ℝ (Fin 2)) x.1).source := by simp [c]
  refine ⟨0, 1, one_pos, isCoprime_one_right, c.prod (OpenPartialHomeomorph.refl Circle), ?_,
    ⟨fun y hy z hyz ↦ ?_, fun a ha b hab ↦ ?_, fun y hy z hz ↦ ?_⟩⟩
  · simp [hc]
  · simp only [OpenPartialHomeomorph.prod_source, OpenPartialHomeomorph.refl_source,
      mem_prod, mem_univ, and_true, Setoid.ker_def] at hy hyz ⊢
    exact hyz ▸ hy
  · simp only [OpenPartialHomeomorph.prod_target, OpenPartialHomeomorph.refl_target, mem_prod,
      mem_univ, and_true, fiberSetoid_zero_one] at ha hab ⊢
    exact hab ▸ ha
  · simp only [OpenPartialHomeomorph.prod_source, OpenPartialHomeomorph.refl_source, mem_prod,
      mem_univ, and_true] at hy hz
    rw [Setoid.ker_def, fiberSetoid_zero_one, OpenPartialHomeomorph.prod_apply]
    exact (c.injOn.eq_iff hy hz).symm

/-- The product of a boundaryless surface with a circle is Seifert fibred. -/
theorem isSeifertFibered_prod_circle (F : Type*) [TopologicalSpace F]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F] : IsSeifertFibered (F × Circle) :=
  ⟨_, isSeifertFibration_ker_fst⟩

end TauCeti
