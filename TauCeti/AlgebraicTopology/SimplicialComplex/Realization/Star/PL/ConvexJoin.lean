/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Join
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Cone
public import TauCeti.Topology.PL.Cone
public import TauCeti.Topology.PL.Product

/-!
# Piecewise-linear joins of vertex stars with a centre

Let `F` be an ambient coordinate formula embedding the geometric link of a vertex `v` onto a
set `T` of a coordinate space `κ → ℝ`, and let `b` be a point there. Sending each point
`(1 - t) • y + t • v` of the closed star of `v`, with `y` in the link, to
`(1 - t) • F y + t • b` identifies the closed star with the convex join of `T` and `b`, provided
these segments do not meet away from `b`. That proviso is recorded by a height function `h`
recovering the parameter `t` along each segment.

When `F`, its inverse on `T`, and `h` are piecewise linear, the resulting homeomorphism and its
inverse have piecewise-linear ambient coordinate formulas. This is pseudo-radial projection: for a
link identified with the boundary of a simplex and `b` the barycentre, it identifies the closed
star of a vertex with the whole simplex, and for a link identified with a facet of a simplex and
`b` the opposite vertex, it identifies the closed star with that simplex. Such simplex models are
the local models for piecewise-linear charts on the open vertex stars of a combinatorial
manifold.

Only the closed star needs to be compact; the ambient complex and both vertex types may be
infinite.

## Main results

* `AbstractSimplicialComplex.exists_homeomorph_closedStarRealization_convexJoin`: the
  identification of a closed vertex star with the convex join of a link model and a centre, with
  piecewise-linear coordinate formulas in both directions.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 1, “Joins and Cones”, and Chapter 2, “Pseudo-Radial Projection”, pp. 20–21.
-/

public section

noncomputable section

open Set TauCeti

namespace AbstractSimplicialComplex

variable {ι κ : Type*} [DecidableEq ι] {K : AbstractSimplicialComplex ι} {v : ι}

/-- The ambient formula of the join map: cone the link formula, then put the centre at the
apex. -/
private def joinFormula (F : (ι → ℝ) → (κ → ℝ)) (b : κ → ℝ) (v : ι) :
    (ι → ℝ) → (κ → ℝ) :=
  coneToJoin b ∘ coneMap F ∘ starToCone v

/-- The ambient formula of the inverse join map: read off the height, cone the inverse link
formula, then put the vertex `v` at the apex. -/
private def joinInverseFormula (G : (κ → ℝ) → (ι → ℝ)) (h : (κ → ℝ) → ℝ) (b : κ → ℝ)
    (v : ι) : (κ → ℝ) → (ι → ℝ) :=
  coneToJoin (Pi.single v 1) ∘ coneMap G ∘ fun z => (z - h z • b, 1 - h z)

/-- Away from the apex, the join formula is the point at parameter `x v` on the segment from the
image of the radial projection to the centre. -/
private theorem joinFormula_of_lt (F : (ι → ℝ) → (κ → ℝ)) (b : κ → ℝ)
    (x : closedStarRealization K {v}) (hx : x.1.1 v < 1) :
    joinFormula F b v (x.1.1 : ι → ℝ) = (1 - x.1.1 v) • F ((starLinkProjection K v
      ⟨x.1, (mem_puncturedClosedStar K v _).mpr ⟨x.2, hx⟩⟩).1.1 : ι → ℝ) + x.1.1 v • b := by
  rw [joinFormula, Function.comp_apply, Function.comp_apply, starToCone_of_lt x hx,
    coneMap_smul F _ (sub_pos.mpr hx).ne', coneToJoin_apply]
  module

/-- The join formula sends the apex to the centre. -/
private theorem joinFormula_starApex (F : (ι → ℝ) → (κ → ℝ)) (b : κ → ℝ) :
    joinFormula F b v ((starApex K v).1.1 : ι → ℝ) = b := by
  rw [joinFormula, Function.comp_apply, Function.comp_apply,
    starToCone_of_not_lt (starApex K v) (by simp [vertex_val]), coneMap_zero, coneToJoin_apply]
  simp

variable {F : (ι → ℝ) → (κ → ℝ)} {G : (κ → ℝ) → (ι → ℝ)} {b : κ → ℝ} {h : (κ → ℝ) → ℝ}

/-- Every point of the closed star is sent into the join of the link model with the centre. -/
private theorem joinFormula_mem (hne : (geometricLink K v).Nonempty)
    (x : closedStarRealization K {v}) :
    joinFormula F b v (x.1.1 : ι → ℝ) ∈
      convexJoin ℝ (range fun y : geometricLink K v => F (y.1.1 : ι → ℝ)) {b} := by
  by_cases hx : x.1.1 v < 1
  · refine mem_convexJoin.mpr ⟨_, mem_range_self (starLinkProjection K v
      ⟨x.1, (mem_puncturedClosedStar K v _).mpr ⟨x.2, hx⟩⟩), b, rfl, ?_⟩
    rw [joinFormula_of_lt F b x hx]
    exact ⟨1 - x.1.1 v, x.1.1 v, sub_nonneg.mpr (Realization.le_one K x.1 v),
      Realization.nonneg K x.1 v, by ring, rfl⟩
  · obtain ⟨y, hy⟩ := hne
    rw [eq_starApex_of_not_lt K v hx, joinFormula_starApex]
    exact mem_convexJoin.mpr ⟨_, mem_range_self ⟨y, hy⟩, b, rfl, right_mem_segment ℝ _ _⟩

/-- Every point of the join of the link model with the centre is hit by the join formula. -/
private theorem exists_joinFormula_eq {z : κ → ℝ}
    (hz : z ∈ convexJoin ℝ (range fun y : geometricLink K v => F (y.1.1 : ι → ℝ)) {b}) :
    ∃ x : closedStarRealization K {v}, joinFormula F b v (x.1.1 : ι → ℝ) = z := by
  obtain ⟨_, ⟨y, rfl⟩, b', hb', α, β, hα, hβ, hαβ, rfl⟩ := mem_convexJoin.mp hz
  rw [mem_singleton_iff] at hb'
  subst b'
  have hβle : β ≤ 1 := by linarith
  rcases hβle.lt_or_eq with hβ1 | rfl
  · let r := starRay K v y ⟨β, hβ, hβ1⟩
    have hrv : r.1.1 v = β := by simp [r]
    have hr := ((mem_puncturedClosedStar K v _).mp r.2).1
    refine ⟨⟨r.1, hr⟩, ?_⟩
    -- The punctured-star point rebuilt from `r` is `r` itself, whose projection is `y`.
    rw [joinFormula_of_lt F b ⟨r.1, hr⟩ (hrv ▸ hβ1), Subtype.coe_eta,
      starLinkProjection_starRay]
    simp only [hrv]
    congr 2
    linarith
  · obtain rfl : α = 0 := by linarith
    refine ⟨starApex K v, ?_⟩
    rw [joinFormula_starApex]
    simp

/-- The height function reads off the apex coordinate along the join formula. -/
private theorem h_joinFormula (hne : (geometricLink K v).Nonempty)
    (hhF : ∀ y : geometricLink K v, ∀ t ∈ Icc (0 : ℝ) 1,
      h ((1 - t) • F (y.1.1 : ι → ℝ) + t • b) = t)
    (x : closedStarRealization K {v}) : h (joinFormula F b v (x.1.1 : ι → ℝ)) = x.1.1 v := by
  by_cases hx : x.1.1 v < 1
  · rw [joinFormula_of_lt F b x hx]
    exact hhF _ _ ⟨Realization.nonneg K x.1 v, Realization.le_one K x.1 v⟩
  · obtain ⟨y, hy⟩ := hne
    have hb := hhF ⟨y, hy⟩ 1 ⟨zero_le_one, le_rfl⟩
    rw [sub_self, zero_smul, one_smul, zero_add] at hb
    rw [eq_starApex_of_not_lt K v hx, joinFormula_starApex, hb, starApex_val, vertex_val]
    simp

/-- The inverse formula undoes the join formula on the closed star. -/
private theorem joinInverseFormula_joinFormula (hne : (geometricLink K v).Nonempty)
    (hGF : ∀ y : geometricLink K v, G (F (y.1.1 : ι → ℝ)) = y.1.1)
    (hhF : ∀ y : geometricLink K v, ∀ t ∈ Icc (0 : ℝ) 1,
      h ((1 - t) • F (y.1.1 : ι → ℝ) + t • b) = t)
    (x : closedStarRealization K {v}) :
    joinInverseFormula G h b v (joinFormula F b v (x.1.1 : ι → ℝ)) = x.1.1 := by
  have hx' := h_joinFormula hne hhF x
  by_cases hx : x.1.1 v < 1
  · set p := starLinkProjection K v ⟨x.1, (mem_puncturedClosedStar K v _).mpr ⟨x.2, hx⟩⟩
    have hray := starRay_starLinkProjection K v ⟨x.1, (mem_puncturedClosedStar K v _).mpr ⟨x.2, hx⟩⟩
    simp only [joinInverseFormula, Function.comp_apply]
    rw [hx', joinFormula_of_lt F b x hx, add_sub_cancel_right,
      coneMap_smul G _ (sub_pos.mpr hx).ne', hGF, coneToJoin_apply]
    funext w
    have hw := congrArg (fun z : puncturedClosedStar K v => z.1.1 w) hray
    simp only [starRay_apply] at hw
    rw [← hw]
    by_cases hvw : v = w
    · subst hvw
      simp
    · simp [Ne.symm hvw, hvw]
  · rw [eq_starApex_of_not_lt K v hx] at hx' ⊢
    simp only [joinInverseFormula, Function.comp_apply]
    rw [hx', joinFormula_starApex, starApex_val, vertex_val]
    simp [coneToJoin_apply, Finsupp.single_eq_pi_single]

/-- The join formula is piecewise linear on the closed-star coordinates. -/
private theorem isPLOn_joinFormula (hK : IsCompact (closedStarRealization K {v}))
    (hF : IsPLOn F (range fun y : geometricLink K v => (y.1.1 : ι → ℝ))) :
    IsPLOn (joinFormula F b v) (range fun x : closedStarRealization K {v} => (x.1.1 : ι → ℝ)) :=
  (isPLOn_continuousAffineMap (coneToJoin b) univ).comp
    ((hF.coneMap (K.isCompact_range_geometricLink v hK)).comp
      (isPLOn_continuousAffineMap (starToCone v) _) (by rintro _ ⟨x, rfl⟩; exact starToCone_mem x))
    (fun _ _ => mem_univ _)

/-- Removing the centre's share of a join point lands in the cone over the link model. -/
private theorem mem_cone_of_mem_convexJoin
    (hhF : ∀ y : geometricLink K v, ∀ t ∈ Icc (0 : ℝ) 1,
      h ((1 - t) • F (y.1.1 : ι → ℝ) + t • b) = t)
    {z : κ → ℝ} (hz : z ∈ convexJoin ℝ (range fun y : geometricLink K v => F (y.1.1 : ι → ℝ)) {b}) :
    (z - h z • b, 1 - h z) ∈ (range fun y : geometricLink K v => F (y.1.1 : ι → ℝ)).cone := by
  obtain ⟨_, ⟨y, rfl⟩, _, rfl, α, β, hα, hβ, hαβ, rfl⟩ := mem_convexJoin.mp hz
  obtain rfl : α = 1 - β := by linarith
  rw [hhF y β ⟨hβ, by linarith⟩, add_sub_cancel_right]
  rcases hα.lt_or_eq with hα | hα
  · exact (smul_mem_cone_iff _ hα).mpr (mem_range_self y)
  · rw [← hα, zero_smul]
    exact zero_mem_cone _

/-- The inverse join formula is piecewise linear on the join. -/
private theorem isPLOn_joinInverseFormula (hK : IsCompact (closedStarRealization K {v}))
    (hF : IsPLOn F (range fun y : geometricLink K v => (y.1.1 : ι → ℝ)))
    (hG : IsPLOn G (range fun y : geometricLink K v => F (y.1.1 : ι → ℝ)))
    (hh : IsPLOn h (convexJoin ℝ (range fun y : geometricLink K v => F (y.1.1 : ι → ℝ)) {b}))
    (hhF : ∀ y : geometricLink K v, ∀ t ∈ Icc (0 : ℝ) 1,
      h ((1 - t) • F (y.1.1 : ι → ℝ) + t • b) = t) :
    IsPLOn (joinInverseFormula G h b v)
      (convexJoin ℝ (range fun y : geometricLink K v => F (y.1.1 : ι → ℝ)) {b}) := by
  have hT : IsCompact (range fun y : geometricLink K v => F (y.1.1 : ι → ℝ)) := by
    rw [range_comp' F]
    exact (K.isCompact_range_geometricLink v hK).image_of_continuousOn hF.continuousOn
  -- The pair `(z - h z • b, 1 - h z)` is an affine image of `(z, h z)`.
  let A : ((κ → ℝ) × ℝ) →ᴬ[ℝ] ((κ → ℝ) × ℝ) :=
    ((ContinuousLinearMap.fst ℝ (κ → ℝ) ℝ - (ContinuousLinearMap.snd ℝ (κ → ℝ) ℝ).smulRight b).prod
      (-ContinuousLinearMap.snd ℝ (κ → ℝ) ℝ)).toContinuousAffineMap +
      ContinuousAffineMap.const ℝ _ (0, 1)
  have hpair : IsPLOn (fun z => (z - h z • b, 1 - h z))
      (convexJoin ℝ (range fun y : geometricLink K v => F (y.1.1 : ι → ℝ)) {b}) :=
    ((isPLOn_continuousAffineMap A univ).comp ((isPLOn_id _).prodMk hh)
      (fun _ _ => mem_univ _)).congr fun z _ => by
        ext <;> simp [A, sub_eq_neg_add]
  exact (isPLOn_continuousAffineMap (coneToJoin (Pi.single v 1)) univ).comp
    ((hG.coneMap hT).comp hpair fun _ hz => mem_cone_of_mem_convexJoin hhF hz)
    (fun _ _ => mem_univ _)

/-- **Pseudo-radial projection of a closed vertex star.** Let `F` be a piecewise-linear
coordinate formula for the geometric link of `v`, with a piecewise-linear inverse `G` on its
image `T`, and let `b` be a centre with a piecewise-linear height function `h` that reads off
`t` along every segment from `T` to `b`. Then the closed star of `v` is homeomorphic to the
convex join of `T` and `b`: the apex goes to `b`, the apex coordinate is the height, every other
point `x` goes to `(1 - t) • F y + t • b`, where `t` is its apex coordinate and `y` its radial
projection to the link, and the homeomorphism and its inverse have piecewise-linear ambient
coordinate formulas.

The height condition says exactly that these segments meet only at `b`. -/
theorem exists_homeomorph_closedStarRealization_convexJoin
    (hK : IsCompact (closedStarRealization K {v})) (hne : (geometricLink K v).Nonempty)
    (hF : IsPLOn F (range fun y : geometricLink K v => (y.1.1 : ι → ℝ)))
    (hG : IsPLOn G (range fun y : geometricLink K v => F (y.1.1 : ι → ℝ)))
    (hGF : ∀ y : geometricLink K v, G (F (y.1.1 : ι → ℝ)) = y.1.1)
    (hh : IsPLOn h (convexJoin ℝ (range fun y : geometricLink K v => F (y.1.1 : ι → ℝ)) {b}))
    (hhF : ∀ y : geometricLink K v, ∀ t ∈ Icc (0 : ℝ) 1,
      h ((1 - t) • F (y.1.1 : ι → ℝ) + t • b) = t) :
    ∃ φ : closedStarRealization K {v} ≃ₜ
        convexJoin ℝ (range fun y : geometricLink K v => F (y.1.1 : ι → ℝ)) {b},
      (φ (starApex K v) : κ → ℝ) = b ∧ (∀ x, h (φ x) = x.1.1 v) ∧
      (∀ x (hx : x.1.1 v < 1), (φ x : κ → ℝ) = (1 - x.1.1 v) • F ((starLinkProjection K v
        ⟨x.1, (mem_puncturedClosedStar K v _).mpr ⟨x.2, hx⟩⟩).1.1 : ι → ℝ) + x.1.1 v • b) ∧
      ∃ F' : (ι → ℝ) → (κ → ℝ), ∃ G' : (κ → ℝ) → (ι → ℝ),
        IsPLOn F' (range fun x : closedStarRealization K {v} => (x.1.1 : ι → ℝ)) ∧
        IsPLOn G' (convexJoin ℝ (range fun y : geometricLink K v => F (y.1.1 : ι → ℝ)) {b}) ∧
        (∀ x, F' (x.1.1 : ι → ℝ) = φ x) ∧ ∀ x, G' (φ x) = (x.1.1 : ι → ℝ) := by
  let S := convexJoin ℝ (range fun y : geometricLink K v => F (y.1.1 : ι → ℝ)) {b}
  let f : closedStarRealization K {v} → S := fun x =>
    ⟨joinFormula F b v (x.1.1 : ι → ℝ), joinFormula_mem hne x⟩
  have hFPL := isPLOn_joinFormula (b := b) hK hF
  have hcont : Continuous f :=
    (hFPL.continuousOn.comp_continuous ((continuous_realization_coe K).comp
      continuous_subtype_val) fun x => mem_range_self x).subtype_mk _
  have hinj : Function.Injective f := by
    intro x y hxy
    have hcoe := congrArg (fun z : S => joinInverseFormula G h b v z.1) hxy
    simp only [f, joinInverseFormula_joinFormula hne hGF hhF] at hcoe
    exact Subtype.ext (Subtype.ext (DFunLike.coe_injective hcoe))
  have hsurj : Function.Surjective f := fun z =>
    (exists_joinFormula_eq z.2).imp fun _ hx => Subtype.ext hx
  have : CompactSpace (closedStarRealization K {v}) := isCompact_iff_compactSpace.mp hK
  let φ : closedStarRealization K {v} ≃ₜ S :=
    hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hinj, hsurj⟩)
  -- `Equiv.ofBijective` and `homeoOfEquivCompactToT2` both keep the underlying function, so
  -- `φ x` is `f x` by definition; the rewriting lemmas `Equiv.coe_ofBijective` and
  -- `Continuous.toEquiv_homeoOfEquivCompactToT2` are themselves proved by `rfl`.
  refine ⟨φ, joinFormula_starApex F b, h_joinFormula hne hhF, joinFormula_of_lt F b,
    joinFormula F b v, joinInverseFormula G h b v, hFPL, isPLOn_joinInverseFormula hK hF hG hh hhF,
    fun x => rfl, joinInverseFormula_joinFormula hne hGF hhF⟩

end AbstractSimplicialComplex
