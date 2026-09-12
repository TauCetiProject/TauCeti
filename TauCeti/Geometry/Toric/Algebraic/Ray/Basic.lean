/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.Cone.Basic
public import TauCeti.Geometry.Convex.Cone.Face.Basic
public import TauCeti.Geometry.Convex.Cone.Face.Finite

/-!
# Rays of toric cones

A ray of a cone is a one-dimensional face. This file defines the ray type on Mathlib's face
lattice and proves the finiteness needed to index the primitive ray generators of a toric cone:
finite generation of the ambient cone alone already bounds the rays. It also records the
geometric content of one-dimensionality: every nonzero point of a salient ray spans it as a
pointed cone.

## Main declarations

* `TauCeti.Toric.ToricRay`: the one-dimensional faces of a pointed cone.
* `TauCeti.Toric.ToricRay.finite_of_fg`: a finitely generated pointed cone, and hence a toric
  cone, has finitely many rays.
* `TauCeti.Toric.ToricRay.exists_mem_ne_zero`: every ray contains a nonzero point.
* `TauCeti.Toric.ToricRay.eq_hull_singleton`: every nonzero point of a salient ray generates
  that ray.
* `TauCeti.Toric.ToricRay.instIsEmptyBot`: the zero cone has no rays.
* `TauCeti.Toric.ToricRay.faceEmbedding`: the rays of a face of a cone are rays of the cone.
* `TauCeti.Toric.ToricRay.hullSingleton` and `TauCeti.Toric.ToricRay.eq_hullSingleton`: the cone
  spanned by a nonzero vector is its own only ray.
* `TauCeti.Toric.ToricRay.map_fst_eq_bot_of_map_snd_ne_bot`,
  `TauCeti.Toric.ToricRay.prodRayFst`, `TauCeti.Toric.ToricRay.prodRaySnd`,
  `TauCeti.Toric.ToricRay.prodInl`, `TauCeti.Toric.ToricRay.prodInr` and
  `TauCeti.Toric.ToricRay.prodSplit`: the rays of a product of salient cones are exactly the rays
  of the two factors.

## References

The ray description is from §1.2 of W. Fulton, *Introduction to Toric Varieties*, and §1.2 of
D. Cox, J. Little and H. Schenck, *Toric Varieties*.
-/

public section

namespace TauCeti.Toric

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {σ τ : PointedCone ℝ V}

/-- A ray of a pointed cone is a face whose linear span has real dimension one. -/
-- Interface source: `TauCetiRoadmap/AnalyticToricGeometry/Suggested.lean`.
abbrev ToricRay (σ : PointedCone ℝ V) :=
  {ρ : σ.Face // Module.finrank ℝ (Submodule.span ℝ ((ρ : PointedCone ℝ V) : Set V)) = 1}

namespace ToricRay

/-- The pointed cone underlying a ray. -/
abbrev toPointedCone (ρ : ToricRay σ) : PointedCone ℝ V := ρ.1.toPointedCone

/-- Rays are viewed as sets of vectors: membership `x ∈ ρ` and the coercion `(ρ : Set V)` both
refer to the pointed cone `ρ.toPointedCone` underlying the ray, and two rays with the same
points are equal. -/
instance : SetLike (ToricRay σ) V where
  coe ρ := ρ.toPointedCone
  coe_injective _ρ _τ h := Subtype.ext (PointedCone.Face.ext fun x ↦ Set.ext_iff.mp h x)

/-- The span of the cone underlying a ray has real dimension one. -/
@[simp]
theorem finrank_span (ρ : ToricRay σ) :
    Module.finrank ℝ (Submodule.span ℝ (ρ : Set V)) = 1 := ρ.2

/-- A ray is not the zero pointed cone. -/
theorem toPointedCone_ne_bot (ρ : ToricRay σ) : ρ.toPointedCone ≠ ⊥ := by
  intro hρ
  have hset : (ρ : Set V) = ({0} : Set V) :=
    congrArg (fun C : PointedCone ℝ V ↦ (C : Set V)) hρ
  have hdim := ρ.finrank_span
  rw [hset, Submodule.span_zero_singleton, finrank_bot] at hdim
  omega

/-- Every ray contains a nonzero point. -/
theorem exists_mem_ne_zero (ρ : ToricRay σ) : ∃ x : V, x ∈ ρ ∧ x ≠ 0 := by
  exact Submodule.exists_mem_ne_zero_of_ne_bot ρ.toPointedCone_ne_bot

/-- Every nonzero point of a salient ray generates it as a pointed cone. Only the ray itself has
to be salient; for a ray of a salient ambient cone this follows from `ConvexCone.Salient.anti`
along the face inclusion. -/
theorem eq_hull_singleton (ρ : ToricRay σ) (hρ : (ρ.toPointedCone : ConvexCone ℝ V).Salient)
    {x : V} (hx : x ∈ ρ) (hx0 : x ≠ 0) : ρ.toPointedCone = PointedCone.hull ℝ {x} := by
  apply le_antisymm
  · rw [PointedCone.le_hull_singleton_iff]
    intro y hy
    have hspan_eq : Submodule.span ℝ (ρ : Set V) = ℝ ∙ x :=
      eq_span_singleton_of_mem_of_finrank_eq_one ρ.finrank_span
        (Submodule.subset_span hx) hx0
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hspan_eq ▸ Submodule.subset_span hy)
    refine ⟨a, ?_, ha⟩
    by_contra ha0
    have ha_neg : a < 0 := lt_of_not_ge ha0
    have hnegx : -x ∈ ρ := by
      have hscale : -a⁻¹ • y ∈ ρ :=
        ρ.toPointedCone.smul_mem (neg_nonneg.mpr (inv_nonpos.mpr ha_neg.le)) hy
      rw [← ha, smul_smul, neg_mul, inv_mul_cancel₀ ha_neg.ne, neg_one_smul] at hscale
      exact hscale
    exact hρ x hx hx0 hnegx
  · exact Submodule.span_le.2 fun _ hx' ↦ by simpa using hx' ▸ hx

/-! ### The zero cone -/

/-- The zero cone has no rays: its only face is itself, whose span is zero-dimensional. -/
instance instIsEmptyBot : IsEmpty (ToricRay (⊥ : PointedCone ℝ V)) where
  false ρ := ρ.toPointedCone_ne_bot (le_antisymm ρ.1.isFaceOf.le bot_le)

/-! ### Rays of a face -/

/-- A ray of a face `τ` of a cone `σ` is a ray of `σ`: a face of a face is a face, and
one-dimensionality of the span does not mention the ambient cone. -/
def faceEmbedding (hτ : τ.IsFaceOf σ) : ToricRay τ ↪ ToricRay σ where
  toFun ρ := ⟨⟨ρ.toPointedCone, ρ.1.isFaceOf.trans hτ⟩, ρ.2⟩
  inj' ρ ρ' h := by
    have hcone : ρ.toPointedCone = ρ'.toPointedCone :=
      congrArg (fun ν : ToricRay σ ↦ ν.toPointedCone) h
    exact Subtype.ext (SetLike.coe_injective
      (congrArg (fun C : PointedCone ℝ V ↦ (C : Set V)) hcone))

@[simp]
theorem toPointedCone_faceEmbedding (hτ : τ.IsFaceOf σ) (ρ : ToricRay τ) :
    (faceEmbedding hτ ρ).toPointedCone = ρ.toPointedCone := (rfl)

@[simp]
theorem mem_faceEmbedding (hτ : τ.IsFaceOf σ) (ρ : ToricRay τ) {x : V} :
    x ∈ faceEmbedding hτ ρ ↔ x ∈ ρ := (Iff.rfl)

/-! ### The ray spanned by a vector -/

/-- The cone spanned by a nonzero vector is a ray of itself, and by
`TauCeti.Toric.ToricRay.eq_hullSingleton` its only one. -/
def hullSingleton {x : V} (hx : x ≠ 0) : ToricRay (PointedCone.hull ℝ {x}) :=
  ⟨⟨PointedCone.hull ℝ {x}, PointedCone.IsFaceOf.refl _⟩,
    PointedCone.finrank_span_coe_hull_singleton hx⟩

@[simp]
theorem toPointedCone_hullSingleton {x : V} (hx : x ≠ 0) :
    (hullSingleton hx).toPointedCone = PointedCone.hull ℝ {x} := (rfl)

/-- Membership in the ray spanned by a vector is membership in its underlying cone. -/
@[simp]
theorem mem_hullSingleton {x : V} (hx : x ≠ 0) {y : V} :
    y ∈ hullSingleton hx ↔ y ∈ PointedCone.hull ℝ {x} := (Iff.rfl)

/-- A ray of the cone spanned by a vector is the whole cone: a proper face of that cone misses the
spanning vector, hence is the zero cone, which is not a ray. -/
@[simp]
theorem toPointedCone_eq_of_hull_singleton {x : V}
    (ρ : ToricRay (PointedCone.hull ℝ {x})) : ρ.toPointedCone = PointedCone.hull ℝ {x} := by
  have hx : x ∈ ρ.toPointedCone := by
    by_contra hx
    have h := ρ.1.eq_hull_inter_of_eq_hull {x} rfl
    rw [Set.singleton_inter_eq_empty.2 (by simpa using hx)] at h
    exact ρ.toPointedCone_ne_bot (by simpa using h)
  exact le_antisymm ρ.1.isFaceOf.le (Submodule.span_le.2 (Set.singleton_subset_iff.2 hx))

/-- The cone spanned by a nonzero vector has exactly one ray. -/
theorem eq_hullSingleton {x : V} (hx : x ≠ 0) (ρ : ToricRay (PointedCone.hull ℝ {x})) :
    ρ = hullSingleton hx :=
  SetLike.coe_injective (congrArg (fun C : PointedCone ℝ V ↦ (C : Set V))
    (ρ.toPointedCone_eq_of_hull_singleton.trans (toPointedCone_hullSingleton hx).symm))

/-- Two rays with the same underlying cone are equal. -/
theorem toPointedCone_injective :
    Function.Injective (toPointedCone : ToricRay σ → PointedCone ℝ V) := fun _ _ h ↦
  SetLike.coe_injective (congrArg (fun C : PointedCone ℝ V ↦ (C : Set V)) h)

/-! ### Rays of a product -/

section Prod

variable {V' : Type*} [AddCommGroup V'] [Module ℝ V'] {τ : PointedCone ℝ V'}

/-- A ray of a product of cones is spanned by a single point, so its two projections are the cones
spanned by the two coordinates of that point. -/
private lemma exists_eq_hull_and_map_eq_hull
    (hστ : ((σ.prod τ : PointedCone ℝ (V × V')) : ConvexCone ℝ (V × V')).Salient)
    (G : ToricRay (σ.prod τ)) :
    ∃ p : V × V', p ≠ 0 ∧ G.toPointedCone = PointedCone.hull ℝ {p} ∧
      PointedCone.map (LinearMap.fst ℝ V V') G.toPointedCone = PointedCone.hull ℝ {p.1} ∧
      PointedCone.map (LinearMap.snd ℝ V V') G.toPointedCone = PointedCone.hull ℝ {p.2} := by
  obtain ⟨p, hpG, hp0⟩ := G.exists_mem_ne_zero
  have hGeq : G.toPointedCone = PointedCone.hull ℝ {p} :=
    G.eq_hull_singleton (hστ.anti fun _ hx ↦ G.1.isFaceOf.le hx) hpG hp0
  have hmapfst : PointedCone.map (LinearMap.fst ℝ V V') (PointedCone.hull ℝ {p})
      = PointedCone.hull ℝ ((LinearMap.fst ℝ V V') '' {p}) := Submodule.map_span _ _
  have hmapsnd : PointedCone.map (LinearMap.snd ℝ V V') (PointedCone.hull ℝ {p})
      = PointedCone.hull ℝ ((LinearMap.snd ℝ V V') '' {p}) := Submodule.map_span _ _
  refine ⟨p, hp0, hGeq, ?_, ?_⟩
  · rw [hGeq, hmapfst, Set.image_singleton]; rfl
  · rw [hGeq, hmapsnd, Set.image_singleton]; rfl

/-- A ray of a product of salient cones does not meet both factors: if its projection to the second
factor is not the zero cone, then its projection to the first factor is. A spanning point of the ray
cannot have both coordinates nonzero, because the ray then also contains the point with its second
coordinate replaced by zero, which is not a nonnegative multiple of the spanning point. -/
theorem map_fst_eq_bot_of_map_snd_ne_bot
    (hστ : ((σ.prod τ : PointedCone ℝ (V × V')) : ConvexCone ℝ (V × V')).Salient)
    (G : ToricRay (σ.prod τ))
    (h : PointedCone.map (LinearMap.snd ℝ V V') G.toPointedCone ≠ ⊥) :
    PointedCone.map (LinearMap.fst ℝ V V') G.toPointedCone = ⊥ := by
  obtain ⟨p, -, hGeq, hfst, hsnd⟩ := exists_eq_hull_and_map_eq_hull hστ G
  have hp2 : p.2 ≠ 0 := fun hp2 ↦ h (by rw [hsnd, hp2]; simp)
  have hpG : p ∈ G.toPointedCone := by
    rw [hGeq]; exact PointedCone.subset_hull (Set.mem_singleton p)
  have hmem : (p.1, (0 : V')) ∈ PointedCone.hull ℝ {p} := by
    rw [← hGeq]
    have hp := Submodule.mem_prod.1 (G.1.isFaceOf.le hpG)
    exact G.1.isFaceOf.mem_of_add_mem_left (x := (p.1, 0)) (y := (0, p.2))
      (Submodule.mem_prod.2 ⟨hp.1, Submodule.zero_mem _⟩)
      (Submodule.mem_prod.2 ⟨Submodule.zero_mem _, hp.2⟩) (by simpa using hpG)
  obtain ⟨c, -, hcp⟩ := PointedCone.mem_hull_singleton.1 hmem
  have hc : c = 0 := by
    have h2 : c • p.2 = 0 := by simpa using congrArg Prod.snd hcp
    exact (smul_eq_zero.1 h2).resolve_right hp2
  have hp1 : p.1 = 0 := by
    have h1 := congrArg Prod.fst hcp
    simp [hc] at h1
    exact h1.symm
  rw [hfst, hp1]
  simp

/-- The projection to the first factor of a ray of a product of salient cones whose projection to
the second factor is the zero cone is one-dimensional, hence a ray of that factor. -/
theorem finrank_span_map_fst_eq_one
    (hστ : ((σ.prod τ : PointedCone ℝ (V × V')) : ConvexCone ℝ (V × V')).Salient)
    (G : ToricRay (σ.prod τ))
    (h : PointedCone.map (LinearMap.snd ℝ V V') G.toPointedCone = ⊥) :
    Module.finrank ℝ (Submodule.span ℝ
      ((PointedCone.map (LinearMap.fst ℝ V V') G.toPointedCone : PointedCone ℝ V) : Set V))
      = 1 := by
  obtain ⟨p, hp0, -, hfst, hsnd⟩ := exists_eq_hull_and_map_eq_hull hστ G
  have hp2 : p.2 = 0 := by simpa using hsnd.symm.trans h
  rw [hfst]
  exact PointedCone.finrank_span_coe_hull_singleton fun hp1 ↦ hp0 (Prod.ext hp1 hp2)

/-- The projection to the second factor of a ray of a product of salient cones whose projection to
the second factor is not the zero cone is one-dimensional, hence a ray of that factor. -/
theorem finrank_span_map_snd_eq_one
    (hστ : ((σ.prod τ : PointedCone ℝ (V × V')) : ConvexCone ℝ (V × V')).Salient)
    (G : ToricRay (σ.prod τ))
    (h : PointedCone.map (LinearMap.snd ℝ V V') G.toPointedCone ≠ ⊥) :
    Module.finrank ℝ (Submodule.span ℝ
      ((PointedCone.map (LinearMap.snd ℝ V V') G.toPointedCone : PointedCone ℝ V') : Set V'))
      = 1 := by
  obtain ⟨p, hp0, -, hfst, hsnd⟩ := exists_eq_hull_and_map_eq_hull hστ G
  have hp1 : p.1 = 0 := by
    simpa using hfst.symm.trans (map_fst_eq_bot_of_map_snd_ne_bot hστ G h)
  rw [hsnd]
  exact PointedCone.finrank_span_coe_hull_singleton fun hp2 ↦ hp0 (Prod.ext hp1 hp2)

/-- The ray of the first factor underlying a ray of a product of salient cones whose projection to
the second factor is the zero cone. -/
noncomputable def prodRayFst
    (hστ : ((σ.prod τ : PointedCone ℝ (V × V')) : ConvexCone ℝ (V × V')).Salient)
    (G : ToricRay (σ.prod τ))
    (h : PointedCone.map (LinearMap.snd ℝ V V') G.toPointedCone = ⊥) : ToricRay σ :=
  ⟨⟨_, G.1.isFaceOf.fst⟩, finrank_span_map_fst_eq_one hστ G h⟩

@[simp]
theorem toPointedCone_prodRayFst
    (hστ : ((σ.prod τ : PointedCone ℝ (V × V')) : ConvexCone ℝ (V × V')).Salient)
    (G : ToricRay (σ.prod τ))
    (h : PointedCone.map (LinearMap.snd ℝ V V') G.toPointedCone = ⊥) :
    (prodRayFst hστ G h).toPointedCone =
      PointedCone.map (LinearMap.fst ℝ V V') G.toPointedCone := (rfl)

@[simp]
theorem mem_prodRayFst
    (hστ : ((σ.prod τ : PointedCone ℝ (V × V')) : ConvexCone ℝ (V × V')).Salient)
    (G : ToricRay (σ.prod τ))
    (h : PointedCone.map (LinearMap.snd ℝ V V') G.toPointedCone = ⊥) {x : V} :
    x ∈ prodRayFst hστ G h ↔ x ∈ PointedCone.map (LinearMap.fst ℝ V V') G.toPointedCone := (Iff.rfl)

/-- The ray of the second factor underlying a ray of a product of salient cones whose projection to
the second factor is not the zero cone. -/
noncomputable def prodRaySnd
    (hστ : ((σ.prod τ : PointedCone ℝ (V × V')) : ConvexCone ℝ (V × V')).Salient)
    (G : ToricRay (σ.prod τ))
    (h : PointedCone.map (LinearMap.snd ℝ V V') G.toPointedCone ≠ ⊥) : ToricRay τ :=
  ⟨⟨_, G.1.isFaceOf.snd⟩, finrank_span_map_snd_eq_one hστ G h⟩

@[simp]
theorem toPointedCone_prodRaySnd
    (hστ : ((σ.prod τ : PointedCone ℝ (V × V')) : ConvexCone ℝ (V × V')).Salient)
    (G : ToricRay (σ.prod τ))
    (h : PointedCone.map (LinearMap.snd ℝ V V') G.toPointedCone ≠ ⊥) :
    (prodRaySnd hστ G h).toPointedCone =
      PointedCone.map (LinearMap.snd ℝ V V') G.toPointedCone := (rfl)

@[simp]
theorem mem_prodRaySnd
    (hστ : ((σ.prod τ : PointedCone ℝ (V × V')) : ConvexCone ℝ (V × V')).Salient)
    (G : ToricRay (σ.prod τ))
    (h : PointedCone.map (LinearMap.snd ℝ V V') G.toPointedCone ≠ ⊥) {x : V'} :
    x ∈ prodRaySnd hστ G h ↔ x ∈ PointedCone.map (LinearMap.snd ℝ V V') G.toPointedCone := (Iff.rfl)

/-- A ray of a product of cones is determined by its two projections. -/
theorem prod_ext {G H : ToricRay (σ.prod τ)}
    (h₁ : PointedCone.map (LinearMap.fst ℝ V V') G.toPointedCone
      = PointedCone.map (LinearMap.fst ℝ V V') H.toPointedCone)
    (h₂ : PointedCone.map (LinearMap.snd ℝ V V') G.toPointedCone
      = PointedCone.map (LinearMap.snd ℝ V V') H.toPointedCone) : G = H := by
  apply toPointedCone_injective
  have key {A B : ToricRay (σ.prod τ)}
      (hfst : PointedCone.map (LinearMap.fst ℝ V V') A.toPointedCone ≤
        PointedCone.map (LinearMap.fst ℝ V V') B.toPointedCone)
      (hsnd : PointedCone.map (LinearMap.snd ℝ V V') A.toPointedCone ≤
        PointedCone.map (LinearMap.snd ℝ V V') B.toPointedCone) :
      A.toPointedCone ≤ B.toPointedCone := by
    intro x hx
    obtain ⟨a, ha, ha1⟩ := Submodule.mem_map.1
      (hfst (Submodule.mem_map.2 ⟨x, hx, rfl⟩))
    obtain ⟨c, hc, hc2⟩ := Submodule.mem_map.1
      (hsnd (Submodule.mem_map.2 ⟨x, hx, rfl⟩))
    have hxa : (x.1, a.2) = a := Prod.ext ha1.symm rfl
    have hcx : (c.1, x.2) = c := Prod.ext rfl hc2.symm
    have hadd : (x.1, a.2) + (c.1, x.2) = x + (c.1, a.2) := by
      ext <;> simp [add_comm]
    have hsum : x + (c.1, a.2) ∈ B.toPointedCone := by
      rw [← hadd, hxa, hcx]
      exact Submodule.add_mem _ ha hc
    exact B.1.isFaceOf.mem_of_add_mem_left (x := x) (y := (c.1, a.2))
      (Submodule.mem_prod.2 ⟨by
          have h := B.1.isFaceOf.le ha
          rw [← hxa] at h
          exact (Submodule.mem_prod.1 h).1,
        by
          have h := B.1.isFaceOf.le hc
          rw [← hcx] at h
          exact (Submodule.mem_prod.1 h).2⟩)
      (Submodule.mem_prod.2 ⟨(Submodule.mem_prod.1 (B.1.isFaceOf.le hc)).1,
        (Submodule.mem_prod.1 (B.1.isFaceOf.le ha)).2⟩) hsum
  exact le_antisymm (key h₁.le h₂.le) (key h₁.ge h₂.ge)

/-- A ray of the first factor, read as a ray of a product of cones: its product with the zero
cone. This is a face of the product because the zero cone is a face of the salient second
factor, and its span has the dimension of the span of the ray. -/
def prodInl (hτ : (τ : ConvexCone ℝ V').Salient) (ρ : ToricRay σ) : ToricRay (σ.prod τ) :=
  ⟨⟨ρ.toPointedCone.prod ⊥, ρ.1.isFaceOf.prod hτ.bot_isFaceOf⟩,
    (PointedCone.finrank_span_coe_prod_bot ρ.toPointedCone).trans ρ.2⟩

@[simp]
theorem toPointedCone_prodInl (hτ : (τ : ConvexCone ℝ V').Salient) (ρ : ToricRay σ) :
    (prodInl hτ ρ).toPointedCone = ρ.toPointedCone.prod ⊥ := (rfl)

/-- Membership in a ray included from the first factor is coordinatewise. -/
@[simp]
theorem mem_prodInl (hτ : (τ : ConvexCone ℝ V').Salient) (ρ : ToricRay σ) {x : V × V'} :
    x ∈ prodInl hτ ρ ↔ x.1 ∈ ρ ∧ x.2 = 0 := (Iff.rfl)

/-- A ray of the second factor, read as a ray of a product of cones: its product with the zero
cone. This is a face of the product because the zero cone is a face of the salient first factor,
and its span has the dimension of the span of the ray. -/
def prodInr (hσ : (σ : ConvexCone ℝ V).Salient) (ρ : ToricRay τ) : ToricRay (σ.prod τ) :=
  ⟨⟨(⊥ : PointedCone ℝ V).prod ρ.toPointedCone, hσ.bot_isFaceOf.prod ρ.1.isFaceOf⟩,
    (PointedCone.finrank_span_coe_bot_prod ρ.toPointedCone).trans ρ.2⟩

@[simp]
theorem toPointedCone_prodInr (hσ : (σ : ConvexCone ℝ V).Salient) (ρ : ToricRay τ) :
    (prodInr hσ ρ).toPointedCone = (⊥ : PointedCone ℝ V).prod ρ.toPointedCone := (rfl)

/-- Membership in a ray included from the second factor is coordinatewise. -/
@[simp]
theorem mem_prodInr (hσ : (σ : ConvexCone ℝ V).Salient) (ρ : ToricRay τ) {x : V × V'} :
    x ∈ prodInr hσ ρ ↔ x.1 = 0 ∧ x.2 ∈ ρ := (Iff.rfl)

open Classical in
/-- The decomposition of the rays of a product of salient cones: the rays of `σ.prod τ` are
exactly the rays of the two factors, a ray of a factor corresponding to its product with the zero
cone. The two cases of the forward map are computed by
`TauCeti.Toric.ToricRay.prodSplit_eq_inl` and `TauCeti.Toric.ToricRay.prodSplit_eq_inr`. -/
noncomputable def prodSplit (hσ : (σ : ConvexCone ℝ V).Salient)
    (hτ : (τ : ConvexCone ℝ V').Salient) : ToricRay (σ.prod τ) ≃ ToricRay σ ⊕ ToricRay τ where
  toFun G := if h : PointedCone.map (LinearMap.snd ℝ V V') G.toPointedCone = ⊥ then
    Sum.inl (prodRayFst (hσ.prod hτ) G h) else Sum.inr (prodRaySnd (hσ.prod hτ) G h)
  invFun := Sum.elim (prodInl hτ) (prodInr hσ)
  left_inv G := by
    dsimp only
    by_cases h : PointedCone.map (LinearMap.snd ℝ V V') G.toPointedCone = ⊥
    · -- The ray is the product of its first projection with the zero cone.
      rw [dite_eq_left h, Sum.elim_inl]
      exact prod_ext (Submodule.prod_map_fst ..) ((Submodule.prod_map_snd ..).trans h.symm)
    · -- The ray is the product of the zero cone with its second projection.
      rw [dite_eq_right h, Sum.elim_inr]
      exact prod_ext ((Submodule.prod_map_fst ..).trans
        (map_fst_eq_bot_of_map_snd_ne_bot (hσ.prod hτ) G h).symm) (Submodule.prod_map_snd ..)
  right_inv := by
    rintro (ρ | ρ)
    · have h : PointedCone.map (LinearMap.snd ℝ V V') (prodInl hτ ρ).toPointedCone = ⊥ :=
        Submodule.prod_map_snd ..
      dsimp only
      rw [Sum.elim_inl, dite_eq_left h]
      exact congrArg Sum.inl (toPointedCone_injective (Submodule.prod_map_fst ..))
    · have h : PointedCone.map (LinearMap.snd ℝ V V') (prodInr hσ ρ).toPointedCone ≠ ⊥ :=
        fun hbot ↦ ρ.toPointedCone_ne_bot ((Submodule.prod_map_snd ..).symm.trans hbot)
      dsimp only
      rw [Sum.elim_inr, dite_eq_right h]
      exact congrArg Sum.inr (toPointedCone_injective (Submodule.prod_map_snd ..))

@[simp]
theorem prodSplit_eq_inl (hσ : (σ : ConvexCone ℝ V).Salient)
    (hτ : (τ : ConvexCone ℝ V').Salient) (G : ToricRay (σ.prod τ))
    (h : PointedCone.map (LinearMap.snd ℝ V V') G.toPointedCone = ⊥) :
    prodSplit hσ hτ G = Sum.inl (prodRayFst (hσ.prod hτ) G h) := dite_eq_left h

@[simp]
theorem prodSplit_eq_inr (hσ : (σ : ConvexCone ℝ V).Salient)
    (hτ : (τ : ConvexCone ℝ V').Salient) (G : ToricRay (σ.prod τ))
    (h : PointedCone.map (LinearMap.snd ℝ V V') G.toPointedCone ≠ ⊥) :
    prodSplit hσ hτ G = Sum.inr (prodRaySnd (hσ.prod hτ) G h) := dite_eq_right h

@[simp]
theorem prodSplit_symm_inl (hσ : (σ : ConvexCone ℝ V).Salient)
    (hτ : (τ : ConvexCone ℝ V').Salient) (ρ : ToricRay σ) :
    (prodSplit hσ hτ).symm (Sum.inl ρ) = prodInl hτ ρ := (rfl)

@[simp]
theorem prodSplit_symm_inr (hσ : (σ : ConvexCone ℝ V).Salient)
    (hτ : (τ : ConvexCone ℝ V').Salient) (ρ : ToricRay τ) :
    (prodSplit hσ hτ).symm (Sum.inr ρ) = prodInr hσ ρ := (rfl)

end Prod

/-- A finitely generated pointed cone has finitely many rays. In fact finite generation alone
makes its entire face lattice finite; this is inherited by the subtype of one-dimensional
faces. -/
theorem finite_of_fg (hσ : σ.FG) : Finite (ToricRay σ) := by
  let _ := PointedCone.FG.finite_face hσ
  infer_instance

end ToricRay

end TauCeti.Toric
