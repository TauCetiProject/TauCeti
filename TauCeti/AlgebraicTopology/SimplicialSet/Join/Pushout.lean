/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import TauCeti.AlgebraicTopology.SimplicialSet.Coslice

/-!
# Joins preserve pushouts, and slices turn pushouts of diagrams into pullbacks

For a fixed simplicial set `Y`, the joins `Y ⋆ -` and `- ⋆ Y` preserve pushouts
(`SSet.join.isPushout_map_id_left`, `SSet.join.isPushout_map_id_right`). Indeed, maps `Y ⋆ X ⟶ C`
restricting to `p : Y ⟶ C` are the maps `X ⟶ C_{p/}` into the coslice
(`SSet.coslice.homEquiv`). Two maps out of `Y ⋆ B` and `Y ⋆ D` which agree on `Y ⋆ A` have the same
restriction `p` to `Y`, so they are maps from `B` and `D` into the one coslice `C_{p/}`, and these
glue along a pushout of `B` and `D`. Dually, `- ⋆ Y` is handled through slices.

Consequently slices and coslices turn pushouts of diagrams into pullbacks
(`SSet.slice.isPullback_map_of_isPushout`, `SSet.coslice.isPullback_map_of_isPushout`): if `K` is
the pushout of `B` and `D` along `A`, then the slice over a diagram `p : K ⟶ C` is the fibre product
of the slices over the restrictions of `p` to `B` and to `D`, over the slice over its restriction to
`A`. In other words, a cone over `p` is a pair of cones over its restrictions to `B` and `D` which
agree on `A`. Since the horn `Λ[2, 2]` is the pushout of two edges along their common target, the
slice over a cospan `Λ[2, 2] ⟶ C` is the fibre product of the slices over its two edges, over the
slice over the vertex `2` (`SSet.slice.isPullback_horn₂₂`); dually, the coslice under a span
`Λ[2, 0] ⟶ C` is the fibre product of the coslices under its two edges
(`SSet.coslice.isPullback_horn₂₀`). Pullback and pushout squares in a quasicategory are limit cones
over cospans and colimit cocones under spans, so this reduces them to cones over edges and cocones
under edges.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.8 and §1.2.9.
-/

public section

universe u

open CategoryTheory Limits Simplicial

namespace SSet

variable {A B D K C : SSet.{u}} {t : A ⟶ B} {l : A ⟶ D} {r : B ⟶ K} {b : D ⟶ K}

namespace join

variable (Y : SSet.{u})

/-- **The join `Y ⋆ -` preserves pushouts**: for a pushout square of simplicial sets with corners
`A`, `B`, `D` and `K`, the square of joins `Y ⋆ A`, `Y ⋆ B`, `Y ⋆ D` and `Y ⋆ K` is a pushout
square. -/
lemma isPushout_map_id_left (sq : IsPushout t l r b) :
    IsPushout (map (𝟙 Y) t) (map (𝟙 Y) l) (map (𝟙 Y) r) (map (𝟙 Y) b) := by
  have hw : map (𝟙 Y) t ≫ map (𝟙 Y) r = map (𝟙 Y) l ≫ map (𝟙 Y) b := by
    rw [← map_comp, ← map_comp, sq.w]
  -- Both legs of a cocone restrict to the same map on `Y`, through which they become maps into a
  -- single coslice, glued along the pushout of `B` and `D`.
  have hinl (s : PushoutCocone (map (𝟙 Y) t) (map (𝟙 Y) l)) :
      inl Y D ≫ s.inr = inl Y B ≫ s.inl := by
    simpa using (congrArg (inl Y A ≫ ·) s.condition).symm
  let F₁ (s : PushoutCocone (map (𝟙 Y) t) (map (𝟙 Y) l)) : B ⟶ coslice (inl Y B ≫ s.inl) :=
    coslice.homEquiv.symm ⟨s.inl, rfl⟩
  let F₂ (s : PushoutCocone (map (𝟙 Y) t) (map (𝟙 Y) l)) : D ⟶ coslice (inl Y B ≫ s.inl) :=
    coslice.homEquiv.symm ⟨s.inr, hinl s⟩
  have hF (s : PushoutCocone (map (𝟙 Y) t) (map (𝟙 Y) l)) : t ≫ F₁ s = l ≫ F₂ s :=
    coslice.hom_ext (by simp [F₁, F₂, s.condition])
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk hw
    (fun s ↦ (coslice.homEquiv (sq.desc (F₁ s) (F₂ s) (hF s))).val) (fun s ↦ ?_) (fun s ↦ ?_)
    (fun s m hm₁ hm₂ ↦ ?_))
  · rw [← coslice.homEquiv_comp_coe, sq.inl_desc, Equiv.apply_symm_apply]
  · rw [← coslice.homEquiv_comp_coe, sq.inr_desc, Equiv.apply_symm_apply]
  · have hm : inl Y K ≫ m = inl Y B ≫ s.inl := by
      simp [← hm₁]
    have h : coslice.homEquiv.symm ⟨m, hm⟩ = sq.desc (F₁ s) (F₂ s) (hF s) :=
      sq.hom_ext (coslice.hom_ext (by simp [F₁, hm₁])) (coslice.hom_ext (by simp [F₂, hm₂]))
    rw [← h, Equiv.apply_symm_apply]

/-- **The join `- ⋆ Y` preserves pushouts**: for a pushout square of simplicial sets with corners
`A`, `B`, `D` and `K`, the square of joins `A ⋆ Y`, `B ⋆ Y`, `D ⋆ Y` and `K ⋆ Y` is a pushout
square. -/
lemma isPushout_map_id_right (sq : IsPushout t l r b) :
    IsPushout (map t (𝟙 Y)) (map l (𝟙 Y)) (map r (𝟙 Y)) (map b (𝟙 Y)) := by
  have hw : map t (𝟙 Y) ≫ map r (𝟙 Y) = map l (𝟙 Y) ≫ map b (𝟙 Y) := by
    rw [← map_comp, ← map_comp, sq.w]
  -- Dually, the legs of a cocone become maps into a single slice, glued along the pushout.
  have hinr (s : PushoutCocone (map t (𝟙 Y)) (map l (𝟙 Y))) :
      inr D Y ≫ s.inr = inr B Y ≫ s.inl := by
    simpa using (congrArg (inr A Y ≫ ·) s.condition).symm
  let F₁ (s : PushoutCocone (map t (𝟙 Y)) (map l (𝟙 Y))) : B ⟶ slice (inr B Y ≫ s.inl) :=
    slice.homEquiv.symm ⟨s.inl, rfl⟩
  let F₂ (s : PushoutCocone (map t (𝟙 Y)) (map l (𝟙 Y))) : D ⟶ slice (inr B Y ≫ s.inl) :=
    slice.homEquiv.symm ⟨s.inr, hinr s⟩
  have hF (s : PushoutCocone (map t (𝟙 Y)) (map l (𝟙 Y))) : t ≫ F₁ s = l ≫ F₂ s :=
    slice.hom_ext (by simp [F₁, F₂, s.condition])
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk hw
    (fun s ↦ (slice.homEquiv (sq.desc (F₁ s) (F₂ s) (hF s))).val) (fun s ↦ ?_) (fun s ↦ ?_)
    (fun s m hm₁ hm₂ ↦ ?_))
  · rw [← slice.homEquiv_comp_coe, sq.inl_desc, Equiv.apply_symm_apply]
  · rw [← slice.homEquiv_comp_coe, sq.inr_desc, Equiv.apply_symm_apply]
  · have hm : inr K Y ≫ m = inr B Y ≫ s.inl := by
      simp [← hm₁]
    have h : slice.homEquiv.symm ⟨m, hm⟩ = sq.desc (F₁ s) (F₂ s) (hF s) :=
      sq.hom_ext (slice.hom_ext (by simp [F₁, hm₁])) (slice.hom_ext (by simp [F₂, hm₂]))
    rw [← h, Equiv.apply_symm_apply]

end join

namespace slice

/-- **Slices turn pushouts of diagrams into pullbacks**: if `K` is the pushout of `B` and `D`
along `A`, the slice over a diagram `p : K ⟶ C` is the fibre product of the slices over its
restrictions to `B` and to `D`, over the slice over its restriction to `A`. -/
lemma isPullback_map_of_isPushout (sq : IsPushout t l r b) {p : K ⟶ C} {pA : A ⟶ C}
    {pB : B ⟶ C} {pD : D ⟶ C} (hr : r ≫ p ≫ 𝟙 C = pB) (hb : b ≫ p ≫ 𝟙 C = pD)
    (ht : t ≫ pB ≫ 𝟙 C = pA) (hl : l ≫ pD ≫ 𝟙 C = pA) :
    IsPullback (map r (𝟙 C) hr) (map b (𝟙 C) hb) (map t (𝟙 C) ht) (map l (𝟙 C) hl) := by
  have hw : map r (𝟙 C) hr ≫ map t (𝟙 C) ht = map b (𝟙 C) hb ≫ map l (𝟙 C) hl := by
    rw [map_comp, map_comp]
    congr 1
    exact sq.w
  -- A cone over the cospan consists of maps `T ⋆ B ⟶ C` and `T ⋆ D ⟶ C` agreeing on `T ⋆ A`,
  -- which glue to a map `T ⋆ K ⟶ C` along the pushout square of joins.
  have hcond (s : PullbackCone (map t (𝟙 C) ht) (map l (𝟙 C) hl)) :
      join.map (𝟙 _) t ≫ (homEquiv s.fst).val = join.map (𝟙 _) l ≫ (homEquiv s.snd).val := by
    simpa using congrArg (fun F ↦ (homEquiv F).val) s.condition
  have hinr (s : PullbackCone (map t (𝟙 C) ht) (map l (𝟙 C) hl)) :
      join.inr _ K ≫ (join.isPushout_map_id_left s.pt sq).desc _ _ (hcond s) = p :=
    sq.hom_ext
      (by rw [← join.inr_map_assoc (𝟙 _) r, IsPushout.inl_desc, (homEquiv s.fst).property, ← hr,
        Category.comp_id])
      (by rw [← join.inr_map_assoc (𝟙 _) b, IsPushout.inr_desc, (homEquiv s.snd).property, ← hb,
        Category.comp_id])
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun s ↦ homEquiv.symm ⟨_, hinr s⟩) (fun s ↦ hom_ext (by simp)) (fun s ↦ hom_ext (by simp))
    (fun s m hm₁ hm₂ ↦ hom_ext ?_))
  have h₁ := congrArg (fun F ↦ (homEquiv F).val) hm₁
  have h₂ := congrArg (fun F ↦ (homEquiv F).val) hm₂
  simp only [homEquiv_comp_map_coe, Category.comp_id] at h₁ h₂
  rw [Equiv.apply_symm_apply]
  exact (join.isPushout_map_id_left s.pt sq).hom_ext (by simp [h₁]) (by simp [h₂])

/-- The slice over a cospan `p : Λ[2, 2] ⟶ C` is the fibre product of the slices over its edges
from `0` and from `1` to `2`, over the slice over the vertex `2`. Thus a cone over `p` is a pair of
cones over the two edges which agree on their common target. -/
lemma isPullback_horn₂₂ (p : (Λ[2, 2] : SSet.{u}) ⟶ C) :
    IsPullback (map (p := p) (q := horn₂₂.ι₀₂ ≫ p) horn₂₂.ι₀₂ (𝟙 C) (by simp))
      (map (p := p) (q := horn₂₂.ι₁₂ ≫ p) horn₂₂.ι₁₂ (𝟙 C) (by simp))
      (map (q := stdSimplex.δ 0 ≫ horn₂₂.ι₀₂ ≫ p) (stdSimplex.δ 0) (𝟙 C) (by simp))
      (map (q := stdSimplex.δ 0 ≫ horn₂₂.ι₀₂ ≫ p) (stdSimplex.δ 0) (𝟙 C)
        (by simp [horn₂₂.isPushout.w_assoc])) :=
  isPullback_map_of_isPushout horn₂₂.isPushout _ _ _ _

end slice

namespace coslice

/-- **Coslices turn pushouts of diagrams into pullbacks**: if `K` is the pushout of `B` and `D`
along `A`, the coslice under a diagram `p : K ⟶ C` is the fibre product of the coslices under its
restrictions to `B` and to `D`, over the coslice under its restriction to `A`. -/
lemma isPullback_map_of_isPushout (sq : IsPushout t l r b) {p : K ⟶ C} {pA : A ⟶ C}
    {pB : B ⟶ C} {pD : D ⟶ C} (hr : r ≫ p ≫ 𝟙 C = pB) (hb : b ≫ p ≫ 𝟙 C = pD)
    (ht : t ≫ pB ≫ 𝟙 C = pA) (hl : l ≫ pD ≫ 𝟙 C = pA) :
    IsPullback (map r (𝟙 C) hr) (map b (𝟙 C) hb) (map t (𝟙 C) ht) (map l (𝟙 C) hl) := by
  have hw : map r (𝟙 C) hr ≫ map t (𝟙 C) ht = map b (𝟙 C) hb ≫ map l (𝟙 C) hl := by
    rw [map_comp, map_comp]
    congr 1
    exact sq.w
  -- A cocone under the span consists of maps `B ⋆ T ⟶ C` and `D ⋆ T ⟶ C` agreeing on `A ⋆ T`,
  -- which glue to a map `K ⋆ T ⟶ C` along the pushout square of joins.
  have hcond (s : PullbackCone (map t (𝟙 C) ht) (map l (𝟙 C) hl)) :
      join.map t (𝟙 _) ≫ (homEquiv s.fst).val = join.map l (𝟙 _) ≫ (homEquiv s.snd).val := by
    simpa using congrArg (fun F ↦ (homEquiv F).val) s.condition
  have hinl (s : PullbackCone (map t (𝟙 C) ht) (map l (𝟙 C) hl)) :
      join.inl K _ ≫ (join.isPushout_map_id_right s.pt sq).desc _ _ (hcond s) = p :=
    sq.hom_ext
      (by rw [← join.inl_map_assoc r (𝟙 _), IsPushout.inl_desc, (homEquiv s.fst).property, ← hr,
        Category.comp_id])
      (by rw [← join.inl_map_assoc b (𝟙 _), IsPushout.inr_desc, (homEquiv s.snd).property, ← hb,
        Category.comp_id])
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun s ↦ homEquiv.symm ⟨_, hinl s⟩) (fun s ↦ hom_ext (by simp)) (fun s ↦ hom_ext (by simp))
    (fun s m hm₁ hm₂ ↦ hom_ext ?_))
  have h₁ := congrArg (fun F ↦ (homEquiv F).val) hm₁
  have h₂ := congrArg (fun F ↦ (homEquiv F).val) hm₂
  simp only [homEquiv_comp_map_coe, Category.comp_id] at h₁ h₂
  rw [Equiv.apply_symm_apply]
  exact (join.isPushout_map_id_right s.pt sq).hom_ext (by simp [h₁]) (by simp [h₂])

/-- The coslice under a span `p : Λ[2, 0] ⟶ C` is the fibre product of the coslices under its
edges from `0` to `1` and to `2`, over the coslice under the vertex `0`. Thus a cocone under `p` is
a pair of cocones under the two edges which agree on their common source. -/
lemma isPullback_horn₂₀ (p : (Λ[2, 0] : SSet.{u}) ⟶ C) :
    IsPullback (map (p := p) (q := horn₂₀.ι₀₁ ≫ p) horn₂₀.ι₀₁ (𝟙 C) (by simp))
      (map (p := p) (q := horn₂₀.ι₀₂ ≫ p) horn₂₀.ι₀₂ (𝟙 C) (by simp))
      (map (q := stdSimplex.δ 1 ≫ horn₂₀.ι₀₁ ≫ p) (stdSimplex.δ 1) (𝟙 C) (by simp))
      (map (q := stdSimplex.δ 1 ≫ horn₂₀.ι₀₁ ≫ p) (stdSimplex.δ 1) (𝟙 C)
        (by simp [horn₂₀.isPushout.w_assoc])) :=
  isPullback_map_of_isPushout horn₂₀.isPushout _ _ _ _

end coslice

end SSet
