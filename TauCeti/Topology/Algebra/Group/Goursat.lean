/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Connected.PathConnected
public import TauCeti.GroupTheory.Goursat
import Mathlib.Tactic.Group

/-!
# Topological Goursat coordinates for diagonal overgroups

For a topological group `G`, the map `(g, h) ↦ (g / h, h)` is a self-homeomorphism of `G × G` with
inverse `(a, h) ↦ (a * h, h)` (`Homeomorph.prodDivRight`). When `H : Subgroup (G × G)` contains the
diagonal `(MonoidHom.id G).graph`, this homeomorphism restricts to a coordinate homeomorphism
`H ≃ₜ H.goursatFst × G` (`Subgroup.goursatCoordHomeomorph`), under which group multiplication
becomes the conjugation-twisted semidirect product `(a, h) * (b, k) = (a * (h * b * h⁻¹), h * k)`.

Closedness, preconnectedness, and path connectedness of `H` therefore reduce to those of the normal
subgroup `H.goursatFst ≤ G` whenever `G` itself is preconnected or path connected.

## Main definitions

* `Homeomorph.prodDivRight`: the coordinate homeomorphism `G × G ≃ₜ G × G` given by
  `(g, h) ↦ (g / h, h)`.
* `Subgroup.goursatCoordHomeomorph`: the restricted homeomorphism `H ≃ₜ H.goursatFst × G` for
  `(MonoidHom.id G).graph ≤ H`.

## Main results

* `Subgroup.goursatCoordHomeomorph_mul`: semidirect multiplication law in Goursat coordinates.
* `Subgroup.isClosed_iff_isClosed_goursatFst`: `H` is closed in `G × G` iff `H.goursatFst` is
  closed in `G`.
* `Subgroup.isPreconnected_iff_isPreconnected_goursatFst` and
  `Subgroup.pathConnectedSpace_iff_pathConnectedSpace_goursatFst`: connectedness and path
  connectedness transfer between `H` and `H.goursatFst`.

## References

* Nicolas Bourbaki, *General Topology*, Chapters 1–4, Springer, 1998, Chapter III, §2.
* Serge Lang, *Algebra*, revised third edition, Springer GTM 211, 2002, Chapter I, §9, Exercise 5.
-/

public section

namespace Homeomorph

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The coordinate homeomorphism `G × G ≃ₜ G × G` sending `(g, h)` to `(g / h, h)`, with inverse
`(a, h) ↦ (a * h, h)`. -/
def prodDivRight : G × G ≃ₜ G × G where
  toFun p := (p.1 / p.2, p.2)
  invFun p := (p.1 * p.2, p.2)
  left_inv p := Prod.ext (div_mul_cancel p.1 p.2) rfl
  right_inv p := Prod.ext (mul_div_cancel_right p.1 p.2) rfl
  continuous_toFun := (continuous_fst.div' continuous_snd).prodMk continuous_snd
  continuous_invFun := (continuous_fst.mul continuous_snd).prodMk continuous_snd

@[simp]
theorem prodDivRight_apply (p : G × G) : prodDivRight G p = (p.1 / p.2, p.2) :=
  (rfl)

@[simp]
theorem prodDivRight_symm_apply (p : G × G) : (prodDivRight G).symm p = (p.1 * p.2, p.2) :=
  (rfl)

end Homeomorph

namespace Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Goursat coordinate homeomorphism**: for `H : Subgroup (G × G)` containing the diagonal,
`(g, h) ↦ (g / h, h)` restricts to a homeomorphism `H ≃ₜ H.goursatFst × G`. -/
def goursatCoordHomeomorph {H : Subgroup (G × G)} (hH : (MonoidHom.id G).graph ≤ H) :
    H ≃ₜ H.goursatFst × G where
  toFun p := (⟨p.1.1 / p.1.2, (mem_iff_div_mem_goursatFst hH).mp p.2⟩, p.1.2)
  invFun q := ⟨(q.1.1 * q.2, q.2),
    (mem_iff_div_mem_goursatFst hH).mpr (by simp [mul_div_cancel_right])⟩
  left_inv p := Subtype.ext (Prod.ext (div_mul_cancel p.1.1 p.1.2) rfl)
  right_inv q := Prod.ext (Subtype.ext (mul_div_cancel_right q.1.1 q.2)) rfl
  continuous_toFun :=
    (((continuous_fst.comp continuous_subtype_val).div'
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  continuous_invFun :=
    (((continuous_subtype_val.comp continuous_fst).mul continuous_snd).prodMk
      continuous_snd).subtype_mk _

@[simp]
theorem coe_fst_goursatCoordHomeomorph {H : Subgroup (G × G)} (hH : (MonoidHom.id G).graph ≤ H)
    (p : H) : ((goursatCoordHomeomorph hH p).1 : G) = p.1.1 / p.1.2 :=
  (rfl)

@[simp]
theorem snd_goursatCoordHomeomorph {H : Subgroup (G × G)} (hH : (MonoidHom.id G).graph ≤ H)
    (p : H) : (goursatCoordHomeomorph hH p).2 = p.1.2 :=
  (rfl)

@[simp]
theorem coe_goursatCoordHomeomorph_symm {H : Subgroup (G × G)} (hH : (MonoidHom.id G).graph ≤ H)
    (q : H.goursatFst × G) : ((goursatCoordHomeomorph hH).symm q : G × G) = (q.1.1 * q.2, q.2) :=
  (rfl)

/-- In Goursat coordinates `(a, h) ∈ H.goursatFst × G`, multiplication in `H` is the semidirect law
`(a, h) * (b, k) = (a * (h * b * h⁻¹), h * k)`. -/
theorem goursatCoordHomeomorph_mul {H : Subgroup (G × G)} (hH : (MonoidHom.id G).graph ≤ H)
    (p q : H) :
    goursatCoordHomeomorph hH (p * q) =
      (⟨(goursatCoordHomeomorph hH p).1.1 *
          ((goursatCoordHomeomorph hH p).2 * (goursatCoordHomeomorph hH q).1.1 *
            (goursatCoordHomeomorph hH p).2⁻¹),
        H.goursatFst.mul_mem (goursatCoordHomeomorph hH p).1.2
          ((normal_goursatFst_of_graph_id_le hH).conj_mem _
            (goursatCoordHomeomorph hH q).1.2 _)⟩,
        (goursatCoordHomeomorph hH p).2 * (goursatCoordHomeomorph hH q).2) := by
  refine Prod.ext (Subtype.ext ?_) rfl
  simp only [coe_fst_goursatCoordHomeomorph, snd_goursatCoordHomeomorph, coe_mul, Prod.fst_mul,
    Prod.snd_mul, div_eq_mul_inv]
  group

/-- A subgroup `H ≤ G × G` containing the diagonal is closed if and only if its Goursat kernel
`H.goursatFst` is closed in `G`. -/
theorem isClosed_iff_isClosed_goursatFst {H : Subgroup (G × G)}
    (hH : (MonoidHom.id G).graph ≤ H) :
    IsClosed (H : Set (G × G)) ↔ IsClosed (H.goursatFst : Set G) := by
  constructor
  · intro hclosed
    have hemb : Continuous fun g : G => ((g, (1 : G)) : G × G) :=
      continuous_id.prodMk continuous_const
    have hpre : (fun g : G => (g, (1 : G))) ⁻¹' (H : Set (G × G)) = (H.goursatFst : Set G) := by
      ext g
      exact mem_goursatFst.symm
    exact hpre ▸ hclosed.preimage hemb
  · intro hclosed
    have hpre : (fun p : G × G => p.1 / p.2) ⁻¹' (H.goursatFst : Set G) =
        (H : Set (G × G)) := by
      ext p
      exact (mem_iff_div_mem_goursatFst hH).symm
    exact hpre ▸ hclosed.preimage (continuous_fst.div' continuous_snd)

/-- When `G` is preconnected, `H` is preconnected if and only if `H.goursatFst` is preconnected. -/
theorem isPreconnected_iff_isPreconnected_goursatFst [PreconnectedSpace G] {H : Subgroup (G × G)}
    (hH : (MonoidHom.id G).graph ≤ H) :
    IsPreconnected (H : Set (G × G)) ↔ IsPreconnected (H.goursatFst : Set G) := by
  constructor
  · intro hpre
    have himg : (fun p : G × G => p.1 / p.2) '' (H : Set (G × G)) = (H.goursatFst : Set G) := by
      ext a
      exact ⟨fun ⟨p, hp, hpa⟩ => hpa ▸ (mem_iff_div_mem_goursatFst hH).mp hp,
        fun ha => ⟨(a, 1), mem_goursatFst.mp ha, div_one a⟩⟩
    exact himg ▸ hpre.image _ (continuous_fst.div' continuous_snd).continuousOn
  · intro hpre
    have himg : (fun q : G × G => (q.1 * q.2, q.2)) '' ((H.goursatFst : Set G) ×ˢ Set.univ) =
        (H : Set (G × G)) := by
      ext p
      constructor
      · rintro ⟨⟨a, h⟩, ⟨ha, -⟩, rfl⟩
        exact (mem_iff_div_mem_goursatFst hH).mpr (by simpa [mul_div_cancel_right] using ha)
      · intro hp
        exact ⟨(p.1 / p.2, p.2), ⟨(mem_iff_div_mem_goursatFst hH).mp hp, trivial⟩,
          Prod.ext (div_mul_cancel p.1 p.2) rfl⟩
    exact himg ▸ (hpre.prod isPreconnected_univ).image _
      ((continuous_fst.mul continuous_snd).prodMk continuous_snd).continuousOn

/-- When `G` is path connected, `H` is path connected if and only if `H.goursatFst` is path
connected. -/
theorem pathConnectedSpace_iff_pathConnectedSpace_goursatFst [PathConnectedSpace G]
    {H : Subgroup (G × G)} (hH : (MonoidHom.id G).graph ≤ H) :
    PathConnectedSpace H ↔ PathConnectedSpace H.goursatFst := by
  constructor
  · intro _
    exact Function.Surjective.pathConnectedSpace
      (f := fun p : H => (goursatCoordHomeomorph hH p).1)
      (fun a => ⟨(goursatCoordHomeomorph hH).symm (a, 1), by simp⟩)
      (continuous_fst.comp (goursatCoordHomeomorph hH).continuous)
  · intro _
    exact Function.Surjective.pathConnectedSpace
      (goursatCoordHomeomorph hH).symm.surjective
      (goursatCoordHomeomorph hH).symm.continuous

end Subgroup
