/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Basic

/-!
# Stabilizers and quotient of the Bass–Serre tree

From the path model of `X(𝔸, v₀)` (`GraphOfGroups.bassSerreTree`), this file reads off the vertex
and edge stabilizers of the `π₁(𝔸, v₀)`-action and identifies the quotient graph
`X(𝔸, v₀) / π₁(𝔸, v₀)`:

* **Vertex stabilizers** (`GraphOfGroups.stabilizer_vertex`): the stabilizer of `p A_v` in
  `π₁(𝔸, v₀)` is `(π₁.vertexHom p).range = p A_v p⁻¹`, isomorphic to `A_v` via
  `GraphOfGroups.vertexStabilizerEquiv`.
* **Edge stabilizers** (`GraphOfGroups.stabilizer_edge`): the stabilizer of `[e, p]` is
  `((𝔸.α e).range).map (π₁.vertexHom p) = p α_e(A_e) p⁻¹`, isomorphic to `A_e` via
  `GraphOfGroups.edgeStabilizerEquiv`; for `[e, p · a]` from `p A_v` to `(p a e) A_{v'}` this is
  `p a α_e(A_e) a⁻¹ p⁻¹`.
* **Quotient graph** (`GraphOfGroups.bassSerreQuotientIso`): the quotient `X(𝔸, v₀) / π₁(𝔸, v₀)`
  is isomorphic to the connected component `Γ.component v₀`, and hence to `Γ` itself when `Γ` is
  preconnected (`GraphOfGroups.bassSerreQuotientIsoOfPreconnected`).

## Main definitions

* `TauCeti.GraphOfGroups.vertexStabilizerEquiv`, `TauCeti.GraphOfGroups.edgeStabilizerEquiv`:
  isomorphisms of `A_v` and `A_e` with the corresponding vertex and dart stabilizers.
* `TauCeti.GraphOfGroups.bassSerreQuotient`: the quotient graph `X(𝔸, v₀) / π₁(𝔸, v₀)`.
* `TauCeti.GraphOfGroups.bassSerreQuotientIso`,
  `TauCeti.GraphOfGroups.bassSerreQuotientIsoOfPreconnected`,
  `TauCeti.GraphOfGroups.bassSerreQuotientIsoOfConnected`: isomorphisms of the quotient graph
  with `Γ.component v₀` and (when `Γ` is preconnected or connected) with `Γ`.

## Main results

* `TauCeti.GraphOfGroups.stabilizer_vertex`, `TauCeti.GraphOfGroups.stabilizer_edge`: explicit
  vertex and dart stabilizers.
* `TauCeti.GraphOfGroups.isEllipticSubgroup_vertexHom_range`: every conjugated vertex group
  `p A_v p⁻¹` is elliptic in `X(𝔸, v₀)`.

## References

* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5, pp. 6–7.
* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12.
-/

public section

universe u v w x

namespace TauCeti

namespace GraphOfGroups

open _root_.MulAction

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

/-! ### Vertex and edge stabilizers -/

section Stabilizers

variable {𝔸 v₀}

private theorem homotopic_comp_iff_homotopic_comp_reverse {v : Γ.V} (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (a : 𝔸.vertexGroup v) :
    Path.Homotopic (s.comp p) (p.cons (Letter.vertex a)) ↔
      Path.Homotopic s ((p.comp (Path.ofVertex a)).comp p.reverse) := by
  rw [← Path.comp_ofVertex]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact (Path.Homotopic.comp_comp_reverse s p).symm.trans (h.comp_right p.reverse)
  · exact (h.comp_right p).trans <| by
      simpa using Path.Homotopic.comp_reverse_comp_comp (p.comp (Path.ofVertex a)) p .nil

/-- The stabilizer in `π₁(𝔸, v₀)` of the vertex `p A_v` of `X(𝔸, v₀)` is `p A_v p⁻¹`, the image of
`π₁.vertexHom p : A_v →* π₁(𝔸, v₀)`. -/
theorem stabilizer_vertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    stabilizer (π₁ 𝔸 v₀) (𝔸.bassSerreVertex v₀ p) = (π₁.vertexHom p).range := by
  ext g
  refine π₁.induction_on g fun s => ?_
  rw [mem_stabilizer_iff, mk_smul_bassSerreVertex, bassSerreVertex_eq_iff, MonoidHom.mem_range]
  refine ⟨fun ⟨a, ha⟩ => ⟨a, ?_⟩, fun ⟨a, ha⟩ => ⟨a, ?_⟩⟩
  · rw [π₁.vertexHom_apply]
    exact (π₁.mk_eq_mk_iff.mpr ((homotopic_comp_iff_homotopic_comp_reverse s p a).mp ha)).symm
  · rw [π₁.vertexHom_apply] at ha
    exact (homotopic_comp_iff_homotopic_comp_reverse s p a).mpr (π₁.mk_eq_mk_iff.mp ha.symm)

/-- At the base vertex `1 · A_{v₀}`, the stabilizer is the image of `A_{v₀}` in `π₁(𝔸, v₀)`. -/
@[simp] theorem stabilizer_bassSerreBaseVertex :
    stabilizer (π₁ 𝔸 v₀) (𝔸.bassSerreBaseVertex v₀) =
      (π₁.vertexHom (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)).range :=
  stabilizer_vertex (𝔸 := 𝔸) (v₀ := v₀) .nil

/-- Because `π₁.vertexHom p` is injective, the vertex group `A_v` is isomorphic to the stabilizer
of `p A_v` in `π₁(𝔸, v₀)`. -/
noncomputable def vertexStabilizerEquiv {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    𝔸.vertexGroup v ≃* stabilizer (π₁ 𝔸 v₀) (𝔸.bassSerreVertex v₀ p) :=
  (MonoidHom.ofInjective (π₁.vertexHom_injective p)).trans
    (MulEquiv.subgroupCongr (stabilizer_vertex p).symm)

@[simp] theorem coe_vertexStabilizerEquiv_apply {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (a : 𝔸.vertexGroup v) : (vertexStabilizerEquiv p a : π₁ 𝔸 v₀) = π₁.vertexHom p a :=
  (rfl)

/-- The stabilizer in `π₁(𝔸, v₀)` of the dart `[e, p]` of `X(𝔸, v₀)` is `p α_e(A_e) p⁻¹`, the
conjugate along `p` of the edge-group image `α_e(A_e)`. For `p = q · a` (the dart between `q A_v`
and `(q a e) A_{v'}`), this is `q a α_e(A_e) a⁻¹ q⁻¹`. -/
theorem stabilizer_edge (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    stabilizer (π₁ 𝔸 v₀) (𝔸.bassSerreDart v₀ e p) = ((𝔸.α e).range).map (π₁.vertexHom p) := by
  ext g
  refine π₁.induction_on g fun s => ?_
  rw [mem_stabilizer_iff, mk_smul_bassSerreDart, bassSerreDart_eq_iff, ← MonoidHom.range_comp,
    MonoidHom.mem_range]
  refine ⟨fun ⟨c, hc⟩ => ⟨c, ?_⟩, fun ⟨c, hc⟩ => ⟨c, ?_⟩⟩
  · rw [MonoidHom.comp_apply, π₁.vertexHom_apply]
    exact (π₁.mk_eq_mk_iff.mpr
      ((homotopic_comp_iff_homotopic_comp_reverse s p (𝔸.α e c)).mp hc)).symm
  · rw [MonoidHom.comp_apply, π₁.vertexHom_apply] at hc
    exact (homotopic_comp_iff_homotopic_comp_reverse s p (𝔸.α e c)).mpr
      (π₁.mk_eq_mk_iff.mp hc.symm)

/-- Because both `𝔸.α e` and `π₁.vertexHom p` are injective, the edge group `A_e` is isomorphic to
the stabilizer of `[e, p]` in `π₁(𝔸, v₀)`. -/
noncomputable def edgeStabilizerEquiv (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    𝔸.edgeGroup (Γ.toGeomEdge e) ≃* stabilizer (π₁ 𝔸 v₀) (𝔸.bassSerreDart v₀ e p) :=
  (MonoidHom.ofInjective (f := (π₁.vertexHom p).comp (𝔸.α e))
      ((π₁.vertexHom_injective p).comp (𝔸.α_injective e))).trans
    (MulEquiv.subgroupCongr ((MonoidHom.range_comp (π₁.vertexHom p) (𝔸.α e)).trans
      (stabilizer_edge e p).symm))

@[simp] theorem coe_edgeStabilizerEquiv_apply (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    (edgeStabilizerEquiv e p c : π₁ 𝔸 v₀) = π₁.vertexHom p (𝔸.α e c) :=
  (rfl)

/-- Every conjugated vertex group `p A_v p⁻¹` is elliptic in the Bass–Serre tree `X(𝔸, v₀)`. -/
theorem isEllipticSubgroup_vertexHom_range {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (𝔸.bassSerreTree v₀).IsEllipticSubgroup (π₁.vertexHom p).range :=
  stabilizer_vertex p ▸ (𝔸.bassSerreTree v₀).isEllipticSubgroup_stabilizer _

end Stabilizers

/-! ### The quotient graph `X(𝔸, v₀) / π₁(𝔸, v₀)` -/

/-- The quotient Serre graph `X(𝔸, v₀) / π₁(𝔸, v₀)`. -/
abbrev bassSerreQuotient : SerreGraph.{max u v w, max u v w} :=
  (𝔸.bassSerreTree v₀).quotient

/-- The morphism from `X(𝔸, v₀) / π₁(𝔸, v₀)` to `Γ.component v₀` induced by the invariant
component projection. -/
def bassSerreQuotientToComponent : (𝔸.bassSerreQuotient v₀).Hom (Γ.component v₀) :=
  SerreGraph.quotientLift (𝔸.bassSerreTree v₀).smul_ne_rev (𝔸.bassSerreComponentHom v₀)
    (𝔸.bassSerreComponentHom_comp_action v₀)

@[simp] theorem bassSerreQuotientToComponent_mapV_quotientMap (u : (𝔸.bassSerreTree v₀).V) :
    (𝔸.bassSerreQuotientToComponent v₀).mapV ((𝔸.bassSerreTree v₀).quotientMap.mapV u) =
      (𝔸.bassSerreComponentHom v₀).mapV u :=
  SerreGraph.quotientLift_mapV_quotientMap _ _ u

@[simp] theorem bassSerreQuotientToComponent_mapE_quotientMap (d : (𝔸.bassSerreTree v₀).E) :
    (𝔸.bassSerreQuotientToComponent v₀).mapE ((𝔸.bassSerreTree v₀).quotientMap.mapE d) =
      (𝔸.bassSerreComponentHom v₀).mapE d :=
  SerreGraph.quotientLift_mapE_quotientMap _ _ d

private theorem bassSerreQuotientToComponent_mapV_bijective :
    Function.Bijective (𝔸.bassSerreQuotientToComponent v₀).mapV := by
  refine ⟨fun x y => ?_, fun ⟨v, hv⟩ => ?_⟩
  · obtain ⟨u₁, rfl⟩ := (𝔸.bassSerreTree v₀).quotientMap_mapV_surjective x
    obtain ⟨u₂, rfl⟩ := (𝔸.bassSerreTree v₀).quotientMap_mapV_surjective y
    rw [bassSerreQuotientToComponent_mapV_quotientMap,
      bassSerreQuotientToComponent_mapV_quotientMap]
    refine bassSerreVertex_induction u₁ fun {v₁} p₁ =>
      bassSerreVertex_induction u₂ fun {v₂} p₂ => fun h => ?_
    have hv_eq : v₁ = v₂ := by simpa using congrArg Subtype.val h
    subst hv_eq
    refine GTree.quotientMap_mapV_eq_iff.mpr ⟨π₁.mk (p₂.comp p₁.reverse), ?_⟩
    rw [mk_smul_bassSerreVertex]
    exact bassSerreVertex_congr (by simpa using Path.Homotopic.comp_reverse_comp_comp p₂ p₁ .nil)
  · obtain ⟨P⟩ := (Γ.mem_componentVertices_iff v₀ v).mp hv
    refine ⟨(𝔸.bassSerreTree v₀).quotientMap.mapV
      (𝔸.bassSerreVertex v₀ ((dartPrefunctor 𝔸).mapPath P)), Subtype.ext ?_⟩
    rw [bassSerreQuotientToComponent_mapV_quotientMap, bassSerreComponentHom_mapV]

private theorem bassSerreQuotientToComponent_mapE_bijective :
    Function.Bijective (𝔸.bassSerreQuotientToComponent v₀).mapE := by
  refine ⟨fun x y => ?_, fun ⟨e, he⟩ => ?_⟩
  · obtain ⟨d₁, rfl⟩ := (𝔸.bassSerreTree v₀).quotientMap_mapE_surjective x
    obtain ⟨d₂, rfl⟩ := (𝔸.bassSerreTree v₀).quotientMap_mapE_surjective y
    rw [bassSerreQuotientToComponent_mapE_quotientMap,
      bassSerreQuotientToComponent_mapE_quotientMap]
    refine bassSerreDart_induction d₁ fun e₁ p₁ =>
      bassSerreDart_induction d₂ fun e₂ p₂ => fun h => ?_
    have he_eq : e₁ = e₂ := by simpa using congrArg Subtype.val h
    subst he_eq
    refine GTree.quotientMap_mapE_eq_iff.mpr ⟨π₁.mk (p₂.comp p₁.reverse), ?_⟩
    rw [mk_smul_bassSerreDart]
    exact bassSerreDart_congr (by simpa using Path.Homotopic.comp_reverse_comp_comp p₂ p₁ .nil)
  · obtain ⟨P⟩ := (Γ.mem_componentDarts_iff v₀ e).mp he
    refine ⟨(𝔸.bassSerreTree v₀).quotientMap.mapE
      (𝔸.bassSerreDart v₀ e ((dartPrefunctor 𝔸).mapPath P)), Subtype.ext ?_⟩
    rw [bassSerreQuotientToComponent_mapE_quotientMap, bassSerreComponentHom_mapE]

/-- The quotient of the Bass–Serre tree `X(𝔸, v₀)` by `π₁(𝔸, v₀)` is isomorphic to the connected
component `Γ.component v₀` of the base vertex in `Γ`. -/
noncomputable def bassSerreQuotientIso : (𝔸.bassSerreQuotient v₀).Iso (Γ.component v₀) :=
  (𝔸.bassSerreQuotientToComponent v₀).toIso (𝔸.bassSerreQuotientToComponent_mapV_bijective v₀)
    (𝔸.bassSerreQuotientToComponent_mapE_bijective v₀)

@[simp] theorem bassSerreQuotientIso_toHom :
    (𝔸.bassSerreQuotientIso v₀).toHom = 𝔸.bassSerreQuotientToComponent v₀ :=
  SerreGraph.Hom.toIso_toHom _ _ _

/-- When the underlying graph `Γ` is preconnected, the quotient `X(𝔸, v₀) / π₁(𝔸, v₀)` is
isomorphic to `Γ` itself. -/
noncomputable def bassSerreQuotientIsoOfPreconnected (hΓ : Γ.Preconnected) :
    (𝔸.bassSerreQuotient v₀).Iso Γ :=
  (𝔸.bassSerreQuotientIso v₀).trans (Γ.componentIsoOfPreconnected hΓ)

/-- When `Γ` is connected, the quotient `X(𝔸, v₀) / π₁(𝔸, v₀)` is isomorphic to `Γ`. -/
noncomputable def bassSerreQuotientIsoOfConnected (hΓ : Γ.Connected) :
    (𝔸.bassSerreQuotient v₀).Iso Γ :=
  𝔸.bassSerreQuotientIsoOfPreconnected v₀ (Γ.connected_iff.mp hΓ).2

end GraphOfGroups

end TauCeti
