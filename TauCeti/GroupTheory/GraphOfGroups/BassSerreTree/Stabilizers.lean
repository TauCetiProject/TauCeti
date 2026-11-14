/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Component
public import TauCeti.GroupTheory.GraphOfGroups.BassSerreTree.Basic

/-!
# Stabilizers, quotient graph and local stars of the Bass–Serre tree

For a graph of groups `𝔸` over `Γ` and a base vertex `v₀`, this file identifies the vertex and
dart stabilizers of the Bass–Serre tree `𝔸.bassSerreTree v₀`, its quotient graph under `π₁(𝔸, v₀)`,
the stars of its vertices, and its degeneration over an edgeless graph.

* The stabilizer in `π₁(𝔸, v₀)` of `vertexMk p` (`p A_v`) is `(π₁.vertexHom p).range`, the
  conjugate `p A_v p⁻¹` of `A_v` along `p` (`stabilizer_vertex`). In particular every conjugated
  vertex group is elliptic (`isEllipticSubgroup_range_vertexHom`).
* The stabilizer of `dartMk e p` is `((π₁.vertexHom p).comp (𝔸.α e)).range`, i.e.
  `p α_e(A_e) p⁻¹` (`stabilizer_edge`), and for `dartMk e (p.comp (Path.ofVertex a))` it is
  `p a α_e(A_e) a⁻¹ p⁻¹` (`stabilizer_edge_comp_ofVertex`).
* The quotient graph `(𝔸.bassSerreTree v₀).quotient` is canonically isomorphic to the connected
  component `Γ.component v₀` of `v₀` in `Γ` (`quotientBassSerreTreeIso`), and hence to `Γ` itself
  when `Γ` is preconnected (`quotientBassSerreTreeIsoOfPreconnected`); see also
  `quotient_bassSerreTree`.
* The star of `vertexMk p` at a vertex `v` is in bijection with
  `Σ e : {e : Γ.E // Γ.src e = v}, 𝔸.vertexGroup (Γ.src e.1) ⧸ (𝔸.α e.1).range` (`starEquiv`).
* Over a graph without darts, `𝔸.bassSerreTree v₀` has a single vertex, no darts, trivial action,
  and underlying graph isomorphic to `GTree.point` (`bassSerreTreePointIso`, `bassSerreTree_point`).

## Main declarations

* `TauCeti.GraphOfGroups.stabilizer_vertex`: `Stab(p A_v) = (π₁.vertexHom p).range`.
* `TauCeti.GraphOfGroups.stabilizer_edge`:
  `Stab(dartMk e p) = ((π₁.vertexHom p).comp (𝔸.α e)).range`.
* `TauCeti.GraphOfGroups.quotientBassSerreTreeIso`,
  `TauCeti.GraphOfGroups.quotientBassSerreTreeIsoOfPreconnected`,
  `TauCeti.GraphOfGroups.quotient_bassSerreTree`: isomorphism of `(𝔸.bassSerreTree v₀).quotient`
  with `Γ.component v₀` (and with `Γ` when `Γ` is preconnected).
* `TauCeti.GraphOfGroups.starEquiv`: coset parametrization of the star of `vertexMk p`.
* `TauCeti.GraphOfGroups.bassSerreTreePointIso`, `TauCeti.GraphOfGroups.bassSerreTree_point`: over
  an edgeless graph, `𝔸.bassSerreTree v₀` is a one-vertex tree with trivial action.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12.
* I. Kapovich, R. Weidmann and A. Myasnikov, *Foldings, graphs of groups and the membership
  problem*, Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5.
-/

public section

universe u v w x

namespace TauCeti

namespace GraphOfGroups

/-! ### Vertex and dart stabilizers -/

section Stabilizers

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}

/-- The stabilizer in `π₁(𝔸, v₀)` of the vertex `p A_v` is `p A_v p⁻¹`, the image of
`π₁.vertexHom p : A_v →* π₁(𝔸, v₀)`. -/
theorem stabilizer_vertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    MulAction.stabilizer (π₁ 𝔸 v₀) (vertexMk p) = (π₁.vertexHom p).range := by
  ext g
  refine π₁.induction_on g fun s => ?_
  rw [MulAction.mem_stabilizer_iff, mk_smul_vertexMk, vertexMk_eq_vertexMk_iff,
    MonoidHom.mem_range]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [π₁.vertexHom_apply, π₁.mk_eq_mk_iff]
    have h₁ := ha.comp_right p.reverse
    rw [Quiver.Path.comp_assoc s p p.reverse] at h₁
    exact h₁.symm.trans ((Path.Homotopic.comp_reverse p).comp_left s)
  · rintro ⟨a, ha⟩
    rw [π₁.vertexHom_apply, π₁.mk_eq_mk_iff] at ha
    exact ⟨a, (ha.symm.comp_right p).trans
      (Path.Homotopic.comp_reverse_comp_comp (p.comp (Path.ofVertex a)) p .nil)⟩

/-- The stabilizer of `baseVertex 𝔸 v₀` is the image of `A_{v₀}` in `π₁(𝔸, v₀)`. -/
@[simp] theorem stabilizer_baseVertex :
    MulAction.stabilizer (π₁ 𝔸 v₀) (baseVertex 𝔸 v₀) =
      (π₁.vertexHom (𝔸 := 𝔸) (a := v₀) Quiver.Path.nil).range := by
  rw [baseVertex_def, stabilizer_vertex]

/-- Every conjugated vertex group `(π₁.vertexHom p).range` is elliptic in `bassSerreTree 𝔸 v₀`. -/
theorem isEllipticSubgroup_range_vertexHom {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (bassSerreTree 𝔸 v₀).IsEllipticSubgroup (π₁.vertexHom p).range :=
  GTree.isEllipticSubgroup_iff.mpr ⟨vertexMk p, (stabilizer_vertex p).ge⟩

/-- The stabilizer in `π₁(𝔸, v₀)` of the dart `dartMk e p` is `p α_e(A_e) p⁻¹`, the image of
`(π₁.vertexHom p).comp (𝔸.α e)`. -/
theorem stabilizer_edge (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    MulAction.stabilizer (π₁ 𝔸 v₀) (dartMk e p) = ((π₁.vertexHom p).comp (𝔸.α e)).range := by
  ext g
  refine π₁.induction_on g fun s => ?_
  rw [MulAction.mem_stabilizer_iff, mk_smul_dartMk, dartMk_eq_dartMk_iff, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [MonoidHom.comp_apply, π₁.vertexHom_apply, π₁.mk_eq_mk_iff]
    have h₁ := hc.comp_right p.reverse
    rw [Quiver.Path.comp_assoc s p p.reverse] at h₁
    exact h₁.symm.trans ((Path.Homotopic.comp_reverse p).comp_left s)
  · rintro ⟨c, hc⟩
    rw [MonoidHom.comp_apply, π₁.vertexHom_apply, π₁.mk_eq_mk_iff] at hc
    exact ⟨c, (hc.symm.comp_right p).trans
      (Path.Homotopic.comp_reverse_comp_comp (p.comp (Path.ofVertex (𝔸.α e c))) p .nil)⟩

private theorem vertexHom_cons_vertex_apply {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (a x : 𝔸.vertexGroup v) :
    π₁.vertexHom (p.cons (Letter.vertex a)) x = π₁.vertexHom p (a * x * a⁻¹) := by
  rw [← Path.comp_ofVertex]
  simp only [π₁.vertexHom_apply, Quiver.Path.reverse_comp, Path.reverse_ofVertex, π₁.mk_eq_mk_iff]
  have hax : Path.Homotopic ((p.comp (Path.ofVertex a)).comp (Path.ofVertex x))
      (p.comp (Path.ofVertex (a * x))) := by
    simpa [Path.comp_ofVertex] using Path.Homotopic.mul p a x
  have haxa : Path.Homotopic ((p.comp (Path.ofVertex (a * x))).comp (Path.ofVertex a⁻¹))
      (p.comp (Path.ofVertex (a * x * a⁻¹))) := by
    simpa [Path.comp_ofVertex] using Path.Homotopic.mul p (a * x) a⁻¹
  have h₁ : Path.Homotopic (((p.comp (Path.ofVertex a)).comp (Path.ofVertex x)).comp
      ((Path.ofVertex a⁻¹).comp p.reverse))
      (((p.comp (Path.ofVertex (a * x))).comp (Path.ofVertex a⁻¹)).comp p.reverse) := by
    rw [← Quiver.Path.comp_assoc ((p.comp (Path.ofVertex a)).comp (Path.ofVertex x))]
    exact (hax.comp_right (Path.ofVertex a⁻¹)).comp_right p.reverse
  exact h₁.trans (haxa.comp_right p.reverse)

/-- For `a ∈ A_{src e}`, the stabilizer of `dartMk e (p.comp (Path.ofVertex a))` (joining
`p A_{src e}` to `p a e A_{tgt e}`) is `p a α_e(A_e) a⁻¹ p⁻¹`. -/
theorem stabilizer_edge_comp_ofVertex (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (a : 𝔸.vertexGroup (Γ.src e)) :
    MulAction.stabilizer (π₁ 𝔸 v₀) (dartMk e (p.comp (Path.ofVertex a))) =
      (((π₁.vertexHom p).comp (𝔸.α e)).range).map
        (MulAut.conj (π₁.vertexHom p a) : π₁ 𝔸 v₀ →* π₁ 𝔸 v₀) := by
  rw [stabilizer_edge, MonoidHom.map_range]
  congr 1
  ext c
  simp [vertexHom_cons_vertex_apply, MulAut.conj_apply]

/-- If `A_v` is trivial, the vertex `vertexMk p` has trivial stabilizer. -/
theorem stabilizer_vertex_eq_bot {v : Γ.V} [Subsingleton (𝔸.vertexGroup v)]
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    MulAction.stabilizer (π₁ 𝔸 v₀) (vertexMk p) = ⊥ := by
  rw [stabilizer_vertex, eq_bot_iff]
  rintro _ ⟨a, rfl⟩
  rw [Subsingleton.elim a 1, map_one]
  exact Subgroup.one_mem ⊥

/-- If `A_e` is trivial, the dart `dartMk e p` has trivial stabilizer. -/
theorem stabilizer_edge_eq_bot (e : Γ.E) [Subsingleton (𝔸.edgeGroup (Γ.toGeomEdge e))]
    (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    MulAction.stabilizer (π₁ 𝔸 v₀) (dartMk e p) = ⊥ := by
  rw [stabilizer_edge, eq_bot_iff]
  rintro _ ⟨c, rfl⟩
  rw [Subsingleton.elim c 1, map_one]
  exact Subgroup.one_mem ⊥

end Stabilizers

/-! ### Quotient graph of the Bass–Serre tree -/

section Quotient

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

/-- Projection of `bassSerreTree 𝔸 v₀` onto the connected component `Γ.component v₀` of `v₀`:
every `𝔸`-path from `v₀` to `v` has an underlying `Γ`-path `p.edgePath` witnessing reachability. -/
def bassSerreToComponent : (bassSerreTree 𝔸 v₀).toSerreGraph.Hom (Γ.component v₀) where
  mapV x := ⟨(bassSerreProj 𝔸 v₀).mapV x,
    vertex_induction_on x fun p => by simpa using ⟨p.edgePath⟩⟩
  mapE y := ⟨(bassSerreProj 𝔸 v₀).mapE y,
    dart_induction_on y fun _ p => by simpa using ⟨p.edgePath⟩⟩
  map_src y := Subtype.ext ((bassSerreProj 𝔸 v₀).map_src y)
  map_rev y := Subtype.ext ((bassSerreProj 𝔸 v₀).map_rev y)

@[simp] theorem bassSerreToComponent_mapV_vertexMk {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (bassSerreToComponent 𝔸 v₀).mapV (vertexMk p) =
      ⟨v, (Γ.mem_componentVertices_iff v₀).mpr ⟨p.edgePath⟩⟩ :=
  Subtype.ext (bassSerreProj_mapV_vertexMk p)

@[simp] theorem bassSerreToComponent_mapE_dartMk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (bassSerreToComponent 𝔸 v₀).mapE (dartMk e p) =
      ⟨e, (Γ.mem_componentDarts_iff v₀).mpr ⟨p.edgePath⟩⟩ :=
  Subtype.ext (bassSerreProj_mapE_dartMk e p)

@[simp] theorem componentInclusion_comp_bassSerreToComponent :
    SerreGraph.Hom.comp (Γ.componentInclusion v₀) (bassSerreToComponent 𝔸 v₀) =
      bassSerreProj 𝔸 v₀ := by
  ext <;> (simp [bassSerreToComponent]; rfl)

@[simp] theorem bassSerreToComponent_comp_action (g : π₁ 𝔸 v₀) :
    SerreGraph.Hom.comp (bassSerreToComponent 𝔸 v₀) ((bassSerreTree 𝔸 v₀).action g).toHom =
      bassSerreToComponent 𝔸 v₀ := by
  have hproj := bassSerreProj_comp_action 𝔸 v₀ g
  refine SerreGraph.Hom.ext _ (funext fun x => Subtype.ext ?_) (funext fun y => Subtype.ext ?_)
  · have hV := congrArg (fun f : (bassSerreTree 𝔸 v₀).toSerreGraph.Hom Γ => f.mapV x) hproj
    rw [SerreGraph.Hom.comp_mapV, Function.comp_apply] at hV ⊢
    exact hV
  · have hE := congrArg (fun f : (bassSerreTree 𝔸 v₀).toSerreGraph.Hom Γ => f.mapE y) hproj
    rw [SerreGraph.Hom.comp_mapE, Function.comp_apply] at hE ⊢
    exact hE

private def quotientHomToComponent :
    (bassSerreTree 𝔸 v₀).quotient.Hom (Γ.component v₀) :=
  SerreGraph.quotientLift (bassSerreTree 𝔸 v₀).smul_ne_rev (bassSerreToComponent 𝔸 v₀)
    (bassSerreToComponent_comp_action 𝔸 v₀)

private theorem quotientHomToComponent_mapV_bijective :
    Function.Bijective (quotientHomToComponent 𝔸 v₀).mapV := by
  constructor
  · intro a b h
    obtain ⟨x, rfl⟩ := (bassSerreTree 𝔸 v₀).quotientMap_mapV_surjective a
    obtain ⟨y, rfl⟩ := (bassSerreTree 𝔸 v₀).quotientMap_mapV_surjective b
    refine vertex_induction_on x (fun {v₁} p₁ h => ?_) h
    refine vertex_induction_on y (fun {v₂} p₂ h => ?_) h
    have hv : v₁ = v₂ := by
      simpa [quotientHomToComponent] using congrArg Subtype.val h
    subst hv
    exact GTree.quotientMap_mapV_eq_iff.mpr ⟨π₁.mk (p₂.comp p₁.reverse), by
      rw [mk_smul_vertexMk]
      exact vertexMk_congr (Path.Homotopic.comp_reverse_comp_comp p₂ p₁ .nil)⟩
  · rintro ⟨v, hv⟩
    obtain ⟨q⟩ := (Γ.mem_componentVertices_iff v₀).mp hv
    refine ⟨(bassSerreTree 𝔸 v₀).quotientMap.mapV (vertexMk ((dartPrefunctor 𝔸).mapPath q)), ?_⟩
    exact Subtype.ext (by simp [quotientHomToComponent])

private theorem quotientHomToComponent_mapE_bijective :
    Function.Bijective (quotientHomToComponent 𝔸 v₀).mapE := by
  constructor
  · intro a b h
    obtain ⟨x, rfl⟩ := (bassSerreTree 𝔸 v₀).quotientMap_mapE_surjective a
    obtain ⟨y, rfl⟩ := (bassSerreTree 𝔸 v₀).quotientMap_mapE_surjective b
    refine dart_induction_on x (fun e₁ p₁ h => ?_) h
    refine dart_induction_on y (fun e₂ p₂ h => ?_) h
    have he : e₁ = e₂ := by
      simpa [quotientHomToComponent] using congrArg Subtype.val h
    subst he
    exact GTree.quotientMap_mapE_eq_iff.mpr ⟨π₁.mk (p₂.comp p₁.reverse), by
      rw [mk_smul_dartMk]
      exact dartMk_congr e₁ (Path.Homotopic.comp_reverse_comp_comp p₂ p₁ .nil)⟩
  · rintro ⟨e, he⟩
    obtain ⟨q⟩ := (Γ.mem_componentDarts_iff v₀).mp he
    refine ⟨(bassSerreTree 𝔸 v₀).quotientMap.mapE (dartMk e ((dartPrefunctor 𝔸).mapPath q)), ?_⟩
    exact Subtype.ext (by simp [quotientHomToComponent])

/-- The quotient graph `(bassSerreTree 𝔸 v₀).quotient` is canonically isomorphic to the connected
component `Γ.component v₀` of `v₀` in `Γ`. -/
noncomputable def quotientBassSerreTreeIso :
    (bassSerreTree 𝔸 v₀).quotient.Iso (Γ.component v₀) :=
  (quotientHomToComponent 𝔸 v₀).toIso (quotientHomToComponent_mapV_bijective 𝔸 v₀)
    (quotientHomToComponent_mapE_bijective 𝔸 v₀)

@[simp] theorem quotientBassSerreTreeIso_equivV_mk {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (quotientBassSerreTreeIso 𝔸 v₀).equivV
      ((bassSerreTree 𝔸 v₀).quotientMap.mapV (vertexMk p)) =
      ⟨v, (Γ.mem_componentVertices_iff v₀).mpr ⟨p.edgePath⟩⟩ := by
  apply Subtype.ext
  simp [quotientBassSerreTreeIso, quotientHomToComponent]

@[simp] theorem quotientBassSerreTreeIso_equivE_mk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (quotientBassSerreTreeIso 𝔸 v₀).equivE
      ((bassSerreTree 𝔸 v₀).quotientMap.mapE (dartMk e p)) =
      ⟨e, (Γ.mem_componentDarts_iff v₀).mpr ⟨p.edgePath⟩⟩ := by
  apply Subtype.ext
  simp [quotientBassSerreTreeIso, quotientHomToComponent]

/-- When `Γ` is preconnected, the quotient graph `(bassSerreTree 𝔸 v₀).quotient` is canonically
isomorphic to `Γ`. -/
noncomputable def quotientBassSerreTreeIsoOfPreconnected (hΓ : Γ.Preconnected) :
    (bassSerreTree 𝔸 v₀).quotient.Iso Γ :=
  (quotientBassSerreTreeIso 𝔸 v₀).trans (Γ.componentIsoOfPreconnected v₀ hΓ)

@[simp] theorem quotientBassSerreTreeIsoOfPreconnected_equivV_mk (hΓ : Γ.Preconnected) {v : Γ.V}
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (quotientBassSerreTreeIsoOfPreconnected 𝔸 v₀ hΓ).equivV
      ((bassSerreTree 𝔸 v₀).quotientMap.mapV (vertexMk p)) = v := by
  simp [quotientBassSerreTreeIsoOfPreconnected]
  rfl

@[simp] theorem quotientBassSerreTreeIsoOfPreconnected_equivE_mk (hΓ : Γ.Preconnected) (e : Γ.E)
    (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (quotientBassSerreTreeIsoOfPreconnected 𝔸 v₀ hΓ).equivE
      ((bassSerreTree 𝔸 v₀).quotientMap.mapE (dartMk e p)) = e := by
  simp [quotientBassSerreTreeIsoOfPreconnected]
  rfl

/-- The quotient graph `(bassSerreTree 𝔸 v₀).quotient` is isomorphic to the connected component
`Γ.component v₀` of `v₀`, and hence to `Γ` itself when `Γ` is preconnected. -/
theorem quotient_bassSerreTree :
    Nonempty ((bassSerreTree 𝔸 v₀).quotient.Iso (Γ.component v₀)) ∧
      (Γ.Preconnected → Nonempty ((bassSerreTree 𝔸 v₀).quotient.Iso Γ)) :=
  ⟨⟨quotientBassSerreTreeIso 𝔸 v₀⟩, fun hΓ => ⟨quotientBassSerreTreeIsoOfPreconnected 𝔸 v₀ hΓ⟩⟩

end Quotient

/-! ### Local stars of vertices -/

section Star

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}

private def starOfCoset {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (Σ e : {e : Γ.E // Γ.src e = v}, 𝔸.vertexGroup (Γ.src e.1) ⧸ (𝔸.α e.1).range) →
      {y : (bassSerreTree 𝔸 v₀).E // (bassSerreTree 𝔸 v₀).src y = vertexMk p}
  | ⟨⟨e, he⟩, q⟩ =>
    Quotient.liftOn' q
      (fun a =>
        ⟨dartMk e ((p.cast rfl (congrArg LetterVertex.mk he.symm)).comp (Path.ofVertex a)),
          by cases he; simp⟩)
      fun a₁ a₂ h => by
        obtain ⟨c, hc⟩ := QuotientGroup.leftRel_apply.mp h
        have ha : a₂ = a₁ * 𝔸.α e c := inv_mul_eq_iff_eq_mul.mp hc.symm
        subst ha
        apply Subtype.ext
        have hmul : Path.Homotopic
            ((p.cast rfl (congrArg LetterVertex.mk he.symm)).comp
              (Path.ofVertex (a₁ * 𝔸.α e c)))
            (((p.cast rfl (congrArg LetterVertex.mk he.symm)).comp
              (Path.ofVertex a₁)).comp (Path.ofVertex (𝔸.α e c))) := by
          simpa [Path.comp_ofVertex] using
            (Path.Homotopic.mul (p.cast rfl (congrArg LetterVertex.mk he.symm)) a₁ (𝔸.α e c)).symm
        exact (dartMk_comp_ofVertex_α e _ c).symm.trans (dartMk_congr e hmul.symm)

private theorem starOfCoset_bijective {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    Function.Bijective (starOfCoset p) := by
  constructor
  · rintro ⟨⟨e₁, he₁⟩, q₁⟩ ⟨⟨e₂, he₂⟩, q₂⟩ h
    refine Quotient.inductionOn₂' q₁ q₂ (fun a₁ a₂ h => ?_) h
    have hd : dartMk e₁ ((p.cast rfl (congrArg LetterVertex.mk he₁.symm)).comp
        (Path.ofVertex a₁)) =
      dartMk e₂ ((p.cast rfl (congrArg LetterVertex.mk he₂.symm)).comp
        (Path.ofVertex a₂)) := congrArg Subtype.val h
    have he : e₁ = e₂ := eq_of_dartMk_eq_dartMk hd
    subst he
    subst he₁
    cases he₂
    rw [Quiver.Path.cast_rfl_rfl] at hd
    obtain ⟨c, hc⟩ := dartMk_eq_dartMk_iff.mp hd
    have hmul : Path.Homotopic (p.comp (Path.ofVertex a₁))
        (p.comp (Path.ofVertex (a₂ * 𝔸.α e₁ c))) :=
      hc.trans (by simpa [Path.comp_ofVertex] using Path.Homotopic.mul p a₂ (𝔸.α e₁ c))
    have ha : a₁ = a₂ * 𝔸.α e₁ c :=
      Path.ofVertex_homotopic_ofVertex_iff.mp (Path.Homotopic.comp_left_iff.mp hmul)
    refine Sigma.ext rfl (heq_of_eq (QuotientGroup.eq.mpr ⟨c⁻¹, ?_⟩))
    rw [ha, map_inv, mul_inv_rev, inv_mul_cancel_right]
  · rintro ⟨y, hy⟩
    refine dart_induction_on y (fun e q hy => ?_) hy
    rw [src_dartMk] at hy
    have he : Γ.src e = v := eq_of_vertexMk_eq_vertexMk hy
    subst he
    obtain ⟨a, ha⟩ := vertexMk_eq_vertexMk_iff.mp hy
    refine ⟨⟨⟨e, rfl⟩, a⟩, Subtype.ext ?_⟩
    simpa [starOfCoset] using dartMk_congr e ha.symm

/-- The darts of `bassSerreTree 𝔸 v₀` issuing from `vertexMk p` (`v : Γ.V`) are in canonical
bijection with pairs of a dart `e` of `Γ` with `src e = v` and a left coset in
`A_v ⧸ α_e(A_e)`. -/
noncomputable def starEquiv {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    {y : (bassSerreTree 𝔸 v₀).E // (bassSerreTree 𝔸 v₀).src y = vertexMk p} ≃
      Σ e : {e : Γ.E // Γ.src e = v}, 𝔸.vertexGroup (Γ.src e.1) ⧸ (𝔸.α e.1).range :=
  (Equiv.ofBijective (starOfCoset p) (starOfCoset_bijective p)).symm

@[simp] theorem starEquiv_symm_mk {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (e : {e : Γ.E // Γ.src e = v}) (a : 𝔸.vertexGroup (Γ.src e.1)) :
    (starEquiv p).symm ⟨e, a⟩ =
      ⟨dartMk e.1 ((p.cast rfl (congrArg LetterVertex.mk e.2.symm)).comp (Path.ofVertex a)),
        by rcases e with ⟨_, rfl⟩; simp⟩ := (rfl)

@[simp] theorem starEquiv_dartMk_cons (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (a : 𝔸.vertexGroup (Γ.src e)) :
    starEquiv p ⟨dartMk e (p.cons (Letter.vertex a)), by simp⟩ = ⟨⟨e, rfl⟩, a⟩ := by
  refine ((starEquiv p).eq_symm_apply).mp (Subtype.ext ?_)
  rw [starEquiv_symm_mk]
  simp

theorem starEquiv_dartMk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (a : 𝔸.vertexGroup (Γ.src e)) :
    starEquiv p ⟨dartMk e (p.comp (Path.ofVertex a)), by simp⟩ = ⟨⟨e, rfl⟩, a⟩ := by
  simp

end Star

/-! ### Edgeless graphs of groups -/

section Edgeless

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) [IsEmpty Γ.E]

instance : IsEmpty (bassSerreTree 𝔸 v₀).E :=
  ⟨fun y => dart_induction_on y fun e _ => isEmptyElim e⟩

instance : Unique (bassSerreTree 𝔸 v₀).V where
  default := baseVertex 𝔸 v₀
  uniq x := (bassSerreTree 𝔸 v₀).subsingleton_of_isEmpty_dart.elim x (baseVertex 𝔸 v₀)

/-- Over an edgeless graph, `π₁(𝔸, v₀)` acts trivially on `bassSerreTree 𝔸 v₀`. -/
@[simp] theorem bassSerreTree_action_eq_one_of_isEmpty :
    (bassSerreTree 𝔸 v₀).action = 1 := by
  ext g : 1
  exact SerreGraph.Iso.ext (fun x => Subsingleton.elim _ _) (fun y => isEmptyElim y)

/-- Over an edgeless graph (in particular a one-vertex graph without edges), the Bass–Serre tree
`bassSerreTree 𝔸 v₀` is isomorphic as a Serre graph to the one-vertex tree `GTree.point`. -/
noncomputable def bassSerreTreePointIso :
    (bassSerreTree 𝔸 v₀).toSerreGraph.Iso
      (GTree.point.{max u v w, max u v w} (π₁ 𝔸 v₀)).toSerreGraph where
  equivV := @Equiv.ofUnique _ _ inferInstance
    (@Unique.mk' _ ⟨Classical.choice inferInstance⟩ inferInstance)
  equivE := @Equiv.equivOfIsEmpty _ _ inferInstance
    (GTree.point.{max u v w, max u v w} (π₁ 𝔸 v₀)).isEmpty_dart_of_subsingleton
  map_src y := isEmptyElim y
  map_rev y := isEmptyElim y

@[simp] theorem bassSerreTreePointIso_equivV_smul (g : π₁ 𝔸 v₀) (x : (bassSerreTree 𝔸 v₀).V) :
    (bassSerreTreePointIso 𝔸 v₀).equivV (g • x) = g • (bassSerreTreePointIso 𝔸 v₀).equivV x :=
  Subsingleton.elim _ _

/-- Over an edgeless graph, `bassSerreTree 𝔸 v₀` is isomorphic to `GTree.point` and carries the
trivial action of `π₁(𝔸, v₀)`. -/
theorem bassSerreTree_point :
    Nonempty ((bassSerreTree 𝔸 v₀).toSerreGraph.Iso
        (GTree.point.{max u v w, max u v w} (π₁ 𝔸 v₀)).toSerreGraph) ∧
      (bassSerreTree 𝔸 v₀).action = 1 :=
  ⟨⟨bassSerreTreePointIso 𝔸 v₀⟩, bassSerreTree_action_eq_one_of_isEmpty 𝔸 v₀⟩

/-- Over an edgeless graph, `bassSerreTree 𝔸 v₀` lies in the same deformation space as
`GTree.point`. -/
theorem bassSerreTree_sameDeformationSpace_point :
    (bassSerreTree 𝔸 v₀).SameDeformationSpace
      (GTree.point.{max u v w, max u v w} (π₁ 𝔸 v₀)) :=
  GTree.sameDeformationSpace_iff.mpr
    ⟨(bassSerreTree 𝔸 v₀).dominates_point, (GTree.point _).dominates_of_subsingleton⟩

end Edgeless

end GraphOfGroups

end TauCeti
