/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Quotient
public import TauCeti.GroupTheory.GraphOfGroups.BassSerreTree.Basic

/-!
# Stabilizers, incident darts, and quotient graph of the Bass–Serre tree

For a graph of groups `𝔸` over a Serre graph `Γ` and a base vertex `v₀ : Γ.V`, this file determines
the group-theoretic invariants of the action of `π₁(𝔸, v₀)` on the Bass–Serre tree `X(𝔸, v₀)`:

* The stabilizer in `π₁(𝔸, v₀)` of the vertex `p A_v` (`BassSerreTree.vertexMk p`) is the conjugate
  vertex subgroup `(π₁.vertexHom p).range`, isomorphic to `A_v` via `π₁.vertexHom p`.
* The stabilizer in `π₁(𝔸, v₀)` of the dart `p α_e(A_e)` (`BassSerreTree.dartMk e p`) is
  `((𝔸.α e).range).map (π₁.vertexHom p)`, isomorphic to `A_e` via `(π₁.vertexHom p).comp (𝔸.α e)`.
* Outgoing darts of `X(𝔸, v₀)` at `vertexMk p` projecting to a fixed dart `e : Γ.E` correspond
  bijectively to the left cosets `A_{src e} ⧸ (𝔸.α e).range`, and all outgoing darts at `vertexMk p`
  correspond bijectively to `Σ e : {e : Γ.E // Γ.src e = v}, A_v ⧸ (𝔸.αArrow e).range`.
* The quotient graph `π₁(𝔸, v₀) \ X(𝔸, v₀)` is canonically isomorphic to `Γ.component v₀`, and
  hence to `Γ` itself when `Γ` is preconnected.

## Main definitions

* `TauCeti.GraphOfGroups.stabilizerVertexMulEquiv`: isomorphism `A_v ≃* Stab(p A_v)`.
* `TauCeti.GraphOfGroups.stabilizerEdgeMulEquiv`: isomorphism `A_e ≃* Stab(p α_e(A_e))`.
* `TauCeti.GraphOfGroups.BassSerreTree.incidentDartFiberEquiv` and
  `BassSerreTree.incidentDartEquiv`: coset parameterizations of outgoing darts at a vertex.
* `TauCeti.GraphOfGroups.quotientBassSerreTreeIsoComponent` and
  `TauCeti.GraphOfGroups.quotientBassSerreTreeIso`: identifications of `π₁(𝔸, v₀) \ X(𝔸, v₀)` with
  `Γ.component v₀` and (when `Γ` is preconnected) with `Γ`.

## Main results

* `TauCeti.GraphOfGroups.stabilizer_vertex`: `Stab(p A_v) = (π₁.vertexHom p).range`.
* `TauCeti.GraphOfGroups.stabilizer_edge`:
  `Stab(p α_e(A_e)) = ((𝔸.α e).range).map (π₁.vertexHom p)`.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12, and §5.4.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5.
-/

public section

universe u v w x

namespace TauCeti
namespace GraphOfGroups

/-! ### Vertex and dart stabilizers -/

section Stabilizers

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}

/-- The stabilizer in `π₁(𝔸, v₀)` of the vertex `p A_v` of `X(𝔸, v₀)` is the conjugate vertex
subgroup `(π₁.vertexHom p).range` (`p A_v p⁻¹`). -/
theorem stabilizer_vertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    MulAction.stabilizer (π₁ 𝔸 v₀) (BassSerreTree.vertexMk p) = (π₁.vertexHom p).range := by
  ext g
  refine π₁.induction_on g fun γ => ?_
  rw [MulAction.mem_stabilizer_iff, BassSerreTree.smul_vertexMk,
    BassSerreTree.vertexMk_eq_vertexMk_same_iff, MonoidHom.mem_range]
  refine ⟨fun ⟨a, ha⟩ => ⟨a, ?_⟩, fun ⟨a, ha⟩ => ⟨a, ?_⟩⟩
  · rw [π₁.vertexHom_apply, eq_comm, π₁.mk_eq_mk_iff, Path.comp_ofVertex]
    exact (Path.Homotopic.comp_comp_reverse γ p).symm.trans (ha.comp_right p.reverse)
  · have hγ : γ.Homotopic ((p.comp (Path.ofVertex a)).comp p.reverse) :=
      π₁.mk_eq_mk_iff.mp (ha.symm.trans (π₁.vertexHom_apply p a))
    rw [← Path.comp_ofVertex]
    refine (hγ.comp_right p).trans ?_
    rw [Quiver.Path.comp_assoc]
    simpa only [Quiver.Path.comp_nil] using
      (Path.Homotopic.refl (p.comp (Path.ofVertex a))).comp (Path.Homotopic.reverse_comp p)

/-- At `baseVertex 𝔸 v₀`, the stabilizer in `π₁(𝔸, v₀)` is `(π₁.vertexHom .nil).range`. -/
@[simp] theorem stabilizer_baseVertex :
    MulAction.stabilizer (π₁ 𝔸 v₀) (BassSerreTree.baseVertex 𝔸 v₀) =
      (π₁.vertexHom (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)).range :=
  stabilizer_vertex .nil

/-- The vertex group `A_v` is isomorphic to the stabilizer of `p A_v` in `π₁(𝔸, v₀)` via
`π₁.vertexHom p`. -/
noncomputable def stabilizerVertexMulEquiv {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    𝔸.vertexGroup v ≃* MulAction.stabilizer (π₁ 𝔸 v₀) (BassSerreTree.vertexMk p) :=
  (MonoidHom.ofInjective (π₁.vertexHom_injective p)).trans
    (MulEquiv.subgroupCongr (stabilizer_vertex p).symm)

@[simp] theorem stabilizerVertexMulEquiv_apply_coe {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (a : 𝔸.vertexGroup v) :
    (stabilizerVertexMulEquiv p a : π₁ 𝔸 v₀) = π₁.vertexHom p a :=
  (rfl)

/-- The stabilizer in `π₁(𝔸, v₀)` of the dart `p α_e(A_e)` of `X(𝔸, v₀)` is
`((𝔸.α e).range).map (π₁.vertexHom p)` (`p α_e(A_e) p⁻¹`). -/
theorem stabilizer_edge (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    MulAction.stabilizer (π₁ 𝔸 v₀) (BassSerreTree.dartMk e p) =
      ((𝔸.α e).range).map (π₁.vertexHom p) := by
  rw [← MonoidHom.range_comp]
  ext g
  refine π₁.induction_on g fun γ => ?_
  rw [MulAction.mem_stabilizer_iff, BassSerreTree.smul_dartMk,
    BassSerreTree.dartMk_eq_dartMk_same_iff, MonoidHom.mem_range]
  refine ⟨fun ⟨c, hc⟩ => ⟨c, ?_⟩, fun ⟨c, hc⟩ => ⟨c, ?_⟩⟩
  · rw [MonoidHom.comp_apply, π₁.vertexHom_apply, eq_comm, π₁.mk_eq_mk_iff, Path.comp_ofVertex]
    exact (Path.Homotopic.comp_comp_reverse γ p).symm.trans (hc.comp_right p.reverse)
  · have hγ : γ.Homotopic ((p.comp (Path.ofVertex (𝔸.α e c))).comp p.reverse) :=
      π₁.mk_eq_mk_iff.mp (hc.symm.trans (π₁.vertexHom_apply p (𝔸.α e c)))
    rw [← Path.comp_ofVertex]
    refine (hγ.comp_right p).trans ?_
    rw [Quiver.Path.comp_assoc]
    simpa only [Quiver.Path.comp_nil] using
      (Path.Homotopic.refl (p.comp (Path.ofVertex (𝔸.α e c)))).comp
        (Path.Homotopic.reverse_comp p)

/-- The edge group `A_e` is isomorphic to the stabilizer of `p α_e(A_e)` in `π₁(𝔸, v₀)` via
`(π₁.vertexHom p).comp (𝔸.α e)`. -/
noncomputable def stabilizerEdgeMulEquiv (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    𝔸.edgeGroup (Γ.toGeomEdge e) ≃*
      MulAction.stabilizer (π₁ 𝔸 v₀) (BassSerreTree.dartMk e p) :=
  (MonoidHom.ofInjective (f := (π₁.vertexHom p).comp (𝔸.α e))
      ((π₁.vertexHom_injective p).comp (𝔸.α_injective e))).trans
    (MulEquiv.subgroupCongr ((MonoidHom.range_comp _ _).trans (stabilizer_edge e p).symm))

@[simp] theorem stabilizerEdgeMulEquiv_apply_coe (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    (stabilizerEdgeMulEquiv e p c : π₁ 𝔸 v₀) = π₁.vertexHom p (𝔸.α e c) :=
  (rfl)

/-- Every conjugated vertex subgroup `(π₁.vertexHom p).range` is elliptic in `X(𝔸, v₀)`. -/
theorem isEllipticSubgroup_range_vertexHom {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (𝔸.bassSerreTree v₀).IsEllipticSubgroup (π₁.vertexHom p).range :=
  GTree.isEllipticSubgroup_iff.mpr ⟨BassSerreTree.vertexMk p, (stabilizer_vertex p).ge⟩

end Stabilizers

/-! ### Incident darts and stars of vertices -/

section IncidentDarts

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}

namespace BassSerreTree

/-- Two elements `a, b ∈ A_{src e}` define the same outgoing dart `(p · a) α_e(A_e)` from `p A_v`
above `e` if and only if they lie in the same left coset of `(𝔸.α e).range`. -/
theorem dartMk_cons_vertex_eq_iff (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    {a b : 𝔸.vertexGroup (Γ.src e)} :
    dartMk e (p.cons (Letter.vertex a)) = dartMk e (p.cons (Letter.vertex b)) ↔
      (a : 𝔸.vertexGroup (Γ.src e) ⧸ (𝔸.α e).range) = b := by
  rw [dartMk_eq_dartMk_same_iff, QuotientGroup.eq]
  refine ⟨fun ⟨c, hc⟩ => ?_, fun ⟨c, hc⟩ => ⟨c⁻¹, ?_⟩⟩
  · have hmul : Path.Homotopic (p.cons (Letter.vertex a)) (p.cons (Letter.vertex (b * 𝔸.α e c))) :=
      hc.trans (Path.Homotopic.mul p b (𝔸.α e c))
    obtain rfl : a = b * 𝔸.α e c := (Path.cons_vertex_homotopic_cons_vertex_iff p).mp hmul
    exact ⟨c⁻¹, by rw [map_inv, mul_inv_rev, inv_mul_cancel_right]⟩
  · have hab : a = b * 𝔸.α e c⁻¹ := by
      rw [map_inv, hc, mul_inv_rev, inv_inv, mul_inv_cancel_left]
    rw [hab]
    exact (Path.Homotopic.mul p b (𝔸.α e c⁻¹)).symm

/-- Outgoing darts of `X(𝔸, v₀)` at `vertexMk p` projecting to a fixed dart `e : Γ.E` correspond
bijectively to the left cosets `A_{src e} ⧸ (𝔸.α e).range`. -/
noncomputable def incidentDartFiberEquiv (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.vertexGroup (Γ.src e) ⧸ (𝔸.α e).range) ≃
      {δ : (𝔸.bassSerreTree v₀).E //
        (𝔸.bassSerreTree v₀).src δ = vertexMk p ∧ (projHom 𝔸 v₀).mapE δ = e} :=
  Equiv.ofBijective
    (Quotient.lift
      (fun a : 𝔸.vertexGroup (Γ.src e) =>
        ⟨dartMk e (p.cons (Letter.vertex a)), by simp, projHom_mapE_dartMk e _⟩)
      fun a b hab => Subtype.ext <|
        (dartMk_cons_vertex_eq_iff e p).mpr (Quotient.sound hab))
    ⟨Quotient.ind₂ fun a b h => (dartMk_cons_vertex_eq_iff e p).mp (congrArg Subtype.val h),
      fun ⟨δ, hsrc, hproj⟩ => by
        induction δ using dart_induction_on with
        | mk e' q =>
          rw [projHom_mapE_dartMk] at hproj
          subst hproj
          rw [src_dartMk] at hsrc
          obtain ⟨a, ha⟩ := vertexMk_eq_vertexMk_same_iff.mp hsrc
          exact ⟨(a : 𝔸.vertexGroup (Γ.src e') ⧸ (𝔸.α e').range),
            Subtype.ext (dartMk_congr e' ha.symm)⟩⟩

@[simp] theorem incidentDartFiberEquiv_mk_val (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (a : 𝔸.vertexGroup (Γ.src e)) :
    (incidentDartFiberEquiv e p a).1 = dartMk e (p.cons (Letter.vertex a)) :=
  (rfl)

/-- For an arrow `f : v ⟶ w`, two elements `a, b ∈ A_v` define the same outgoing dart
`arrowMk f (p · a)` if and only if they lie in the same left coset of `(𝔸.αArrow f).range`. -/
theorem arrowMk_cons_vertex_eq_iff {v w : Γ.V} (f : v ⟶ w) (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    {a b : 𝔸.vertexGroup v} :
    arrowMk f (p.cons (Letter.vertex a)) = arrowMk f (p.cons (Letter.vertex b)) ↔
      (a : 𝔸.vertexGroup v ⧸ (𝔸.αArrow f).range) = b := by
  rcases f with ⟨e, rfl, rfl⟩
  rw [αArrow_mk, arrowMk_mk, arrowMk_mk]
  exact dartMk_cons_vertex_eq_iff e p

/-- All darts of `X(𝔸, v₀)` issuing from `vertexMk p` (`p : 𝔸.Path ⟨v₀⟩ ⟨v⟩`) correspond
bijectively to pairs of an outgoing dart `e` at `v` in `Γ` and a left coset of `α_e(A_e)` in
`A_v`. -/
noncomputable def incidentDartEquiv {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (Σ e : {e : Γ.E // Γ.src e = v},
      𝔸.vertexGroup v ⧸ (𝔸.αArrow (⟨e.1, e.2, rfl⟩ : v ⟶ Γ.tgt e.1)).range) ≃
      {δ : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src δ = vertexMk p} :=
  Equiv.ofBijective
    (fun ⟨e, q⟩ => Quotient.liftOn q
      (fun a => ⟨arrowMk (⟨e.1, e.2, rfl⟩ : v ⟶ Γ.tgt e.1) (p.cons (Letter.vertex a)), by simp⟩)
      fun a b hab => Subtype.ext <|
        (arrowMk_cons_vertex_eq_iff (⟨e.1, e.2, rfl⟩ : v ⟶ Γ.tgt e.1) p).mpr
          (Quotient.sound hab))
    ⟨by
      rintro ⟨⟨e₁, he₁⟩, q₁⟩ ⟨⟨e₂, he₂⟩, q₂⟩ h
      induction q₁ using Quotient.inductionOn with | h a₁ => ?_
      induction q₂ using Quotient.inductionOn with | h a₂ => ?_
      have he : e₁ = e₂ := by
        simpa using congrArg (projHom 𝔸 v₀).mapE (congrArg Subtype.val h)
      subst he
      obtain rfl : he₁ = he₂ := rfl
      refine Sigma.ext rfl (heq_of_eq ?_)
      exact (arrowMk_cons_vertex_eq_iff (⟨e₁, he₁, rfl⟩ : v ⟶ Γ.tgt e₁) p).mp
        (congrArg Subtype.val h),
      fun ⟨δ, hsrc⟩ => by
        obtain ⟨_, ⟨e, he, rfl⟩, a, rfl⟩ := exists_eq_arrowMk_of_src_eq p hsrc
        exact ⟨⟨⟨e, he⟩, a⟩, rfl⟩⟩

@[simp] theorem incidentDartEquiv_mk_val {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (e : {e : Γ.E // Γ.src e = v}) (a : 𝔸.vertexGroup v) :
    (incidentDartEquiv p ⟨e, a⟩).1 =
      arrowMk (⟨e.1, e.2, rfl⟩ : v ⟶ Γ.tgt e.1) (p.cons (Letter.vertex a)) :=
  (rfl)

/-- Distinct darts of `X(𝔸, v₀)` with the same source have distinct targets. -/
theorem tgt_injective_of_src_eq {x : (𝔸.bassSerreTree v₀).V} :
    Function.Injective
      (fun δ : {δ : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src δ = x} =>
        (𝔸.bassSerreTree v₀).tgt δ.1) := by
  rintro ⟨δ₁, h₁⟩ ⟨δ₂, h₂⟩ htgt
  apply Subtype.ext
  let f₁ : x ⟶ (𝔸.bassSerreTree v₀).tgt δ₁ := ⟨δ₁, h₁, rfl⟩
  let f₂ : x ⟶ (𝔸.bassSerreTree v₀).tgt δ₁ := ⟨δ₂, h₂, htgt.symm⟩
  have hpath := (𝔸.bassSerreTree v₀).isTree.isAcyclic.eq_of_isReduced
    (SerreGraph.Path.isReduced_toPath _ f₁) (SerreGraph.Path.isReduced_toPath _ f₂)
  have hdarts := congrArg (SerreGraph.Path.darts (𝔸.bassSerreTree v₀).toSerreGraph) hpath
  simpa [f₁, f₂] using hdarts

end BassSerreTree

end IncidentDarts

/-! ### The quotient graph `π₁(𝔸, v₀) \ X(𝔸, v₀)` -/

section QuotientGraph

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

namespace BassSerreTree

/-- The quotient Serre graph `π₁(𝔸, v₀) \ X(𝔸, v₀)`. -/
abbrev quotient : SerreGraph.{max u v w, max u v w} :=
  (𝔸.bassSerreTree v₀).toSerreGraph.quotient (𝔸.bassSerreTree v₀).action
    (𝔸.bassSerreTree v₀).action_smul_ne_rev

/-- The orbit projection morphism `X(𝔸, v₀) → π₁(𝔸, v₀) \ X(𝔸, v₀)`. -/
abbrev quotientMap : (𝔸.bassSerreTree v₀).toSerreGraph.Hom (quotient 𝔸 v₀) :=
  (𝔸.bassSerreTree v₀).toSerreGraph.quotientMap (𝔸.bassSerreTree v₀).action
    (𝔸.bassSerreTree v₀).action_smul_ne_rev

/-- The descended morphism from `π₁(𝔸, v₀) \ X(𝔸, v₀)` to `Γ.component v₀`. -/
def quotientToComponentHom : (quotient 𝔸 v₀).Hom (Γ.component v₀) :=
  SerreGraph.quotientLift (𝔸.bassSerreTree v₀).action_smul_ne_rev (projComponentHom 𝔸 v₀)
    (projComponentHom_comp_action (𝔸 := 𝔸) (v₀ := v₀))

@[simp] theorem quotientToComponentHom_mapV_quotientMap {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    ((quotientToComponentHom 𝔸 v₀).mapV ((quotientMap 𝔸 v₀).mapV (vertexMk p))).1 = v := by
  simp [quotientToComponentHom]

@[simp] theorem quotientToComponentHom_mapE_quotientMap (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    ((quotientToComponentHom 𝔸 v₀).mapE ((quotientMap 𝔸 v₀).mapE (dartMk e p))).1 = e := by
  simp [quotientToComponentHom]

/-- The descended morphism `π₁(𝔸, v₀) \ X(𝔸, v₀) → Γ.component v₀` is bijective on vertices. -/
theorem quotientToComponentHom_mapV_bijective :
    Function.Bijective (quotientToComponentHom 𝔸 v₀).mapV := by
  refine ⟨fun x y hxy => ?_, fun ⟨v, hmem⟩ => ?_⟩
  · obtain ⟨a, rfl⟩ := SerreGraph.quotientMap_mapV_surjective _ _ _ x
    obtain ⟨b, rfl⟩ := SerreGraph.quotientMap_mapV_surjective _ _ _ y
    induction a using vertex_induction_on with | mk p₁ => ?_
    induction b using vertex_induction_on with | mk p₂ => ?_
    have hv : _ = _ := congrArg Subtype.val hxy
    simp only [quotientToComponentHom_mapV_quotientMap] at hv
    subst hv
    refine SerreGraph.quotientMap_mapV_eq_iff.mpr ⟨π₁.mk (p₂.comp p₁.reverse), ?_⟩
    rw [← GTree.smul_vertex_def, smul_vertexMk]
    refine vertexMk_congr ?_
    rw [Quiver.Path.comp_assoc]
    simpa only [Quiver.Path.comp_nil] using
      (Path.Homotopic.refl p₂).comp (Path.Homotopic.reverse_comp p₁)
  · obtain ⟨q⟩ := (Γ.mem_componentVertices_iff v₀).mp hmem
    refine ⟨(quotientMap 𝔸 v₀).mapV (vertexMk ((dartPrefunctor 𝔸).mapPath q)), ?_⟩
    exact Subtype.ext (by simp [quotientToComponentHom])

/-- The descended morphism `π₁(𝔸, v₀) \ X(𝔸, v₀) → Γ.component v₀` is bijective on darts. -/
theorem quotientToComponentHom_mapE_bijective :
    Function.Bijective (quotientToComponentHom 𝔸 v₀).mapE := by
  refine ⟨fun x y hxy => ?_, fun ⟨e, hmem⟩ => ?_⟩
  · obtain ⟨δ₁, rfl⟩ := SerreGraph.quotientMap_mapE_surjective _ _ _ x
    obtain ⟨δ₂, rfl⟩ := SerreGraph.quotientMap_mapE_surjective _ _ _ y
    induction δ₁ using dart_induction_on with | mk e₁ p₁ => ?_
    induction δ₂ using dart_induction_on with | mk e₂ p₂ => ?_
    have he : e₁ = e₂ := by
      have h' := congrArg Subtype.val hxy
      simpa only [quotientToComponentHom_mapE_quotientMap] using h'
    subst he
    refine SerreGraph.quotientMap_mapE_eq_iff.mpr ⟨π₁.mk (p₂.comp p₁.reverse), ?_⟩
    rw [← GTree.smul_dart_def, smul_dartMk]
    refine dartMk_congr e₁ ?_
    rw [Quiver.Path.comp_assoc]
    simpa only [Quiver.Path.comp_nil] using
      (Path.Homotopic.refl p₂).comp (Path.Homotopic.reverse_comp p₁)
  · obtain ⟨q⟩ := (Γ.mem_componentDarts_iff v₀).mp hmem
    refine ⟨(quotientMap 𝔸 v₀).mapE (dartMk e ((dartPrefunctor 𝔸).mapPath q)), ?_⟩
    exact Subtype.ext (by simp [quotientToComponentHom])

end BassSerreTree

/-- The quotient graph `π₁(𝔸, v₀) \ X(𝔸, v₀)` of the Bass–Serre tree is canonically isomorphic to
the connected component `Γ.component v₀` of `v₀` in `Γ`. -/
noncomputable def quotientBassSerreTreeIsoComponent :
    (BassSerreTree.quotient 𝔸 v₀).Iso (Γ.component v₀) :=
  (BassSerreTree.quotientToComponentHom 𝔸 v₀).toIso
    (BassSerreTree.quotientToComponentHom_mapV_bijective 𝔸 v₀)
    (BassSerreTree.quotientToComponentHom_mapE_bijective 𝔸 v₀)

@[simp] theorem quotientBassSerreTreeIsoComponent_equivV_quotientMap {v : Γ.V}
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    ((quotientBassSerreTreeIsoComponent 𝔸 v₀).equivV
      ((BassSerreTree.quotientMap 𝔸 v₀).mapV (BassSerreTree.vertexMk p))).1 = v := by
  simp [quotientBassSerreTreeIsoComponent]

@[simp] theorem quotientBassSerreTreeIsoComponent_equivE_quotientMap (e : Γ.E)
    (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    ((quotientBassSerreTreeIsoComponent 𝔸 v₀).equivE
      ((BassSerreTree.quotientMap 𝔸 v₀).mapE (BassSerreTree.dartMk e p))).1 = e := by
  simp [quotientBassSerreTreeIsoComponent]

/-- When the underlying graph `Γ` is preconnected, the quotient graph `π₁(𝔸, v₀) \ X(𝔸, v₀)` is
canonically isomorphic to `Γ` itself. -/
noncomputable def quotientBassSerreTreeIso (hΓ : Γ.Preconnected) :
    (BassSerreTree.quotient 𝔸 v₀).Iso Γ :=
  (quotientBassSerreTreeIsoComponent 𝔸 v₀).trans (Γ.componentIsoOfPreconnected v₀ hΓ)

@[simp] theorem quotientBassSerreTreeIso_equivV_quotientMap (hΓ : Γ.Preconnected) {v : Γ.V}
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (quotientBassSerreTreeIso 𝔸 v₀ hΓ).equivV
      ((BassSerreTree.quotientMap 𝔸 v₀).mapV (BassSerreTree.vertexMk p)) = v := by
  simp [quotientBassSerreTreeIso]

@[simp] theorem quotientBassSerreTreeIso_equivE_quotientMap (hΓ : Γ.Preconnected) (e : Γ.E)
    (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (quotientBassSerreTreeIso 𝔸 v₀ hΓ).equivE
      ((BassSerreTree.quotientMap 𝔸 v₀).mapE (BassSerreTree.dartMk e p)) = e := by
  simp [quotientBassSerreTreeIso]

end QuotientGraph

end GraphOfGroups
end TauCeti
