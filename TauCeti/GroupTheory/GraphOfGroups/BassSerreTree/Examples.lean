/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.BassSerreTree.Stabilizers
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Special cases and concrete checks for Bass–Serre trees

This file specializes the Bass–Serre tree `X(𝔸, v₀)` and its quotient and stabilizer API to standard
test cases:

* **Edgeless and disconnected base graphs** (`bassSerreTreePointIso`,
  `unique_bassSerreTree_and_quotient_two_isolated_vertices`): over a graph with no darts, `X(𝔸, v₀)`
  is a single point regardless of `A_{v₀}` or isolated vertices outside the component of `v₀`; for
  two isolated vertices with trivial groups, both `X(𝔸, false)` and `π₁ \ X(𝔸, false)` have
  cardinality `1` while the ambient graph has `2` vertices and no `𝔸`-path between them.
* **Necessity of the right `A_v`-coset relation** (`mk_ofVertex_ne_one_and_vertexMk_eq_baseVertex`):
  nontrivial elements `g ≠ 1` of `A_{v₀}` yield distinct homotopy classes in `π₁(𝔸, v₀)` while
  collapsing to the single `baseVertex` in `X(𝔸, v₀)`.
* **Trivial vertex groups** (`bassSerreVertexReducedPathEquiv`): `π₁(𝔸, v₀)` acts freely on
  `X(𝔸, v₀)`, whose vertices correspond bijectively to reduced edge paths of `Γ` starting at `v₀`
  (the universal cover of `Γ.component v₀`).
* **Free product `ℤ ∗ ℤ`** (`freeProductZ2IncidentDartEquiv`, `freeProductZ2_neighbour_injective`):
  the base vertex `⟨a⟩` has incident darts and neighbours indexed injectively by `ℤ`.
* **Baumslag–Solitar group `BS(1, 2)`** (`bs12_natCard_incident_darts`): every vertex of the
  Bass–Serre tree of `BS(1, 2)` has degree `3` (`1` outgoing dart in the index-`1` direction and `2`
  in the index-`2` direction).

## References

* J.-P. Serre, *Trees*, Chapter I, §5.3.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2.
-/

public section

universe u v w x

namespace TauCeti
namespace GraphOfGroups

variable {Γ : SerreGraph.{u, v}}

/-! ### Graphs without edges and disconnected base graphs -/

section Edgeless

variable (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) [IsEmpty Γ.E]

instance : IsEmpty (𝔸.bassSerreTree v₀).E :=
  ⟨fun δ => isEmptyElim ((BassSerreTree.projHom 𝔸 v₀).mapE δ)⟩

instance : Unique (𝔸.bassSerreTree v₀).V where
  default := BassSerreTree.baseVertex 𝔸 v₀
  uniq x := @Subsingleton.elim _ (𝔸.bassSerreTree v₀).subsingleton_of_isEmpty_dart x _

/-- Over a graph without edges, the Bass–Serre tree `X(𝔸, v₀)` is isomorphic as a Serre graph to a
single point, regardless of `A_{v₀}` or other isolated vertices of `Γ`. -/
noncomputable def bassSerreTreePointIso :
    (𝔸.bassSerreTree v₀).toSerreGraph.Iso SerreGraph.point.{0, 0} where
  equivV := Equiv.ofUnique _ _
  equivE := Equiv.equivOfIsEmpty _ _
  map_src δ := isEmptyElim δ
  map_rev δ := isEmptyElim δ

variable {v₀} in
/-- Over a graph without edges, no `𝔸`-path connects distinct vertices. -/
theorem isEmpty_path_of_ne {u v : Γ.V} (huv : u ≠ v) :
    IsEmpty (𝔸.Path ⟨u⟩ ⟨v⟩) :=
  ⟨fun p => huv (SerreGraph.eq_of_path_of_forall_src_eq_tgt Γ isEmptyElim p.edgePath)⟩

end Edgeless

/-- For two isolated vertices with trivial vertex groups, `X(𝔸, false)` and its quotient
`π₁ \ X(𝔸, false)` each have a single vertex, whereas the ambient graph has two vertices and no
`𝔸`-path between them. -/
theorem unique_bassSerreTree_and_quotient_two_isolated_vertices :
    let Γ₂ := SerreGraph.segment.restrict ∅ fun _ h => h.elim
    let 𝔸₂ := GraphOfGroups.trivial Γ₂
    Nat.card (𝔸₂.bassSerreTree (false : Γ₂.V)).V = 1 ∧
      Nat.card (BassSerreTree.quotient 𝔸₂ (false : Γ₂.V)).V = 1 ∧
      Nat.card Γ₂.V = 2 ∧
      IsEmpty (𝔸₂.Path ⟨(false : Γ₂.V)⟩ ⟨(true : Γ₂.V)⟩) := by
  dsimp only
  let Γ₂ := SerreGraph.segment.restrict ∅ fun _ h => h.elim
  let 𝔸₂ := GraphOfGroups.trivial Γ₂
  let v₀ : Γ₂.V := false
  have hEmptyE : IsEmpty (𝔸₂.bassSerreTree v₀).E :=
    ⟨fun δ => ((BassSerreTree.projHom 𝔸₂ v₀).mapE δ).2.elim⟩
  have hSubT : Subsingleton (𝔸₂.bassSerreTree v₀).V :=
    @GTree.subsingleton_of_isEmpty_dart _ _ (𝔸₂.bassSerreTree v₀) hEmptyE
  have hSubQ : Subsingleton (BassSerreTree.quotient 𝔸₂ v₀).V :=
    ⟨fun x y => by
      obtain ⟨a, rfl⟩ := SerreGraph.quotientMap_mapV_surjective _ _ _ x
      obtain ⟨b, rfl⟩ := SerreGraph.quotientMap_mapV_surjective _ _ _ y
      exact congrArg _ (@Subsingleton.elim _ hSubT a b)⟩
  refine ⟨Nat.card_eq_one_iff_unique.mpr ⟨hSubT, ⟨BassSerreTree.baseVertex 𝔸₂ v₀⟩⟩,
    Nat.card_eq_one_iff_unique.mpr
      ⟨hSubQ, ⟨(BassSerreTree.quotientMap 𝔸₂ v₀).mapV (BassSerreTree.baseVertex 𝔸₂ v₀)⟩⟩,
    (Nat.card_congr SerreGraph.segmentVEquiv).trans (by simp),
    ⟨fun p => Bool.false_ne_true
      (SerreGraph.eq_of_path_of_forall_src_eq_tgt Γ₂ (fun e => e.2.elim) p.edgePath)⟩⟩

/-! ### Necessity of the right `A_v`-coset relation -/

/-- Every nontrivial element `g ≠ 1` of `A_{v₀}` defines a nontrivial homotopy class
`π₁.mk (Path.ofVertex g) ≠ 1` at `v₀`, whereas in `X(𝔸, v₀)` all vertex-letter paths
`Path.ofVertex g` represent `baseVertex 𝔸 v₀`. -/
theorem mk_ofVertex_ne_one_and_vertexMk_eq_baseVertex {𝔸 : GraphOfGroups.{u, v, w, x} Γ}
    {v₀ : Γ.V} {g : 𝔸.vertexGroup v₀} (hg : g ≠ 1) :
    π₁.mk (Path.ofVertex g) ≠ (1 : π₁ 𝔸 v₀) ∧
      BassSerreTree.vertexMk (Path.ofVertex g) = BassSerreTree.baseVertex 𝔸 v₀ :=
  ⟨π₁.mk_ofVertex_eq_one_iff.not.mpr hg, BassSerreTree.vertexMk_ofVertex g⟩

/-! ### Trivial vertex groups: universal cover and free action -/

section TrivialGroups

variable (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) [∀ v, Subsingleton (𝔸.vertexGroup v)]

/-- When all vertex groups of `𝔸` are trivial, every vertex stabilizer in `X(𝔸, v₀)` is trivial. -/
@[simp] theorem stabilizer_vertex_eq_bot_of_subsingleton (x : (𝔸.bassSerreTree v₀).V) :
    MulAction.stabilizer (π₁ 𝔸 v₀) x = ⊥ := by
  induction x using BassSerreTree.vertex_induction_on with
  | mk p =>
    rw [stabilizer_vertex, eq_bot_iff]
    rintro _ ⟨a, rfl⟩
    rw [Subsingleton.elim a 1, map_one]
    exact Subgroup.one_mem ⊥

/-- When all vertex groups of `𝔸` are trivial, every dart stabilizer in `X(𝔸, v₀)` is trivial. -/
@[simp] theorem stabilizer_edge_eq_bot_of_subsingleton (δ : (𝔸.bassSerreTree v₀).E) :
    MulAction.stabilizer (π₁ 𝔸 v₀) δ = ⊥ :=
  le_bot_iff.mp <| ((𝔸.bassSerreTree v₀).stabilizer_dart_le_stabilizer_src δ).trans_eq
    (stabilizer_vertex_eq_bot_of_subsingleton 𝔸 v₀ _)

/-- When all vertex groups of `𝔸` are trivial, the vertices of `X(𝔸, v₀)` correspond bijectively
to reduced edge paths of `Γ` starting at `v₀` (the vertices of the universal cover of
`Γ.component v₀`). -/
noncomputable def bassSerreVertexReducedPathEquiv :
    (𝔸.bassSerreTree v₀).V ≃
      Σ v : Γ.V, {p : Γ.Path v₀ v // SerreGraph.Path.IsReduced Γ p} where
  toFun := BassSerreTree.vertexLift
    (fun {v} p => ⟨v, ⟨SerreGraph.Path.reduce Γ p.edgePath,
      SerreGraph.Path.isReduced_reduce Γ _⟩⟩)
    (fun hpq => Sigma.ext rfl (heq_of_eq (Subtype.ext (hpq.edgePath.reduce_eq Γ))))
    (fun _ _ => by simp)
  invFun x := BassSerreTree.vertexMk ((dartPrefunctor 𝔸).mapPath x.2.1)
  left_inv x := by
    induction x using BassSerreTree.vertex_induction_on with
    | mk p =>
      rw [BassSerreTree.vertexLift_vertexMk]
      exact BassSerreTree.vertexMk_congr <|
        (((SerreGraph.Path.homotopic_reduce Γ p.edgePath).symm.mapPath_dartPrefunctor 𝔸).trans
          (Path.homotopic_mapPath_edgePath p).symm)
  right_inv := fun ⟨_, ⟨q, hq⟩⟩ => by
    simp only [BassSerreTree.vertexLift_vertexMk, Path.edgePath_mapPath_dartPrefunctor,
      SerreGraph.Path.reduce_eq_self_of_isReduced Γ q hq]

end TrivialGroups

/-! ### Free product `ℤ ∗ ℤ` -/

section FreeProduct

/-- The segment graph of groups presenting `ℤ ∗ ℤ`, with vertex groups `Multiplicative ℤ` and
trivial edge group `PUnit`. -/
@[expose] def freeProductZ2 : GraphOfGroups.{0, 0, 0, 0} SerreGraph.segment :=
  GraphOfGroups.segment (1 : PUnit →* Multiplicative ℤ) (1 : PUnit →* Multiplicative ℤ)
    (Function.injective_of_subsingleton _) (Function.injective_of_subsingleton _)

/-- In the Bass–Serre tree of `ℤ ∗ ℤ`, the darts issuing from the base vertex `⟨a⟩` at `false`
are in canonical bijection with `ℤ` via `k ↦ dartMk false (Path.ofVertex (ofAdd k))`. -/
noncomputable def freeProductZ2IncidentDartEquiv :
    ℤ ≃ {δ : (freeProductZ2.bassSerreTree (false : SerreGraph.segment.V)).E //
      (freeProductZ2.bassSerreTree (false : SerreGraph.segment.V)).src δ =
        BassSerreTree.baseVertex freeProductZ2 (false : SerreGraph.segment.V)} :=
  ({ toFun := fun k => QuotientGroup.mk (Multiplicative.ofAdd k)
     invFun := Quotient.lift Multiplicative.toAdd fun _ _ hxy => by
       obtain ⟨⟨⟩, hc⟩ := QuotientGroup.leftRel_apply.mp hxy
       exact congrArg Multiplicative.toAdd (inv_mul_eq_one.mp (hc.symm.trans (map_one _)))
     left_inv := toAdd_ofAdd
     right_inv := Quotient.ind fun x => congrArg QuotientGroup.mk (ofAdd_toAdd x) } :
    ℤ ≃ freeProductZ2.vertexGroup (SerreGraph.segment.src (false : SerreGraph.segment.E)) ⧸
      (freeProductZ2.α (false : SerreGraph.segment.E)).range).trans <|
    (BassSerreTree.incidentDartFiberEquiv (𝔸 := freeProductZ2)
      (v₀ := (false : SerreGraph.segment.V)) (false : SerreGraph.segment.E) .nil).trans <|
      Equiv.subtypeEquivRight fun δ => and_iff_left_of_imp fun hsrc =>
        (((BassSerreTree.projHom freeProductZ2 (false : SerreGraph.segment.V)).map_src δ).trans
          (congrArg (BassSerreTree.projHom freeProductZ2 (false : SerreGraph.segment.V)).mapV
            hsrc)).trans
          (BassSerreTree.projHom_mapV_vertexMk
            (.nil : freeProductZ2.Path ⟨(false : SerreGraph.segment.V)⟩
              ⟨(false : SerreGraph.segment.V)⟩))

@[simp] theorem freeProductZ2IncidentDartEquiv_apply_val (k : ℤ) :
    (freeProductZ2IncidentDartEquiv k).1 =
      BassSerreTree.dartMk (𝔸 := freeProductZ2) (v₀ := (false : SerreGraph.segment.V))
        (false : SerreGraph.segment.E)
        (Path.ofVertex (Multiplicative.ofAdd k :
          freeProductZ2.vertexGroup (false : SerreGraph.segment.V))) :=
  (BassSerreTree.incidentDartFiberEquiv_mk_val (𝔸 := freeProductZ2)
    (v₀ := (false : SerreGraph.segment.V)) (false : SerreGraph.segment.E) .nil
    (Multiplicative.ofAdd k : freeProductZ2.vertexGroup (false : SerreGraph.segment.V))).trans <|
    congrArg
      (BassSerreTree.dartMk (𝔸 := freeProductZ2) (v₀ := (false : SerreGraph.segment.V))
        (false : SerreGraph.segment.E))
      (Path.ofVertex_eq_nil_cons _).symm

/-- In the Bass–Serre tree of `ℤ ∗ ℤ`, the neighbours `a^k ⟨b⟩` (`k ∈ ℤ`) of the base vertex
`⟨a⟩` are pairwise distinct, so `⟨a⟩` has countably infinite degree. -/
theorem freeProductZ2_neighbour_injective :
    Function.Injective fun k : ℤ =>
      BassSerreTree.vertexMk (𝔸 := freeProductZ2) (v₀ := (false : SerreGraph.segment.V))
        ((Path.ofVertex (Multiplicative.ofAdd k :
            freeProductZ2.vertexGroup (false : SerreGraph.segment.V))).cons
          (Letter.dart (SerreGraph.segment.dart (false : SerreGraph.segment.E)))) := by
  intro k₁ k₂ hk
  apply freeProductZ2IncidentDartEquiv.injective
  apply BassSerreTree.tgt_injective_of_src_eq
  dsimp only
  rw [freeProductZ2IncidentDartEquiv_apply_val, freeProductZ2IncidentDartEquiv_apply_val]
  exact ((BassSerreTree.tgt_dartMk _ _).trans hk).trans (BassSerreTree.tgt_dartMk _ _).symm

end FreeProduct

/-! ### Baumslag–Solitar group `BS(1, 2)` -/

section BS12

/-- Squaring on `Multiplicative ℤ` (doubling on `ℤ`) is injective. -/
theorem powMonoidHom_two_multiplicativeInt_injective :
    Function.Injective (powMonoidHom 2 : Multiplicative ℤ →* Multiplicative ℤ) := by
  intro x y h
  obtain ⟨m, rfl⟩ := Multiplicative.ofAdd.surjective x
  obtain ⟨n, rfl⟩ := Multiplicative.ofAdd.surjective y
  have hmn : (2 : ℕ) • m = (2 : ℕ) • n := Multiplicative.ofAdd.injective h
  rw [two_nsmul, two_nsmul] at hmn
  exact congrArg Multiplicative.ofAdd (by omega)

/-- The loop graph of groups presenting `BS(1, 2) = ⟨a, t | t a t⁻¹ = a²⟩`, with vertex and edge
group `Multiplicative ℤ`, `α = id` and `ω = powMonoidHom 2`. -/
@[expose] def bs12 : GraphOfGroups.{0, 0, 0, 0} (SerreGraph.rose Unit) :=
  GraphOfGroups.loop (.id (Multiplicative ℤ)) (powMonoidHom 2)
    Function.injective_id powMonoidHom_two_multiplicativeInt_injective

private theorem natCard_quotient_powMonoidHom_two :
    Nat.card (Multiplicative ℤ ⧸ (powMonoidHom 2 : Multiplicative ℤ →* Multiplicative ℤ).range) =
      2 := by
  let e :
      (Multiplicative ℤ ⧸ (powMonoidHom 2 : Multiplicative ℤ →* Multiplicative ℤ).range) ≃ Bool :=
    { toFun := Quotient.lift (fun x => decide (Multiplicative.toAdd x % 2 ≠ 0)) fun x y hxy => by
        obtain ⟨z, hz⟩ := QuotientGroup.leftRel_apply.mp hxy
        have hadd : (2 : ℕ) • Multiplicative.toAdd z =
            -Multiplicative.toAdd x + Multiplicative.toAdd y :=
          Multiplicative.toAdd.congr_arg hz
        rw [two_nsmul] at hadd
        have hmod : Multiplicative.toAdd x % 2 = Multiplicative.toAdd y % 2 := by omega
        simp [hmod]
      invFun := fun b => QuotientGroup.mk (Multiplicative.ofAdd (cond b 1 0))
      left_inv := Quotient.ind fun x => Quotient.sound <| QuotientGroup.leftRel_apply.mpr <| by
        refine ⟨Multiplicative.ofAdd ((Multiplicative.toAdd x -
          cond (decide (Multiplicative.toAdd x % 2 ≠ 0)) 1 0) / 2), ?_⟩
        apply Multiplicative.toAdd.injective
        simp only [powMonoidHom_apply, toAdd_pow, toAdd_mul, toAdd_inv, toAdd_ofAdd,
          two_nsmul, Quotient.lift_mk]
        by_cases hodd : Multiplicative.toAdd x % 2 ≠ 0 <;> simp [hodd] <;> omega
      right_inv := fun b => by cases b <;> decide }
  simpa using Nat.card_congr e

private noncomputable def bs12IncidentDartSumEquiv (v₀ : (SerreGraph.rose Unit).V)
    (p : bs12.Path ⟨v₀⟩ ⟨(SerreGraph.rose Unit).src ((), true)⟩) :
    {δ : (bs12.bassSerreTree v₀).E //
      (bs12.bassSerreTree v₀).src δ = BassSerreTree.vertexMk p} ≃
      (bs12.vertexGroup ((SerreGraph.rose Unit).src ((), true)) ⧸ (bs12.α ((), true)).range) ⊕
        (bs12.vertexGroup ((SerreGraph.rose Unit).src ((), false)) ⧸ (bs12.α ((), false)).range) :=
  ({ toFun := fun ⟨δ, h⟩ =>
       if hm : ((BassSerreTree.projHom bs12 v₀).mapE δ).2 = true then
         .inl ⟨δ, h, Prod.ext (Subsingleton.elim _ _) hm⟩
       else
         .inr ⟨δ, h, Prod.ext (Subsingleton.elim _ _) (Bool.eq_false_iff.mpr hm)⟩
     invFun := Sum.elim (fun x => ⟨x.1, x.2.1⟩) (fun x => ⟨x.1, x.2.1⟩)
     left_inv := fun ⟨_, _⟩ => by
       dsimp only
       split_ifs <;> rfl
     right_inv := by
       rintro (⟨_, _, hm⟩ | ⟨_, _, hm⟩) <;> simp [hm] } :
    {δ : (bs12.bassSerreTree v₀).E //
      (bs12.bassSerreTree v₀).src δ = BassSerreTree.vertexMk p} ≃
      {δ : (bs12.bassSerreTree v₀).E //
        (bs12.bassSerreTree v₀).src δ = BassSerreTree.vertexMk p ∧
          (BassSerreTree.projHom bs12 v₀).mapE δ = ((), true)} ⊕
        {δ : (bs12.bassSerreTree v₀).E //
          (bs12.bassSerreTree v₀).src δ = BassSerreTree.vertexMk p ∧
            (BassSerreTree.projHom bs12 v₀).mapE δ = ((), false)}).trans <|
    Equiv.sumCongr
      (BassSerreTree.incidentDartFiberEquiv (𝔸 := bs12) ((), true) p).symm
      (BassSerreTree.incidentDartFiberEquiv (𝔸 := bs12) ((), false) p).symm

/-- In the Bass–Serre tree of `BS(1, 2)`, every vertex has degree `3`: `1` dart in the direction
with `[A : α(C)] = 1` and `2` darts in the direction with `[A : ω(C)] = 2`. -/
theorem bs12_natCard_incident_darts (v₀ : (SerreGraph.rose Unit).V)
    (x : (bs12.bassSerreTree v₀).V) :
    Nat.card {δ : (bs12.bassSerreTree v₀).E // (bs12.bassSerreTree v₀).src δ = x} = 3 := by
  induction x using BassSerreTree.vertex_induction_on with
  | @mk v p =>
    obtain rfl : v = (SerreGraph.rose Unit).src ((), true) := Subsingleton.elim _ _
    have hcard₁ : Nat.card (Multiplicative ℤ ⧸ (MonoidHom.id (Multiplicative ℤ)).range) = 1 :=
      Nat.card_eq_one_iff_unique.mpr
        ⟨⟨Quotient.ind₂ fun a b =>
            Quotient.sound <| QuotientGroup.leftRel_apply.mpr ⟨a⁻¹ * b, rfl⟩⟩,
          ⟨1⟩⟩
    have hα₁ :
        Nat.card (bs12.vertexGroup ((SerreGraph.rose Unit).src ((), true)) ⧸
          (bs12.α ((), true)).range) = 1 :=
      (congrArg (fun f : Multiplicative ℤ →* Multiplicative ℤ =>
        Nat.card (Multiplicative ℤ ⧸ f.range)) (loop_α_true _ _ _ _)).trans hcard₁
    have hα₂ :
        Nat.card (bs12.vertexGroup ((SerreGraph.rose Unit).src ((), false)) ⧸
          (bs12.α ((), false)).range) = 2 :=
      (congrArg (fun f : Multiplicative ℤ →* Multiplicative ℤ =>
        Nat.card (Multiplicative ℤ ⧸ f.range)) (loop_α_false _ _ _ _)).trans
        natCard_quotient_powMonoidHom_two
    have hfin₁ :
        Finite (bs12.vertexGroup ((SerreGraph.rose Unit).src ((), true)) ⧸
          (bs12.α ((), true)).range) :=
      Nat.finite_of_card_ne_zero (by rw [hα₁]; omega)
    have hfin₂ :
        Finite (bs12.vertexGroup ((SerreGraph.rose Unit).src ((), false)) ⧸
          (bs12.α ((), false)).range) :=
      Nat.finite_of_card_ne_zero (by rw [hα₂]; omega)
    exact (Nat.card_congr (bs12IncidentDartSumEquiv v₀ p)).trans <|
      (@Nat.card_sum _ _ hfin₁ hfin₂).trans (hα₁ ▸ hα₂ ▸ rfl)

end BS12

end GraphOfGroups
end TauCeti
