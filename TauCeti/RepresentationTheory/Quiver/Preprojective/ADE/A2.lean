/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Admissible
public import TauCeti.RepresentationTheory.Quiver.AdmissibleIdeal
public import TauCeti.RepresentationTheory.Quiver.Zigzag.ADE.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Orientation

/-!
# The preprojective algebra of `A₂`

The doubled one-arrow quiver has two length-two paths, one backtrack at each vertex. Its local
preprojective relations kill both paths, so the preprojective algebra is the arrow-ideal-square-zero
quotient. In particular it is finite-dimensional over any field.

The orientation is from the smaller to the larger Bourbaki-numbered vertex. The ideal computation
is over a commutative ring; finite-dimensionality uses a field.

See Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson problem*,
Section 1, for the preprojective presentation.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

/-- The source-to-sink orientation of the Bourbaki-numbered `A₂` graph. -/
abbrev preprojectiveA2Quiver := OrientedQuiver zigzagA2Graph
  (Orientation.ofLinearOrder zigzagA2Graph)

private abbrev v0 : preprojectiveA2Quiver := OrientedQuiver.vertex zigzagA2Graph
  (Orientation.ofLinearOrder zigzagA2Graph) 0

private abbrev v1 : preprojectiveA2Quiver := OrientedQuiver.vertex zigzagA2Graph
  (Orientation.ofLinearOrder zigzagA2Graph) 1

private def a2Arrow : (OrientedQuiver.vertex zigzagA2Graph
    (Orientation.ofLinearOrder zigzagA2Graph) 0 ⟶
    OrientedQuiver.vertex zigzagA2Graph
    (Orientation.ofLinearOrder zigzagA2Graph) 1) :=
  OrientedQuiver.arrow zigzagA2Graph (Orientation.ofLinearOrder zigzagA2Graph)
    ((zigzagA2Graph_adj 0 1).2 (by decide)) (by
      simpa only [Orientation.mem_ofLinearOrder_iff] using (show (0 : Fin 2) < 1 by decide))

private instance : IsEmpty (v0 ⟶ v0) := by
  constructor
  intro e
  have h : zigzagA2Graph.Adj 0 0 := by
    simpa only [OrientedQuiver.vertexEquiv_symm_vertex] using e.1
  exact (zigzagA2Graph_adj 0 0).mp h (by decide)

private instance : IsEmpty (v1 ⟶ v0) := by
  constructor
  intro e
  have h : (1 : Fin 2) < 0 := by
    simpa only [OrientedQuiver.vertexEquiv_symm_vertex,
      Orientation.mem_ofLinearOrder_iff] using e.2
  omega

private instance : IsEmpty (v1 ⟶ v1) := by
  constructor
  intro e
  have h : zigzagA2Graph.Adj 1 1 := by
    simpa only [OrientedQuiver.vertexEquiv_symm_vertex] using e.1
  exact (zigzagA2Graph_adj 1 1).mp h (by decide)

/-- Finite enumeration of the vertices of the chosen `A₂` orientation. -/
noncomputable instance instFintypePreprojectiveA2Quiver :
    Fintype preprojectiveA2Quiver := Fintype.ofFinite _

/-- Finite enumeration of arrows in the chosen `A₂` orientation. -/
noncomputable instance instFintypePreprojectiveA2QuiverHom (i j : preprojectiveA2Quiver) :
    Fintype (i ⟶ j) := Fintype.ofFinite _

private theorem sum_a2 {M : Type*} [AddCommMonoid M] (f : preprojectiveA2Quiver → M) :
    ∑ i : preprojectiveA2Quiver, f i = f v0 + f v1 := by
  let e := OrientedQuiver.vertexEquiv zigzagA2Graph
    (Orientation.ofLinearOrder zigzagA2Graph)
  calc
    _ = ∑ i : Fin 2, f (e i) :=
      (Fintype.sum_equiv e (fun i => f (e i)) f (fun _ => rfl)).symm
    _ = _ := by simp [Fin.sum_univ_two, e, v0, v1]

private theorem localPreprojectiveRelator_zero (k : Type*) [CommRing k] :
    localPreprojectiveRelator k v0 = -tailBacktrackElem k a2Arrow := by
  rw [localPreprojectiveRelator_def, sum_a2, sum_a2]
  simp [Fintype.sum_subsingleton (fun a : v0 ⟶ v1 =>
    tailBacktrackElem k a) a2Arrow]

private theorem localPreprojectiveRelator_one (k : Type*) [CommRing k] :
    localPreprojectiveRelator k v1 = headBacktrackElem k a2Arrow := by
  rw [localPreprojectiveRelator_def, sum_a2, sum_a2]
  simp [Fintype.sum_subsingleton (fun a : v0 ⟶ v1 =>
    headBacktrackElem k a) a2Arrow]

private theorem tailBacktrack_mem_preprojectiveIdeal (k : Type*) [CommRing k] :
    tailBacktrackElem k a2Arrow ∈ preprojectiveIdeal k preprojectiveA2Quiver := by
  have h := localPreprojectiveRelator_mem_preprojectiveIdeal k v0
  rw [localPreprojectiveRelator_zero] at h
  exact neg_mem_iff.mp h

private theorem headBacktrack_mem_preprojectiveIdeal (k : Type*) [CommRing k] :
    headBacktrackElem k a2Arrow ∈ preprojectiveIdeal k preprojectiveA2Quiver := by
  rw [← localPreprojectiveRelator_one]
  exact localPreprojectiveRelator_mem_preprojectiveIdeal k v1

private def e01 : (Symmetrify.of.obj v0 ⟶ Symmetrify.of.obj v1) := Sum.inl a2Arrow

private def e10 : (Symmetrify.of.obj v1 ⟶ Symmetrify.of.obj v0) := Sum.inr a2Arrow

private theorem reverse_e01 : Quiver.reverse e01 = e10 := by
  simp [e01, e10, symmetrify_reverse]
  rfl

private noncomputable def vertices : Fin 2 ≃ Symmetrify preprojectiveA2Quiver :=
  (OrientedQuiver.vertexEquiv zigzagA2Graph
    (Orientation.ofLinearOrder zigzagA2Graph)).trans
      (Equiv.ofBijective _ symmetrify_of_obj_bijective)

private theorem vertices_zero : vertices 0 = Symmetrify.of.obj v0 := by
  simp [vertices, v0, OrientedQuiver.vertexEquiv_apply]; rfl

private theorem vertices_one : vertices 1 = Symmetrify.of.obj v1 := by
  simp [vertices, v1, OrientedQuiver.vertexEquiv_apply]; rfl

private theorem vertex_cases (i : Symmetrify preprojectiveA2Quiver) :
    i = Symmetrify.of.obj v0 ∨ i = Symmetrify.of.obj v1 := by
  have hcases : ∀ x : Fin 2, x = 0 ∨ x = 1 := by
    intro x
    fin_cases x <;> simp
  have h := hcases (vertices.symm i)
  rcases h with h | h
  · left
    calc
      i = vertices (vertices.symm i) := (vertices.apply_symm_apply i).symm
      _ = _ := by rw [h, vertices_zero]
  · right
    calc
      i = vertices (vertices.symm i) := (vertices.apply_symm_apply i).symm
      _ = _ := by rw [h, vertices_one]

private theorem doubleArrow_cases {i j : Symmetrify preprojectiveA2Quiver} (e : i ⟶ j) :
    (i = Symmetrify.of.obj v0 ∧ j = Symmetrify.of.obj v1 ∧ HEq e e01) ∨
      (i = Symmetrify.of.obj v1 ∧ j = Symmetrify.of.obj v0 ∧ HEq e e10) := by
  rcases vertex_cases i with rfl | rfl <;> rcases vertex_cases j with rfl | rfl
  · cases e with
    | inl a =>
        have ha : v0 ⟶ v0 := by simpa only [symmetrify_of_obj] using a
        exact isEmptyElim ha
    | inr a =>
        have ha : v0 ⟶ v0 := by simpa only [symmetrify_of_obj] using a
        exact isEmptyElim ha
  · cases e with
    | inl a =>
        simp only [symmetrify_of_obj] at a
        have he : a = a2Arrow := Subsingleton.elim _ _
        exact Or.inl ⟨rfl, rfl, by simp [e01, he]⟩
    | inr a =>
        have ha : v1 ⟶ v0 := by simpa only [symmetrify_of_obj] using a
        exact isEmptyElim ha
  · cases e with
    | inl a =>
        have ha : v1 ⟶ v0 := by simpa only [symmetrify_of_obj] using a
        exact isEmptyElim ha
    | inr a =>
        simp only [symmetrify_of_obj] at a
        have he : a = a2Arrow := Subsingleton.elim _ _
        exact Or.inr ⟨rfl, rfl, by simp [e10, he]⟩
  · cases e with
    | inl a =>
        have ha : v1 ⟶ v1 := by simpa only [symmetrify_of_obj] using a
        exact isEmptyElim ha
    | inr a =>
        have ha : v1 ⟶ v1 := by simpa only [symmetrify_of_obj] using a
        exact isEmptyElim ha

private theorem v0_ne_v1 : (Symmetrify.of.obj v0 : Symmetrify preprojectiveA2Quiver) ≠
    Symmetrify.of.obj v1 := by
  intro h
  have hq : v0 = v1 := (symmetrify_of_obj_bijective (Q := preprojectiveA2Quiver)).1 h
  have h' : (0 : Fin 2) = 1 :=
    (OrientedQuiver.vertexEquiv zigzagA2Graph
      (Orientation.ofLinearOrder zigzagA2Graph)).injective (by
        simpa only [OrientedQuiver.vertexEquiv_apply, v0, v1] using hq)
  exact (by decide : (0 : Fin 2) ≠ 1) h'

private theorem mul_arrows_mem_preprojectiveIdeal (k : Type*) [CommRing k]
    {i j l : Symmetrify preprojectiveA2Quiver} (a : i ⟶ j) (b : j ⟶ l) :
    (ofArrow b * ofArrow a : pathAlgebra k (Symmetrify preprojectiveA2Quiver)) ∈
      preprojectiveIdeal k preprojectiveA2Quiver := by
  rcases doubleArrow_cases a with ⟨hi, hj, ha⟩ | ⟨hi, hj, ha⟩
  · rcases doubleArrow_cases b with ⟨hj', hl, hb⟩ | ⟨hj', hl, hb⟩
    · exact (v0_ne_v1 (hj.symm.trans hj').symm).elim
    · subst i; subst j; subst l
      cases ha
      cases hb
      have h := tailBacktrack_mem_preprojectiveIdeal k
      rw [← ofArrow_reverse_mul_ofArrow_eq_tailBacktrackElem] at h
      rw [Symmetrify.of_map] at h
      -- The backtrack lemma names the original arrow through `Symmetrify.of.map`.
      change ofArrow (Quiver.reverse e01) * ofArrow e01 ∈
        preprojectiveIdeal k preprojectiveA2Quiver at h
      rw [reverse_e01] at h
      exact h
  · rcases doubleArrow_cases b with ⟨hj', hl, hb⟩ | ⟨hj', hl, hb⟩
    · subst i; subst j; subst l
      cases ha
      cases hb
      have h := headBacktrack_mem_preprojectiveIdeal k
      rw [← ofArrow_mul_ofArrow_reverse_eq_headBacktrackElem] at h
      rw [Symmetrify.of_map] at h
      -- The backtrack lemma names the original arrow through `Symmetrify.of.map`.
      change ofArrow e01 * ofArrow (Quiver.reverse e01) ∈
        preprojectiveIdeal k preprojectiveA2Quiver at h
      rw [reverse_e01] at h
      exact h
    · exact (v0_ne_v1 (hj'.symm.trans hj).symm).elim

private theorem arrowIdeal_sq_le_preprojectiveIdeal (k : Type*) [CommRing k] :
    arrowIdeal k (Symmetrify preprojectiveA2Quiver) ^ 2 ≤
      (preprojectiveIdeal k preprojectiveA2Quiver).asIdeal := by
  have hpow : arrowIdeal k (Symmetrify preprojectiveA2Quiver) ^ 2 =
      arrowIdeal k (Symmetrify preprojectiveA2Quiver) *
        arrowIdeal k (Symmetrify preprojectiveA2Quiver) := by
    simpa only [Submodule.pow_one] using
      (Submodule.pow_succ (arrowIdeal k (Symmetrify preprojectiveA2Quiver)) (n := 1))
  let S : Set (pathAlgebra k (Symmetrify preprojectiveA2Quiver)) :=
    Set.range fun e : Σ a b : Symmetrify preprojectiveA2Quiver, a ⟶ b => ofArrow e.2.2
  have htwo : (Ideal.span S).IsTwoSided := by
    dsimp [S]
    rw [← arrowIdeal_eq_span_arrows]
    infer_instance
  have hspan := @Ideal.span_mul_span (pathAlgebra k (Symmetrify preprojectiveA2Quiver)) _ S S htwo
  rw [hpow, arrowIdeal_eq_span_arrows]
  -- Name the common generator set so the span-product theorem can be applied explicitly.
  change Ideal.span S * Ideal.span S ≤ (preprojectiveIdeal k preprojectiveA2Quiver).asIdeal
  rw [hspan]
  refine Ideal.span_le.mpr ?_
  rintro x ⟨a, ⟨⟨i, j, e⟩, rfl⟩, b, ⟨⟨i', j', e'⟩, rfl⟩, rfl⟩
  by_cases h : j' = i
  · subst j'
    exact mul_arrows_mem_preprojectiveIdeal k e' e
  · -- The set product from `Ideal.span_mul_span` is the displayed product of two arrows.
    change (ofArrow e * ofArrow e' : pathAlgebra k (Symmetrify preprojectiveA2Quiver)) ∈
      (preprojectiveIdeal k preprojectiveA2Quiver).asIdeal
    rw [ofArrow_eq_ofPath, ofArrow_eq_ofPath,
      ofPath_mul_ofPath_of_not_composable h]
    exact Submodule.zero_mem _

/-- **The preprojective relation ideal of `A₂` is the square of the arrow ideal.** The two
local relations kill the two backtracks, which are all the paths of length two in the doubled
one-edge quiver. -/
@[simp]
theorem preprojectiveIdeal_A2_eq_arrowIdeal_sq (k : Type*) [CommRing k] :
    (preprojectiveIdeal k preprojectiveA2Quiver).asIdeal =
      arrowIdeal k (Symmetrify preprojectiveA2Quiver) ^ 2 :=
  le_antisymm (preprojectiveIdeal_le_arrowIdeal_sq k)
    (arrowIdeal_sq_le_preprojectiveIdeal k)

/-- **The `A₂` preprojective relation ideal is admissible.** -/
theorem isAdmissibleIdeal_preprojectiveIdeal_A2 (k : Type*) [CommRing k] :
    IsAdmissibleIdeal (preprojectiveIdeal k preprojectiveA2Quiver).asIdeal where
  exists_arrowIdeal_pow_le := ⟨2, (preprojectiveIdeal_A2_eq_arrowIdeal_sq k).ge⟩
  le_arrowIdeal_sq := (preprojectiveIdeal_A2_eq_arrowIdeal_sq k).le

/-- **The preprojective algebra of `A₂` is the arrow-ideal-square-zero quotient** of its doubled
path algebra. -/
noncomputable def preprojectiveAlgebraEquivA2 (k : Type*) [CommRing k] :
    preprojectiveAlgebra k preprojectiveA2Quiver ≃ₐ[k]
      pathAlgebra k (Symmetrify preprojectiveA2Quiver) ⧸
        arrowIdeal k (Symmetrify preprojectiveA2Quiver) ^ 2 :=
  Ideal.quotientEquivAlgOfEq k (preprojectiveIdeal_A2_eq_arrowIdeal_sq k)

/-- The `A₂` presentation sends a class to the same path-algebra representative in the
arrow-ideal-square-zero quotient. -/
@[simp]
theorem preprojectiveAlgebraEquivA2_preprojectiveMk (k : Type*) [CommRing k]
    (x : pathAlgebra k (Symmetrify preprojectiveA2Quiver)) :
    preprojectiveAlgebraEquivA2 k (preprojectiveMk k preprojectiveA2Quiver x) =
      Ideal.Quotient.mk (arrowIdeal k (Symmetrify preprojectiveA2Quiver) ^ 2) x := by
  rw [preprojectiveMk_apply, preprojectiveAlgebraEquivA2]
  exact Ideal.quotientEquivAlgOfEq_mk k (preprojectiveIdeal_A2_eq_arrowIdeal_sq k) x

/-- **The `A₂` preprojective algebra is finite-dimensional** over every field. -/
noncomputable instance instFiniteDimensionalPreprojectiveAlgebraA2 (k : Type*) [Field k] :
    FiniteDimensional k (preprojectiveAlgebra k preprojectiveA2Quiver) :=
  (isAdmissibleIdeal_preprojectiveIdeal_A2 k).finiteDimensional_quotient

end TauCeti
