/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Admissible
public import TauCeti.RepresentationTheory.Quiver.AdmissibleIdeal.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Truncation
public import TauCeti.RepresentationTheory.Quiver.Zigzag.ADE.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Orientation

/-!
# The preprojective algebra of `A₂`

The doubled one-arrow quiver has two length-two paths, one backtrack at each vertex. Its local
preprojective relations kill both paths, so the preprojective algebra is the arrow-ideal-square-zero
quotient. In particular it is finite-dimensional over any field.

Over any commutative ring this quotient is free on the two vertex idempotents and the two
oppositely oriented arrows, `TauCeti.preprojectiveA2Basis`; the products of these basis vectors are
recorded by `TauCeti.preprojectiveA2Basis_mul`.

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

/-- The vertex `0` of the chosen `A₂` orientation. -/
abbrev preprojectiveA2VertexZero : preprojectiveA2Quiver := OrientedQuiver.vertex zigzagA2Graph
  (Orientation.ofLinearOrder zigzagA2Graph) 0

/-- The vertex `1` of the chosen `A₂` orientation. -/
abbrev preprojectiveA2VertexOne : preprojectiveA2Quiver := OrientedQuiver.vertex zigzagA2Graph
  (Orientation.ofLinearOrder zigzagA2Graph) 1

/-- The unique arrow from vertex `0` to vertex `1` in the chosen `A₂` orientation. -/
def preprojectiveA2Arrow : (OrientedQuiver.vertex zigzagA2Graph
    (Orientation.ofLinearOrder zigzagA2Graph) 0 ⟶
    OrientedQuiver.vertex zigzagA2Graph
    (Orientation.ofLinearOrder zigzagA2Graph) 1) :=
  OrientedQuiver.arrow zigzagA2Graph (Orientation.ofLinearOrder zigzagA2Graph)
    ((zigzagA2Graph_adj 0 1).2 (by decide)) (by
      simpa only [Orientation.mem_ofLinearOrder_iff] using (show (0 : Fin 2) < 1 by decide))

instance : IsEmpty (preprojectiveA2VertexZero ⟶ preprojectiveA2VertexZero) := by
  constructor
  intro e
  have h : zigzagA2Graph.Adj 0 0 := by
    simpa only [OrientedQuiver.vertexEquiv_symm_vertex] using e.1
  exact (zigzagA2Graph_adj 0 0).mp h (by decide)

instance : IsEmpty (preprojectiveA2VertexOne ⟶ preprojectiveA2VertexZero) := by
  constructor
  intro e
  have h : (1 : Fin 2) < 0 := by
    simpa only [OrientedQuiver.vertexEquiv_symm_vertex,
      Orientation.mem_ofLinearOrder_iff] using e.2
  omega

instance : IsEmpty (preprojectiveA2VertexOne ⟶ preprojectiveA2VertexOne) := by
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
    ∑ i : preprojectiveA2Quiver, f i = f preprojectiveA2VertexZero +
      f preprojectiveA2VertexOne := by
  let e := OrientedQuiver.vertexEquiv zigzagA2Graph
    (Orientation.ofLinearOrder zigzagA2Graph)
  calc
    _ = ∑ i : Fin 2, f (e i) :=
      (Fintype.sum_equiv e (fun i => f (e i)) f (fun _ => rfl)).symm
    _ = _ := by simp [Fin.sum_univ_two, e, preprojectiveA2VertexZero,
      preprojectiveA2VertexOne]

private theorem localPreprojectiveRelator_zero (k : Type*) [CommRing k] :
    localPreprojectiveRelator k preprojectiveA2VertexZero =
      -tailBacktrackElem k preprojectiveA2Arrow := by
  rw [localPreprojectiveRelator_def, sum_a2, sum_a2]
  simp [Fintype.sum_subsingleton
    (fun a : preprojectiveA2VertexZero ⟶ preprojectiveA2VertexOne =>
      tailBacktrackElem k a) preprojectiveA2Arrow]

private theorem localPreprojectiveRelator_one (k : Type*) [CommRing k] :
    localPreprojectiveRelator k preprojectiveA2VertexOne =
      headBacktrackElem k preprojectiveA2Arrow := by
  rw [localPreprojectiveRelator_def, sum_a2, sum_a2]
  simp [Fintype.sum_subsingleton
    (fun a : preprojectiveA2VertexZero ⟶ preprojectiveA2VertexOne =>
      headBacktrackElem k a) preprojectiveA2Arrow]

private theorem tailBacktrack_mem_preprojectiveIdeal (k : Type*) [CommRing k] :
    tailBacktrackElem k preprojectiveA2Arrow ∈
      preprojectiveIdeal k preprojectiveA2Quiver := by
  have h := localPreprojectiveRelator_mem_preprojectiveIdeal k preprojectiveA2VertexZero
  rw [localPreprojectiveRelator_zero] at h
  exact neg_mem_iff.mp h

private theorem headBacktrack_mem_preprojectiveIdeal (k : Type*) [CommRing k] :
    headBacktrackElem k preprojectiveA2Arrow ∈
      preprojectiveIdeal k preprojectiveA2Quiver := by
  rw [← localPreprojectiveRelator_one]
  exact localPreprojectiveRelator_mem_preprojectiveIdeal k preprojectiveA2VertexOne

/-- The forward arrow in the doubled `A₂` quiver. -/
def preprojectiveA2ForwardArrow : (Symmetrify.of.obj preprojectiveA2VertexZero ⟶
    Symmetrify.of.obj preprojectiveA2VertexOne) := Sum.inl preprojectiveA2Arrow

/-- The reverse arrow in the doubled `A₂` quiver. -/
def preprojectiveA2ReverseArrow : (Symmetrify.of.obj preprojectiveA2VertexOne ⟶
    Symmetrify.of.obj preprojectiveA2VertexZero) := Sum.inr preprojectiveA2Arrow

/-- The formal reverse of the forward arrow is the reverse arrow. Not a simp lemma: simp rewrites
the left side with Mathlib's `Quiver.symmetrify_reverse`. -/
theorem reverse_preprojectiveA2ForwardArrow :
    Quiver.reverse preprojectiveA2ForwardArrow = preprojectiveA2ReverseArrow := by
  simp [preprojectiveA2ForwardArrow, preprojectiveA2ReverseArrow, symmetrify_reverse]
  rfl

/-- The formal reverse of the reverse arrow is the forward arrow. Not a simp lemma, for the same
reason as `TauCeti.reverse_preprojectiveA2ForwardArrow`. -/
theorem reverse_preprojectiveA2ReverseArrow :
    Quiver.reverse preprojectiveA2ReverseArrow = preprojectiveA2ForwardArrow := by
  rw [← reverse_preprojectiveA2ForwardArrow, Quiver.reverse_reverse]

/-- The two vertices of the doubled `A₂` quiver. -/
noncomputable def preprojectiveA2DoubledVertexEquiv :
    Fin 2 ≃ Symmetrify preprojectiveA2Quiver :=
  (OrientedQuiver.vertexEquiv zigzagA2Graph
    (Orientation.ofLinearOrder zigzagA2Graph)).trans
      (Equiv.ofBijective _ symmetrify_of_obj_bijective)

/-- The vertex numbered zero under `TauCeti.preprojectiveA2DoubledVertexEquiv`. -/
@[simp]
theorem preprojectiveA2DoubledVertexEquiv_zero :
    preprojectiveA2DoubledVertexEquiv 0 = Symmetrify.of.obj preprojectiveA2VertexZero := by
  simp [preprojectiveA2DoubledVertexEquiv, preprojectiveA2VertexZero,
    OrientedQuiver.vertexEquiv_apply]
  rfl

/-- The vertex numbered one under `TauCeti.preprojectiveA2DoubledVertexEquiv`. -/
@[simp]
theorem preprojectiveA2DoubledVertexEquiv_one :
    preprojectiveA2DoubledVertexEquiv 1 = Symmetrify.of.obj preprojectiveA2VertexOne := by
  simp [preprojectiveA2DoubledVertexEquiv, preprojectiveA2VertexOne,
    OrientedQuiver.vertexEquiv_apply]
  rfl

/-- The inverse vertex equivalence sends the doubled vertex zero to zero. Not a simp lemma: simp
rewrites the left side with Mathlib's `Quiver.Symmetrify.of_obj`. -/
theorem preprojectiveA2DoubledVertexEquiv_symm_zero :
    preprojectiveA2DoubledVertexEquiv.symm (Symmetrify.of.obj preprojectiveA2VertexZero) = 0 :=
  (Equiv.symm_apply_eq _).2 preprojectiveA2DoubledVertexEquiv_zero.symm

/-- The inverse vertex equivalence sends the doubled vertex one to one. Not a simp lemma, for the
same reason as `TauCeti.preprojectiveA2DoubledVertexEquiv_symm_zero`. -/
theorem preprojectiveA2DoubledVertexEquiv_symm_one :
    preprojectiveA2DoubledVertexEquiv.symm (Symmetrify.of.obj preprojectiveA2VertexOne) = 1 :=
  (Equiv.symm_apply_eq _).2 preprojectiveA2DoubledVertexEquiv_one.symm

/-- Every vertex of the doubled `A₂` quiver is one of its two named vertices. -/
theorem preprojectiveA2DoubledVertex_cases (i : Symmetrify preprojectiveA2Quiver) :
    i = Symmetrify.of.obj preprojectiveA2VertexZero ∨
      i = Symmetrify.of.obj preprojectiveA2VertexOne := by
  have hcases : ∀ x : Fin 2, x = 0 ∨ x = 1 := by
    intro x
    fin_cases x <;> simp
  have h := hcases (preprojectiveA2DoubledVertexEquiv.symm i)
  rcases h with h | h
  · left
    calc
      i = preprojectiveA2DoubledVertexEquiv
          (preprojectiveA2DoubledVertexEquiv.symm i) :=
        (preprojectiveA2DoubledVertexEquiv.apply_symm_apply i).symm
      _ = _ := by rw [h, preprojectiveA2DoubledVertexEquiv_zero]
  · right
    calc
      i = preprojectiveA2DoubledVertexEquiv
          (preprojectiveA2DoubledVertexEquiv.symm i) :=
        (preprojectiveA2DoubledVertexEquiv.apply_symm_apply i).symm
      _ = _ := by rw [h, preprojectiveA2DoubledVertexEquiv_one]

/-- Every arrow of the doubled `A₂` quiver is its forward or reverse arrow. -/
theorem preprojectiveA2DoubledArrow_cases
    {i j : Symmetrify preprojectiveA2Quiver} (e : i ⟶ j) :
    (i = Symmetrify.of.obj preprojectiveA2VertexZero ∧
      j = Symmetrify.of.obj preprojectiveA2VertexOne ∧
        HEq e preprojectiveA2ForwardArrow) ∨
      (i = Symmetrify.of.obj preprojectiveA2VertexOne ∧
        j = Symmetrify.of.obj preprojectiveA2VertexZero ∧
          HEq e preprojectiveA2ReverseArrow) := by
  rcases preprojectiveA2DoubledVertex_cases i with rfl | rfl <;>
    rcases preprojectiveA2DoubledVertex_cases j with rfl | rfl
  · cases e with
    | inl a =>
        have ha : preprojectiveA2VertexZero ⟶ preprojectiveA2VertexZero := by
          simpa only [symmetrify_of_obj] using a
        exact isEmptyElim ha
    | inr a =>
        have ha : preprojectiveA2VertexZero ⟶ preprojectiveA2VertexZero := by
          simpa only [symmetrify_of_obj] using a
        exact isEmptyElim ha
  · cases e with
    | inl a =>
        simp only [symmetrify_of_obj] at a
        have he : a = preprojectiveA2Arrow := Subsingleton.elim _ _
        exact Or.inl ⟨rfl, rfl, by simp [preprojectiveA2ForwardArrow, he]⟩
    | inr a =>
        have ha : preprojectiveA2VertexOne ⟶ preprojectiveA2VertexZero := by
          simpa only [symmetrify_of_obj] using a
        exact isEmptyElim ha
  · cases e with
    | inl a =>
        have ha : preprojectiveA2VertexOne ⟶ preprojectiveA2VertexZero := by
          simpa only [symmetrify_of_obj] using a
        exact isEmptyElim ha
    | inr a =>
        simp only [symmetrify_of_obj] at a
        have he : a = preprojectiveA2Arrow := Subsingleton.elim _ _
        exact Or.inr ⟨rfl, rfl, by simp [preprojectiveA2ReverseArrow, he]⟩
  · cases e with
    | inl a =>
        have ha : preprojectiveA2VertexOne ⟶ preprojectiveA2VertexOne := by
          simpa only [symmetrify_of_obj] using a
        exact isEmptyElim ha
    | inr a =>
        have ha : preprojectiveA2VertexOne ⟶ preprojectiveA2VertexOne := by
          simpa only [symmetrify_of_obj] using a
        exact isEmptyElim ha

/-- The two vertices of the doubled `A₂` quiver are distinct. -/
theorem preprojectiveA2DoubledVertexZero_ne_one :
    (Symmetrify.of.obj preprojectiveA2VertexZero : Symmetrify preprojectiveA2Quiver) ≠
      Symmetrify.of.obj preprojectiveA2VertexOne := by
  intro h
  have hq : preprojectiveA2VertexZero = preprojectiveA2VertexOne :=
    (symmetrify_of_obj_bijective (Q := preprojectiveA2Quiver)).1 h
  have h' : (0 : Fin 2) = 1 :=
    (OrientedQuiver.vertexEquiv zigzagA2Graph
      (Orientation.ofLinearOrder zigzagA2Graph)).injective (by
        simpa only [OrientedQuiver.vertexEquiv_apply, preprojectiveA2VertexZero,
          preprojectiveA2VertexOne] using hq)
  exact (by decide : (0 : Fin 2) ≠ 1) h'

private theorem mul_arrows_mem_preprojectiveIdeal (k : Type*) [CommRing k]
    {i j l : Symmetrify preprojectiveA2Quiver} (a : i ⟶ j) (b : j ⟶ l) :
    (ofArrow b * ofArrow a : pathAlgebra k (Symmetrify preprojectiveA2Quiver)) ∈
      preprojectiveIdeal k preprojectiveA2Quiver := by
  rcases preprojectiveA2DoubledArrow_cases a with ⟨hi, hj, ha⟩ | ⟨hi, hj, ha⟩
  · rcases preprojectiveA2DoubledArrow_cases b with ⟨hj', hl, hb⟩ | ⟨hj', hl, hb⟩
    · exact (preprojectiveA2DoubledVertexZero_ne_one (hj.symm.trans hj').symm).elim
    · subst i; subst j; subst l
      cases ha
      cases hb
      have h := tailBacktrack_mem_preprojectiveIdeal k
      rw [← ofArrow_reverse_mul_ofArrow_eq_tailBacktrackElem] at h
      rw [Symmetrify.of_map] at h
      -- The backtrack lemma names the original arrow through `Symmetrify.of.map`.
      change ofArrow (Quiver.reverse preprojectiveA2ForwardArrow) *
        ofArrow preprojectiveA2ForwardArrow ∈
        preprojectiveIdeal k preprojectiveA2Quiver at h
      rw [reverse_preprojectiveA2ForwardArrow] at h
      exact h
  · rcases preprojectiveA2DoubledArrow_cases b with ⟨hj', hl, hb⟩ | ⟨hj', hl, hb⟩
    · subst i; subst j; subst l
      cases ha
      cases hb
      have h := headBacktrack_mem_preprojectiveIdeal k
      rw [← ofArrow_mul_ofArrow_reverse_eq_headBacktrackElem] at h
      rw [Symmetrify.of_map] at h
      -- The backtrack lemma names the original arrow through `Symmetrify.of.map`.
      change ofArrow preprojectiveA2ForwardArrow *
        ofArrow (Quiver.reverse preprojectiveA2ForwardArrow) ∈
        preprojectiveIdeal k preprojectiveA2Quiver at h
      rw [reverse_preprojectiveA2ForwardArrow] at h
      exact h
    · exact (preprojectiveA2DoubledVertexZero_ne_one (hj'.symm.trans hj).symm).elim

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

/-! ### The path basis -/

private def a2ShortPath : Fin 4 → ShortPath (Symmetrify preprojectiveA2Quiver) 2
  | 0 => ⟨⟨Symmetrify.of.obj preprojectiveA2VertexZero,
      Symmetrify.of.obj preprojectiveA2VertexZero, .nil⟩, by simp⟩
  | 1 => ⟨⟨Symmetrify.of.obj preprojectiveA2VertexOne,
      Symmetrify.of.obj preprojectiveA2VertexOne, .nil⟩, by simp⟩
  | 2 => ⟨⟨Symmetrify.of.obj preprojectiveA2VertexZero,
      Symmetrify.of.obj preprojectiveA2VertexOne, preprojectiveA2ForwardArrow.toPath⟩, by simp⟩
  | 3 => ⟨⟨Symmetrify.of.obj preprojectiveA2VertexOne,
      Symmetrify.of.obj preprojectiveA2VertexZero, preprojectiveA2ReverseArrow.toPath⟩, by simp⟩

private theorem a2ShortPath_injective : Function.Injective a2ShortPath := by
  intro i j h
  apply Fin.ext
  have hc := congrArg
    (fun x : ShortPath (Symmetrify preprojectiveA2Quiver) 2 =>
      2 * x.1.2.2.length + (preprojectiveA2DoubledVertexEquiv.symm x.1.1).val) h
  fin_cases i <;> fin_cases j <;>
    simp only [a2ShortPath, preprojectiveA2DoubledVertexEquiv_symm_zero,
      preprojectiveA2DoubledVertexEquiv_symm_one] at hc <;>
    simp at hc ⊢

private theorem a2ShortPath_surjective : Function.Surjective a2ShortPath := by
  rintro ⟨⟨i, j, p⟩, hp⟩
  dsimp only at hp
  have hlen : p.length = 0 ∨ p.length = 1 := by omega
  rcases hlen with hlen | hlen
  · obtain rfl := Path.eq_of_length_zero p hlen
    obtain rfl := Path.eq_nil_of_length_zero p hlen
    rcases preprojectiveA2DoubledVertex_cases i with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · obtain ⟨c, e, q, hq, rfl⟩ := Path.eq_toPath_comp_of_length_eq_succ p hlen
    obtain rfl := Path.eq_of_length_zero q hq
    obtain rfl := Path.eq_nil_of_length_zero q hq
    rcases preprojectiveA2DoubledArrow_cases e with
      ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩
    · cases he
      exact ⟨2, rfl⟩
    · cases he
      exact ⟨3, rfl⟩

private theorem a2ShortPath_bijective : Function.Bijective a2ShortPath :=
  ⟨a2ShortPath_injective, a2ShortPath_surjective⟩

private noncomputable def a2ShortPathEquiv :
    Fin 4 ≃ ShortPath (Symmetrify preprojectiveA2Quiver) 2 :=
  Equiv.ofBijective a2ShortPath a2ShortPath_bijective

section Basis

variable (k : Type*) [CommRing k]

/-- The basis of the `A₂` preprojective algebra consisting, in order, of the vertex at `0`, the
vertex at `1`, the arrow `0 → 1`, and its formal reverse `1 → 0`. -/
noncomputable def preprojectiveA2Basis :
    Module.Basis (Fin 4) k (preprojectiveAlgebra k preprojectiveA2Quiver) :=
  (((arrowIdealQuotientBasis k (Symmetrify preprojectiveA2Quiver) 2).reindex
    a2ShortPathEquiv.symm).map (preprojectiveAlgebraEquivA2 k).symm.toLinearEquiv)

private theorem preprojectiveA2Basis_apply (i : Fin 4) :
    preprojectiveA2Basis k i =
      preprojectiveMk k preprojectiveA2Quiver (ofPath (a2ShortPath i).1) := by
  rw [preprojectiveA2Basis, Module.Basis.map_apply, Module.Basis.reindex_apply,
    Equiv.symm_symm, AlgEquiv.toLinearEquiv_apply]
  apply (preprojectiveAlgebraEquivA2 k).injective
  rw [AlgEquiv.apply_symm_apply, arrowIdealQuotientBasis_apply,
    preprojectiveAlgebraEquivA2_preprojectiveMk, a2ShortPathEquiv, Equiv.ofBijective_apply]

/-- The first basis vector is the trivial path at vertex zero. -/
theorem preprojectiveA2Basis_zero :
    preprojectiveA2Basis k 0 =
      preprojectiveMk k preprojectiveA2Quiver
        (ofPath ⟨Symmetrify.of.obj preprojectiveA2VertexZero,
          Symmetrify.of.obj preprojectiveA2VertexZero, .nil⟩) := by
  simpa [a2ShortPath] using preprojectiveA2Basis_apply k (0 : Fin 4)

/-- The second basis vector is the trivial path at vertex one. -/
theorem preprojectiveA2Basis_one :
    preprojectiveA2Basis k 1 =
      preprojectiveMk k preprojectiveA2Quiver
        (ofPath ⟨Symmetrify.of.obj preprojectiveA2VertexOne,
          Symmetrify.of.obj preprojectiveA2VertexOne, .nil⟩) := by
  simpa [a2ShortPath] using preprojectiveA2Basis_apply k (1 : Fin 4)

/-- The third basis vector is the forward arrow. -/
theorem preprojectiveA2Basis_two :
    preprojectiveA2Basis k 2 = preprojectiveMk k preprojectiveA2Quiver
      (ofPath ⟨Symmetrify.of.obj preprojectiveA2VertexZero,
        Symmetrify.of.obj preprojectiveA2VertexOne,
          preprojectiveA2ForwardArrow.toPath⟩) := by
  simpa [a2ShortPath] using preprojectiveA2Basis_apply k (2 : Fin 4)

/-- The fourth basis vector is the reverse arrow. -/
theorem preprojectiveA2Basis_three :
    preprojectiveA2Basis k 3 = preprojectiveMk k preprojectiveA2Quiver
      (ofPath ⟨Symmetrify.of.obj preprojectiveA2VertexOne,
        Symmetrify.of.obj preprojectiveA2VertexZero,
          preprojectiveA2ReverseArrow.toPath⟩) := by
  simpa [a2ShortPath] using preprojectiveA2Basis_apply k (3 : Fin 4)

/-- Paths of length at least two vanish in the `A₂` preprojective algebra. -/
theorem preprojectiveMk_A2_ofPath_eq_zero_of_two_le
    (p : Quiver.TotalPath (Symmetrify preprojectiveA2Quiver)) (hp : 2 ≤ p.2.2.length) :
    preprojectiveMk k preprojectiveA2Quiver (ofPath p) = 0 := by
  rw [preprojectiveMk_eq_zero_iff, ← TwoSidedIdeal.mem_asIdeal,
    preprojectiveIdeal_A2_eq_arrowIdeal_sq]
  exact Ideal.pow_le_pow_right hp (ofPath_mem_arrowIdeal_pow p)

/-- The partial multiplication operation on indices of `TauCeti.preprojectiveA2Basis`; `none`
means that the product is zero. -/
def preprojectiveA2BasisMul : Fin 4 → Fin 4 → Option (Fin 4)
  | 0, 0 => some 0
  | 0, 3 => some 3
  | 1, 1 => some 1
  | 1, 2 => some 2
  | 2, 0 => some 2
  | 3, 1 => some 3
  | _, _ => none

/-- The partial multiplication table evaluated on the sixteen pairs of basis indices. -/
@[simp]
theorem preprojectiveA2BasisMul_apply (i j : Fin 4) :
    preprojectiveA2BasisMul i j = ![![some 0, none, none, some 3], ![none, some 1, some 2, none],
      ![some 2, none, none, none], ![none, some 3, none, none]] i j := by
  fin_cases i <;> fin_cases j <;> rfl

/-- The multiplication table of `TauCeti.preprojectiveA2Basis`. -/
@[simp]
theorem preprojectiveA2Basis_mul (i j : Fin 4) :
    preprojectiveA2Basis k i * preprojectiveA2Basis k j =
      (preprojectiveA2BasisMul i j).elim 0 (preprojectiveA2Basis k) := by
  fin_cases i <;> fin_cases j <;>
    simp only [preprojectiveA2BasisMul, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Fin.isValue, Option.elim_some, Option.elim_none]
  all_goals simp only [preprojectiveA2Basis_apply, a2ShortPath]
  all_goals rw [← map_mul]
  all_goals first
    | rw [ofPath_mul_ofPath_of_not_composable preprojectiveA2DoubledVertexZero_ne_one, map_zero]
    | rw [ofPath_mul_ofPath_of_not_composable preprojectiveA2DoubledVertexZero_ne_one.symm,
        map_zero]
    | rw [ofPath_mul_ofPath_of_comp, Path.comp_nil]
    | rw [ofPath_mul_ofPath_of_comp, Path.nil_comp]
    | (rw [ofPath_mul_ofPath_of_comp]
       exact preprojectiveMk_A2_ofPath_eq_zero_of_two_le k _ (by simp))

end Basis

/-- **The `A₂` preprojective algebra is finite-dimensional** over every field. -/
noncomputable instance instFiniteDimensionalPreprojectiveAlgebraA2 (k : Type*) [Field k] :
    FiniteDimensional k (preprojectiveAlgebra k preprojectiveA2Quiver) :=
  (isAdmissibleIdeal_preprojectiveIdeal_A2 k).finiteDimensional_quotient

end TauCeti
