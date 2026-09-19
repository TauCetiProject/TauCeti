/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Topology
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Picard.Torsion.Basic
public import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Bounding prime torsion by the topological genus

Let `T` be a numerical type with `n` components, intersection matrix `A` and multiplicities `mᵢ`,
and let `e` be the number of edges of its intersection graph, so that the topological genus
`g_top = 1 - n + e` is the first Betti number of that graph. This file proves that for a prime `ℓ`
dividing no multiplicity and no intersection number of two distinct meeting components,

`dim_{𝔽_ℓ} Coker(A)[ℓ] ≤ g_top` and hence `dim_{𝔽_ℓ} Pic(T)[ℓ] ≤ g_top`,

the second bound following from the first through the injection `Pic(T) → Coker(A)`
([Stacks, Tag 0CE7](https://stacks.math.columbia.edu/tag/0CE7)). This is
[Stacks, Lemma 55.2.6](https://stacks.math.columbia.edu/tag/0C6X), the combinatorial input for the
bound `dim Pic(T)[ℓ] ≤ g_top` on minimal numerical types in
[Stacks, Proposition 55.7.4](https://stacks.math.columbia.edu/tag/0C9X), which in turn is what
forces a reduced nodal special fibre in the proof of semistable reduction.

## Main results

* `TauCeti.NumericalType.finrank_cokerTorsion_le_topologicalGenus`:
  `dim_{𝔽_ℓ} Coker(A)[ℓ] ≤ g_top`.
* `TauCeti.NumericalType.finrank_torsion_le_topologicalGenus`: `dim_{𝔽_ℓ} Pic(T)[ℓ] ≤ g_top`.

## Implementation notes

The Stacks Project argues with dual lattices. The proof here is instead linear algebra over
`𝔽_ℓ`, in two steps.

* Lifting kernel vectors of `A` modulo `ℓ` to `ℤ` and dividing their images under `A` by `ℓ`
  gives a surjection from the kernel of `A` over `𝔽_ℓ` onto `Coker(A)[ℓ]`. It kills the
  multiplicity vector, which is nonzero modulo `ℓ`, so
  `dim Coker(A)[ℓ] + 1 ≤ dim ker (A mod ℓ)`.
* Rescaling by the multiplicities, which are units modulo `ℓ`, turns `A` into the Laplacian
  `Bᵀ W B` of the intersection graph, where `B` is an oriented incidence matrix and `W` is the
  diagonal matrix of the edge weights `-mᵢ aᵢⱼ mⱼ`, again units modulo `ℓ`. Connectedness gives
  `rank B ≥ n - 1`, and Sylvester's rank inequality
  `Matrix.rank_add_rank_le_rank_mul_add_card` then gives `rank (A mod ℓ) ≥ 2(n - 1) - e`.

Together these give `dim Coker(A)[ℓ] ≤ n - rank (A mod ℓ) - 1 ≤ 1 - n + e`.
-/

public section

namespace TauCeti

open Matrix

namespace NumericalType

universe u

variable {T : NumericalType.{u}} {ℓ : ℕ}

/-! ### Torsion classes from the kernel of the intersection matrix modulo `ℓ` -/

/-- Two solutions of `ℓ q = y A` whose `y` agree modulo `ℓ` define the same class in
`Coker(A)`. -/
private lemma mk_eq_mk_of_intCast_eq (hℓ : ℓ ≠ 0) {y y' q q' : T.Component → ℤ}
    (hq : (ℓ : ℤ) • q = y ᵥ* T.intersection) (hq' : (ℓ : ℤ) • q' = y' ᵥ* T.intersection)
    (hy : ∀ i, (y i : ZMod ℓ) = y' i) :
    (Submodule.Quotient.mk q : T.Coker) = Submodule.Quotient.mk q' := by
  have hdvd : ∀ i, (ℓ : ℤ) ∣ y i - y' i := fun i ↦
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (hy i).symm
  choose z hz using hdvd
  rw [Submodule.Quotient.eq, mem_intersectionRelations_iff]
  refine ⟨z, smul_right_injective (T.Component → ℤ) (r := (ℓ : ℤ)) (by exact_mod_cast hℓ) ?_⟩
  simp only
  rw [smul_sub, hq, hq', ← sub_vecMul, ← smul_vecMul]
  congr 1
  funext i
  simp [hz i]

/-- The integral lift of a vector modulo `ℓ`. -/
private def intLift (x : T.Component → ZMod ℓ) : T.Component → ℤ :=
  fun i ↦ (x i).cast

private lemma intCast_intLift (x : T.Component → ZMod ℓ) (i : T.Component) :
    ((intLift x i : ℤ) : ZMod ℓ) = x i :=
  ZMod.intCast_zmod_cast (x i)

/-- The intersection matrix reduced modulo `ℓ`. -/
private abbrev intersectionMod (T : NumericalType.{u}) (ℓ : ℕ) :
    Matrix T.Component T.Component (ZMod ℓ) :=
  T.intersection.map (Int.castRingHom (ZMod ℓ))

private lemma intCast_vecMul (y : T.Component → ℤ) (j : T.Component) :
    (((y ᵥ* T.intersection) j : ℤ) : ZMod ℓ) =
      ((fun i ↦ (y i : ZMod ℓ)) ᵥ* intersectionMod T ℓ) j :=
  RingHom.map_vecMul (Int.castRingHom (ZMod ℓ)) T.intersection y j

private lemma dvd_intLift_vecMul {x : T.Component → ZMod ℓ}
    (hx : x ∈ LinearMap.ker (intersectionMod T ℓ).vecMulLinear) (j : T.Component) :
    (ℓ : ℤ) ∣ (intLift x ᵥ* T.intersection) j := by
  rw [LinearMap.mem_ker, vecMulLinear_apply] at hx
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, intCast_vecMul, funext (intCast_intLift x), hx,
    Pi.zero_apply]

/-- The quotient `(y A) / ℓ` attached to a kernel vector `x` of `A` modulo `ℓ`, with `y` the
integral lift of `x`. -/
private def liftQuot (x : T.Component → ZMod ℓ) : T.Component → ℤ :=
  fun j ↦ (intLift x ᵥ* T.intersection) j / ℓ

private lemma smul_liftQuot {x : T.Component → ZMod ℓ}
    (hx : x ∈ LinearMap.ker (intersectionMod T ℓ).vecMulLinear) :
    (ℓ : ℤ) • liftQuot x = intLift x ᵥ* T.intersection := by
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, liftQuot]
  exact Int.mul_ediv_cancel' (dvd_intLift_vecMul hx j)

private lemma mem_cokerTorsion_mk_iff {q : T.Component → ℤ} :
    (Submodule.Quotient.mk q : T.Coker) ∈ T.cokerTorsion ℓ ↔
      ∃ y, y ᵥ* T.intersection = (ℓ : ℤ) • q := by
  rw [AddSubgroup.torsionBy.nsmul_iff, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero, mem_intersectionRelations_iff, ← Nat.cast_smul_eq_nsmul ℤ]

variable (T ℓ) in
/-- The torsion class `[(y A) / ℓ]` of `Coker(A)` attached to a kernel vector of the intersection
matrix modulo `ℓ`, where `y` is any integral lift of that vector. -/
private noncomputable def kerToCokerTorsion (hℓ : ℓ ≠ 0) :
    LinearMap.ker (intersectionMod T ℓ).vecMulLinear →+ T.cokerTorsion ℓ where
  toFun x := ⟨Submodule.Quotient.mk (liftQuot x.1),
    mem_cokerTorsion_mk_iff.2 ⟨_, (smul_liftQuot x.2).symm⟩⟩
  map_zero' := by
    refine Subtype.ext (mk_eq_mk_of_intCast_eq hℓ (smul_liftQuot (zero_mem _))
      (y' := 0) (q' := 0) (by simp) fun i ↦ ?_)
    simp [intCast_intLift]
  map_add' x y := by
    refine Subtype.ext (mk_eq_mk_of_intCast_eq hℓ (smul_liftQuot (add_mem x.2 y.2))
      (y' := intLift x.1 + intLift y.1) (q' := liftQuot x.1 + liftQuot y.1)
      (by rw [smul_add, smul_liftQuot x.2, smul_liftQuot y.2, add_vecMul]) fun i ↦ ?_)
    simp [intCast_intLift]

private lemma kerToCokerTorsion_surjective (hℓ : ℓ ≠ 0) :
    Function.Surjective (kerToCokerTorsion T ℓ hℓ) := by
  rintro ⟨t, ht⟩
  induction t using Submodule.Quotient.induction_on with
  | H q =>
    obtain ⟨y, hy⟩ := mem_cokerTorsion_mk_iff.1 ht
    have hx : (fun i ↦ (y i : ZMod ℓ)) ∈ LinearMap.ker (intersectionMod T ℓ).vecMulLinear := by
      rw [LinearMap.mem_ker, vecMulLinear_apply]
      funext j
      rw [← intCast_vecMul, hy, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, Int.cast_mul,
        Int.cast_natCast, ZMod.natCast_self, zero_mul]
    refine ⟨⟨_, hx⟩, Subtype.ext ?_⟩
    exact mk_eq_mk_of_intCast_eq hℓ (smul_liftQuot hx) hy.symm fun i ↦ intCast_intLift _ i

private lemma multiplicityMod_mem_ker :
    (fun i ↦ ((T.multiplicity i : ℤ) : ZMod ℓ)) ∈
      LinearMap.ker (intersectionMod T ℓ).vecMulLinear := by
  rw [LinearMap.mem_ker, vecMulLinear_apply]
  funext j
  rw [← intCast_vecMul, T.multiplicity_vecMul_intersection]
  simp

/-- The `ℓ`-torsion of `Coker(A)` has dimension at most one less than the kernel of the
intersection matrix modulo `ℓ`, provided `ℓ` does not divide some multiplicity. -/
private lemma finrank_cokerTorsion_add_one_le [Fact ℓ.Prime] {i : T.Component}
    (hi : ¬ ℓ ∣ (T.multiplicity i : ℕ)) :
    Module.finrank (ZMod ℓ) (T.cokerTorsion ℓ) + 1 ≤
      Module.finrank (ZMod ℓ) (LinearMap.ker (intersectionMod T ℓ).vecMulLinear) := by
  have hℓ : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  set ψ := (kerToCokerTorsion T ℓ hℓ).toZModLinearMap ℓ
  have hsurj : Function.Surjective ψ := kerToCokerTorsion_surjective hℓ
  have hrange : LinearMap.range ψ = ⊤ := LinearMap.range_eq_top.2 hsurj
  have hmem : (⟨_, multiplicityMod_mem_ker⟩ : LinearMap.ker (intersectionMod T ℓ).vecMulLinear) ∈
      LinearMap.ker ψ := by
    rw [LinearMap.mem_ker]
    refine Subtype.ext (mk_eq_mk_of_intCast_eq hℓ (smul_liftQuot multiplicityMod_mem_ker)
      (y' := fun i ↦ (T.multiplicity i : ℤ)) (q' := 0)
      (by rw [smul_zero, T.multiplicity_vecMul_intersection]) fun i ↦ intCast_intLift _ i)
  have hne : (⟨_, multiplicityMod_mem_ker⟩ :
      LinearMap.ker (intersectionMod T ℓ).vecMulLinear) ≠ 0 := by
    intro h
    have := congrFun (congrArg Subtype.val h) i
    exact hi ((ZMod.natCast_eq_zero_iff _ _).1 (by exact_mod_cast this))
  have hpos := Submodule.finrank_mono ((Submodule.span_singleton_le_iff_mem _ _).2 hmem)
  rw [finrank_span_singleton hne] at hpos
  have := ψ.finrank_range_add_finrank_ker
  rw [hrange, finrank_top] at this
  omega

/-! ### The intersection matrix modulo `ℓ` as a weighted graph Laplacian -/

variable (T) in
/-- The pair `(a, b)` is an edge of the intersection graph oriented from `a` to `b`: the two
components meet, and `a` comes first in a fixed enumeration of the components. -/
private def IsOriented (a b : T.Component) : Prop :=
  Fintype.equivFin T.Component a < Fintype.equivFin T.Component b ∧ T.Adj a b

private noncomputable instance : DecidableRel (IsOriented T) := fun a b ↦ by
  rw [IsOriented, adj_iff]
  infer_instance

/-- Two distinct components are ordered one way or the other by the fixed enumeration. -/
private lemma equivFin_lt_or_gt {a b : T.Component} (hab : a ≠ b) :
    Fintype.equivFin T.Component a < Fintype.equivFin T.Component b ∨
      Fintype.equivFin T.Component b < Fintype.equivFin T.Component a :=
  lt_or_gt_of_ne ((Fintype.equivFin T.Component).injective.ne hab)

variable (T) in
/-- The oriented edges of the intersection graph. -/
private abbrev OrientedEdge : Type u :=
  {p : T.Component × T.Component // IsOriented T p.1 p.2}

/-- A sum over oriented edges, as a sum over all ordered pairs of components. -/
private lemma sum_orientedEdge {M : Type*} [AddCommMonoid M] (f : T.Component → T.Component → M) :
    ∑ p : OrientedEdge T, f p.1.1 p.1.2 =
      ∑ a, ∑ b, if IsOriented T a b then f a b else 0 := by
  rw [← Fintype.sum_prod_type', ← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) fun p : T.Component × T.Component ↦ f p.1 p.2).symm

variable (T ℓ) in
/-- The weight `mₐ aₐᵦ mᵦ` of a pair of components, modulo `ℓ`. -/
private def edgeWeight (a b : T.Component) : ZMod ℓ :=
  ((T.multiplicity a * T.intersection a b * T.multiplicity b : ℤ) : ZMod ℓ)

/-- Summing the two orientations of a pair of components. -/
private lemma edgeWeight_orient_add (a b : T.Component) :
    ((if IsOriented T a b then edgeWeight T ℓ a b else 0) +
      if IsOriented T b a then edgeWeight T ℓ b a else 0) =
      if a = b then 0 else edgeWeight T ℓ a b := by
  by_cases hab : a = b
  · subst hab
    simp [IsOriented]
  have hsymm : edgeWeight T ℓ b a = edgeWeight T ℓ a b := by
    simp only [edgeWeight, T.intersection_comm b a]
    ring_nf
  simp only [hab, ↓reduceIte, hsymm]
  by_cases hadj : T.Adj a b
  · rcases equivFin_lt_or_gt hab with h | h
    · simp only [IsOriented, h, h.not_gt, hadj, hadj.symm, and_self, false_and, ↓reduceIte,
        add_zero]
    · simp only [IsOriented, h, h.not_gt, hadj, hadj.symm, and_self, false_and, ↓reduceIte,
        zero_add]
  · have hzero : T.intersection a b = 0 :=
      le_antisymm (not_lt.1 fun h ↦ hadj ((T.adj_iff).2 ⟨hab, h⟩)) (T.offDiagonal_nonneg a b hab)
    have hadj' : ¬ T.Adj b a := fun h ↦ hadj h.symm
    simp only [IsOriented, hadj, hadj', and_false, ↓reduceIte, add_zero, edgeWeight, hzero,
      mul_zero, zero_mul, Int.cast_zero]

/-- The fibre relation, weighted by the multiplicities: every row of `(mₐ aₐᵦ mᵦ)` sums to zero. -/
private lemma sum_edgeWeight (a : T.Component) : ∑ b, edgeWeight T ℓ a b = 0 := by
  have h : ∑ b, (T.multiplicity a * T.intersection a b * T.multiplicity b : ℤ) = 0 := by
    simp_rw [mul_assoc, ← Finset.mul_sum, mul_comm (T.intersection a _), T.fiber_relation a,
      mul_zero]
  simp only [edgeWeight, ← Int.cast_sum, h, Int.cast_zero]

/-- The `(j, k)` entry of `∑ₐ,ᵦ gₐᵦ (eₐ - eᵦ)(eₐ - eᵦ)ᵀ`. -/
private lemma sum_sum_incidence_mul (g : T.Component → T.Component → ZMod ℓ)
    (j k : T.Component) :
    ∑ a, ∑ b, ((if j = a then (1 : ZMod ℓ) else 0) - if j = b then 1 else 0) *
      ((if k = a then 1 else 0) - if k = b then 1 else 0) * g a b =
      (if j = k then ∑ b, (g j b + g b j) else 0) - g j k - g k j := by
  simp only [sub_mul, mul_sub, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_add_distrib]
  by_cases h : j = k
  · subst h
    simp only [ite_true]
    ring
  · simp only [h, Ne.symm h, ite_false]
    ring

variable (T ℓ) in
/-- The oriented incidence matrix of the intersection graph, with entries in `ZMod ℓ`: the row of
the edge from `a` to `b` is `eₐ - eᵦ`. -/
private def incidence : Matrix (OrientedEdge T) T.Component (ZMod ℓ) :=
  .of fun p i ↦ (if i = p.1.1 then 1 else 0) - if i = p.1.2 then 1 else 0

variable (T ℓ) in
/-- The diagonal matrix of the negated edge weights `-mₐ aₐᵦ mᵦ`. -/
private def edgeWeightDiagonal : Matrix (OrientedEdge T) (OrientedEdge T) (ZMod ℓ) :=
  diagonal fun p ↦ -edgeWeight T ℓ p.1.1 p.1.2

variable (T ℓ) in
/-- The diagonal matrix of the multiplicities modulo `ℓ`. -/
private def multiplicityDiagonal : Matrix T.Component T.Component (ZMod ℓ) :=
  diagonal fun i ↦ ((T.multiplicity i : ℤ) : ZMod ℓ)

/-- After rescaling by the multiplicities, the intersection matrix modulo `ℓ` is the Laplacian
of the intersection graph weighted by the numbers `mₐ aₐᵦ mᵦ`. -/
private lemma multiplicityDiagonal_mul_mul :
    multiplicityDiagonal T ℓ * intersectionMod T ℓ * multiplicityDiagonal T ℓ =
      (incidence T ℓ)ᵀ * edgeWeightDiagonal T ℓ * incidence T ℓ := by
  ext j k
  have hL : (multiplicityDiagonal T ℓ * intersectionMod T ℓ * multiplicityDiagonal T ℓ) j k =
      edgeWeight T ℓ j k := by
    simp [multiplicityDiagonal, edgeWeight, diagonal_mul, mul_diagonal]
  rw [hL, mul_apply]
  simp only [mul_diagonal, transpose_apply, edgeWeightDiagonal, incidence, of_apply]
  rw [sum_orientedEdge (fun a b ↦ ((if j = a then 1 else 0) - if j = b then 1 else 0) *
    -edgeWeight T ℓ a b * ((if k = a then 1 else 0) - if k = b then 1 else 0))]
  set g : T.Component → T.Component → ZMod ℓ := fun a b ↦
    if IsOriented T a b then edgeWeight T ℓ a b else 0 with hg
  have hsum : (∑ a, ∑ b, if IsOriented T a b then
      ((if j = a then 1 else 0) - if j = b then 1 else 0) * -edgeWeight T ℓ a b *
        ((if k = a then 1 else 0) - if k = b then 1 else 0) else 0) =
      -∑ a, ∑ b, ((if j = a then (1 : ZMod ℓ) else 0) - if j = b then 1 else 0) *
        ((if k = a then 1 else 0) - if k = b then 1 else 0) * g a b := by
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
    simp only [hg]
    split_ifs <;> ring
  have hpair (a b : T.Component) : g a b + g b a = if a = b then 0 else edgeWeight T ℓ a b :=
    edgeWeight_orient_add a b
  rw [hsum, sum_sum_incidence_mul]
  by_cases hjk : j = k
  · subst hjk
    have hjj : g j j = 0 := by simp [hg, IsOriented]
    have hdiag (b : T.Component) : (if j = b then 0 else edgeWeight T ℓ j b) =
        edgeWeight T ℓ j b - if j = b then edgeWeight T ℓ j b else 0 := by
      split_ifs <;> ring
    simp only [↓reduceIte, hpair, hjj, hdiag, Finset.sum_sub_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, sum_edgeWeight]
    ring
  · have h := hpair j k
    simp only [hjk, ↓reduceIte] at h ⊢
    rw [← h]
    ring

/-- A vector killed by the oriented incidence matrix takes equal values at adjacent components. -/
private lemma eq_of_incidence_mulVec_eq_zero {x : T.Component → ZMod ℓ}
    (hx : incidence T ℓ *ᵥ x = 0) {a b : T.Component} (hab : T.Adj a b) : x a = x b := by
  have key (p : OrientedEdge T) : x p.1.1 = x p.1.2 := by
    have := congrFun hx p
    simp only [mulVec, dotProduct, incidence, of_apply, sub_mul, ite_mul, one_mul, zero_mul,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      Pi.zero_apply] at this
    exact sub_eq_zero.1 this
  rcases equivFin_lt_or_gt ((T.adj_iff).1 hab).1 with h | h
  · exact key ⟨(a, b), h, hab⟩
  · exact (key ⟨(b, a), h, hab.symm⟩).symm

/-- The intersection graph being connected, the kernel of its oriented incidence matrix consists
of the constant vectors, so has dimension at most one. -/
private lemma finrank_ker_incidence_le_one [Fact ℓ.Prime] :
    Module.finrank (ZMod ℓ) (LinearMap.ker (incidence T ℓ).mulVecLin) ≤ 1 := by
  obtain ⟨i⟩ := T.componentNonempty
  have hconst {x : T.Component → ZMod ℓ} (hx : incidence T ℓ *ᵥ x = 0) (j : T.Component) :
      x i = x j := by
    induction T.reflTransGen_adj i j with
    | refl => rfl
    | tail _ hbc ih => exact ih.trans (eq_of_incidence_mulVec_eq_zero hx hbc)
  have hinj : Function.Injective
      ((LinearMap.proj i : (T.Component → ZMod ℓ) →ₗ[ZMod ℓ] ZMod ℓ).domRestrict
        (LinearMap.ker (incidence T ℓ).mulVecLin)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hx⟩ hxi
    rw [LinearMap.domRestrict_apply, LinearMap.proj_apply] at hxi
    exact Subtype.ext (funext fun j ↦ (hconst hx j).symm.trans hxi)
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

/-- There are as many oriented edges as edges of the intersection graph. -/
private lemma card_orientedEdge :
    Fintype.card (OrientedEdge T) = T.intersectionGraph.edgeSet.ncard := by
  let f : OrientedEdge T → T.intersectionGraph.edgeSet := fun p ↦
    ⟨s(p.1.1, p.1.2), by simpa [SimpleGraph.mem_edgeSet] using p.2.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq ↦ ?_, fun ⟨e, he⟩ ↦ ?_⟩
    · have h := congrArg Subtype.val hpq
      simp only [f, Sym2.eq_iff] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Subtype.ext (Prod.ext h1 h2)
      · have hp := p.2.1
        have hq := q.2.1
        rw [h1, h2] at hp
        exact absurd (hp.trans hq) (lt_irrefl _)
    · induction e using Sym2.ind with
      | h a b =>
        have hab : T.Adj a b := by simpa [SimpleGraph.mem_edgeSet] using he
        rcases equivFin_lt_or_gt ((T.adj_iff).1 hab).1 with h | h
        · exact ⟨⟨(a, b), h, hab⟩, rfl⟩
        · exact ⟨⟨(b, a), h, hab.symm⟩, Subtype.ext Sym2.eq_swap⟩
  rw [← Nat.card_eq_fintype_card, Nat.card_eq_of_bijective f hf, Nat.card_coe_set_eq]

/-- Modulo a prime `ℓ` dividing no multiplicity and no nonzero off-diagonal intersection number,
the kernel of the intersection matrix has dimension at most `1 + (1 - #components + #edges)`. -/
private lemma finrank_ker_intersectionMod_add_card_le [Fact ℓ.Prime]
    (hm : ∀ i, ¬ ℓ ∣ (T.multiplicity i : ℕ))
    (ha : ∀ i j, T.Adj i j → ¬ (ℓ : ℤ) ∣ T.intersection i j) :
    Module.finrank (ZMod ℓ) (LinearMap.ker (intersectionMod T ℓ).vecMulLinear) +
        Fintype.card T.Component ≤ Fintype.card (OrientedEdge T) + 2 := by
  have hmult (i : T.Component) : ((T.multiplicity i : ℤ) : ZMod ℓ) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    exact hm i
  have hD : IsUnit (multiplicityDiagonal T ℓ).det := by
    rw [multiplicityDiagonal, det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    exact fun i _ ↦ hmult i
  have hW : IsUnit (edgeWeightDiagonal T ℓ).det := by
    rw [edgeWeightDiagonal, det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro p _
    rw [neg_ne_zero, edgeWeight, Int.cast_mul, Int.cast_mul]
    refine mul_ne_zero (mul_ne_zero (hmult _) ?_) (hmult _)
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ha _ _ p.2.2
  have hrank : (intersectionMod T ℓ).rank =
      ((incidence T ℓ)ᵀ * edgeWeightDiagonal T ℓ * incidence T ℓ).rank := by
    rw [← multiplicityDiagonal_mul_mul, rank_mul_eq_left_of_isUnit_det _ _ hD,
      rank_mul_eq_right_of_isUnit_det _ _ hD]
  have hsyl := rank_add_rank_le_rank_mul_add_card
    ((incidence T ℓ)ᵀ * edgeWeightDiagonal T ℓ) (incidence T ℓ)
  rw [rank_mul_eq_left_of_isUnit_det _ _ hW, rank_transpose, ← hrank] at hsyl
  have hsymm : (intersectionMod T ℓ).vecMulLinear = (intersectionMod T ℓ).mulVecLin := by
    rw [← mulVecLin_transpose, ← transpose_map, T.intersection_isSymm.eq]
  have hB := (incidence T ℓ).mulVecLin.finrank_range_add_finrank_ker
  have hA := (intersectionMod T ℓ).mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hA hB
  rw [rank, rank] at hsyl
  rw [hsymm]
  have := finrank_ker_incidence_le_one (T := T) (ℓ := ℓ)
  omega

/-! ### The bound -/

variable (T) in
/-- **The `ℓ`-torsion of `Coker(A)` is bounded by the topological genus.** If the prime `ℓ`
divides no multiplicity and no intersection number of two distinct meeting components, then
`dim_{𝔽_ℓ} Coker(A)[ℓ] ≤ 1 - n + e`, the first Betti number of the intersection graph. -/
theorem finrank_cokerTorsion_le_topologicalGenus (ℓ : ℕ) [Fact ℓ.Prime]
    (hm : ∀ i, ¬ ℓ ∣ (T.multiplicity i : ℕ))
    (ha : ∀ i j, T.Adj i j → ¬ (ℓ : ℤ) ∣ T.intersection i j) :
    (Module.finrank (ZMod ℓ) (T.cokerTorsion ℓ) : ℤ) ≤ T.topologicalGenus := by
  obtain ⟨i⟩ := T.componentNonempty
  have h1 := finrank_cokerTorsion_add_one_le (hm i)
  have h2 := finrank_ker_intersectionMod_add_card_le hm ha
  rw [topologicalGenus_def, Nat.card_eq_fintype_card, ← card_orientedEdge]
  omega

variable (T) in
/-- The comparison map `Pic(T) → Coker(A)` restricted to `ℓ`-torsion. -/
private def torsionToCokerTorsion (ℓ : ℕ) : T.torsion ℓ →+ T.cokerTorsion ℓ :=
  (T.picToCoker.toAddMonoidHom.comp (T.torsion ℓ).subtype).codRestrict _ fun x ↦ by
    rw [AddSubgroup.torsionBy.nsmul_iff]
    simp [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.1 x.2]

variable (T) in
/-- **The `ℓ`-torsion of `Pic(T)` is bounded by the topological genus.** If the prime `ℓ` divides
no multiplicity and no intersection number of two distinct meeting components, then
`dim_{𝔽_ℓ} Pic(T)[ℓ] ≤ g_top`. -/
theorem finrank_torsion_le_topologicalGenus (ℓ : ℕ) [Fact ℓ.Prime]
    (hm : ∀ i, ¬ ℓ ∣ (T.multiplicity i : ℕ))
    (ha : ∀ i j, T.Adj i j → ¬ (ℓ : ℤ) ∣ T.intersection i j) :
    (Module.finrank (ZMod ℓ) (T.torsion ℓ) : ℤ) ≤ T.topologicalGenus := by
  have hℓ : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  have : Module.Finite (ZMod ℓ) (T.cokerTorsion ℓ) :=
    Module.Finite.of_surjective ((kerToCokerTorsion T ℓ hℓ).toZModLinearMap ℓ)
      (kerToCokerTorsion_surjective hℓ)
  have hinj : Function.Injective ((torsionToCokerTorsion T ℓ).toZModLinearMap ℓ) :=
    fun x y h ↦ Subtype.ext (T.picToCoker_injective (congrArg Subtype.val h))
  exact (Int.ofNat_le.2 (LinearMap.finrank_le_finrank_of_injective hinj)).trans
    (T.finrank_cokerTorsion_le_topologicalGenus ℓ hm ha)

end NumericalType

end TauCeti
