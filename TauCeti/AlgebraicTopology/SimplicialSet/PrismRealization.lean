/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.Homotopy.TopCat.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne
public import TauCeti.AlgebraicTopology.SimplicialSet.TrivialFibration
public import TauCeti.AlgebraicTopology.SimplicialSet.WeakEquivalence

/-!
# Geometric realization of simplicial homotopies

A homotopy of simplicial sets `H : X ⊗ Δ[1] ⟶ Y` from `f` to `g` realizes to a homotopy from `|f|`
to `|g|` (`SSet.Homotopy.toTop`). Consequently simplicial homotopy equivalences, and in particular
the trivial fibrations of the Kan–Quillen model structure (the maps with the right lifting property
with respect to all monomorphisms), are weak equivalences
(`SSet.modelCategoryQuillen.weakEquivalence_of_homotopyEquiv`,
`SSet.modelCategoryQuillen.weakEquivalence_of_rlp_monomorphisms`). This is the converse direction
to Mathlib's `TopCat.Homotopy.toSSet`.

The realization `|X ⊗ Δ[1]|` is not identified with `|X| × I` here; what is needed is the continuous
map `SSet.toTopCylinder X : |X| × I → |X ⊗ Δ[1]|` restricting to `|ι₀|` and `|ι₁|` on the two ends.
It is adjoint to a map from `X` to the singular simplicial set of the path space
`C(I, |X ⊗ Δ[1]|)`, obtained from the triangulation of the prism `Δᵖ × I` by the nondegenerate
`(p + 1)`-simplices of `Δ[p] ⊗ Δ[1]` (`SSet.prodStdSimplex₁.prism`): the `k`th simplex, with
vertices `(0, 0), …, (k, 0), (k, 1), …, (p, 1)`, covers the points `(s, t)` with
`s₀ + ⋯ + s_(k-1) ≤ 1 - t ≤ s₀ + ⋯ + s_k`.

The pieces must agree on overlaps, and the triangulations must be natural in `Δ[p]`, including
under degeneracies. Both follow from one fact (`SSet.prodStdSimplex.toTopObjMk_eq_of_map_eq`): a
point of `|Δ[p] ⊗ Δ[q]|` is determined by the distribution of its barycentric coordinates on the
vertices `Fin (p + 1) × Fin (q + 1)`. Indeed every point lies in the interior of the realization of
a nondegenerate simplex, a chain of vertices which the distribution determines. The distribution of
the point `(s, t)` of the prism is the comonotone coupling of `s` with the distribution `(1 - t, t)`
on `Fin 2`, which is natural in `s`.

## Main declarations

* `SSet.toTopObjMk x w`: the point of `|X|` with barycentric coordinates `w` in the simplex `x`.
* `SSet.prodStdSimplex.toTopObjMk_eq_of_map_eq`: points of `|Δ[p] ⊗ Δ[q]|` are determined by their
  coordinates on the vertices.
* `SSet.prodStdSimplex₁.prism`: the triangulation `Δᵖ × I → |Δ[p] ⊗ Δ[1]|` of the prism, natural
  in `Δ[p]` (`SSet.prodStdSimplex₁.prism_naturality`), with ends `ι₀` and `ι₁`.
* `SSet.toTopCylinder X`: the triangulation `|X| × I → |X ⊗ Δ[1]|` of the realized cylinder.
* `SSet.Homotopy.toTop`: the realization of a simplicial homotopy.
* `SSet.toTopHomotopyEquiv`: the realization of a simplicial homotopy equivalence.

## References

* J. Milnor, *The geometric realization of a semi-simplicial complex*, Ann. of Math. 65 (1957),
  357–362.
* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Sections I.2 and I.11.
-/

public section

open CategoryTheory MonoidalCategory Opposite Convexity Simplicial MorphismProperty
  HomotopicalAlgebra

universe u

namespace SSet

variable {X Y : SSet.{u}}

/-- The point of the geometric realization `|X|` with barycentric coordinates `w` in the
realization of the `n`-simplex `x` of `X`: the value at `w` of the singular simplex
`(sSetTopAdj.unit.app X).app _ x` of `|X|`. -/
noncomputable def toTopObjMk {n : ℕ} (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) : |X| :=
  TopCat.toSSetObjEquiv _ _ ((sSetTopAdj.unit.app X).app _ x) w

/-- The point of `|X|` given by an `n`-simplex depends continuously on its coordinates. -/
@[fun_prop]
lemma continuous_toTopObjMk {n : ℕ} (x : X _⦋n⦌) : Continuous (toTopObjMk x) :=
  (TopCat.toSSetObjEquiv _ _ ((sSetTopAdj.unit.app X).app _ x)).continuous

/-- The realization of a map sends the point of a simplex to the point of its image. -/
@[simp]
lemma toTop_map_toTopObjMk (f : X ⟶ Y) {n : ℕ} (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    toTop.map f (toTopObjMk x w) = toTopObjMk (f.app _ x) w := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (sSetTopAdj.unit.naturality f) _) x
  dsimp at h
  rw [toTopObjMk, toTopObjMk, h]
  rfl

/-- The point of a face or degeneracy of a simplex is the point of the simplex with the
transported coordinates. -/
lemma toTopObjMk_map {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (m + 1))) :
    toTopObjMk (X.map θ.op x) w = toTopObjMk x (StdSimplex.map θ w) := by
  have h := ConcreteCategory.congr_hom ((sSetTopAdj.unit.app X).naturality θ.op) x
  dsimp at h
  rw [toTopObjMk, toTopObjMk, h]
  rfl

/-- Two continuous maps out of `|X|` agree once they agree on the points of all simplices. -/
lemma toTop_hom_ext {T : TopCat.{u}} {g₁ g₂ : |X| ⟶ T}
    (h : ∀ (n : ℕ) (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))),
      g₁ (toTopObjMk x w) = g₂ (toTopObjMk x w)) : g₁ = g₂ := by
  apply (sSetTopAdj.homEquiv X T).injective
  ext ⟨n⟩ x
  induction n using SimplexCategory.rec with | _ n => ?_
  apply (T.toSSetObjEquiv _).injective
  ext w
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact h n x w

namespace prodStdSimplex

variable {p q : ℕ}

/-- The barycentric coordinates supported on the range of an injective map, pulled back along it. -/
private noncomputable def comapWeights {α β : Type*} {g : α → β} (hg : Function.Injective g)
    (w : StdSimplex ℝ β) (h : ↑w.weights.support ⊆ Set.range g) : StdSimplex ℝ α where
  weights := Finsupp.comapDomain g w.weights hg.injOn
  nonneg a := by simp
  total := by
    have := w.total
    rwa [← Finsupp.mapDomain_comapDomain g hg w.weights h,
      Finsupp.sum_mapDomain_index (by simp) (by simp)] at this

private lemma map_comapWeights {α β : Type*} {g : α → β} (hg : Function.Injective g)
    (w : StdSimplex ℝ β) (h : ↑w.weights.support ⊆ Set.range g) :
    StdSimplex.map g (comapWeights hg w h) = w := by
  rw [← StdSimplex.weights_inj, StdSimplex.weights_map]
  exact Finsupp.mapDomain_comapDomain g hg w.weights h

/-- A simplex of `Δ[p] ⊗ Δ[q]` with the same vertex at `j` and `j + 1` is the degeneracy `σ j` of
its face opposite `j + 1`. -/
private lemma σ_δ_succ_of_eq {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n + 1⦌) (j : Fin (n + 1))
    (hj : objEquiv x j.castSucc = objEquiv x j.succ) :
    (Δ[p] ⊗ Δ[q]).σ j ((Δ[p] ⊗ Δ[q]).δ j.succ x) = x := by
  apply objEquiv.injective
  refine OrderHom.ext _ _ (funext fun k ↦ ?_)
  -- The vertices of a face or degeneracy are those of `x` reindexed (`objEquiv_map_apply`).
  change objEquiv x (j.succ.succAbove (j.predAbove k)) = objEquiv x k
  rcases lt_trichotomy k j.succ with hk | hk | hk
  · rw [Fin.predAbove_of_le_castSucc _ _ (Fin.le_castSucc_iff.2 hk),
      Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using hk), Fin.castSucc_castPred]
  · subst hk
    rw [Fin.predAbove_succ_self, Fin.succAbove_of_castSucc_lt _ _ Fin.castSucc_lt_succ, hj]
  · rw [Fin.predAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def] at hk ⊢; lia),
      Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def, Fin.lt_def] at hk ⊢; lia),
      Fin.succ_pred]

/-- Every point of the realization of a simplex of `Δ[p] ⊗ Δ[q]` is the point, with nowhere
vanishing coordinates, of a simplex with injective vertex map, with the same distribution of
coordinates on the vertices. -/
private lemma exists_injective_toTopObjMk_eq {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    ∃ (r : ℕ) (y : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋r⦌) (w' : StdSimplex ℝ (Fin (r + 1))),
      Function.Injective (objEquiv y) ∧ (∀ j, w'.weights j ≠ 0) ∧
      toTopObjMk x w = toTopObjMk y w' ∧
      StdSimplex.map (objEquiv x) w = StdSimplex.map (objEquiv y) w' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases h0 : ∃ j, w.weights j = 0
  · -- Pass to the face opposite a vertex with vanishing coordinate.
    obtain ⟨j, hj⟩ := h0
    obtain _ | n := n
    · simp at hj
    have hsupp : ↑w.weights.support ⊆ Set.range j.succAbove := by
      intro i hi
      exact Fin.exists_succAbove_eq (fun h ↦ by simp [h, hj] at hi)
    obtain ⟨r, y, w'', hy, hw'', h₁, h₂⟩ :=
      ih n (by lia) ((Δ[p] ⊗ Δ[q]).δ j x) (comapWeights Fin.succAbove_right_injective w hsupp)
    refine ⟨r, y, w'', hy, hw'', ?_, ?_⟩
    · rw [← h₁, SimplicialObject.δ, toTopObjMk_map]
      exact congrArg _ (map_comapWeights _ w hsupp).symm
    · rw [← h₂]
      conv_lhs => rw [← map_comapWeights Fin.succAbove_right_injective w hsupp]
      -- The vertices of the face `δ j x` are those of `x` reindexed by `j.succAbove`.
      rw [StdSimplex.map_map]
      rfl
  · push Not at h0
    by_cases hi : Function.Injective (objEquiv x)
    · exact ⟨n, x, w, hi, h0, rfl, rfl⟩
    -- Pass to a degeneracy of the face opposite a repeated vertex.
    obtain _ | n := n
    · exact absurd (fun a b _ ↦ Fin.ext (by have := a.isLt; have := b.isLt; lia)) hi
    obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), objEquiv x j.castSucc = objEquiv x j.succ := by
      have h : ¬ StrictMono (objEquiv x) := fun h ↦ hi h.injective
      rw [Fin.strictMono_iff_lt_succ] at h
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact ⟨j, ((objEquiv x).monotone (Fin.castSucc_le_succ j)).eq_of_not_lt hj⟩
    have hx := (σ_δ_succ_of_eq x j hj).symm
    obtain ⟨r, y, w'', hy, hw'', h₁, h₂⟩ :=
      ih n (by lia) ((Δ[p] ⊗ Δ[q]).δ j.succ x) (StdSimplex.map j.predAbove w)
    refine ⟨r, y, w'', hy, hw'', ?_, ?_⟩
    · rw [← h₁]
      conv_lhs => rw [hx]
      rw [SimplicialObject.σ, toTopObjMk_map]
      rfl
    · -- The vertices of `x = σ j (δ j.succ x)` are those of the face reindexed by `j.predAbove`.
      rw [← h₂, StdSimplex.map_map]
      conv_lhs => rw [hx]
      rfl

/-- Two points of the realizations of simplices of `Δ[p] ⊗ Δ[q]` with injective vertex maps and
nowhere vanishing coordinates agree if their coordinates have the same distribution on the
vertices. -/
private lemma toTopObjMk_eq_of_injective {r r' : ℕ} {y : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋r⦌}
    {y' : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋r'⦌} {w : StdSimplex ℝ (Fin (r + 1))}
    {w' : StdSimplex ℝ (Fin (r' + 1))} (hy : Function.Injective (objEquiv y))
    (hy' : Function.Injective (objEquiv y')) (hw : ∀ j, w.weights j ≠ 0)
    (hw' : ∀ j, w'.weights j ≠ 0)
    (h : StdSimplex.map (objEquiv y) w = StdSimplex.map (objEquiv y') w') :
    toTopObjMk y w = toTopObjMk y' w' := by
  classical
  have hsupp {r : ℕ} (w : StdSimplex ℝ (Fin (r + 1))) (hw : ∀ j, w.weights j ≠ 0) :
      w.weights.support = Finset.univ :=
    Finset.eq_univ_iff_forall.2 fun j ↦ by simpa using hw j
  have himage : Finset.univ.image (objEquiv y) = Finset.univ.image (objEquiv y') := by
    have := congrArg (fun w ↦ w.weights.support) h
    simpa only [StdSimplex.weights_map, Finsupp.mapDomain_support_of_injective hy,
      Finsupp.mapDomain_support_of_injective hy', hsupp w hw, hsupp w' hw'] using this
  obtain rfl : r = r' := by
    simpa [Finset.card_image_of_injective _ hy, Finset.card_image_of_injective _ hy'] using
      congrArg Finset.card himage
  have hmono {y : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋r⦌} (hy : Function.Injective (objEquiv y)) :
      StrictMono (toLex ∘ objEquiv y) :=
    (Prod.Lex.toLex_mono.comp (objEquiv y).monotone).strictMono_of_injective
      (toLex.injective.comp hy)
  have hrange : Set.range (toLex ∘ objEquiv y) = Set.range (toLex ∘ objEquiv y') := by
    have : Set.range (objEquiv y) = Set.range (objEquiv y') := by
      rw [← Set.image_univ, ← Set.image_univ, ← Finset.coe_univ, ← Finset.coe_image,
        ← Finset.coe_image, himage]
    rw [Set.range_comp, Set.range_comp, this]
  obtain rfl : y = y' := by
    apply objEquiv.injective
    refine OrderHom.ext _ _ (funext fun k ↦ ?_)
    exact toLex.injective
      (congrFun ((StrictMono.range_inj_of_wellFoundedLT (hmono hy) (hmono hy')).1 hrange) k)
  obtain rfl : w = w' := by
    rw [← StdSimplex.weights_inj, StdSimplex.weights_map, StdSimplex.weights_map] at h
    exact (StdSimplex.weights_inj).1 (Finsupp.mapDomain_injective hy h)
  rfl

/-- A point of the geometric realization of `Δ[p] ⊗ Δ[q]` is determined by the distribution of its
barycentric coordinates on the vertices `Fin (p + 1) × Fin (q + 1)`: the points of two simplices
agree when their coordinates push forward to the same coordinates on the vertices. -/
theorem toTopObjMk_eq_of_map_eq {n n' : ℕ} {x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌}
    {x' : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n'⦌} {w : StdSimplex ℝ (Fin (n + 1))}
    {w' : StdSimplex ℝ (Fin (n' + 1))}
    (h : StdSimplex.map (objEquiv x) w = StdSimplex.map (objEquiv x') w') :
    toTopObjMk x w = toTopObjMk x' w' := by
  obtain ⟨r, y, v, hy, hv, h₁, h₂⟩ := exists_injective_toTopObjMk_eq x w
  obtain ⟨r', y', v', hy', hv', h₁', h₂'⟩ := exists_injective_toTopObjMk_eq x' w'
  rw [h₁, h₁']
  exact toTopObjMk_eq_of_injective hy hy' hv hv' (h₂.symm.trans (h.trans h₂'))

end prodStdSimplex

namespace prodStdSimplex₁

/-! ### Cumulative sums on `Fin (n + 1)` -/

/-- The sum of the values of `g` at the `j : Fin (n + 1)` with `j < N`. Unlike `Fin.partialSum`,
it is indexed by all `N : ℕ`, which makes it convenient for telescoping along initial segments. -/
private noncomputable def cumSum {n : ℕ} (g : Fin (n + 1) → ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) ↦ j.val < N), g j

private lemma cumSum_zero {n : ℕ} (g : Fin (n + 1) → ℝ) : cumSum g 0 = 0 := by
  simp [cumSum]

private lemma sum_filter_lt_succ {n : ℕ} (g : Fin (n + 1) → ℝ) {N : ℕ} (hN : N < n + 1) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) ↦ j.val < N + 1), g j =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) ↦ j.val < N), g j + g ⟨N, hN⟩ := by
  refine Eq.trans ?_ (add_comm _ _)
  rw [← Finset.sum_insert (by simp)]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  lia

private lemma cumSum_succ {n : ℕ} (g : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    cumSum g (i.val + 1) = cumSum g i.val + g i :=
  sum_filter_lt_succ g i.isLt

private lemma cumSum_of_le {n N : ℕ} (g : Fin (n + 1) → ℝ) (hN : n + 1 ≤ N) :
    cumSum g N = ∑ j, g j := by
  rw [cumSum, Finset.filter_true_of_mem (fun j _ ↦ by lia)]

/-- Telescoping along cumulative sums. -/
private lemma sum_sub_cumSum {n : ℕ} (g : Fin (n + 1) → ℝ) (F : ℝ → ℝ) (N : ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) ↦ i.val < N),
      (F (cumSum g (i.val + 1)) - F (cumSum g i.val)) = F (cumSum g N) - F 0 := by
  induction N with
  | zero => simp [cumSum_zero]
  | succ N ih =>
    by_cases hN : N < n + 1
    · rw [sum_filter_lt_succ _ hN, ih]
      ring
    · rw [Finset.filter_congr (q := fun i : Fin (n + 1) ↦ i.val < N) (fun i _ ↦ by lia), ih,
        cumSum_of_le g (by lia), cumSum_of_le g (by lia)]

private lemma eq_of_cumSum_eq {n : ℕ} {g g' : Fin (n + 1) → ℝ}
    (h : ∀ N, cumSum g N = cumSum g' N) : g = g' := by
  funext i
  have := h (i.val + 1)
  rwa [cumSum_succ, cumSum_succ, h, add_right_inj] at this

/-- For a monotone map `f`, the `j` with `f j < N` form an initial segment. -/
private lemma exists_lt_iff_lt {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) (N : ℕ) :
    ∃ a : ℕ, ∀ j, (f j).val < N ↔ j.val < a := by
  classical
  refine ⟨(Finset.univ.filter fun j ↦ (f j).val < N).card, fun j ↦ ⟨fun hj ↦ ?_, fun hj ↦ ?_⟩⟩
  · have : Finset.Iic j ⊆ Finset.univ.filter fun j ↦ (f j).val < N := fun i hi ↦ by
      simp only [Finset.mem_Iic] at hi
      simpa using lt_of_le_of_lt (Fin.le_def.1 (f.monotone hi)) hj
    simpa [Fin.card_Iic] using Finset.card_le_card this
  · by_contra hj'
    have : (Finset.univ.filter fun j ↦ (f j).val < N) ⊆ Finset.Iio j := fun i hi ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_Iio]
      by_contra hij
      exact hj' (lt_of_le_of_lt (Fin.le_def.1 (f.monotone (not_lt.1 hij))) hi)
    have := Finset.card_le_card this
    simp only [Fin.card_Iio] at this
    lia

/-- Sums of the coordinates of a pushforward over a set are sums over its preimage. -/
private lemma sum_filter_weights_map {α β : Type*} [Fintype α] [Fintype β] (g : α → β)
    (w : StdSimplex ℝ α) (P : β → Prop) [DecidablePred P] :
    ∑ b ∈ Finset.univ.filter P, (StdSimplex.map g w).weights b =
      ∑ a ∈ Finset.univ.filter (fun a ↦ P (g a)), w.weights a := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter, StdSimplex.weights_map,
    ← Finsupp.sum_fintype (Finsupp.mapDomain g w.weights) (fun b r ↦ if P b then r else 0)
      (by simp),
    Finsupp.sum_mapDomain_index (by simp) (fun _ _ _ ↦ by split_ifs <;> simp),
    Finsupp.sum_fintype _ _ (by simp)]

private lemma cumSum_mono {n : ℕ} {g : Fin (n + 1) → ℝ} (hg : 0 ≤ g) : Monotone (cumSum g) :=
  fun _ _ h ↦ Finset.sum_le_sum_of_subset_of_nonneg
    (fun j hj ↦ by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢; lia)
    (fun j _ _ ↦ hg j)

private lemma sum_filter_prod {n : ℕ} (h : Fin (n + 1) × Fin 2 → ℝ) (P : Fin (n + 1) → Prop)
    [DecidablePred P] (b : Fin 2) :
    ∑ x ∈ Finset.univ.filter (fun x : Fin (n + 1) × Fin 2 ↦ P x.1 ∧ x.2 = b), h x =
      ∑ i ∈ Finset.univ.filter P, h (i, b) := by
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases (by decide : ∀ b : Fin 2, b = 0 ∨ b = 1) b with rfl | rfl <;>
    by_cases hP : P i <;> simp [hP]

/-! ### The prism -/

open unitInterval

variable {p : ℕ}

section

variable (s : StdSimplex ℝ (Fin (p + 1)))

private lemma cumSum_nonneg (N : ℕ) : 0 ≤ cumSum s.weights N :=
  Finset.sum_nonneg fun j _ ↦ s.nonneg j

private lemma cumSum_le_one (N : ℕ) : cumSum s.weights N ≤ 1 := by
  have := cumSum_mono s.nonneg (le_max_left N (p + 1))
  rwa [cumSum_of_le _ (le_max_right _ _), StdSimplex.total_of_fintype] at this

@[fun_prop]
private lemma continuous_cumSum {Z : Type*} [TopologicalSpace Z]
    {f : Z → StdSimplex ℝ (Fin (p + 1))} (hf : Continuous f) (N : ℕ) :
    Continuous fun z ↦ cumSum (f z).weights N :=
  continuous_finsetSum _ fun j _ ↦ (StdSimplex.continuous_weights_apply ℝ j).comp hf

end

/-- `min a v` for `b = 0`, and `max a v` for `b = 1`. -/
private noncomputable def clamp (v : ℝ) (b : Fin 2) (a : ℝ) : ℝ :=
  if b = 0 then min a v else max a v

@[simp]
private lemma clamp_zero (v a : ℝ) : clamp v 0 a = min a v := rfl

@[simp]
private lemma clamp_one (v a : ℝ) : clamp v 1 a = max a v := rfl

private lemma clamp_mono (v : ℝ) (b : Fin 2) : Monotone (clamp v b) := by
  intro a a' h
  unfold clamp
  split_ifs
  exacts [min_le_min_right _ h, max_le_max_right _ h]

/-- The barycentric coordinates on the vertices `Fin (p + 1) × Fin 2` of the point `(s, t)` of the
prism: of the first coordinate `s` of a vertex `i`, the part in `[0, 1 - t]` of the interval of
cumulative sums it occupies goes to the bottom vertex `(i, 0)`, and the rest to the top vertex
`(i, 1)`. -/
private noncomputable def prismWeights (s : StdSimplex ℝ (Fin (p + 1))) (t : I)
    (x : Fin (p + 1) × Fin 2) : ℝ :=
  clamp (1 - t) x.2 (cumSum s.weights (x.1.val + 1)) - clamp (1 - t) x.2 (cumSum s.weights x.1.val)

@[fun_prop]
private lemma continuous_prismWeights (x : Fin (p + 1) × Fin 2) :
    Continuous fun z : StdSimplex ℝ (Fin (p + 1)) × I ↦ prismWeights z.1 z.2 x := by
  unfold prismWeights clamp
  split_ifs <;> fun_prop

private lemma sum_prismWeights (s : StdSimplex ℝ (Fin (p + 1))) (t : I) :
    ∑ x, prismWeights s t x = 1 := by
  have h := sum_sub_cumSum s.weights id (p + 1)
  simp only [id] at h
  rw [Finset.filter_true_of_mem (fun j _ ↦ j.isLt), cumSum_of_le _ le_rfl,
    StdSimplex.total_of_fintype, sub_zero] at h
  rw [Fintype.sum_prod_type, ← h]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Fin.sum_univ_two, prismWeights, clamp_zero, clamp_one]
  linarith [min_add_max (cumSum s.weights (i.val + 1)) (1 - t),
    min_add_max (cumSum s.weights i.val) (1 - t)]

/-- The barycentric coordinates `prismWeights s t` on the vertices of the prism. -/
private noncomputable def prismMeasure (s : StdSimplex ℝ (Fin (p + 1))) (t : I) :
    StdSimplex ℝ (Fin (p + 1) × Fin 2) where
  weights := Finsupp.equivFunOnFinite.symm (prismWeights s t)
  nonneg x := sub_nonneg.2 (clamp_mono _ _ (cumSum_mono s.nonneg (Nat.le_succ _)))
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simpa using sum_prismWeights s t

private lemma prismMeasure_weights (s : StdSimplex ℝ (Fin (p + 1))) (t : I)
    (x : Fin (p + 1) × Fin 2) : (prismMeasure s t).weights x = prismWeights s t x := rfl

/-- The `k`th closed piece of the prism `Δᵖ × I`, the realization of the `k`th nondegenerate
`(p + 1)`-simplex of `Δ[p] ⊗ Δ[1]`. -/
private def piece (k : Fin (p + 1)) : Set (StdSimplex ℝ (Fin (p + 1)) × I) :=
  {z | cumSum z.1.weights k.val ≤ 1 - z.2 ∧ 1 - (z.2 : ℝ) ≤ cumSum z.1.weights (k.val + 1)}

private lemma isClosed_piece (k : Fin (p + 1)) : IsClosed (piece k) := by
  simp only [piece, Set.ofPred_and]
  exact (isClosed_le (by fun_prop) (by fun_prop)).inter (isClosed_le (by fun_prop) (by fun_prop))

private lemma exists_mem_piece (z : StdSimplex ℝ (Fin (p + 1)) × I) : ∃ k, z ∈ piece k := by
  have hex : ∃ N, 1 - (z.2 : ℝ) ≤ cumSum z.1.weights (N + 1) :=
    ⟨p, by rw [cumSum_of_le _ le_rfl, StdSimplex.total_of_fintype]; linarith [z.2.2.1]⟩
  classical
  have hle : Nat.find hex ≤ p :=
    Nat.find_min' hex (by
      rw [cumSum_of_le _ le_rfl, StdSimplex.total_of_fintype]
      linarith [z.2.2.1])
  refine ⟨⟨Nat.find hex, by lia⟩, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · simp only [h, cumSum_zero]
    linarith [z.2.2.2]
  · have := Nat.find_min hex (Nat.sub_lt h one_pos)
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by lia] at this
    exact (not_le.1 this).le

private lemma iUnion_piece : ⋃ k, piece (p := p) k = Set.univ :=
  Set.eq_univ_of_forall fun z ↦ Set.mem_iUnion.2 (exists_mem_piece z)

private lemma objEquiv_nonDegenerateEquiv_castSucc (k i : Fin (p + 1)) (hi : i ≤ k) :
    prodStdSimplex.objEquiv (nonDegenerateEquiv.{u} k).val i.castSucc = (i, 0) := by
  refine Prod.ext ?_ ?_
  · exact Fin.predAbove_castSucc_of_le _ _ hi
  · refine stdSimplex.objMk₁_of_castSucc_lt _ _ ?_
    rw [Fin.lt_def]
    simp only [Fin.val_castSucc, Fin.val_succ]
    have := Fin.le_def.1 hi
    lia

private lemma objEquiv_nonDegenerateEquiv_succ (k i : Fin (p + 1)) (hi : k ≤ i) :
    prodStdSimplex.objEquiv (nonDegenerateEquiv.{u} k).val i.succ = (i, 1) := by
  refine Prod.ext ?_ ?_
  · exact Fin.predAbove_succ_of_le _ _ hi
  · refine stdSimplex.objMk₁_of_le_castSucc _ _ ?_
    rw [Fin.le_def]
    simp only [Fin.val_castSucc, Fin.val_succ]
    have := Fin.le_def.1 hi
    lia

private lemma injective_objEquiv_nonDegenerateEquiv (k : Fin (p + 1)) :
    Function.Injective (prodStdSimplex.objEquiv (nonDegenerateEquiv.{u} k).val) :=
  (prodStdSimplex.nonDegenerate_iff_injective_objEquiv _).1 (nonDegenerateEquiv k).2

private lemma support_prismMeasure_subset {k : Fin (p + 1)} {z : StdSimplex ℝ (Fin (p + 1)) × I}
    (hz : z ∈ piece k) :
    ↑(prismMeasure z.1 z.2).weights.support ⊆
      Set.range (prodStdSimplex.objEquiv (nonDegenerateEquiv.{u} k).val) := by
  rintro ⟨i, b⟩ hx
  simp only [Finset.mem_coe, Finsupp.mem_support_iff] at hx
  obtain ⟨hk₁, hk₂⟩ := hz
  have hmono := cumSum_mono z.1.nonneg
  rcases (by decide : ∀ b : Fin 2, b = 0 ∨ b = 1) b with rfl | rfl
  · by_cases hi : i ≤ k
    · exact ⟨i.castSucc, objEquiv_nonDegenerateEquiv_castSucc.{u} k i hi⟩
    · refine absurd ?_ hx
      have : cumSum z.1.weights (k.val + 1) ≤ cumSum z.1.weights i.val :=
        hmono (by have := Fin.lt_def.1 (not_le.1 hi); lia)
      rw [prismMeasure_weights]
      simp only [prismWeights, clamp_zero]
      rw [min_eq_right (by linarith [hmono (Nat.le_succ i.val)]), min_eq_right (by linarith),
        sub_self]
  · by_cases hi : k ≤ i
    · exact ⟨i.succ, objEquiv_nonDegenerateEquiv_succ.{u} k i hi⟩
    · refine absurd ?_ hx
      have : cumSum z.1.weights (i.val + 1) ≤ cumSum z.1.weights k.val :=
        hmono (by have := Fin.lt_def.1 (not_le.1 hi); lia)
      rw [prismMeasure_weights]
      simp only [prismWeights, clamp_one]
      rw [max_eq_right (by linarith), max_eq_right (by linarith [hmono (Nat.le_succ i.val)]),
        sub_self]

/-- The barycentric coordinates in the `k`th nondegenerate `(p + 1)`-simplex of `Δ[p] ⊗ Δ[1]` of a
point of the `k`th piece of the prism. -/
private noncomputable def pieceWeights (k : Fin (p + 1)) (z : StdSimplex ℝ (Fin (p + 1)) × I)
    (hz : z ∈ piece k) : StdSimplex ℝ (Fin (p + 2)) :=
  prodStdSimplex.comapWeights (injective_objEquiv_nonDegenerateEquiv.{u} k) _
    (support_prismMeasure_subset hz)

private lemma map_pieceWeights (k : Fin (p + 1)) (z : StdSimplex ℝ (Fin (p + 1)) × I)
    (hz : z ∈ piece k) :
    StdSimplex.map (prodStdSimplex.objEquiv (nonDegenerateEquiv.{u} k).val)
      (pieceWeights.{u} k z hz) = prismMeasure z.1 z.2 :=
  prodStdSimplex.map_comapWeights _ _ _

private lemma continuous_pieceWeights (k : Fin (p + 1)) :
    Continuous fun z : piece k ↦ pieceWeights.{u} k z.1 z.2 := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (p + 2))).continuous_iff]
  exact continuous_pi fun j ↦ (continuous_prismWeights _).comp continuous_subtype_val

/-- The underlying function of `SSet.prodStdSimplex₁.prism`. -/
private noncomputable def prismFun (p : ℕ) (z : StdSimplex ℝ (Fin (p + 1)) × I) :
    |(Δ[p] ⊗ Δ[1] : SSet.{u})| :=
  toTopObjMk (nonDegenerateEquiv (exists_mem_piece z).choose).val
    (pieceWeights.{u} _ z (exists_mem_piece z).choose_spec)

private lemma prismFun_eq {s : StdSimplex ℝ (Fin (p + 1))} {t : I} {n : ℕ}
    (x : (Δ[p] ⊗ Δ[1] : SSet.{u}) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1)))
    (h : StdSimplex.map (prodStdSimplex.objEquiv x) w = prismMeasure s t) :
    prismFun p (s, t) = toTopObjMk x w :=
  prodStdSimplex.toTopObjMk_eq_of_map_eq ((map_pieceWeights _ _ _).trans h.symm)

variable (p) in
/-- The triangulation of the prism `Δᵖ × I` by the nondegenerate `(p + 1)`-simplices of
`Δ[p] ⊗ Δ[1]`, as a continuous map to the geometric realization `|Δ[p] ⊗ Δ[1]|`. For `k ≤ p`, the
points `(s, t)` with `s₀ + ⋯ + s_(k-1) ≤ 1 - t ≤ s₀ + ⋯ + s_k` lie in the realization of the
`k`th simplex `(0, 0), …, (k, 0), (k, 1), …, (p, 1)`. -/
noncomputable def prism : C(StdSimplex ℝ (Fin (p + 1)) × I, |(Δ[p] ⊗ Δ[1] : SSet.{u})|) where
  toFun := prismFun p
  continuous_toFun := by
    refine (locallyFinite_of_finite _).continuous iUnion_piece isClosed_piece fun k ↦ ?_
    rw [continuousOn_iff_continuous_domRestrict]
    have : (piece k).domRestrict (prismFun.{u} p) =
        fun z : piece k ↦ toTopObjMk (nonDegenerateEquiv k).val (pieceWeights.{u} k z.1 z.2) :=
      funext fun z ↦ prismFun_eq _ _ (map_pieceWeights _ _ _)
    rw [this]
    exact (continuous_toTopObjMk _).comp (continuous_pieceWeights.{u} k)

/-- A point of a simplex of `Δ[p] ⊗ Δ[1]` whose coordinates on the vertices are those of `(s, t)` is
the image of `(s, t)` under the triangulation of the prism. -/
private lemma prism_eq {s : StdSimplex ℝ (Fin (p + 1))} {t : I} {n : ℕ}
    (x : (Δ[p] ⊗ Δ[1] : SSet.{u}) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1)))
    (h : StdSimplex.map (prodStdSimplex.objEquiv x) w = prismMeasure s t) :
    prism p (s, t) = toTopObjMk x w :=
  prismFun_eq x w h

/-- The vertex coordinates of the prism are natural in the simplex. -/
private lemma map_prismMeasure {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (s : StdSimplex ℝ (Fin (m + 1))) (t : I) :
    StdSimplex.map (Prod.map f id) (prismMeasure s t) = prismMeasure (StdSimplex.map f s) t := by
  classical
  rw [← StdSimplex.weights_inj]
  ext ⟨i, b⟩
  revert i
  rw [← funext_iff]
  refine eq_of_cumSum_eq fun N ↦ ?_
  obtain ⟨a, ha⟩ := exists_lt_iff_lt f N
  have hcum : cumSum (StdSimplex.map f s).weights N = cumSum s.weights a := by
    rw [cumSum, sum_filter_weights_map f s (fun i ↦ i.val < N), cumSum]
    exact Finset.sum_congr (Finset.filter_congr fun j _ ↦ ha j) fun _ _ ↦ rfl
  have h₁ := sum_filter_weights_map (Prod.map f id) (prismMeasure s t)
    (fun x ↦ x.1.val < N ∧ x.2 = b)
  simp only [Prod.map_fst, Prod.map_snd, id] at h₁
  rw [sum_filter_prod (fun x ↦ (StdSimplex.map (Prod.map f id) (prismMeasure s t)).weights x)
    (fun i ↦ i.val < N), sum_filter_prod (fun x ↦ (prismMeasure s t).weights x)
    (fun j ↦ (f j).val < N)] at h₁
  rw [cumSum, h₁, cumSum, Finset.sum_congr (Finset.filter_congr fun j _ ↦ ha j) fun _ _ ↦ rfl]
  simp only [prismMeasure_weights, prismWeights]
  rw [sum_sub_cumSum s.weights (clamp _ b), sum_sub_cumSum _ (clamp _ b), hcum]

/-- The triangulation of the prism is natural in the simplex. -/
lemma prism_naturality {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (s : StdSimplex ℝ (Fin (m + 1))) (t : I) :
    toTop.map (SSet.stdSimplex.map f ▷ Δ[1]) (prism.{u} m (s, t)) =
      prism n (StdSimplex.map f s, t) := by
  obtain ⟨k, hk⟩ := exists_mem_piece (s, t)
  rw [prism_eq _ _ (map_pieceWeights.{u} k (s, t) hk), toTop_map_toTopObjMk]
  refine (prism_eq _ _ ?_).symm
  rw [← map_prismMeasure, ← map_pieceWeights.{u} k (s, t) hk, StdSimplex.map_map]
  -- The vertices of the image of a simplex under `f ▷ Δ[1]` are those of the simplex, with `f`
  -- applied to the first coordinates.
  rfl

/-- The bottom face `t = 0` of the triangulation of the prism is the bottom inclusion `ι₀`. -/
lemma prism_zero (s : StdSimplex ℝ (Fin (p + 1))) :
    prism.{u} p (s, 0) = toTop.map ι₀ (toTopObjMk (stdSimplex.objEquiv.symm (𝟙 ⦋p⦌)) s) := by
  rw [toTop_map_toTopObjMk]
  refine prism_eq _ _ ?_
  rw [← StdSimplex.weights_inj, StdSimplex.weights_map]
  have hinj : Function.Injective fun i : Fin (p + 1) ↦ (i, (0 : Fin 2)) :=
    fun _ _ h ↦ congrArg Prod.fst h
  -- The vertices of the bottom inclusion of the identity simplex are the `(i, 0)`.
  change Finsupp.mapDomain (fun i ↦ (i, 0)) s.weights = _
  ext ⟨i, b⟩
  rcases (by decide : ∀ b : Fin 2, b = 0 ∨ b = 1) b with rfl | rfl
  · rw [Finsupp.mapDomain_apply_of_injective hinj, prismMeasure_weights]
    simp only [prismWeights, clamp_zero, Set.Icc.coe_zero, sub_zero]
    rw [min_eq_left (cumSum_le_one _ _), min_eq_left (cumSum_le_one _ _), cumSum_succ]
    ring
  · rw [Finsupp.mapDomain_of_notMem_range _ _ (by simp), prismMeasure_weights]
    simp only [prismWeights, clamp_one, Set.Icc.coe_zero, sub_zero]
    rw [max_eq_right (cumSum_le_one _ _), max_eq_right (cumSum_le_one _ _), sub_self]

/-- The top face `t = 1` of the triangulation of the prism is the top inclusion `ι₁`. -/
lemma prism_one (s : StdSimplex ℝ (Fin (p + 1))) :
    prism.{u} p (s, 1) = toTop.map ι₁ (toTopObjMk (stdSimplex.objEquiv.symm (𝟙 ⦋p⦌)) s) := by
  rw [toTop_map_toTopObjMk]
  refine prism_eq _ _ ?_
  rw [← StdSimplex.weights_inj, StdSimplex.weights_map]
  have hinj : Function.Injective fun i : Fin (p + 1) ↦ (i, (1 : Fin 2)) :=
    fun _ _ h ↦ congrArg Prod.fst h
  -- The vertices of the top inclusion of the identity simplex are the `(i, 1)`.
  change Finsupp.mapDomain (fun i ↦ (i, 1)) s.weights = _
  ext ⟨i, b⟩
  rcases (by decide : ∀ b : Fin 2, b = 0 ∨ b = 1) b with rfl | rfl
  · rw [Finsupp.mapDomain_of_notMem_range _ _ (by simp), prismMeasure_weights]
    simp only [prismWeights, clamp_zero, Set.Icc.coe_one, sub_self]
    rw [min_eq_right (cumSum_nonneg _ _), min_eq_right (cumSum_nonneg _ _), sub_self]
  · rw [Finsupp.mapDomain_apply_of_injective hinj, prismMeasure_weights]
    simp only [prismWeights, clamp_one, Set.Icc.coe_one, sub_self]
    rw [max_eq_left (cumSum_nonneg _ _), max_eq_left (cumSum_nonneg _ _), cumSum_succ]
    ring

end prodStdSimplex₁

/-! ### Realization of the cylinder and of homotopies -/

open unitInterval

variable (X) in
/-- The map from `X` to the singular simplicial set of the path space `C(I, |X ⊗ Δ[1]|)` sending
an `n`-simplex `x` to the triangulated prism over it, the composite of
`SSet.prodStdSimplex₁.prism n` with the realization of `x ▷ Δ[1]`. -/
private noncomputable def cylinderPaths :
    X ⟶ TopCat.toSSet.obj (TopCat.of C(I, |X ⊗ Δ[1]|)) where
  app n := ↾fun x ↦ (TopCat.toSSetObjEquiv _ n).symm
    (((toTop.map (yonedaEquiv.symm x ▷ Δ[1])).hom.comp (prodStdSimplex₁.prism _)).curry)
  naturality n m f := by
    ext x
    induction n using Opposite.rec with | op n
    induction m using Opposite.rec with | op m
    induction n using SimplexCategory.rec with | _ n
    induction m using SimplexCategory.rec with | _ m
    obtain ⟨f, rfl⟩ : ∃ g : ⦋m⦌ ⟶ ⦋n⦌, g.op = f := ⟨f.unop, rfl⟩
    apply (TopCat.toSSetObjEquiv _ _).injective
    ext w t
    simp only [TypeCat.Fun.toFun_apply, ConcreteCategory.comp_apply, TypeCat.ofHom_apply,
      Equiv.apply_symm_apply, ContinuousMap.curry_apply, ContinuousMap.comp_apply]
    rw [← yonedaEquiv_symm_naturality_left, MonoidalCategory.comp_whiskerRight, Functor.map_comp,
      TopCat.hom_comp, ContinuousMap.comp_apply, prodStdSimplex₁.prism_naturality]
    -- Both sides are now the singular simplex over `x` precomposed with `StdSimplex.map f`
    -- (`TopCat.toSSetObjEquiv_naturality_apply`).
    rfl

/-- The value of a continuous map out of `|X|` at the point of a simplex is the value of the
corresponding singular simplex. -/
private lemma apply_toTopObjMk {T : TopCat.{u}} (F : |X| ⟶ T) {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    F (toTopObjMk x w) = TopCat.toSSetObjEquiv _ _ ((sSetTopAdj.homEquiv X T F).app _ x) w := by
  rw [Adjunction.homEquiv_unit]
  rfl

/-- The `ι₀` and `ι₁` simplices of the prism over a simplex `x` of `X` are mapped by `x ▷ Δ[1]` to
the `ι₀` and `ι₁` simplices of `X ⊗ Δ[1]` over `x`. -/
private lemma whiskerRight_app_app_objEquiv_symm_id {n : ℕ} (x : X _⦋n⦌) (i : Δ[n] ⟶ Δ[n] ⊗ Δ[1])
    (j : X ⟶ X ⊗ Δ[1]) (hij : i ≫ yonedaEquiv.symm x ▷ Δ[1] = yonedaEquiv.symm x ≫ j) :
    (yonedaEquiv.symm x ▷ Δ[1]).app _ (i.app _ (stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))) =
      j.app _ x := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, hij, NatTrans.comp_app,
    ConcreteCategory.comp_apply, yonedaEquiv_symm_app_objEquiv_symm, op_id,
    CategoryTheory.Functor.map_id]
  rfl

variable (X) in
/-- The triangulation of the realization of the cylinder `X ⊗ Δ[1]`: the continuous map
`|X| × I → |X ⊗ Δ[1]|` which over the realization of each simplex `x` of `X` is the triangulation
`SSet.prodStdSimplex₁.prism` of the prism over `x`. -/
noncomputable def toTopCylinder : C(|X| × I, |X ⊗ Δ[1]|) :=
  ((sSetTopAdj.homEquiv _ _).symm (cylinderPaths X)).hom.uncurry

/-- Over the realization of a simplex, the triangulation of the realized cylinder is the
triangulation of the prism. -/
lemma toTopCylinder_toTopObjMk {n : ℕ} (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) (t : I) :
    toTopCylinder X (toTopObjMk x w, t) =
      toTop.map (yonedaEquiv.symm x ▷ Δ[1]) (prodStdSimplex₁.prism n (w, t)) := by
  have h := apply_toTopObjMk ((sSetTopAdj.homEquiv _ _).symm (cylinderPaths X)) x w
  rw [Equiv.apply_symm_apply] at h
  exact DFunLike.congr_fun h t

/-- The bottom of the triangulation of the realized cylinder is the realization of `ι₀`. -/
@[simp]
lemma toTopCylinder_zero (z : |X|) : toTopCylinder X (z, 0) = toTop.map ι₀ z := by
  refine ConcreteCategory.congr_hom (toTop_hom_ext (g₁ := TopCat.ofHom
    ((toTopCylinder X).comp ⟨fun z ↦ (z, 0), by fun_prop⟩)) fun n x w ↦ ?_) z
  -- Unfold the evaluation of the composite continuous map.
  change toTopCylinder X (toTopObjMk x w, 0) = _
  rw [toTopCylinder_toTopObjMk, prodStdSimplex₁.prism_zero, toTop_map_toTopObjMk,
    toTop_map_toTopObjMk, toTop_map_toTopObjMk,
    whiskerRight_app_app_objEquiv_symm_id x ι₀ ι₀ (ι₀_comp _)]

/-- The top of the triangulation of the realized cylinder is the realization of `ι₁`. -/
@[simp]
lemma toTopCylinder_one (z : |X|) : toTopCylinder X (z, 1) = toTop.map ι₁ z := by
  refine ConcreteCategory.congr_hom (toTop_hom_ext (g₁ := TopCat.ofHom
    ((toTopCylinder X).comp ⟨fun z ↦ (z, 1), by fun_prop⟩)) fun n x w ↦ ?_) z
  -- Unfold the evaluation of the composite continuous map.
  change toTopCylinder X (toTopObjMk x w, 1) = _
  rw [toTopCylinder_toTopObjMk, prodStdSimplex₁.prism_one, toTop_map_toTopObjMk,
    toTop_map_toTopObjMk, toTop_map_toTopObjMk,
    whiskerRight_app_app_objEquiv_symm_id x ι₁ ι₁ (ι₁_comp _)]

/-- The realization of a simplicial homotopy `H` between `f` and `g`: the homotopy between `|f|` and
`|g|` given by the realization of `H.h : X ⊗ Δ[1] ⟶ Y` composed with the triangulation of the
realized cylinder. -/
noncomputable def Homotopy.toTop {f g : X ⟶ Y} (H : Homotopy f g) :
    TopCat.Homotopy (SSet.toTop.map f) (SSet.toTop.map g) where
  -- Inside this declaration `toTop` would refer to `SSet.Homotopy.toTop` itself.
  toFun z := SSet.toTop.map H.h (toTopCylinder X (z.2, z.1))
  continuous_toFun := by fun_prop
  map_zero_left z := by
    rw [toTopCylinder_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp, H.h₀]
  map_one_left z := by
    rw [toTopCylinder_one, ← ConcreteCategory.comp_apply, ← Functor.map_comp, H.h₁]

/-- The realization of a simplicial homotopy equivalence is a homotopy equivalence. -/
noncomputable def toTopHomotopyEquiv (f : X ⟶ Y) (g : Y ⟶ X) (H₁ : Homotopy (f ≫ g) (𝟙 X))
    (H₂ : Homotopy (g ≫ f) (𝟙 Y)) : ContinuousMap.HomotopyEquiv |X| |Y| where
  toFun := (toTop.map f).hom
  invFun := (toTop.map g).hom
  left_inv := by
    have := H₁.toTop
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at this
    exact ⟨this⟩
  right_inv := by
    have := H₂.toTop
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at this
    exact ⟨this⟩

namespace modelCategoryQuillen

/-- A simplicial homotopy equivalence is a weak equivalence. -/
theorem weakEquivalence_of_homotopyEquiv (f : X ⟶ Y) (g : Y ⟶ X) (H₁ : Homotopy (f ≫ g) (𝟙 X))
    (H₂ : Homotopy (g ≫ f) (𝟙 Y)) : WeakEquivalence f :=
  (weakEquivalence_iff f).2 (toTopHomotopyEquiv f g H₁ H₂).isWeakHomotopyEquivalence

/-- A morphism with the right lifting property with respect to all monomorphisms, that is, a
trivial fibration of the Kan–Quillen model structure, is a weak equivalence. -/
theorem weakEquivalence_of_rlp_monomorphisms {p : X ⟶ Y} (hp : (monomorphisms SSet.{u}).rlp p) :
    WeakEquivalence p := by
  have := isSplitEpi_of_rlp_monomorphisms hp
  let h := Shrinking.ofRLP hp (section_ p) (IsSplitEpi.id p)
  exact weakEquivalence_of_homotopyEquiv p h.section_ h.homotopy
    (RelativeMorphism.Homotopy.ofEq (congrArg _ h.section_comp))

end modelCategoryQuillen

end SSet
