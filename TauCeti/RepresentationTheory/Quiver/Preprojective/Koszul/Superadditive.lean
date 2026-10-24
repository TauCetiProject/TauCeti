/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.Algebra.Order.BigOperators.WeightedGrowth
public import TauCeti.RepresentationTheory.Quiver.Preprojective.HilbertSeries.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Resolution
public import TauCeti.RepresentationTheory.Quiver.Symmetrify

/-!
# Koszulity of preprojective algebras over quivers with superadditive weights

Let `Π = Π_k(Q)` be the preprojective algebra of a finite quiver `Q` over a field `k`. The Koszul
complex of the vertex module `S_v`,

```text
0 ⟶ e_v Π ⟶ ⨁_{b : w ⟶ v} e_w Π ⟶ e_v Π ⟶ S_v ⟶ 0,
```

is exact except possibly at its left end, whose defect consists of the `y ∈ e_v Π` killed by every
arrow `b*` of the doubled quiver leaving `v`. This file proves that the defect vanishes as soon as
`Q` carries a **positive superadditive weight**, a weight `δ` on its vertices with `δ_i > 0` and
`2 δ_i ≤ ∑_j (#(i ⟶ j) + #(j ⟶ i)) δ_j` at every vertex. No assumption on the sinks of `Q` or on
its shape is needed: the condition lives at quiver level. For orientations of a connected simple
graph, a connected graph which is not a Dynkin diagram produces such a weight
(`TauCeti.exists_pos_two_mul_le_sum_orientedQuiver_of_not_exists_dynkinType_iso`, in
`Koszul/NonDynkin.lean`), so there the Koszul complexes are projective resolutions and the matrix
Hilbert series of `Π` is `((1 + t²) I - t A)⁻¹`
(`TauCeti.preprojectiveHilbertSeries_eq_inv_of_not_exists_dynkinType_iso`,
`Koszul/NonDynkin.lean`).

## Main results

* `TauCeti.forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_two_mul_le_sum`: **the Koszul
  complex of every vertex module is exact at its left end when `Q` carries a positive
  superadditive weight.**
* `TauCeti.preprojectiveKoszulLeft_injective_of_two_mul_le_sum`: injectivity of the bundled map.
* `TauCeti.mul_preprojectiveHilbertSeries_eq_one_of_two_mul_le_sum` and
  `TauCeti.preprojectiveHilbertSeries_eq_inv_of_two_mul_le_sum`: for such a quiver, with `A` the
  arrow-count matrix of the doubled quiver, `((1 + t²) I - t A) H = I` and `H = ((1 + t²) I -
  t A)⁻¹` for the matrix Hilbert series `H` of `Π`, with no hypothesis on sinks.

## References

* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), for the superadditive weight argument in the non-Dynkin case.
* I. N. Bernstein, I. M. Gelfand and V. A. Ponomarev, *Coxeter functors and Gabriel's theorem*,
  Russian Math. Surveys 28 (1973), for reflection at the sources of a quiver and the splitting of
  simple summands from representations on which a reflection is not faithful.
* I. M. Gelfand and V. A. Ponomarev, *Model algebras and representations of graphs*, Funct. Anal.
  Appl. 13 (1979), where the preprojective algebra is introduced through these reflections.
-/
/-
Proof outline. Fix a vertex `i` and read the graded corners `e_w Π_m e_i` as the layers of the
column `Π e_i`. Two consecutive layers `m` and `m + 1`, with the arrows of the doubled quiver
between them, form a representation of a bipartite quiver whose sources carry `e_• Π_m e_i`. The
Koszul complex says that in degree `m` the left map `y ↦ (b* y)_b` at `v` is exactly the map out of
the source `v`, and that its cokernel is the layer `e_v Π_{m+2} e_i`: the next pair of layers is
the reflection of the previous one at all of its sources.

* The pair of layers `0` and `1` is indecomposable, since `e_• Π_0 e_i` is the line through `e_i`.
* An indecomposable pair with a nonzero element of the Koszul defect in degree `m` is that line
  alone (`LayersIndecomposable.preprojectiveCorner_succ_eq_bot`), so the layer `m + 1` vanishes.
* If the Koszul map is injective in degree `m`, a splitting of the layers `m + 1` and `m + 2` pulls
  back along it to a splitting of the layers `m` and `m + 1`, so indecomposability passes from one
  pair to the next (`LayersIndecomposable.succ`).
* While the Koszul map stays injective the dimensions obey
  `dim e_v Π_{n+2} e_i + dim e_v Π_n e_i = ∑_w #(w ⟶ v) dim e_w Π_{n+1} e_i`, so the weighted
  dimensions `s_n = ∑_w δ_w dim e_w Π_n e_i` satisfy `2 s_{n+1} ≤ s_{n+2} + s_n`, with
  `s_0 = δ_i > 0` and `2 s_0 ≤ s_1`. The increments of `s` are therefore at least `δ_i`, and no
  layer can vanish.

By induction on the degree, the Koszul map is injective in every degree.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

section Quiver

variable (k : Type w) {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

local notation "Π" => preprojectiveAlgebra k Q
local notation "π" => preprojectiveMk k Q
local notation "E" => preprojectiveCorner k Q

/-- A splitting of the layers `e_• Π_m e_i` and `e_• Π_{m+1} e_i` of the column `Π e_i` into two
pieces, vertex by vertex, which every arrow of the doubled quiver respects. -/
private structure IsLayerSplitting (m : ℕ) (i : Symmetrify Q)
    (A B A' B' : Symmetrify Q → Submodule k Π) : Prop where
  inf_eq_bot : ∀ w, A w ⊓ B w = ⊥
  sup_eq : ∀ w, A w ⊔ B w = E m i w
  inf_eq_bot' : ∀ w, A' w ⊓ B' w = ⊥
  sup_eq' : ∀ w, A' w ⊔ B' w = E (m + 1) i w
  mul_mem : ∀ {w l : Symmetrify Q} (b : w ⟶ l), ∀ x ∈ A w, π (ofArrow b) * x ∈ A' l
  mul_mem' : ∀ {w l : Symmetrify Q} (b : w ⟶ l), ∀ x ∈ B w, π (ofArrow b) * x ∈ B' l

/-- The layers `m` and `m + 1` of the column `Π e_i` are indecomposable: one of the two pieces of
every splitting vanishes. -/
private def LayersIndecomposable (m : ℕ) (i : Symmetrify Q) : Prop :=
  ∀ A B A' B' : Symmetrify Q → Submodule k Π, IsLayerSplitting k m i A B A' B' →
    (∀ w, A w = ⊥ ∧ A' w = ⊥) ∨ (∀ w, B w = ⊥ ∧ B' w = ⊥)

variable {k}

private theorem IsLayerSplitting.symm {m : ℕ} {i : Symmetrify Q}
    {A B A' B' : Symmetrify Q → Submodule k Π} (h : IsLayerSplitting k m i A B A' B') :
    IsLayerSplitting k m i B A B' A' where
  inf_eq_bot w := by rw [inf_comm]; exact h.inf_eq_bot w
  sup_eq w := by rw [sup_comm]; exact h.sup_eq w
  inf_eq_bot' w := by rw [inf_comm]; exact h.inf_eq_bot' w
  sup_eq' w := by rw [sup_comm]; exact h.sup_eq' w
  mul_mem := h.mul_mem'
  mul_mem' := h.mul_mem

/-- If the lower piece `B` of a splitting vanishes, so does the upper piece `B'`, since the layer
`e_• Π_{m+1} e_i` is spanned by arrow multiples of the layer below it. -/
private theorem IsLayerSplitting.upper_eq_bot {m : ℕ} {i : Symmetrify Q}
    {A B A' B' : Symmetrify Q → Submodule k Π} (h : IsLayerSplitting k m i A B A' B')
    (hB : ∀ w, B w = ⊥) (l : Symmetrify Q) : B' l = ⊥ := by
  obtain ⟨v, rfl⟩ : ∃ v : Q, Symmetrify.of.obj v = l := ⟨l, rfl⟩
  refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
  obtain ⟨z, hz, rfl⟩ := exists_eq_sum_preprojectiveMk_ofArrow_mul_of_mem_preprojectiveCorner
    ((h.sup_eq' _).le (Submodule.mem_sup_right hx))
  have hA : ∑ w, ∑ b, π (ofArrow b) * z w b ∈ A' (Symmetrify.of.obj v) :=
    sum_mem fun w _ => sum_mem fun b _ => h.mul_mem b _ <| by
      have hzw := hz w b
      rwa [← h.sup_eq w, hB w, sup_bot_eq] at hzw
  have h0 := Submodule.mem_inf.2 ⟨hA, hx⟩
  rwa [h.inf_eq_bot', Submodule.mem_bot] at h0

variable (k) in
/-- The layers `0` and `1` of every column are indecomposable, since `e_• Π_0 e_i` is the line
through `e_i`. -/
private theorem layersIndecomposable_zero (i : Symmetrify Q) : LayersIndecomposable k 0 i := by
  classical
  intro A B A' B' h
  have hle (w : Symmetrify Q) : A w ≤ E 0 i w ∧ B w ≤ E 0 i w :=
    ⟨le_sup_left.trans (h.sup_eq w).le, le_sup_right.trans (h.sup_eq w).le⟩
  -- Away from `i` both pieces of the lower layer vanish.
  have hoff (w : Symmetrify Q) (hw : w ≠ i) : A w = ⊥ ∧ B w = ⊥ := by
    have hE : E 0 i w = ⊥ := by
      rw [← Submodule.finrank_eq_zero, finrank_preprojectiveCorner_zero, ite_eq_right (Ne.symm hw)]
    exact ⟨eq_bot_iff.2 ((hle w).1.trans hE.le), eq_bot_iff.2 ((hle w).2.trans hE.le)⟩
  -- At `i` the lower layer is a line, so one of its two pieces vanishes.
  have := Submodule.finiteDimensional_of_le (hle i).1
  have := Submodule.finiteDimensional_of_le (hle i).2
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (A i) (B i)
  rw [h.sup_eq, h.inf_eq_bot, finrank_bot, add_zero, finrank_preprojectiveCorner_zero,
    ite_eq_left rfl] at hdim
  by_cases hA : Module.finrank k (A i) = 0
  · have hA' (w : Symmetrify Q) : A w = ⊥ := by
      by_cases hw : w = i
      · subst hw
        exact Submodule.finrank_eq_zero.1 hA
      · exact (hoff w hw).1
    exact Or.inl fun w => ⟨hA' w, h.symm.upper_eq_bot hA' w⟩
  · have hB' (w : Symmetrify Q) : B w = ⊥ := by
      by_cases hw : w = i
      · subst hw
        exact Submodule.finrank_eq_zero.1 (by omega)
      · exact (hoff w hw).2
    exact Or.inr fun w => ⟨hB' w, h.upper_eq_bot hB' w⟩

/-- **A nonzero element of the Koszul defect splits off.** If the layers `m` and `m + 1` of the
column `Π e_i` are indecomposable and a nonzero `y ∈ e_v Π_m e_i` is killed by every arrow leaving
`v`, then the line through `y` is a summand of the two layers, so the layer `m + 1` vanishes. -/
private theorem LayersIndecomposable.preprojectiveCorner_succ_eq_bot {m : ℕ} {i : Symmetrify Q}
    (hI : LayersIndecomposable k m i) {v : Q} {y : Π} (hy : y ∈ E m i (Symmetrify.of.obj v))
    (hy0 : y ≠ 0) (hb : ∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
      π (ofArrow (Quiver.reverse b)) * y = 0) (l : Symmetrify Q) : E (m + 1) i l = ⊥ := by
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (k ∙ y)
  have hyE : (k ∙ y) ≤ E m i (Symmetrify.of.obj v) :=
    (Submodule.span_singleton_le_iff_mem _ _).2 hy
  -- Every arrow leaving `v` kills `y`.
  have hb' (l' : Symmetrify Q) (c : Symmetrify.of.obj v ⟶ l') : π (ofArrow c) * y = 0 := by
    simpa only [Quiver.reverse_reverse] using hb l' (Quiver.reverse c)
  -- The line through `y` against a complement of it in the lower layer and all of the upper one.
  let A : Symmetrify Q → Submodule k Π := fun w =>
    if w = Symmetrify.of.obj v then k ∙ y else ⊥
  let B : Symmetrify Q → Submodule k Π := fun w =>
    if w = Symmetrify.of.obj v then C ⊓ E m i w else E m i w
  have hs : IsLayerSplitting k m i A B (fun _ => ⊥) (fun l => E (m + 1) i l) :=
    { inf_eq_bot := fun w => by
        by_cases hw : w = Symmetrify.of.obj v
        · simp only [A, B, hw, ↓reduceIte]
          exact eq_bot_iff.2 ((inf_le_inf_left _ inf_le_left).trans hC.inf_eq_bot.le)
        · simp only [A, B, hw, ↓reduceIte, bot_inf_eq]
      sup_eq := fun w => by
        by_cases hw : w = Symmetrify.of.obj v
        · simp only [A, B, hw, ↓reduceIte]
          rw [← sup_inf_assoc_of_le _ hyE, hC.sup_eq_top, top_inf_eq]
        · simp only [A, B, hw, ↓reduceIte, bot_sup_eq]
      inf_eq_bot' := fun _ => bot_inf_eq _
      sup_eq' := fun _ => bot_sup_eq _
      mul_mem := fun {w l'} b x hx => by
        by_cases hw : w = Symmetrify.of.obj v
        · simp only [A, hw, ↓reduceIte] at hx
          subst hw
          obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
          have hyb : π (ofArrow b) * y = 0 := hb' l' b
          rw [mul_smul_comm, hyb, smul_zero]
          exact Submodule.zero_mem _
        · simp only [A, hw, ↓reduceIte, Submodule.mem_bot] at hx
          rw [hx, mul_zero]
          exact Submodule.zero_mem _
      mul_mem' := fun {w l'} b x hx => by
        have hxE : x ∈ E m i w := by
          by_cases hw : w = Symmetrify.of.obj v
          · simp only [B, hw, ↓reduceIte] at hx
            rw [hw]
            exact hx.2
          · simpa only [B, hw, ↓reduceIte] using hx
        exact preprojectiveMk_ofArrow_mul_mem_preprojectiveCorner b hxE }
  rcases hI A B _ _ hs with h | h
  · have hA := (h (Symmetrify.of.obj v)).1
    simp only [A, ↓reduceIte, Submodule.span_singleton_eq_bot] at hA
    exact absurd hA hy0
  · exact (h l).2

/-- Under injectivity of the Koszul map in degree `m`, a splitting `(A, B, A', B')` of the layers
`m + 1` and `m + 2` writes every `x ∈ e_v Π_m e_i` as `y₁ + y₂`, where the arrows leaving `v` send
`y₁` into `A` and `y₂` into `B`. -/
private theorem IsLayerSplitting.exists_add_eq {m : ℕ} {i : Symmetrify Q}
    {A B A' B' : Symmetrify Q → Submodule k Π} (h : IsLayerSplitting k (m + 1) i A B A' B')
    (hinj : ∀ (v : Q), ∀ y ∈ E m i (Symmetrify.of.obj v),
      (∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
        π (ofArrow (Quiver.reverse b)) * y = 0) → y = 0)
    {v : Q} {x : Π} (hx : x ∈ E m i (Symmetrify.of.obj v)) :
    ∃ y₁ ∈ E m i (Symmetrify.of.obj v), ∃ y₂ ∈ E m i (Symmetrify.of.obj v),
      (∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
        π (ofArrow (Quiver.reverse b)) * y₁ ∈ A w) ∧
      (∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
        π (ofArrow (Quiver.reverse b)) * y₂ ∈ B w) ∧ y₁ + y₂ = x := by
  -- Split every component `b* x` of the image of `x`.
  have hdec (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v) :
      ∃ a ∈ A w, ∃ c ∈ B w, a + c = π (ofArrow (Quiver.reverse b)) * x :=
    Submodule.mem_sup.1 ((h.sup_eq w).ge (preprojectiveMk_ofArrow_mul_mem_preprojectiveCorner _ hx))
  choose α hα β hβ hαβ using hdec
  -- The two halves of `∑_b b (ε_b b* x) = 0` lie in `A'` and in `B'`, so each of them vanishes.
  have hA : ∑ w, ∑ b, π (ofArrow b) * (doubledArrowSign k b • α w b) ∈
      A' (Symmetrify.of.obj v) :=
    sum_mem fun w _ => sum_mem fun b _ => h.mul_mem b _ (Submodule.smul_mem _ _ (hα w b))
  have hB : ∑ w, ∑ b, π (ofArrow b) * (doubledArrowSign k b • β w b) ∈
      B' (Symmetrify.of.obj v) :=
    sum_mem fun w _ => sum_mem fun b _ => h.mul_mem' b _ (Submodule.smul_mem _ _ (hβ w b))
  have hAB : ∑ w, ∑ b, π (ofArrow b) * (doubledArrowSign k b • α w b) +
      ∑ w, ∑ b, π (ofArrow b) * (doubledArrowSign k b • β w b) = 0 := by
    rw [← sum_preprojectiveMk_ofArrow_mul_doubledArrowSign_smul_eq_zero k v x,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by rw [← mul_add, ← smul_add, hαβ]
  have hA0 : ∑ w, ∑ b, π (ofArrow b) * (doubledArrowSign k b • α w b) = 0 := by
    have h0 := Submodule.mem_inf.2
      ⟨hA, (eq_neg_of_add_eq_zero_left hAB).symm ▸ neg_mem hB⟩
    rwa [h.inf_eq_bot', Submodule.mem_bot] at h0
  rw [hA0, zero_add] at hAB
  -- Both halves come from the lower layer, by exactness at the middle term.
  obtain ⟨y₁, hy₁, hα₁⟩ :=
    exists_mem_preprojectiveCorner_of_sum_preprojectiveMk_ofArrow_mul_eq_zero (fun w b =>
      Submodule.smul_mem _ _ ((le_sup_left.trans (h.sup_eq w).le) (hα w b))) hA0
  obtain ⟨y₂, hy₂, hβ₂⟩ :=
    exists_mem_preprojectiveCorner_of_sum_preprojectiveMk_ofArrow_mul_eq_zero (fun w b =>
      Submodule.smul_mem _ _ ((le_sup_right.trans (h.sup_eq w).le) (hβ w b))) hAB
  -- The signs `ε_b` square to `1`.
  have hsign (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v) {a y : Π}
      (hay : doubledArrowSign k b • a =
        doubledArrowSign k b • (π (ofArrow (Quiver.reverse b)) * y)) :
      π (ofArrow (Quiver.reverse b)) * y = a := by
    have h' := congrArg (doubledArrowSign k b • ·) hay
    simpa only [smul_smul, doubledArrowSign_mul_self, one_smul] using h'.symm
  refine ⟨y₁, hy₁, y₂, hy₂, fun w b => hsign w b (hα₁ w b) ▸ hα w b,
    fun w b => hsign w b (hβ₂ w b) ▸ hβ w b, ?_⟩
  -- Their sum differs from `x` by an element of the Koszul defect, which is zero.
  have hz := hinj v (x - (y₁ + y₂)) (sub_mem hx (add_mem hy₁ hy₂)) fun w b => by
    rw [mul_sub, mul_add, hsign w b (hα₁ w b), hsign w b (hβ₂ w b), hαβ, sub_self]
  exact (sub_eq_zero.1 hz).symm

/-- **Indecomposability passes to the next pair of layers.** If the layers `m` and `m + 1` of the
column `Π e_i` are indecomposable and the Koszul map is injective in degree `m`, then the layers
`m + 1` and `m + 2` are indecomposable: a splitting of them pulls back along `y ↦ (b* y)_b`. -/
private theorem LayersIndecomposable.succ {m : ℕ} {i : Symmetrify Q}
    (hI : LayersIndecomposable k m i)
    (hinj : ∀ (v : Q), ∀ y ∈ E m i (Symmetrify.of.obj v),
      (∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
        π (ofArrow (Quiver.reverse b)) * y = 0) → y = 0) :
    LayersIndecomposable k (m + 1) i := by
  intro A B A' B' h
  -- The elements of the lower layer which the arrows leaving their vertex send into `A`.
  let C : (Symmetrify Q → Submodule k Π) → Symmetrify Q → Submodule k Π := fun A v =>
    E m i v ⊓ ⨅ (w : Symmetrify Q) (b : w ⟶ v),
      (A w).comap (LinearMap.mulLeft k (π (ofArrow (Quiver.reverse b))))
  have hC {A : Symmetrify Q → Submodule k Π} {v : Symmetrify Q} {x : Π} :
      x ∈ C A v ↔ x ∈ E m i v ∧ ∀ (w : Symmetrify Q) (b : w ⟶ v),
        π (ofArrow (Quiver.reverse b)) * x ∈ A w := by
    simp only [C, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.mulLeft_apply]
  have hs : IsLayerSplitting k m i (C A) (C B) A B :=
    { inf_eq_bot := fun v => by
        obtain ⟨v, rfl⟩ : ∃ v' : Q, Symmetrify.of.obj v' = v := ⟨v, rfl⟩
        refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
        obtain ⟨hxA, hxB⟩ := Submodule.mem_inf.1 hx
        refine hinj v x (hC.1 hxA).1 fun w b => ?_
        have h0 := Submodule.mem_inf.2 ⟨(hC.1 hxA).2 w b, (hC.1 hxB).2 w b⟩
        rwa [h.inf_eq_bot, Submodule.mem_bot] at h0
      sup_eq := fun v => by
        obtain ⟨v, rfl⟩ : ∃ v' : Q, Symmetrify.of.obj v' = v := ⟨v, rfl⟩
        refine le_antisymm (sup_le inf_le_left inf_le_left) fun x hx => ?_
        obtain ⟨y₁, hy₁, y₂, hy₂, h₁, h₂, rfl⟩ := h.exists_add_eq hinj hx
        exact Submodule.add_mem_sup (hC.2 ⟨hy₁, h₁⟩) (hC.2 ⟨hy₂, h₂⟩)
      inf_eq_bot' := h.inf_eq_bot
      sup_eq' := h.sup_eq
      mul_mem := fun {w l} b x hx => by
        simpa only [Quiver.reverse_reverse] using (hC.1 hx).2 l (Quiver.reverse b)
      mul_mem' := fun {w l} b x hx => by
        simpa only [Quiver.reverse_reverse] using (hC.1 hx).2 l (Quiver.reverse b) }
  rcases hI _ _ _ _ hs with h' | h'
  · exact Or.inl fun w => ⟨(h' w).2, h.symm.upper_eq_bot (fun w => (h' w).2) w⟩
  · exact Or.inr fun w => ⟨(h' w).2, h.upper_eq_bot (fun w => (h' w).2) w⟩

/-- Exactness of the Koszul complex at its left end in every degree and on every graded corner, for
a quiver whose underlying multigraph carries a positive superadditive weight. -/
private theorem eq_zero_of_mem_preprojectiveCorner_of_two_mul_le_sum {S : Type*} [CommRing S]
    [LinearOrder S] [IsStrictOrderedRing S] {δ : Q → S} (hδ : ∀ i, 0 < δ i)
    (hδle : ∀ i, 2 * δ i ≤
      ∑ j, ((Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) : ℕ) : S) * δ j)
    (m : ℕ) (i v : Q) {y : Π} (hy : y ∈ E m (Symmetrify.of.obj i) (Symmetrify.of.obj v))
    (hb : ∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
      π (ofArrow (Quiver.reverse b)) * y = 0) : y = 0 := by
  classical
  induction m using Nat.strong_induction_on generalizing v y with
  | _ m IH =>
  -- The layers `m` and `m + 1` of the column `Π e_i` are indecomposable.
  have hI (n : ℕ) (hn : n ≤ m) : LayersIndecomposable k n (Symmetrify.of.obj i) := by
    induction n with
    | zero => exact layersIndecomposable_zero k _
    | succ n ihn => exact (ihn (by omega)).succ fun v _ hy hb => IH n (by omega) v hy hb
  by_contra hy0
  have hE := (hI m le_rfl).preprojectiveCorner_succ_eq_bot hy hy0 hb
  -- The weighted dimensions of the layers of the column `Π e_i`.
  set s : ℕ → S := fun n => ∑ w : Q, δ w *
    (Module.finrank k (E n (Symmetrify.of.obj i) (Symmetrify.of.obj w)) : S) with hs
  have hs0 : s 0 = δ i := by
    simp only [hs]
    rw [Finset.sum_eq_single i (fun w _ hw => by
      rw [finrank_preprojectiveCorner_zero,
        ite_eq_right fun h => hw (symmetrify_of_obj_bijective.injective h).symm, Nat.cast_zero,
        mul_zero]) (fun h => absurd (Finset.mem_univ i) h),
      finrank_preprojectiveCorner_zero, ite_eq_left rfl, Nat.cast_one, mul_one]
  have hs1 : 2 * s 0 ≤ s 1 := by
    rw [hs0]
    refine (hδle i).trans_eq (Finset.sum_congr rfl fun w _ => ?_)
    rw [finrank_preprojectiveCorner_one, card_symmetrify_hom, mul_comm]
  -- While the Koszul map is injective, the dimensions obey the Koszul recursion.
  have hrec (j : ℕ) (hj : j + 2 ≤ m + 1) : 2 * s (j + 1) ≤ s (j + 2) + s j := by
    have hv (v : Q) : ∑ w : Q, Fintype.card (Symmetrify.of.obj w ⟶ Symmetrify.of.obj v) *
        Module.finrank k (E (j + 1) (Symmetrify.of.obj i) (Symmetrify.of.obj w)) =
          Module.finrank k (E (j + 2) (Symmetrify.of.obj i) (Symmetrify.of.obj v)) +
            Module.finrank k (E j (Symmetrify.of.obj i) (Symmetrify.of.obj v)) := by
      -- The vertices of the doubled quiver are those of `Q`.
      rw [Fintype.sum_equiv (Equiv.ofBijective _ symmetrify_of_obj_bijective)
        (fun w : Q => Fintype.card (Symmetrify.of.obj w ⟶ Symmetrify.of.obj v) *
          Module.finrank k (E (j + 1) (Symmetrify.of.obj i) (Symmetrify.of.obj w)))
        (fun w : Symmetrify Q => Fintype.card (w ⟶ Symmetrify.of.obj v) *
          Module.finrank k (E (j + 1) (Symmetrify.of.obj i) w)) fun _ => rfl]
      exact (sum_card_mul_finrank_preprojectiveCorner_eq_iff k Q j _ v).2
        fun y hy hb => IH j (by omega) v hy hb
    calc 2 * s (j + 1)
        = ∑ w : Q, 2 * δ w *
            (Module.finrank k (E (j + 1) (Symmetrify.of.obj i) (Symmetrify.of.obj w)) : S) := by
          simp only [hs, Finset.mul_sum, mul_assoc]
      _ ≤ ∑ w : Q, (∑ v : Q,
            ((Fintype.card (w ⟶ v) + Fintype.card (v ⟶ w) : ℕ) : S) * δ v) *
            (Module.finrank k (E (j + 1) (Symmetrify.of.obj i) (Symmetrify.of.obj w)) : S) :=
          Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (hδle w) (Nat.cast_nonneg _)
      _ = ∑ v : Q, δ v *
            ((∑ w : Q, Fintype.card (Symmetrify.of.obj w ⟶ Symmetrify.of.obj v) *
              Module.finrank k (E (j + 1) (Symmetrify.of.obj i) (Symmetrify.of.obj w)) : ℕ) :
                S) := by
          simp only [Finset.sum_mul, Finset.mul_sum, Nat.cast_sum, Nat.cast_mul,
            card_symmetrify_hom]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
          push_cast
          ring
      _ = s (j + 2) + s j := by
          simp only [hv, hs, Nat.cast_add, mul_add, Finset.sum_add_distrib]
  -- But the layer `m + 1` vanishes, while the weighted dimensions stay positive.
  have hz : s (m + 1) = 0 :=
    Finset.sum_eq_zero fun w _ => by rw [hE, finrank_bot, Nat.cast_zero, mul_zero]
  exact ((mul_pos (Nat.cast_add_one_pos _) (hs0 ▸ hδ i)).trans_le
    (add_one_mul_le_of_two_mul_le_add hs1 hrec)).ne' hz

variable (k)

/-- **Exactness of the Koszul complex at its left end, for a quiver with a positive superadditive
weight.** Let `δ` be a weight on the vertices of a finite quiver `Q` with `δ_i > 0` and
`2 δ_i ≤ ∑_j (#(i ⟶ j) + #(j ⟶ i)) δ_j` at every vertex, that is `(2I - A) δ ≤ 0` for the
adjacency matrix `A` of the underlying multigraph. If `y = e_v y` in the preprojective algebra of
`Q` over a field `k`, then `b* y = 0` for every arrow `b` of the doubled quiver into `v` exactly
when `y = 0`. -/
theorem forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_two_mul_le_sum {S : Type*}
    [CommRing S] [LinearOrder S] [IsStrictOrderedRing S] {δ : Q → S} (hδ : ∀ i, 0 < δ i)
    (hδle : ∀ i, 2 * δ i ≤
      ∑ j, ((Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) : ℕ) : S) * δ j)
    (v : Q) {y : Π} (hy : π (doubledVertexIdempotent k v) * y = y) :
    (∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
      π (ofArrow (Quiver.reverse b)) * y = 0) ↔ y = 0 :=
  ⟨eq_zero_of_forall_mem_preprojectiveCorner
      (fun m i _ hy' hb' => eq_zero_of_mem_preprojectiveCorner_of_two_mul_le_sum hδ hδle m i v hy'
        hb') hy,
    fun h w b => by rw [h, mul_zero]⟩

/-- For a quiver with a positive superadditive weight, the left Koszul differential at each vertex
is injective. -/
theorem preprojectiveKoszulLeft_injective_of_two_mul_le_sum {S : Type*} [CommRing S]
    [LinearOrder S] [IsStrictOrderedRing S] {δ : Q → S} (hδ : ∀ i, 0 < δ i)
    (hδle : ∀ i, 2 * δ i ≤
      ∑ j, ((Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) : ℕ) : S) * δ j)
    (v : Q) : Function.Injective (preprojectiveKoszulLeft k v) :=
  (preprojectiveKoszulLeft_injective_iff k v).2 fun _ hy =>
    (forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_two_mul_le_sum k hδ hδle v hy).1

variable [DecidableEq Q]

/-- **The Hilbert series identity for a quiver with a superadditive weight.** Let `δ` be a weight
on the vertices of a finite quiver `Q` over a strictly ordered commutative ring, positive with

```text
2 δ_i ≤ ∑_j (#(i ⟶ j) + #(j ⟶ i)) δ_j
```

at every vertex. No hypothesis on the sinks of `Q` is needed: the matrix Hilbert series `H` of `Π`
satisfies `((1 + X²) I - X A) H = I` for `A_{v,w} = #(w ⟶ v)` the arrow-count matrix of the doubled
quiver. -/
theorem mul_preprojectiveHilbertSeries_eq_one_of_two_mul_le_sum {S : Type*} [CommRing S]
    [LinearOrder S] [IsStrictOrderedRing S] {δ : Q → S} (hδ : ∀ i, 0 < δ i)
    (hδle : ∀ i, 2 * δ i ≤
      ∑ j, ((Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) : ℕ) : S) * δ j) :
    (((1 : PowerSeries ℤ) + PowerSeries.X ^ 2) • (1 : Matrix Q Q (PowerSeries ℤ)) -
        (PowerSeries.X : PowerSeries ℤ) • Matrix.of fun v w : Q =>
          (Fintype.card (Symmetrify.of.obj w ⟶ Symmetrify.of.obj v) : PowerSeries ℤ)) *
      preprojectiveHilbertSeries k Q = 1 :=
  (mul_preprojectiveHilbertSeries_eq_one_iff k Q).2 fun v _ hy =>
    (forall_preprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_two_mul_le_sum k hδ hδle v hy).1

/-- **The Hilbert series of a preprojective algebra whose quiver carries a superadditive weight**
is the inverse matrix `H = ((1 + X²) I - X A)⁻¹`, under the same hypothesis on `δ`. -/
theorem preprojectiveHilbertSeries_eq_inv_of_two_mul_le_sum {S : Type*} [CommRing S]
    [LinearOrder S] [IsStrictOrderedRing S] {δ : Q → S} (hδ : ∀ i, 0 < δ i)
    (hδle : ∀ i, 2 * δ i ≤
      ∑ j, ((Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) : ℕ) : S) * δ j) :
    preprojectiveHilbertSeries k Q =
      (((1 : PowerSeries ℤ) + PowerSeries.X ^ 2) • (1 : Matrix Q Q (PowerSeries ℤ)) -
        (PowerSeries.X : PowerSeries ℤ) • Matrix.of fun v w : Q =>
          (Fintype.card (Symmetrify.of.obj w ⟶ Symmetrify.of.obj v) : PowerSeries ℤ))⁻¹ :=
  (Matrix.inv_eq_right_inv
    (mul_preprojectiveHilbertSeries_eq_one_of_two_mul_le_sum k hδ hδle)).symm

end Quiver
end TauCeti
