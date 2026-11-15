/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Extreme
public import TauCeti.NumberTheory.Height.Twisted.Weight.Slope
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# The Harder--Narasimhan filtration of a weighted system of linear forms

For a finite-dimensional vector space `V` equipped with spanning finite families of linear forms
`L v` and finitely supported real weights `c v`, iterating `exceptionalSubspace` downward from `⊤`
constructs a strictly increasing chain of subspaces `⊥ = T₀ < T₁ < ⋯ < Tᵣ = ⊤`, exposed here as
`twistedFiltration L c`.

Measuring segment slopes by `weightSlope L c U W = (weight L c W - weight L c U) / (dim W - dim U)`
(the quantity `μ(W, U)` in Evertse--Ferretti, §15, (15.5), defined in
`TauCeti.NumberTheory.Height.Twisted.Weight.Slope`), the consecutive slopes of
`twistedFiltration L c` are strictly decreasing. Every segment line supports the set of dimension
and weight pairs `(dim U, weight U)` from above across all subspaces `U` of `V`, and any subspace
lying on the `i`-th supporting line sits between `Tᵢ` and `Tᵢ₊₁`. Consequently each `Tᵢ` is the
unique subspace of its dimension achieving at least `weight L c Tᵢ`, and the pairs
`(finrank K T, weight L c T)` for `T ∈ twistedFiltration L c` are precisely the extreme points of
the upper convex hull hypograph of `{(finrank K U, weight L c U)}`.

## Main definitions

* `TauCeti.twistedFiltration`: the strictly increasing Harder--Narasimhan filtration `⊥ = T₀ < ⋯ <
  Tᵣ = ⊤` obtained by repeatedly passing to the exceptional subspace on restricted forms.

## Main results

* `TauCeti.isChain_lt_twistedFiltration`, `TauCeti.head_twistedFiltration`,
  `TauCeti.getLast_twistedFiltration`, `TauCeti.length_twistedFiltration_le_finrank_add_one`:
  structural chain properties.
* `TauCeti.getElem_length_sub_two_twistedFiltration`: on a nontrivial space, the penultimate term
  of `twistedFiltration L c` is `exceptionalSubspace L c`.
* `TauCeti.strictAnti_weightSlope_twistedFiltration`: consecutive segment slopes strictly decrease.
* `TauCeti.weight_sub_weightSlope_mul_finrank_le`,
  `TauCeti.weight_sub_weightSlope_mul_finrank_le_left`, and
  `TauCeti.le_and_le_of_weight_sub_weightSlope_mul_finrank_eq`: global supporting-line upper bounds
  and interval containment on equality.
* `TauCeti.eq_of_mem_twistedFiltration_of_finrank_eq_of_le_weight` and
  `TauCeti.weight_le_of_mem_twistedFiltration_of_finrank_eq`: each filtration subspace uniquely
  maximizes weight among all subspaces of its dimension.
* `TauCeti.extremePoints_convexHull_finrank_le_weight`: the vertices of the upper convex hull of
  `{(finrank K U, weight L c U)}` are exactly the points `(finrank K T, weight L c T)` for
  `T ∈ twistedFiltration L c`.
* `TauCeti.twistedFiltration_fin_two_proj_of_lt`: for two coordinate forms with distinct weights at
  a single place, the filtration is `[⊥, K ∙ e₂, ⊤]`.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
  §15, (15.5) and Lemma 15.4.
-/

public noncomputable section

open Function Module Submodule Set

namespace TauCeti

section Filtration

variable {K V ι Ω : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
  [FiniteDimensional K V]

/-- One top-down step of the Harder--Narasimhan filtration inside `W`: the exceptional subspace for
the forms restricted to `W`, mapped back into `V`. -/
private def nextSubspace (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (W : Submodule K V) : Submodule K V :=
  (exceptionalSubspace (fun v i ↦ (L v i).comp W.subtype) c).map W.subtype

private theorem nextSubspace_le (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (W : Submodule K V) : nextSubspace L c W ≤ W :=
  Submodule.map_subtype_le W _

private theorem nextSubspace_bot (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    nextSubspace L c ⊥ = ⊥ :=
  eq_bot_iff.mpr (nextSubspace_le L c ⊥)

private theorem nextSubspace_lt (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    {W : Submodule K V} (hW : W ≠ ⊥) : nextSubspace L c W < W := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  have hne := exceptionalSubspace_ne_top (fun v i ↦ (L v i).comp W.subtype) c
  refine lt_of_le_of_ne (nextSubspace_le L c W) fun heq ↦ hne ?_
  simpa [nextSubspace, Submodule.comap_map_eq_of_injective W.injective_subtype,
    Submodule.comap_subtype_self] using congrArg (Submodule.comap W.subtype) heq

private theorem finrank_nextSubspace_lt (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    {W : Submodule K V} (hW : W ≠ ⊥) :
    finrank K ↥(nextSubspace L c W) < finrank K W :=
  Submodule.finrank_lt_finrank_of_lt (nextSubspace_lt L c hW)

private theorem nextSubspace_top (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    nextSubspace L c ⊤ = exceptionalSubspace L c :=
  map_exceptionalSubspace_comp_linearEquiv L c (LinearEquiv.ofTop ⊤ rfl)

private theorem map_nextSubspace_comp_of_injective (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    {f : M →ₗ[K] V} (hf : Function.Injective f) (U : Submodule K M) :
    (nextSubspace (fun v i ↦ (L v i).comp f) c U).map f = nextSubspace L c (U.map f) := by
  let e : U ≃ₗ[K] U.map f := Submodule.equivMapOfInjective f hf U
  have hforms : (fun v i ↦ ((L v i).comp f).comp U.subtype) =
      fun v i ↦ ((L v i).comp (U.map f).subtype).comp e.toLinearMap := by
    ext v i x; simp [e]
  have hsub : f.comp U.subtype = (U.map f).subtype.comp e.toLinearMap := by
    ext x; simp [e]
  rw [nextSubspace, hforms, ← Submodule.map_comp, hsub, Submodule.map_comp,
    map_exceptionalSubspace_comp_linearEquiv _ c e, nextSubspace]

/-- Top-down recursive chain `⊥ = T₀ < ⋯ < Tₖ = W` inside `W`. -/
private def twistedFiltrationAux (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (W : Submodule K V) : List (Submodule K V) :=
  open Classical in
  if _hW : W = ⊥ then [⊥]
  else twistedFiltrationAux L c (nextSubspace L c W) ++ [W]
termination_by finrank K W
decreasing_by exact finrank_nextSubspace_lt L c _hW

private theorem twistedFiltrationAux_bot (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    twistedFiltrationAux L c ⊥ = [⊥] := by rw [twistedFiltrationAux]; simp

private theorem twistedFiltrationAux_of_ne_bot (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    {W : Submodule K V} (hW : W ≠ ⊥) :
    twistedFiltrationAux L c W = twistedFiltrationAux L c (nextSubspace L c W) ++ [W] := by
  rw [twistedFiltrationAux]; simp [hW]

private theorem map_twistedFiltrationAux_comp_of_injective
    (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    {f : M →ₗ[K] V} (hf : Function.Injective f) (U : Submodule K M) :
    (twistedFiltrationAux (fun v i ↦ (L v i).comp f) c U).map (Submodule.map f) =
      twistedFiltrationAux L c (U.map f) := by
  by_cases hU : U = ⊥
  · subst U; simp [twistedFiltrationAux_bot]
  · have hmap : U.map f ≠ ⊥ := fun h ↦ hU <| eq_bot_iff.mpr fun x hx ↦ by
      have hx' : f x ∈ (⊥ : Submodule K V) := h ▸ Submodule.mem_map_of_mem hx
      exact hf (by simpa using hx')
    rw [twistedFiltrationAux_of_ne_bot _ c hU, twistedFiltrationAux_of_ne_bot L c hmap,
      List.map_append, List.map_singleton, ← map_nextSubspace_comp_of_injective L c hf U,
      map_twistedFiltrationAux_comp_of_injective L c hf (nextSubspace _ c U)]
termination_by finrank K U
decreasing_by exact finrank_nextSubspace_lt _ c hU

/-- The Harder--Narasimhan filtration `⊥ = T₀ < T₁ < ⋯ < Tᵣ = ⊤` of a weighted system of linear
forms (Evertse--Ferretti, §15, Lemma 15.4). On a zero-dimensional space it is `[⊥]`; on a
nontrivial space with invalid (non-spanning or infinitely supported) data it is `[⊥, ⊤]`. -/
def twistedFiltration (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    List (Submodule K V) :=
  twistedFiltrationAux L c ⊤

private theorem twistedFiltrationAux_eq_map_subtype
    (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) (W : Submodule K V) :
    twistedFiltrationAux L c W =
      (twistedFiltration (fun v i ↦ (L v i).comp W.subtype) c).map (Submodule.map W.subtype) := by
  simpa only [twistedFiltration, Submodule.map_subtype_top] using
    (map_twistedFiltrationAux_comp_of_injective L c W.injective_subtype ⊤).symm

/-- Pulling forms back along a linear equivalence transports every subspace in
`twistedFiltration` to its image. -/
theorem map_twistedFiltration_comp_linearEquiv
    (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M] (e : M ≃ₗ[K] V) :
    (twistedFiltration (fun v i ↦ (L v i).comp e.toLinearMap) c).map
      (Submodule.map e.toLinearMap) = twistedFiltration L c := by
  have htop : (⊤ : Submodule K M).map e.toLinearMap = ⊤ := by rw [Submodule.map_top, e.range]
  simpa only [twistedFiltration, htop] using
    map_twistedFiltrationAux_comp_of_injective L c e.injective ⊤

/-- On a zero-dimensional space, the filtration is the single-term list `[⊥]`. -/
@[simp]
theorem twistedFiltration_of_subsingleton [Subsingleton V]
    (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    twistedFiltration L c = [⊥] := by
  rw [twistedFiltration, Subsingleton.elim (⊤ : Submodule K V) ⊥, twistedFiltrationAux_bot]

/-- On a nontrivial space, `twistedFiltration L c` is obtained by mapping the filtration of the
forms restricted to `exceptionalSubspace L c` into `V` and appending `⊤`. -/
theorem twistedFiltration_eq_append_top [Nontrivial V]
    (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    twistedFiltration L c =
      (twistedFiltration (fun v i ↦ (L v i).comp (exceptionalSubspace L c).subtype) c).map
        (Submodule.map (exceptionalSubspace L c).subtype) ++ [⊤] := by
  rw [twistedFiltration, twistedFiltrationAux_of_ne_bot L c top_ne_bot, nextSubspace_top,
    twistedFiltrationAux_eq_map_subtype]

private theorem twistedFiltrationAux_ne_nil (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (W : Submodule K V) : twistedFiltrationAux L c W ≠ [] := by
  by_cases hW : W = ⊥
  · simp [hW, twistedFiltrationAux_bot]
  · simp [twistedFiltrationAux_of_ne_bot L c hW]

/-- The filtration is never empty. -/
@[simp]
theorem twistedFiltration_ne_nil (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    twistedFiltration L c ≠ [] :=
  twistedFiltrationAux_ne_nil L c ⊤

/-- The filtration has positive length. -/
theorem length_twistedFiltration_pos (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    0 < (twistedFiltration L c).length :=
  List.length_pos_iff_ne_nil.mpr (twistedFiltration_ne_nil L c)

private theorem head_twistedFiltrationAux (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (W : Submodule K V) :
    (twistedFiltrationAux L c W).head (twistedFiltrationAux_ne_nil L c W) = ⊥ := by
  by_cases hW : W = ⊥
  · subst W; simp [twistedFiltrationAux_bot]
  · simp only [twistedFiltrationAux_of_ne_bot L c hW,
      List.head_append_of_ne_nil (twistedFiltrationAux_ne_nil L c _)]
    exact head_twistedFiltrationAux L c (nextSubspace L c W)
termination_by finrank K W
decreasing_by exact finrank_nextSubspace_lt L c hW

/-- The first term of `twistedFiltration L c` is `⊥`. -/
@[simp]
theorem head_twistedFiltration (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    (twistedFiltration L c).head (twistedFiltration_ne_nil L c) = ⊥ :=
  head_twistedFiltrationAux L c ⊤

/-- Index `0` of `twistedFiltration L c` is `⊥`. -/
@[simp]
theorem getElem_zero_twistedFiltration (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    (twistedFiltration L c)[0]'(length_twistedFiltration_pos L c) = ⊥ := by
  rw [← List.head_eq_getElem_zero (twistedFiltration_ne_nil L c), head_twistedFiltration]

private theorem getLast_twistedFiltrationAux (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (W : Submodule K V) :
    (twistedFiltrationAux L c W).getLast (twistedFiltrationAux_ne_nil L c W) = W := by
  by_cases hW : W = ⊥
  · subst W; simp [twistedFiltrationAux_bot]
  · simp [twistedFiltrationAux_of_ne_bot L c hW]

private theorem getElem_length_sub_one_twistedFiltrationAux
    (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) (W : Submodule K V) :
    (twistedFiltrationAux L c W)[(twistedFiltrationAux L c W).length - 1]'(by
      have := List.length_pos_iff_ne_nil.mpr (twistedFiltrationAux_ne_nil L c W); omega) = W := by
  rw [← List.getLast_eq_getElem (twistedFiltrationAux_ne_nil L c W), getLast_twistedFiltrationAux]

/-- The last term of `twistedFiltration L c` is `⊤`. -/
@[simp]
theorem getLast_twistedFiltration (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    (twistedFiltration L c).getLast (twistedFiltration_ne_nil L c) = ⊤ :=
  getLast_twistedFiltrationAux L c ⊤

/-- The last index of `twistedFiltration L c` equals `⊤`. -/
@[simp]
theorem getElem_length_sub_one_twistedFiltration (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    (twistedFiltration L c)[(twistedFiltration L c).length - 1]'(by
      have := length_twistedFiltration_pos L c; omega) = ⊤ :=
  getElem_length_sub_one_twistedFiltrationAux L c ⊤

private theorem isChain_lt_twistedFiltrationAux (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (W : Submodule K V) : (twistedFiltrationAux L c W).IsChain (· < ·) := by
  by_cases hW : W = ⊥
  · subst W; simp [twistedFiltrationAux_bot]
  · rw [twistedFiltrationAux_of_ne_bot L c hW]
    refine (isChain_lt_twistedFiltrationAux L c (nextSubspace L c W)).append
      (List.isChain_singleton W) fun x hx y hy ↦ ?_
    simp only [Option.mem_def, List.getLast?_eq_some_getLast (twistedFiltrationAux_ne_nil L c _),
      List.head?_cons, Option.some.injEq] at hx hy
    subst hx hy
    simpa [getLast_twistedFiltrationAux] using nextSubspace_lt L c hW
termination_by finrank K W
decreasing_by exact finrank_nextSubspace_lt L c hW

/-- `twistedFiltration L c` is a strictly increasing chain of submodules. -/
theorem isChain_lt_twistedFiltration (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    (twistedFiltration L c).IsChain (· < ·) :=
  isChain_lt_twistedFiltrationAux L c ⊤

/-- Each term of `twistedFiltration L c` is strictly contained in the next term. -/
theorem getElem_lt_getElem_succ_twistedFiltration
    (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (i : Fin ((twistedFiltration L c).length - 1)) :
    (twistedFiltration L c)[i.val]'(by omega) <
      (twistedFiltration L c)[i.val + 1]'(by omega) :=
  (isChain_lt_twistedFiltration L c).getElem i.val (by omega)

/-- Every earlier term of `twistedFiltration L c` is strictly contained in every later term. -/
theorem pairwise_lt_twistedFiltration (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    (twistedFiltration L c).Pairwise (· < ·) :=
  List.isChain_iff_pairwise.mp (isChain_lt_twistedFiltration L c)

/-- `twistedFiltration L c` has no duplicate terms. -/
theorem nodup_twistedFiltration (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    (twistedFiltration L c).Nodup :=
  (pairwise_lt_twistedFiltration L c).imp ne_of_lt

/-- Subspace dimensions strictly increase along `twistedFiltration L c`. -/
theorem strictMono_finrank_twistedFiltration (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    StrictMono fun i : Fin (twistedFiltration L c).length ↦
      finrank K (twistedFiltration L c)[i.val] := by
  intro i j hij
  exact Submodule.finrank_lt_finrank_of_lt
    (List.pairwise_iff_getElem.mp (pairwise_lt_twistedFiltration L c) i.val j.val i.isLt j.isLt hij)

/-- `twistedFiltration L c` has at most `finrank K V + 1` terms. -/
theorem length_twistedFiltration_le_finrank_add_one
    (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    (twistedFiltration L c).length ≤ finrank K V + 1 := by
  simpa using Fintype.card_le_of_injective
    (fun i : Fin (twistedFiltration L c).length ↦
      (⟨finrank K (twistedFiltration L c)[i.val],
        Nat.lt_succ_of_le (Submodule.finrank_le _)⟩ : Fin (finrank K V + 1)))
    fun i j h ↦ (strictMono_finrank_twistedFiltration L c).injective (congrArg Fin.val h)

/-- On a nontrivial space, `twistedFiltration L c` has at least two terms. -/
theorem two_le_length_twistedFiltration [Nontrivial V]
    (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    2 ≤ (twistedFiltration L c).length := by
  rw [twistedFiltration, twistedFiltrationAux_of_ne_bot L c top_ne_bot, List.length_append,
    List.length_singleton]
  have := List.length_pos_iff_ne_nil.mpr (twistedFiltrationAux_ne_nil L c (nextSubspace L c ⊤))
  omega

/-- The filtration equals `[⊥]` if and only if the ambient space is zero-dimensional. -/
theorem twistedFiltration_eq_singleton_bot_iff
    (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    twistedFiltration L c = [⊥] ↔ Subsingleton V := by
  refine ⟨fun h ↦ not_nontrivial_iff_subsingleton.mp fun _ ↦ ?_,
    fun _ ↦ twistedFiltration_of_subsingleton L c⟩
  have hlen := two_le_length_twistedFiltration L c
  rw [h, List.length_singleton] at hlen; omega

/-- On a nontrivial space, the penultimate term of `twistedFiltration L c` is
`exceptionalSubspace L c`. -/
theorem getElem_length_sub_two_twistedFiltration [Nontrivial V]
    (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    (twistedFiltration L c)[(twistedFiltration L c).length - 2]'(by
      have := two_le_length_twistedFiltration L c; omega) = exceptionalSubspace L c := by
  let l := twistedFiltrationAux L c (exceptionalSubspace L c)
  have hdecomp : twistedFiltration L c = l ++ [⊤] := by
    rw [twistedFiltration, twistedFiltrationAux_of_ne_bot L c top_ne_bot, nextSubspace_top]
  have hpos : 0 < l.length :=
    List.length_pos_iff_ne_nil.mpr (twistedFiltrationAux_ne_nil L c _)
  have hget : (l ++ [⊤])[(l ++ [⊤]).length - 2]'(by simp) = exceptionalSubspace L c := by
    have hidx : (l ++ [⊤]).length - 2 = l.length - 1 := by simp
    simp only [hidx]
    rw [List.getElem_append_left (by omega)]
    exact getElem_length_sub_one_twistedFiltrationAux L c _
  simpa only [hdecomp] using hget

/-- On a nontrivial space, the filtration is the two-term list `[⊥, ⊤]` if and only if the
exceptional subspace is `⊥`. -/
theorem twistedFiltration_eq_pair_bot_top_iff [Nontrivial V]
    (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    twistedFiltration L c = [⊥, ⊤] ↔ exceptionalSubspace L c = ⊥ := by
  refine ⟨fun h ↦ by simpa [h] using (getElem_length_sub_two_twistedFiltration L c).symm,
    fun h ↦ ?_⟩
  rw [twistedFiltration, twistedFiltrationAux_of_ne_bot L c top_ne_bot, nextSubspace_top, h,
    twistedFiltrationAux_bot]; rfl

/-- Failure of spanning on a nontrivial space gives the fallback filtration `[⊥, ⊤]`. -/
@[simp]
theorem twistedFiltration_of_not_forall_span_eq_top [Nontrivial V]
    {L : Ω → ι → Module.Dual K V} {c : Ω → ι → ℝ} (hL : ¬∀ v, span K (range (L v)) = ⊤) :
    twistedFiltration L c = [⊥, ⊤] :=
  (twistedFiltration_eq_pair_bot_top_iff L c).mpr
    (exceptionalSubspace_eq_bot_of_not_forall_span_eq_top hL)

/-- Failure of finite weight support on a nontrivial space gives the fallback filtration
`[⊥, ⊤]`. -/
@[simp]
theorem twistedFiltration_of_not_hasFiniteSupport [Nontrivial V]
    {L : Ω → ι → Module.Dual K V} {c : Ω → ι → ℝ} (hc : ¬HasFiniteSupport c) :
    twistedFiltration L c = [⊥, ⊤] :=
  (twistedFiltration_eq_pair_bot_top_iff L c).mpr
    (exceptionalSubspace_eq_bot_of_not_hasFiniteSupport hc)

/-- Zero form weights on a nontrivial space give the two-term filtration `[⊥, ⊤]`, showing in
particular that the filtration need not be a complete flag in dimension at least `2`. -/
@[simp]
theorem twistedFiltration_zero [Nontrivial V] (L : Ω → ι → Module.Dual K V) :
    twistedFiltration L 0 = [⊥, ⊤] :=
  (twistedFiltration_eq_pair_bot_top_iff L 0).mpr (exceptionalSubspace_zero L)

/-- Under total weight zero, the filtration on a nontrivial space is `[⊥, ⊤]` if and only if every
proper subspace has nonpositive weight (semistability). -/
theorem twistedFiltration_eq_pair_bot_top_iff_of_weight_top_eq_zero [Nontrivial V]
    {L : Ω → ι → Module.Dual K V} (hL : ∀ v, span K (range (L v)) = ⊤)
    {c : Ω → ι → ℝ} (hc : HasFiniteSupport c) (htop : weight L c ⊤ = 0) :
    twistedFiltration L c = [⊥, ⊤] ↔ ∀ U, U ≠ ⊤ → weight L c U ≤ 0 := by
  rw [twistedFiltration_eq_pair_bot_top_iff,
    exceptionalSubspace_eq_bot_iff_of_weight_top_eq_zero hL hc htop]

/-! ### Slope monotonicity and supporting-line bounds -/

omit [Fintype ι] [FiniteDimensional K V] in
private theorem forall_span_range_comp_subtype_eq_top
    {L : Ω → ι → Module.Dual K V} (hL : ∀ v, span K (range (L v)) = ⊤)
    (W : Submodule K V) :
    ∀ v, span K (range fun i ↦ (L v i).comp W.subtype) = ⊤ := fun v ↦
  Module.Dual.span_range_comp_eq_top_of_injective (hL v) W.injective_subtype

private theorem weight_sub_weightSlope_nextSubspace_le
    {L : Ω → ι → Module.Dual K V} (hL : ∀ v, span K (range (L v)) = ⊤)
    {c : Ω → ι → ℝ} (hc : HasFiniteSupport c)
    {U W : Submodule K V} (hW : W ≠ ⊥) (hUW : U ≤ W) :
    weight L c U - weightSlope L c (nextSubspace L c W) W * finrank K U ≤
      weight L c W - weightSlope L c (nextSubspace L c W) W * finrank K W := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  have hbound := (forall_weightRatio_le_iff.mp
    (exceptionalSubspace_spec (forall_span_range_comp_subtype_eq_top hL W) hc).2.1)
    (U.comap W.subtype)
  have htop : weight (fun v i ↦ (L v i).comp W.subtype) c ⊤ = weight L c W := by
    rw [weight_comp_subtype, Submodule.map_subtype_top]
  rw [weight_comap_subtype L c hUW, htop,
    (Submodule.comapSubtypeEquivOfLe hUW).finrank_eq, weightRatio_comp_subtype] at hbound
  dsimp only [nextSubspace]
  linarith

private theorem nextSubspace_le_of_weight_sub_weightSlope_ge
    {L : Ω → ι → Module.Dual K V} (hL : ∀ v, span K (range (L v)) = ⊤)
    {c : Ω → ι → ℝ} (hc : HasFiniteSupport c)
    {U W : Submodule K V} (hW : W ≠ ⊥) (hUW : U ≤ W)
    (hge : weight L c W - weightSlope L c (nextSubspace L c W) W * finrank K W ≤
      weight L c U - weightSlope L c (nextSubspace L c W) W * finrank K U) :
    nextSubspace L c W ≤ U := by
  by_cases hne : U = W
  · subst hne; exact nextSubspace_le L c U
  · have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
    have hmap : (U.comap W.subtype).map W.subtype = U := by
      rw [Submodule.map_comap_subtype, inf_of_le_right hUW]
    have hU' : U.comap W.subtype ≠ ⊤ := fun h ↦
      hne (by rw [← hmap, h, Submodule.map_subtype_top])
    have hratio : weightRatio (fun v i ↦ (L v i).comp W.subtype) c
        (exceptionalSubspace (fun v i ↦ (L v i).comp W.subtype) c) ≤
        weightRatio (fun v i ↦ (L v i).comp W.subtype) c (U.comap W.subtype) := by
      rw [le_weightRatio_iff hU', weight_comap_subtype L c hUW, weight_comp_subtype,
        Submodule.map_subtype_top, (Submodule.comapSubtypeEquivOfLe hUW).finrank_eq,
        weightRatio_comp_subtype]
      dsimp only [nextSubspace] at hge
      linarith
    exact (Submodule.map_mono
      (exceptionalSubspace_le (forall_span_range_comp_subtype_eq_top hL W) hc hratio)).trans_eq hmap

private theorem weightSlope_lt_weightSlope_nextSubspace
    {L : Ω → ι → Module.Dual K V} (hL : ∀ v, span K (range (L v)) = ⊤)
    {c : Ω → ι → ℝ} (hc : HasFiniteSupport c)
    {W : Submodule K V} (hT : nextSubspace L c W ≠ ⊥) :
    weightSlope L c (nextSubspace L c W) W <
      weightSlope L c (nextSubspace L c (nextSubspace L c W)) (nextSubspace L c W) := by
  set T := nextSubspace L c W
  set S := nextSubspace L c T
  have hW : W ≠ ⊥ := fun h ↦ hT (h ▸ nextSubspace_bot L c)
  have hST : S < T := nextSubspace_lt L c hT
  have hTW : T < W := nextSubspace_lt L c hW
  have hSW : S ≤ W := hST.le.trans hTW.le
  have hle := weight_sub_weightSlope_nextSubspace_le hL hc hW hSW
  have hEq := weight_sub_weightSlope_mul_finrank_eq L c hTW.le
  have hlt : weight L c S - weightSlope L c T W * finrank K S <
      weight L c T - weightSlope L c T W * finrank K T := by
    refine lt_of_le_of_ne (hle.trans_eq hEq.symm) fun heq ↦ not_le_of_gt hST ?_
    exact nextSubspace_le_of_weight_sub_weightSlope_ge hL hc hW hSW (by linarith)
  rw [lt_weightSlope_iff hST]
  linarith

private theorem weightSlope_succ_lt_twistedFiltrationAux
    {L : Ω → ι → Module.Dual K V} (hL : ∀ v, span K (range (L v)) = ⊤)
    {c : Ω → ι → ℝ} (hc : HasFiniteSupport c) (W : Submodule K V) (k : ℕ)
    (hk : k + 2 < (twistedFiltrationAux L c W).length) :
    let l := twistedFiltrationAux L c W
    weightSlope L c (l[k + 1]'(by dsimp [l]; omega)) (l[k + 2]'hk) <
      weightSlope L c (l[k]'(by dsimp [l]; omega)) (l[k + 1]'(by dsimp [l]; omega)) := by
  dsimp only
  by_cases hW : W = ⊥
  · subst W; simp [twistedFiltrationAux_bot] at hk
  · let T := nextSubspace L c W
    let l := twistedFiltrationAux L c T
    have hdecomp : twistedFiltrationAux L c W = l ++ [W] :=
      twistedFiltrationAux_of_ne_bot L c hW
    have hlen : (twistedFiltrationAux L c W).length = l.length + 1 := by
      rw [hdecomp, List.length_append, List.length_singleton]
    by_cases hlast : k + 2 < l.length
    · have h0 : (twistedFiltrationAux L c W)[k]'(by omega) = l[k]'(by omega) := by
        simp only [hdecomp]; exact List.getElem_append_left (by omega)
      have h1 : (twistedFiltrationAux L c W)[k + 1]'(by omega) = l[k + 1]'(by omega) := by
        simp only [hdecomp]; exact List.getElem_append_left (by omega)
      have h2 : (twistedFiltrationAux L c W)[k + 2]'hk = l[k + 2]'hlast := by
        simp only [hdecomp]; exact List.getElem_append_left hlast
      simpa only [h0, h1, h2] using weightSlope_succ_lt_twistedFiltrationAux hL hc T k hlast
    · have hk_eq : k + 2 = l.length := by omega
      have hT : T ≠ ⊥ := fun h ↦ by simp [l, h, twistedFiltrationAux_bot] at hk_eq
      let l' := twistedFiltrationAux L c (nextSubspace L c T)
      have hdecompT : l = l' ++ [T] := twistedFiltrationAux_of_ne_bot L c hT
      have hlen' : l.length = l'.length + 1 := by
        rw [hdecompT, List.length_append, List.length_singleton]
      have hk0 : (twistedFiltrationAux L c W)[k]'(by omega) = nextSubspace L c T := by
        simp only [hdecomp]; rw [List.getElem_append_left (by omega)]
        simp only [hdecompT]; rw [List.getElem_append_left (by omega)]
        have hkeq : k = l'.length - 1 := by omega
        simpa only [hkeq] using getElem_length_sub_one_twistedFiltrationAux L c _
      have hk1 : (twistedFiltrationAux L c W)[k + 1]'(by omega) = T := by
        have hk1eq : k + 1 = l'.length := by omega
        simp [hdecomp, hdecompT, hk1eq]
      have hk2 : (twistedFiltrationAux L c W)[k + 2]'hk = W := by
        simp [hdecomp, hk_eq]
      rw [hk0, hk1, hk2]
      exact weightSlope_lt_weightSlope_nextSubspace hL hc hT
termination_by finrank K W
decreasing_by exact finrank_nextSubspace_lt L c hW

private theorem strictAnti_weightSlope_twistedFiltrationAux
    {L : Ω → ι → Module.Dual K V} (hL : ∀ v, span K (range (L v)) = ⊤)
    {c : Ω → ι → ℝ} (hc : HasFiniteSupport c) (W : Submodule K V) :
    StrictAnti fun i : Fin ((twistedFiltrationAux L c W).length - 1) ↦
      weightSlope L c
        ((twistedFiltrationAux L c W)[i.val]'(by omega))
        ((twistedFiltrationAux L c W)[i.val + 1]'(by omega)) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ (hab : a < b)
  induction b, hab using Nat.le_induction with
  | base => exact weightSlope_succ_lt_twistedFiltrationAux hL hc W a (by omega)
  | succ k _ ih =>
    exact (weightSlope_succ_lt_twistedFiltrationAux hL hc W k (by omega)).trans
      (ih (Nat.lt_of_succ_lt hb))

/-- Consecutive segment slopes of `twistedFiltration L c` strictly decrease.
This holds unconditionally: for invalid data the filtration has at most one segment. -/
theorem strictAnti_weightSlope_twistedFiltration
    (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) :
    StrictAnti fun i : Fin ((twistedFiltration L c).length - 1) ↦
      weightSlope L c
        ((twistedFiltration L c)[i.val]'(by omega))
        ((twistedFiltration L c)[i.val + 1]'(by omega)) := by
  by_cases h : (∀ v, span K (range (L v)) = ⊤) ∧ HasFiniteSupport c
  · exact strictAnti_weightSlope_twistedFiltrationAux h.1 h.2 ⊤
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ (hij : i < j)
    cases subsingleton_or_nontrivial V
    · simp [twistedFiltration_of_subsingleton] at hi
    · rcases not_and_or.mp h with hL | hc
      · simp [twistedFiltration_of_not_forall_span_eq_top hL] at hi hj; omega
      · simp [twistedFiltration_of_not_hasFiniteSupport hc] at hi hj; omega

private theorem supporting_line_step_of_lt_slope
    {L : Ω → ι → Module.Dual K V} (hL : ∀ v, span K (range (L v)) = ⊤)
    {c : Ω → ι → ℝ} (hc : HasFiniteSupport c)
    {U T : Submodule K V} {μ_TW μ B : ℝ} (hμ : μ_TW < μ)
    (hinf : weight L c (U ⊓ T) - μ * finrank K ↥(U ⊓ T) ≤ B)
    (hsup : weight L c (U ⊔ T) - μ_TW * finrank K ↥(U ⊔ T) ≤
      weight L c T - μ_TW * finrank K T) :
    weight L c U - μ * finrank K U ≤ B ∧
      (B ≤ weight L c U - μ * finrank K U → U ≤ T) := by
  have hsuper := weight_inf_add_weight_sup hL hc U T
  have hdim : (finrank K ↥(U ⊔ T) : ℝ) + finrank K ↥(U ⊓ T) =
      finrank K U + finrank K T := by exact_mod_cast finrank_sup_add_finrank_inf_eq U T
  have hdim_le : (finrank K T : ℝ) ≤ finrank K ↥(U ⊔ T) := by
    exact_mod_cast Submodule.finrank_mono (le_sup_right : T ≤ U ⊔ T)
  have hident : μ * (finrank K ↥(U ⊓ T) : ℝ) +
      (μ - μ_TW) * ((finrank K ↥(U ⊔ T) : ℝ) - finrank K T) =
      μ * finrank K U - μ_TW * finrank K ↥(U ⊔ T) + μ_TW * finrank K T := by
    rw [eq_sub_iff_add_eq'.mpr hdim]; ring
  have hkey : (weight L c U - μ * finrank K U) +
      (μ - μ_TW) * ((finrank K ↥(U ⊔ T) : ℝ) - finrank K T) ≤ B := by
    linarith [hsuper, hinf, hsup, hident]
  have hnonneg : 0 ≤ (μ - μ_TW) * ((finrank K ↥(U ⊔ T) : ℝ) - finrank K T) :=
    mul_nonneg (sub_nonneg.mpr hμ.le) (sub_nonneg.mpr hdim_le)
  refine ⟨by linarith [hkey, hnonneg], fun hge ↦ ?_⟩
  have hzero : (μ - μ_TW) * ((finrank K ↥(U ⊔ T) : ℝ) - finrank K T) = 0 :=
    le_antisymm (by linarith [hkey, hge]) hnonneg
  have hsub_zero := (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hμ.ne')
  have hdim_eq : finrank K ↥(U ⊔ T) = finrank K T := by
    exact_mod_cast sub_eq_zero.mp hsub_zero
  exact le_sup_left.trans (Submodule.eq_of_le_of_finrank_eq le_sup_right hdim_eq.symm).ge

private theorem supporting_line_twistedFiltrationAux
    {L : Ω → ι → Module.Dual K V} (hL : ∀ v, span K (range (L v)) = ⊤)
    {c : Ω → ι → ℝ} (hc : HasFiniteSupport c)
    (W : Submodule K V) (i : Fin ((twistedFiltrationAux L c W).length - 1))
    {U : Submodule K V} (hUW : U ≤ W) :
    let l := twistedFiltrationAux L c W
    let u := l[i.val]'(by dsimp [l]; omega)
    let v := l[i.val + 1]'(by dsimp [l]; omega)
    let μ := weightSlope L c u v
    weight L c U - μ * finrank K U ≤ weight L c v - μ * finrank K v ∧
      (weight L c v - μ * finrank K v ≤ weight L c U - μ * finrank K U → u ≤ U ∧ U ≤ v) := by
  dsimp only
  by_cases hW : W = ⊥
  · subst W; have hi := i.isLt; simp [twistedFiltrationAux_bot] at hi
  · let T := nextSubspace L c W
    let lT := twistedFiltrationAux L c T
    have hTW : T < W := nextSubspace_lt L c hW
    have hdecomp : twistedFiltrationAux L c W = lT ++ [W] :=
      twistedFiltrationAux_of_ne_bot L c hW
    have hlT_pos : 0 < lT.length :=
      List.length_pos_iff_ne_nil.mpr (twistedFiltrationAux_ne_nil L c T)
    have hlen : (twistedFiltrationAux L c W).length = lT.length + 1 := by
      rw [hdecomp, List.length_append, List.length_singleton]
    have hi_le : i.val ≤ lT.length - 1 := by have := i.isLt; omega
    rcases lt_or_eq_of_le hi_le with hilt | hieq
    · have h0 : (twistedFiltrationAux L c W)[i.val]'(by omega) = lT[i.val]'(by omega) := by
        simp only [hdecomp]; exact List.getElem_append_left (by omega)
      have h1 : (twistedFiltrationAux L c W)[i.val + 1]'(by omega) = lT[i.val + 1]'(by omega) := by
        simp only [hdecomp]; exact List.getElem_append_left (by omega)
      have hlast0 : (twistedFiltrationAux L c W)[lT.length - 1]'(by omega) = T := by
        simp only [hdecomp]; rw [List.getElem_append_left (by omega)]
        exact getElem_length_sub_one_twistedFiltrationAux L c T
      have hlast1 : (twistedFiltrationAux L c W)[lT.length]'(by omega) = W := by simp [hdecomp]
      have hslope_lt : weightSlope L c T W <
          weightSlope L c (lT[i.val]'(by omega)) (lT[i.val + 1]'(by omega)) := by
        have hanti := strictAnti_weightSlope_twistedFiltrationAux hL hc W
          (a := ⟨i.val, i.isLt⟩) (b := ⟨lT.length - 1, by omega⟩) hilt
        have heq_idx : lT.length - 1 + 1 = lT.length := by omega
        simpa only [h0, h1, hlast0, heq_idx, hlast1] using hanti
      have hIH_inf := (supporting_line_twistedFiltrationAux hL hc T ⟨i.val, hilt⟩
        (inf_le_right : U ⊓ T ≤ T)).1
      have hsup_T : weight L c (U ⊔ T) - weightSlope L c T W * finrank K ↥(U ⊔ T) ≤
          weight L c T - weightSlope L c T W * finrank K T :=
        (weight_sub_weightSlope_nextSubspace_le hL hc hW (sup_le hUW hTW.le)).trans_eq
          (weight_sub_weightSlope_mul_finrank_eq L c hTW.le).symm
      obtain ⟨hub, heqT⟩ := supporting_line_step_of_lt_slope hL hc hslope_lt hIH_inf hsup_T
      rw [h0, h1]
      exact ⟨hub, fun hge ↦ (supporting_line_twistedFiltrationAux hL hc T ⟨i.val, hilt⟩
        (heqT hge)).2 hge⟩
    · have h0 : (twistedFiltrationAux L c W)[i.val]'(by omega) = T := by
        simp only [hdecomp, hieq]; rw [List.getElem_append_left (by omega)]
        exact getElem_length_sub_one_twistedFiltrationAux L c T
      have h1 : (twistedFiltrationAux L c W)[i.val + 1]'(by omega) = W := by
        have heq_idx : i.val + 1 = lT.length := by omega
        simp [hdecomp, heq_idx]
      rw [h0, h1]
      exact ⟨weight_sub_weightSlope_nextSubspace_le hL hc hW hUW,
        fun hge ↦ ⟨nextSubspace_le_of_weight_sub_weightSlope_ge hL hc hW hUW hge, hUW⟩⟩
termination_by finrank K W
decreasing_by all_goals exact finrank_nextSubspace_lt L c hW

/-- Every segment of `twistedFiltration L c` defines a supporting line lying at or above
`(finrank K U, weight L c U)` for every subspace `U` of `V` (Evertse--Ferretti, Lemma 15.4). -/
theorem weight_sub_weightSlope_mul_finrank_le
    {L : Ω → ι → Module.Dual K V} (hL : ∀ v, span K (range (L v)) = ⊤)
    {c : Ω → ι → ℝ} (hc : HasFiniteSupport c)
    (i : Fin ((twistedFiltration L c).length - 1)) (U : Submodule K V) :
    weight L c U -
        weightSlope L c
          ((twistedFiltration L c)[i.val]'(by omega))
          ((twistedFiltration L c)[i.val + 1]'(by omega)) * finrank K U ≤
      weight L c ((twistedFiltration L c)[i.val + 1]'(by omega)) -
        weightSlope L c
          ((twistedFiltration L c)[i.val]'(by omega))
          ((twistedFiltration L c)[i.val + 1]'(by omega)) *
          finrank K ((twistedFiltration L c)[i.val + 1]'(by omega)) :=
  (supporting_line_twistedFiltrationAux hL hc ⊤ i le_top).1

/-- Supporting-line upper bound for the `i`-th segment of `twistedFiltration L c`, expressed
relative to the left endpoint `(twistedFiltration L c)[i]`. -/
theorem weight_sub_weightSlope_mul_finrank_le_left
    {L : Ω → ι → Module.Dual K V} (hL : ∀ v, span K (range (L v)) = ⊤)
    {c : Ω → ι → ℝ} (hc : HasFiniteSupport c)
    (i : Fin ((twistedFiltration L c).length - 1)) (U : Submodule K V) :
    weight L c U -
        weightSlope L c
          ((twistedFiltration L c)[i.val]'(by omega))
          ((twistedFiltration L c)[i.val + 1]'(by omega)) * finrank K U ≤
      weight L c ((twistedFiltration L c)[i.val]'(by omega)) -
        weightSlope L c
          ((twistedFiltration L c)[i.val]'(by omega))
          ((twistedFiltration L c)[i.val + 1]'(by omega)) *
          finrank K ((twistedFiltration L c)[i.val]'(by omega)) :=
  (weight_sub_weightSlope_mul_finrank_le hL hc i U).trans_eq
    (weight_sub_weightSlope_mul_finrank_eq L c
      (getElem_lt_getElem_succ_twistedFiltration L c i).le).symm

/-- Any subspace `U` attaining the `i`-th supporting-line bound of `twistedFiltration L c` is
sandwiched between the `i`-th and `(i + 1)`-st filtration subspaces. -/
theorem le_and_le_of_weight_sub_weightSlope_mul_finrank_eq
    {L : Ω → ι → Module.Dual K V} (hL : ∀ v, span K (range (L v)) = ⊤)
    {c : Ω → ι → ℝ} (hc : HasFiniteSupport c)
    (i : Fin ((twistedFiltration L c).length - 1)) {U : Submodule K V}
    (heq : weight L c U -
        weightSlope L c
          ((twistedFiltration L c)[i.val]'(by omega))
          ((twistedFiltration L c)[i.val + 1]'(by omega)) * finrank K U =
      weight L c ((twistedFiltration L c)[i.val + 1]'(by omega)) -
        weightSlope L c
          ((twistedFiltration L c)[i.val]'(by omega))
          ((twistedFiltration L c)[i.val + 1]'(by omega)) *
          finrank K ((twistedFiltration L c)[i.val + 1]'(by omega))) :
    ((twistedFiltration L c)[i.val]'(by omega)) ≤ U ∧
      U ≤ ((twistedFiltration L c)[i.val + 1]'(by omega)) :=
  (supporting_line_twistedFiltrationAux hL hc ⊤ i le_top).2 heq.ge

/-- Every subspace `T` in `twistedFiltration L c` is the unique subspace of dimension
`finrank K T` having weight at least `weight L c T`. -/
theorem eq_of_mem_twistedFiltration_of_finrank_eq_of_le_weight
    {L : Ω → ι → Module.Dual K V} (hL : ∀ v, span K (range (L v)) = ⊤)
    {c : Ω → ι → ℝ} (hc : HasFiniteSupport c)
    {T U : Submodule K V} (hT : T ∈ twistedFiltration L c)
    (hdim : finrank K U = finrank K T) (hw : weight L c T ≤ weight L c U) :
    U = T := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hT
  by_cases hk0 : k = 0
  · subst hk0
    rw [getElem_zero_twistedFiltration, finrank_bot] at hdim
    exact (Submodule.finrank_eq_zero.mp hdim).trans (getElem_zero_twistedFiltration L c).symm
  · let i : Fin ((twistedFiltration L c).length - 1) := ⟨k - 1, by omega⟩
    have hTk : (twistedFiltration L c)[i.val + 1]'(by dsimp [i]; omega) =
        (twistedFiltration L c)[k]'hk := by congr 1; dsimp [i]; omega
    have hle := weight_sub_weightSlope_mul_finrank_le hL hc i U
    have hUT := (le_and_le_of_weight_sub_weightSlope_mul_finrank_eq hL hc i
      (le_antisymm hle (by rw [hTk, hdim]; linarith))).2
    rw [hTk] at hUT
    exact Submodule.eq_of_le_of_finrank_eq hUT hdim

/-- Every subspace `T` in `twistedFiltration L c` maximizes `weight L c` among all subspaces of
its dimension. -/
theorem weight_le_of_mem_twistedFiltration_of_finrank_eq
    {L : Ω → ι → Module.Dual K V} (hL : ∀ v, span K (range (L v)) = ⊤)
    {c : Ω → ι → ℝ} (hc : HasFiniteSupport c)
    {T U : Submodule K V} (hT : T ∈ twistedFiltration L c)
    (hdim : finrank K U = finrank K T) :
    weight L c U ≤ weight L c T := by
  by_contra! hgt
  exact (eq_of_mem_twistedFiltration_of_finrank_eq_of_le_weight hL hc hT hdim hgt.le ▸ hgt).false

/-! ### Exact upper convex hull characterization -/

omit [FiniteDimensional K V] in
private theorem weight_sub_mul_finrank_lt_of_finrank_lt
    {L : Ω → ι → Module.Dual K V} {c : Ω → ι → ℝ} {U T : Submodule K V}
    {μ μL : ℝ} (hμ : μ < μL) (hd : finrank K U < finrank K T)
    (hle : weight L c U - μL * finrank K U ≤ weight L c T - μL * finrank K T) :
    weight L c U - μ * finrank K U < weight L c T - μ * finrank K T := by
  nlinarith [(Nat.cast_lt (α := ℝ)).mpr hd]

omit [FiniteDimensional K V] in
private theorem weight_sub_mul_finrank_lt_of_lt_finrank
    {L : Ω → ι → Module.Dual K V} {c : Ω → ι → ℝ} {U T : Submodule K V}
    {μR μ : ℝ} (hμ : μR < μ) (hd : finrank K T < finrank K U)
    (hle : weight L c U - μR * finrank K U ≤ weight L c T - μR * finrank K T) :
    weight L c U - μ * finrank K U < weight L c T - μ * finrank K T := by
  nlinarith [(Nat.cast_lt (α := ℝ)).mpr hd]

private theorem exists_strict_supporting_slope_of_interior
    {L : Ω → ι → Module.Dual K V} (hL : ∀ v, span K (range (L v)) = ⊤)
    {c : Ω → ι → ℝ} (hc : HasFiniteSupport c)
    (k : Fin (twistedFiltration L c).length) (hk0 : k.val ≠ 0)
    (hk_lt : k.val < (twistedFiltration L c).length - 1) :
    ∃ μ : ℝ, ∀ U : Submodule K V,
      finrank K U ≠ finrank K (twistedFiltration L c)[k.val] →
        weight L c U - μ * finrank K U <
          weight L c (twistedFiltration L c)[k.val] -
            μ * finrank K (twistedFiltration L c)[k.val] := by
  let iL : Fin ((twistedFiltration L c).length - 1) := ⟨k.val - 1, by omega⟩
  let iR : Fin ((twistedFiltration L c).length - 1) := ⟨k.val, hk_lt⟩
  set μL := weightSlope L c ((twistedFiltration L c)[iL.val]'(by omega))
    ((twistedFiltration L c)[iL.val + 1]'(by omega)) with hμL
  set μR := weightSlope L c ((twistedFiltration L c)[iR.val]'(by omega))
    ((twistedFiltration L c)[iR.val + 1]'(by omega))
  have hμ : μR < μL := strictAnti_weightSlope_twistedFiltration L c
    (a := iL) (b := iR) (Fin.mk_lt_mk.mpr (by omega))
  refine ⟨(μL + μR) / 2, fun U hne ↦ ?_⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hTk : (twistedFiltration L c)[k.val] =
        (twistedFiltration L c)[iL.val + 1]'(by omega) := by congr 1; dsimp [iL]; omega
    have hle := weight_sub_weightSlope_mul_finrank_le hL hc iL U
    rw [← hμL, ← hTk] at hle
    exact weight_sub_mul_finrank_lt_of_finrank_lt (μL := μL) (by linarith [hμ]) hlt hle
  · exact weight_sub_mul_finrank_lt_of_lt_finrank (μR := μR) (by linarith [hμ]) hgt
      (weight_sub_weightSlope_mul_finrank_le_left hL hc iR U)

private theorem exists_strict_supporting_slope_of_mem_twistedFiltration
    {L : Ω → ι → Module.Dual K V} (hL : ∀ v, span K (range (L v)) = ⊤)
    {c : Ω → ι → ℝ} (hc : HasFiniteSupport c)
    (k : Fin (twistedFiltration L c).length) :
    ∃ μ : ℝ, ∀ U : Submodule K V,
      finrank K U ≠ finrank K (twistedFiltration L c)[k.val] →
        weight L c U - μ * finrank K U <
          weight L c (twistedFiltration L c)[k.val] -
            μ * finrank K (twistedFiltration L c)[k.val] := by
  cases subsingleton_or_nontrivial V
  · exact ⟨0, fun U hne ↦
      (hne (congrArg (fun W : Submodule K V ↦ finrank K W) (Subsingleton.elim U _))).elim⟩
  · have h2 := two_le_length_twistedFiltration L c
    by_cases hk0 : k.val = 0
    · let i0 : Fin ((twistedFiltration L c).length - 1) := ⟨0, by omega⟩
      set μ₀ := weightSlope L c ((twistedFiltration L c)[i0.val]'(by omega))
        ((twistedFiltration L c)[i0.val + 1]'(by omega)) with hμ₀
      refine ⟨μ₀ + 1, fun U hne ↦ ?_⟩
      have hTk : (twistedFiltration L c)[k.val] =
          (twistedFiltration L c)[i0.val]'(by omega) := by simp only [hk0]; rfl
      have h0 : (twistedFiltration L c)[k.val] = ⊥ := by
        simpa only [hk0] using getElem_zero_twistedFiltration L c
      have hd : finrank K (twistedFiltration L c)[k.val] < finrank K U := by
        rw [h0, finrank_bot] at hne ⊢; exact Nat.pos_of_ne_zero hne
      have hle := weight_sub_weightSlope_mul_finrank_le_left hL hc i0 U
      rw [← hμ₀, ← hTk] at hle
      exact weight_sub_mul_finrank_lt_of_lt_finrank (μR := μ₀) (by linarith) hd hle
    · by_cases hklast : k.val = (twistedFiltration L c).length - 1
      · let ir : Fin ((twistedFiltration L c).length - 1) :=
          ⟨(twistedFiltration L c).length - 2, by omega⟩
        set μᵣ := weightSlope L c ((twistedFiltration L c)[ir.val]'(by omega))
          ((twistedFiltration L c)[ir.val + 1]'(by omega)) with hμᵣ
        refine ⟨μᵣ - 1, fun U hne ↦ ?_⟩
        have hTk : (twistedFiltration L c)[k.val] =
            (twistedFiltration L c)[ir.val + 1]'(by omega) := by congr 1; dsimp [ir]; omega
        have hTr : (twistedFiltration L c)[k.val] = ⊤ := by
          simpa only [hklast] using getElem_length_sub_one_twistedFiltration L c
        have hd : finrank K U < finrank K (twistedFiltration L c)[k.val] :=
          lt_of_le_of_ne (by rw [hTr, finrank_top]; exact Submodule.finrank_le U) hne
        have hle := weight_sub_weightSlope_mul_finrank_le hL hc ir U
        rw [← hμᵣ, ← hTk] at hle
        exact weight_sub_mul_finrank_lt_of_finrank_lt (μL := μᵣ) (by linarith) hd hle
      · exact exists_strict_supporting_slope_of_interior hL hc k hk0 (by have := k.isLt; omega)

private theorem not_mem_extremePoints_of_finrank_strict_between
    {L : Ω → ι → Module.Dual K V} (hL : ∀ v, span K (range (L v)) = ⊤)
    {c : Ω → ι → ℝ} (hc : HasFiniteSupport c)
    (i : Fin ((twistedFiltration L c).length - 1)) {U : Submodule K V}
    (hlo : finrank K ((twistedFiltration L c)[i.val]'(by omega)) < finrank K U)
    (hhi : finrank K U < finrank K ((twistedFiltration L c)[i.val + 1]'(by omega)))
    {y : ℝ} (hy : y ≤ weight L c U) :
    ((finrank K U : ℝ), y) ∉
      (convexHull ℝ {p : ℝ × ℝ | ∃ W : Submodule K V,
        p.1 = finrank K W ∧ p.2 ≤ weight L c W}).extremePoints ℝ := by
  let A := {p : ℝ × ℝ | ∃ W : Submodule K V, p.1 = finrank K W ∧ p.2 ≤ weight L c W}
  let T₀ := (twistedFiltration L c)[i.val]'(by omega)
  let T₁ := (twistedFiltration L c)[i.val + 1]'(by omega)
  let d₀ : ℝ := (finrank K T₀ : ℝ)
  let d₁ : ℝ := (finrank K T₁ : ℝ)
  let d : ℝ := (finrank K U : ℝ)
  have hd₀ : d₀ < d := Nat.cast_lt.mpr hlo
  have hd₁ : d < d₁ := Nat.cast_lt.mpr hhi
  let μ := weightSlope L c T₀ T₁
  have hT₀₁ : T₀ ≤ T₁ := (getElem_lt_getElem_succ_twistedFiltration L c i).le
  have hline : weight L c U ≤ weight L c T₀ + μ * (d - d₀) := by
    have hle := weight_sub_weightSlope_mul_finrank_le_left hL hc i U
    dsimp only [T₀, T₁, μ, d, d₀] at hle ⊢
    linarith [hle]
  let δ := weight L c T₀ + μ * (d - d₀) - y
  have hδ : 0 ≤ δ := by dsimp only [δ]; linarith [hy, hline]
  have hw₁ : weight L c T₁ = weight L c T₀ + μ * (d₁ - d₀) := by
    have hmul := weightSlope_mul_finrank_sub_finrank L c hT₀₁
    dsimp only [T₀, T₁, μ, d₀, d₁] at hmul ⊢
    linarith [hmul]
  let q₀ : ℝ × ℝ := (d₀, weight L c T₀ - δ)
  let q₁ : ℝ × ℝ := (d₁, weight L c T₁ - δ)
  have hq₀ : q₀ ∈ convexHull ℝ A := subset_convexHull ℝ A ⟨T₀, rfl, by dsimp [q₀]; linarith [hδ]⟩
  have hq₁ : q₁ ∈ convexHull ℝ A := subset_convexHull ℝ A ⟨T₁, rfl, by dsimp [q₁]; linarith [hδ]⟩
  let t : ℝ := (d - d₀) / (d₁ - d₀)
  have ht0 : 0 < t := div_pos (sub_pos.mpr hd₀) (sub_pos.mpr (hd₀.trans hd₁))
  have ht1 : 0 < 1 - t := by
    rw [sub_pos, div_lt_one (sub_pos.mpr (hd₀.trans hd₁))]; linarith [hd₁]
  have hseg : (d, y) ∈ openSegment ℝ q₀ q₁ := by
    refine ⟨1 - t, t, ht1, ht0, by ring, Prod.ext ?_ ?_⟩
    · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, q₀, q₁, t]
      field_simp [ne_of_gt (sub_pos.mpr (hd₀.trans hd₁))]; ring
    · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, q₀, q₁, t, hw₁, δ]
      field_simp [ne_of_gt (sub_pos.mpr (hd₀.trans hd₁))]; ring
  intro hextr
  have heq := (mem_extremePoints.mp hextr).2 q₀ hq₀ q₁ hq₁ hseg
  exact hd₀.ne (congrArg Prod.fst heq.1)

private theorem exists_finrank_eq_or_strict_between_twistedFiltration
    (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ) (U : Submodule K V) :
    (∃ k : Fin (twistedFiltration L c).length,
        finrank K U = finrank K (twistedFiltration L c)[k.val]) ∨
      ∃ i : Fin ((twistedFiltration L c).length - 1),
        finrank K ((twistedFiltration L c)[i.val]'(by omega)) < finrank K U ∧
          finrank K U < finrank K ((twistedFiltration L c)[i.val + 1]'(by omega)) := by
  classical
  by_cases hex : ∃ k : Fin (twistedFiltration L c).length,
      finrank K U = finrank K (twistedFiltration L c)[k.val]
  · exact Or.inl hex
  · right
    push Not at hex
    have hpos_len : 0 < (twistedFiltration L c).length := length_twistedFiltration_pos L c
    have h0 : finrank K ((twistedFiltration L c)[0]'hpos_len) < finrank K U := by
      have hne := hex ⟨0, hpos_len⟩
      rw [getElem_zero_twistedFiltration, finrank_bot] at hne ⊢
      exact Nat.pos_of_ne_zero hne
    have hlast : finrank K U <
        finrank K ((twistedFiltration L c)[(twistedFiltration L c).length - 1]'(by omega)) :=
      lt_of_le_of_ne (by rw [getElem_length_sub_one_twistedFiltration, finrank_top]; exact
        Submodule.finrank_le U) (hex ⟨(twistedFiltration L c).length - 1, by omega⟩)
    let s : Finset (Fin (twistedFiltration L c).length) :=
      Finset.univ.filter fun j ↦ finrank K (twistedFiltration L c)[j.val] < finrank K U
    have hs : s.Nonempty := ⟨⟨0, hpos_len⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩⟩
    let j := s.max' hs
    have hj_mem := Finset.mem_filter.mp (s.max'_mem hs)
    have hj_lt : j.val < (twistedFiltration L c).length - 1 := by
      refine lt_of_le_of_ne (Nat.le_sub_one_of_lt j.isLt) fun hEq ↦ ?_
      have hsub : (twistedFiltration L c)[j.val] =
          (twistedFiltration L c)[(twistedFiltration L c).length - 1]'(by omega) := by congr 1
      exact (lt_irrefl _) ((hsub ▸ hj_mem.2).trans hlast)
    refine ⟨⟨j.val, hj_lt⟩, hj_mem.2, lt_of_le_of_ne ?_ (hex ⟨j.val + 1, by omega⟩)⟩
    by_contra! hnext
    have hmem_next : (⟨j.val + 1, by omega⟩ : Fin (twistedFiltration L c).length) ∈ s :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnext⟩
    have hle_max : j.val + 1 ≤ j.val := s.le_max' ⟨j.val + 1, by omega⟩ hmem_next
    omega

omit [FiniteDimensional K V] in
private theorem not_mem_extremePoints_of_snd_lt
    (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    {U : Submodule K V} {y : ℝ} (hlt : y < weight L c U) :
    ((finrank K U : ℝ), y) ∉
      (convexHull ℝ {p : ℝ × ℝ | ∃ W : Submodule K V,
        p.1 = finrank K W ∧ p.2 ≤ weight L c W}).extremePoints ℝ := by
  let A := {p : ℝ × ℝ | ∃ W : Submodule K V, p.1 = finrank K W ∧ p.2 ≤ weight L c W}
  let q_hi : ℝ × ℝ := (finrank K U, weight L c U)
  let q_lo : ℝ × ℝ := (finrank K U, 2 * y - weight L c U)
  have hseg : ((finrank K U : ℝ), y) ∈ openSegment ℝ q_hi q_lo :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num,
      Prod.ext (by simp [q_hi, q_lo]; ring) (by simp [q_hi, q_lo]; ring)⟩
  intro hp
  have heq := (mem_extremePoints.mp hp).2
    q_hi (subset_convexHull ℝ A ⟨U, rfl, le_rfl⟩)
    q_lo (subset_convexHull ℝ A ⟨U, rfl, by dsimp [q_lo]; linarith⟩) hseg
  exact hlt.ne (congrArg Prod.snd heq.1).symm

/-- The vertices (extreme points) of the upper convex hull hypograph of
`{(finrank K U, weight L c U)}` are precisely the pairs `(finrank K T, weight L c T)` for
`T ∈ twistedFiltration L c` (Evertse--Ferretti, §15, Lemma 15.4). -/
theorem extremePoints_convexHull_finrank_le_weight
    {L : Ω → ι → Module.Dual K V} (hL : ∀ v, span K (range (L v)) = ⊤)
    {c : Ω → ι → ℝ} (hc : HasFiniteSupport c) :
    (convexHull ℝ {p : ℝ × ℝ | ∃ U : Submodule K V,
        p.1 = finrank K U ∧ p.2 ≤ weight L c U}).extremePoints ℝ =
      (fun T : Submodule K V ↦ ((finrank K T : ℝ), weight L c T)) ''
        {T | T ∈ twistedFiltration L c} := by
  apply Subset.antisymm
  · intro p hp
    obtain ⟨U, hp₁, hp₂⟩ := extremePoints_convexHull_subset hp
    have hp_eq : p = ((finrank K U : ℝ), p.2) := Prod.ext hp₁ rfl
    rw [hp_eq] at hp
    have hp₂_eq : p.2 = weight L c U :=
      le_antisymm hp₂ (le_of_not_gt fun hlt ↦ not_mem_extremePoints_of_snd_lt L c hlt hp)
    rcases exists_finrank_eq_or_strict_between_twistedFiltration L c U with
      ⟨k, hk⟩ | ⟨i, hlo, hhi⟩
    · have hle_wt : weight L c U ≤ weight L c (twistedFiltration L c)[k.val] :=
        weight_le_of_mem_twistedFiltration_of_finrank_eq hL hc (List.getElem_mem k.isLt) hk
      have hwt_eq : weight L c U = weight L c (twistedFiltration L c)[k.val] := by
        refine le_antisymm hle_wt (le_of_not_gt fun hlt ↦ ?_)
        have hp' := hp
        rw [hk, hp₂_eq] at hp'
        exact not_mem_extremePoints_of_snd_lt L c hlt hp'
      exact ⟨(twistedFiltration L c)[k.val], List.getElem_mem k.isLt,
        by rw [hp_eq, hp₂_eq, hk, hwt_eq]⟩
    · exact (not_mem_extremePoints_of_finrank_strict_between hL hc i hlo hhi hp₂ hp).elim
  · rintro _ ⟨T, hT, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hT
    obtain ⟨μ, hμ⟩ := exists_strict_supporting_slope_of_mem_twistedFiltration hL hc ⟨k, hk⟩
    let f : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.snd ℝ ℝ ℝ - μ • LinearMap.fst ℝ ℝ ℝ
    have hf_apply (x : ℝ × ℝ) : f x = x.2 - μ * x.1 := by simp [f]
    refine mem_extremePoints_convexHull_of_strict_max
      ⟨(twistedFiltration L c)[k], rfl, le_rfl⟩ f ?_
    rintro q ⟨U, hq₁, hq₂⟩ hne
    rw [hf_apply, hf_apply, hq₁]
    dsimp only
    by_cases hdim : finrank K U = finrank K (twistedFiltration L c)[k]
    · have hle_wt : weight L c U ≤ weight L c (twistedFiltration L c)[k] :=
        weight_le_of_mem_twistedFiltration_of_finrank_eq hL hc (List.getElem_mem hk) hdim
      have hlt_y : q.2 < weight L c (twistedFiltration L c)[k] :=
        lt_of_le_of_ne (hq₂.trans hle_wt) fun hy ↦ hne (Prod.ext (hq₁.trans (by simp [hdim])) hy)
      rw [hdim]; linarith
    · linarith [hμ U hdim]

end Filtration

section FinTwo

/-- For the two coordinate forms on `K²` with weights supported at a single place `v₀` satisfying
`c v₀ 0 < c v₀ 1`, the Harder--Narasimhan filtration is `[⊥, K ∙ e₂, ⊤]`. -/
theorem twistedFiltration_fin_two_proj_of_lt {K Ω : Type*} [Field K]
    {v₀ : Ω} {c : Ω → Fin 2 → ℝ} (hsupp : support c ⊆ {v₀}) (hc : c v₀ 0 < c v₀ 1) :
    twistedFiltration (fun (_ : Ω) (i : Fin 2) ↦
      (LinearMap.proj i : Module.Dual K (Fin 2 → K))) c =
      [⊥, K ∙ Pi.single (1 : Fin 2) (1 : K), ⊤] := by
  let L : Ω → Fin 2 → Module.Dual K (Fin 2 → K) := fun _ i ↦ LinearMap.proj i
  let E : Submodule K (Fin 2 → K) := K ∙ Pi.single 1 1
  have hE : exceptionalSubspace L c = E := exceptionalSubspace_fin_two_proj_of_lt hsupp hc
  have hdimE : finrank K E = 1 :=
    finrank_span_singleton (Pi.single_eq_zero_iff.not.mpr one_ne_zero)
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (hdimE.symm ▸ Nat.one_pos)
  have hEE : exceptionalSubspace (fun v i ↦ (L v i).comp E.subtype) c = ⊥ := by
    have hlt := Submodule.finrank_lt (exceptionalSubspace_ne_top
      (fun v i ↦ (L v i).comp E.subtype) c)
    exact Submodule.finrank_eq_zero.mp (by omega)
  have hsub : twistedFiltration (fun v i ↦ (L v i).comp E.subtype) c = [⊥, ⊤] :=
    (twistedFiltration_eq_pair_bot_top_iff _ c).mpr hEE
  rw [twistedFiltration_eq_append_top L c, hE, hsub]
  simp [E]

end FinTwo

end TauCeti
