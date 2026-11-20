/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Cube.Homotopy
public import TauCeti.KnotTheory.Khovanov.Homology
public import TauCeti.KnotTheory.Khovanov.Mark.Basic

/-!
# Sliding a mark across a crossing

Let `c` be a crossing of a link diagram and let `p` and `q` be the arc marks on opposite sides of a
local strand through `c`: for a slot `k : Fin 4`, `p` lies on `D.crossing c k` and `q` lies on
`D.crossing c (oppositeCrossingSlot k)`. Each local smoothing at `c` joins every slot to one of its
neighbours and never to its opposite slot, so in every smoothing state `s` the circles selected by
`p` and `q` are the two circles through slots `0` and `2` in some order. In particular,
`X_p + X_q = X_0 + X_2` on every state, and when only one circle of `s` meets `c` the marks `p` and
`q` select the same circle.

Reversing the saddle map along the edges in direction `c` gives a bidegree-`(-1, -2)` homotopy `H`
on the Khovanov complex (`TauCeti.OrientedPDCode.khovanovComplexMarkSlideHom`): on a state `S`
having the `B`-smoothing at `c` (`c ∈ S`), `H` applies the reverse saddle `S → S \ {c}` with the
cube Koszul sign `(-1) ^ #{b ∈ S \ {c} | b < c}`, and on a state with `c ∉ S` it vanishes.

All mixed squares formed by the reverse saddle at `c` and a forward saddle at another crossing
`a ≠ c` commute by `TauCeti.PDCode.resolutionEdgeMap_comp_resolutionEdgeMap_comm`, so their signed
contributions to `d ≫ H + H ≫ d` cancel by `CategoryTheory.Functor.cubeReverseEdgeHomotopyZero`.
What remains on each state is the round-trip saddle composite at `c` alone:

* when two circles of the state pass through `c`, the composite is `Δ ∘ m = X ⊗ 1 + 1 ⊗ X` on the
  two circles at `c` (`TauCeti.PDCode.resolutionSplitMap_comp_resolutionMergeMap`), which is
  `X_p + X_q`;
* when one circle of the state passes through `c`, the composite is `m ∘ Δ = 2 • X` on that circle
  (`TauCeti.PDCode.resolutionMergeMap_comp_resolutionSplitMap`), which again equals `X_p + X_q`
  because `p` and `q` lie on that same circle.

Hence `d ≫ H + H ≫ d = X_p + X_q`, so `X_p` is chain homotopic to `-X_q` and sliding a mark across
one crossing negates the induced `X` action on Khovanov cohomology
(`TauCeti.OrientedPDCode.homologyMap_khovanovComplexMarkX_oppositeCrossingSlot`). Moreover `H`
satisfies `H² = 0` (since its image is supported on `c ∉ S`) and intertwines the opposite-strand
actions via `X_p ≫ H = H ≫ X_q` (in operator notation, `H ∘ X_p = X_q ∘ H`): every edge in `H`
changes `c`, so one of its two endpoints has a single circle at `c` where `p` and `q` coincide,
whereas the differential `d` also contains edges at `a ≠ c` that need not identify `p` and `q`.

## Main definitions

* `TauCeti.PDCode.resolutionCubeReverseSaddle`: the reverse saddle along `c` from vertex
  `insert c S` in quantum degree `j` to vertex `S` in quantum degree `j - 2`.
* `TauCeti.OrientedPDCode.khovanovComplexMarkSlideHom`: the signed reverse-saddle homotopy
  components `H` of cochain degree `-1` and quantum degree `-2` on `khovanovComplex`.
* `TauCeti.OrientedPDCode.khovanovComplexMarkSlideHomotopyZero`,
  `TauCeti.OrientedPDCode.khovanovComplexMarkSlideHomotopyNeg`: the chain homotopies
  `X_p + X_q ≃ 0` and `X_p ≃ -X_q`.

## Main results

* `TauCeti.PDCode.resolutionSplitMap_comp_resolutionMergeMap`: `Δ ∘ m = X_0 + X_2`.
* `TauCeti.PDCode.resolutionMergeMap_comp_resolutionSplitMap`: `m ∘ Δ = 2 • X_0`.
* `TauCeti.PDCode.resolutionEdgeMap_circleX_oppositeCrossingSlot`: every saddle at `c` carries `X_p`
  to `X_q`.
* `OrientedPDCode.d_comp_khovanovComplexMarkSlideHom_add_khovanovComplexMarkSlideHom_comp_d`:
  `d ≫ H + H ≫ d = X_p + X_q`.
* `OrientedPDCode.khovanovComplexMarkSlideHom_comp_khovanovComplexMarkSlideHom`: `H² = 0`.
* `OrientedPDCode.khovanovComplexMarkX_f_comp_khovanovComplexMarkSlideHom_oppositeCrossingSlot`:
  `(X_p).f i ≫ H i l = H i l ≫ (X_q).f l` (`H ∘ X_p = X_q ∘ H`).
* `OrientedPDCode.homologyMap_khovanovComplexMarkX_oppositeCrossingSlot`: sliding a mark across one
  crossing negates the induced map on Khovanov homology.

## References

* M. Khovanov, *Patterns in knot cohomology I*, Experiment. Math. 12 (2003), §3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), §2.
-/

public section

noncomputable section

open CategoryTheory Limits Finset PiTensorProduct DualNumber

namespace TauCeti.PDCode

universe u

variable {n : ℕ}

/-! ### Opposite slots at a crossing and their resolved circles -/

private theorem slotSmoothing_oppositeCrossingSlot_cases (b : Bool) (k : Fin 4) :
    (k = 0 ∧ oppositeCrossingSlot k = 2) ∨
      (k = 2 ∧ oppositeCrossingSlot k = 0) ∨
      (slotSmoothing b k = 0 ∧ slotSmoothing b (oppositeCrossingSlot k) = 2) ∨
      (slotSmoothing b k = 2 ∧ slotSmoothing b (oppositeCrossingSlot k) = 0) := by
  rw [oppositeCrossingSlot_eq_swap_mul_swap]
  revert k
  cases b <;> simp only [slotSmoothing_false, slotSmoothing_true] <;> decide

/-- At any crossing `c` and slot `k`, the circles of `k` and its opposite slot
`oppositeCrossingSlot k` in a smoothed diagram are the circles of slots `0` and `2`, in one of the
two orders. -/
theorem CrossingCircle.mk_crossing_oppositeCrossingSlot_pair {D : PDCode n} {s : Fin n → Bool}
    (c : Fin n) (k : Fin 4) :
    ((⟦D.crossing c k⟧ : D.CrossingCircle s) = ⟦D.crossing c 0⟧ ∧
      (⟦D.crossing c (oppositeCrossingSlot k)⟧ : D.CrossingCircle s) = ⟦D.crossing c 2⟧) ∨
    ((⟦D.crossing c k⟧ : D.CrossingCircle s) = ⟦D.crossing c 2⟧ ∧
      (⟦D.crossing c (oppositeCrossingSlot k)⟧ : D.CrossingCircle s) = ⟦D.crossing c 0⟧) := by
  rcases slotSmoothing_oppositeCrossingSlot_cases (D.smoothingChoice s c) k with
    ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact .inl ⟨by rw [h₁], by rw [h₂]⟩
  · exact .inr ⟨by rw [h₁], by rw [h₂]⟩
  · refine .inl ⟨?_, ?_⟩
    · rw [← CrossingCircle.mk_crossing_slotSmoothing, h₁]
    · rw [← CrossingCircle.mk_crossing_slotSmoothing, h₂]
  · refine .inr ⟨?_, ?_⟩
    · rw [← CrossingCircle.mk_crossing_slotSmoothing, h₁]
    · rw [← CrossingCircle.mk_crossing_slotSmoothing, h₂]

/-- When only one circle of `s` passes through `c`, the arc marks at a slot `k` of `c` and at its
opposite slot select the same resolved circle. -/
theorem Mark.resolvedCircle_onArc_crossing_eq_oppositeCrossingSlot_of_card_circlesAt_eq_one
    (D : PDCode n) {s : Fin n → Bool} {c : Fin n} (hs : #(D.circlesAt s c) = 1) (k : Fin 4) :
    (Mark.onArc D (D.crossing c k)).resolvedCircle s =
      (Mark.onArc D (D.crossing c (oppositeCrossingSlot k))).resolvedCircle s := by
  have h02 : (⟦D.crossing c 0⟧ : D.CrossingCircle s) = ⟦D.crossing c 2⟧ :=
    (D.card_circlesAt_eq_one_iff s c).mp hs
  rw [Mark.resolvedCircle_onArc, Mark.resolvedCircle_onArc]
  rcases CrossingCircle.mk_crossing_oppositeCrossingSlot_pair (D := D) (s := s) c k with
    ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂, h02]
  · rw [h₁, h₂, h02]

/-- In any state `s`, the sum of the `X` actions at the two opposite slots `k` and
`oppositeCrossingSlot k` of `c` equals the sum of the `X` actions on the circles through slots `0`
and `2` of `c`. -/
theorem circleX_resolvedCircle_onArc_add_oppositeCrossingSlot (D : PDCode n)
    (R : Type u) [CommSemiring R] (s : Fin n → Bool) (c : Fin n) (k : Fin 4) :
    Khovanov.circleX R ((Mark.onArc D (D.crossing c k)).resolvedCircle s) +
      Khovanov.circleX R
        ((Mark.onArc D (D.crossing c (oppositeCrossingSlot k))).resolvedCircle s) =
    Khovanov.circleX R (.inl ⟦D.crossing c 0⟧) +
      Khovanov.circleX R (.inl ⟦D.crossing c 2⟧) := by
  rw [Mark.resolvedCircle_onArc, Mark.resolvedCircle_onArc]
  rcases CrossingCircle.mk_crossing_oppositeCrossingSlot_pair (D := D) (s := s) c k with
    ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂]
  · rw [h₁, h₂, add_comm]

/-! ### Local Frobenius round-trip and intertwining identities at a saddle -/

section Saddle

variable (D : PDCode n) {s t : Fin n → Bool} {c : Fin n}
  (hst : ∀ j, j ≠ c → s j = t j) (hc : s c ≠ t c) (R : Type u) [CommSemiring R]

/-- **Merging two circles at `c` and splitting the result back (`Δ ∘ m = X ⊗ 1 + 1 ⊗ X`).** On a
state `s` with two circles through `c`, merging along `s → t` and splitting back along `t → s` acts
as the sum of the `X` actions on the two circles of `s` through slots `0` and `2` of `c`, and as the
identity on every other factor. -/
theorem resolutionSplitMap_comp_resolutionMergeMap (hs : #(D.circlesAt s c) = 2) :
    D.resolutionSplitMap (fun j hj ↦ (hst j hj).symm) hc.symm hs R ∘ₗ
        (D.resolutionMergeMap hst hc hs R).toLinearMap =
      Khovanov.circleX R (.inl ⟦D.crossing c 0⟧) +
        Khovanov.circleX R (.inl ⟦D.crossing c 2⟧) := by
  have hts : ∀ j, j ≠ c → t j = s j := fun j hj ↦ (hst j hj).symm
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.add_apply]
  have hproj :
      D.resolutionSplitMap hts hc.symm hs R (D.resolutionMergeMap hst hc hs R x) =
        x * D.resolutionSplitMap hts hc.symm hs R 1 := by
    rw [resolutionSplitMap_def, resolutionMergeMap_def,
      ← mul_one (fiberwiseMul (A := fun _ ↦ R[ε]) _ x)]
    exact Khovanov.fiberwiseSplit_fiberwiseMul_mul _ x 1
  rw [hproj, D.resolutionSplitMap_one, NonUnitalNonAssocSemiring.left_distrib,
    CommMagma.mul_comm x, CommMagma.mul_comm x, ← Khovanov.circleX_apply, ← Khovanov.circleX_apply]

/-- **Splitting one circle at `c` and merging the two pieces back (`m ∘ Δ = 2 • X`).** On a state
`s` with one circle through `c` (so two circles of `t` pass through `c`), splitting along `s → t`
and merging back along `t → s` acts as `2 • X` on the circle of `s` through `c`. -/
theorem resolutionMergeMap_comp_resolutionSplitMap (ht : #(D.circlesAt t c) = 2) :
    (D.resolutionMergeMap (fun j hj ↦ (hst j hj).symm) hc.symm ht R).toLinearMap ∘ₗ
        D.resolutionSplitMap hst hc ht R =
      2 • Khovanov.circleX R (.inl ⟦D.crossing c 0⟧) := by
  have hts : ∀ j, j ≠ c → t j = s j := fun j hj ↦ (hst j hj).symm
  have hs : #(D.circlesAt s c) = 1 :=
    D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hts hc.symm ht
  have hf : Function.Surjective (D.saddleResolvedCircleMap hts hs) :=
    D.saddleResolvedCircleMap_surjective hts hs
  have hf0 : D.saddleResolvedCircleMap hts hs (.inl ⟦D.crossing c 0⟧) = .inl ⟦D.crossing c 0⟧ :=
    (D.saddleResolvedCircleMap_eq_crossing_iff hts hs _).mpr (.inl rfl)
  have hf2 : D.saddleResolvedCircleMap hts hs (.inl ⟦D.crossing c 2⟧) = .inl ⟦D.crossing c 0⟧ :=
    (D.saddleResolvedCircleMap_eq_crossing_iff hts hs _).mpr (.inr rfl)
  rw [two_smul]
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.add_apply]
  have hsplit :
      D.resolutionSplitMap hst hc ht R x =
        fiberwiseMul (A := fun _ ↦ R[ε]) (Function.surjInv hf) x *
          D.resolutionSplitMap hst hc ht R 1 := by
    rw [resolutionSplitMap_def]
    exact Khovanov.fiberwiseSplit_eq_fiberwiseMul_surjInv_mul hf x
  rw [hsplit, resolutionMergeMap_def, map_mul, fiberwiseMul_fiberwiseMul_surjInv hf x,
    D.resolutionSplitMap_one, map_add, fiberwiseMul_singleAlgHom, fiberwiseMul_singleAlgHom,
    hf0, hf2, NonUnitalNonAssocSemiring.left_distrib, CommMagma.mul_comm x,
    ← Khovanov.circleX_apply]

/-- **The round-trip saddle identity in either direction.** Composing the saddle map `s → t` at `c`
with the reverse saddle map `t → s` at `c` always equals the sum of the `X` actions on the circles
through slots `0` and `2` of `c`: it is `Δ ∘ m = X_0 + X_2` when `s` has two circles at `c`, and
`m ∘ Δ = 2 • X_0 = X_0 + X_2` when `s` has one circle at `c` (where slots `0` and `2` lie on the
same circle). -/
theorem resolutionEdgeMap_comp_resolutionEdgeMap_self
    (h : #(D.circlesAt s c) = 2 ∨ #(D.circlesAt t c) = 2) :
    D.resolutionEdgeMap (fun j hj ↦ (hst j hj).symm) hc.symm h.symm R ∘ₗ
        D.resolutionEdgeMap hst hc h R =
      Khovanov.circleX R (.inl ⟦D.crossing c 0⟧) +
        Khovanov.circleX R (.inl ⟦D.crossing c 2⟧) := by
  by_cases hs : #(D.circlesAt s c) = 2
  · rw [D.resolutionEdgeMap_eq_resolutionMergeMap hst hc h R hs,
      D.resolutionEdgeMap_eq_resolutionSplitMap _ _ _ R hs]
    exact D.resolutionSplitMap_comp_resolutionMergeMap hst hc R hs
  · have ht : #(D.circlesAt t c) = 2 := h.resolve_left hs
    have hs1 : #(D.circlesAt s c) = 1 :=
      D.card_circlesAt_eq_one_of_card_circlesAt_eq_two (fun j hj ↦ (hst j hj).symm) hc.symm ht
    have h02 : (⟦D.crossing c 0⟧ : D.CrossingCircle s) = ⟦D.crossing c 2⟧ :=
      (D.card_circlesAt_eq_one_iff s c).mp hs1
    rw [D.resolutionEdgeMap_eq_resolutionSplitMap hst hc h R ht,
      D.resolutionEdgeMap_eq_resolutionMergeMap _ _ _ R ht,
      D.resolutionMergeMap_comp_resolutionSplitMap hst hc R ht, ← h02, two_smul]

/-- Composing a saddle map at `c` with its reverse equals `X_p + X_q` for the two opposite arc marks
at any slot `k` of `c`. -/
theorem resolutionEdgeMap_comp_resolutionEdgeMap_eq_circleX_add_circleX
    (h : #(D.circlesAt s c) = 2 ∨ #(D.circlesAt t c) = 2) (k : Fin 4) :
    D.resolutionEdgeMap (fun j hj ↦ (hst j hj).symm) hc.symm h.symm R ∘ₗ
        D.resolutionEdgeMap hst hc h R =
      Khovanov.circleX R ((Mark.onArc D (D.crossing c k)).resolvedCircle s) +
        Khovanov.circleX R
          ((Mark.onArc D (D.crossing c (oppositeCrossingSlot k))).resolvedCircle s) := by
  rw [D.resolutionEdgeMap_comp_resolutionEdgeMap_self hst hc R h,
    D.circleX_resolvedCircle_onArc_add_oppositeCrossingSlot R s c k]

/-- **Every saddle at `c` intertwines `X` on opposite slots of `c`.** Because one of `s` or `t` has
a single circle passing through `c` (on which `k` and `oppositeCrossingSlot k` select the same
circle), applying `X` at slot `k` before the saddle equals applying `X` at `oppositeCrossingSlot k`
after it. -/
theorem resolutionEdgeMap_circleX_oppositeCrossingSlot
    (h : #(D.circlesAt s c) = 2 ∨ #(D.circlesAt t c) = 2) (k : Fin 4)
    (x : Khovanov.CircleTensor R (D.ResolvedCircle s)) :
    D.resolutionEdgeMap hst hc h R
        (Khovanov.circleX R ((Mark.onArc D (D.crossing c k)).resolvedCircle s) x) =
      Khovanov.circleX R
        ((Mark.onArc D (D.crossing c (oppositeCrossingSlot k))).resolvedCircle t)
        (D.resolutionEdgeMap hst hc h R x) := by
  by_cases hs : #(D.circlesAt s c) = 2
  · have ht1 : #(D.circlesAt t c) = 1 :=
      D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hst hc hs
    rw [← Mark.resolvedCircle_onArc_crossing_eq_oppositeCrossingSlot_of_card_circlesAt_eq_one
      D ht1 k]
    exact D.resolutionEdgeMap_circleX (Mark.onArc D (D.crossing c k)) hst hc R h x
  · have ht : #(D.circlesAt t c) = 2 := h.resolve_left hs
    have hs1 : #(D.circlesAt s c) = 1 :=
      D.card_circlesAt_eq_one_of_card_circlesAt_eq_two (fun j hj ↦ (hst j hj).symm) hc.symm ht
    rw [Mark.resolvedCircle_onArc_crossing_eq_oppositeCrossingSlot_of_card_circlesAt_eq_one
      D hs1 k]
    exact D.resolutionEdgeMap_circleX
      (Mark.onArc D (D.crossing c (oppositeCrossingSlot k))) hst hc R h x

end Saddle

/-! ### Reverse-saddle morphisms on the Khovanov cube of resolutions -/

section Cube

variable (D : PDCode n) (c : Fin n) (hD : D.IsPlanar) (R : Type u) [CommRing R] {j j' j'' : ℤ}

private theorem reverseSaddle_resolutionCubeι_mem_range (hj : j' = j - 2) {S : Finset (Fin n)}
    (hc : c ∉ S) (x : (D.resolutionCube hD R j).obj (insert c S)) :
    let hst : ∀ i, i ≠ c → cubeState (insert c S) i = cubeState S i :=
      fun i hi ↦ (cubeState_eq_of_covBy (covBy_insert hc) hc (mem_insert_self c S) i hi).symm
    let hc_ne : cubeState (insert c S) c ≠ cubeState S c :=
      (cubeState_ne_of_notMem_of_mem hc (mem_insert_self c S)).symm
    D.resolutionEdgeMap hst hc_ne (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two hst hc_ne) R
        ((D.resolutionCubeι hD R j (insert c S)).hom x) ∈
      LinearMap.range (D.resolutionCubeι hD R j' S).hom := by
  intro hst hc_ne
  have hx : (D.resolutionCubeι hD R j (insert c S)).hom x ∈
      (Khovanov.circleQuantumGrading R (D.ResolvedCircle (cubeState (insert c S)))).piece
        (j - #(insert c S)) := by
    rw [← range_resolutionCubeι]
    exact LinearMap.mem_range_self _ x
  rw [range_resolutionCubeι]
  have hx' := (D.isHomogeneous_resolutionEdgeMap hst hc_ne
    (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two hst hc_ne) R).map_mem hx
  convert hx' using 2
  rw [card_insert_of_notMem hc, Nat.cast_succ]
  omega

/-- **The reverse saddle along `c` on the Khovanov cube of resolutions**, mapping the vertex
`insert c S` (`c ∉ S`) in quantum degree `j` to the vertex `S` in quantum degree `j' = j - 2`.
Because removing `c` lowers the cube height by `1` while the saddle map has circle-tensor quantum
degree `-1`, the net shift in `j` is `-2`. -/
def resolutionCubeReverseSaddle (hj : j' = j - 2) (S : Finset (Fin n)) (hc : c ∉ S) :
    (D.resolutionCube hD R j).obj (insert c S) ⟶ (D.resolutionCube hD R j').obj S :=
  let hst : ∀ i, i ≠ c → cubeState (insert c S) i = cubeState S i :=
    fun i hi ↦ (cubeState_eq_of_covBy (covBy_insert hc) hc (mem_insert_self c S) i hi).symm
  let hc_ne : cubeState (insert c S) c ≠ cubeState S c :=
    (cubeState_ne_of_notMem_of_mem hc (mem_insert_self c S)).symm
  ModuleCat.ofHom <|
    (LinearEquiv.ofInjective _ (D.resolutionCubeι_injective hD R j' S)).symm.toLinearMap ∘ₗ
      ((D.resolutionEdgeMap hst hc_ne
          (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two hst hc_ne) R) ∘ₗ
        (D.resolutionCubeι hD R j (insert c S)).hom).codRestrict _
        (D.reverseSaddle_resolutionCubeι_mem_range c hD R hj hc)

/-- Under the vertex inclusions `resolutionCubeι`, `resolutionCubeReverseSaddle` acts by the saddle
map from `cubeState (insert c S)` back to `cubeState S`. -/
@[reassoc]
theorem resolutionCubeReverseSaddle_comp_resolutionCubeι (hj : j' = j - 2) (S : Finset (Fin n))
    (hc : c ∉ S) :
    D.resolutionCubeReverseSaddle c hD R hj S hc ≫ D.resolutionCubeι hD R j' S =
      D.resolutionCubeι hD R j (insert c S) ≫
        ModuleCat.ofHom (D.resolutionEdgeMap
          (fun i hi ↦ (cubeState_eq_of_covBy (covBy_insert hc) hc (mem_insert_self c S) i hi).symm)
          (cubeState_ne_of_notMem_of_mem hc (mem_insert_self c S)).symm
          (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two
            (fun i hi ↦
              (cubeState_eq_of_covBy (covBy_insert hc) hc (mem_insert_self c S) i hi).symm)
            (cubeState_ne_of_notMem_of_mem hc (mem_insert_self c S)).symm) R) := by
  ext x
  simp [resolutionCubeReverseSaddle]

/-- **The reverse saddle at `c` commutes with all unaffected cube edges `a ≠ c`.** Each mixed square
consists of four saddle edges between states differing at `c` and `a`, which commute by
`TauCeti.PDCode.resolutionEdgeMap_comp_resolutionEdgeMap_comm`. -/
theorem isCubeReverseEdgeCompatible_resolutionCubeReverseSaddle (hj : j' = j - 2) :
    Functor.IsCubeReverseEdgeCompatible (D.resolutionCube hD R j) (D.resolutionCube hD R j') c
      (D.resolutionCubeReverseSaddle c hD R hj) := by
  rw [Functor.isCubeReverseEdgeCompatible_def]
  intro S hc a ha
  have haS : a ∉ S := fun haS ↦ ha (mem_insert_of_mem haS)
  have hc' : c ∉ insert a S := fun hc' ↦ ha (by
    rcases mem_insert.1 hc' with rfl | hmem
    · exact mem_insert_self c S
    · exact absurd hmem hc)
  have hst₁ : ∀ i, i ≠ c → cubeState (insert c S) i = cubeState S i :=
    fun i hi ↦ (cubeState_eq_of_covBy (covBy_insert hc) hc (mem_insert_self c S) i hi).symm
  have hc₁ : cubeState (insert c S) c ≠ cubeState S c :=
    (cubeState_ne_of_notMem_of_mem hc (mem_insert_self c S)).symm
  have ht₁u : ∀ i, i ≠ a → cubeState S i = cubeState (insert a S) i :=
    cubeState_eq_of_covBy (covBy_insert haS) haS (mem_insert_self a S)
  have hc₁' : cubeState S a ≠ cubeState (insert a S) a :=
    cubeState_ne_of_notMem_of_mem haS (mem_insert_self a S)
  have hst₂ : ∀ i, i ≠ a → cubeState (insert c S) i = cubeState (insert c (insert a S)) i := by
    intro i hi
    simp [cubeState_apply, hi]
  have hc₂ : cubeState (insert c S) a ≠ cubeState (insert c (insert a S)) a :=
    cubeState_ne_of_notMem_of_mem ha (mem_insert_of_mem (mem_insert_self a S))
  have ht₂u : ∀ i, i ≠ c → cubeState (insert c (insert a S)) i = cubeState (insert a S) i :=
    fun i hi ↦ (cubeState_eq_of_covBy (covBy_insert hc') hc'
      (mem_insert_self c (insert a S)) i hi).symm
  have hc₂' : cubeState (insert c (insert a S)) c ≠ cubeState (insert a S) c :=
    (cubeState_ne_of_notMem_of_mem hc' (mem_insert_self c (insert a S))).symm
  rw [← cancel_mono (D.resolutionCubeι hD R j' (insert a S)), Category.assoc, Category.assoc,
    D.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι hD R j' haS,
    D.resolutionCubeReverseSaddle_comp_resolutionCubeι_assoc c hD R hj S hc,
    D.resolutionCubeReverseSaddle_comp_resolutionCubeι c hD R hj (insert a S) hc',
    reassoc_of% (D.resolutionCube_map_homOfLE_comp_resolutionCubeι hD R j (insert_comm a c S)
      (insert_subset_insert c (S.subset_insert a)) hst₂ hc₂
      (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two hst₂ hc₂))]
  ext x
  exact LinearMap.congr_fun (D.resolutionEdgeMap_comp_resolutionEdgeMap_comm
    hst₁ hc₁ ht₁u hc₁' hst₂ hc₂ ht₂u hc₂'
    (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two hst₁ hc₁)
    (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two ht₁u hc₁')
    (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two hst₂ hc₂)
    (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two ht₂u hc₂') R)
    ((D.resolutionCubeι hD R j (insert c S)).hom x)

/-- On a cube vertex `S` with `c ∉ S`, advancing along `c` and then applying the reverse saddle at
`c` equals `X_p + X_q` for the opposite arc marks at slot `k` of `c`. -/
theorem resolutionCube_map_comp_resolutionCubeReverseSaddle (k : Fin 4) (hj : j' = j - 2)
    (S : Finset (Fin n)) (hc : c ∉ S) :
    (D.resolutionCube hD R j).map (homOfLE (S.subset_insert c)) ≫
        D.resolutionCubeReverseSaddle c hD R hj S hc =
      (D.resolutionCubeMarkX (Mark.onArc D (D.crossing c k)) hD R hj).app S +
        (D.resolutionCubeMarkX
          (Mark.onArc D (D.crossing c (oppositeCrossingSlot k))) hD R hj).app S := by
  rw [← cancel_mono (D.resolutionCubeι hD R j' S), Category.assoc, Preadditive.add_comp,
    D.resolutionCubeReverseSaddle_comp_resolutionCubeι c hD R hj S hc,
    D.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι_assoc hD R j hc,
    D.resolutionCubeMarkX_app_comp_resolutionCubeι, D.resolutionCubeMarkX_app_comp_resolutionCubeι]
  have hst := cubeState_eq_of_covBy (covBy_insert hc) hc (mem_insert_self c S)
  have hc_ne := cubeState_ne_of_notMem_of_mem hc (mem_insert_self c S)
  have hround := D.resolutionEdgeMap_comp_resolutionEdgeMap_eq_circleX_add_circleX hst hc_ne R
    (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two hst hc_ne) k
  ext x
  exact LinearMap.congr_fun hround ((D.resolutionCubeι hD R j S).hom x)

/-- On a cube vertex `insert c S` (`c ∉ S`), applying the reverse saddle at `c` and then advancing
along `c` equals `X_p + X_q` for the opposite arc marks at slot `k` of `c`. -/
theorem resolutionCubeReverseSaddle_comp_resolutionCube_map (k : Fin 4) (hj : j' = j - 2)
    (S : Finset (Fin n)) (hc : c ∉ S) :
    D.resolutionCubeReverseSaddle c hD R hj S hc ≫
        (D.resolutionCube hD R j').map (homOfLE (S.subset_insert c)) =
      (D.resolutionCubeMarkX (Mark.onArc D (D.crossing c k)) hD R hj).app (insert c S) +
        (D.resolutionCubeMarkX
          (Mark.onArc D (D.crossing c (oppositeCrossingSlot k))) hD R hj).app (insert c S) := by
  rw [← cancel_mono (D.resolutionCubeι hD R j' (insert c S)), Category.assoc, Preadditive.add_comp,
    D.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι hD R j' hc,
    D.resolutionCubeReverseSaddle_comp_resolutionCubeι_assoc c hD R hj S hc,
    D.resolutionCubeMarkX_app_comp_resolutionCubeι, D.resolutionCubeMarkX_app_comp_resolutionCubeι]
  have hts : ∀ i, i ≠ c → cubeState (insert c S) i = cubeState S i :=
    fun i hi ↦ (cubeState_eq_of_covBy (covBy_insert hc) hc (mem_insert_self c S) i hi).symm
  have hc_ne : cubeState (insert c S) c ≠ cubeState S c :=
    (cubeState_ne_of_notMem_of_mem hc (mem_insert_self c S)).symm
  have hround := D.resolutionEdgeMap_comp_resolutionEdgeMap_eq_circleX_add_circleX hts hc_ne R
    (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two hts hc_ne) k
  ext x
  exact LinearMap.congr_fun hround ((D.resolutionCubeι hD R j (insert c S)).hom x)

/-- Along every `c`-edge of the cube, the reverse saddle intertwines `X` at slot `k` of `c` with `X`
at `oppositeCrossingSlot k`. -/
@[reassoc]
theorem resolutionCubeMarkX_app_comp_resolutionCubeReverseSaddle_oppositeCrossingSlot (k : Fin 4)
    (hj : j' = j - 2) (hj' : j'' = j' - 2) (S : Finset (Fin n)) (hc : c ∉ S) :
    (D.resolutionCubeMarkX (Mark.onArc D (D.crossing c k)) hD R hj).app (insert c S) ≫
        D.resolutionCubeReverseSaddle c hD R hj' S hc =
      D.resolutionCubeReverseSaddle c hD R hj S hc ≫
        (D.resolutionCubeMarkX
          (Mark.onArc D (D.crossing c (oppositeCrossingSlot k))) hD R hj').app S := by
  rw [← cancel_mono (D.resolutionCubeι hD R j'' S), Category.assoc, Category.assoc,
    D.resolutionCubeReverseSaddle_comp_resolutionCubeι c hD R hj' S hc,
    D.resolutionCubeMarkX_app_comp_resolutionCubeι_assoc,
    D.resolutionCubeMarkX_app_comp_resolutionCubeι,
    D.resolutionCubeReverseSaddle_comp_resolutionCubeι_assoc c hD R hj S hc]
  ext x
  exact D.resolutionEdgeMap_circleX_oppositeCrossingSlot _ _ R _ k
    ((D.resolutionCubeι hD R j (insert c S)).hom x)

/-- Along every `c`-edge of the cube, the reverse saddle commutes with the `X` action at any fixed
mark `r`. -/
@[reassoc]
theorem resolutionCubeMarkX_app_comp_resolutionCubeReverseSaddle (r : D.Mark)
    (hj : j' = j - 2) (hj' : j'' = j' - 2) (S : Finset (Fin n)) (hc : c ∉ S) :
    (D.resolutionCubeMarkX r hD R hj).app (insert c S) ≫
        D.resolutionCubeReverseSaddle c hD R hj' S hc =
      D.resolutionCubeReverseSaddle c hD R hj S hc ≫
        (D.resolutionCubeMarkX r hD R hj').app S := by
  rw [← cancel_mono (D.resolutionCubeι hD R j'' S), Category.assoc, Category.assoc,
    D.resolutionCubeReverseSaddle_comp_resolutionCubeι c hD R hj' S hc,
    D.resolutionCubeMarkX_app_comp_resolutionCubeι_assoc,
    D.resolutionCubeMarkX_app_comp_resolutionCubeι,
    D.resolutionCubeReverseSaddle_comp_resolutionCubeι_assoc c hD R hj S hc]
  ext x
  exact D.resolutionEdgeMap_circleX r _ _ R _
    ((D.resolutionCubeι hD R j (insert c S)).hom x)

end Cube

end TauCeti.PDCode

/-! ### The mark-slide homotopy on the normalized Khovanov complex and homology -/

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ} (D : OrientedPDCode n) (c : Fin n) (hD : D.toPDCode.IsPlanar)
  (R : Type u) [CommRing R] {j j' j'' : ℤ}

/-- **The signed reverse-saddle homotopy `H` at crossing `c`** on the normalized Khovanov complex,
of cochain degree `-1` (`l + 1 = i`) and quantum degree `-2` (`j' = j - 2`). On a state summand `U`
containing `c` it acts by `TauCeti.PDCode.resolutionCubeReverseSaddle` with Koszul sign
`(-1) ^ #{b ∈ U \ {c} | b < c}`, and on a state avoiding `c` it vanishes. -/
def khovanovComplexMarkSlideHom (hj : j' = j - 2) (i l : ℤ) :
    (D.khovanovComplex hD R j).X i ⟶ (D.khovanovComplex hD R j').X l :=
  eqToHom (D.khovanovComplex_X hD R j i) ≫
    Functor.cubeReverseEdgeHom
      (D.toPDCode.resolutionCube hD R
        (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount))
      (D.toPDCode.resolutionCube hD R
        (j' - D.positiveCrossingCount + 2 * D.negativeCrossingCount))
      c (D.toPDCode.resolutionCubeReverseSaddle c hD R (by omega))
      (i + D.negativeCrossingCount) (l + D.negativeCrossingCount) ≫
    eqToHom (D.khovanovComplex_X hD R j' l).symm

/-- The mark-slide homotopy vanishes outside cochain degree `-1`. -/
theorem khovanovComplexMarkSlideHom_of_ne (hj : j' = j - 2) {i l : ℤ} (hil : l + 1 ≠ i) :
    D.khovanovComplexMarkSlideHom c hD R hj i l = 0 := by
  rw [khovanovComplexMarkSlideHom,
    Functor.cubeReverseEdgeHom_of_ne _ _ _ _ (by omega), zero_comp, comp_zero]

/-- On a state summand avoiding `c`, the mark-slide homotopy at `c` vanishes. -/
@[reassoc (attr := simp)]
theorem khovanovComplexι_khovanovComplexMarkSlideHom_of_notMem (hj : j' = j - 2) {i l : ℤ}
    (U : {U : Finset (Fin n) // (#U : ℤ) = i + D.negativeCrossingCount}) (hc : c ∉ U.1) :
    D.khovanovComplexι hD R j U ≫ D.khovanovComplexMarkSlideHom c hD R hj i l = 0 := by
  rw [khovanovComplexι_def, khovanovComplexMarkSlideHom, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp, Functor.ι_cubeReverseEdgeHom_of_notMem_assoc _ _ _ _ U hc,
    zero_comp]

/-- On a state summand `insert c S` (`c ∉ S`), the mark-slide homotopy at `c` applies the reverse
saddle into `S` with Koszul sign `(-1) ^ #{b ∈ S | b < c}`. -/
@[reassoc (attr := simp)]
theorem khovanovComplexι_khovanovComplexMarkSlideHom_insert (hj : j' = j - 2) {i : ℤ}
    (S : {S : Finset (Fin n) // (#S : ℤ) = i + D.negativeCrossingCount}) (hc : c ∉ S.1) :
    D.khovanovComplexι hD R j ⟨insert c S.1, by
        rw [card_insert_of_notMem hc, Nat.cast_succ, S.2]
        omega⟩ ≫
      D.khovanovComplexMarkSlideHom c hD R hj (i + 1) i =
    ((-1 : ℤ) ^ #{b ∈ S.1 | b < c}) •
      (D.toPDCode.resolutionCubeReverseSaddle c hD R (by omega) S.1 hc ≫
        D.khovanovComplexι hD R j' S) := by
  let F := D.toPDCode.resolutionCube hD R
    (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
  let G := D.toPDCode.resolutionCube hD R
    (j' - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
  have he : i + 1 + (D.negativeCrossingCount : ℤ) = i + D.negativeCrossingCount + 1 := by omega
  rw [khovanovComplexι_def, khovanovComplexMarkSlideHom, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  have hι :
      F.cubeComplexι (r := i + 1 + D.negativeCrossingCount) ⟨insert c S.1, by
          rw [card_insert_of_notMem hc, Nat.cast_succ, S.2]; omega⟩ =
        F.cubeComplexι (r := i + D.negativeCrossingCount + 1) ⟨insert c S.1, by
          rw [card_insert_of_notMem hc, Nat.cast_succ, S.2]⟩ ≫
          (F.cubeComplex.XIsoOfEq he.symm).hom :=
    (F.cubeComplexι_comp_XIsoOfEq_hom he.symm
      ⟨insert c S.1, by rw [card_insert_of_notMem hc, Nat.cast_succ, S.2]⟩).symm
  have hH :
      (F.cubeComplex.XIsoOfEq he.symm).hom ≫
          Functor.cubeReverseEdgeHom F G c
            (D.toPDCode.resolutionCubeReverseSaddle c hD R (by omega))
            (i + 1 + D.negativeCrossingCount) (i + D.negativeCrossingCount) =
        Functor.cubeReverseEdgeHom F G c
          (D.toPDCode.resolutionCubeReverseSaddle c hD R (by omega))
          (i + D.negativeCrossingCount + 1) (i + D.negativeCrossingCount) := by
    clear hι
    revert he
    generalize i + 1 + (D.negativeCrossingCount : ℤ) = m
    rintro rfl
    simp
  rw [hι, Category.assoc, ← Category.assoc (F.cubeComplex.XIsoOfEq he.symm).hom, hH,
    Functor.ι_cubeReverseEdgeHom_insert_assoc F G c _ S hc, Preadditive.zsmul_comp,
    Category.assoc, ← khovanovComplexι_def]

/-- Projecting the mark-slide homotopy at `c` onto a state containing `c` gives `0`. -/
@[reassoc (attr := simp)]
theorem khovanovComplexMarkSlideHom_khovanovComplexπ_of_mem (hj : j' = j - 2) {i l : ℤ}
    (T : {T : Finset (Fin n) // (#T : ℤ) = l + D.negativeCrossingCount}) (hc : c ∈ T.1) :
    D.khovanovComplexMarkSlideHom c hD R hj i l ≫ D.khovanovComplexπ hD R j' T = 0 := by
  rw [khovanovComplexMarkSlideHom, khovanovComplexπ_def, Category.assoc, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Functor.cubeReverseEdgeHom_π_of_mem _ _ _ _ T hc, comp_zero]

/-- Projecting the mark-slide homotopy at `c` onto a state `S` avoiding `c` gives the state
projection onto `insert c S` followed by the reverse saddle with sign `(-1) ^ #{b ∈ S | b < c}`. -/
@[reassoc (attr := simp)]
theorem khovanovComplexMarkSlideHom_khovanovComplexπ_of_notMem (hj : j' = j - 2) {i : ℤ}
    (S : {S : Finset (Fin n) // (#S : ℤ) = i + D.negativeCrossingCount}) (hc : c ∉ S.1) :
    D.khovanovComplexMarkSlideHom c hD R hj (i + 1) i ≫ D.khovanovComplexπ hD R j' S =
      ((-1 : ℤ) ^ #{b ∈ S.1 | b < c}) •
        (D.khovanovComplexπ hD R j ⟨insert c S.1, by
            rw [card_insert_of_notMem hc, Nat.cast_succ, S.2]
            omega⟩ ≫
          D.toPDCode.resolutionCubeReverseSaddle c hD R (by omega) S.1 hc) := by
  refine D.khovanovComplex_hom_ext hD R j fun U ↦ ?_
  by_cases hcU : c ∈ U.1
  · have hcard : (#(U.1.erase c) : ℤ) = i + D.negativeCrossingCount := by
      have := card_erase_add_one hcU
      have := U.2
      omega
    let V : {V : Finset (Fin n) // (#V : ℤ) = i + D.negativeCrossingCount} := ⟨U.1.erase c, hcard⟩
    have hcV : c ∉ V.1 := notMem_erase c U.1
    have hU : U = ⟨insert c V.1, by rw [card_insert_of_notMem hcV, Nat.cast_succ, V.2]; omega⟩ :=
      Subtype.ext (insert_erase hcU).symm
    rw [hU, khovanovComplexι_khovanovComplexMarkSlideHom_insert_assoc D c hD R hj V hcV,
      Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
    by_cases hVS : V = S
    · subst hVS
      rw [khovanovComplexι_π_self, Category.comp_id, khovanovComplexι_π_self_assoc]
    · rw [khovanovComplexι_π_of_ne D hD R j' hVS, comp_zero, smul_zero,
        khovanovComplexι_π_of_ne_assoc, zero_comp, smul_zero]
      intro hins
      apply hVS
      apply Subtype.ext
      have hErase := congrArg (fun X ↦ X.1.erase c) hins
      dsimp only at hErase
      rwa [erase_insert hcV, erase_insert hc] at hErase
  · rw [khovanovComplexι_khovanovComplexMarkSlideHom_of_notMem_assoc D c hD R hj U hcU, zero_comp,
      Preadditive.comp_zsmul, khovanovComplexι_π_of_ne_assoc, zero_comp, smul_zero]
    intro hins
    exact hcU (congrArg Subtype.val hins ▸ mem_insert_self c S.1)

/-- **The mark-slide homotopy squares to zero (`H² = 0`).** Its image lies in state summands
avoiding `c`, on which a second application of `H` vanishes. -/
@[reassoc (attr := simp)]
theorem khovanovComplexMarkSlideHom_comp_khovanovComplexMarkSlideHom (hj : j' = j - 2)
    (hj' : j'' = j' - 2) (i l m : ℤ) :
    D.khovanovComplexMarkSlideHom c hD R hj i l ≫
        D.khovanovComplexMarkSlideHom c hD R hj' l m = 0 := by
  rw [khovanovComplexMarkSlideHom, khovanovComplexMarkSlideHom, Category.assoc, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Functor.cubeReverseEdgeHom_comp_cubeReverseEdgeHom_assoc, zero_comp, comp_zero]

private theorem khovanovComplexMarkX_f_eq (p : D.toPDCode.Mark) (hj : j' = j - 2) (i : ℤ) :
    (D.khovanovComplexMarkX p hD R hj).f i =
      eqToHom (D.khovanovComplex_X hD R j i) ≫
        (NatTrans.cubeComplexMap (D.toPDCode.resolutionCubeMarkX p hD R
          (j := j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
          (j' := j' - D.positiveCrossingCount + 2 * D.negativeCrossingCount) (by omega))).f
          (i + D.negativeCrossingCount) ≫
        eqToHom (D.khovanovComplex_X hD R j' i).symm := by
  refine D.khovanovComplex_hom_ext hD R j fun S ↦ ?_
  rw [khovanovComplexι_khovanovComplexMarkX_f, khovanovComplexι_def D hD R j S, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, NatTrans.ι_cubeComplexMap_f_assoc,
    ← khovanovComplexι_def]

/-- **The mark-slide homotopy intertwines opposite-strand `X` actions (`H ∘ X_p = X_q ∘ H`).** In
categorical composition order, `(X_p).f i ≫ H i l = H i l ≫ (X_q).f l` for `p` at slot `k` of `c`
and `q` at `oppositeCrossingSlot k`. -/
@[reassoc]
theorem khovanovComplexMarkX_f_comp_khovanovComplexMarkSlideHom_oppositeCrossingSlot (k : Fin 4)
    (hj : j' = j - 2) (hj' : j'' = j' - 2) (i l : ℤ) :
    (D.khovanovComplexMarkX (PDCode.Mark.onArc D.toPDCode (D.toPDCode.crossing c k))
          hD R hj).f i ≫
        D.khovanovComplexMarkSlideHom c hD R hj' i l =
      D.khovanovComplexMarkSlideHom c hD R hj i l ≫
        (D.khovanovComplexMarkX
          (PDCode.Mark.onArc D.toPDCode (D.toPDCode.crossing c (PDCode.oppositeCrossingSlot k)))
          hD R hj').f l := by
  rw [D.khovanovComplexMarkX_f_eq _ _ _ hj, D.khovanovComplexMarkX_f_eq _ _ _ hj',
    khovanovComplexMarkSlideHom, khovanovComplexMarkSlideHom]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [Functor.cubeComplexMap_f_comp_cubeReverseEdgeHom_assoc _ _ _ _ _ fun S hc ↦
    D.toPDCode.resolutionCubeMarkX_app_comp_resolutionCubeReverseSaddle_oppositeCrossingSlot c hD R
      k (j := j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
      (j' := j' - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
      (j'' := j'' - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
      (by omega) (by omega) S hc]

/-- The mark-slide homotopy at `c` commutes with the `X` action at any fixed mark `r`. -/
@[reassoc]
theorem khovanovComplexMarkX_f_comp_khovanovComplexMarkSlideHom (r : D.toPDCode.Mark)
    (hj : j' = j - 2) (hj' : j'' = j' - 2) (i l : ℤ) :
    (D.khovanovComplexMarkX r hD R hj).f i ≫ D.khovanovComplexMarkSlideHom c hD R hj' i l =
      D.khovanovComplexMarkSlideHom c hD R hj i l ≫ (D.khovanovComplexMarkX r hD R hj').f l := by
  rw [D.khovanovComplexMarkX_f_eq _ _ _ hj, D.khovanovComplexMarkX_f_eq _ _ _ hj',
    khovanovComplexMarkSlideHom, khovanovComplexMarkSlideHom]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [Functor.cubeComplexMap_f_comp_cubeReverseEdgeHom_assoc _ _ _ _ _ fun S hc ↦
    D.toPDCode.resolutionCubeMarkX_app_comp_resolutionCubeReverseSaddle c hD R r
      (j := j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
      (j' := j' - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
      (j'' := j'' - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
      (by omega) (by omega) S hc]

/-- **The mark-slide chain homotopy equation (`d ≫ H + H ≫ d = X_p + X_q`)** on the normalized
Khovanov complex, for opposite arc marks `p` and `q` at slot `k` and `oppositeCrossingSlot k` of
crossing `c`. -/
theorem d_comp_khovanovComplexMarkSlideHom_add_khovanovComplexMarkSlideHom_comp_d (k : Fin 4)
    (hj : j' = j - 2) (i : ℤ) :
    (D.khovanovComplex hD R j).d i (i + 1) ≫
        D.khovanovComplexMarkSlideHom c hD R hj (i + 1) i +
      D.khovanovComplexMarkSlideHom c hD R hj i (i - 1) ≫
        (D.khovanovComplex hD R j').d (i - 1) i =
    (D.khovanovComplexMarkX (PDCode.Mark.onArc D.toPDCode (D.toPDCode.crossing c k)) hD R hj).f i +
      (D.khovanovComplexMarkX
        (PDCode.Mark.onArc D.toPDCode (D.toPDCode.crossing c (PDCode.oppositeCrossingSlot k)))
        hD R hj).f i := by
  let F := D.toPDCode.resolutionCube hD R
    (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
  let G := D.toPDCode.resolutionCube hD R
    (j' - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
  let h := D.toPDCode.resolutionCubeReverseSaddle c hD R
    (j := j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
    (j' := j' - D.positiveCrossingCount + 2 * D.negativeCrossingCount) (by omega)
  let p := PDCode.Mark.onArc D.toPDCode (D.toPDCode.crossing c k)
  let q := PDCode.Mark.onArc D.toPDCode (D.toPDCode.crossing c (PDCode.oppositeCrossingSlot k))
  let Hzero := Functor.cubeReverseEdgeHomotopyZero c h
    (D.toPDCode.isCubeReverseEdgeCompatible_resolutionCubeReverseSaddle c hD R (by omega))
    (D.toPDCode.resolutionCubeMarkX p hD R (by omega) +
      D.toPDCode.resolutionCubeMarkX q hD R (by omega))
    (fun S hc ↦ (D.toPDCode.resolutionCube_map_comp_resolutionCubeReverseSaddle c hD R k
      (by omega) S hc).symm)
    (fun S hc ↦ (D.toPDCode.resolutionCubeReverseSaddle_comp_resolutionCube_map c hD R k
      (by omega) S hc).symm)
  have hcube := Hzero.comm (i + D.negativeCrossingCount)
  have hhom : Hzero.hom = Functor.cubeReverseEdgeHom F G c h := by
    funext a b
    simp [Hzero, F, G, h]
  rw [hhom, HomologicalComplex.zero_f, add_zero] at hcube
  have hrel_next : (ComplexShape.up ℤ).Rel (i + D.negativeCrossingCount)
      (i + 1 + D.negativeCrossingCount) := by
    simp only [ComplexShape.up_Rel]
    omega
  have hrel_prev : (ComplexShape.up ℤ).Rel (i - 1 + D.negativeCrossingCount)
      (i + D.negativeCrossingCount) := by
    simp only [ComplexShape.up_Rel]
    omega
  rw [dNext_eq _ hrel_next, prevD_eq _ hrel_prev] at hcube
  refine D.khovanovComplex_hom_ext hD R j fun S ↦ ?_
  rw [Preadditive.comp_add, Preadditive.comp_add, khovanovComplexι_khovanovComplexMarkX_f,
    khovanovComplexι_khovanovComplexMarkX_f]
  have hdNext :
      D.khovanovComplexι hD R j S ≫
          (D.khovanovComplex hD R j).d i (i + 1) ≫
          D.khovanovComplexMarkSlideHom c hD R hj (i + 1) i =
        F.cubeComplexι S ≫ F.cubeComplex.d (i + D.negativeCrossingCount)
          (i + 1 + D.negativeCrossingCount) ≫
          Functor.cubeReverseEdgeHom F G c h
            (i + 1 + D.negativeCrossingCount) (i + D.negativeCrossingCount) ≫
          eqToHom (D.khovanovComplex_X hD R j' i).symm := by
    rw [khovanovComplexι_def, D.khovanovComplex_d hD R j i (i + 1), khovanovComplexMarkSlideHom]
    simp only [F, G, h, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hprevD :
      D.khovanovComplexι hD R j S ≫
          D.khovanovComplexMarkSlideHom c hD R hj i (i - 1) ≫
          (D.khovanovComplex hD R j').d (i - 1) i =
        F.cubeComplexι S ≫ Functor.cubeReverseEdgeHom F G c h
            (i + D.negativeCrossingCount) (i - 1 + D.negativeCrossingCount) ≫
          G.cubeComplex.d (i - 1 + D.negativeCrossingCount) (i + D.negativeCrossingCount) ≫
          eqToHom (D.khovanovComplex_X hD R j' i).symm := by
    rw [khovanovComplexι_def, khovanovComplexMarkSlideHom, D.khovanovComplex_d hD R j' (i - 1) i]
    simp only [F, G, h, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [hdNext, hprevD]
  have hsum := congrArg (fun f ↦ F.cubeComplexι S ≫ f ≫
    eqToHom (D.khovanovComplex_X hD R j' i).symm) hcube.symm
  simpa only [F, G, h, p, q, Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
    NatTrans.cubeComplexMap_add, HomologicalComplex.add_f_apply,
    NatTrans.ι_cubeComplexMap_f_assoc, ← khovanovComplexι_def] using hsum

/-- **Chain null-homotopy `X_p + X_q ≃ 0`** on the normalized Khovanov complex for opposite arc
marks `p` and `q` at slot `k` and `oppositeCrossingSlot k` of crossing `c`, witnessed by
`TauCeti.OrientedPDCode.khovanovComplexMarkSlideHom`. -/
def khovanovComplexMarkSlideHomotopyZero (k : Fin 4) (hj : j' = j - 2) :
    Homotopy
      (D.khovanovComplexMarkX (PDCode.Mark.onArc D.toPDCode (D.toPDCode.crossing c k)) hD R hj +
        D.khovanovComplexMarkX
          (PDCode.Mark.onArc D.toPDCode (D.toPDCode.crossing c (PDCode.oppositeCrossingSlot k)))
          hD R hj)
      0 where
  hom := D.khovanovComplexMarkSlideHom c hD R hj
  zero _ _ hil := D.khovanovComplexMarkSlideHom_of_ne c hD R hj hil
  comm i := by
    have hrel_next : (ComplexShape.up ℤ).Rel i (i + 1) := rfl
    have hrel_prev : (ComplexShape.up ℤ).Rel (i - 1) i := sub_add_cancel i 1
    rw [HomologicalComplex.add_f_apply, HomologicalComplex.zero_f, add_zero, dNext_eq _ hrel_next,
      prevD_eq _ hrel_prev]
    exact (D.d_comp_khovanovComplexMarkSlideHom_add_khovanovComplexMarkSlideHom_comp_d c hD R k
      hj i).symm

/-- The components of `khovanovComplexMarkSlideHomotopyZero` are `khovanovComplexMarkSlideHom`. -/
@[simp]
theorem khovanovComplexMarkSlideHomotopyZero_hom (k : Fin 4) (hj : j' = j - 2) (i l : ℤ) :
    (D.khovanovComplexMarkSlideHomotopyZero c hD R k hj).hom i l =
      D.khovanovComplexMarkSlideHom c hD R hj i l :=
  (rfl)

/-- **Chain homotopy `X_p ≃ -X_q`** on the normalized Khovanov complex when sliding a mark across
crossing `c` from slot `k` to `oppositeCrossingSlot k`, witnessed by
`TauCeti.OrientedPDCode.khovanovComplexMarkSlideHom`. -/
def khovanovComplexMarkSlideHomotopyNeg (k : Fin 4) (hj : j' = j - 2) :
    Homotopy
      (D.khovanovComplexMarkX (PDCode.Mark.onArc D.toPDCode (D.toPDCode.crossing c k)) hD R hj)
      (-D.khovanovComplexMarkX
        (PDCode.Mark.onArc D.toPDCode (D.toPDCode.crossing c (PDCode.oppositeCrossingSlot k)))
        hD R hj) where
  hom := D.khovanovComplexMarkSlideHom c hD R hj
  zero _ _ hil := D.khovanovComplexMarkSlideHom_of_ne c hD R hj hil
  comm i := by
    have hzero := (D.khovanovComplexMarkSlideHomotopyZero c hD R k hj).comm i
    have hhom : (D.khovanovComplexMarkSlideHomotopyZero c hD R k hj).hom =
        D.khovanovComplexMarkSlideHom c hD R hj := rfl
    rw [hhom, HomologicalComplex.add_f_apply, HomologicalComplex.zero_f, add_zero] at hzero
    rw [HomologicalComplex.neg_f_apply]
    exact eq_add_neg_of_add_eq hzero

/-- The components of `khovanovComplexMarkSlideHomotopyNeg` are `khovanovComplexMarkSlideHom`. -/
@[simp]
theorem khovanovComplexMarkSlideHomotopyNeg_hom (k : Fin 4) (hj : j' = j - 2) (i l : ℤ) :
    (D.khovanovComplexMarkSlideHomotopyNeg c hD R k hj).hom i l =
      D.khovanovComplexMarkSlideHom c hD R hj i l :=
  (rfl)

/-- **Sliding a mark across one crossing negates the induced `X` map on Khovanov homology.** For
opposite arc marks `p` and `q` at slot `k` and `oppositeCrossingSlot k` of crossing `c`, the maps
induced on `D.khovanovHomology hD R i j ⟶ D.khovanovHomology hD R i j'` satisfy `X_p = -X_q`. -/
theorem homologyMap_khovanovComplexMarkX_oppositeCrossingSlot (k : Fin 4) (hj : j' = j - 2)
    (i : ℤ) :
    HomologicalComplex.homologyMap
      (D.khovanovComplexMarkX (PDCode.Mark.onArc D.toPDCode (D.toPDCode.crossing c k)) hD R hj) i =
    -HomologicalComplex.homologyMap
      (D.khovanovComplexMarkX
        (PDCode.Mark.onArc D.toPDCode (D.toPDCode.crossing c (PDCode.oppositeCrossingSlot k)))
        hD R hj) i := by
  rw [(D.khovanovComplexMarkSlideHomotopyNeg c hD R k hj).homologyMap_eq i,
    HomologicalComplex.homologyMap_neg]

end TauCeti.OrientedPDCode
