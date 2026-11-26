/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Cube.Homotopy
public import TauCeti.KnotTheory.Khovanov.Homology
public import TauCeti.KnotTheory.Khovanov.Mark.Basic

import TauCeti.KnotTheory.Khovanov.Resolution.NeckCutting

/-!
# Sliding a mark across a crossing

Let `c` be a crossing of a link diagram and let `p` and `q` be the arc marks on opposite sides of a
local strand through `c`: for a slot `k : Fin 4`, `p` lies on `D.crossing c k` and `q` lies on
`D.crossing c (oppositeCrossingSlot k)`. Each local smoothing at `c` joins every slot to one of its
neighbours and never to its opposite slot, so in every smoothing state `s` the circles selected by
`p` and `q` are the two circles through slots `0` and `2` in some order
(`TauCeti.PDCode.CrossingCircle.mk_crossing_oppositeCrossingSlot_pair`). In particular,
`X_p + X_q = X_0 + X_2` on every state, and when only one circle of `s` meets `c` the marks `p` and
`q` select the same circle
(`PDCode.Mark.resolvedCircle_onArc_crossing_eq_oppositeCrossingSlot_of_card_circlesAt_eq_one`).

Reversing the saddle map along the edges in direction `c` gives a bidegree-`(-1, -2)` homotopy `H`
on the Khovanov complex (`TauCeti.OrientedPDCode.khovanovComplexMarkSlideHom`): on a state `S`
having the `B`-smoothing at `c` (`c ∈ S`), `H` applies the reverse saddle `S → S \ {c}` with the
cube Koszul sign `(-1) ^ #{b ∈ S \ {c} | b < c}`, and on a state with `c ∉ S` it vanishes.

All mixed squares formed by the reverse saddle at `c` and a forward saddle at another crossing
`a ≠ c` commute by `TauCeti.PDCode.resolutionEdgeMap_comp_resolutionEdgeMap_comm`, so their signed
contributions to `d ≫ H + H ≫ d` cancel by `CategoryTheory.Functor.cubeReverseEdgeHomotopyZero`.
What remains on each state is the round-trip saddle composite at `c` alone
(`TauCeti.PDCode.resolutionEdgeMap_reverse_resolutionEdgeMap`,
`TauCeti.PDCode.resolutionEdgeMap_comp_resolutionEdgeMap_eq_circleX_add_circleX`):

* when two circles of the state pass through `c`, the composite is `Δ ∘ m = X ⊗ 1 + 1 ⊗ X` on the
  two circles at `c` (`TauCeti.PDCode.resolutionSplitMap_resolutionMergeMap`), which is `X_p + X_q`;
* when one circle of the state passes through `c`, the composite is `m ∘ Δ = 2 • X` on that circle
  (`TauCeti.PDCode.resolutionMergeMap_resolutionSplitMap`), which again equals `X_p + X_q` because
  `p` and `q` lie on that same circle.

Hence `d ≫ H + H ≫ d = X_p + X_q`, so `X_p` is chain homotopic to `-X_q` and sliding a mark across
one crossing negates the induced `X` action on Khovanov cohomology
(`TauCeti.OrientedPDCode.homologyMap_khovanovComplexMarkX_oppositeCrossingSlot`). Moreover `H`
satisfies `H² = 0` (since its image is supported on `c ∉ S`) and intertwines the opposite-strand
actions via `X_p ≫ H = H ≫ X_q` (in operator notation, `H ∘ X_p = X_q ∘ H`, from
`TauCeti.PDCode.resolutionEdgeMap_circleX_oppositeCrossingSlot`): every edge in `H` changes `c`, so
one of its two endpoints has a single circle at `c` where `p` and `q` coincide, whereas the
differential `d` also contains edges at `a ≠ c` that need not identify `p` and `q`.

## Main definitions

* `TauCeti.PDCode.resolutionCubeReverseSaddle`: the reverse saddle along `c` from vertex
  `insert c S` in quantum degree `j` to vertex `S` in quantum degree `j - 2`.
* `TauCeti.OrientedPDCode.khovanovComplexMarkSlideHom`: the signed reverse-saddle homotopy
  components `H` of cochain degree `-1` and quantum degree `-2` on `khovanovComplex`.
* `TauCeti.OrientedPDCode.khovanovComplexMarkSlideHomotopyZero`,
  `TauCeti.OrientedPDCode.khovanovComplexMarkSlideHomotopyNeg`: the chain homotopies
  `X_p + X_q ≃ 0` and `X_p ≃ -X_q`.

## Main results

* `TauCeti.PDCode.isCubeReverseEdgeCompatible_resolutionCubeReverseSaddle`: the reverse saddle at
  `c` commutes with all unaffected cube edges `a ≠ c`.
* `TauCeti.PDCode.resolutionCube_map_comp_resolutionCubeReverseSaddle`,
  `TauCeti.PDCode.resolutionCubeReverseSaddle_comp_resolutionCube_map`: the forward-then-reverse and
  reverse-then-forward composites along `c` equal `X_p + X_q`.
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

open CategoryTheory Limits Finset

namespace TauCeti.PDCode

universe u

variable {n : ℕ}

/-! ### Reverse-saddle morphisms on the Khovanov cube of resolutions -/

section Cube

variable (D : PDCode n) (c : Fin n) (hD : D.IsPlanar) (R : Type u) [CommRing R] {j j' j'' : ℤ}

private theorem resolutionEdgeMap_insert_mem_piece (hj : j' = j - 2) {S : Finset (Fin n)}
    (hc : c ∉ S)
    {x : Khovanov.CircleTensor R (D.ResolvedCircle (cubeState (insert c S)))}
    (hx : x ∈ (Khovanov.circleQuantumGrading R
      (D.ResolvedCircle (cubeState (insert c S)))).piece (j - #(insert c S))) :
    D.resolutionEdgeMap cubeState_insert_eq_of_ne (cubeState_insert_ne hc)
        (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two cubeState_insert_eq_of_ne
          (cubeState_insert_ne hc)) R x ∈
      (Khovanov.circleQuantumGrading R (D.ResolvedCircle (cubeState S))).piece (j' - #S) := by
  convert (D.isHomogeneous_resolutionEdgeMap cubeState_insert_eq_of_ne (cubeState_insert_ne hc)
    (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two cubeState_insert_eq_of_ne
      (cubeState_insert_ne hc)) R).map_mem hx using 2
  rw [card_insert_of_notMem hc, Nat.cast_succ]
  omega

/-- **The reverse saddle along `c` on the Khovanov cube of resolutions**, mapping the vertex
`insert c S` (`c ∉ S`) in quantum degree `j` to the vertex `S` in quantum degree `j' = j - 2`.
Because removing `c` lowers the cube height by `1` while the saddle map has circle-tensor quantum
degree `-1`, the net shift in `j` is `-2`. -/
def resolutionCubeReverseSaddle (hj : j' = j - 2) (S : Finset (Fin n)) (hc : c ∉ S) :
    (D.resolutionCube hD R j).obj (insert c S) ⟶ (D.resolutionCube hD R j').obj S :=
  -- `resolutionCube` is not `@[expose]`, so `resolutionCubeVertexEquiv` identifies each vertex
  -- with its graded submodule for `LinearMap.restrict`.
  ModuleCat.ofHom <|
    (D.resolutionCubeVertexEquiv hD R j' S).symm.toLinearMap ∘ₗ
      ((D.resolutionEdgeMap cubeState_insert_eq_of_ne (cubeState_insert_ne hc)
          (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two cubeState_insert_eq_of_ne
            (cubeState_insert_ne hc)) R).restrict
        (fun _ hx ↦ D.resolutionEdgeMap_insert_mem_piece c hD R hj hc hx)) ∘ₗ
      (D.resolutionCubeVertexEquiv hD R j (insert c S)).toLinearMap

/-- Under the vertex inclusions `resolutionCubeι`, `resolutionCubeReverseSaddle` acts by the saddle
map from `cubeState (insert c S)` back to `cubeState S`. -/
@[reassoc]
theorem resolutionCubeReverseSaddle_comp_resolutionCubeι (hj : j' = j - 2) (S : Finset (Fin n))
    (hc : c ∉ S) :
    D.resolutionCubeReverseSaddle c hD R hj S hc ≫ D.resolutionCubeι hD R j' S =
      D.resolutionCubeι hD R j (insert c S) ≫
        ModuleCat.ofHom (D.resolutionEdgeMap cubeState_insert_eq_of_ne (cubeState_insert_ne hc)
          (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two cubeState_insert_eq_of_ne
            (cubeState_insert_ne hc)) R) := by
  ext x
  simp only [resolutionCubeReverseSaddle, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearMap.comp_apply, LinearEquiv.coe_coe]
  change D.resolutionCubeι hD R j' S _ = _
  rw [← coe_resolutionCubeVertexEquiv, LinearEquiv.apply_symm_apply, LinearMap.restrict_apply,
    Subtype.coe_mk, coe_resolutionCubeVertexEquiv]

/-- **The reverse saddle at `c` commutes with all unaffected cube edges `a ≠ c`.** Each mixed square
consists of four saddle edges between states differing at `c` and `a`, which commute by
`TauCeti.PDCode.resolutionEdgeMap_comp_resolutionEdgeMap_comm`. -/
theorem isCubeReverseEdgeCompatible_resolutionCubeReverseSaddle (hj : j' = j - 2) :
    Functor.IsCubeReverseEdgeCompatible (D.resolutionCube hD R j) (D.resolutionCube hD R j') c
      (D.resolutionCubeReverseSaddle c hD R hj) := by
  rw [Functor.isCubeReverseEdgeCompatible_iff]
  intro S hc a ha
  have haS : a ∉ S := fun haS ↦ ha (mem_insert_of_mem haS)
  have hc' : c ∉ insert a S := notMem_insert_of_notMem_insert_swap hc ha
  have hst₁ : ∀ i, i ≠ c → cubeState (insert c S) i = cubeState S i := cubeState_insert_eq_of_ne
  have hc₁ : cubeState (insert c S) c ≠ cubeState S c := cubeState_insert_ne hc
  have ht₁u : ∀ i, i ≠ a → cubeState S i = cubeState (insert a S) i :=
    fun i hi ↦ (cubeState_insert_eq_of_ne i hi).symm
  have hc₁' : cubeState S a ≠ cubeState (insert a S) a := (cubeState_insert_ne haS).symm
  have hst₂ : ∀ i, i ≠ a → cubeState (insert c S) i = cubeState (insert c (insert a S)) i := by
    intro i hi
    rw [insert_comm c a S]
    exact (cubeState_insert_eq_of_ne i hi).symm
  have hc₂ : cubeState (insert c S) a ≠ cubeState (insert c (insert a S)) a := by
    rw [insert_comm c a S]
    exact (cubeState_insert_ne ha).symm
  have ht₂u : ∀ i, i ≠ c → cubeState (insert c (insert a S)) i = cubeState (insert a S) i :=
    cubeState_insert_eq_of_ne
  have hc₂' : cubeState (insert c (insert a S)) c ≠ cubeState (insert a S) c :=
    cubeState_insert_ne hc'
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
  have hst : ∀ i, i ≠ c → cubeState S i = cubeState (insert c S) i :=
    fun i hi ↦ (cubeState_insert_eq_of_ne i hi).symm
  have hc_ne : cubeState S c ≠ cubeState (insert c S) c := (cubeState_insert_ne hc).symm
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
  have hts : ∀ i, i ≠ c → cubeState (insert c S) i = cubeState S i := cubeState_insert_eq_of_ne
  have hc_ne : cubeState (insert c S) c ≠ cubeState S c := cubeState_insert_ne hc
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
@[simp]
theorem khovanovComplexMarkSlideHom_of_ne (hj : j' = j - 2) {i l : ℤ} (hil : l + 1 ≠ i) :
    D.khovanovComplexMarkSlideHom c hD R hj i l = 0 := by
  rw [khovanovComplexMarkSlideHom,
    Functor.cubeReverseEdgeHom_of_ne _ _ _ _ (by omega), zero_comp, comp_zero]

/-- On a state summand avoiding `c`, the mark-slide homotopy at `c` vanishes. -/
@[reassoc (attr := simp)]
theorem khovanovComplexι_khovanovComplexMarkSlideHom_of_notMem (hj : j' = j - 2) {i l : ℤ}
    (U : {U : Finset (Fin n) // (#U : ℤ) = i + D.negativeCrossingCount}) (hc : c ∉ U.val) :
    D.khovanovComplexι hD R j U ≫ D.khovanovComplexMarkSlideHom c hD R hj i l = 0 := by
  rw [khovanovComplexι_def, khovanovComplexMarkSlideHom, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp, Functor.ι_cubeReverseEdgeHom_of_notMem_assoc _ _ _ _ U hc,
    zero_comp]

/-- On a state summand `insert c S` (`c ∉ S`), the mark-slide homotopy at `c` applies the reverse
saddle into `S` with Koszul sign `(-1) ^ #{b ∈ S | b < c}`. -/
@[reassoc (attr := simp)]
theorem khovanovComplexι_khovanovComplexMarkSlideHom_insert (hj : j' = j - 2) {i : ℤ}
    (S : {S : Finset (Fin n) // (#S : ℤ) = i + D.negativeCrossingCount}) (hc : c ∉ S.val) :
    D.khovanovComplexι hD R j ⟨insert c S.val, by
        rw [card_insert_of_notMem hc, Nat.cast_succ, S.property]
        omega⟩ ≫
      D.khovanovComplexMarkSlideHom c hD R hj (i + 1) i =
    ((-1 : ℤ) ^ #{b ∈ S.val | b < c}) •
      (D.toPDCode.resolutionCubeReverseSaddle c hD R (by omega) S.val hc ≫
        D.khovanovComplexι hD R j' S) := by
  let F := D.toPDCode.resolutionCube hD R
    (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
  let G := D.toPDCode.resolutionCube hD R
    (j' - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
  have he : i + 1 + (D.negativeCrossingCount : ℤ) = i + D.negativeCrossingCount + 1 := by omega
  have hι :
      F.cubeComplexι (r := i + 1 + D.negativeCrossingCount) ⟨insert c S.val, by
          rw [card_insert_of_notMem hc, Nat.cast_succ, S.property]; omega⟩ =
        F.cubeComplexι (r := i + D.negativeCrossingCount + 1) ⟨insert c S.val, by
          rw [card_insert_of_notMem hc, Nat.cast_succ, S.property]⟩ ≫
          (F.cubeComplex.XIsoOfEq he.symm).hom :=
    (F.cubeComplexι_comp_XIsoOfEq_hom he.symm
      ⟨insert c S.val, by rw [card_insert_of_notMem hc, Nat.cast_succ, S.property]⟩).symm
  rw [khovanovComplexι_def, khovanovComplexMarkSlideHom, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp, hι, Category.assoc,
    Functor.XIsoOfEq_hom_comp_cubeReverseEdgeHom_assoc F G c _ he.symm,
    Functor.ι_cubeReverseEdgeHom_insert_assoc F G c _ S hc, Preadditive.zsmul_comp,
    Category.assoc, ← khovanovComplexι_def]

/-- Projecting the mark-slide homotopy at `c` onto a state containing `c` gives `0`. -/
@[reassoc (attr := simp)]
theorem khovanovComplexMarkSlideHom_khovanovComplexπ_of_mem (hj : j' = j - 2) {i l : ℤ}
    (T : {T : Finset (Fin n) // (#T : ℤ) = l + D.negativeCrossingCount}) (hc : c ∈ T.val) :
    D.khovanovComplexMarkSlideHom c hD R hj i l ≫ D.khovanovComplexπ hD R j' T = 0 := by
  rw [khovanovComplexMarkSlideHom, khovanovComplexπ_def, Category.assoc, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Functor.cubeReverseEdgeHom_π_of_mem _ _ _ _ T hc, comp_zero]

/-- Projecting the mark-slide homotopy at `c` onto a state `S` avoiding `c` gives the state
projection onto `insert c S` followed by the reverse saddle with sign `(-1) ^ #{b ∈ S | b < c}`. -/
@[reassoc (attr := simp)]
theorem khovanovComplexMarkSlideHom_khovanovComplexπ_of_notMem (hj : j' = j - 2) {i : ℤ}
    (S : {S : Finset (Fin n) // (#S : ℤ) = i + D.negativeCrossingCount}) (hc : c ∉ S.val) :
    D.khovanovComplexMarkSlideHom c hD R hj (i + 1) i ≫ D.khovanovComplexπ hD R j' S =
      ((-1 : ℤ) ^ #{b ∈ S.val | b < c}) •
        (D.khovanovComplexπ hD R j ⟨insert c S.val, by
            rw [card_insert_of_notMem hc, Nat.cast_succ, S.property]
            omega⟩ ≫
          D.toPDCode.resolutionCubeReverseSaddle c hD R (by omega) S.val hc) := by
  let F := D.toPDCode.resolutionCube hD R
    (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
  let G := D.toPDCode.resolutionCube hD R
    (j' - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
  have he : i + 1 + (D.negativeCrossingCount : ℤ) = i + D.negativeCrossingCount + 1 := by omega
  rw [khovanovComplexMarkSlideHom, khovanovComplexπ_def, Category.assoc, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    ← Functor.XIsoOfEq_hom_comp_cubeReverseEdgeHom_assoc F G c _ he,
    Functor.cubeReverseEdgeHom_π_of_notMem F G c _ S hc, Preadditive.comp_zsmul,
    Preadditive.comp_zsmul, F.XIsoOfEq_hom_comp_cubeComplexπ_assoc he, ← Category.assoc,
    ← khovanovComplexπ_def]

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
  rw [D.khovanovComplexMarkX_f _ hD R hj, D.khovanovComplexMarkX_f _ hD R hj',
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
  rw [D.khovanovComplexMarkX_f _ hD R hj, D.khovanovComplexMarkX_f _ hD R hj',
    khovanovComplexMarkSlideHom, khovanovComplexMarkSlideHom]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [Functor.cubeComplexMap_f_comp_cubeReverseEdgeHom_assoc _ _ _ _ _ fun S hc ↦
    D.toPDCode.resolutionCubeMarkX_app_comp_resolutionCubeReverseSaddle c hD R r
      (j := j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
      (j' := j' - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
      (j'' := j'' - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
      (by omega) (by omega) S hc]

/-- Transporting `d ≫ H + H ≫ d` on the normalized Khovanov complex across `khovanovComplex_X`
identifies it with `dNext + prevD` of `Functor.cubeReverseEdgeHom` at height `i + n₋`. -/
private theorem d_comp_khovanovComplexMarkSlideHom_add_comp_d_eq (hj : j' = j - 2) (i : ℤ) :
    (D.khovanovComplex hD R j).d i (i + 1) ≫
        D.khovanovComplexMarkSlideHom c hD R hj (i + 1) i +
      D.khovanovComplexMarkSlideHom c hD R hj i (i - 1) ≫
        (D.khovanovComplex hD R j').d (i - 1) i =
      eqToHom (D.khovanovComplex_X hD R j i) ≫
        (dNext (i + D.negativeCrossingCount)
          (Functor.cubeReverseEdgeHom
            (D.toPDCode.resolutionCube hD R
              (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount))
            (D.toPDCode.resolutionCube hD R
              (j' - D.positiveCrossingCount + 2 * D.negativeCrossingCount))
            c (D.toPDCode.resolutionCubeReverseSaddle c hD R (by omega))) +
        prevD (i + D.negativeCrossingCount)
          (Functor.cubeReverseEdgeHom
            (D.toPDCode.resolutionCube hD R
              (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount))
            (D.toPDCode.resolutionCube hD R
              (j' - D.positiveCrossingCount + 2 * D.negativeCrossingCount))
            c (D.toPDCode.resolutionCubeReverseSaddle c hD R (by omega)))) ≫
        eqToHom (D.khovanovComplex_X hD R j' i).symm := by
  have hrel_next : (ComplexShape.up ℤ).Rel (i + D.negativeCrossingCount)
      (i + 1 + D.negativeCrossingCount) := by
    simp only [ComplexShape.up_Rel]
    omega
  have hrel_prev : (ComplexShape.up ℤ).Rel (i - 1 + D.negativeCrossingCount)
      (i + D.negativeCrossingCount) := by
    simp only [ComplexShape.up_Rel]
    omega
  rw [D.khovanovComplex_d hD R j i (i + 1), D.khovanovComplex_d hD R j' (i - 1) i,
    khovanovComplexMarkSlideHom, khovanovComplexMarkSlideHom, dNext_eq _ hrel_next,
    prevD_eq _ hrel_prev]
  simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]

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
  have hcube := (Functor.cubeReverseEdgeHomotopyZero c
    (D.toPDCode.resolutionCubeReverseSaddle c hD R
      (j := j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
      (j' := j' - D.positiveCrossingCount + 2 * D.negativeCrossingCount) (by omega))
    (D.toPDCode.isCubeReverseEdgeCompatible_resolutionCubeReverseSaddle c hD R (by omega))
    (D.toPDCode.resolutionCubeMarkX
        (PDCode.Mark.onArc D.toPDCode (D.toPDCode.crossing c k)) hD R (by omega) +
      D.toPDCode.resolutionCubeMarkX
        (PDCode.Mark.onArc D.toPDCode (D.toPDCode.crossing c (PDCode.oppositeCrossingSlot k)))
        hD R (by omega))
    (fun S hc ↦ (D.toPDCode.resolutionCube_map_comp_resolutionCubeReverseSaddle c hD R k
      (by omega) S hc).symm)
    (fun S hc ↦ (D.toPDCode.resolutionCubeReverseSaddle_comp_resolutionCube_map c hD R k
      (by omega) S hc).symm)).comm (i + D.negativeCrossingCount)
  rw [funext₂ (Functor.cubeReverseEdgeHomotopyZero_hom _ _ _ _ _ _),
    HomologicalComplex.zero_f, add_zero] at hcube
  rw [D.d_comp_khovanovComplexMarkSlideHom_add_comp_d_eq c hD R hj i, ← hcube,
    NatTrans.cubeComplexMap_add, HomologicalComplex.add_f_apply, Preadditive.add_comp,
    Preadditive.comp_add, ← D.khovanovComplexMarkX_f, ← D.khovanovComplexMarkX_f]

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
        hD R hj) :=
  Homotopy.equivSubZero.symm <|
    (Homotopy.ofEq (sub_neg_eq_add _ _)).trans
      (D.khovanovComplexMarkSlideHomotopyZero c hD R k hj)

/-- The components of `khovanovComplexMarkSlideHomotopyNeg` are `khovanovComplexMarkSlideHom`. -/
@[simp]
theorem khovanovComplexMarkSlideHomotopyNeg_hom (k : Fin 4) (hj : j' = j - 2) (i l : ℤ) :
    (D.khovanovComplexMarkSlideHomotopyNeg c hD R k hj).hom i l =
      D.khovanovComplexMarkSlideHom c hD R hj i l := by
  -- `Homotopy.equivSubZero` (`@[expose]`, no `@[simps]`) preserves `.hom` definitionally.
  rw [khovanovComplexMarkSlideHomotopyNeg]
  change ((Homotopy.ofEq (sub_neg_eq_add _ _)).trans
    (D.khovanovComplexMarkSlideHomotopyZero c hD R k hj)).hom i l = _
  rw [Homotopy.trans_hom, Homotopy.ofEq_hom, Pi.zero_apply, Pi.zero_apply, zero_add,
    khovanovComplexMarkSlideHomotopyZero_hom]

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
