/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.Complex
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Mark

/-!
# The `X` action at a mark

A mark `p` on a PD-code, on an arc or on a labelled crossing-free circle, selects in every
complete smoothing `s` the resolved circle `p.resolvedCircle s` through it. Multiplying the
factor of that circle by `X` is the endomorphism `TauCeti.Khovanov.circleX` of the circle tensor,
of quantum degree `-2` and with square zero.

The saddle correspondence of an edge of the cube carries the circle through `p` to the circle
through `p`. Hence the action commutes with every merge and every split
(`TauCeti.PDCode.resolutionEdgeMap_circleX`): for a merge because the merge is multiplicative,
and for a split by the Frobenius projection formula `Δ(m(a) z) = a Δ(z)`.

Consequently the action at `p` is a map of cubes of resolutions
`TauCeti.PDCode.resolutionCubeMarkX` from quantum degree `j` to quantum degree `j - 2`, and a
cochain map `TauCeti.OrientedPDCode.khovanovComplexMarkX` of bidegree `(0, -2)` on the normalized
Khovanov complex. Both square to zero. This is Khovanov's action of a marked circle, from which
the reduced complex of a marked diagram is formed.

## References

* M. Khovanov, *Patterns in knot cohomology I*, Experiment. Math. 12 (2003), §3.
-/

public section

noncomputable section

open CategoryTheory Finset

namespace TauCeti.PDCode

universe u

variable {n : ℕ} (D : PDCode n) (p : D.Mark)

section Saddle

variable {s t : Fin n → Bool} {c : Fin n} (hst : ∀ j, j ≠ c → s j = t j) (hc : s c ≠ t c)
  (R : Type u) [CommSemiring R]

/-- A resolution merge carries `X` on the circle through a mark to `X` on the circle through the
same mark. -/
theorem resolutionMergeMap_circleX (hs : #(D.circlesAt s c) = 2)
    (x : Khovanov.CircleTensor R (D.ResolvedCircle s)) :
    D.resolutionMergeMap hst hc hs R (Khovanov.circleX R (p.resolvedCircle s) x) =
      Khovanov.circleX R (p.resolvedCircle t) (D.resolutionMergeMap hst hc hs R x) := by
  rw [resolutionMergeMap_def, Khovanov.fiberwiseMul_circleX,
    Mark.saddleResolvedCircleMap_resolvedCircle]

/-- A resolution split carries `X` on the circle through a mark to `X` on the circle through the
same mark. -/
theorem resolutionSplitMap_circleX (ht : #(D.circlesAt t c) = 2)
    (x : Khovanov.CircleTensor R (D.ResolvedCircle s)) :
    D.resolutionSplitMap hst hc ht R (Khovanov.circleX R (p.resolvedCircle s) x) =
      Khovanov.circleX R (p.resolvedCircle t) (D.resolutionSplitMap hst hc ht R x) := by
  have hts : ∀ j, j ≠ c → t j = s j := fun j hj ↦ (hst j hj).symm
  rw [resolutionSplitMap_def, ← Mark.saddleResolvedCircleMap_resolvedCircle p hts
    (D.card_circlesAt_eq_one_of_card_circlesAt_eq_two hts hc.symm ht),
    Khovanov.fiberwiseSplit_circleX]

/-- **The `X` action at a mark commutes with every saddle.** Along an edge of the cube that
merges two circles or splits one, `X` on the circle through `p` before the saddle is `X` on the
circle through `p` after it. -/
theorem resolutionEdgeMap_circleX (h : #(D.circlesAt s c) = 2 ∨ #(D.circlesAt t c) = 2)
    (x : Khovanov.CircleTensor R (D.ResolvedCircle s)) :
    D.resolutionEdgeMap hst hc h R (Khovanov.circleX R (p.resolvedCircle s) x) =
      Khovanov.circleX R (p.resolvedCircle t) (D.resolutionEdgeMap hst hc h R x) := by
  by_cases hs : #(D.circlesAt s c) = 2
  · rw [D.resolutionEdgeMap_eq_resolutionMergeMap hst hc h R hs, AlgHom.toLinearMap_apply,
      AlgHom.toLinearMap_apply]
    exact D.resolutionMergeMap_circleX p hst hc R hs x
  · rw [D.resolutionEdgeMap_eq_resolutionSplitMap hst hc h R (h.resolve_left hs)]
    exact D.resolutionSplitMap_circleX p hst hc R (h.resolve_left hs) x

end Saddle

variable (hD : D.IsPlanar) (R : Type u) [CommRing R] {j j' j'' : ℤ}

/-- **The `X` action at a mark on the cube of resolutions.** On the vertex `S` it multiplies the
factor of the circle through `p` by `X`, mapping the degree-`j` cube to the degree-`j'` cube
for `j' = j - 2`. It is a map of cubes because it commutes with every saddle. -/
def resolutionCubeMarkX (hj : j' = j - 2) : D.resolutionCube hD R j ⟶ D.resolutionCube hD R j' :=
  resolutionCubeHom hD R j hD (fun s ↦ Khovanov.circleX R (p.resolvedCircle s))
    (fun s ↦ Khovanov.isHomogeneous_circleX (p.resolvedCircle s))
    (fun _ _ _ hst hc h _ x ↦ D.resolutionEdgeMap_circleX p hst hc R h x) (by omega)

/-- On the vertex `S`, the `X` action at `p` multiplies the factor of the circle through `p` in the
resolution of `S` by `X`. -/
@[reassoc]
theorem resolutionCubeMarkX_app_comp_resolutionCubeι (hj : j' = j - 2) (S : Finset (Fin n)) :
    (D.resolutionCubeMarkX p hD R hj).app S ≫ D.resolutionCubeι hD R j' S =
      D.resolutionCubeι hD R j S ≫
        ModuleCat.ofHom (Khovanov.circleX R (p.resolvedCircle (cubeState S))) :=
  resolutionCubeHom_app_comp_resolutionCubeι ..

/-- The `X` action at a mark on the cube of resolutions squares to zero. -/
@[reassoc (attr := simp)]
theorem resolutionCubeMarkX_comp_resolutionCubeMarkX (hj : j' = j - 2) (hj' : j'' = j' - 2) :
    D.resolutionCubeMarkX p hD R hj ≫ D.resolutionCubeMarkX p hD R hj' = 0 := by
  ext S : 2
  rw [NatTrans.comp_app, NatTrans.app_zero, ← cancel_mono (D.resolutionCubeι hD R j'' S),
    Category.assoc, resolutionCubeMarkX_app_comp_resolutionCubeι,
    resolutionCubeMarkX_app_comp_resolutionCubeι_assoc, Limits.zero_comp]
  ext x
  simp

end TauCeti.PDCode

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ} (D : OrientedPDCode n) (p : D.toPDCode.Mark) (hD : D.toPDCode.IsPlanar)
  (R : Type u) [CommRing R] {j j' j'' : ℤ}

/-- **The `X` chain action at a mark** on the normalized Khovanov complex, from quantum degree `j`
to quantum degree `j' = j - 2`. It is the index translation of the cochain map of signed cube
complexes induced by `TauCeti.PDCode.resolutionCubeMarkX`; on each state it multiplies the factor
of the circle through `p` by `X`. -/
def khovanovComplexMarkX (hj : j' = j - 2) :
    D.khovanovComplex hD R j ⟶ D.khovanovComplex hD R j' :=
  eqToHom (D.khovanovComplex_apply hD R j) ≫
    ((ComplexShape.embeddingUp'Add (1 : ℤ) D.negativeCrossingCount).restrictionFunctor
      (ModuleCat.{u} R)).map (NatTrans.cubeComplexMap
        (D.toPDCode.resolutionCubeMarkX p hD R (j := j - D.positiveCrossingCount +
          2 * D.negativeCrossingCount) (j' := j' - D.positiveCrossingCount +
            2 * D.negativeCrossingCount) (by omega))) ≫
    eqToHom (D.khovanovComplex_apply hD R j').symm

/-- On a state summand, the `X` chain action at `p` is the `X` action at `p` on the corresponding
vertex of the cube of resolutions. -/
@[reassoc (attr := simp)]
theorem khovanovComplexι_khovanovComplexMarkX_f (hj : j' = j - 2) {i : ℤ}
    (S : {S : Finset (Fin n) // (#S : ℤ) = i + D.negativeCrossingCount}) :
    D.khovanovComplexι hD R j S ≫ (D.khovanovComplexMarkX p hD R hj).f i =
      (D.toPDCode.resolutionCubeMarkX p hD R (by omega)).app S.val ≫
        D.khovanovComplexι hD R j' S := by
  rw [khovanovComplexMarkX, khovanovComplexι_def, khovanovComplexι_def]
  -- The restriction functor produces complexes of shape `up' 1`, which `erw` identifies with the
  -- cochain shape `up ℤ`; the embedding sends `i` to `i + n₋` by definition, so the remaining
  -- transport between these two cube terms is an identity.
  erw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f,
    HomologicalComplex.eqToHom_f, ComplexShape.Embedding.restrictionFunctor_map,
    HomologicalComplex.restrictionMap_f]
  simp only [eqToHom_trans_assoc, Category.assoc]
  erw [eqToHom_refl, Category.id_comp, NatTrans.ι_cubeComplexMap_f_assoc]

/-- Projecting the marked `X` chain action onto a state gives the marked `X` action of that
state. -/
@[reassoc (attr := simp)]
theorem khovanovComplexMarkX_f_khovanovComplexπ (hj : j' = j - 2) {i : ℤ}
    (S : {S : Finset (Fin n) // (#S : ℤ) = i + D.negativeCrossingCount}) :
    (D.khovanovComplexMarkX p hD R hj).f i ≫ D.khovanovComplexπ hD R j' S =
      D.khovanovComplexπ hD R j S ≫
        (D.toPDCode.resolutionCubeMarkX p hD R (by omega)).app S.val := by
  refine D.khovanovComplex_hom_ext hD R j fun T ↦ ?_
  by_cases h : T = S
  · subst h
    simp
  · simp [h]

/-- The `X` chain action at a mark squares to zero. -/
@[reassoc (attr := simp)]
theorem khovanovComplexMarkX_comp_khovanovComplexMarkX (hj : j' = j - 2) (hj' : j'' = j' - 2) :
    D.khovanovComplexMarkX p hD R hj ≫ D.khovanovComplexMarkX p hD R hj' = 0 := by
  ext i : 1
  refine D.khovanovComplex_hom_ext hD R j fun S ↦ ?_
  rw [HomologicalComplex.comp_f, khovanovComplexι_khovanovComplexMarkX_f_assoc,
    khovanovComplexι_khovanovComplexMarkX_f, ← NatTrans.comp_app_assoc,
    PDCode.resolutionCubeMarkX_comp_resolutionCubeMarkX, NatTrans.app_zero, Limits.zero_comp,
    HomologicalComplex.zero_f, Limits.comp_zero]

end TauCeti.OrientedPDCode
