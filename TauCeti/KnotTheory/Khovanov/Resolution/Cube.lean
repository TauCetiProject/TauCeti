/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.GradedObject
public import TauCeti.Algebra.Homology.Cube.Basic
public import TauCeti.CategoryTheory.Functor.OfCubeEdges
public import TauCeti.KnotTheory.Khovanov.Resolution.Edge
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Planar

/-!
# The Khovanov cube of resolutions of a planar code

The vertices of the cube of resolutions of a PD-code `D` with `n` crossings are the subsets
`S ⊆ Fin n`, where `S` is the set of crossings given the `B`-smoothing; the corresponding native
state `TauCeti.PDCode.cubeState S` is `false` exactly on `S`. The edge from `S` to `S ∪ {a}`
changes the smoothing at the crossing `a`. When `D` is planar, every such edge merges two circles
or splits one, so it carries the saddle map `TauCeti.PDCode.resolutionEdgeMap` between the
resolved-circle tensors, of quantum degree `-1`, and every square face of saddle maps commutes.

Shifting the vertex `S` by its height `|S|`, the vertex `V(S)⟨|S|⟩` in quantum degree `j` is the
homogeneous piece of degree `j - |S|` of the circle tensor of `S`. Along each edge the height
grows by one, which compensates the quantum degree `-1` of the saddle map, so for each quantum
degree `j` the degree-`j` pieces form a commutative cube of `R`-modules,
`TauCeti.PDCode.resolutionCube`. Its signed totalization is the degree-`j` component of the
unnormalized Khovanov complex, Bar-Natan's bracket `⟦D⟧`, whose term in cochain degree `r` is
`⊕[|S| = r] V(S)⟨r⟩`. The family of these cochain complexes, indexed by the quantum degree, is
`TauCeti.PDCode.khovanovBracket`. The normalized Khovanov complex of an oriented code with `n₊`
positive and `n₋` negative crossings is obtained from it by lowering the cochain degree by `n₋`
and raising the quantum degree by `n₊ - 2n₋`.

## Main definitions

All in the namespace `TauCeti.PDCode`:

* `cubeState S`: the state with the `B`-smoothing exactly at the crossings of `S`.
* `resolutionCube D hD R j`: the degree-`j` quantum component of the cube of resolutions of the
  planar code `D`, a functor `Finset (Fin n) ⥤ ModuleCat R`.
* `khovanovBracket D hD R`: the unnormalized Khovanov complex, as a graded object of cochain
  complexes indexed by the quantum degree.

## Main results

* `resolutionCube_obj`, `range_resolutionCubeι`: the vertex `S` in quantum degree `j` is the
  degree `j - |S|` piece of the circle tensor of the resolution of `S`, included by
  `resolutionCubeι`.
* `resolutionCube_map_homOfLE_insert_comp_resolutionCubeι`: along the edge from `S` to
  `S ∪ {a}` the cube acts by the saddle map at the crossing `a`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §2.2.
-/

public section

noncomputable section

open CategoryTheory Finset

namespace TauCeti.PDCode

universe u

variable {n : ℕ}

/-! ### The states of the vertices -/

/-- The state of the vertex `S` of the cube of resolutions: it selects the `B`-smoothing
(`false`) exactly at the crossings of `S`, and the `A`-smoothing (`true`) at the others. -/
def cubeState (S : Finset (Fin n)) : Fin n → Bool :=
  fun i ↦ decide (i ∉ S)

/-- The defining formula of the state of a vertex. -/
theorem cubeState_apply (S : Finset (Fin n)) (i : Fin n) : cubeState S i = decide (i ∉ S) :=
  (rfl)

/-- The state of the vertex `S` selects the `B`-smoothing exactly at the crossings of `S`. -/
@[simp]
theorem cubeState_eq_false_iff {S : Finset (Fin n)} {i : Fin n} :
    cubeState S i = false ↔ i ∈ S := by
  simp [cubeState]

/-- The state of the vertex `S` selects the `A`-smoothing exactly away from `S`. -/
@[simp]
theorem cubeState_eq_true_iff {S : Finset (Fin n)} {i : Fin n} :
    cubeState S i = true ↔ i ∉ S := by
  simp [cubeState]

/-- The set of `B`-smoothings of the state of the vertex `S` is `S`. -/
theorem filter_cubeState_eq_false (S : Finset (Fin n)) :
    ({i | cubeState S i = false} : Finset (Fin n)) = S := by
  ext
  simp

/-- The vertex `S` is recovered from its state. -/
theorem cubeState_injective : Function.Injective (cubeState (n := n)) := fun S T h ↦ by
  rw [← filter_cubeState_eq_false S, ← filter_cubeState_eq_false T, h]

/-- Along an edge `S ⋖ T` of the cube, the states of `S` and `T` agree away from the added
crossing `a ∈ T \ S`. -/
theorem cubeState_eq_of_covBy {S T : Finset (Fin n)} (h : S ⋖ T) {a : Fin n} (haS : a ∉ S)
    (haT : a ∈ T) (j : Fin n) (hj : j ≠ a) : cubeState S j = cubeState T j := by
  obtain ⟨b, hbS, rfl⟩ := h.exists_finset_insert
  obtain rfl : a = b := (mem_insert.mp haT).resolve_right haS
  simp [cubeState, hj]

/-- Along an edge `S ⋖ T` of the cube, the states of `S` and `T` differ at the added crossing
`a ∈ T \ S`. -/
theorem cubeState_ne_of_notMem_of_mem {S T : Finset (Fin n)} {a : Fin n} (haS : a ∉ S)
    (haT : a ∈ T) : cubeState S a ≠ cubeState T a := by
  simp [cubeState, haS, haT]

/-! ### The cube of resolutions -/

/-- The crossing added along an edge `S ⋖ T` of the cube. -/
private def edgeCrossing {S T : Finset (Fin n)} (h : S ⋖ T) : Fin n :=
  h.exists_finset_insert.choose

private theorem edgeCrossing_notMem {S T : Finset (Fin n)} (h : S ⋖ T) : edgeCrossing h ∉ S :=
  h.exists_finset_insert.choose_spec.1

private theorem insert_edgeCrossing {S T : Finset (Fin n)} (h : S ⋖ T) :
    insert (edgeCrossing h) S = T :=
  h.exists_finset_insert.choose_spec.2

private theorem edgeCrossing_mem {S T : Finset (Fin n)} (h : S ⋖ T) : edgeCrossing h ∈ T :=
  (insert_edgeCrossing h).subset (mem_insert_self _ _)

/-- The crossing added along an edge is the unique element of `T \ S`. -/
private theorem edgeCrossing_eq {S T : Finset (Fin n)} (h : S ⋖ T) {a : Fin n} (haS : a ∉ S)
    (haT : a ∈ T) : edgeCrossing h = a := by
  rw [← insert_edgeCrossing h] at haT
  exact ((mem_insert.mp haT).resolve_right haS).symm

variable (D : PDCode n) (hD : D.IsPlanar) (R : Type u) [CommRing R] (j : ℤ)

/-- The vertex `S` of the degree-`j` cube: the homogeneous piece of degree `j - |S|` of the
circle tensor of the resolution of `S`, that is, the degree-`j` piece of `V(S)⟨|S|⟩`. -/
private abbrev resolutionCubeVertex (S : Finset (Fin n)) : ModuleCat.{u} R :=
  ModuleCat.of R ((Khovanov.circleQuantumGrading R (D.ResolvedCircle (cubeState S))).piece
    (j - #S))

/-- The saddle map along the edge from `cubeState S` to `cubeState T`, for `S ⋖ T`. -/
private abbrev resolutionCubeEdgeMap {S T : Finset (Fin n)} (h : S ⋖ T) :
    Khovanov.CircleTensor R (D.ResolvedCircle (cubeState S)) →ₗ[R]
      Khovanov.CircleTensor R (D.ResolvedCircle (cubeState T)) :=
  D.resolutionEdgeMap (cubeState_eq_of_covBy h (edgeCrossing_notMem h) (edgeCrossing_mem h))
    (cubeState_ne_of_notMem_of_mem (edgeCrossing_notMem h) (edgeCrossing_mem h))
    (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two
      (cubeState_eq_of_covBy h (edgeCrossing_notMem h) (edgeCrossing_mem h))
      (cubeState_ne_of_notMem_of_mem (edgeCrossing_notMem h) (edgeCrossing_mem h))) R

/-- The saddle map along an edge `S ⋖ T` is the resolution edge map at any crossing `a ∈ T \ S`;
the crossing is determined by the edge. -/
private theorem resolutionCubeEdgeMap_eq {S T : Finset (Fin n)} (h : S ⋖ T) {a : Fin n}
    (haS : a ∉ S) (haT : a ∈ T) :
    resolutionCubeEdgeMap D hD R h =
      D.resolutionEdgeMap (cubeState_eq_of_covBy h haS haT) (cubeState_ne_of_notMem_of_mem haS haT)
        (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two (cubeState_eq_of_covBy h haS haT)
          (cubeState_ne_of_notMem_of_mem haS haT)) R := by
  obtain rfl := edgeCrossing_eq h haS haT
  rfl

/-- The saddle map along an edge `S ⋖ T` lowers the quantum degree by one while the height grows
by one, so it maps the degree-`j` piece of `V(S)⟨|S|⟩` to that of `V(T)⟨|T|⟩`. -/
private theorem resolutionCubeEdgeMap_mem {S T : Finset (Fin n)} (h : S ⋖ T) (x)
    (hx : x ∈ (Khovanov.circleQuantumGrading R (D.ResolvedCircle (cubeState S))).piece
      (j - #S)) :
    resolutionCubeEdgeMap D hD R h x ∈
      (Khovanov.circleQuantumGrading R (D.ResolvedCircle (cubeState T))).piece (j - #T) := by
  have hT : (#T : ℤ) = #S + 1 := by
    rw [← insert_edgeCrossing h, card_insert_of_notMem (edgeCrossing_notMem h), Nat.cast_succ]
  have hx' : resolutionCubeEdgeMap D hD R h x ∈
      (Khovanov.circleQuantumGrading R (D.ResolvedCircle (cubeState T))).piece (j - #S + -1) :=
    (D.isHomogeneous_resolutionEdgeMap _ _ _ R).map_mem hx
  convert hx' using 2
  omega

/-- The saddle map along an edge `S ⋖ T`, as a map between the vertices of the degree-`j`
cube. -/
private def resolutionCubeEdge {S T : Finset (Fin n)} (h : S ⋖ T) :
    resolutionCubeVertex D R j S ⟶ resolutionCubeVertex D R j T :=
  ModuleCat.ofHom ((resolutionCubeEdgeMap D hD R h).restrict
    (resolutionCubeEdgeMap_mem D hD R j h))

/-- The square faces of saddle maps of a planar code commute. -/
private theorem resolutionCubeEdge_comp_resolutionCubeEdge {S T₁ T₂ U : Finset (Fin n)}
    (h₁ : S ⋖ T₁) (h₁' : T₁ ⋖ U) (h₂ : S ⋖ T₂) (h₂' : T₂ ⋖ U) :
    resolutionCubeEdge D hD R j h₁ ≫ resolutionCubeEdge D hD R j h₁' =
      resolutionCubeEdge D hD R j h₂ ≫ resolutionCubeEdge D hD R j h₂' := by
  obtain rfl | hT := eq_or_ne T₁ T₂
  · rfl
  -- The face adds the crossing `c` of the first route and the crossing `c'` of the second.
  set c := edgeCrossing h₁
  set c' := edgeCrossing h₂
  have hcS : c ∉ S := edgeCrossing_notMem h₁
  have hc'S : c' ∉ S := edgeCrossing_notMem h₂
  have hT₁ : insert c S = T₁ := insert_edgeCrossing h₁
  have hT₂ : insert c' S = T₂ := insert_edgeCrossing h₂
  have hcc' : c ≠ c' := by
    rintro hcc'
    exact hT (hT₁.symm.trans (hcc' ▸ hT₂))
  have hcT₂ : c ∉ T₂ := by simp [← hT₂, hcc', hcS]
  have hc'T₁ : c' ∉ T₁ := by simp [← hT₁, hcc'.symm, hc'S]
  have hcU : c ∈ U := h₁'.le (edgeCrossing_mem h₁)
  have hc'U : c' ∈ U := h₂'.le (edgeCrossing_mem h₂)
  have e₁ := cubeState_eq_of_covBy h₁ hcS (edgeCrossing_mem h₁)
  have n₁ := cubeState_ne_of_notMem_of_mem hcS (edgeCrossing_mem h₁)
  have e₁' := cubeState_eq_of_covBy h₁' hc'T₁ hc'U
  have n₁' := cubeState_ne_of_notMem_of_mem hc'T₁ hc'U
  have e₂ := cubeState_eq_of_covBy h₂ hc'S (edgeCrossing_mem h₂)
  have n₂ := cubeState_ne_of_notMem_of_mem hc'S (edgeCrossing_mem h₂)
  have e₂' := cubeState_eq_of_covBy h₂' hcT₂ hcU
  have n₂' := cubeState_ne_of_notMem_of_mem hcT₂ hcU
  have hface := D.resolutionEdgeMap_comp_resolutionEdgeMap_comm e₁ n₁ e₁' n₁' e₂ n₂ e₂' n₂'
    (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two e₁ n₁)
    (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two e₁' n₁')
    (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two e₂ n₂)
    (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two e₂' n₂') R
  -- After unfolding the restricted edge maps, this is the face relation `hface` at the crossings
  -- `c` and `c'`, applied to the underlying element of `x`.
  ext x
  simpa [resolutionCubeEdge, resolutionCubeEdgeMap_eq D hD R h₁' hc'T₁ hc'U,
    resolutionCubeEdgeMap_eq D hD R h₂' hcT₂ hcU] using LinearMap.congr_fun hface x.1

/-- **The Khovanov cube of resolutions** of a planar code `D`, in quantum degree `j`. Its vertex
`S` is the homogeneous piece of degree `j - |S|` of the circle tensor of the resolution
`cubeState S`, the degree-`j` piece of `V(S)⟨|S|⟩`, and along the edge from `S` to `S ∪ {a}` it
acts by the saddle map at the crossing `a`, merging two circles or splitting one. -/
def resolutionCube : Finset (Fin n) ⥤ ModuleCat.{u} R :=
  Functor.ofCubeEdges (X := resolutionCubeVertex D R j)
    (fun _ _ h ↦ resolutionCubeEdge D hD R j h)
    (fun _ _ _ _ h₁ h₁' h₂ h₂' ↦ resolutionCubeEdge_comp_resolutionCubeEdge D hD R j h₁ h₁' h₂ h₂')

/-- The vertex `S` of the degree-`j` cube of resolutions is the piece of degree `j - |S|` of the
circle tensor of the resolution of `S`. -/
theorem resolutionCube_obj (S : Finset (Fin n)) :
    (D.resolutionCube hD R j).obj S =
      ModuleCat.of R ((Khovanov.circleQuantumGrading R (D.ResolvedCircle (cubeState S))).piece
        (j - #S)) :=
  (rfl)

/-- The inclusion of the vertex `S` of the degree-`j` cube of resolutions into the circle tensor
of the resolution of `S`. -/
def resolutionCubeι (S : Finset (Fin n)) : (D.resolutionCube hD R j).obj S ⟶
    ModuleCat.of R (Khovanov.CircleTensor R (D.ResolvedCircle (cubeState S))) :=
  ModuleCat.ofHom (Submodule.subtype _)

/-- The inclusion of a vertex of the cube of resolutions is injective. -/
theorem resolutionCubeι_injective (S : Finset (Fin n)) :
    Function.Injective (D.resolutionCubeι hD R j S).hom :=
  Subtype.val_injective

/-- The image of the vertex `S` of the degree-`j` cube of resolutions is the piece of degree
`j - |S|` of the circle tensor of the resolution of `S`. -/
@[simp]
theorem range_resolutionCubeι (S : Finset (Fin n)) :
    LinearMap.range (D.resolutionCubeι hD R j S).hom =
      (Khovanov.circleQuantumGrading R (D.ResolvedCircle (cubeState S))).piece (j - #S) :=
  Submodule.range_subtype _

instance (S : Finset (Fin n)) : Mono (D.resolutionCubeι hD R j S) :=
  (ModuleCat.mono_iff_injective _).mpr (D.resolutionCubeι_injective hD R j S)

private theorem resolutionCube_map_homOfLE_insert {S : Finset (Fin n)} {a : Fin n} (ha : a ∉ S) :
    (D.resolutionCube hD R j).map (homOfLE (subset_insert a S)) =
      resolutionCubeEdge D hD R j (covBy_insert ha) :=
  Functor.ofCubeEdges_map_homOfLE_insert _ _ ha

/-- Along the edge from `S` to `S ∪ {a}`, the cube of resolutions acts by the saddle map
`TauCeti.PDCode.resolutionEdgeMap` at the crossing `a`: it merges the two circles through `a` or
splits the circle through `a`. -/
@[reassoc]
theorem resolutionCube_map_homOfLE_insert_comp_resolutionCubeι {S : Finset (Fin n)} {a : Fin n}
    (ha : a ∉ S) :
    (D.resolutionCube hD R j).map (homOfLE (subset_insert a S)) ≫
        D.resolutionCubeι hD R j (insert a S) =
      D.resolutionCubeι hD R j S ≫ ModuleCat.ofHom
        (D.resolutionEdgeMap (cubeState_eq_of_covBy (covBy_insert ha) ha (mem_insert_self a S))
          (cubeState_ne_of_notMem_of_mem ha (mem_insert_self a S))
          (hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two
            (cubeState_eq_of_covBy (covBy_insert ha) ha (mem_insert_self a S))
            (cubeState_ne_of_notMem_of_mem ha (mem_insert_self a S))) R) := by
  rw [resolutionCube_map_homOfLE_insert D hD R j ha]
  ext x
  -- Both sides apply a saddle map to the underlying element of `x`: on the left the edge map at
  -- the chosen crossing of the edge, restricted to the homogeneous pieces, and on the right the
  -- one at `a`.
  exact LinearMap.congr_fun
    (resolutionCubeEdgeMap_eq D hD R (covBy_insert ha) ha (mem_insert_self a S)) x.1

/-! ### The unnormalized Khovanov complex -/

/-- **The unnormalized Khovanov complex** of a planar code `D`, Bar-Natan's bracket `⟦D⟧`, as a
family of cochain complexes indexed by the quantum degree. Its degree-`j` component is the signed
totalization of the degree-`j` cube of resolutions: in cochain degree `r` it is the biproduct of
the degree-`j` pieces of `V(S)⟨r⟩` over the subsets `S` with `|S| = r`, and its differential is
the sum of the saddle maps along the edges from `S` to `S ∪ {a}`, with sign `(-1)` to the number of
crossings of `S` below `a`. -/
def khovanovBracket : GradedObject ℤ (CochainComplex (ModuleCat.{u} R) ℤ) :=
  fun j ↦ (D.resolutionCube hD R j).cubeComplex

/-- The degree-`j` component of the unnormalized Khovanov complex is the signed totalization of
the degree-`j` cube of resolutions. -/
theorem khovanovBracket_apply : D.khovanovBracket hD R j = (D.resolutionCube hD R j).cubeComplex :=
  (rfl)

end TauCeti.PDCode
