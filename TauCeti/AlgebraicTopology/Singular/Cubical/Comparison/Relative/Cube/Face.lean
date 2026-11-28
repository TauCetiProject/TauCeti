/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Cube.Pair

/-!
# The boundary of the fundamental class of the cube at the points of its faces

The connecting morphism `Hₘ₊₂(Iᵐ⁺², ∂Iᵐ⁺²) ⟶ Hₘ₊₁(∂Iᵐ⁺²)` of normalized cubical homology sends the
class of the identity cube to the class of its boundary, the signed sum `∑ᵢ (-1)ⁱ (∂ᵢ⁰ - ∂ᵢ¹)` of
the faces of the cube (`TauCeti.cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle`). This file reads
that class in the local homology of `∂Iᵐ⁺²` at a point of the interior of one face.

For `i : Fin (m + 2)` and `t ∈ {0, 1}`, the face `∂ᵢᵗ` of `Iᵐ⁺²` is the cube `x ↦ i.insertNth t x`,
read in the boundary `∂Iᵐ⁺²` (`TauCeti.cubeBoundaryFace`). Let `a = ∂ᵢᵗ(y)` be the image of a point
`y` of the interior of `Iᵐ⁺¹`. Every other face misses `a`, and the face `∂ᵢᵗ` carries `∂Iᵐ⁺¹` off
`a`, so it is a map of pairs `(Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ (∂Iᵐ⁺², ∂Iᵐ⁺² ∖ {a})`. In the local homology
`Hₘ₊₁(∂Iᵐ⁺², ∂Iᵐ⁺² ∖ {a}; k)`, with coefficients in any ring `k`, the image of the boundary of the
fundamental class `[Iᵐ⁺², ∂Iᵐ⁺²]` is therefore the image of the fundamental class
`[Iᵐ⁺¹, ∂Iᵐ⁺¹]` under this face, with the sign of the face in the boundary of the identity cube:

* `(-1)ⁱ` for the face `t = 0`
  (`TauCeti.homologyMap_cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle_face_zero`);
* `-(-1)ⁱ` for the face `t = 1`
  (`TauCeti.homologyMap_cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle_face_one`).

This is the cube case of the comparison that fundamental chains of manifolds with corners need
over the integers: at an interior point of each codimension-one face, the boundary of the
fundamental class relative to the boundary is compared with the fundamental class of the face, up
to a sign that integral coefficients see. The face condition of
`TauCeti.TwistingChainSystem.exists_isRepresenting_of_faces` asks for this comparison on the
compactified trajectory spaces, whose faces are products. Over a ring in which `-1 = 1`, such as
`ZMod 2`, the signs disappear.

## Main definitions

* `TauCeti.cubeBoundaryFace`: the face `∂ᵢᵗ` of `Iᵐ⁺²`, as a singular cube of `∂Iᵐ⁺²`.
* `TauCeti.cubeBoundaryFaceLocalPair`: the local pair `(∂Iᵐ⁺², ∂Iᵐ⁺² ∖ {∂ᵢᵗ(y)})`.

## Main results

* `TauCeti.cubicalBoundaryChainOfCube_upCube`: the boundary of the identity cube of `Iᵐ⁺²` is the
  signed sum `∑ᵢ (-1)ⁱ (∂ᵢ⁰ - ∂ᵢ¹)` of the faces `cubeBoundaryFace`.
* `TauCeti.homologyMap_cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle_face_zero`,
  `TauCeti.homologyMap_cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle_face_one`: at an interior
  point of the face `∂ᵢᵗ`, the boundary of `[Iᵐ⁺², ∂Iᵐ⁺²]` is `(-1)ⁱ`, respectively `-(-1)ⁱ`, times
  the image of `[Iᵐ⁺¹, ∂Iᵐ⁺¹]` under the face.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II (the boundary of a
  singular cube).
* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. 166 (2007), Lemma 2.2 (fundamental chains of manifolds with corners).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Proposition 5.2.6.
-/

public section

noncomputable section

open CategoryTheory Limits Set
open scoped unitInterval Topology

universe u

namespace TauCeti

/-! ### The faces of the cube in its boundary -/

section Face

variable (m : ℕ) (i : Fin (m + 2)) {t : I} (ht : t = 0 ∨ t = 1)

/-- The face `∂ᵢᵗ` of the cube `Iᵐ⁺²`, for `t ∈ {0, 1}`: the face `x ↦ i.insertNth t x` of the
identity cube, read as a singular cube of the boundary `∂Iᵐ⁺²`. -/
def cubeBoundaryFace : SingularCube (cubeBoundaryPair.{u} (m + 1 + 1)).snd (m + 1) :=
  (cubeBoundaryPair.{u} (m + 1 + 1)).liftSnd (SingularCube.face i t
      (upCube.{u} (m + 1 + 1) : SingularCube (cubeBoundaryPair.{u} (m + 1 + 1)).fst (m + 1 + 1)))
    (TopPair.face_mem_range_map (mapsTo_upCube_boundary (m + 1 + 1)) i ht)

/-- The face `∂ᵢᵗ` of the identity cube, lifted to the boundary `∂Iᵐ⁺²`, is `cubeBoundaryFace`. -/
theorem liftSnd_face_upCube
    (h : ∀ x, SingularCube.face i t (upCube.{u} (m + 1 + 1) :
      SingularCube (cubeBoundaryPair.{u} (m + 1 + 1)).fst (m + 1 + 1)) x ∈
        range (cubeBoundaryPair.{u} (m + 1 + 1)).map) :
    (cubeBoundaryPair.{u} (m + 1 + 1)).liftSnd (SingularCube.face i t
        (upCube.{u} (m + 1 + 1) : SingularCube (cubeBoundaryPair.{u} (m + 1 + 1)).fst (m + 1 + 1)))
        h =
      cubeBoundaryFace m i ht :=
  (rfl)

/-- Pushed into the cube `Iᵐ⁺²`, the face `cubeBoundaryFace` is the face `∂ᵢᵗ` of the identity
cube. -/
theorem map_comp_cubeBoundaryFace :
    (cubeBoundaryPair.{u} (m + 1 + 1)).map.hom.comp (cubeBoundaryFace m i ht) =
      SingularCube.face i t
        (upCube.{u} (m + 1 + 1) :
          SingularCube (cubeBoundaryPair.{u} (m + 1 + 1)).fst (m + 1 + 1)) := by
  rw [← liftSnd_face_upCube m i ht (TopPair.face_mem_range_map (mapsTo_upCube_boundary _) i ht)]
  exact ContinuousMap.ext fun x ↦ TopPair.map_liftSnd (X := cubeBoundaryPair.{u} (m + 1 + 1)) _ _ x

/-- The face `∂ᵢᵗ` sends `x` to the point `i.insertNth t x` of the cube. -/
@[simp]
theorem val_cubeBoundaryFace_apply (x : I^(Fin (m + 1))) :
    (cubeBoundaryFace.{u} m i ht x).val = ULift.up (i.insertNth t x) :=
  -- The embedding of `∂Iᵐ⁺²` is the inclusion of the subtype, and the identity cube is `ULift.up`.
  (ContinuousMap.congr_fun (map_comp_cubeBoundaryFace m i ht) x).trans
    (SingularCube.face_apply i t _ x)

/-- The face `∂ᵢᵗ` is injective. -/
theorem cubeBoundaryFace_injective : Function.Injective (cubeBoundaryFace.{u} m i ht) :=
  fun _ _ h ↦ by
    simpa using congrArg (fun z : (cubeBoundaryPair.{u} (m + 1 + 1)).snd ↦ z.val.down) h

variable {m i ht} {y : I^(Fin (m + 1))}

/-- **The other faces miss the interior points of a face.** For `t, s ∈ {0, 1}` and a face `∂ⱼˢ`
other than `∂ᵢᵗ`, the face `∂ⱼˢ` misses the image under `∂ᵢᵗ` of every interior point of
`Iᵐ⁺¹`. -/
theorem cubeBoundaryFace_ne_of_notMem_boundary (hy : y ∉ Cube.boundary (Fin (m + 1)))
    (j : Fin (m + 2)) {s : I} (hs : s = 0 ∨ s = 1) (hji : j ≠ i ∨ s ≠ t) (x : I^(Fin (m + 1))) :
    cubeBoundaryFace.{u} m j hs x ≠ cubeBoundaryFace.{u} m i ht y := by
  intro h
  have h' := congrArg (fun z : (cubeBoundaryPair.{u} (m + 1 + 1)).snd ↦ z.val.down j) h
  simp only [val_cubeBoundaryFace_apply, Fin.insertNth_apply_same] at h'
  obtain rfl | hji' := eq_or_ne j i
  · -- Two faces in the same direction are at different heights.
    rw [Fin.insertNth_apply_same] at h'
    exact hji.resolve_left (fun h ↦ h rfl) h'
  · -- In the coordinate `j`, the face `∂ⱼˢ` takes the value `s ∈ {0, 1}`, and `∂ᵢᵗ(y)` a value
    -- of `y`, which is neither `0` nor `1` since `y` is not on the boundary.
    obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hji'
    rw [Fin.insertNth_apply_succAbove] at h'
    exact hy ⟨j', by rcases hs with rfl | rfl <;> simp [← h']⟩

/-- The local pair `(∂Iᵐ⁺², ∂Iᵐ⁺² ∖ {∂ᵢᵗ(y)})` of the boundary of the cube `Iᵐ⁺²` at the image of a
point `y` under the face `∂ᵢᵗ`. -/
abbrev cubeBoundaryFaceLocalPair (i : Fin (m + 2)) (ht : t = 0 ∨ t = 1) (y : I^(Fin (m + 1))) :
    TopPair.{u} :=
  TopPair.ofSubset ({cubeBoundaryFace m i ht y}ᶜ : Set (cubeBoundaryPair.{u} (m + 1 + 1)).snd)

/-- **The face `∂ᵢᵗ` as a map of pairs.** For a point `y` of the interior of `Iᵐ⁺¹`, the face `∂ᵢᵗ`
carries the boundary `∂Iᵐ⁺¹` into the complement of `∂ᵢᵗ(y)` in `∂Iᵐ⁺²`. -/
theorem mapsTo_cubeBoundaryFace (hy : y ∉ Cube.boundary (Fin (m + 1))) :
    MapsTo (cubeBoundaryFace m i ht) (Cube.boundary (Fin (m + 1)))
      (range (cubeBoundaryFaceLocalPair.{u} i ht y).map) :=
  fun _ hx ↦ ⟨⟨_, fun h ↦ hy (cubeBoundaryFace_injective m i ht h ▸ hx)⟩, rfl⟩

end Face

/-! ### The boundary of the fundamental class at a point of a face -/

section Boundary

variable (k : Type u) [Ring k] {m : ℕ} (i : Fin (m + 2)) {t : I} (ht : t = 0 ∨ t = 1)
  {y : I^(Fin (m + 1))} (hy : y ∉ Cube.boundary (Fin (m + 1)))

/-- **The boundary of the identity cube of `Iᵐ⁺²`**, as a chain of `∂Iᵐ⁺²`, is the signed sum
`∑ᵢ (-1)ⁱ (∂ᵢ⁰ - ∂ᵢ¹)` of its faces. -/
theorem cubicalBoundaryChainOfCube_upCube (m : ℕ) :
    TopPair.cubicalBoundaryChainOfCube k _ (mapsTo_upCube_boundary.{u} (m + 1 + 1)) =
      ∑ i : Fin (m + 2), (-1 : k) ^ (i : ℕ) •
        (NormalizedCubicalChain.ofCube _ k (cubeBoundaryFace m i (.inl rfl)) -
          NormalizedCubicalChain.ofCube _ k (cubeBoundaryFace m i (.inr rfl))) :=
  TopPair.cubicalBoundaryChainOfCube_def k _ _

include hy in
/-- A face other than `∂ᵢᵗ` vanishes in the relative chains of `(∂Iᵐ⁺², ∂Iᵐ⁺² ∖ {∂ᵢᵗ(y)})`. -/
private lemma cubicalChainOfCube_cubeBoundaryFace_eq_zero (j : Fin (m + 2)) {s : I}
    (hs : s = 0 ∨ s = 1) (hji : j ≠ i ∨ s ≠ t) :
    TopPair.cubicalChainOfCube k (P := cubeBoundaryFaceLocalPair i ht y)
      (cubeBoundaryFace m j hs) = 0 := by
  have hc : ∀ x, cubeBoundaryFace m j hs x ∈ range (cubeBoundaryFaceLocalPair i ht y).map :=
    fun x ↦ ⟨⟨_, cubeBoundaryFace_ne_of_notMem_boundary hy j hs hji x⟩, rfl⟩
  -- The face is a cube of the subspace `∂Iᵐ⁺² ∖ {∂ᵢᵗ(y)}`, pushed into `∂Iᵐ⁺²`.
  have hlift : (cubeBoundaryFaceLocalPair i ht y).map.hom.comp
      ((cubeBoundaryFaceLocalPair i ht y).liftSnd (cubeBoundaryFace m j hs) hc) =
        cubeBoundaryFace m j hs :=
    ContinuousMap.ext (TopPair.map_liftSnd _ hc)
  rw [← hlift]
  exact TopPair.cubicalChainOfCube_map_comp_eq_zero k _

include hy in
/-- **The boundary of the identity cube at a point of a face, at the chain level.** In the relative
chains of `(∂Iᵐ⁺², ∂Iᵐ⁺² ∖ {∂ᵢᵗ(y)})`, the boundary `∑ⱼ (-1)ʲ (∂ⱼ⁰ - ∂ⱼ¹)` of the identity cube
of `Iᵐ⁺²` is the term `(-1)ⁱ (∂ᵢ⁰ - ∂ᵢ¹)` of the direction `i` alone. -/
private lemma cokernel_π_f_cubicalBoundaryChainOfCube_upCube :
    ((cokernel.π ((normalizedCubicalChainComplex k).map
        (cubeBoundaryFaceLocalPair i ht y).map)).f (m + 1)).hom
      (TopPair.cubicalBoundaryChainOfCube k _ (mapsTo_upCube_boundary.{u} (m + 1 + 1))) =
      (-1 : k) ^ (i : ℕ) • (TopPair.cubicalChainOfCube k (cubeBoundaryFace m i (.inl rfl)) -
        TopPair.cubicalChainOfCube k (cubeBoundaryFace m i (.inr rfl))) := by
  -- The relative chains of the pair are a quotient of the chains of `∂Iᵐ⁺²`, which is the ambient
  -- space of the pair only after unfolding `TopPair.ofSubset`, so the boundary chain is expanded by
  -- terms rather than by `rw`.
  refine (congrArg _ (cubicalBoundaryChainOfCube_upCube k m)).trans ((map_sum _ _ _).trans ?_)
  refine (Finset.sum_congr rfl fun j _ ↦ (map_smul _ _ _).trans (congrArg _
    ((map_sub _ _ _).trans (congrArg₂ _
      (TopPair.cokernel_π_f_ofCube k (P := cubeBoundaryFaceLocalPair i ht y) _)
      (TopPair.cokernel_π_f_ofCube k (P := cubeBoundaryFaceLocalPair i ht y) _))))).trans ?_
  rw [Finset.sum_eq_single i (fun j _ hj ↦ ?_) (by simp)]
  rw [cubicalChainOfCube_cubeBoundaryFace_eq_zero k i ht hy j _ (.inl hj),
    cubicalChainOfCube_cubeBoundaryFace_eq_zero k i ht hy j _ (.inl hj), sub_zero, smul_zero]

include hy in
/-- The image of the boundary of the fundamental class of `Iᵐ⁺²` in the local homology at
`∂ᵢᵗ(y)` is `c` times the image of the fundamental class of `Iᵐ⁺¹` under the face `∂ᵢᵗ`, as soon
as the same holds for the chains: the boundary of the identity cube is `c` times the face. -/
private lemma homologyMap_cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle_of_eq_smul (c : k)
    (hc : ((cokernel.π ((normalizedCubicalChainComplex k).map
        (cubeBoundaryFaceLocalPair i ht y).map)).f (m + 1)).hom
      (TopPair.cubicalBoundaryChainOfCube k _ (mapsTo_upCube_boundary.{u} (m + 1 + 1))) =
      c • TopPair.cubicalChainOfCube k (cubeBoundaryFace m i ht)) :
    (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
        (cubeBoundaryFaceLocalPair i ht y).map)) (m + 1)).hom
      (((cubeBoundaryPair.{u} (m + 1 + 1)).cubicalHomologyδ k (m + 1 + 1) (m + 1)).hom
        (((cubeBoundaryPair.{u} (m + 1 + 1)).cubicalChainComplex k).homologyπ (m + 1 + 1)
          (cubeBoundaryPairCycle k (m + 1)))) =
      c • HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
            (cubeBoundaryPairHom (cubeBoundaryFace m i ht) (mapsTo_cubeBoundaryFace hy))) (m + 1)
          (((cubeBoundaryPair.{u} (m + 1)).cubicalChainComplex k).homologyπ (m + 1)
            (cubeBoundaryPairCycle k m)) := by
  -- The chain-level identity, on cycles.
  have hcyc : HomologicalComplex.cyclesMap (cokernel.π ((normalizedCubicalChainComplex k).map
        (cubeBoundaryFaceLocalPair i ht y).map)) (m + 1) (cubeBoundaryCycle k (m + 1)) =
      c • TopPair.cubicalCycleOfCube k (cubeBoundaryFace m i ht) (mapsTo_cubeBoundaryFace hy) := by
    refine HomologicalComplex.moduleCat_iCycles_injective _ _ ?_
    refine (HomologicalComplex.moduleCat_iCycles_cyclesMap_apply _ _ _ _).trans ?_
    exact ((congrArg _ (iCycles_cubeBoundaryCycle k (m + 1))).trans hc).trans
      ((map_smul _ c _).trans (congrArg (c • ·) (TopPair.iCycles_cubicalCycleOfCube k _ _))).symm
  -- The connecting morphism sends the fundamental class to the fundamental cycle of `∂Iᵐ⁺²`, and
  -- the map to the local homology acts on that cycle by the chain-level identity.
  have hnat : (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
        (cubeBoundaryFaceLocalPair i ht y).map)) (m + 1)).hom
        (((normalizedCubicalChainComplex k).obj (cubeBoundaryPair.{u} (m + 1 + 1)).snd).homologyπ
          (m + 1) (cubeBoundaryCycle k (m + 1))) =
      ((cubeBoundaryFaceLocalPair i ht y).cubicalChainComplex k).homologyπ (m + 1)
        (HomologicalComplex.cyclesMap (cokernel.π ((normalizedCubicalChainComplex k).map
          (cubeBoundaryFaceLocalPair i ht y).map)) (m + 1) (cubeBoundaryCycle k (m + 1))) :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality
      (cokernel.π ((normalizedCubicalChainComplex k).map
        (cubeBoundaryFaceLocalPair i ht y).map)) (m + 1))
      (cubeBoundaryCycle k (m + 1))
  -- The ambient space of the local pair is `∂Iᵐ⁺²` only after unfolding `TopPair.ofSubset`, so the
  -- steps are chained by terms rather than rewritten.
  exact ((congrArg _ (cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle k (m + 1))).trans
    (hnat.trans (congrArg _ hcyc))).trans ((map_smul _ _ _).trans
      (congrArg _ (homologyMap_cubeBoundaryPairHom_cubeBoundaryPairCycle k _ _).symm))

include hy in
/-- **The boundary of the fundamental class of the cube at a point of a face `∂ᵢ⁰`.** Let `y` be a
point of the interior of `Iᵐ⁺¹` and `a = ∂ᵢ⁰(y)` the corresponding point of the face
`x ↦ i.insertNth 0 x` of `Iᵐ⁺²`. In the local homology `Hₘ₊₁(∂Iᵐ⁺², ∂Iᵐ⁺² ∖ {a}; k)`, the image
of the boundary of the fundamental class `[Iᵐ⁺², ∂Iᵐ⁺²]` is `(-1)ⁱ` times the image of the
fundamental class `[Iᵐ⁺¹, ∂Iᵐ⁺¹]` under the face, read as a map of pairs
`(Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ (∂Iᵐ⁺², ∂Iᵐ⁺² ∖ {a})`. -/
theorem homologyMap_cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle_face_zero :
    (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
        (cubeBoundaryFaceLocalPair i (.inl rfl) y).map)) (m + 1)).hom
      (((cubeBoundaryPair.{u} (m + 1 + 1)).cubicalHomologyδ k (m + 1 + 1) (m + 1)).hom
        (((cubeBoundaryPair.{u} (m + 1 + 1)).cubicalChainComplex k).homologyπ (m + 1 + 1)
          (cubeBoundaryPairCycle k (m + 1)))) =
      (-1 : k) ^ (i : ℕ) •
        HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
            (cubeBoundaryPairHom (cubeBoundaryFace m i (.inl rfl))
              (mapsTo_cubeBoundaryFace hy))) (m + 1)
          (((cubeBoundaryPair.{u} (m + 1)).cubicalChainComplex k).homologyπ (m + 1)
            (cubeBoundaryPairCycle k m)) :=
  homologyMap_cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle_of_eq_smul k i _ hy _ (by
    -- The opposite face `∂ᵢ¹` misses the point of `∂ᵢ⁰`.
    rw [cokernel_π_f_cubicalBoundaryChainOfCube_upCube k i (.inl rfl) hy,
      cubicalChainOfCube_cubeBoundaryFace_eq_zero k i (.inl rfl) hy i (.inr rfl)
        (.inr zero_ne_one.symm), sub_zero])

include hy in
/-- **The boundary of the fundamental class of the cube at a point of a face `∂ᵢ¹`.** Let `y` be a
point of the interior of `Iᵐ⁺¹` and `a = ∂ᵢ¹(y)` the corresponding point of the face
`x ↦ i.insertNth 1 x` of `Iᵐ⁺²`. In the local homology `Hₘ₊₁(∂Iᵐ⁺², ∂Iᵐ⁺² ∖ {a}; k)`, the image
of the boundary of the fundamental class `[Iᵐ⁺², ∂Iᵐ⁺²]` is `-(-1)ⁱ` times the image of the
fundamental class `[Iᵐ⁺¹, ∂Iᵐ⁺¹]` under the face, read as a map of pairs
`(Iᵐ⁺¹, ∂Iᵐ⁺¹) ⟶ (∂Iᵐ⁺², ∂Iᵐ⁺² ∖ {a})`. -/
theorem homologyMap_cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle_face_one :
    (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
        (cubeBoundaryFaceLocalPair i (.inr rfl) y).map)) (m + 1)).hom
      (((cubeBoundaryPair.{u} (m + 1 + 1)).cubicalHomologyδ k (m + 1 + 1) (m + 1)).hom
        (((cubeBoundaryPair.{u} (m + 1 + 1)).cubicalChainComplex k).homologyπ (m + 1 + 1)
          (cubeBoundaryPairCycle k (m + 1)))) =
      -((-1 : k) ^ (i : ℕ)) •
        HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
            (cubeBoundaryPairHom (cubeBoundaryFace m i (.inr rfl))
              (mapsTo_cubeBoundaryFace hy))) (m + 1)
          (((cubeBoundaryPair.{u} (m + 1)).cubicalChainComplex k).homologyπ (m + 1)
            (cubeBoundaryPairCycle k m)) :=
  homologyMap_cubicalHomologyδ_homologyπ_cubeBoundaryPairCycle_of_eq_smul k i _ hy _ (by
    -- The opposite face `∂ᵢ⁰` misses the point of `∂ᵢ¹`.
    rw [cokernel_π_f_cubicalBoundaryChainOfCube_upCube k i (.inr rfl) hy,
      cubicalChainOfCube_cubeBoundaryFace_eq_zero k i (.inr rfl) hy i (.inl rfl)
        (.inr zero_ne_one), zero_sub, smul_neg, neg_smul])

end Boundary

end TauCeti
