/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.DiskSphere
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.Topology.Category.TopPair
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map

/-!
# The Hurewicz map

For a space `X` with a base point `x` and a coefficient object `R` of an abelian category with
coproducts, this file constructs the Hurewicz map

`HomotopyGroup.hurewicz R n : π_{n+1}(X, x) → (R ⟶ Hₙ₊₁(X; R))`

on Mathlib's cubical homotopy groups `HomotopyGroup (Fin (n + 1)) X x`.  It sends the class of a
generalized loop `p : Iⁿ⁺¹ → X`, which maps the boundary `∂Iⁿ⁺¹` of the cube to `x`, to the image
of the generator of `Hₙ₊₁(Iⁿ⁺¹, ∂Iⁿ⁺¹; R) ≅ R` under the map of pairs
`p : (Iⁿ⁺¹, ∂Iⁿ⁺¹) ⟶ (X, {x})`, read in `Hₙ₊₁(X; R)` through the isomorphism
`Hₙ₊₁(X; R) ≅ Hₙ₊₁(X, {x}; R)`.  With `C = ModuleCat ℤ` and `R = ℤ`, evaluating the resulting
morphism at `1` gives the classical Hurewicz map `π_{n+1}(X, x) → Hₙ₊₁(X; ℤ)`,
`[p] ↦ p_*[Iⁿ⁺¹]`.

The ingredients are the following.

* The cube pair `TauCeti.cubeBoundaryPair n = (Iⁿ, ∂Iⁿ)` is isomorphic to the Euclidean disk pair
  `TauCeti.diskBoundaryPair n = (Dⁿ, Sⁿ⁻¹)` (`TauCeti.diskBoundaryPairIsoCube`), through the affine
  homeomorphism of the cube onto the closed unit ball of the sup norm and the radial rescaling of
  that ball onto the Euclidean disk.  Hence `Hₙ(Iⁿ, ∂Iⁿ; R) ≅ R`
  (`TauCeti.singularHomologyCubeBoundaryPairIso`), transported from
  `TauCeti.singularHomologyDiskBoundaryPairIso`.  No choices enter: the disk generator comes from
  the standard generator of the homology of the boundary sphere, and the homeomorphisms are
  explicit.
* A generalized loop `p : Ω^ (Fin n) X x` is a map of pairs `(Iⁿ, ∂Iⁿ) ⟶ (X, {x})`
  (`GenLoop.toCubeBoundaryPairHom`), and homotopic generalized loops induce homotopic maps of pairs,
  hence the same map on relative homology (`GenLoop.singularHomologyMap_toCubeBoundaryPairHom_eq`).
* Since a point is contractible, `Hₖ₊₁(X) ⟶ Hₖ₊₁(X, {x})` is an isomorphism
  (`TauCeti.singularHomologyIsoOfSubsetSingleton`, from
  `TopPair.isIso_singularHomologyπ_of_contractibleSpace`).

The Hurewicz map is natural in based maps (`HomotopyGroup.hurewicz_map`) and sends the identity
class to zero (`HomotopyGroup.hurewicz_one`).  That it is a group homomorphism is not proved in
this file.

## Main declarations

* `TauCeti.cubeBoundaryPair`: the pair `(Iⁿ, ∂Iⁿ)`.
* `TauCeti.diskBoundaryPairIsoCube`: the isomorphism of pairs `(Dⁿ, Sⁿ⁻¹) ≅ (Iⁿ, ∂Iⁿ)`.
* `TauCeti.singularHomologyCubeBoundaryPairIso`: `Hₙ(Iⁿ, ∂Iⁿ; R) ≅ R`.
* `GenLoop.toCubeBoundaryPairHom`: a generalized loop as a map of pairs `(Iⁿ, ∂Iⁿ) ⟶ (X, {x})`.
* `GenLoop.hurewicz`: the Hurewicz class of a generalized loop, characterized by
  `GenLoop.hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom`.
* `HomotopyGroup.hurewicz`: the Hurewicz map on homotopy classes.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2, the Hurewicz maps `πₙ(X, x₀) → Hₙ(X)` and `πₙ(X, A, x₀) → Hₙ(X, A)`, defined by
  pushing forward a generator of `Hₙ(Dⁿ, ∂Dⁿ)`.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped unitInterval Topology Topology.Homotopy

universe w v u

namespace TauCeti

section CubePair

variable (n : ℕ)

/-- The cube `Iⁿ` and its boundary `∂Iⁿ` as a topological pair, lifted to the universe `w`. -/
abbrev cubeBoundaryPair : TopPair.{w} :=
  TopPair.ofSubset (X := TopCat.of (ULift.{w} (I^(Fin n))))
    (ULift.down ⁻¹' Cube.boundary (Fin n))

/-- The homeomorphism from the Euclidean disk `Dⁿ` onto the cube `Iⁿ`: the radial rescaling of the
disk onto the closed unit ball of the sup norm on `Fin n → ℝ`, followed by the inverse of the affine
homeomorphism `TauCeti.cubeHomeomorphClosedBall` of the cube onto that ball. -/
def diskHomeomorphCube : TopCat.disk.{w} n ≃ₜ (I^(Fin n)) :=
  (diskHomeomorphClosedBall n).trans (cubeHomeomorphClosedBall (Fin n)).symm

variable {n} in
/-- `TauCeti.diskHomeomorphCube` carries the boundary sphere of the disk onto the boundary of the
cube. -/
theorem diskHomeomorphCube_mem_boundary_iff (z : TopCat.disk.{w} n) :
    diskHomeomorphCube n z ∈ Cube.boundary (Fin n) ↔
      z ∈ Set.range (TopCat.diskBoundaryInclusion.{w} n) := by
  rw [← norm_diskHomeomorphClosedBall_eq_one_iff, Cube.boundary, Set.mem_ofPred_eq,
    ← norm_cubeHomeomorphClosedBall_eq_one_iff, diskHomeomorphCube, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply]

/-- The homeomorphism `TauCeti.diskHomeomorphCube` as an isomorphism in `TopCat` from the disk
onto the lifted cube. -/
private def diskIsoCube : TopCat.disk.{w} n ≅ TopCat.of (ULift.{w} (I^(Fin n))) :=
  TopCat.isoOfHomeo ((diskHomeomorphCube n).trans Homeomorph.ulift.{w}.symm)

/-- The homeomorphism `TauCeti.diskHomeomorphCube` as a map of pairs `(Dⁿ, Sⁿ⁻¹) ⟶ (Iⁿ, ∂Iⁿ)`. -/
def diskBoundaryPairToCube : diskBoundaryPair.{w} n ⟶ cubeBoundaryPair.{w} n :=
  TopPair.ofHom (diskIsoCube n).hom
    (TopCat.ofHom ⟨fun s ↦ ⟨ULift.up (diskHomeomorphCube n (TopCat.diskBoundaryInclusion n s)),
      (diskHomeomorphCube_mem_boundary_iff _).2 ⟨s, rfl⟩⟩,
      (continuous_uliftUp.comp ((diskHomeomorphCube n).continuous.comp
        (TopCat.diskBoundaryInclusion n).hom.continuous)).subtype_mk _⟩)
    (by ext; rfl)

private lemma surjective_snd_diskBoundaryPairToCube :
    Function.Surjective (TopPair.Hom.snd (diskBoundaryPairToCube.{w} n)) := by
  rintro ⟨y, hy⟩
  obtain ⟨s, hs⟩ := (diskHomeomorphCube_mem_boundary_iff ((diskHomeomorphCube n).symm y.down)).1
    (by rwa [Homeomorph.apply_symm_apply])
  refine ⟨s, Subtype.ext (ULift.ext ?_)⟩
  -- The subspace component of the map is `TauCeti.diskHomeomorphCube` on the boundary sphere.
  change diskHomeomorphCube n (TopCat.diskBoundaryInclusion n s) = y.down
  rw [hs, Homeomorph.apply_symm_apply]

/-- **The disk pair is the cube pair**: `TauCeti.diskBoundaryPairToCube` is an isomorphism of
pairs `(Dⁿ, Sⁿ⁻¹) ≅ (Iⁿ, ∂Iⁿ)`. -/
def diskBoundaryPairIsoCube : diskBoundaryPair.{w} n ≅ cubeBoundaryPair.{w} n :=
  have : IsIso (TopPair.Hom.fst (diskBoundaryPairToCube.{w} n)) :=
    inferInstanceAs (IsIso (diskIsoCube n).hom)
  have := TopPair.isIso_of_isIso_fst_of_surjective_snd _ (surjective_snd_diskBoundaryPairToCube n)
  asIso (diskBoundaryPairToCube n)

@[simp]
lemma diskBoundaryPairIsoCube_hom : (diskBoundaryPairIsoCube.{w} n).hom =
    diskBoundaryPairToCube n :=
  (rfl)

end CubePair

section CubePairHomology

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)

/-- **The relative homology of a cube modulo its boundary in its dimension**:
`Hₙ(Iⁿ, ∂Iⁿ; R) ≅ R`, transported from `TauCeti.singularHomologyDiskBoundaryPairIso` along the
isomorphism of pairs `TauCeti.diskBoundaryPairIsoCube`. -/
def singularHomologyCubeBoundaryPairIso : (cubeBoundaryPair.{w} n).singularHomology R n ≅ R :=
  (SSetPair.homologyFunctor R n).mapIso
      (TopPair.toSSetPair.mapIso (diskBoundaryPairIsoCube n)).symm ≪≫
    singularHomologyDiskBoundaryPairIso R n

/-- The generator of `Hₙ(Iⁿ, ∂Iⁿ; R)` is the image of the generator of `Hₙ(Dⁿ, Sⁿ⁻¹; R)` under
`TauCeti.diskBoundaryPairToCube`. -/
lemma singularHomologyCubeBoundaryPairIso_inv :
    (singularHomologyCubeBoundaryPairIso R n).inv =
      (singularHomologyDiskBoundaryPairIso R n).inv ≫
        TopPair.singularHomologyMap (diskBoundaryPairToCube.{w} n) R n :=
  (rfl)

/-- The relative homology of a cube modulo its boundary vanishes outside its dimension:
`Hₖ(Iⁿ, ∂Iⁿ; R) = 0` for `k ≠ n`. -/
theorem isZero_singularHomology_cubeBoundaryPair_of_ne {k : ℕ} (hk : k ≠ n) :
    IsZero ((cubeBoundaryPair.{w} n).singularHomology R k) :=
  (isZero_singularHomology_diskBoundaryPair_of_ne R hk).of_iso
    ((SSetPair.homologyFunctor R k).mapIso
      (TopPair.toSSetPair.mapIso (diskBoundaryPairIsoCube n))).symm

end CubePairHomology

end TauCeti

namespace GenLoop

open TauCeti

variable {n : ℕ} {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- A generalized loop `p : Ω^ (Fin n) X x`, a map `Iⁿ → X` sending the boundary of the cube to
`x`, as a map of pairs `(Iⁿ, ∂Iⁿ) ⟶ (X, {x})`. -/
def toCubeBoundaryPairHom (p : Ω^ (Fin n) X x) :
    cubeBoundaryPair.{w} n ⟶ TopPair.ofSubset ({x} : Set (TopCat.of X)) :=
  TopPair.ofSubsetMap (TopCat.ofHom (p.1.comp ⟨ULift.down, continuous_uliftDown⟩))
    fun z hz ↦ _root_.GenLoop.boundary p z.down hz

@[simp]
lemma toCubeBoundaryPairHom_fst_apply (p : Ω^ (Fin n) X x) (z : (cubeBoundaryPair.{w} n).fst) :
    TopPair.Hom.fst (toCubeBoundaryPairHom p) z = p (ULift.down z) :=
  TopPair.ofSubsetMap_fst_apply _ _ z

/-- Postcomposing a generalized loop with a based map postcomposes its map of pairs with the
induced map `(X, {x}) ⟶ (Y, {y})`. -/
lemma toCubeBoundaryPairHom_map (f : C(X, Y)) (hf : f x = y) (p : Ω^ (Fin n) X x) :
    toCubeBoundaryPairHom (GenLoop.map f hf p) =
      toCubeBoundaryPairHom p ≫ TopPair.ofSubsetMap (TopCat.ofHom f)
        (Set.mapsTo_singleton.2 (Set.mem_singleton_iff.2 hf)) :=
  TopPair.ofSubsetMap_comp (TopCat.ofHom (p.1.comp ⟨ULift.down, continuous_uliftDown⟩))
    (TopCat.ofHom f) _ _ _

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

/-- **Homotopic generalized loops induce the same map on relative homology**: a homotopy relative
to the boundary of the cube is a homotopy of the maps of pairs `(Iⁿ, ∂Iⁿ) ⟶ (X, {x})`. -/
theorem singularHomologyMap_toCubeBoundaryPairHom_eq {p q : Ω^ (Fin n) X x}
    (h : _root_.GenLoop.Homotopic p q) (k : ℕ) :
    TopPair.singularHomologyMap (toCubeBoundaryPairHom p) R k =
      TopPair.singularHomologyMap (toCubeBoundaryPairHom q) R k := by
  obtain ⟨H⟩ := h
  let d : C(ULift.{w} (I^(Fin n)), I^(Fin n)) := ⟨ULift.down, continuous_uliftDown⟩
  exact (TopPair.ofSubsetHomotopy (g₀ := TopCat.ofHom (p.1.comp d))
    (g₁ := TopCat.ofHom (q.1.comp d)) (H.toHomotopy.compContinuousMap d)
    fun τ z hz ↦ (H.eq_fst τ hz).trans
      (_root_.GenLoop.boundary p z.down hz)).congr_singularHomologyMap R k

end GenLoop

namespace GenLoop

open TauCeti

variable {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) {n : ℕ}

/-- **The Hurewicz class of a generalized loop** `p : Iⁿ⁺¹ → X`: the image of the generator
`TauCeti.singularHomologyCubeBoundaryPairIso` of `Hₙ₊₁(Iⁿ⁺¹, ∂Iⁿ⁺¹; R)` under the map of pairs
`p : (Iⁿ⁺¹, ∂Iⁿ⁺¹) ⟶ (X, {x})`, read in `Hₙ₊₁(X; R)` through the isomorphism
`TauCeti.singularHomologyIsoOfSubsetSingleton`
(`GenLoop.hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom`). -/
def hurewicz (p : Ω^ (Fin (n + 1)) X x) :
    R ⟶ ((singularHomologyFunctor C (n + 1)).obj R).obj (TopCat.of X) :=
  (singularHomologyCubeBoundaryPairIso R (n + 1)).inv ≫
    TopPair.singularHomologyMap (toCubeBoundaryPairHom p) R (n + 1) ≫
      (singularHomologyIsoOfSubsetSingleton R n x).inv

/-- The Hurewicz class of a generalized loop, followed by the isomorphism
`Hₙ₊₁(X; R) ≅ Hₙ₊₁(X, {x}; R)`, is the image of the generator of `Hₙ₊₁(Iⁿ⁺¹, ∂Iⁿ⁺¹; R)` under the
loop viewed as a map of pairs. -/
@[reassoc (attr := simp)]
lemma hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom (p : Ω^ (Fin (n + 1)) X x) :
    hurewicz R p ≫ (singularHomologyIsoOfSubsetSingleton R n x).hom =
      (singularHomologyCubeBoundaryPairIso R (n + 1)).inv ≫
        TopPair.singularHomologyMap (toCubeBoundaryPairHom p) R (n + 1) := by
  simp only [hurewicz, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Homotopic generalized loops have the same Hurewicz class. -/
theorem hurewicz_eq_of_homotopic {p q : Ω^ (Fin (n + 1)) X x}
    (h : _root_.GenLoop.Homotopic p q) : hurewicz R p = hurewicz R q := by
  rw [hurewicz, hurewicz, singularHomologyMap_toCubeBoundaryPairHom_eq R h]

/-- **Naturality of the Hurewicz class**: for a based map `f : (X, x) → (Y, y)`, the Hurewicz
class of `f ∘ p` is the image of that of `p` under `f_* : Hₙ₊₁(X; R) ⟶ Hₙ₊₁(Y; R)`. -/
theorem hurewicz_map (f : C(X, Y)) (hf : f x = y) (p : Ω^ (Fin (n + 1)) X x) :
    hurewicz R (GenLoop.map f hf p) =
      hurewicz R p ≫ ((singularHomologyFunctor C (n + 1)).obj R).map (TopCat.ofHom f) := by
  let g : TopPair.ofSubset ({x} : Set (TopCat.of X)) ⟶ TopPair.ofSubset ({y} : Set (TopCat.of Y)) :=
    TopPair.ofSubsetMap (TopCat.ofHom f) (Set.mapsTo_singleton.2 (Set.mem_singleton_iff.2 hf))
  have hfst : TopPair.Hom.fst g = TopCat.ofHom f := by
    ext z
    exact TopPair.ofSubsetMap_fst_apply _ _ z
  -- The quotient map from absolute to relative homology is natural in the map of pairs `g`,
  -- whose ambient component is `f`.
  have hπ := SSetPair.homologyπ_naturality (TopPair.toSSetPair.map g) R (n + 1)
  rw [TopPair.toSSetPair_map_right, hfst] at hπ
  have hπ' : ((singularHomologyFunctor C (n + 1)).obj R).map (TopCat.ofHom f) ≫
      (singularHomologyIsoOfSubsetSingleton R n y).hom =
        (singularHomologyIsoOfSubsetSingleton R n x).hom ≫
          TopPair.singularHomologyMap g R (n + 1) := by
    rw [singularHomologyIsoOfSubsetSingleton_hom, singularHomologyIsoOfSubsetSingleton_hom]
    exact hπ
  rw [← cancel_mono (singularHomologyIsoOfSubsetSingleton R n y).hom,
    hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom, Category.assoc, hπ',
    hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom_assoc, toCubeBoundaryPairHom_map,
    TopPair.singularHomologyMap_comp]

end GenLoop

namespace HomotopyGroup

open TauCeti

variable {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)

/-- **The Hurewicz map** `π_{n+1}(X, x) → (R ⟶ Hₙ₊₁(X; R))`, sending the class of a generalized
loop `p` to its Hurewicz class `GenLoop.hurewicz R p`: the image of the generator of
`Hₙ₊₁(Iⁿ⁺¹, ∂Iⁿ⁺¹; R) ≅ R` under `p : (Iⁿ⁺¹, ∂Iⁿ⁺¹) ⟶ (X, {x})`, read in `Hₙ₊₁(X; R)`. -/
def hurewicz :
    HomotopyGroup (Fin (n + 1)) X x →
      (R ⟶ ((singularHomologyFunctor C (n + 1)).obj R).obj (TopCat.of X)) :=
  Quotient.lift (GenLoop.hurewicz R) fun _ _ h ↦ GenLoop.hurewicz_eq_of_homotopic R h

@[simp]
lemma hurewicz_mk (p : Ω^ (Fin (n + 1)) X x) :
    hurewicz R n (⟦p⟧ : HomotopyGroup (Fin (n + 1)) X x) = GenLoop.hurewicz R p :=
  (rfl)

/-- **Naturality of the Hurewicz map**: for a based map `f : (X, x) → (Y, y)`, the Hurewicz class
of `f_* a` is the image of the Hurewicz class of `a` under `f_* : Hₙ₊₁(X; R) ⟶ Hₙ₊₁(Y; R)`. -/
theorem hurewicz_map (f : C(X, Y)) (hf : f x = y) (a : HomotopyGroup (Fin (n + 1)) X x) :
    hurewicz R n (HomotopyGroup.map f hf a) =
      hurewicz R n a ≫ ((singularHomologyFunctor C (n + 1)).obj R).map (TopCat.ofHom f) :=
  Quotient.inductionOn a (GenLoop.hurewicz_map R f hf)

/-- The Hurewicz map sends the identity class to zero. -/
@[simp]
theorem hurewicz_one : hurewicz R n (1 : HomotopyGroup (Fin (n + 1)) X x) = 0 := by
  -- The identity class is the image of the identity class of a point, whose homology vanishes in
  -- positive degrees.
  let c : C(PUnit.{w + 1}, X) := ContinuousMap.const _ x
  have h : (1 : HomotopyGroup (Fin (n + 1)) X x) =
      HomotopyGroup.map (y := x) c rfl (1 : HomotopyGroup (Fin (n + 1)) PUnit.{w + 1} .unit) :=
    (HomotopyGroup.map_one (y := x) c rfl).symm
  rw [h]
  refine (hurewicz_map R n c rfl _).trans ?_
  rw [(isZero_singularHomologyFunctor_of_contractibleSpace R (TopCat.of PUnit.{w + 1})
    n.succ_ne_zero).eq_of_tgt (hurewicz R n 1) 0, zero_comp]

end HomotopyGroup
