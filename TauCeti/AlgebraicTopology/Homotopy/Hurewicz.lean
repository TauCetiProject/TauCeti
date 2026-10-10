/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.DiskSphere
public import TauCeti.AlgebraicTopology.Singular.Excision
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
  explicit.  These are proved in `TauCeti/AlgebraicTopology/Disk.lean` and
  `TauCeti/AlgebraicTopology/Singular/DiskSphere.lean`.
* A generalized loop `p : Ω^ (Fin n) X x` is a map of pairs `(Iⁿ, ∂Iⁿ) ⟶ (X, {x})`
  (`GenLoop.toCubeBoundaryPairHom`), and homotopic generalized loops induce homotopic maps of pairs,
  hence the same map on relative homology (`GenLoop.singularHomologyMap_toCubeBoundaryPairHom_eq`).
* Since a point is contractible, `Hₖ₊₁(X) ⟶ Hₖ₊₁(X, {x})` is an isomorphism
  (`TauCeti.singularHomologyIsoOfSubsetSingleton`, from
  `TopPair.isIso_singularHomologyπ_of_contractibleSpace`).

The Hurewicz map is natural in based maps (`HomotopyGroup.hurewicz_map`) and sends the identity
class to zero (`HomotopyGroup.hurewicz_one`).

It is moreover a group homomorphism (`HomotopyGroup.hurewicz_mul`), bundled as
`HomotopyGroup.hurewiczHom`.  The product `[q] * [p]` is represented by a concatenation of `p` and
`q` along the first direction of the cube, with a slab `1/4 ≤ z₀ ≤ 1/2` between them sent to the
base point.  This concatenation is a map of pairs out of `(Iⁿ⁺¹, A)`, where `A` is the union of
`∂Iⁿ⁺¹` and the slab, and its restrictions to the two halves `z₀ ≤ 1/4` and `z₀ ≥ 1/2` are
reparametrisations of `p` and `q`.  So additivity reduces to a *pinch identity* in `Hₖ(Iⁿ⁺¹, A)`:
the inclusion of `(Iⁿ⁺¹, ∂Iⁿ⁺¹)` induces the sum of the maps induced by the two halves.  Write
`A = U ∩ V` with `U = ∂Iⁿ⁺¹ ∪ {z₀ ≥ 1/4}` and `V = ∂Iⁿ⁺¹ ∪ {z₀ ≤ 1/2}`.  Their interiors cover the
cube, so by excision and the long exact sequence of the triple `(Iⁿ⁺¹, U, A)` a map into
`Hₖ(Iⁿ⁺¹, A)` is determined by its images in `Hₖ(Iⁿ⁺¹, U)` and `Hₖ(Iⁿ⁺¹, V)`
(`TopPair.singularHomology_inter_hom_ext`).  In `(Iⁿ⁺¹, U)` the inclusion is homotopic to the
left half, while the right half lands in `U` and induces zero; symmetrically in `(Iⁿ⁺¹, V)`.

## Main declarations

* `GenLoop.toCubeBoundaryPairHom`: a generalized loop as a map of pairs `(Iⁿ, ∂Iⁿ) ⟶ (X, {x})`.
* `GenLoop.hurewicz`: the Hurewicz class of a generalized loop, characterized by
  `GenLoop.hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom`.
* `HomotopyGroup.hurewicz`: the Hurewicz map on homotopy classes.
* `HomotopyGroup.hurewicz_mul`, `HomotopyGroup.hurewiczHom`: the Hurewicz map is a homomorphism
  from `π_{n+1}(X, x)`, written additively, to the group of morphisms `R ⟶ Hₙ₊₁(X; R)`.

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
  rw [← cancel_mono (singularHomologyIsoOfSubsetSingleton R n y).hom,
    hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom, Category.assoc,
    singularHomologyIsoOfSubsetSingleton_hom_naturality R n f hf,
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

/-! ### The Hurewicz map is a homomorphism -/

namespace TauCeti

namespace Hurewicz

open TopPair

variable {m : ℕ} (i : Fin m)

/-- The cube `Iᵐ`, lifted to the universe `w`: the ambient space of `TauCeti.cubeBoundaryPair m`. -/
private abbrev cubeSpace (m : ℕ) : TopCat.{w} := TopCat.of (ULift.{w} (I^(Fin m)))

/-- The boundary of the cube, together with the points whose `i`-th coordinate is at least `1/4`. -/
private abbrev upperSet : Set (cubeSpace.{w} m) :=
  ULift.down ⁻¹' Cube.boundary (Fin m) ∪ {z | (1 / 4 : ℝ) ≤ z.down i}

/-- The boundary of the cube, together with the points whose `i`-th coordinate is at most `1/2`. -/
private abbrev lowerSet : Set (cubeSpace.{w} m) :=
  ULift.down ⁻¹' Cube.boundary (Fin m) ∪ {z | (z.down i : ℝ) ≤ 1 / 2}

/-- The interiors of `upperSet i` and `lowerSet i` cover the cube. -/
private lemma interior_upperSet_union_interior_lowerSet :
    interior (upperSet.{w} i) ∪ interior (lowerSet.{w} i) = Set.univ := by
  have hc : Continuous fun z : cubeSpace.{w} m ↦ (z.down i : ℝ) :=
    continuous_subtype_val.comp ((continuous_apply i).comp continuous_uliftDown)
  refine Set.eq_univ_of_forall fun z ↦ ?_
  rcases lt_or_ge (1 / 4 : ℝ) (z.down i) with h | h
  · exact Or.inl (interior_maximal (fun _ h' ↦ Or.inr (le_of_lt h'))
      (isOpen_lt continuous_const hc) h)
  · refine Or.inr (interior_maximal (fun _ h' ↦ Or.inr (le_of_lt h'))
      (isOpen_lt hc continuous_const) (?_ : (z.down i : ℝ) < 1 / 2))
    linarith

/-- Reparametrise the `i`-th coordinate of the cube by `φ`. -/
private def stretch (φ : C(I, I)) : cubeSpace.{w} m ⟶ cubeSpace.{w} m :=
  TopCat.ofHom ⟨fun z ↦ ⟨Function.update z.down i (φ (z.down i))⟩,
    continuous_uliftUp.comp (continuous_uliftDown.update i
      (φ.continuous.comp ((continuous_apply i).comp continuous_uliftDown)))⟩

private lemma stretch_apply (φ : C(I, I)) (z : cubeSpace.{w} m) :
    (stretch i φ z).down = Function.update z.down i (φ (z.down i)) :=
  (rfl)

private lemma stretch_apply_self (φ : C(I, I)) (z : cubeSpace.{w} m) :
    (stretch i φ z).down i = φ (z.down i) := by
  rw [stretch_apply, Function.update_self]

/-- The straight-line homotopy, in the `i`-th coordinate, from the identity to `stretch i φ`. -/
private def stretchHomotopy (φ : C(I, I)) :
    (TopCat.Hom.hom (𝟙 (cubeSpace.{w} m))).Homotopy (TopCat.Hom.hom (stretch i φ)) where
  toFun p := ⟨Function.update p.2.down i (Set.Icc.convexComb (p.2.down i) (φ (p.2.down i)) p.1)⟩
  continuous_toFun := by
    have hs : Continuous fun p : I × cubeSpace.{w} m ↦ p.2.down i :=
      (continuous_apply i).comp (continuous_uliftDown.comp continuous_snd)
    exact continuous_uliftUp.comp ((continuous_uliftDown.comp continuous_snd).update i
      (Set.Icc.continuous_convexComb_prod.comp
        (hs.prodMk ((φ.continuous.comp hs).prodMk continuous_fst))))
  map_zero_left z := ULift.ext (by simp)
  map_one_left z := ULift.ext ((congrArg (Function.update z.down i)
    (Set.Icc.convexComb_one _ _)).trans (stretch_apply i φ z).symm)

private lemma stretchHomotopy_apply (φ : C(I, I)) (τ : I) (z : cubeSpace.{w} m) :
    (stretchHomotopy i φ (τ, z)).down =
      Function.update z.down i (Set.Icc.convexComb (z.down i) (φ (z.down i)) τ) :=
  (rfl)

/-- Updating the `i`-th coordinate of a boundary point of the cube gives a boundary point, unless
that coordinate was `0` or `1`. -/
private lemma update_mem_boundary_or {z : I^(Fin m)} (hz : z ∈ Cube.boundary (Fin m)) (a : I) :
    Function.update z i a ∈ Cube.boundary (Fin m) ∨ z i = 0 ∨ z i = 1 := by
  obtain ⟨j, hj⟩ := hz
  by_cases hji : j = i
  · exact Or.inr (hji ▸ hj)
  · exact Or.inl ⟨j, by rwa [Function.update_of_ne hji]⟩

private lemma update_mem_boundary_of {z : I^(Fin m)} {a : I} (ha : a = 0 ∨ a = 1) :
    Function.update z i a ∈ Cube.boundary (Fin m) :=
  ⟨i, by rwa [Function.update_self]⟩

/-- `s ↦ s / 4`, onto the first quarter of the unit interval. -/
private def quarter : C(I, I) :=
  ⟨fun s ↦ ⟨s / 4, by constructor <;> linarith [s.2.1, s.2.2]⟩, by fun_prop⟩

/-- `s ↦ (s + 1) / 2`, onto the second half of the unit interval. -/
private def upperHalf : C(I, I) :=
  ⟨fun s ↦ ⟨(s + 1) / 2, by constructor <;> linarith [s.2.1, s.2.2]⟩, by fun_prop⟩

@[simp] private lemma coe_quarter (s : I) : (quarter s : ℝ) = s / 4 := (rfl)

@[simp] private lemma coe_upperHalf (s : I) : (upperHalf s : ℝ) = (s + 1) / 2 := (rfl)

/-- The cube relative to its boundary and the slab `1/4 ≤ zᵢ ≤ 1/2`. -/
private abbrev slabPair : TopPair.{w} := ofSubset (upperSet.{w} i ∩ lowerSet.{w} i)

/-- The identity of the cube carries `s` into any `t ⊇ s`. -/
private lemma mapsTo_id {s t : Set (cubeSpace.{w} m)} (h : s ⊆ t) :
    Set.MapsTo (𝟙 (cubeSpace.{w} m)) s t :=
  fun _ hz ↦ h hz

/-- Following a map of pairs by an enlargement of the target subspace. -/
private lemma ofSubsetMap_comp_ofSubsetMap_id {B : Set (cubeSpace.{w} m)}
    {B' B'' : Set (cubeSpace.{w} m)} (g : cubeSpace.{w} m ⟶ cubeSpace.{w} m)
    (hB : Set.MapsTo g B B') (h : Set.MapsTo (𝟙 (cubeSpace.{w} m)) B' B'')
    (hB'' : Set.MapsTo g B B'') :
    ofSubsetMap g hB ≫ ofSubsetMap (𝟙 _) h = ofSubsetMap g hB'' :=
  (ofSubsetMap_comp g (𝟙 _) hB h hB'').symm

private lemma boundary_subset_inter :
    Set.MapsTo (𝟙 (cubeSpace.{w} m)) (ULift.down ⁻¹' Cube.boundary (Fin m))
      (upperSet i ∩ lowerSet i) :=
  fun _ hz ↦ ⟨Or.inl hz, Or.inl hz⟩

private lemma mapsTo_stretch_quarter :
    Set.MapsTo (stretch.{w} i quarter) (ULift.down ⁻¹' Cube.boundary (Fin m))
      (upperSet i ∩ lowerSet i) := by
  intro z hz
  rcases update_mem_boundary_or i hz (quarter (z.down i)) with h | h | h
  · exact ⟨Or.inl h, Or.inl h⟩
  · exact ⟨Or.inl (update_mem_boundary_of i (Or.inl (Subtype.ext (by simp [h])))),
      Or.inl (update_mem_boundary_of i (Or.inl (Subtype.ext (by simp [h]))))⟩
  · refine ⟨Or.inr ?_, Or.inr ?_⟩ <;>
    · rw [Set.mem_ofPred_eq, stretch_apply_self]
      norm_num [h]

private lemma mapsTo_stretch_upperHalf :
    Set.MapsTo (stretch.{w} i upperHalf) (ULift.down ⁻¹' Cube.boundary (Fin m))
      (upperSet i ∩ lowerSet i) := by
  intro z hz
  rcases update_mem_boundary_or i hz (upperHalf (z.down i)) with h | h | h
  · exact ⟨Or.inl h, Or.inl h⟩
  · refine ⟨Or.inr ?_, Or.inr ?_⟩ <;>
    · rw [Set.mem_ofPred_eq, stretch_apply_self]
      norm_num [h]
  · exact ⟨Or.inl (update_mem_boundary_of i (Or.inr (Subtype.ext (by simp [h])))),
      Or.inl (update_mem_boundary_of i (Or.inr (Subtype.ext (by simp [h]))))⟩

/-- The straight-line homotopy from the identity to the quarter stretch keeps the boundary of the
cube inside `upperSet i`. -/
private lemma stretchHomotopy_quarter_mem_upperSet (τ : I) (z : cubeSpace.{w} m)
    (hz : z ∈ ULift.down ⁻¹' Cube.boundary (Fin m)) :
    stretchHomotopy i quarter (τ, z) ∈ upperSet i := by
  rcases update_mem_boundary_or i hz (Set.Icc.convexComb (z.down i) (quarter (z.down i)) τ)
    with h | h | h
  · exact Or.inl h
  · refine Or.inl (update_mem_boundary_of i (Or.inl (Subtype.ext ?_)))
    simp [h]
  · refine Or.inr ?_
    rw [Set.mem_ofPred_eq, stretchHomotopy_apply, Function.update_self,
      Set.Icc.coe_convexComb, coe_quarter, h, Set.Icc.coe_one]
    linarith [τ.2.2]

/-- The straight-line homotopy from the identity to the upper half stretch keeps the boundary of
the cube inside `lowerSet i`. -/
private lemma stretchHomotopy_upperHalf_mem_lowerSet (τ : I) (z : cubeSpace.{w} m)
    (hz : z ∈ ULift.down ⁻¹' Cube.boundary (Fin m)) :
    stretchHomotopy i upperHalf (τ, z) ∈ lowerSet i := by
  rcases update_mem_boundary_or i hz (Set.Icc.convexComb (z.down i) (upperHalf (z.down i)) τ)
    with h | h | h
  · exact Or.inl h
  · refine Or.inr ?_
    rw [Set.mem_ofPred_eq, stretchHomotopy_apply, Function.update_self,
      Set.Icc.coe_convexComb, coe_upperHalf, h, Set.Icc.coe_zero]
    linarith [τ.2.2]
  · refine Or.inl (update_mem_boundary_of i (Or.inr (Subtype.ext ?_)))
    simp [h]

/-- The upper half stretch lands in `upperSet i`. -/
private lemma stretch_upperHalf_mem_upperSet (z : cubeSpace.{w} m) :
    stretch i upperHalf z ∈ upperSet i := by
  refine Or.inr ?_
  rw [Set.mem_ofPred_eq, stretch_apply_self, coe_upperHalf]
  linarith [(z.down i).2.1]

/-- The quarter stretch lands in `lowerSet i`. -/
private lemma stretch_quarter_mem_lowerSet (z : cubeSpace.{w} m) :
    stretch i quarter z ∈ lowerSet i := by
  refine Or.inr ?_
  rw [Set.mem_ofPred_eq, stretch_apply_self, coe_quarter]
  linarith [(z.down i).2.2]

section Pinch

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

/-- A map of pairs from the cube pair to `(Iᵐ, B)` whose image lies in `B` induces zero on relative
homology. -/
private lemma singularHomologyMap_ofSubsetMap_eq_zero {B : Set (cubeSpace.{w} m)}
    (g : cubeSpace.{w} m ⟶ cubeSpace.{w} m)
    (hB : Set.MapsTo g (ULift.down ⁻¹' Cube.boundary (Fin m)) B) (hg : ∀ z, g z ∈ B) (k : ℕ) :
    (cubeBoundaryPair.{w} m).singularHomologyMap (ofSubsetMap g hB) R k = 0 :=
  singularHomologyMap_eq_zero_of_fac _ R
    (TopCat.ofHom (⟨fun z ↦ ⟨g z, hg z⟩, by fun_prop⟩ : C(cubeSpace.{w} m, B)))
    (by rw [ofSubsetMap_fst]; rfl) k

/-- **The pinch identity.** On `Hₖ(Iᵐ, ∂Iᵐ)`, the map to the relative homology of the cube modulo
its boundary and the slab `1/4 ≤ zᵢ ≤ 1/2` is the sum of the maps induced by the two halves of the
complement of the slab, each parametrised by `stretch`. -/
private theorem singularHomologyMap_inclusion_eq_add (k : ℕ) :
    (cubeBoundaryPair.{w} m).singularHomologyMap
        (ofSubsetMap (𝟙 _) (boundary_subset_inter i) : _ ⟶ slabPair i) R k =
      (cubeBoundaryPair.{w} m).singularHomologyMap
          (ofSubsetMap _ (mapsTo_stretch_quarter i) : _ ⟶ slabPair i) R k +
        (cubeBoundaryPair.{w} m).singularHomologyMap
          (ofSubsetMap _ (mapsTo_stretch_upperHalf i) : _ ⟶ slabPair i) R k := by
  refine singularHomology_inter_hom_ext R (interior_upperSet_union_interior_lowerSet i)
    (mapsTo_id Set.inter_subset_left) (mapsTo_id Set.inter_subset_right) k ?_ ?_
  · -- In `(Iᵐ, upperSet i)`, the identity is homotopic to the quarter stretch, and the upper half
    -- lands in `upperSet i`.
    rw [Preadditive.add_comp, ← singularHomologyMap_comp, ← singularHomologyMap_comp,
      ← singularHomologyMap_comp,
      ofSubsetMap_comp_ofSubsetMap_id (𝟙 _) _ _ (mapsTo_id Set.subset_union_left),
      ofSubsetMap_comp_ofSubsetMap_id (stretch i quarter) _ _
        ((mapsTo_stretch_quarter i).mono_right Set.inter_subset_left),
      ofSubsetMap_comp_ofSubsetMap_id (stretch i upperHalf) _ _
        ((mapsTo_stretch_upperHalf i).mono_right Set.inter_subset_left),
      singularHomologyMap_ofSubsetMap_eq_zero R (stretch i upperHalf) _
        (stretch_upperHalf_mem_upperSet i), add_zero]
    exact (ofSubsetHomotopy (stretchHomotopy i quarter)
      (stretchHomotopy_quarter_mem_upperSet i)).congr_singularHomologyMap R k
  · -- In `(Iᵐ, lowerSet i)`, the identity is homotopic to the upper half stretch, and the quarter
    -- lands in `lowerSet i`.
    rw [Preadditive.add_comp, ← singularHomologyMap_comp, ← singularHomologyMap_comp,
      ← singularHomologyMap_comp,
      ofSubsetMap_comp_ofSubsetMap_id (𝟙 _) _ _ (mapsTo_id Set.subset_union_left),
      ofSubsetMap_comp_ofSubsetMap_id (stretch i quarter) _ _
        ((mapsTo_stretch_quarter i).mono_right Set.inter_subset_right),
      ofSubsetMap_comp_ofSubsetMap_id (stretch i upperHalf) _ _
        ((mapsTo_stretch_upperHalf i).mono_right Set.inter_subset_right),
      singularHomologyMap_ofSubsetMap_eq_zero R (stretch i quarter) _
        (stretch_quarter_mem_lowerSet i), zero_add]
    exact (ofSubsetHomotopy (stretchHomotopy i upperHalf)
      (stretchHomotopy_upperHalf_mem_lowerSet i)).congr_singularHomologyMap R k

end Pinch

section FatConcatenation

variable {X : Type w} [TopologicalSpace X] {x : X}

/-- On the first half of the `i`-th direction, `transAt i f g` runs `f` at double speed. -/
private lemma transAt_apply_of_le (f g : Ω^ (Fin m) X x) {t : I^(Fin m)}
    (h : (t i : ℝ) ≤ 1 / 2) {a : I} (ha : (a : ℝ) = 2 * t i) :
    GenLoop.transAt i f g t = f (Function.update t i a) := by
  simp only [GenLoop.transAt, GenLoop.coe_copy]
  rw [ite_eq_left h, Set.projIcc_of_mem _ ⟨by rw [← ha]; exact a.2.1,
    by rw [← ha]; exact a.2.2⟩]
  exact congrArg (fun b ↦ f (Function.update t i b)) (Subtype.ext ha.symm)

/-- On the second half of the `i`-th direction, `transAt i f g` runs `g` at double speed. -/
private lemma transAt_apply_of_lt (f g : Ω^ (Fin m) X x) {t : I^(Fin m)}
    (h : 1 / 2 < (t i : ℝ)) {a : I} (ha : (a : ℝ) = 2 * t i - 1) :
    GenLoop.transAt i f g t = g (Function.update t i a) := by
  simp only [GenLoop.transAt, GenLoop.coe_copy]
  rw [ite_eq_right (not_le.2 h), Set.projIcc_of_mem _ ⟨by rw [← ha]; exact a.2.1,
    by rw [← ha]; exact a.2.2⟩]
  exact congrArg (fun b ↦ g (Function.update t i b)) (Subtype.ext ha.symm)

/-- The concatenation of `p`, a constant piece and `q` along the `i`-th direction: `p` is run on
`zᵢ ≤ 1/4`, the slab `1/4 ≤ zᵢ ≤ 1/2` goes to the base point, and `q` is run on `zᵢ ≥ 1/2`.  It
represents the product `[q] * [p]`. -/
private def fatTrans (p q : Ω^ (Fin m) X x) : Ω^ (Fin m) X x :=
  GenLoop.transAt i (GenLoop.transAt i p GenLoop.const) q

/-- The fat concatenation sends the boundary of the cube and the slab to the base point. -/
private lemma fatTrans_apply_of_mem (p q : Ω^ (Fin m) X x) {z : cubeSpace.{w} m}
    (hz : z ∈ upperSet i ∩ lowerSet i) : fatTrans i p q z.down = x := by
  obtain ⟨hU | hU, hV | hV⟩ := hz
  · exact GenLoop.boundary _ _ hU
  · exact GenLoop.boundary _ _ hU
  · exact GenLoop.boundary _ _ hV
  rw [Set.mem_ofPred_eq] at hU hV
  have h₂ : 2 * (z.down i : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  rw [fatTrans, transAt_apply_of_le i _ _ hV (a := ⟨_, h₂⟩) rfl]
  by_cases h : 2 * (z.down i : ℝ) ≤ 1 / 2
  · rw [transAt_apply_of_le i _ _ (by simpa using h) (a := 1)
      (by simp only [Function.update_self, Set.Icc.coe_one]; linarith), Function.update_idem]
    exact GenLoop.boundary _ _ (update_mem_boundary_of i (Or.inr rfl))
  · rw [transAt_apply_of_lt i _ _ (by simpa using not_le.1 h)
      (a := ⟨4 * z.down i - 1, by constructor <;> linarith⟩) (by simp; ring)]
    exact GenLoop.const_apply

/-- On the first quarter, read through `stretch i quarter`, the fat concatenation is `p`. -/
private lemma fatTrans_stretch_quarter (p q : Ω^ (Fin m) X x) (z : cubeSpace.{w} m) :
    fatTrans i p q (stretch i quarter z).down = p z.down := by
  have hs := (z.down i).2
  have h₂ : (z.down i : ℝ) / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  rw [fatTrans, transAt_apply_of_le i _ _ (a := ⟨_, h₂⟩)
      (by rw [stretch_apply_self, coe_quarter]; linarith [hs.2])
      (by rw [stretch_apply_self, coe_quarter]; ring),
    stretch_apply, Function.update_idem,
    transAt_apply_of_le i _ _ (a := z.down i) (by simp; linarith [hs.2]) (by simp; ring),
    Function.update_idem, Function.update_eq_self]

/-- On the upper half, read through `stretch i upperHalf`, the fat concatenation is `q`. -/
private lemma fatTrans_stretch_upperHalf (p q : Ω^ (Fin m) X x) (z : cubeSpace.{w} m) :
    fatTrans i p q (stretch i upperHalf z).down = q z.down := by
  have hs := (z.down i).2
  rcases hs.1.eq_or_lt with h₀ | h₀
  · -- On the face `zᵢ = 0` both loops are at the base point.
    have hz : z.down i = 0 := Subtype.ext h₀.symm
    rw [GenLoop.boundary q _ ⟨i, Or.inl hz⟩, fatTrans,
      transAt_apply_of_le i _ _ (a := 1) (by rw [stretch_apply_self, coe_upperHalf, hz]; norm_num)
        (by rw [stretch_apply_self, coe_upperHalf, hz]; norm_num),
      transAt_apply_of_lt i _ _ (a := 1) (by norm_num) (by norm_num)]
    exact GenLoop.const_apply
  · rw [fatTrans, transAt_apply_of_lt i _ _ (a := z.down i)
        (by rw [stretch_apply_self, coe_upperHalf]; linarith)
        (by rw [stretch_apply_self, coe_upperHalf]; ring),
      stretch_apply, Function.update_idem, Function.update_eq_self]

end FatConcatenation

end Hurewicz

end TauCeti

namespace GenLoop

open TauCeti TauCeti.Hurewicz TopPair

variable {X : Type w} [TopologicalSpace X] {x : X}
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) {n : ℕ}

/-- The Hurewicz class of the fat concatenation of `p` and `q` is the sum of their Hurewicz
classes: the fat concatenation is a map of pairs from the cube modulo its boundary and the slab,
whose restrictions to the two halves are `p` and `q`, so this is the pinch identity
`TauCeti.Hurewicz.singularHomologyMap_inclusion_eq_add` pushed forward to `X`. -/
private lemma hurewicz_fatTrans (p q : Ω^ (Fin (n + 1)) X x) :
    hurewicz R (fatTrans 0 p q) = hurewicz R p + hurewicz R q := by
  let F : cubeSpace.{w} (n + 1) ⟶ TopCat.of X :=
    TopCat.ofHom ((fatTrans 0 p q).1.comp ⟨ULift.down, continuous_uliftDown⟩)
  have hF : Set.MapsTo F (upperSet 0 ∩ lowerSet 0) {x} :=
    fun _ hz ↦ fatTrans_apply_of_mem 0 p q hz
  have h₁ : toCubeBoundaryPairHom (fatTrans 0 p q) =
      ofSubsetMap (𝟙 _) (boundary_subset_inter 0) ≫ ofSubsetMap F hF :=
    ofSubsetMap_comp (𝟙 _) F (boundary_subset_inter 0) hF (hF.comp (boundary_subset_inter 0))
  have h₂ : toCubeBoundaryPairHom p =
      ofSubsetMap (stretch 0 quarter) (mapsTo_stretch_quarter 0) ≫ ofSubsetMap F hF :=
    calc toCubeBoundaryPairHom p
        _ = ofSubsetMap (stretch 0 quarter ≫ F) (hF.comp (mapsTo_stretch_quarter 0)) := by
          rw [toCubeBoundaryPairHom]
          congr 1
          ext z
          exact (fatTrans_stretch_quarter 0 p q z).symm
        _ = _ := ofSubsetMap_comp _ _ _ _ _
  have h₃ : toCubeBoundaryPairHom q =
      ofSubsetMap (stretch 0 upperHalf) (mapsTo_stretch_upperHalf 0) ≫ ofSubsetMap F hF :=
    calc toCubeBoundaryPairHom q
        _ = ofSubsetMap (stretch 0 upperHalf ≫ F) (hF.comp (mapsTo_stretch_upperHalf 0)) := by
          rw [toCubeBoundaryPairHom]
          congr 1
          ext z
          exact (fatTrans_stretch_upperHalf 0 p q z).symm
        _ = _ := ofSubsetMap_comp _ _ _ _ _
  simp only [hurewicz, h₁, h₂, h₃, singularHomologyMap_comp,
    singularHomologyMap_inclusion_eq_add, Preadditive.add_comp, Preadditive.comp_add]

end GenLoop

namespace HomotopyGroup

open TauCeti

variable {X : Type w} [TopologicalSpace X] {x : X}
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)

/-- **The Hurewicz map is additive**: it sends a product of homotopy classes to the sum of their
Hurewicz classes. -/
@[simp]
theorem hurewicz_mul (a b : HomotopyGroup (Fin (n + 1)) X x) :
    hurewicz R n (a * b) = hurewicz R n a + hurewicz R n b := by
  refine Quotient.inductionOn₂ a b fun q p ↦ ?_
  -- `[q] * [p]` is the class of the fat concatenation, which runs `p` and then `q`.
  have hp : (⟦GenLoop.transAt 0 p GenLoop.const⟧ : HomotopyGroup (Fin (n + 1)) X x) = ⟦p⟧ := by
    rw [← HomotopyGroup.mul_spec, ← HomotopyGroup.one_def]
    exact one_mul (M := HomotopyGroup (Fin (n + 1)) X x) _
  rw [hurewicz_mk, hurewicz_mk, add_comm (GenLoop.hurewicz R q), ← GenLoop.hurewicz_fatTrans,
    ← hurewicz_mk, Hurewicz.fatTrans, ← HomotopyGroup.mul_spec, hp]

/-- The Hurewicz map sends the inverse of a class to the negative of its Hurewicz class. -/
@[simp]
theorem hurewicz_inv (a : HomotopyGroup (Fin (n + 1)) X x) :
    hurewicz R n a⁻¹ = -hurewicz R n a :=
  eq_neg_of_add_eq_zero_left (by rw [← hurewicz_mul, inv_mul_cancel, hurewicz_one])

/-- **The Hurewicz homomorphism** `π_{n+1}(X, x) → (R ⟶ Hₙ₊₁(X; R))`, from the homotopy group,
written additively, to the group of morphisms from `R` to singular homology. -/
def hurewiczHom :
    Additive (HomotopyGroup (Fin (n + 1)) X x) →+
      (R ⟶ ((singularHomologyFunctor C (n + 1)).obj R).obj (TopCat.of X)) where
  toFun a := hurewicz R n a.toMul
  map_zero' := hurewicz_one R n
  map_add' a b := hurewicz_mul R n a.toMul b.toMul

@[simp]
lemma hurewiczHom_apply (a : Additive (HomotopyGroup (Fin (n + 1)) X x)) :
    hurewiczHom R n a = hurewicz R n a.toMul :=
  (rfl)

end HomotopyGroup
