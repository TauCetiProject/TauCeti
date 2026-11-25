/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.Basic
public import Mathlib.Topology.Homotopy.Affine
public import TauCeti.AlgebraicTopology.Singular.Empty
public import TauCeti.AlgebraicTopology.Singular.Fibration.Deformation
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.SubspaceCompl
public import TauCeti.AlgebraicTopology.Singular.Triple
public import TauCeti.Analysis.Convex.Star
public import TauCeti.Topology.Category.TopCat.Fiber
public import TauCeti.Topology.Homotopy.PuncturedStarConvex

/-!
# Homology of a Serre fibration over a disk, relative to the boundary sphere

Let `p : E → K` be a Serre fibration whose base `K` is a convex neighbourhood of `0` in a real
normed space `V` of finite dimension `r`, and let `F = p⁻¹(0)` be the fibre over `0`. This file
computes the relative singular homology of `E` modulo the part of `E` over `K ∖ {0}`, with
coefficients in a module `M` over a ring `R`:

* `Hₘ(E, p⁻¹(K ∖ {0}); M) = 0` for `m < r`
  (`TauCeti.TopCat.isZero_singularHomology_preimage_ne_zero`);
* `Hₙ₊ᵣ(E, p⁻¹(K ∖ {0}); M) ≅ Hₙ(F; M)`
  (`TauCeti.TopCat.singularHomologyPreimageNeZeroIso`).

For the closed unit ball `Dʳ` of `V`, the part of `E` over the punctured ball and the part over the
unit sphere `Sʳ⁻¹` have the same homology, since the punctured ball deforms radially onto the
sphere. Hence, for a Serre fibration `p : E → Dʳ`,

* `Hₘ(E, p⁻¹(Sʳ⁻¹); M) = 0` for `m < r`
  (`TauCeti.TopCat.isZero_singularHomology_preimage_sphere`);
* `Hₙ₊ᵣ(E, p⁻¹(Sʳ⁻¹); M) ≅ Hₙ(F; M)` (`TauCeti.TopCat.singularHomologyPreimageSphereIso`).

This is the computation over a single cell behind the first page of the Serre spectral sequence
of a fibration over a CW complex: pulled back along the characteristic map of an `r`-cell, the
fibration becomes a Serre fibration over `Dʳ`, and the relative homology of the cell's part of the
filtration is the homology of the fibre, shifted by `r`. For the product bundle `B × V → V` the
same computation is `TauCeti.prodThomPairSingularHomologyIso`.

## The argument

Everything rests on one vanishing statement for an arbitrary base `B`
(`TauCeti.TopCat.isZero_singularHomology_preimage_of_deformation`): if `B` deforms into `A ⊆ B`
in the weak sense (by a homotopy starting at the identity, ending in `A`, and keeping `A` in `A`),
then `H_*(E, p⁻¹(A); M) = 0`.

The computation then removes one dimension at a time, along the extensions `W ⊆ W'` of
`Submodule.LineExtension`: `W' = W ⊕ ℝv` with a functional `φ` on `W'` whose kernel is `W` and
which is `1` at `v`. The part of `E` over `K ∖ W` is the union of the open parts over the
complements in `K` of the two closed half-subspaces `{x ∈ W' | ±φ x ≤ 0}`, which intersect in the
part over `K ∖ W'`. Each of these complements is star-convex about a small positive multiple of
`±v`, so `K` deforms into it along straight lines (`ContinuousMap.Homotopy.affine`), and `E`
modulo the part over it is acyclic. The relative Mayer–Vietoris sequence then gives
`Hₙ₊₁(E, p⁻¹(K ∖ W)) ≅ Hₙ(E, p⁻¹(K ∖ W'))`; this chain of steps is the general computation
`TauCeti.subspaceComplPairSingularHomologyIso`, applied to the composite `E → K → V`. After `r`
steps from `W = 0` the subspace is all of
`V`, the part of `E` over `K ∖ V` is empty, and `Hₙ(E) ≅ Hₙ(F)` because `K` contracts onto `0`
along straight lines. Over the closed unit ball, the radial deformation
`StarConvex.radialHomotopy` of the punctured ball onto the sphere passes from `K ∖ {0}` to
`Sʳ⁻¹`.

## Main results

* `TauCeti.TopCat.isZero_singularHomology_preimage_of_starConvex`,
  `TauCeti.TopCat.isZero_singularHomology_preimage_compl_setOf_mem_and_nonpos`,
  `TauCeti.TopCat.isZero_singularHomology_preimage_ne_zero_preimage_sphere`: the acyclic pairs from
  which the computation is assembled, also used for the cohomological computation
  `TauCeti.TopCat.singularCohomologyPreimageSphereIso`.
* `TauCeti.TopCat.SerreDisk.proj`, `TauCeti.TopCat.SerreDisk.pair`,
  `TauCeti.TopCat.SerreDisk.botIso` and their naturality
  `TauCeti.TopCat.SerreDisk.proj_apply_of_comp_eq`,
  `TauCeti.TopCat.SerreDisk.botIso_hom_naturality`: the projection `E → K → V` and the pairs it
  defines, shared with the cohomological computation.
* `TauCeti.TopCat.isZero_singularHomology_preimage_ne_zero`,
  `TauCeti.TopCat.singularHomologyPreimageNeZeroIso`: the relative homology of `E` modulo the part
  over `K ∖ {0}`.
* `TauCeti.TopCat.isZero_singularHomology_preimage_sphere`,
  `TauCeti.TopCat.singularHomologyPreimageSphereIso`: the relative homology of `E` modulo the part
  over the boundary sphere, for a Serre fibration over the closed unit ball.
* `TauCeti.TopCat.singularHomologyPreimageNeZeroIso_hom_naturality`,
  `TauCeti.TopCat.singularHomologyPreimageSphereIso_hom_naturality`: both isomorphisms are natural
  in maps of fibrations over the base, which induce the maps of the fibres over `0`.
* `TauCeti.TopCat.singularHomologyPreimageNeZeroRelIso`: the same computation relative to an open
  set `A ⊆ E`, `Hₘ(E, A ∪ p⁻¹(K ∖ {0}); M) ≅ Hₙ(E, A; M)`, when `E` is acyclic modulo `A` and the
  part over the complement of every closed half-subspace.
* `TauCeti.TopCat.singularHomologyPreimageNeZeroIso_hom_comp_homologyMap_comp_singularHomologyπ`:
  it is compatible with `TauCeti.TopCat.singularHomologyPreimageNeZeroIso` through the inclusion
  of the fibre and the map `Hₙ(E) → Hₙ(E, A)`.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.D, the proof of Theorem 4D.10.
* A. Hatcher,
  [*Spectral Sequences in Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/SSAT/SSch1.pdf),
  Chapter 1, Section 1.1 (the homology spectral sequence).
-/

public section

noncomputable section

open CategoryTheory Limits Module Metric Set Topology
open scoped unitInterval

universe u

namespace TauCeti

namespace TopCat

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {K : Set V}
  {E : _root_.TopCat.{u}} {p : E ⟶ _root_.TopCat.of K} {R : Type*} [Ring R] (M : ModuleCat.{u} R)

/-- **A Serre fibration over a convex set is acyclic modulo the part over a star-convex set.** Let
`p : E ⟶ K` be a Serre fibration over a convex set `K`, and `S ⊆ V` star-convex about a point
`c ∈ K ∩ S`. Then `Hₘ(E, p⁻¹(K ∩ S); M) = 0` for every `m`: `K` deforms into `K ∩ S` along straight
lines towards `c`. -/
theorem isZero_singularHomology_preimage_of_starConvex (hp : serreFibrations p) (hK : Convex ℝ K)
    {c : V} (hc : c ∈ K) {S : Set V} (hS : StarConvex ℝ c S) (hcS : c ∈ S) (m : ℕ) :
    IsZero ((TopPair.ofSubset (p ⁻¹' {x : K | (x : V) ∈ S})).singularHomology M m) :=
  let G := ContinuousMap.Homotopy.affine ⟨((↑) : K → V), continuous_subtypeVal⟩ (.const K c)
  isZero_singularHomology_preimage_of_deformation hp
    ⟨fun q ↦ ⟨G q, hK.lineMap_mem q.2.property hc q.1.property⟩, by fun_prop⟩
    (fun x ↦ Subtype.ext (by simp [G]))
    (fun x ↦ by simpa [G] using hcS)
    (fun t x hx ↦ by
      simp only [mem_ofPred_eq, ContinuousMap.coe_mk, G, ContinuousMap.Homotopy.affine_apply,
        AffineMap.lineMap_apply_module] at hx ⊢
      rw [add_comm]
      exact hS hx t.property.1 (sub_nonneg.2 t.property.2) (add_sub_cancel _ _)) M m

/-- **A Serre fibration over a convex neighbourhood of `0` is acyclic modulo the part over the
complement of a closed half-subspace.** Let `p : E ⟶ K` be a Serre fibration over a convex
neighbourhood `K` of `0`, `W` a subspace of `V` and `φ` a functional with `φ v = 1` for some
`v ∈ W`. Then `Hₘ(E, p⁻¹(K ∖ {y ∈ W | φ y ≤ 0}); M) = 0` for every `m`: the complement of the
closed half-subspace is star-convex about a point of `K` on the open half-line through `v`. -/
theorem isZero_singularHomology_preimage_compl_setOf_mem_and_nonpos (hp : serreFibrations p)
    (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V)) (W : Submodule ℝ V) (φ : V →ₗ[ℝ] ℝ) (v : V)
    (hv : v ∈ W) (hφv : φ v = 1) (m : ℕ) :
    IsZero ((TopPair.ofSubset
      (p ⁻¹' {x : K | (x : V) ∈ {y | y ∈ W ∧ φ y ≤ 0}ᶜ})).singularHomology M m) := by
  obtain ⟨c, hcK, hcS, hS⟩ :=
    exists_mem_starConvex_compl_setOf_mem_and_nonpos hK₀ hv (hφv ▸ one_pos)
  exact isZero_singularHomology_preimage_of_starConvex M hp hK hcK hS hcS m

namespace SerreDisk

/-- The composite `E → K → V` of the fibration with the inclusion of the base. The preimage
under it of a set `S ⊆ V` is the part of `E` over `K ∩ S`
(`TauCeti.TopCat.SerreDisk.preimage_proj`). -/
abbrev proj (p : E ⟶ _root_.TopCat.of K) : C(E, V) :=
  ⟨fun e ↦ (p e : V), continuous_subtypeVal.comp p.hom.continuous⟩

omit [NormedSpace ℝ V] in
/-- The projection `E → K → V` sends a point of `E` to its image in the base, read in `V`. -/
lemma proj_apply (p : E ⟶ _root_.TopCat.of K) (e : E) : proj p e = p e :=
  (rfl)

omit [NormedSpace ℝ V] in
/-- The preimage of a set `S ⊆ V` under the projection `E → K → V` is the part of `E` over
`K ∩ S`. -/
lemma preimage_proj (p : E ⟶ _root_.TopCat.of K) (S : Set V) :
    proj p ⁻¹' S = p ⁻¹' {x : K | (x : V) ∈ S} :=
  (rfl)

/-- The pair `(E, p⁻¹(K ∖ W))`. -/
abbrev pair (p : E ⟶ _root_.TopCat.of K) (W : Submodule ℝ V) : TopPair.{u} :=
  subspaceComplPair (proj p) ∅ W

/-- The acyclicity hypothesis of `TauCeti.subspaceComplPairSingularHomologyIso` for the pairs
`pair p`, with `A = ∅`. -/
private lemma isZero_half (hp : serreFibrations p) (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V))
    (W : Submodule ℝ V) (φ : V →ₗ[ℝ] ℝ) (v : V) (hv : v ∈ W) (hφv : φ v = 1) (m : ℕ) :
    IsZero ((TopPair.ofSubset (∅ ∪ proj p ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ)).singularHomology
      M m) := by
  rw [Set.empty_union, preimage_proj]
  exact isZero_singularHomology_preimage_compl_setOf_mem_and_nonpos M hp hK hK₀ W φ v hv hφv m

/-- `Hₙ(E, ∅) ≅ Hₙ(F)`: the base contracts onto `0` along straight lines, so the inclusion of the
fibre over `0` is a homology isomorphism. -/
private def emptyIso (hp : serreFibrations p) (hK : Convex ℝ K) (h₀ : (0 : V) ∈ K) (n : ℕ) :
    (pair p (⊤ : Submodule ℝ V)).singularHomology M n ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        M).obj (_root_.TopCat.of (p ⁻¹' {x : K | (x : V) = 0})) :=
  have h (m : ℕ) := isZero_singularHomology_preimage_of_starConvex M hp hK h₀
    (starConvex_singleton (0 : V)) rfl m
  haveI := TopPair.isIso_homologyMap_map_of_isZero _ _ (h (n + 1)) (h n)
  (asIso ((pair p (⊤ : Submodule ℝ V)).singularHomologyπ M n)).symm ≪≫
    (asIso (SSet.homologyMap (TopCat.toSSet.map
      (TopPair.ofSubset (p ⁻¹' {x : K | (x : V) ∈ ({0} : Set V)})).map)
      M n)).symm

/-- The inclusion of the fibre over `0` followed by `Hₙ(E) ⟶ Hₙ(E, ∅)` is the inverse of
`emptyIso`. -/
@[reassoc]
private lemma homologyMap_comp_singularHomologyπ_eq_emptyIso_inv (hp : serreFibrations p)
    (hK : Convex ℝ K) (h₀ : (0 : V) ∈ K) (n : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map (TopPair.ofSubset (p ⁻¹' {x : K | (x : V) = 0})).map)
        M n ≫ (pair p (⊤ : Submodule ℝ V)).singularHomologyπ M n =
      (emptyIso M hp hK h₀ n).inv :=
  -- `emptyIso` is defined as the inverse of this composite; its fibre `{x | x ∈ {0}}` is
  -- `{x | x = 0}` by definition of membership in a singleton.
  rfl

/-- The identification of `(E, p⁻¹(K ∖ {0}))` with `(E, p⁻¹(K ∖ ⊥))`. -/
def botIso (p : E ⟶ _root_.TopCat.of K) :
    TopPair.ofSubset (p ⁻¹' {x : K | (x : V) ≠ 0}) ≅ pair p (⊥ : Submodule ℝ V) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun e ↦ by
    simp only [mem_preimage, mem_ofPred_eq, mem_compl_iff, SetLike.mem_coe, Submodule.mem_bot,
      empty_union]
    rfl

end SerreDisk

open SerreDisk

variable [FiniteDimensional ℝ V]

/-- **A Serre fibration over a convex neighbourhood of `0` has vanishing homology modulo the part
over the punctured base, below the dimension.** Let `K` be a convex neighbourhood of `0` in a
finite-dimensional real normed space `V`, and let `p : E ⟶ K` be a Serre fibration. Then
`Hₘ(E, p⁻¹(K ∖ {0}); M) = 0` for every `m < dim V`. -/
theorem isZero_singularHomology_preimage_ne_zero (hp : serreFibrations p) (hK : Convex ℝ K)
    (hK₀ : K ∈ 𝓝 (0 : V)) {m : ℕ} (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (p ⁻¹' {x : K | (x : V) ≠ 0})).singularHomology M m) :=
  (isZero_singularHomology_subspaceComplPair M (proj p) ∅ isOpen_empty
    (isZero_half M hp hK hK₀) m ⊥ (by simpa using hm)).of_iso
    (asIso (TopPair.singularHomologyMap (botIso p).hom M m))

/-- **The homology of a Serre fibration over a convex neighbourhood of `0`, modulo the part over
the punctured base, is the shifted homology of the fibre over `0`.** Let `K` be a convex
neighbourhood of `0` in a real normed space `V` of finite dimension `r`, and let `p : E ⟶ K` be a
Serre fibration. Then `Hₘ(E, p⁻¹(K ∖ {0}); M) ≅ Hₙ(p⁻¹(0); M)` for `m = n + r`.

The isomorphism is the composite of `r` relative Mayer–Vietoris connecting morphisms, for a fixed
choice of a flag of subspaces of `V` (`Submodule.lineExtension`), followed by the inverse of the
homology isomorphism induced by the inclusion of the fibre. -/
def singularHomologyPreimageNeZeroIso (hp : serreFibrations p) (hK : Convex ℝ K)
    (hK₀ : K ∈ 𝓝 (0 : V)) (n m : ℕ) (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset (p ⁻¹' {x : K | (x : V) ≠ 0})).singularHomology M m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        M).obj (_root_.TopCat.of (p ⁻¹' {x : K | (x : V) = 0})) :=
  asIso (TopPair.singularHomologyMap (botIso p).hom M m) ≪≫
    subspaceComplPairSingularHomologyIso M (proj p) ∅ isOpen_empty
      (isZero_half M hp hK hK₀) (finrank ℝ V) ⊥ (by simp) n m h ≪≫
    emptyIso M hp hK (mem_of_mem_nhds hK₀) n

section Sphere

variable {p : E ⟶ _root_.TopCat.of (closedBall (0 : V) 1)}

/-- The punctured closed unit ball, as a subset of the closed unit ball. -/
private abbrev puncturedBall : Set (closedBall (0 : V) 1) := {x | (x : V) ≠ 0}

/-- The unit sphere, as a subset of the closed unit ball. -/
private abbrev unitSphere : Set (closedBall (0 : V) 1) := {x | (x : V) ∈ sphere (0 : V) 1}

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The part of `E` over the unit sphere lies in the part over the punctured closed unit ball. -/
lemma preimage_sphere_subset_preimage_ne_zero
    (p : E ⟶ _root_.TopCat.of (closedBall (0 : V) 1)) :
    p ⁻¹' {x | (x : V) ∈ sphere (0 : V) 1} ⊆ p ⁻¹' {x | (x : V) ≠ 0} :=
  preimage_mono fun _ hx h ↦ by simp [h] at hx

/-- The radial deformation of the punctured closed unit ball onto the unit sphere: the
straight-line homotopy `StarConvex.radialHomotopy` from the radial projection to the identity, run
backwards and read on the punctured ball as a subset of the closed unit ball. -/
private def radial : C(I × _root_.TopCat.of (puncturedBall (V := V)),
    _root_.TopCat.of (puncturedBall (V := V))) :=
  let H := ((convex_closedBall (0 : V) 1).starConvex
    (mem_closedBall_self zero_le_one)).radialHomotopy one_pos sphere_subset_closedBall
  { toFun q := ⟨⟨H.symm (q.1, ⟨q.2, q.2.val.property, q.2.property⟩), (H.symm _).property.1⟩,
      (H.symm _).property.2⟩
    continuous_toFun := by fun_prop }

omit [FiniteDimensional ℝ V] in
/-- **A Serre fibration over a disk is acyclic over the punctured disk modulo the part over the
boundary sphere.** Let `p : E ⟶ Dʳ` be a Serre fibration over the closed unit ball. Then
`Hₘ(p⁻¹(Dʳ ∖ {0}), p⁻¹(Sʳ⁻¹); M) = 0` for every `m`: the punctured ball deforms radially onto the
sphere. -/
theorem isZero_singularHomology_preimage_ne_zero_preimage_sphere (hp : serreFibrations p)
    (m : ℕ) :
    IsZero ((TopTriple.innerPair.obj
      (TopTriple.ofSubset (preimage_sphere_subset_preimage_ne_zero p))).singularHomology M m) := by
  have hz := isZero_singularHomology_preimage_of_deformation
    (mem_serreFibrations_restrictPreimage hp puncturedBall)
    (A := Subtype.val ⁻¹' unitSphere) radial
    (fun x ↦ by ext; simp [radial])
    (fun x ↦ by
      rw [mem_preimage, mem_ofPred_eq]
      simp [radial, ContinuousMap.Homotopy.symm_apply, norm_smul, (norm_pos_iff.2 x.property).ne'])
    (fun t x hx ↦ by
      rw [mem_preimage, mem_ofPred_eq] at hx ⊢
      have hx' : ‖(x : V)‖ = 1 := mem_sphere_zero_iff_norm.1 hx
      simp [radial, hx']) M m
  exact hz.of_iso (asIso (TopPair.singularHomologyMap
    (TopPair.ofSubsetPreimageValIso (X := E) (preimage_sphere_subset_preimage_ne_zero p)).hom M
      m)).symm

omit [FiniteDimensional ℝ V] in
private lemma isIso_totalToOuter (hp : serreFibrations p) (m : ℕ) :
    IsIso (TopPair.singularHomologyMap (TopTriple.totalToOuter.app (TopTriple.ofSubset
      (preimage_sphere_subset_preimage_ne_zero p))) M m) :=
  TopTriple.isIso_singularHomologyMap_totalToOuter_of_isZero _ _ m
    (isZero_singularHomology_preimage_ne_zero_preimage_sphere M hp m)
    fun m' _ ↦ isZero_singularHomology_preimage_ne_zero_preimage_sphere M hp m'

omit [FiniteDimensional ℝ V] in
/-- **Over a disk, the part over the boundary sphere and the part off the centre have the same
relative homology.** For a Serre fibration `p : E ⟶ Dʳ` over the closed unit ball, the inclusion
`(E, p⁻¹(Sʳ⁻¹)) ⟶ (E, p⁻¹(Dʳ ∖ {0}))` induces isomorphisms on relative singular homology, with
coefficients in any module `M`. -/
theorem isIso_singularHomologyMap_ofSubsetMap_preimage_sphere (hp : serreFibrations p) (m : ℕ) :
    IsIso (TopPair.singularHomologyMap
      (TopPair.ofSubsetMap (B := p ⁻¹' {x | (x : V) ∈ sphere (0 : V) 1})
        (B' := p ⁻¹' {x | (x : V) ≠ 0}) (𝟙 E) fun _ hx ↦ ne_of_mem_sphere hx one_ne_zero)
      M m) := by
  have := isIso_totalToOuter M hp m
  rwa [TopTriple.totalToOuter_app_ofSubset] at this

/-- **A Serre fibration over a disk has vanishing homology modulo the part over the boundary
sphere, below the dimension.** Let `p : E ⟶ Dʳ` be a Serre fibration over the closed unit ball of
a real normed space of finite dimension `r`. Then `Hₘ(E, p⁻¹(Sʳ⁻¹); M) = 0` for every `m < r`. -/
theorem isZero_singularHomology_preimage_sphere (hp : serreFibrations p) {m : ℕ}
    (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (p ⁻¹' {x | (x : V) ∈ sphere (0 : V) 1})).singularHomology M m) :=
  (isZero_singularHomology_preimage_ne_zero M hp (convex_closedBall 0 1)
    (closedBall_mem_nhds 0 one_pos) hm).of_iso
    (@asIso _ _ _ _ _ (isIso_totalToOuter M hp m))

/-- **The homology of a Serre fibration over a disk, modulo the part over the boundary sphere, is
the shifted homology of the fibre over the centre.** Let `p : E ⟶ Dʳ` be a Serre fibration over
the closed unit ball of a real normed space of finite dimension `r`. Then
`Hₘ(E, p⁻¹(Sʳ⁻¹); M) ≅ Hₙ(p⁻¹(0); M)` for `m = n + r`.

The isomorphism is the map induced by the inclusion `(E, p⁻¹(Sʳ⁻¹)) ⟶ (E, p⁻¹(Dʳ ∖ {0}))`
followed by `TauCeti.TopCat.singularHomologyPreimageNeZeroIso`. -/
def singularHomologyPreimageSphereIso (hp : serreFibrations p) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset (p ⁻¹' {x | (x : V) ∈ sphere (0 : V) 1})).singularHomology M m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        M).obj (_root_.TopCat.of (p ⁻¹' {x | (x : V) = 0})) :=
  @asIso _ _ _ _ _ (isIso_totalToOuter M hp m) ≪≫
    singularHomologyPreimageNeZeroIso M hp (convex_closedBall 0 1)
      (closedBall_mem_nhds 0 one_pos) n m h

end Sphere

/-! ### Naturality in maps of fibrations -/

section Naturality

variable {E' : _root_.TopCat.{u}}

namespace SerreDisk

variable {p' : E' ⟶ _root_.TopCat.of K} {f : E ⟶ E'}

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A map `f` over the base commutes with the projections `E → K → V` and `E' → K → V`. -/
lemma proj_apply_of_comp_eq (hf : f ≫ p' = p) (e : E) : proj p' (f e) = proj p e :=
  congrArg Subtype.val (ConcreteCategory.congr_hom hf e)

/-- The map of pairs `(E, p⁻¹(K ∖ W)) ⟶ (E', p'⁻¹(K ∖ W))` induced by a map `f` over `K`. -/
private abbrev pairMap (hf : f ≫ p' = p) (W : Submodule ℝ V) : pair p W ⟶ pair p' W :=
  subspaceComplPairMap f (proj_apply_of_comp_eq hf) (mapsTo_empty _ _) W

omit [FiniteDimensional ℝ V] in
private lemma emptyIso_hom_naturality (hp : serreFibrations p) (hp' : serreFibrations p')
    (hK : Convex ℝ K) (h₀ : (0 : V) ∈ K) (hf : f ≫ p' = p)
    (g : _root_.TopCat.of (p ⁻¹' {x : K | (x : V) = 0}) ⟶
      _root_.TopCat.of (p' ⁻¹' {x : K | (x : V) = 0}))
    (hg : ∀ x, (g x : E') = f x) (n : ℕ) :
    (emptyIso M hp hK h₀ n).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map g =
      TopPair.singularHomologyMap (pairMap hf ⊤) M n ≫ (emptyIso M hp' hK h₀ n).hom := by
  let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M
  let ι := (TopPair.ofSubset (p ⁻¹' {x : K | (x : V) ∈ ({0} : Set V)})).map
  let ι' := (TopPair.ofSubset (p' ⁻¹' {x : K | (x : V) ∈ ({0} : Set V)})).map
  -- On the fibres, `g` followed by the inclusion is the inclusion followed by `f`.
  have hgι : g ≫ ι' = ι ≫ f := by
    ext x
    exact hg x
  have hH : H.map g ≫ H.map ι' = H.map ι ≫ H.map f := ((CommSq.mk hgι).map H).w
  have hπ := TopPair.singularHomologyπ_naturality
    (pairMap hf (⊤ : Submodule ℝ V)) M n
  rw [subspaceComplPairMap_fst] at hπ
  -- `emptyIso` is the inverse of `H.map ι` followed by `π`; chase the square of `g` and `f`
  -- through the inclusions, then use the naturality of `π`.
  have key : H.map g ≫ (emptyIso M hp' hK h₀ n).inv =
      (emptyIso M hp hK h₀ n).inv ≫
        TopPair.singularHomologyMap (pairMap hf ⊤) M n :=
    calc H.map g ≫ (emptyIso M hp' hK h₀ n).inv
        = H.map g ≫ H.map ι' ≫
            (pair p' (⊤ : Submodule ℝ V)).singularHomologyπ M n :=
          congrArg (H.map g ≫ ·)
            (homologyMap_comp_singularHomologyπ_eq_emptyIso_inv M hp' hK h₀ n).symm
      _ = (H.map ι ≫ H.map f ≫
            (pair p' (⊤ : Submodule ℝ V)).singularHomologyπ M n :
              H.obj (_root_.TopCat.of (p ⁻¹' {x : K | (x : V) = 0})) ⟶ _) :=
          ((reassoc_of% hH) _).trans (Category.assoc _ _ _)
      _ = (H.map ι ≫ (pair p (⊤ : Submodule ℝ V)).singularHomologyπ M n ≫
            TopPair.singularHomologyMap (pairMap hf ⊤)
              M n : H.obj (_root_.TopCat.of (p ⁻¹' {x : K | (x : V) = 0})) ⟶ _) :=
          congrArg (H.map ι ≫ ·) hπ
      _ = (emptyIso M hp hK h₀ n).inv ≫ TopPair.singularHomologyMap (pairMap hf ⊤) M n :=
          (Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ _) (homologyMap_comp_singularHomologyπ_eq_emptyIso_inv M hp hK h₀ n))
  rw [← Iso.comp_inv_eq, Category.assoc, key, Iso.hom_inv_id_assoc]

omit [FiniteDimensional ℝ V] in
/-- The identification `TauCeti.TopCat.SerreDisk.botIso` is natural in maps over the base. -/
lemma botIso_hom_naturality (hf : f ≫ p' = p) :
    (botIso p).hom ≫ subspaceComplPairMap f (proj_apply_of_comp_eq hf) (mapsTo_empty _ _) ⊥ =
      TopPair.ofSubsetMap f (f.mapsTo_preimage_of_comp_eq hf _) ≫ (botIso p').hom := by
  rw [subspaceComplPairMap_eq_ofSubsetMap f (proj_apply_of_comp_eq hf) (mapsTo_empty _ _) ⊥
    ((mapsTo_empty _ _).union_union fun e he ↦ by rwa [mem_preimage, proj_apply_of_comp_eq hf])]
  simp only [botIso, TopPair.ofSubsetIso_hom]
  exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ rfl

end SerreDisk

open SerreDisk

/-- **The homology of a Serre fibration over a convex neighbourhood of `0`, modulo the part over
the punctured base, is natural in maps of fibrations.** Let `p : E ⟶ K` and `p' : E' ⟶ K` be Serre
fibrations and `f : E ⟶ E'` a map over `K`, restricting to `g` on the fibres over `0`. Under the
isomorphisms `Hₘ(E, p⁻¹(K ∖ {0}); M) ≅ Hₙ(p⁻¹(0); M)` of
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso`, the map induced by `f` on relative homology is
the map induced by `g` on the homology of the fibres. -/
@[reassoc]
theorem singularHomologyPreimageNeZeroIso_hom_naturality {p' : E' ⟶ _root_.TopCat.of K}
    {f : E ⟶ E'} (hp : serreFibrations p) (hp' : serreFibrations p') (hK : Convex ℝ K)
    (hK₀ : K ∈ 𝓝 (0 : V)) (hf : f ≫ p' = p)
    (g : _root_.TopCat.of (p ⁻¹' {x : K | (x : V) = 0}) ⟶
      _root_.TopCat.of (p' ⁻¹' {x : K | (x : V) = 0}))
    (hg : ∀ x, (g x : E') = f x) (n m : ℕ) (h : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap (TopPair.ofSubsetMap f (f.mapsTo_preimage_of_comp_eq hf _))
        M m ≫ (singularHomologyPreimageNeZeroIso M hp' hK hK₀ n m h).hom =
      (singularHomologyPreimageNeZeroIso M hp hK hK₀ n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map g := by
  simp only [singularHomologyPreimageNeZeroIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [emptyIso_hom_naturality M hp hp' hK (mem_of_mem_nhds hK₀) hf g hg,
    subspaceComplPairSingularHomologyIso_hom_naturality_assoc M isOpen_empty
      (isZero_half M hp hK hK₀) isOpen_empty (isZero_half M hp' hK hK₀) f
      (proj_apply_of_comp_eq hf) (mapsTo_empty _ _),
    ← TopPair.singularHomologyMap_comp_assoc (botIso p).hom, botIso_hom_naturality hf,
    TopPair.singularHomologyMap_comp_assoc]

variable {p : E ⟶ _root_.TopCat.of (closedBall (0 : V) 1)}
  {p' : E' ⟶ _root_.TopCat.of (closedBall (0 : V) 1)} {f : E ⟶ E'}

/-- **The homology of a Serre fibration over a disk relative to the boundary sphere is natural in
maps of fibrations.** Let `p : E ⟶ Dʳ` and `p' : E' ⟶ Dʳ` be Serre fibrations and `f : E ⟶ E'` a
map over `Dʳ`, restricting to `g` on the fibres over the centre. Under the isomorphisms
`Hₘ(E, p⁻¹(Sʳ⁻¹); M) ≅ Hₙ(p⁻¹(0); M)` of `TauCeti.TopCat.singularHomologyPreimageSphereIso`, the map
induced by `f` on relative homology is the map induced by `g` on the homology of the fibres. -/
@[reassoc]
theorem singularHomologyPreimageSphereIso_hom_naturality (hp : serreFibrations p)
    (hp' : serreFibrations p') (hf : f ≫ p' = p)
    (g : _root_.TopCat.of (p ⁻¹' {x | (x : V) = 0}) ⟶ _root_.TopCat.of (p' ⁻¹' {x | (x : V) = 0}))
    (hg : ∀ x, (g x : E') = f x) (n m : ℕ) (h : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap (TopPair.ofSubsetMap f (f.mapsTo_preimage_of_comp_eq hf _))
        M m ≫
        (singularHomologyPreimageSphereIso M hp' n m h).hom =
      (singularHomologyPreimageSphereIso M hp n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map g := by
  -- The inclusion `(E, p⁻¹(Sʳ⁻¹)) ⟶ (E, p⁻¹(Dʳ ∖ {0}))` commutes with the maps induced by `f`.
  have hpair : TopPair.ofSubsetMap f (f.mapsTo_preimage_of_comp_eq hf unitSphere) ≫
        TopTriple.totalToOuter.app (TopTriple.ofSubset
          (preimage_sphere_subset_preimage_ne_zero p')) =
      TopTriple.totalToOuter.app (TopTriple.ofSubset
          (preimage_sphere_subset_preimage_ne_zero p)) ≫
        TopPair.ofSubsetMap f (f.mapsTo_preimage_of_comp_eq hf puncturedBall) :=
    TopPair.hom_ext_of_fst _ (by
      ext x
      exact (TopPair.ofSubsetMap_fst_apply f _ x).trans (TopPair.ofSubsetMap_fst_apply f
        (f.mapsTo_preimage_of_comp_eq hf puncturedBall) x).symm)
  have hι := (TopPair.singularHomologyMap_comp _ _ _ _).symm.trans
    ((congrArg (TopPair.singularHomologyMap · M m) hpair).trans
      (TopPair.singularHomologyMap_comp _ _ _ _))
  -- `singularHomologyPreimageSphereIso` is this inclusion followed by
  -- `singularHomologyPreimageNeZeroIso`, whose naturality was proved above.
  calc _ = (_ ≫ _) ≫ (singularHomologyPreimageNeZeroIso M hp' (convex_closedBall 0 1)
          (closedBall_mem_nhds 0 one_pos) n m h).hom :=
        (Category.assoc _ _ _).symm.trans (hι =≫ _)
    _ = _ ≫ (singularHomologyPreimageNeZeroIso M hp (convex_closedBall 0 1)
          (closedBall_mem_nhds 0 one_pos) n m h).hom ≫ _ :=
        (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
          (singularHomologyPreimageNeZeroIso_hom_naturality M hp hp' (convex_closedBall 0 1)
            (closedBall_mem_nhds 0 one_pos) hf g hg n m h))
    _ = _ := (Category.assoc _ _ _).symm

end Naturality

/-! ### Relative to an open subset of the total space -/

section Relative

namespace SerreDisk

variable (p : E ⟶ _root_.TopCat.of K)

variable (A : Set E)

/-- The identification of `(E, A ∪ p⁻¹(K ∖ {0}))` with `(E, A ∪ p⁻¹(K ∖ ⊥))`. -/
private def relBotIso :
    TopPair.ofSubset (A ∪ p ⁻¹' {x : K | (x : V) ≠ 0}) ≅
      subspaceComplPair (proj p) A (⊥ : Submodule ℝ V) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun e ↦ by
    simp only [mem_union, mem_preimage, mem_ofPred_eq, mem_compl_iff, SetLike.mem_coe,
      Submodule.mem_bot]
    rfl

/-- The identification of `(E, A ∪ p⁻¹(K ∖ V))` with `(E, A)`. -/
private def relTopIso : subspaceComplPair (proj p) A (⊤ : Submodule ℝ V) ≅ TopPair.ofSubset A :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun e ↦ by simp

end SerreDisk

open SerreDisk

variable {A : Set E} (hA : IsOpen A)
  (hA' : ∀ (W : Submodule ℝ V) (φ : V →ₗ[ℝ] ℝ) (v : V), v ∈ W → φ v = 1 → ∀ n,
    IsZero ((TopPair.ofSubset (A ∪ p ⁻¹' {x : K | ¬((x : V) ∈ W ∧ φ x ≤ 0)})).singularHomology
      M n))

omit [FiniteDimensional ℝ V] in
include hA' in
/-- The hypothesis on `A`, read through the composite `E → K → V`. -/
private lemma isZero_relHalf (W : Submodule ℝ V) (φ : V →ₗ[ℝ] ℝ) (v : V) (hv : v ∈ W)
    (hφv : φ v = 1) (n : ℕ) :
    IsZero ((TopPair.ofSubset (A ∪ proj p ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ)).singularHomology
      M n) := by
  rw [preimage_proj]
  simpa only [mem_compl_iff, mem_ofPred_eq] using hA' W φ v hv hφv n

/-- **The homology of `E` modulo an open set `A` and the part over the punctured base.** Let `K` be
a subset of a real normed space `V` of finite dimension `r`, let `p : E ⟶ K` be continuous, and
let `A` be an open subset of `E` such that `E` is acyclic modulo `A` and the part of `E` over the
complement in `K` of every closed half-subspace. Then
`Hₘ(E, A ∪ p⁻¹(K ∖ {0}); M) ≅ Hₙ(E, A; M)` for `m = n + r`.

The isomorphism is the composite of `r` relative Mayer–Vietoris connecting morphisms, for the
same flag of subspaces of `V` as `TauCeti.TopCat.singularHomologyPreimageNeZeroIso`, which it
extends
(`TauCeti.TopCat.singularHomologyPreimageNeZeroIso_hom_comp_homologyMap_comp_singularHomologyπ`).
For a product `K × Y` and `A = K × Y'` it computes the homology of `E` modulo the complement of
`{0} × (Y ∖ Y')`. -/
def singularHomologyPreimageNeZeroRelIso (n m : ℕ) (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset (A ∪ p ⁻¹' {x : K | (x : V) ≠ 0})).singularHomology M m ≅
      (TopPair.ofSubset A).singularHomology M n :=
  asIso (TopPair.singularHomologyMap (relBotIso p A).hom M m) ≪≫
    subspaceComplPairSingularHomologyIso M (proj p) A hA (isZero_relHalf M hA')
      (finrank ℝ V) ⊥ (by simp) n m h ≪≫
    asIso (TopPair.singularHomologyMap (relTopIso p A).hom M n)

/-- **Compatibility with the homology of the fibre.** For a Serre fibration `p : E ⟶ K` over a
convex neighbourhood of `0` and an open set `A ⊆ E` as in
`TauCeti.TopCat.singularHomologyPreimageNeZeroRelIso`, the square

`Hₘ(E, p⁻¹(K ∖ {0})) ≅ Hₙ(p⁻¹(0)) → Hₙ(E) → Hₙ(E, A)`
`Hₘ(E, p⁻¹(K ∖ {0})) → Hₘ(E, A ∪ p⁻¹(K ∖ {0})) ≅ Hₙ(E, A)`

commutes, where the unlabelled maps are induced by inclusions. -/
theorem singularHomologyPreimageNeZeroIso_hom_comp_homologyMap_comp_singularHomologyπ
    (hp : serreFibrations p) (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V)) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    (singularHomologyPreimageNeZeroIso M hp hK hK₀ n m h).hom ≫
        SSet.homologyMap (_root_.TopCat.toSSet.map
          (TopPair.ofSubset (p ⁻¹' {x : K | (x : V) = 0})).map) M n ≫
        (TopPair.ofSubset A).singularHomologyπ M n =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 E) fun _ ↦ Or.inr) M m ≫
        (singularHomologyPreimageNeZeroRelIso M hA hA' n m h).hom := by
  -- The two isomorphisms are the same chain of connecting morphisms, related by the naturality
  -- of `subspaceComplPairSingularHomologyIso` along the identity of `E`, which carries `∅` into
  -- `A`; at the end, the map `Hₙ(E) ⟶ Hₙ(E, A)` factors through `Hₙ(E, ∅)`.
  have hnat := subspaceComplPairSingularHomologyIso_hom_naturality M isOpen_empty
    (isZero_half M hp hK hK₀) hA (isZero_relHalf M hA') (𝟙 E) (fun _ ↦ rfl) (mapsTo_empty _ A)
    (finrank ℝ V) ⊥ (by simp) n m h
  have hbot : (botIso p).hom ≫ subspaceComplPairMap (𝟙 E) (fun _ ↦ rfl) (mapsTo_empty _ A) ⊥ =
      TopPair.ofSubsetMap (𝟙 E) (fun _ ↦ Or.inr) ≫ (relBotIso p A).hom := by
    rw [subspaceComplPairMap_eq_ofSubsetMap (𝟙 E) (fun _ ↦ rfl) (mapsTo_empty _ A) ⊥
      fun e he ↦ he.elim (fun h ↦ (notMem_empty e h).elim) Or.inr]
    simp only [botIso, relBotIso, TopPair.ofSubsetIso_hom]
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ rfl
  -- The map `(E, ∅) ⟶ (E, A)` through which `Hₙ(E) ⟶ Hₙ(E, A)` factors.
  have hmaps : MapsTo (𝟙 E) (∅ ∪ proj p ⁻¹' ((⊤ : Submodule ℝ V) : Set V)ᶜ) A := by
    rintro e (h | h)
    exacts [(notMem_empty e h).elim, (h Submodule.mem_top).elim]
  have htop : subspaceComplPairMap (𝟙 E) (fun _ ↦ rfl) (mapsTo_empty _ A) ⊤ ≫
      (relTopIso p A).hom = TopPair.ofSubsetMap (𝟙 E) hmaps := by
    rw [subspaceComplPairMap_eq_ofSubsetMap (𝟙 E) (fun _ ↦ rfl) (mapsTo_empty _ A) ⊤
      fun e he ↦ he.elim (fun h ↦ (notMem_empty e h).elim) Or.inr]
    simp only [relTopIso, TopPair.ofSubsetIso_hom]
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ rfl
  -- `emptyIso` is inverse to the inclusion of the fibre followed by `Hₙ(E) ⟶ Hₙ(E, ∅)`.
  have hempty : (emptyIso M hp hK (mem_of_mem_nhds hK₀) n).hom ≫
      SSet.homologyMap (_root_.TopCat.toSSet.map
        (TopPair.ofSubset (p ⁻¹' {x : K | (x : V) = 0})).map) M n ≫
      (TopPair.ofSubset A).singularHomologyπ M n =
        TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 E) hmaps) M n := by
    rw [← TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id _ hmaps n]
    exact (congrArg (_ ≫ ·) (homologyMap_comp_singularHomologyπ_eq_emptyIso_inv_assoc M hp hK
      (mem_of_mem_nhds hK₀) n _)).trans (Iso.hom_inv_id_assoc _ _)
  simp only [singularHomologyPreimageNeZeroIso, singularHomologyPreimageNeZeroRelIso,
    Iso.trans_hom, asIso_hom, Category.assoc]
  rw [hempty, ← htop, TopPair.singularHomologyMap_comp, reassoc_of% hnat,
    ← TopPair.singularHomologyMap_comp_assoc, hbot, TopPair.singularHomologyMap_comp_assoc]

end Relative

end TopCat

end TauCeti
