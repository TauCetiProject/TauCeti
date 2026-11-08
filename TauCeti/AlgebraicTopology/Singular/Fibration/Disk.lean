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
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Relative
public import TauCeti.AlgebraicTopology.Singular.Triple
public import TauCeti.Analysis.Convex.Star
public import TauCeti.LinearAlgebra.Submodule.LineExtension
public import TauCeti.Topology.Homotopy.PuncturedStarConvex

/-!
# Homology of a Serre fibration over a disk, relative to the boundary sphere

Let `p : E → K` be a Serre fibration whose base `K` is a convex neighbourhood of `0` in a real
normed space `V` of finite dimension `r`, and let `F = p⁻¹(0)` be the fibre over `0`. This file
computes the relative singular homology of `E` modulo the part of `E` over `K ∖ {0}`, with
coefficients in a ring `R`:

* `Hₘ(E, p⁻¹(K ∖ {0}); R) = 0` for `m < r`
  (`TauCeti.TopCat.isZero_singularHomology_preimage_ne_zero`);
* `Hₙ₊ᵣ(E, p⁻¹(K ∖ {0}); R) ≅ Hₙ(F; R)`
  (`TauCeti.TopCat.singularHomologyPreimageNeZeroIso`).

For the closed unit ball `Dʳ` of `V`, the part of `E` over the punctured ball and the part over the
unit sphere `Sʳ⁻¹` have the same homology, since the punctured ball deforms radially onto the
sphere. Hence, for a Serre fibration `p : E → Dʳ`,

* `Hₘ(E, p⁻¹(Sʳ⁻¹); R) = 0` for `m < r`
  (`TauCeti.TopCat.isZero_singularHomology_preimage_sphere`);
* `Hₙ₊ᵣ(E, p⁻¹(Sʳ⁻¹); R) ≅ Hₙ(F; R)` (`TauCeti.TopCat.singularHomologyPreimageSphereIso`).

This is the computation over a single cell behind the first page of the Serre spectral sequence
of a fibration over a CW complex: pulled back along the characteristic map of an `r`-cell, the
fibration becomes a Serre fibration over `Dʳ`, and the relative homology of the cell's part of the
filtration is the homology of the fibre, shifted by `r`. For the product bundle `B × V → V` the
same computation is `TauCeti.prodThomPairSingularHomologyIso`.

## The argument

Everything rests on one vanishing statement for an arbitrary base `B`
(`TauCeti.TopCat.isZero_singularHomology_preimage_of_deformation`): if `B` deforms into `A ⊆ B`
in the weak sense (by a homotopy starting at the identity, ending in `A`, and keeping `A` in `A`),
then `H_*(E, p⁻¹(A); R) = 0`.

The computation then removes one dimension at a time, along the extensions `W ⊆ W'` of
`Submodule.LineExtension`: `W' = W ⊕ ℝv` with a functional `φ` that vanishes on `W` and is `1` at
`v`. The part of `E` over `K ∖ W` is the union of the open parts over the complements in `K` of the
two closed half-subspaces `{x ∈ W' | ±φ x ≤ 0}`, which intersect in the part over `K ∖ W'`. Each of
these complements is star-convex about a small positive multiple of `±v`, so `K` deforms into it
along straight lines (`ContinuousMap.Homotopy.affine`), and `E` modulo the part over it is
acyclic. The relative Mayer–Vietoris sequence (`TopCat.relativeMayerVietorisδ`) then gives
`Hₙ₊₁(E, p⁻¹(K ∖ W)) ≅ Hₙ(E, p⁻¹(K ∖ W'))`. After `r` steps from `W = 0` the subspace is all of
`V`, the part of `E` over `K ∖ V` is empty, and `Hₙ(E) ≅ Hₙ(F)` because `K` contracts onto `0`
along straight lines. Over the closed unit ball, the radial deformation
`StarConvex.radialHomotopy` of the punctured ball onto the sphere passes from `K ∖ {0}` to
`Sʳ⁻¹`.

## Main results

* `TauCeti.TopCat.isZero_singularHomology_preimage_ne_zero`,
  `TauCeti.TopCat.singularHomologyPreimageNeZeroIso`: the relative homology of `E` modulo the part
  over `K ∖ {0}`.
* `TauCeti.TopCat.isZero_singularHomology_preimage_sphere`,
  `TauCeti.TopCat.singularHomologyPreimageSphereIso`: the relative homology of `E` modulo the part
  over the boundary sphere, for a Serre fibration over the closed unit ball.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.D, the proof of Theorem 4D.10, and Section 5.1 (the Serre spectral sequence).
-/

public section

noncomputable section

open CategoryTheory Limits Module Metric Set Topology
open scoped unitInterval

universe u

namespace TauCeti

namespace TopCat

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {K : Set V}
  {E : _root_.TopCat.{u}} {p : E ⟶ _root_.TopCat.of K} (R : Type u) [Ring R]

namespace SerreDisk

/-- For a Serre fibration over a convex set `K`, the pair `(E, p⁻¹(K ∩ S))` is acyclic when
`S ⊆ V` is star-convex about a point `c ∈ K ∩ S`: `K` deforms into `K ∩ S` along straight lines
towards `c`, by the affine homotopy from the inclusion of `K` to the constant map at `c`. -/
private lemma isZero_of_starConvex (hp : serreFibrations p) (hK : Convex ℝ K) {c : V}
    (hc : c ∈ K) {S : Set V} (hS : StarConvex ℝ c S) (hcS : c ∈ S) (m : ℕ) :
    IsZero ((TopPair.ofSubset (p ⁻¹' {x : K | (x : V) ∈ S})).singularHomology
      (ModuleCat.of R R) m) :=
  let G := ContinuousMap.Homotopy.affine ⟨((↑) : K → V), continuous_subtype_val⟩ (.const K c)
  isZero_singularHomology_preimage_of_deformation hp
    ⟨fun q ↦ ⟨G q, hK.lineMap_mem q.2.2 hc q.1.2⟩, by fun_prop⟩
    (fun x ↦ Subtype.ext (by simp [G]))
    (fun x ↦ by simpa [G] using hcS)
    (fun t x hx ↦ by
      simp only [mem_ofPred_eq, ContinuousMap.coe_mk, G, ContinuousMap.Homotopy.affine_apply,
        AffineMap.lineMap_apply_module] at hx ⊢
      rw [add_comm]
      exact hS hx t.2.1 (sub_nonneg.2 t.2.2) (add_sub_cancel _ _)) R m

/-- The part of `K` off a subspace `W`. -/
private abbrev cpl (W : Submodule ℝ V) : Set (_root_.TopCat.of K) :=
  {x | (x : V) ∈ (W : Set V)ᶜ}

/-- The complement in `K` of the closed half-subspace `{x ∈ W | φ x ≤ 0}`. -/
private abbrev half (W : Submodule ℝ V) (φ : V →ₗ[ℝ] ℝ) : Set (_root_.TopCat.of K) :=
  {x | (x : V) ∈ {y | y ∈ W ∧ φ y ≤ 0}ᶜ}

private lemma isOpen_half [FiniteDimensional ℝ V] (W : Submodule ℝ V) (φ : V →ₗ[ℝ] ℝ) :
    IsOpen (p ⁻¹' half (K := K) W φ) :=
  (((W.closed_of_finiteDimensional.inter (isClosed_le φ.continuous_of_finiteDimensional
    continuous_const)).isOpen_compl).preimage continuous_subtype_val).preimage p.hom.continuous

/-- The part of `E` over the complement of a closed half-subspace is acyclic. -/
private lemma isZero_half (hp : serreFibrations p) (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V))
    {W : Submodule ℝ V} {φ : V →ₗ[ℝ] ℝ} {v : V} (hv : v ∈ W) (hφv : φ v = 1) (m : ℕ) :
    IsZero ((TopPair.ofSubset (p ⁻¹' half (K := K) W φ)).singularHomology
      (ModuleCat.of R R) m) := by
  -- A neighbourhood of `0` is absorbent, so it contains a positive multiple of `v`.
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t • v ∈ K :=
    ((absorbent_nhds_zero hK₀).eventually_nhdsNE_zero v).filter_mono
      (nhdsWithin_mono _ fun _ h ↦ ne_of_gt h)
  obtain ⟨t, htK, ht : 0 < t⟩ := (hev.and self_mem_nhdsWithin).exists
  have htv : 0 < φ (t • v) := by simpa [hφv] using ht
  exact isZero_of_starConvex R hp hK htK
    (starConvex_compl_setOf_mem_and_nonpos (W.smul_mem t hv) htv)
    (fun h ↦ (not_le.2 htv) h.2) m

/-- The pair `(E, p⁻¹(K ∖ W))`. -/
private abbrev pair (p : E ⟶ _root_.TopCat.of K) (W : Submodule ℝ V) : TopPair.{u} :=
  TopPair.ofSubset (p ⁻¹' cpl W)

variable {W : Submodule ℝ V}

/-- The part of `E` over `K ∖ W` is the union of the parts over the two half-subspace complements
of a step. -/
private def unionIso (p : E ⟶ _root_.TopCat.of K) (s : W.LineExtension) :
    pair p W ≅ TopPair.ofSubset (p ⁻¹' half s.W' s.φ ∪ p ⁻¹' half s.W' (-s.φ)) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun _ ↦ (Set.ext_iff.1 s.compl_union_compl _).symm

/-- The part of `E` over the intersection of the two half-subspace complements of a step is the
part over `K ∖ W'`. -/
private def interIso (p : E ⟶ _root_.TopCat.of K) (s : W.LineExtension) :
    TopPair.ofSubset (p ⁻¹' half s.W' s.φ ∩ p ⁻¹' half s.W' (-s.φ)) ≅ pair p s.W' :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun _ ↦ Set.ext_iff.1 s.compl_inter_compl _

private lemma isZero_biprod (hp : serreFibrations p) (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V))
    (s : W.LineExtension) (n : ℕ) :
    IsZero ((TopPair.ofSubset (p ⁻¹' half s.W' s.φ)).singularHomology (ModuleCat.of R R) n ⊞
      (TopPair.ofSubset (p ⁻¹' half s.W' (-s.φ))).singularHomology (ModuleCat.of R R) n) :=
  biprod_isZero_iff _ _ |>.2 ⟨isZero_half R hp hK hK₀ s.v_mem s.apply_v n,
    isZero_half R hp hK hK₀ (neg_mem s.v_mem) (by simp [s.apply_v]) n⟩

variable [FiniteDimensional ℝ V]

private lemma isIso_relativeMayerVietorisδ (hp : serreFibrations p) (hK : Convex ℝ K)
    (hK₀ : K ∈ 𝓝 (0 : V)) (s : W.LineExtension) (n : ℕ) :
    IsIso (TopCat.relativeMayerVietorisδ (ModuleCat.of R R) (isOpen_half (p := p) s.W' s.φ)
      (isOpen_half (p := p) s.W' (-s.φ)) (n + 1) n rfl) := by
  have := (TopCat.relativeMayerVietoris_exact₃ (ModuleCat.of R R) (isOpen_half (p := p) s.W' s.φ)
    (isOpen_half (p := p) s.W' (-s.φ)) (n + 1) n rfl).mono_g
      ((isZero_biprod R hp hK hK₀ s _).eq_of_src _ _)
  have := (TopCat.relativeMayerVietoris_exact₁ (ModuleCat.of R R) (isOpen_half (p := p) s.W' s.φ)
    (isOpen_half (p := p) s.W' (-s.φ)) (n + 1) n rfl).epi_f
      ((isZero_biprod R hp hK hK₀ s _).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- One step of the computation: `Hₙ₊₁(E, p⁻¹(K ∖ W)) ≅ Hₙ(E, p⁻¹(K ∖ W'))`. -/
private def stepIso (hp : serreFibrations p) (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V))
    (s : W.LineExtension) (n : ℕ) :
    (pair p W).singularHomology (ModuleCat.of R R) (n + 1) ≅
      (pair p s.W').singularHomology (ModuleCat.of R R) n :=
  haveI := isIso_relativeMayerVietorisδ R hp hK hK₀ s n
  asIso (TopPair.singularHomologyMap (unionIso p s).hom (ModuleCat.of R R) (n + 1)) ≪≫
    asIso (TopCat.relativeMayerVietorisδ (ModuleCat.of R R) (isOpen_half (p := p) s.W' s.φ)
      (isOpen_half (p := p) s.W' (-s.φ)) (n + 1) n rfl) ≪≫
    asIso (TopPair.singularHomologyMap (interIso p s).hom (ModuleCat.of R R) n)

private lemma isZero_singularHomology_zero (hp : serreFibrations p) (hK : Convex ℝ K)
    (hK₀ : K ∈ 𝓝 (0 : V)) (s : W.LineExtension) :
    IsZero ((pair p W).singularHomology (ModuleCat.of R R) 0) := by
  have := TopCat.epi_relativeMayerVietorisFromBiprod_zero (ModuleCat.of R R)
    (isOpen_half (p := p) s.W' s.φ) (isOpen_half (p := p) s.W' (-s.φ))
  exact ((isZero_biprod R hp hK hK₀ s 0).of_epi
    (TopCat.relativeMayerVietorisFromBiprod (ModuleCat.of R R) _ _ 0)).of_iso
      (asIso (TopPair.singularHomologyMap (unionIso p s).hom (ModuleCat.of R R) 0))

/-- `Hₙ(E, p⁻¹(K ∖ W)) = 0` below the codimension of `W`. -/
private lemma isZero_singularHomology_pair_of_lt (hp : serreFibrations p) (hK : Convex ℝ K)
    (hK₀ : K ∈ 𝓝 (0 : V)) :
    ∀ (n : ℕ) (W : Submodule ℝ V), n + finrank ℝ W < finrank ℝ V →
      IsZero ((pair p W).singularHomology (ModuleCat.of R R) n)
  | 0, W, h => isZero_singularHomology_zero R hp hK hK₀
      (W.lineExtension (Submodule.lt_top_of_finrank_lt_finrank (by omega)).ne)
  | n + 1, W, h =>
    let s := W.lineExtension (Submodule.lt_top_of_finrank_lt_finrank (by omega)).ne
    (isZero_singularHomology_pair_of_lt hp hK hK₀ n s.W' (by rw [s.finrank_eq]; omega)).of_iso
      (stepIso R hp hK hK₀ s n)

/-- The identification of `(E, p⁻¹(K ∖ W))` with `(E, p⁻¹(K ∖ V))` for `W` of full dimension. -/
private def topIso (p : E ⟶ _root_.TopCat.of K) (hW : finrank ℝ W = finrank ℝ V) :
    pair p W ≅ pair p (⊤ : Submodule ℝ V) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun e ↦ by
    rw [Submodule.eq_top_of_finrank_eq hW]
    rfl

/-- `Hₘ(E, p⁻¹(K ∖ W)) ≅ Hₙ(E, p⁻¹(K ∖ V))` for `m = n + c`, with `c` the codimension of `W`, by
`c` successive steps. -/
private def chainIso (hp : serreFibrations p) (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V)) :
    ∀ (c : ℕ) (W : Submodule ℝ V), finrank ℝ W + c = finrank ℝ V → ∀ (n m : ℕ), n + c = m →
      ((pair p W).singularHomology (ModuleCat.of R R) m ≅
        (pair p (⊤ : Submodule ℝ V)).singularHomology (ModuleCat.of R R) n)
  | 0, _, hW, n, _, rfl =>
    asIso (TopPair.singularHomologyMap (topIso p hW).hom (ModuleCat.of R R) n)
  | c + 1, W, hW, n, _, rfl =>
    let s := W.lineExtension (Submodule.lt_top_of_finrank_lt_finrank (by omega)).ne
    stepIso R hp hK hK₀ s (n + c) ≪≫
      chainIso hp hK hK₀ c s.W' (by rw [s.finrank_eq]; omega) n (n + c) rfl

omit [FiniteDimensional ℝ V] in
private instance (p : E ⟶ _root_.TopCat.of K) : IsEmpty (pair p (⊤ : Submodule ℝ V)).snd :=
  ⟨fun e ↦ e.2 Submodule.mem_top⟩

omit [FiniteDimensional ℝ V] in
/-- `Hₙ(E, ∅) ≅ Hₙ(F)`: the base contracts onto `0` along straight lines, so the inclusion of the
fibre over `0` is a homology isomorphism. -/
private def emptyIso (hp : serreFibrations p) (hK : Convex ℝ K) (h₀ : (0 : V) ∈ K) (n : ℕ) :
    (pair p (⊤ : Submodule ℝ V)).singularHomology (ModuleCat.of R R) n ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {x : K | (x : V) = 0})) :=
  have h (m : ℕ) := isZero_of_starConvex R hp hK h₀ (starConvex_singleton (0 : V)) rfl m
  haveI := TopPair.isIso_homologyMap_map_of_isZero _ _ (h (n + 1)) (h n)
  (asIso ((pair p (⊤ : Submodule ℝ V)).singularHomologyπ (ModuleCat.of R R) n)).symm ≪≫
    (asIso (SSet.homologyMap (TopCat.toSSet.map
      (TopPair.ofSubset (p ⁻¹' {x : K | (x : V) ∈ ({0} : Set V)})).map)
      (ModuleCat.of R R) n)).symm

omit [FiniteDimensional ℝ V] in
/-- The identification of `(E, p⁻¹(K ∖ {0}))` with `(E, p⁻¹(K ∖ ⊥))`. -/
private def botIso (p : E ⟶ _root_.TopCat.of K) :
    TopPair.ofSubset (p ⁻¹' {x : K | (x : V) ≠ 0}) ≅ pair p (⊥ : Submodule ℝ V) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun e ↦ by
    simp only [mem_preimage, mem_ofPred_eq, mem_compl_iff, SetLike.mem_coe, Submodule.mem_bot]
    rfl

end SerreDisk

open SerreDisk

variable [FiniteDimensional ℝ V]

/-- **A Serre fibration over a convex neighbourhood of `0` has vanishing homology modulo the part
over the punctured base, below the dimension.** Let `K` be a convex neighbourhood of `0` in a
finite-dimensional real normed space `V`, and let `p : E ⟶ K` be a Serre fibration. Then
`Hₘ(E, p⁻¹(K ∖ {0}); R) = 0` for every `m < dim V`. -/
theorem isZero_singularHomology_preimage_ne_zero (hp : serreFibrations p) (hK : Convex ℝ K)
    (hK₀ : K ∈ 𝓝 (0 : V)) {m : ℕ} (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (p ⁻¹' {x : K | (x : V) ≠ 0})).singularHomology
      (ModuleCat.of R R) m) :=
  (isZero_singularHomology_pair_of_lt R hp hK hK₀ m ⊥ (by simpa using hm)).of_iso
    (asIso (TopPair.singularHomologyMap (botIso p).hom (ModuleCat.of R R) m))

/-- **The homology of a Serre fibration over a convex neighbourhood of `0`, modulo the part over
the punctured base, is the shifted homology of the fibre over `0`.** Let `K` be a convex
neighbourhood of `0` in a real normed space `V` of finite dimension `r`, and let `p : E ⟶ K` be a
Serre fibration. Then `Hₘ(E, p⁻¹(K ∖ {0}); R) ≅ Hₙ(p⁻¹(0); R)` for `m = n + r`.

The isomorphism is the composite of `r` relative Mayer–Vietoris connecting morphisms, for a fixed
choice of a flag of subspaces of `V` (`Submodule.lineExtension`), followed by the inverse of the
homology isomorphism induced by the inclusion of the fibre. -/
def singularHomologyPreimageNeZeroIso (hp : serreFibrations p) (hK : Convex ℝ K)
    (hK₀ : K ∈ 𝓝 (0 : V)) (n m : ℕ) (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset (p ⁻¹' {x : K | (x : V) ≠ 0})).singularHomology (ModuleCat.of R R) m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {x : K | (x : V) = 0})) :=
  asIso (TopPair.singularHomologyMap (botIso p).hom (ModuleCat.of R R) m) ≪≫
    chainIso R hp hK hK₀ (finrank ℝ V) ⊥ (by simp) n m h ≪≫
    emptyIso R hp hK (mem_of_mem_nhds hK₀) n

section Sphere

variable {p : E ⟶ _root_.TopCat.of (closedBall (0 : V) 1)}

/-- The punctured closed unit ball, as a subset of the closed unit ball. -/
private abbrev puncturedBall : Set (closedBall (0 : V) 1) := {x | (x : V) ≠ 0}

/-- The unit sphere, as a subset of the closed unit ball. -/
private abbrev unitSphere : Set (closedBall (0 : V) 1) := {x | (x : V) ∈ sphere (0 : V) 1}

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
private lemma unitSphere_subset_puncturedBall : unitSphere (V := V) ⊆ puncturedBall := by
  intro x hx h
  simp [h] at hx

/-- The radial deformation of the punctured closed unit ball onto the unit sphere: the
straight-line homotopy `StarConvex.radialHomotopy` from the radial projection to the identity, run
backwards and read on the punctured ball as a subset of the closed unit ball. -/
private def radial : C(I × _root_.TopCat.of (puncturedBall (V := V)),
    _root_.TopCat.of (puncturedBall (V := V))) :=
  let H := ((convex_closedBall (0 : V) 1).starConvex
    (mem_closedBall_self zero_le_one)).radialHomotopy one_pos sphere_subset_closedBall
  { toFun q := ⟨⟨H.symm (q.1, ⟨q.2, q.2.1.2, q.2.2⟩), (H.symm _).2.1⟩, (H.symm _).2.2⟩
    continuous_toFun := by fun_prop }

omit [FiniteDimensional ℝ V] in
/-- The part of `E` over the punctured ball is acyclic modulo the part over the unit sphere. -/
private lemma isZero_singularHomology_puncturedBall_unitSphere (hp : serreFibrations p) (m : ℕ) :
    IsZero ((TopTriple.innerPair.obj (TopTriple.ofSubset (preimage_mono (f := p)
      (unitSphere_subset_puncturedBall (V := V))))).singularHomology (ModuleCat.of R R) m) := by
  have hz := isZero_singularHomology_preimage_of_deformation
    (mem_serreFibrations_restrictPreimage hp puncturedBall)
    (A := Subtype.val ⁻¹' unitSphere) radial
    (fun x ↦ by ext; simp [radial])
    (fun x ↦ by
      rw [mem_preimage, mem_ofPred_eq]
      simp [radial, ContinuousMap.Homotopy.symm_apply, norm_smul, (norm_pos_iff.2 x.2).ne'])
    (fun t x hx ↦ by
      rw [mem_preimage, mem_ofPred_eq] at hx ⊢
      have hx' : ‖(x : V)‖ = 1 := mem_sphere_zero_iff_norm.1 hx
      simp [radial, hx']) R m
  exact hz.of_iso (asIso (TopPair.singularHomologyMap
    (TopPair.ofSubsetPreimageValIso (X := E) (preimage_mono (f := p)
      (unitSphere_subset_puncturedBall (V := V)))).hom (ModuleCat.of R R) m)).symm

omit [FiniteDimensional ℝ V] in
private lemma isIso_totalToOuter (hp : serreFibrations p) (m : ℕ) :
    IsIso (TopPair.singularHomologyMap (TopTriple.totalToOuter.app (TopTriple.ofSubset
      (preimage_mono (f := p) (unitSphere_subset_puncturedBall (V := V))))) (ModuleCat.of R R)
      m) :=
  TopTriple.isIso_singularHomologyMap_totalToOuter_of_isZero _ _ m
    (isZero_singularHomology_puncturedBall_unitSphere R hp m)
    fun m' _ ↦ isZero_singularHomology_puncturedBall_unitSphere R hp m'

/-- **A Serre fibration over a disk has vanishing homology modulo the part over the boundary
sphere, below the dimension.** Let `p : E ⟶ Dʳ` be a Serre fibration over the closed unit ball of
a real normed space of finite dimension `r`. Then `Hₘ(E, p⁻¹(Sʳ⁻¹); R) = 0` for every `m < r`. -/
theorem isZero_singularHomology_preimage_sphere (hp : serreFibrations p) {m : ℕ}
    (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (p ⁻¹' {x | (x : V) ∈ sphere (0 : V) 1})).singularHomology
      (ModuleCat.of R R) m) :=
  (isZero_singularHomology_preimage_ne_zero R hp (convex_closedBall 0 1)
    (closedBall_mem_nhds 0 one_pos) hm).of_iso
    (@asIso _ _ _ _ _ (isIso_totalToOuter R hp m))

/-- **The homology of a Serre fibration over a disk, modulo the part over the boundary sphere, is
the shifted homology of the fibre over the centre.** Let `p : E ⟶ Dʳ` be a Serre fibration over
the closed unit ball of a real normed space of finite dimension `r`. Then
`Hₘ(E, p⁻¹(Sʳ⁻¹); R) ≅ Hₙ(p⁻¹(0); R)` for `m = n + r`.

The isomorphism is the map induced by the inclusion `(E, p⁻¹(Sʳ⁻¹)) ⟶ (E, p⁻¹(Dʳ ∖ {0}))`
followed by `TauCeti.TopCat.singularHomologyPreimageNeZeroIso`. -/
def singularHomologyPreimageSphereIso (hp : serreFibrations p) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset (p ⁻¹' {x | (x : V) ∈ sphere (0 : V) 1})).singularHomology
        (ModuleCat.of R R) m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {x | (x : V) = 0})) :=
  @asIso _ _ _ _ _ (isIso_totalToOuter R hp m) ≪≫
    singularHomologyPreimageNeZeroIso R hp (convex_closedBall 0 1)
      (closedBall_mem_nhds 0 one_pos) n m h

end Sphere

end TopCat

end TauCeti
