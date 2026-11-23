/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.TopHomology

/-!
# Cubical cycles glued from relative cycles of faces

Let `Y` be a compact topological `n`-manifold, the boundary of a compact manifold with corners in
the intended application, and suppose that `Y` is covered by faces: continuous maps
`fᵢ : Xᵢ → Y` with subsets `Aᵢ ⊆ Xᵢ`, the boundaries of the faces. A normalized cubical `n`-cycle
`z` of `Y` that is a sum `z = ∑ᵢ (fᵢ)_♯ cᵢ` of push-forwards of relative cycles `cᵢ` of the pairs
`(Xᵢ, Aᵢ)`, with relative classes `aᵢ`, is *glued* from the faces. This file shows that the class
of such a cycle is determined by local data at the interior points of the faces.

* At a point `x` of `Y` which no other face reaches and which is not the image of a point of `Aᵢ`,
  the image of `[z]` in the local cubical homology `Hₙ(Y, Y ∖ {x})` is the image of `aᵢ` under the
  map of pairs `fᵢ : (Xᵢ, Aᵢ) ⟶ (Y, Y ∖ {x})`
  (`TauCeti.homologyMap_cokernel_π_homologyπ_of_iCycles_eq_sum`). Indeed in the relative chains of
  `(Y, Y ∖ {x})` every other summand vanishes, since it is the push-forward of a chain of
  `Y ∖ {x}`, and the `i`-th summand is the push-forward of the relative cycle `cᵢ`.
* A class of `Hₙ(Y)` is determined by its images in the local cubical homology at the points of a
  set meeting every path component (`TauCeti.cubicalHomology_ext_of_localHomology`). This is the
  statement for singular homology
  (`TauCeti.singularHomology_ext_of_singularHomologyToLocalHomology`), transported through the
  absolute and relative cubical–singular comparisons
  (`TopPair.homologyMap_π_comp_singularCubicalHomologyIso_inv`).

Together: if `μ ∈ Hₙ(Y)` has, at one interior point of a face in each path component of `Y`, the
local image of the face class there, then `z` is a cycle representing `μ`
(`TauCeti.homologyπ_eq_of_iCycles_eq_sum`).

This is the **gluing condition** of the representing chain systems of Barraud and Cornea
(`TauCeti.TwistingChainSystem.exists_isRepresenting`), reduced to points. There `Y` is the boundary
of a compactified trajectory space `M x y`, the faces are the products `M x z × M z y` of
lower-dimensional trajectory spaces, the `cᵢ` are the cross products of their fundamental chains
relative to the boundary, and `μ` is the image of the fundamental class `[M x y, ∂M x y]` under the
connecting morphism. The gluing condition then follows by comparing, at an interior point of each
face, the local image of this class with the image of the product of the fundamental classes of
the factors, taken with the sign of the boundary orientation.

## Main results

* `TauCeti.homologyMap_cokernel_π_homologyπ_of_iCycles_eq_sum`: the local image of a glued cycle at
  an interior point of a single face.
* `TauCeti.cubicalHomology_ext_of_localHomology`: on a compact manifold, top-dimensional cubical
  classes are detected in local cubical homology on any set meeting every path component.
* `TauCeti.homologyπ_eq_of_iCycles_eq_sum`: a glued cycle represents every class with the local
  images of the faces at one interior point of each path component.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. 166 (2007), 657–722, Appendix A.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 5 and the Appendix.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, Lemma 3.27.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set

universe u

namespace TauCeti

variable {k : Type u} [Ring k] {Y : Type u} [TopologicalSpace Y] {n : ℕ}
  {ι : Type*} {s : Finset ι} {X : ι → TopCat.{u}} {A : ∀ i, Set (X i)}
  {f : ∀ i, X i ⟶ TopCat.of Y} {c : ∀ i, NormalizedCubicalChain (X i) k n}
  {a : ∀ i, ((TopPair.ofSubset (A i)).cubicalChainComplex k).homology n}
  {z : ((normalizedCubicalChainComplex k).obj (TopCat.of Y)).cycles n}

section Glue

/-- **The local image of a glued cycle at an interior point of one face.** Let `z` be a normalized
cubical `n`-cycle of `Y` which is the sum of the push-forwards along maps `fⱼ : Xⱼ ⟶ Y` of chains
`cⱼ` representing classes `aⱼ` of the relative cubical homology `Hₙ(Xⱼ, Aⱼ)`. Let `x` be a point
of `Y` outside the images of the other faces `fⱼ`, `j ≠ i`, and outside the image of `Aᵢ`. Then the
image of the class of `z` in the local cubical homology `Hₙ(Y, Y ∖ {x})` is the image of `aᵢ` under
the map of pairs `fᵢ : (Xᵢ, Aᵢ) ⟶ (Y, Y ∖ {x})`. -/
theorem homologyMap_cokernel_π_homologyπ_of_iCycles_eq_sum
    (hc : ∀ i ∈ s, (TopPair.ofSubset (A i)).IsCubicalRepresentative k (c i) (a i))
    (hz : (((normalizedCubicalChainComplex k).obj (TopCat.of Y)).iCycles n).hom z =
      ∑ i ∈ s, NormalizedCubicalChain.map k (f i).hom n (c i))
    {x : Y} {i : ι} (hi : i ∈ s) (hA : MapsTo (f i) (A i) ({x}ᶜ : Set (TopCat.of Y)))
    (hj : ∀ j ∈ s, j ≠ i → x ∉ range (f j)) :
    (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
        (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of Y))).map)) n).hom
        ((((normalizedCubicalChainComplex k).obj (TopCat.of Y)).homologyπ n).hom z) =
      (HomologicalComplex.homologyMap
        (TopPair.cubicalChainComplexMap k (TopPair.ofSubsetMap (f i) hA)) n).hom (a i) := by
  let Q := TopPair.ofSubset ({x}ᶜ : Set (TopCat.of Y))
  let φ := TopPair.cubicalChainComplexMap k (TopPair.ofSubsetMap (f i) hA)
  obtain ⟨r, hr, hra⟩ := (TopPair.isCubicalRepresentative_iff _ _).1 (hc i hi)
  rw [← hra]
  let π := cokernel.π ((normalizedCubicalChainComplex k).map Q.map)
  -- On cycles of the relative chains of `(Y, Y ∖ {x})`, the image of `z` is the image of `r`.
  have hcyc : (HomologicalComplex.cyclesMap π n).hom z =
      (HomologicalComplex.cyclesMap φ n).hom r := by
    apply (ModuleCat.mono_iff_injective _).1
      (inferInstance : Mono ((Q.cubicalChainComplex k).iCycles n))
    refine (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i π n) z).trans
      (Eq.trans ?_ (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ n) r).symm)
    calc (π.f n).hom ((((normalizedCubicalChainComplex k).obj (TopCat.of Y)).iCycles n).hom z)
        = (π.f n).hom (∑ j ∈ s, NormalizedCubicalChain.map k (f j).hom n (c j)) :=
          congrArg (π.f n).hom hz
      _ = ∑ j ∈ s, (π.f n).hom (NormalizedCubicalChain.map k (f j).hom n (c j)) := map_sum _ _ _
      _ = (π.f n).hom (NormalizedCubicalChain.map k (f i).hom n (c i)) :=
          Finset.sum_eq_single_of_mem i hi fun j hj' hji ↦
            Q.cokernel_π_f_map_eq_zero_of_range_subset k (f j)
              (fun _ hy ↦ ⟨⟨_, fun h ↦ hj j hj' hji (h ▸ hy)⟩, rfl⟩) (c j)
      _ = (φ.f n).hom (((cokernel.π ((normalizedCubicalChainComplex k).map
            (TopPair.ofSubset (A i)).map)).f n).hom (c i)) := by
          have h := (TopPair.π_cubicalChainComplexMap_f_apply k (TopPair.ofSubsetMap (f i) hA) n
            (c i)).symm
          rwa [TopPair.ofSubsetMap_fst] at h
      _ = (φ.f n).hom ((((TopPair.ofSubset (A i)).cubicalChainComplex k).iCycles n).hom r) :=
          congrArg (φ.f n).hom hr
  exact (ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality π n) z).trans
    ((congrArg ((Q.cubicalChainComplex k).homologyπ n).hom hcyc).trans
      (ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality φ n) r).symm)

end Glue

section Detect

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [T2Space Y] [ChartedSpace E Y] [CompactSpace Y]

/-- **Top-dimensional cubical classes of a compact manifold are detected locally.** On a compact
Hausdorff space `Y` modelled on a real normed space of finite dimension `n`, two classes of the
normalized cubical homology `Hₙ(Y)` are equal as soon as their images in the local cubical
homology `Hₙ(Y, Y ∖ {x})` agree at every point `x` of a set `D` from which every point of `Y` can
be reached by a path. -/
theorem cubicalHomology_ext_of_localHomology (hn : finrank ℝ E = n) {D : Set Y}
    (hD : ∀ y, ∃ x ∈ D, Joined x y)
    {μ μ' : ((normalizedCubicalChainComplex k).obj (TopCat.of Y)).homology n}
    (h : ∀ x ∈ D,
      (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
          (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of Y))).map)) n).hom μ =
        (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
          (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of Y))).map)) n).hom μ') :
    μ = μ' := by
  let e := singularCubicalHomologyIso k (TopCat.of Y) n
  apply (ConcreteCategory.bijective_of_isIso e.inv).1
  refine singularHomology_ext_of_singularHomologyToLocalHomology (ModuleCat.of k k) hn hD
    fun x hx ↦ ?_
  let Q := TopPair.ofSubset ({x}ᶜ : Set (TopCat.of Y))
  -- The local image of the singular class is the relative singular class of the local image of
  -- the cubical class.
  have hloc (ν : ((normalizedCubicalChainComplex k).obj (TopCat.of Y)).homology n) :
      singularHomologyToLocalHomology (ModuleCat.of k k) x n (e.inv.hom ν) =
        (TopPair.singularCubicalHomologyIso k Q n).inv.hom
          ((HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
            Q.map)) n).hom ν) :=
    (singularHomologyToLocalHomology_eq_singularHomologyπ (ModuleCat.of k k) x
    (e.inv.hom ν)).trans (ConcreteCategory.congr_hom
      (TopPair.homologyMap_π_comp_singularCubicalHomologyIso_inv k Q n) ν).symm
  rw [hloc, hloc, h x hx]

/-- **A cycle glued from the faces represents the class with their local images.** Let `Y` be a
compact Hausdorff space modelled on a real normed space of finite dimension `n`, covered by faces
`fᵢ : Xᵢ ⟶ Y` with boundaries `Aᵢ ⊆ Xᵢ`, and let `z` be a normalized cubical `n`-cycle of `Y`
which is the sum of the push-forwards of chains `cᵢ` representing classes `aᵢ` of `Hₙ(Xᵢ, Aᵢ)`.
Suppose that every path component of `Y` contains a point `x` interior to a single face `i`: outside
the images of the other faces and of `Aᵢ`, at which `μ` has the local image of `aᵢ`. Then `z`
represents `μ`. -/
theorem homologyπ_eq_of_iCycles_eq_sum (hn : finrank ℝ E = n)
    (hc : ∀ i ∈ s, (TopPair.ofSubset (A i)).IsCubicalRepresentative k (c i) (a i))
    (hz : (((normalizedCubicalChainComplex k).obj (TopCat.of Y)).iCycles n).hom z =
      ∑ i ∈ s, NormalizedCubicalChain.map k (f i).hom n (c i))
    {μ : ((normalizedCubicalChainComplex k).obj (TopCat.of Y)).homology n}
    (hμ : ∀ y, ∃ x, Joined x y ∧ ∃ i ∈ s, ∃ hA : MapsTo (f i) (A i) ({x}ᶜ : Set (TopCat.of Y)),
      (∀ j ∈ s, j ≠ i → x ∉ range (f j)) ∧
        (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
          (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of Y))).map)) n).hom μ =
        (HomologicalComplex.homologyMap
          (TopPair.cubicalChainComplexMap k (TopPair.ofSubsetMap (f i) hA)) n).hom (a i)) :
    (((normalizedCubicalChainComplex k).obj (TopCat.of Y)).homologyπ n).hom z = μ := by
  refine cubicalHomology_ext_of_localHomology hn (D := {x | _})
    (fun y ↦ (hμ y).imp fun _ ⟨hxy, hx⟩ ↦ ⟨hx, hxy⟩) ?_
  rintro x ⟨i, hi, hA, hj, hloc⟩
  rw [homologyMap_cokernel_π_homologyπ_of_iCycles_eq_sum hc hz hi hA hj, hloc]

end Detect

end TauCeti
