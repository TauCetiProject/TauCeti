/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.SubspaceCompl
public import TauCeti.AlgebraicTopology.Cohomology.Triple
public import TauCeti.AlgebraicTopology.Singular.Fibration.Disk

/-!
# Cohomology of a Serre fibration over a disk, relative to the boundary sphere

Let `p : E → K` be a Serre fibration whose base `K` is a convex neighbourhood of `0` in a real
normed space `V` of finite dimension `r`, and let `F = p⁻¹(0)` be the fibre over `0`. This file
computes the relative singular cohomology of `E` modulo the part of `E` over `K ∖ {0}`, with
coefficients `Hom(C(-; R), M)` for a projective module `R` and any module `M` (for instance
`R = M = ℤ`):

* `Hᵐ(E, p⁻¹(K ∖ {0}); R, M) = 0` for `m < r`
  (`TauCeti.TopCat.isZero_singularCohomology_preimage_ne_zero`);
* `Hⁿ(F; R, M) ≅ Hⁿ⁺ʳ(E, p⁻¹(K ∖ {0}); R, M)`
  (`TauCeti.TopCat.singularCohomologyPreimageNeZeroIso`).

For a Serre fibration `p : E → Dʳ` over the closed unit ball of `V` the same holds modulo the part
over the unit sphere `Sʳ⁻¹`:

* `Hᵐ(E, p⁻¹(Sʳ⁻¹); R, M) = 0` for `m < r`
  (`TauCeti.TopCat.isZero_singularCohomology_preimage_sphere`);
* `Hⁿ(F; R, M) ≅ Hⁿ⁺ʳ(E, p⁻¹(Sʳ⁻¹); R, M)` (`TauCeti.TopCat.singularCohomologyPreimageSphereIso`).

Both isomorphisms are natural in maps of fibrations over the base, which induce the maps of the
fibres over `0`. This is the computation over a single cell behind the first page of the
cohomological Serre spectral sequence of a fibration over a CW complex: pulled back along the
characteristic map of an `r`-cell, the fibration becomes a Serre fibration over `Dʳ`, and the
relative cohomology of the cell's part of the filtration is the cohomology of the fibre, shifted
by `r`. The homology counterpart is `TauCeti.TopCat.singularHomologyPreimageSphereIso`.

## The argument

The vanishing statements follow from the vanishing of relative homology in the same degrees
(`TauCeti.TopCat.isZero_singularHomology_preimage_ne_zero`,
`TauCeti.TopCat.isZero_singularHomology_preimage_sphere`), since with projective coefficients the
relative singular chains are projective
(`TopPair.isZero_singularCohomology_of_isZero_singularHomology`).

The isomorphism follows the homology computation. The part of `E` over the complement in `K` of
every closed half-subspace of `V` is acyclic
(`TauCeti.TopCat.isZero_singularHomology_preimage_compl_setOf_mem_and_nonpos`), hence has vanishing
relative cohomology, so the Mayer–Vietoris computation
`TauCeti.subspaceComplPairSingularCohomologyIso`, applied to the composite `E → K → V` and the zero
subspace, gives `Hⁿ(E) ≅ Hⁿ⁺ʳ(E, p⁻¹(K ∖ {0}))`. The pair `(E, F)` is acyclic, since `K` contracts
onto `0` along straight lines (`TauCeti.TopCat.isZero_singularHomology_preimage_of_starConvex`), so
restriction `Hⁿ(E) ⟶ Hⁿ(F)` is an isomorphism. Over the closed unit ball, the part of `E` over the
punctured ball is acyclic modulo the part over the sphere
(`TauCeti.TopCat.isZero_singularHomology_preimage_ne_zero_preimage_sphere`), so restriction from
`(E, p⁻¹(Dʳ ∖ {0}))` to `(E, p⁻¹(Sʳ⁻¹))` is an isomorphism
(`TauCeti.TopTriple.isIso_singularCohomologyMap_totalToOuter_of_isZero`). The projection
`E → K → V`, the pairs it defines and their naturality are shared with the homology computation
(`TauCeti.TopCat.SerreDisk.proj`, `TauCeti.TopCat.SerreDisk.botIso`).

## Main results

* `TauCeti.TopCat.isZero_singularCohomology_preimage_ne_zero`,
  `TauCeti.TopCat.singularCohomologyPreimageNeZeroIso`: the relative cohomology of `E` modulo the
  part over `K ∖ {0}`.
* `TauCeti.TopCat.isZero_singularCohomology_preimage_sphere`,
  `TauCeti.TopCat.singularCohomologyPreimageSphereIso`: the relative cohomology of `E` modulo the
  part over the boundary sphere, for a Serre fibration over the closed unit ball.
* `TauCeti.TopCat.singularCohomologyPreimageNeZeroIso_hom_naturality`,
  `TauCeti.TopCat.singularCohomologyPreimageSphereIso_hom_naturality`: both isomorphisms are
  natural in maps of fibrations over the base.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.D, the proof of Theorem 4D.10.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 5.1.
-/

public section

noncomputable section

open CategoryTheory Limits Module Metric Set Topology

universe u

namespace TauCeti

namespace TopCat

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {K : Set V}
  {E E' : _root_.TopCat.{u}} {p : E ⟶ _root_.TopCat.of K} {A : Type*} [Ring A]
  (R : ModuleCat.{u} A) [Projective R] (k : Type*) [Ring k] [Linear k (ModuleCat.{u} A)]
  (M : ModuleCat.{u} A)

open SerreDisk

namespace SerreDiskCohomology

/-- The part of `E` over the complement of a closed half-subspace has vanishing cohomology. -/
private lemma isZero_half (hp : serreFibrations p) (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V))
    (W : Submodule ℝ V) (φ : V →ₗ[ℝ] ℝ) (v : V) (hv : v ∈ W) (hφv : φ v = 1) (n : ℕ) :
    IsZero ((TopPair.ofSubset (proj p ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ)).singularCohomology R k M n) := by
  rw [preimage_proj]
  exact TopPair.isZero_singularCohomology_of_isZero_singularHomology _ R M n fun j _ ↦
    isZero_singularHomology_preimage_compl_setOf_mem_and_nonpos R hp hK hK₀ W φ v hv hφv j

/-- `Hⁿ(E, ∅) ≅ Hⁿ(F)`: the pair `(E, F)` is acyclic, since the base contracts onto `0` along
straight lines, so restriction to the fibre is an isomorphism. -/
private def emptyIso (hp : serreFibrations p) (hK : Convex ℝ K) (h₀ : (0 : V) ∈ K) (n : ℕ) :
    (pair p (⊤ : Submodule ℝ V)).singularCohomology R k M n ≅
      (_root_.TopCat.of (p ⁻¹' {x : K | (x : V) = 0})).singularCohomology R k M n :=
  -- The fibre is written `p⁻¹{x | (x : V) ∈ {0}}` here, the form taken by
  -- `TauCeti.TopCat.isZero_singularHomology_preimage_of_starConvex`. It is definitionally the
  -- fibre `p⁻¹{x | (x : V) = 0}` of the statement, since `Set.mem_singleton_iff` is `Iff.rfl`.
  have h (m : ℕ) := TopPair.isZero_singularCohomology_of_isZero_singularHomology
    (TopPair.ofSubset (p ⁻¹' {x : K | (x : V) ∈ ({0} : Set V)})) R (k := k) M m fun j _ ↦
      isZero_singularHomology_preimage_of_starConvex R hp hK h₀ (starConvex_singleton (0 : V)) rfl j
  asIso ((pair p (⊤ : Submodule ℝ V)).singularCohomologyπ R k M n) ≪≫
    @asIso _ _ _ _ _ (TopPair.isIso_singularCohomologyMap_map_of_isZero _ R k M (h n) (h (n + 1)))

private lemma emptyIso_hom (hp : serreFibrations p) (hK : Convex ℝ K) (h₀ : (0 : V) ∈ K)
    (n : ℕ) :
    (emptyIso R k M hp hK h₀ n).hom =
      (pair p (⊤ : Submodule ℝ V)).singularCohomologyπ R k M n ≫
        TopCat.singularCohomologyMap
          (TopPair.ofSubset (p ⁻¹' {x : K | (x : V) ∈ ({0} : Set V)})).map n :=
  rfl

end SerreDiskCohomology

open SerreDiskCohomology

variable [FiniteDimensional ℝ V]

/-- **A Serre fibration over a convex neighbourhood of `0` has vanishing cohomology modulo the
part over the punctured base, below the dimension.** Let `K` be a convex neighbourhood of `0` in a
finite-dimensional real normed space `V`, and let `p : E ⟶ K` be a Serre fibration. Then
`Hᵐ(E, p⁻¹(K ∖ {0}); R, M) = 0` for every `m < dim V`. -/
theorem isZero_singularCohomology_preimage_ne_zero (hp : serreFibrations p) (hK : Convex ℝ K)
    (hK₀ : K ∈ 𝓝 (0 : V)) {m : ℕ} (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (p ⁻¹' {x : K | (x : V) ≠ 0})).singularCohomology R k M m) :=
  TopPair.isZero_singularCohomology_of_isZero_singularHomology _ R M m fun _ hj ↦
    isZero_singularHomology_preimage_ne_zero R hp hK hK₀ (hj.trans_lt hm)

/-- **The cohomology of a Serre fibration over a convex neighbourhood of `0`, modulo the part over
the punctured base, is the shifted cohomology of the fibre over `0`.** Let `K` be a convex
neighbourhood of `0` in a real normed space `V` of finite dimension `r`, and let `p : E ⟶ K` be a
Serre fibration. Then `Hⁿ(p⁻¹(0); R, M) ≅ Hᵐ(E, p⁻¹(K ∖ {0}); R, M)` for `m = n + r`.

The isomorphism is the inverse of restriction from `E` to the fibre, followed by the composite of
`r` Mayer–Vietoris connecting morphisms, for a fixed choice of a flag of subspaces of `V`
(`Submodule.lineExtension`). -/
def singularCohomologyPreimageNeZeroIso (hp : serreFibrations p) (hK : Convex ℝ K)
    (hK₀ : K ∈ 𝓝 (0 : V)) (n m : ℕ) (h : n + finrank ℝ V = m) :
    (_root_.TopCat.of (p ⁻¹' {x : K | (x : V) = 0})).singularCohomology R k M n ≅
      (TopPair.ofSubset (p ⁻¹' {x : K | (x : V) ≠ 0})).singularCohomology R k M m :=
  (emptyIso R k M hp hK (mem_of_mem_nhds hK₀) n).symm ≪≫
    subspaceComplPairSingularCohomologyIso R k M (proj p) (isZero_half R k M hp hK hK₀)
      (finrank ℝ V) ⊥ (by simp) n m h ≪≫
    TopPair.singularCohomologyMapIso R k M (botIso p) m

private lemma singularCohomologyPreimageNeZeroIso_hom (hp : serreFibrations p) (hK : Convex ℝ K)
    (hK₀ : K ∈ 𝓝 (0 : V)) (n m : ℕ) (h : n + finrank ℝ V = m) :
    (singularCohomologyPreimageNeZeroIso R k M hp hK hK₀ n m h).hom =
      (emptyIso R k M hp hK (mem_of_mem_nhds hK₀) n).inv ≫
        (subspaceComplPairSingularCohomologyIso R k M (proj p) (isZero_half R k M hp hK hK₀)
          (finrank ℝ V) ⊥ (by simp) n m h).hom ≫
        TopPair.singularCohomologyMap (botIso p).hom m := by
  simp only [singularCohomologyPreimageNeZeroIso, Iso.trans_hom, Iso.symm_hom,
    TopPair.singularCohomologyMapIso_hom]

section Sphere

variable {p : E ⟶ _root_.TopCat.of (closedBall (0 : V) 1)}

omit [FiniteDimensional ℝ V] in
/-- Restriction from `(E, p⁻¹(Dʳ ∖ {0}))` to `(E, p⁻¹(Sʳ⁻¹))` is an isomorphism, since the part of
`E` over the punctured ball is acyclic modulo the part over the sphere. -/
private lemma isIso_totalToOuter (hp : serreFibrations p) (m : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (TopTriple.totalToOuter.app
        (TopTriple.ofSubset (preimage_sphere_subset_preimage_ne_zero p))) m) :=
  have h (j : ℕ) := TopPair.isZero_singularCohomology_of_isZero_singularHomology
    (TopTriple.innerPair.obj
      (TopTriple.ofSubset (preimage_sphere_subset_preimage_ne_zero p)))
    R (k := k) M j fun i _ ↦ isZero_singularHomology_preimage_ne_zero_preimage_sphere R hp i
  TopTriple.isIso_singularCohomologyMap_totalToOuter_of_isZero _ R k M m (h m) fun j _ ↦ h j

/-- **A Serre fibration over a disk has vanishing cohomology modulo the part over the boundary
sphere, below the dimension.** Let `p : E ⟶ Dʳ` be a Serre fibration over the closed unit ball of
a finite-dimensional real normed space of dimension `r`. Then `Hᵐ(E, p⁻¹(Sʳ⁻¹); R, M) = 0` for every
`m < r`. -/
theorem isZero_singularCohomology_preimage_sphere (hp : serreFibrations p) {m : ℕ}
    (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (p ⁻¹' {x | (x : V) ∈ sphere (0 : V) 1})).singularCohomology
      R k M m) :=
  TopPair.isZero_singularCohomology_of_isZero_singularHomology _ R M m fun _ hj ↦
    isZero_singularHomology_preimage_sphere R hp (hj.trans_lt hm)

/-- **The cohomology of a Serre fibration over a disk, modulo the part over the boundary sphere,
is the shifted cohomology of the fibre over the centre.** Let `p : E ⟶ Dʳ` be a Serre fibration
over the closed unit ball of a real normed space of finite dimension `r`. Then
`Hⁿ(p⁻¹(0); R, M) ≅ Hᵐ(E, p⁻¹(Sʳ⁻¹); R, M)` for `m = n + r`.

The isomorphism is `TauCeti.TopCat.singularCohomologyPreimageNeZeroIso` followed by restriction
along the inclusion `(E, p⁻¹(Sʳ⁻¹)) ⟶ (E, p⁻¹(Dʳ ∖ {0}))`. -/
def singularCohomologyPreimageSphereIso (hp : serreFibrations p) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    (_root_.TopCat.of (p ⁻¹' {x | (x : V) = 0})).singularCohomology R k M n ≅
      (TopPair.ofSubset (p ⁻¹' {x | (x : V) ∈ sphere (0 : V) 1})).singularCohomology R k M m :=
  singularCohomologyPreimageNeZeroIso R k M hp (convex_closedBall 0 1)
      (closedBall_mem_nhds 0 one_pos) n m h ≪≫
    @asIso _ _ _ _ _ (isIso_totalToOuter R k M hp m)

private lemma singularCohomologyPreimageSphereIso_hom (hp : serreFibrations p) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    (singularCohomologyPreimageSphereIso R k M hp n m h).hom =
      (singularCohomologyPreimageNeZeroIso R k M hp (convex_closedBall 0 1)
        (closedBall_mem_nhds 0 one_pos) n m h).hom ≫
        TopPair.singularCohomologyMap (TopTriple.totalToOuter.app
          (TopTriple.ofSubset (preimage_sphere_subset_preimage_ne_zero p))) m :=
  rfl

end Sphere

/-! ### Naturality in maps of fibrations -/

section Naturality

namespace SerreDiskCohomology

variable {p' : E' ⟶ _root_.TopCat.of K} {f : E ⟶ E'}

omit [FiniteDimensional ℝ V] in
@[reassoc]
private lemma emptyIso_hom_naturality (hp : serreFibrations p) (hp' : serreFibrations p')
    (hK : Convex ℝ K) (h₀ : (0 : V) ∈ K) (hf : f ≫ p' = p)
    (g : _root_.TopCat.of (p ⁻¹' {x : K | (x : V) = 0}) ⟶
      _root_.TopCat.of (p' ⁻¹' {x : K | (x : V) = 0}))
    (hg : ∀ x, (g x : E') = f x) (n : ℕ) :
    TopPair.singularCohomologyMap
        (subspaceComplPairMap f (proj_apply_of_comp_eq hf) (mapsTo_empty _ _) ⊤) n ≫
        (emptyIso R k M hp hK h₀ n).hom =
      (emptyIso R k M hp' hK h₀ n).hom ≫ TopCat.singularCohomologyMap g n := by
  -- As in `emptyIso`, the fibres are written with `∈ {0}`, definitionally equal to `= 0`.
  let ι := (TopPair.ofSubset (p ⁻¹' {x : K | (x : V) ∈ ({0} : Set V)})).map
  let ι' := (TopPair.ofSubset (p' ⁻¹' {x : K | (x : V) ∈ ({0} : Set V)})).map
  -- On the fibres, `g` followed by the inclusion is the inclusion followed by `f`.
  have hgι : g ≫ ι' = ι ≫ f := by
    ext x
    exact hg x
  have hH : TopCat.singularCohomologyMap (R := R) (k := k) (M := M) ι' n ≫
      TopCat.singularCohomologyMap g n =
        TopCat.singularCohomologyMap f n ≫ TopCat.singularCohomologyMap ι n :=
    (TopCat.singularCohomologyMap_comp g ι' n).symm.trans
      ((congrArg (TopCat.singularCohomologyMap · n) hgι).trans
        (TopCat.singularCohomologyMap_comp ι f n))
  have hπ := TopPair.singularCohomologyπ_naturality (R := R) (k := k) (M := M)
    (subspaceComplPairMap f (proj_apply_of_comp_eq hf) (mapsTo_empty f (∅ : Set E')) ⊤) n
  rw [subspaceComplPairMap_fst] at hπ
  rw [emptyIso_hom, emptyIso_hom]
  -- Chase the square of `g` and `f` through the inclusions of the fibres, then use the
  -- naturality of the map from relative to absolute cohomology. The objects of these composites
  -- (`(pair p ⊤).fst`, `(TopPair.ofSubset _).fst`, `E`) agree only after unfolding
  -- `TopPair.ofSubset`, so `rw`, `simp` and `calc` cannot reassociate them and the chase is
  -- assembled as a term, which is checked up to definitional unfolding.
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ TopCat.singularCohomologyMap ι n) hπ.symm)).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hH.symm).trans
        (Category.assoc _ _ _).symm))

omit [FiniteDimensional ℝ V] in
@[reassoc]
private lemma emptyIso_inv_naturality (hp : serreFibrations p) (hp' : serreFibrations p')
    (hK : Convex ℝ K) (h₀ : (0 : V) ∈ K) (hf : f ≫ p' = p)
    (g : _root_.TopCat.of (p ⁻¹' {x : K | (x : V) = 0}) ⟶
      _root_.TopCat.of (p' ⁻¹' {x : K | (x : V) = 0}))
    (hg : ∀ x, (g x : E') = f x) (n : ℕ) :
    (emptyIso R k M hp' hK h₀ n).inv ≫
        TopPair.singularCohomologyMap
          (subspaceComplPairMap f (proj_apply_of_comp_eq hf) (mapsTo_empty _ _) ⊤) n =
      TopCat.singularCohomologyMap g n ≫ (emptyIso R k M hp hK h₀ n).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv,
    emptyIso_hom_naturality R k M hp hp' hK h₀ hf g hg n]

end SerreDiskCohomology

open SerreDiskCohomology

/-- **The cohomology of a Serre fibration over a convex neighbourhood of `0`, modulo the part over
the punctured base, is natural in maps of fibrations.** Let `p : E ⟶ K` and `p' : E' ⟶ K` be Serre
fibrations and `f : E ⟶ E'` a map over `K`, restricting to `g` on the fibres over `0`. Under the
isomorphisms `Hⁿ(p⁻¹(0); R, M) ≅ Hᵐ(E, p⁻¹(K ∖ {0}); R, M)` of
`TauCeti.TopCat.singularCohomologyPreimageNeZeroIso`, the map induced by `f` on relative
cohomology is the map induced by `g` on the cohomology of the fibres. -/
@[reassoc]
theorem singularCohomologyPreimageNeZeroIso_hom_naturality {p' : E' ⟶ _root_.TopCat.of K}
    {f : E ⟶ E'} (hp : serreFibrations p) (hp' : serreFibrations p') (hK : Convex ℝ K)
    (hK₀ : K ∈ 𝓝 (0 : V)) (hf : f ≫ p' = p)
    (g : _root_.TopCat.of (p ⁻¹' {x : K | (x : V) = 0}) ⟶
      _root_.TopCat.of (p' ⁻¹' {x : K | (x : V) = 0}))
    (hg : ∀ x, (g x : E') = f x) (n m : ℕ) (h : n + finrank ℝ V = m) :
    (singularCohomologyPreimageNeZeroIso R k M hp' hK hK₀ n m h).hom ≫
        TopPair.singularCohomologyMap (TopPair.ofSubsetMap f (f.mapsTo_preimage_of_comp_eq hf _))
          m =
      TopCat.singularCohomologyMap g n ≫
        (singularCohomologyPreimageNeZeroIso R k M hp hK hK₀ n m h).hom := by
  rw [singularCohomologyPreimageNeZeroIso_hom, singularCohomologyPreimageNeZeroIso_hom,
    Category.assoc, Category.assoc, ← TopPair.singularCohomologyMap_comp,
    ← botIso_hom_naturality hf, TopPair.singularCohomologyMap_comp,
    subspaceComplPairSingularCohomologyIso_hom_naturality_assoc R k M
      (isZero_half R k M hp hK hK₀) (isZero_half R k M hp' hK hK₀) f (proj_apply_of_comp_eq hf),
    emptyIso_inv_naturality_assoc R k M hp hp' hK (mem_of_mem_nhds hK₀) hf g hg n]

variable {p : E ⟶ _root_.TopCat.of (closedBall (0 : V) 1)}
  {p' : E' ⟶ _root_.TopCat.of (closedBall (0 : V) 1)} {f : E ⟶ E'}

/-- **The cohomology of a Serre fibration over a disk relative to the boundary sphere is natural
in maps of fibrations.** Let `p : E ⟶ Dʳ` and `p' : E' ⟶ Dʳ` be Serre fibrations and `f : E ⟶ E'`
a map over `Dʳ`, restricting to `g` on the fibres over the centre. Under the isomorphisms
`Hⁿ(p⁻¹(0); R, M) ≅ Hᵐ(E, p⁻¹(Sʳ⁻¹); R, M)` of `TauCeti.TopCat.singularCohomologyPreimageSphereIso`,
the map induced by `f` on relative cohomology is the map induced by `g` on the cohomology of the
fibres. -/
@[reassoc]
theorem singularCohomologyPreimageSphereIso_hom_naturality (hp : serreFibrations p)
    (hp' : serreFibrations p') (hf : f ≫ p' = p)
    (g : _root_.TopCat.of (p ⁻¹' {x | (x : V) = 0}) ⟶ _root_.TopCat.of (p' ⁻¹' {x | (x : V) = 0}))
    (hg : ∀ x, (g x : E') = f x) (n m : ℕ) (h : n + finrank ℝ V = m) :
    (singularCohomologyPreimageSphereIso R k M hp' n m h).hom ≫
        TopPair.singularCohomologyMap (TopPair.ofSubsetMap f (f.mapsTo_preimage_of_comp_eq hf _))
          m =
      TopCat.singularCohomologyMap g n ≫
        (singularCohomologyPreimageSphereIso R k M hp n m h).hom := by
  -- The inclusion `(E, p⁻¹(Sʳ⁻¹)) ⟶ (E, p⁻¹(Dʳ ∖ {0}))` commutes with the maps induced by `f`.
  have hpair : TopPair.ofSubsetMap f (f.mapsTo_preimage_of_comp_eq hf _) ≫
        TopTriple.totalToOuter.app
          (TopTriple.ofSubset (preimage_sphere_subset_preimage_ne_zero p')) =
      TopTriple.totalToOuter.app
          (TopTriple.ofSubset (preimage_sphere_subset_preimage_ne_zero p)) ≫
        TopPair.ofSubsetMap f (f.mapsTo_preimage_of_comp_eq hf {x | (x : V) ≠ 0}) :=
    TopPair.hom_ext_of_fst _ (by
      ext x
      exact (TopPair.ofSubsetMap_fst_apply f _ x).trans (TopPair.ofSubsetMap_fst_apply f
        (f.mapsTo_preimage_of_comp_eq hf {x | (x : V) ≠ 0}) x).symm)
  have hTO : TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (TopTriple.totalToOuter.app
        (TopTriple.ofSubset (preimage_sphere_subset_preimage_ne_zero p'))) m ≫
        TopPair.singularCohomologyMap (TopPair.ofSubsetMap f (f.mapsTo_preimage_of_comp_eq hf _))
          m =
      TopPair.singularCohomologyMap (TopPair.ofSubsetMap f
          (f.mapsTo_preimage_of_comp_eq hf {x | (x : V) ≠ 0})) m ≫
        TopPair.singularCohomologyMap (TopTriple.totalToOuter.app
          (TopTriple.ofSubset (preimage_sphere_subset_preimage_ne_zero p))) m :=
    (TopPair.singularCohomologyMap_comp _ _ m).symm.trans
      ((congrArg (TopPair.singularCohomologyMap · m) hpair).trans
        (TopPair.singularCohomologyMap_comp _ _ m))
  rw [singularCohomologyPreimageSphereIso_hom, singularCohomologyPreimageSphereIso_hom]
  -- Move the inclusion past `f` with `hTO`, then use the naturality of
  -- `singularCohomologyPreimageNeZeroIso`. As in `emptyIso_hom_naturality`, the objects of these
  -- composites agree only after unfolding `TopPair.ofSubset` and `TopTriple.outerPair`, so the
  -- chase is assembled as a term rather than with `rw` or `simp`.
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hTO).trans
    (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
      (singularCohomologyPreimageNeZeroIso_hom_naturality R k M hp hp' (convex_closedBall 0 1)
        (closedBall_mem_nhds 0 one_pos) hf g hg n m h))).trans (Category.assoc _ _ _)))

end Naturality

end TopCat

end TauCeti
