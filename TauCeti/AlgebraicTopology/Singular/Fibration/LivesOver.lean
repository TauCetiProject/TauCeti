/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.Convergence
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Exhaustive
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LivesOver
public import TauCeti.AlgebraicTopology.Singular.Triple

/-!
# Classes living over the fundamental class, read off a subspace of the base

Let `p : E → B` be a Serre fibration and `b ∈ B`. A class `α ∈ Hₖ(E)` lives over the fundamental
class at `b` when its localization `Hₖ(E) → Hₖ(E, E ∖ p⁻¹(b))` at the fibre is nonzero
(`TauCeti.LivesOverFundamentalClass`). This file replaces the complement of the fibre by the part
of `E` over a smaller subspace `A ⊆ B ∖ {b}` onto which `B ∖ {b}` deforms, relative to `A`. The
model case is a CW structure on `B` with a single top cell containing `b` in its interior, `A` its
codimension-one skeleton: radial projection in the top cell deforms `B ∖ {b}` onto `A`.

* The map `Hₖ(E, p⁻¹(A)) → Hₖ(E, E ∖ p⁻¹(b))` induced by the identity of `E` is an isomorphism
  (`TauCeti.TopCat.singularHomologyPreimageIsoLocalHomology`, stated for the part of `E` over any
  subset `S` of `B` in place of `{b}`): the pair `(E ∖ p⁻¹(b), p⁻¹(A))` is acyclic, because a Serre
  fibration pulls the deformation of `B ∖ {b}` into `A` back to an acyclic pair
  (`TauCeti.TopCat.isZero_singularHomology_preimage_of_homotopyRel`), and the long exact sequence of
  the triple `(E, E ∖ p⁻¹(b), p⁻¹(A))` does the rest.
* Under this isomorphism the localization at the fibre is the map `Hₖ(E) → Hₖ(E, p⁻¹(A))`
  (`TauCeti.TopCat.singularHomologyπ_comp_singularHomologyPreimageIsoLocalHomology_hom`). So `α`
  lives over the fundamental class at `b` exactly when its image in `Hₖ(E, p⁻¹(A))` is nonzero
  (`TauCeti.TopCat.livesOverFundamentalClass_iff_singularHomologyπ_ne_zero`), that is, exactly
  when `α` does not come from the homology of `p⁻¹(A)`
  (`TauCeti.TopCat.livesOverFundamentalClass_iff_notMem_range`).

For a CW model with a single top cell this is the description of the shriek map `j_!` of the
inclusion of `b` by Barraud, Damian, Humilière and Oancea, `Hₖ(E) → Hₖ(E, E|_{B'}) ≅ Hₖ₋ₙ(F_b)`
with `B'` the `(n - 1)`-skeleton (their Lemma 2.9 and Proposition 2.6); the identification of
`Hₖ(E, E ∖ p⁻¹(b))` with `Hₖ₋ₙ(p⁻¹(b))` over a chart is
`TauCeti.TopCat.singularHomologyComplFiberIso`.

In the Serre spectral sequence over a relative CW complex `C ⊆ B`
(`TauCeti.TopCat.serreSpectralSequence`) the image of `Hₖ(p⁻¹(skeletonLT C n))` in `Hₖ(E)` is the
piece `F_{n-1} Hₖ(E)` of the filtration of the abutment
(`TauCeti.range_abutmentFiltrationι_comp_filteredSpaceAbutmentIso_hom`). So, when `B ∖ {b}` deforms
into the `(n - 1)`-skeleton:

* `α` lives over the fundamental class at `b` exactly when `α ∉ F_{n-1} Hₖ(E)`
  (`TauCeti.TopCat.livesOverFundamentalClass_iff_notMem_range_abutmentFiltrationι`);
* a class of `F_n Hₖ(E)`, which is all of `Hₖ(E)` when `p` takes values in the `n`-skeleton
  (`TauCeti.TopCat.isIso_serreSpectralObject_abutmentFiltrationι_of_range_subset`), lives over the
  fundamental class at `b` exactly when its image in the top column
  `E^∞_{n,k-n} = F_n Hₖ(E) / F_{n-1} Hₖ(E)` is nonzero
  (`TauCeti.TopCat.livesOverFundamentalClass_iff_cokernel_π_ne_zero`). This is the
  characterization of Barraud–Damian–Humilière–Oancea's Proposition 2.6.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4, Lemma 2.9 and Proposition 2.6.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Set

namespace TauCeti

namespace TopCat

section Deformation

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p) (R : Type u) [Ring R]
  {S A : Set B} (hA : A ⊆ Sᶜ) {g : C((Sᶜ : Set B), (Sᶜ : Set B))}
  (H : (ContinuousMap.id _).HomotopyRel g (Subtype.val ⁻¹' A)) (hg : ∀ x, (g x : B) ∈ A)

variable (p) in
/-- The part of `E` over `A ⊆ B ∖ S` lies in the complement of the part over `S`. -/
lemma mapsTo_preimage_compl_preimage (hA : A ⊆ Sᶜ) : MapsTo (𝟙 E) (p ⁻¹' A) (p ⁻¹' S)ᶜ :=
  fun _ hx ↦ hA hx

include hp hA H hg in
/-- **The complement of the part over `S` deforms into the part over `A`, in homology.** Let
`p : E ⟶ B` be a Serre fibration and `A ⊆ B ∖ S`, and suppose that the identity of `B ∖ S` is
homotopic, relative to `A`, to a map with values in `A`. Then the identity of `E` induces
isomorphisms `Hₙ(E, p⁻¹(A); R) ≅ Hₙ(E, E ∖ p⁻¹(S); R)` in every degree. -/
theorem isIso_singularHomologyMap_ofSubsetMap_preimage_compl_preimage (n : ℕ) :
    IsIso (TopPair.singularHomologyMap
      (TopPair.ofSubsetMap (𝟙 E) (mapsTo_preimage_compl_preimage p hA)) (ModuleCat.of R R) n) := by
  -- The pair `(E ∖ p⁻¹(S), p⁻¹(A))` is acyclic, so the triple `(E, E ∖ p⁻¹(S), p⁻¹(A))` gives the
  -- isomorphism.
  have hz := isZero_singularHomology_preimage_of_homotopyRel hp hA H hg R
  let T := TopTriple.ofSubset (mapsTo_preimage_compl_preimage p hA)
  rw [← TopTriple.totalToOuter_app_ofSubset (mapsTo_preimage_compl_preimage p hA)]
  exact T.isIso_singularHomologyMap_totalToOuter_of_isZero _ n (hz n) fun m _ ↦ hz m

include hp hA H hg in
/-- **The local homology along the part over `S`, read off the part over `A`.** For a Serre
fibration `p : E ⟶ B` and `A ⊆ B ∖ S` such that the identity of `B ∖ S` is homotopic, relative to
`A`, to a map with values in `A`, the isomorphism `Hₙ(E, p⁻¹(A); R) ≅ Hₙ(E, E ∖ p⁻¹(S); R)` induced
by the identity of `E`. -/
def singularHomologyPreimageIsoLocalHomology (n : ℕ) :
    (TopPair.ofSubset (p ⁻¹' A)).singularHomology (ModuleCat.of R R) n ≅
      localHomology (ModuleCat.of R R) ((p : E → B) ⁻¹' S) n :=
  haveI := isIso_singularHomologyMap_ofSubsetMap_preimage_compl_preimage hp R hA H hg n
  asIso (TopPair.singularHomologyMap
    (TopPair.ofSubsetMap (𝟙 E) (mapsTo_preimage_compl_preimage p hA)) (ModuleCat.of R R) n)

include hp hA H hg in
@[simp]
lemma singularHomologyPreimageIsoLocalHomology_hom (n : ℕ) :
    (singularHomologyPreimageIsoLocalHomology hp R hA H hg n).hom =
      TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (𝟙 E) (mapsTo_preimage_compl_preimage p hA)) (ModuleCat.of R R) n :=
  (rfl)

include hp hA H hg in
/-- **The map to the local homology along `S` factors through the part over `A`.** Under
`TauCeti.TopCat.singularHomologyPreimageIsoLocalHomology`, the map
`Hₙ(E) → Hₙ(E, E ∖ p⁻¹(S))` is the map `Hₙ(E) → Hₙ(E, p⁻¹(A))`. For `S = {b}` the former is the
localization at the fibre `TauCeti.fiberLocalization`. -/
@[reassoc]
lemma singularHomologyπ_comp_singularHomologyPreimageIsoLocalHomology_hom (n : ℕ) :
    (TopPair.ofSubset (p ⁻¹' A)).singularHomologyπ (ModuleCat.of R R) n ≫
        (singularHomologyPreimageIsoLocalHomology hp R hA H hg n).hom =
      (TopPair.ofSubset ((p ⁻¹' S)ᶜ : Set E)).singularHomologyπ (ModuleCat.of R R) n :=
  TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id _ _ n

end Deformation

section Point

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p) (R : Type u) [Ring R]
  {b : B} {A : Set B} (hA : A ⊆ {b}ᶜ) {g : C(({b}ᶜ : Set B), ({b}ᶜ : Set B))}
  (H : (ContinuousMap.id _).HomotopyRel g (Subtype.val ⁻¹' A)) (hg : ∀ x, (g x : B) ∈ A)

include hp hA H hg in
/-- **Living over the fundamental class, read off the part over `A`.** For a Serre fibration
`p : E ⟶ B`, a point `b ∈ B` and `A ⊆ B ∖ {b}` such that the identity of `B ∖ {b}` is homotopic,
relative to `A`, to a map with values in `A`, a class `α ∈ Hₙ(E; R)` lives over the fundamental
class at `b` exactly when its image in `Hₙ(E, p⁻¹(A); R)` is nonzero. -/
theorem livesOverFundamentalClass_iff_singularHomologyπ_ne_zero {n : ℕ}
    (α : ((_root_.TopCat.toSSet.obj E).homology (ModuleCat.of R R) n : ModuleCat.{u} R)) :
    LivesOverFundamentalClass (ModuleCat.of R R) p b α ↔
      ((TopPair.ofSubset (p ⁻¹' A)).singularHomologyπ (ModuleCat.of R R) n).hom α ≠ 0 := by
  -- The localization at the fibre is `Hₙ(E) → Hₙ(E, p⁻¹(A))` followed by an isomorphism.
  rw [livesOverFundamentalClass_iff,
    ← (singularHomologyPreimageIsoLocalHomology hp R hA H hg n).toLinearEquiv.map_ne_zero_iff]
  exact (congrArg (fun f ↦ ModuleCat.Hom.hom f α ≠ 0)
    (singularHomologyπ_comp_singularHomologyPreimageIsoLocalHomology_hom hp R hA H hg
      n)).to_iff.symm

include hp hA H hg in
/-- **A class lives over the fundamental class exactly when it does not come from the part over
`A`.** For a Serre fibration `p : E ⟶ B`, a point `b ∈ B` and `A ⊆ B ∖ {b}` such that the identity
of `B ∖ {b}` is homotopic, relative to `A`, to a map with values in `A`, a class `α ∈ Hₙ(E; R)`
lives over the fundamental class at `b` exactly when it is not in the image of
`Hₙ(p⁻¹(A); R) → Hₙ(E; R)`. -/
theorem livesOverFundamentalClass_iff_notMem_range {n : ℕ}
    (α : ((_root_.TopCat.toSSet.obj E).homology (ModuleCat.of R R) n : ModuleCat.{u} R)) :
    LivesOverFundamentalClass (ModuleCat.of R R) p b α ↔
      α ∉ LinearMap.range (SSet.homologyMap
        (_root_.TopCat.toSSet.map (TopPair.ofSubset (p ⁻¹' A)).map) (ModuleCat.of R R) n).hom := by
  rw [livesOverFundamentalClass_iff_singularHomologyπ_ne_zero hp R hA H hg, not_iff_not,
    ((TopPair.ofSubset (p ⁻¹' A)).singularHomology_exact_space (ModuleCat.of R R)
      n).moduleCat_range_eq_ker]
  exact LinearMap.mem_ker.symm

end Point

section SpectralSequence

open Topology Topology.RelCWComplex

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p) (R : Type u) [Ring R]
  [T2Space B] {C D : Set B} [RelCWComplex C D] {b : B} {n : ℕ}
  (hA : (skeletonLT C n : Set B) ⊆ {b}ᶜ) {g : C(({b}ᶜ : Set B), ({b}ᶜ : Set B))}
  (H : (ContinuousMap.id _).HomotopyRel g (Subtype.val ⁻¹' skeletonLT C n))
  (hg : ∀ x, (g x : B) ∈ (skeletonLT C n : Set B))

variable (p C) in
/-- **Over an `n`-dimensional base the filtration of the abutment stops at `n`.** If `p` takes
values in the `n`-skeleton `skeletonLT C (n + 1)`, the piece `F_n Hₖ(E; R)` of the filtration of
the abutment of the Serre spectral sequence is all of `Hₖ(E; R)`. -/
theorem isIso_serreSpectralObject_abutmentFiltrationι_of_range_subset
    (hpn : range p ⊆ skeletonLT C ((n + 1 : ℕ) : ℕ∞)) (k : ℤ) :
    IsIso ((serreSpectralObject C p R).abutmentFiltrationι ((n : ℤ) - 1 + 1) k) :=
  CochainComplex.isIso_filtrationAbutmentFiltrationι _ _
    (singularChainFiltration_eq_top _ (eq_univ_of_forall fun x ↦ by
      rw [mem_preimageSkeleton_iff, show ((n : ℤ) - 1 + 1 + 1).toNat = n + 1 by lia]
      exact hpn (mem_range_self x))) k

include hp hA H hg in
/-- **Living over the fundamental class through the filtration of the Serre spectral sequence.**
Let `p : E ⟶ B` be a Serre fibration over a space containing a relative CW complex `C`, and let
`b ∈ B` be such that the identity of `B ∖ {b}` is homotopic, relative to the `(n - 1)`-skeleton
`skeletonLT C n`, to a map into it, as for a single top cell of dimension `n` containing `b` in its
interior. Then a class `α ∈ Hₖ(E; R)` lives over the fundamental class at `b` exactly when it does
not lie in the piece `F_{n-1} Hₖ(E; R)` of the filtration of the abutment of the Serre spectral
sequence. -/
theorem livesOverFundamentalClass_iff_notMem_range_abutmentFiltrationι {k : ℕ}
    (α : ((_root_.TopCat.toSSet.obj E).homology (ModuleCat.of R R) k : ModuleCat.{u} R)) :
    LivesOverFundamentalClass (ModuleCat.of R R) p b α ↔
      α ∉ LinearMap.range ((serreSpectralObject C p R).abutmentFiltrationι ((n : ℤ) - 1) (-k) ≫
        (filteredSpaceAbutmentIso (ModuleCat.of R R) (monotone_preimageSkeleton (C := C) p)
          k).hom).hom := by
  rw [range_abutmentFiltrationι_comp_filteredSpaceAbutmentIso_hom,
    livesOverFundamentalClass_iff_notMem_range hp R hA H hg, preimageSkeleton_natCast_sub_one]
  -- The two sides differ only in the instance arguments carried by the homology of `E`.
  exact Iff.rfl

include hp hA H hg in
/-- **Living over the fundamental class is detected in the top column `E^∞_{n,*}`.** Let
`p : E ⟶ B` be a Serre fibration over a space containing a relative CW complex `C`, and let
`b ∈ B` be such that the identity of `B ∖ {b}` is homotopic, relative to the `(n - 1)`-skeleton
`skeletonLT C n`, to a map into it, as for a single top cell of dimension `n` containing `b` in its
interior. Then a class of the piece `F_n Hₖ(E; R)` of the filtration of the abutment of the Serre
spectral sequence lives over the fundamental class at `b` exactly when its image in the graded
piece `F_n Hₖ(E; R) / F_{n-1} Hₖ(E; R)` is nonzero. This graded piece is the term `E^∞_{n,k-n}`
(`CategoryTheory.Abelian.SpectralObject.EInftyIsoCokernel`), and when `p` takes values in the
`n`-skeleton the piece `F_n Hₖ(E; R)` is all of `Hₖ(E; R)`
(`TauCeti.TopCat.isIso_serreSpectralObject_abutmentFiltrationι_of_range_subset`). -/
theorem livesOverFundamentalClass_iff_cokernel_π_ne_zero {k : ℕ}
    (x : (serreSpectralObject C p R).abutmentFiltration ((n : ℤ) - 1 + 1) (-k)) :
    LivesOverFundamentalClass (ModuleCat.of R R) p b
        (((serreSpectralObject C p R).abutmentFiltrationι _ (-k) ≫
          (filteredSpaceAbutmentIso (ModuleCat.of R R) (monotone_preimageSkeleton (C := C) p)
            k).hom).hom x) ↔
      (cokernel.π ((serreSpectralObject C p R).abutmentFiltrationMap ((n : ℤ) - 1) (-k))).hom x ≠
        0 := by
  -- Both conditions say that `x` does not come from `F_{n-1}`: the embedding of `F_n` into
  -- `Hₖ(E)` is injective and restricts to the embedding of `F_{n-1}`.
  refine (livesOverFundamentalClass_iff_notMem_range_abutmentFiltrationι hp R hA H hg _).trans ?_
  have hinj := (ModuleCat.mono_iff_injective ((serreSpectralObject C p R).abutmentFiltrationι
    ((n : ℤ) - 1 + 1) (-k) ≫ (filteredSpaceAbutmentIso (ModuleCat.of R R)
      (monotone_preimageSkeleton (C := C) p) k).hom)).1 inferInstance
  have hex := (ShortComplex.exact_cokernel
    ((serreSpectralObject C p R).abutmentFiltrationMap ((n : ℤ) - 1) (-k))).moduleCat_range_eq_ker
  rw [not_iff_not, ← LinearMap.mem_ker, ← hex]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, hinj ?_⟩
    rw [← ModuleCat.comp_apply, Abelian.SpectralObject.abutmentFiltrationMap_ι_assoc]
    exact hy
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    rw [← ModuleCat.comp_apply, Abelian.SpectralObject.abutmentFiltrationMap_ι_assoc]

end SpectralSequence

end TopCat

end TauCeti
