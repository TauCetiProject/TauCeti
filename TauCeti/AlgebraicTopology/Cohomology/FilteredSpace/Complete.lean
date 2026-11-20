/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.FilteredSpace.Basic
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Complete
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.AlgebraicTopology.SimplicialSet.Cochains.Basic
import TauCeti.Algebra.Homology.Embedding.ExtendSubobject
import TauCeti.Algebra.Homology.Subobject
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

/-!
# Convergence of the cohomology spectral sequence of an exhaustive filtration of a space

Let `X : ℤ → Set Y` be an increasing family of subsets of a space `Y` absorbing compact sets:
every compact subset of `Y` lies in some `X q`. The family need not reach `Y` at any finite stage,
as for the preimages of the skeleta of an infinite-dimensional CW complex. The cohomology spectral
sequence of the filtered space (`TauCeti.filteredSpaceCohomologySpectralSequence`) is that of the
decreasing filtration of the singular cochains of `Y` by the cochains vanishing on the `X (p - 1)`.
In each degree this filtration has nonzero stages all the way down, so the convergence theorems
for finite filtrations do not apply. What replaces finiteness is completeness.

* **Stages.** A cochain lies in the stage at `q` exactly when it vanishes on every singular simplex
  whose image lies in `X q` (`TauCeti.mem_range_singularCochainFiltration_arrow_f_iff`).
* **Completeness.** In every degree the filtration is complete and separated
  (`TauCeti.isCompleteFiltration_singularCochainFiltration`). A cochain is the family of its
  restrictions to the singular simplices (`TauCeti.cochainComponentsLinearEquiv`), and in these
  coordinates the filtration is the weight filtration of a product
  (`TauCeti.isCompleteFiltration_pi`), the weight of a simplex being the first stage containing it.
  A singular simplex has compact image, so it has a weight.
* **Convergence.** If moreover `X (-1) = ∅` and `Hⁿ(X j, X (j - 1)) = 0` whenever `n < j`, the
  filtration is complete and first-quadrant. The induced filtration `F^p Hⁿ(Y)` of the abutment then
  vanishes for `n < p` (`TauCeti.isZero_filteredSpaceCohomologySpectralObject_abutmentFiltration`),
  and is everything for `p ≤ 0` (`CochainComplex.isIso_filtrationAbutmentFiltrationι`), so it is
  finite in each degree. The spectral sequence converges strongly: on every page `r` with `p < r`
  and `q + 1 < r` the object at `(p, q)` is the graded piece `F^p H / F^{p+1} H` of
  `H^{p+q}(Y)` (`TauCeti.filteredSpaceCohomologySpectralSequencePageXIsoGradedOfExhaustive`).

For the preimages of the skeleta of a CW complex under a Serre fibration the vanishing hypothesis
holds, which gives the convergence of the cohomology Serre spectral sequence over an arbitrary CW
complex (`TauCeti.AlgebraicTopology.Cohomology.Fibration.Convergence`).

## References

* C. A. Weibel, *An introduction to homological algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, Theorem 5.5.10 (complete convergence).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2 and Section 5.1.
* A. Hatcher, *Algebraic Topology*, Proposition A.1 (compact subsets of CW complexes).
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex
open scoped Simplicial

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (k : Type*)
  [Ring k] [Linear k C] (M : C) {Y : TopCat.{w}} {X : ℤ → Set Y}

/-- **The stages of the filtration of singular cochains.** A cochain of `Y` of degree `n` lies in
the stage at `q` of the filtration, the cochains relative to `X q`, exactly when it vanishes on
every singular `n`-simplex of `Y` whose image lies in `X q`. -/
theorem mem_range_singularCochainFiltration_arrow_f_iff (q : ℤ) {n : ℕ} {m : ℤ}
    (hn : ComplexShape.embeddingUpNat.f n = m)
    (x : ((Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat).X m) :
    x ∈ LinearMap.range ((singularCochainFiltration R k M X q).arrow.f m).hom ↔
      ∀ σ : (TopCat.toSSet.obj Y) _⦋n⦌, Set.range (Y.toSSetObjEquiv _ σ) ⊆ X q →
        (TopCat.toSSet.obj Y).ιChainComplex (R := R) σ ≫
          ((Y.singularCochainComplex R k M).extendXIso _ hn).hom x = 0 := by
  rw [← singularCochainFiltrationIso_hom_comp_singularCochainFiltrationι, comp_f,
    ModuleCat.hom_comp, LinearMap.range_comp_of_range_eq_top _ (ModuleCat.range_eq_top_of_epi _),
    singularCochainFiltrationι_def]
  refine (HomologicalComplex.mem_range_extendMap_f_iff _ _ hn x).trans ?_
  have h := TopPair.mem_range_linearYonedaFunctor_map_singularChainComplexπ_f_iff
    (TopPair.ofSubset (X q)) R k M n (((Y.singularCochainComplex R k M).extendXIso _ hn).hom x)
  rwa [TopPair.range_ofSubset_map] at h

/-- **The filtration of singular cochains by an exhaustive filtration of a space is complete.**
If every compact subset of `Y` lies in some `X q`, then in each degree the stages of the filtration
of the singular cochains of `Y` at `X (j - a)`, `j : ℕ`, form a complete separated filtration, for
every offset `a`. A cochain is determined by its restrictions to the singular simplices, and each
simplex lies in some `X (j - a)`. -/
theorem isCompleteFiltration_singularCochainFiltration (hX : Monotone X)
    (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q) (a m : ℤ) :
    IsCompleteFiltration fun j : ℕ ↦
      LinearMap.range ((singularCochainFiltration R k M X (j - a)).arrow.f m).hom := by
  classical
  by_cases hm : ∃ n : ℕ, ComplexShape.embeddingUpNat.f n = m
  · obtain ⟨n, hn⟩ := hm
    -- A singular simplex has compact image, so it lies in some stage `X (j - a)`.
    have hσ (σ : (TopCat.toSSet.obj Y) _⦋n⦌) :
        ∃ j : ℕ, Set.range (Y.toSSetObjEquiv _ σ) ⊆ X (j - a) := by
      obtain ⟨q, hq⟩ := hK _ (isCompact_range (Y.toSSetObjEquiv _ σ).continuous)
      exact ⟨(q + a).toNat, hq.trans (hX (by lia))⟩
    -- In the coordinates given by the simplices, the filtration is a weight filtration of a
    -- product, with the weight of a simplex the first stage containing it.
    let G : ℕ → Submodule k ((TopCat.toSSet.obj Y) _⦋n⦌ → (R ⟶ M)) := fun j ↦
      ⨅ (σ) (_ : Nat.find (hσ σ) < j), LinearMap.ker (LinearMap.proj σ)
    have hG := isCompleteFiltration_pi (fun σ ↦ Nat.find (hσ σ)) G fun j v ↦ by simp [G]
    convert ((hG.comp_add_right 1).comap_linearEquiv
      (cochainComponentsLinearEquiv k (TopCat.toSSet.obj Y) R M n)).comap_linearEquiv
        ((Y.singularCochainComplex R k M).extendXIso _ hn).toLinearEquiv using 1
    funext j
    ext x
    rw [mem_range_singularCochainFiltration_arrow_f_iff R k M _ hn]
    simp only [G, Submodule.mem_comap, Submodule.mem_iInf, LinearMap.mem_ker]
    -- A simplex lies in `X (j - a)` exactly when its weight is at most `j`; the coordinates of a
    -- cochain are its restrictions to the summands of the simplices.
    -- After unfolding the coordinates, the two conditions on the value differ only by the
    -- definitional identification of `Iso.toLinearEquiv` with the underlying map, closed by `rfl`.
    refine forall_congr' fun σ ↦ imp_congr ?_ (by
      rw [LinearMap.proj_apply, LinearEquiv.coe_coe, cochainComponentsLinearEquiv_apply]; rfl)
    rw [Nat.lt_succ_iff, Nat.find_le_iff]
    exact ⟨fun h ↦ ⟨j, le_rfl, h⟩, fun ⟨i, hi, h⟩ ↦ h.trans (hX (by lia))⟩
  · push Not at hm
    have : Subsingleton (((Y.singularCochainComplex R k M).extend
        ComplexShape.embeddingUpNat).X m) :=
      ModuleCat.isZero_iff_subsingleton.1 (isZero_extend_X _ _ m hm)
    exact
      { antitone _ _ _ x _ := by rw [Subsingleton.elim x 0]; exact zero_mem _
        eq_zero_of_forall_mem x _ := Subsingleton.elim x 0
        exists_limit x _ := ⟨0, fun j ↦ by rw [Subsingleton.elim (0 - x j) 0]; exact zero_mem _⟩ }

section Convergence

variable (hX : Monotone X)

/-- The graded piece `F^j/F^{j+1}` of the filtration of cochains, the relative cochains of
`(X j, X (j - 1))`, has no cohomology below degree `j` when `Hⁿ(X j, X (j - 1)) = 0` for `n < j`. -/
private lemma isZero_homology_cokernel_singularCochainFiltration_sub_one
    (hvanish : ∀ (j : ℤ) (n : ℕ), n < j →
      IsZero ((TopPair.ofInclusion (hX (by lia : j - 1 ≤ j))).singularCohomology R k M n))
    (j : ℤ) (n : ℤ) (hn : n < j) :
    IsZero ((cokernel (Subobject.ofLE (singularCochainFiltration R k M X (j + 1 - 1))
      (singularCochainFiltration R k M X (j - 1))
      (antitone_singularCochainFiltration_sub_one R k M hX (by lia)))).homology n) :=
  (isZero_homology_cokernel_singularCochainFiltration R k M (hX (by lia : j - 1 ≤ j)) n
    fun n' hn' ↦ hvanish j n' (by lia)).of_iso
    ((homologyFunctor _ _ n).mapIso (Subobject.cokernelOfLEIsoOfEq (by rw [add_sub_cancel_right])
      rfl _ _))

/-- **The filtration of the abutment of an exhaustive filtration of a space is finite.** Suppose
that every compact subset of `Y` lies in some `X q`, that `X (-1)` is empty and that the relative
cohomology `Hⁿ(X j, X (j - 1))` vanishes whenever `n < j`. Then the piece `F^p Hⁿ(Y)` of the
filtration of the abutment, the image of the cohomology of `Y` relative to `X (p - 1)`, vanishes for
`n < p`. -/
theorem isZero_filteredSpaceCohomologySpectralObject_abutmentFiltration
    (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q) (hempty : X (-1) = ∅)
    (hvanish : ∀ (j : ℤ) (n : ℕ), n < j →
      IsZero ((TopPair.ofInclusion (hX (by lia : j - 1 ≤ j))).singularCohomology R k M n))
    {p n : ℤ} (hn : n < p) :
    IsZero ((filteredSpaceCohomologySpectralObject R k M hX).abutmentFiltration (-p) n) :=
  CochainComplex.isZero_filtrationAbutmentFiltration_of_antitone_of_firstQuadrant _
    (antitone_singularCochainFiltration_sub_one R k M hX)
    (singularCochainFiltration_eq_top R k M (by rwa [zero_sub]))
    (isCompleteFiltration_singularCochainFiltration R k M hX hK 1)
    (fun j _ n hn ↦ isZero_homology_cokernel_singularCochainFiltration_sub_one R k M hX hvanish j n
      hn) hn

/-- **Strong convergence of the cohomology spectral sequence of an exhaustive filtration of a
space.** Suppose that every compact subset of `Y` lies in some `X q`, that `X (-1)` is empty and
that the relative cohomology `Hⁿ(X j, X (j - 1))` vanishes whenever `n < j`. Then on every page
`r ≥ 1` with `p < r` and `q + 1 < r`, the object at `(p, q)` is the graded piece
`F^p H / F^{p+1} H` of the filtration of the abutment in degree `p + q`, which is `H^{p+q}(Y)` by
`TauCeti.filteredSpaceCohomologyAbutmentIso`. No stage `X q` need be all of `Y`. -/
def filteredSpaceCohomologySpectralSequencePageXIsoGradedOfExhaustive
    (hK : ∀ K : Set Y, IsCompact K → ∃ q, K ⊆ X q) (hempty : X (-1) = ∅)
    (hvanish : ∀ (j : ℤ) (n : ℕ), n < j →
      IsZero ((TopPair.ofInclusion (hX (by lia : j - 1 ≤ j))).singularCohomology R k M n))
    (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) (hp : p < r) (hq : q + 1 < r) :
    ((filteredSpaceCohomologySpectralSequence R k M hX).page r).X (p, q) ≅
      cokernel ((filteredSpaceCohomologySpectralObject R k M hX).abutmentFiltrationMap (-p - 1)
        (p + q)) :=
  CochainComplex.decreasingFiltrationSpectralSequencePageXIsoGradedOfFirstQuadrant _
    (antitone_singularCochainFiltration_sub_one R k M hX)
    (singularCochainFiltration_eq_top R k M (by rwa [zero_sub]))
    (isCompleteFiltration_singularCochainFiltration R k M hX hK 1)
    (fun j _ n hn ↦ isZero_homology_cokernel_singularCochainFiltration_sub_one R k M hX hvanish j n
      hn) r hr p q hp hq

end Convergence

end TauCeti
