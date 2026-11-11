/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Sequence
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Convergence
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Indexing
public import TauCeti.AlgebraicTopology.Cohomology.Triple
import TauCeti.Algebra.Homology.Embedding.ExtendSubobject

/-!
# The cohomological spectral sequence of a filtered space

Let `X : ℤ → Set Y` be an increasing family of subsets of a topological space `Y`, for instance
the preimages of the skeleta of a CW complex under a map to it. The relative singular cochains of
the pairs `(Y, X (p - 1))`, the cochains of `Y` vanishing on the singular simplices of `X (p - 1)`,
form a decreasing filtration `F^p` of the singular cochains of `Y`
(`TauCeti.singularCochainFiltration`). This file studies the spectral sequence of that filtered
complex (`TauCeti.filteredSpaceCohomologySpectralSequence`), in the classical cohomological
indexing of `CochainComplex.decreasingFiltrationSpectralSequence`. The filtered complexes of
`TauCeti.Algebra.Homology.SpectralSequence.Filtered` are indexed by `ℤ`, so the singular cochains,
indexed by `ℕ`, are extended by zero along `ComplexShape.embeddingUpNat`.

* **Stages.** For a subset `S` of `Y`, the relative cochains of `(Y, S)` form a subcomplex of the
  cochains of `Y` (`TauCeti.relativeSingularCochainSubobject`). It is everything when `S` is
  empty and zero when `S` is all of `Y`, and it decreases as `S` grows.
* **Graded pieces.** For `S ⊆ T`, the quotient of the relative cochains of `(Y, S)` by those of
  `(Y, T)` is the relative cochain complex of `(T, S)`
  (`TauCeti.relativeSingularCochainSubobjectCokernelIso`), by the short exact cochain sequence of
  the triple `(Y, T, S)`.
* **First page.** The object at `(p, q)` on the first page is the relative singular cohomology
  `Hⁿ(X p, X (p - 1))` with `p + q = n`
  (`TauCeti.filteredSpaceCohomologySpectralSequenceFirstPageXIso`); it vanishes when `p + q < 0`.
* **Convergence.** The abutment in degree `n` is `Hⁿ(Y)`
  (`TauCeti.filteredSpaceCohomologyAbutmentIso`). When `X b = ∅` and `X a = Y`, the filtration
  is finite and the spectral sequence converges strongly
  (`TauCeti.filteredSpaceCohomologySpectralSequencePageXIsoGradedOfFinite`).

For a Serre fibration over a CW complex, filtered by the preimages of the skeleta of the base, this
is the cohomological Serre spectral sequence; its stages need not vanish over an
infinite-dimensional base, where convergence rests on the completeness of the cochain filtration
instead of its finiteness.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2, the spectral sequence of a filtered differential graded module, and Chapter 5,
  its application to the cochains of a fibration.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C) {Y : TopCat.{w}}

/-! ### The relative cochains of a subset as a subcomplex -/

section Subobject

/-- The inclusion of the relative singular cochains of `(Y, S)` into the singular cochains of `Y`,
with both cochain complexes extended by zero to complexes indexed by `ℤ`. -/
def relativeSingularCochainι (S : Set Y) :
    ((TopPair.ofSubset S).singularCochainComplex R k M).extend ComplexShape.embeddingUpNat ⟶
      (Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat :=
  extendMap ((TopPair.ofSubset S).singularCochainComplexShortComplex R k M).f _

/-- The inclusion of relative cochains is induced by the quotient map from the singular chains of
`Y` to the relative singular chains of `(Y, S)`. -/
lemma relativeSingularCochainι_def (S : Set Y) :
    relativeSingularCochainι R k M S =
      extendMap ((TopPair.ofSubset S).singularCochainComplexShortComplex R k M).f
        ComplexShape.embeddingUpNat := (rfl)

instance (S : Set Y) : Mono (relativeSingularCochainι R k M S) := by
  have := ((TopPair.ofSubset S).shortExact_singularCochainComplexShortComplex R k M).mono_f
  have (n : ℕ) : Mono (((TopPair.ofSubset S).singularCochainComplexShortComplex R k M).f.f n) :=
    (HomologicalComplex.eval (ModuleCat.{v} k) (ComplexShape.up ℕ) n).map_mono
      ((TopPair.ofSubset S).singularCochainComplexShortComplex R k M).f
  rw [relativeSingularCochainι_def]
  exact mono_extendMap_of_mono_f _ _

/-- The relative singular cochains of `(Y, S)`, the cochains vanishing on the singular simplices
of `S`, as a subcomplex of the singular cochains of `Y`, extended by zero to a complex indexed by
`ℤ`. -/
def relativeSingularCochainSubobject (S : Set Y) :
    Subobject ((Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat) :=
  Subobject.mk (relativeSingularCochainι R k M S)

/-- The subcomplex of relative cochains of `(Y, S)` is the extended relative cochain complex of
`(Y, S)`. -/
def relativeSingularCochainSubobjectIso (S : Set Y) :
    (relativeSingularCochainSubobject R k M S : CochainComplex (ModuleCat.{v} k) ℤ) ≅
      ((TopPair.ofSubset S).singularCochainComplex R k M).extend ComplexShape.embeddingUpNat :=
  Subobject.underlyingIso (relativeSingularCochainι R k M S)

/-- The identification of the subcomplex of relative cochains with the relative cochain complex
is compatible with the inclusions into the cochains of `Y`. -/
@[reassoc (attr := simp)]
lemma relativeSingularCochainSubobjectIso_hom_comp_relativeSingularCochainι (S : Set Y) :
    (relativeSingularCochainSubobjectIso R k M S).hom ≫ relativeSingularCochainι R k M S =
      (relativeSingularCochainSubobject R k M S).arrow :=
  Subobject.underlyingIso_hom_comp_eq_mk _

variable {R k M}

/-- For `S ⊆ T`, the relative cochain map of the map of pairs `(Y, S) ⟶ (Y, T)`, followed by the
inclusion of the relative cochains of `(Y, S)`, is the inclusion of the relative cochains of
`(Y, T)`: a cochain vanishing on `T` vanishes on `S`. -/
@[reassoc]
lemma extendMap_comp_relativeSingularCochainι {S T : Set Y} (h : S ⊆ T) :
    extendMap ((TopTriple.ofSubset h).singularCochainComplexShortComplex R k M).f
        ComplexShape.embeddingUpNat ≫ relativeSingularCochainι R k M S =
      relativeSingularCochainι R k M T := by
  rw [relativeSingularCochainι_def, relativeSingularCochainι_def]
  -- The chain-level identity `π_{(Y, S)} ≫ ((Y, S) ⟶ (Y, T)) = π_{(Y, T)}` of the triple
  -- `(Y, T, S)`, under the contravariant functor `Hom(-, M)`. The pairs of the triple are the pairs
  -- `(Y, S)` and `(Y, T)` only up to unfolding the triple, so the composites are formed with
  -- `exact` rather than `rw`.
  exact (extendMap_comp _ _ _).symm.trans <| congrArg (extendMap · _) <|
    (Functor.map_comp _ _ _).symm.trans <|
    congrArg (fun f ↦ (TauCeti.ChainComplex.linearYonedaFunctor k M).map f.op)
      ((TopTriple.ofSubset h).singularChainComplexπ_comp_totalToOuter R)

/-- The relative cochains of `(Y, S)` decrease as `S` grows. -/
lemma relativeSingularCochainSubobject_anti {S T : Set Y} (h : S ⊆ T) :
    relativeSingularCochainSubobject R k M T ≤ relativeSingularCochainSubobject R k M S :=
  Subobject.mk_le_mk_of_comm _ (extendMap_comp_relativeSingularCochainι h)

/-- Under the identifications of the subcomplexes of relative cochains with relative cochain
complexes, the inclusion for `S ⊆ T` is the relative cochain map of `(Y, S) ⟶ (Y, T)`. -/
@[reassoc]
lemma ofLE_comp_relativeSingularCochainSubobjectIso_hom {S T : Set Y} (h : S ⊆ T) :
    Subobject.ofLE _ _ (relativeSingularCochainSubobject_anti (R := R) (k := k) (M := M) h) ≫
        (relativeSingularCochainSubobjectIso R k M S).hom =
      (relativeSingularCochainSubobjectIso R k M T).hom ≫
        extendMap ((TopTriple.ofSubset h).singularCochainComplexShortComplex R k M).f
          ComplexShape.embeddingUpNat :=
  (Iso.eq_comp_inv _).1 <| (Subobject.ofLE_mk_le_mk_of_comm
    (f₁ := relativeSingularCochainι R k M T) (f₂ := relativeSingularCochainι R k M S) _
    (extendMap_comp_relativeSingularCochainι h)).trans (Category.assoc _ _ _).symm

/-- The relative cochains of `(Y, ∅)` are all the cochains of `Y`. -/
@[simp]
lemma relativeSingularCochainSubobject_eq_top {S : Set Y} (hS : S = ∅) :
    relativeSingularCochainSubobject R k M S = ⊤ := by
  have : IsEmpty (TopPair.ofSubset S).snd := by
    rw [hS]
    exact Set.isEmpty_coe_sort.2 rfl
  have hS' := (TopPair.ofSubset S).shortExact_singularCochainComplexShortComplex R k M
  -- The cochains of the empty subspace vanish, so the relative cochains are all the cochains.
  have hz : IsZero ((TopPair.ofSubset S).snd.singularCochainComplex R k M) :=
    (TauCeti.ChainComplex.linearYonedaFunctor k M).map_isZero
      (SSet.isZero_chainComplex (X := (TopPair.toSSetPair.obj (TopPair.ofSubset S)).left) R).op
  have : IsIso ((TopPair.ofSubset S).singularCochainComplexShortComplex R k M).f :=
    hS'.isIso_f_iff.2 hz
  have : IsIso (relativeSingularCochainι R k M S) := by
    rw [relativeSingularCochainι_def]
    exact Functor.map_isIso (ComplexShape.embeddingUpNat.extendFunctor _) _
  exact Subobject.mk_eq_top_of_isIso _

/-- The relative cochains of `(Y, Y)` vanish. -/
@[simp]
lemma relativeSingularCochainSubobject_eq_bot {S : Set Y} (hS : S = Set.univ) :
    relativeSingularCochainSubobject R k M S = ⊥ := by
  have hiso : IsIso (TopPair.ofSubset S).map := by
    refine TopCat.isIso_of_bijective_of_isOpenMap _ ⟨Subtype.val_injective, fun y ↦ ?_⟩
      (hS ▸ isOpen_univ : IsOpen S).isOpenEmbedding_subtypeVal.isOpenMap
    exact ⟨⟨y, hS ▸ Set.mem_univ y⟩, rfl⟩
  have hc := (TopPair.ofSubset S).shortExact_singularChainComplexShortComplex R
  -- The chains of the subspace `S = Y` are all the chains, so the relative chains vanish, and
  -- with them the relative cochains.
  have : IsIso (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.ofSubset S).map) R) :=
    Functor.map_isIso ((SSet.chainComplexFunctor C).obj R) _
  have hz : IsZero ((TopPair.ofSubset S).singularChainComplex R) :=
    hc.isIso_f_iff.1 this
  have hz' : IsZero (((TopPair.ofSubset S).singularCochainComplex R k M).extend
      ComplexShape.embeddingUpNat) :=
    (ComplexShape.embeddingUpNat.extendFunctor _).map_isZero
      ((TauCeti.ChainComplex.linearYonedaFunctor k M).map_isZero hz.op)
  exact Subobject.mk_eq_bot_iff_zero.2 (hz'.eq_of_src _ _)

variable (R k M)

/-- **The graded pieces of the filtration by relative cochains.** For `S ⊆ T`, the quotient of
the relative cochains of `(Y, S)` by those of `(Y, T)` is the relative singular cochain complex of
the pair `(T, S)`, extended by zero. The isomorphism is induced by restriction from `Y` to `T`
(`TauCeti.π_relativeSingularCochainSubobjectCokernelIso_hom`). -/
def relativeSingularCochainSubobjectCokernelIso {S T : Set Y} (h : S ⊆ T) :
    cokernel (Subobject.ofLE _ _ (relativeSingularCochainSubobject_anti (R := R) (k := k) (M := M)
        h)) ≅
      ((TopPair.ofInclusion h).singularCochainComplex R k M).extend ComplexShape.embeddingUpNat :=
  have hS := ((TopTriple.ofSubset h).shortExact_singularCochainComplexShortComplex R k M).extend
    ComplexShape.embeddingUpNat
  cokernel.mapIso _
      (extendMap ((TopTriple.ofSubset h).singularCochainComplexShortComplex R k M).f
        ComplexShape.embeddingUpNat)
      (relativeSingularCochainSubobjectIso R k M T) (relativeSingularCochainSubobjectIso R k M S)
      (ofLE_comp_relativeSingularCochainSubobjectIso_hom h) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hS.gIsCokernel

/-- The identification of the graded piece with the relative cochains of `(T, S)` is induced by
the restriction of relative cochains along the map of pairs `(T, S) ⟶ (Y, S)`. -/
@[reassoc (attr := simp)]
lemma π_relativeSingularCochainSubobjectCokernelIso_hom {S T : Set Y} (h : S ⊆ T) :
    cokernel.π _ ≫ (relativeSingularCochainSubobjectCokernelIso R k M h).hom =
      (relativeSingularCochainSubobjectIso R k M S).hom ≫
        extendMap ((TopTriple.ofSubset h).singularCochainComplexShortComplex R k M).g
          ComplexShape.embeddingUpNat :=
  (cokernel.π_desc_assoc _ _ _ _).trans <| (Category.assoc _ _ _).trans <|
    congrArg (_ ≫ ·) (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one)

end Subobject

/-! ### The filtration of a space and its spectral sequence -/

variable (X : ℤ → Set Y)

/-- **The filtration of the singular cochains of a filtered space.** For a family of subsets
`X : ℤ → Set Y`, the `p`th stage is the subcomplex of relative cochains of `(Y, X (p - 1))`: the
cochains vanishing on the singular simplices of `X (p - 1)`. -/
def singularCochainFiltration (p : ℤ) :
    Subobject ((Y.singularCochainComplex R k M).extend ComplexShape.embeddingUpNat) :=
  relativeSingularCochainSubobject R k M (X (p - 1))

/-- The `p`th stage of the filtration of the singular cochains is the subcomplex of relative
cochains of `(Y, X (p - 1))`. -/
lemma singularCochainFiltration_def (p : ℤ) :
    singularCochainFiltration R k M X p =
      relativeSingularCochainSubobject R k M (X (p - 1)) := (rfl)

variable {R k M X}

/-- An increasing family of subsets gives a decreasing filtration of singular cochains. -/
lemma antitone_singularCochainFiltration (hX : Monotone X) :
    Antitone (singularCochainFiltration R k M X) :=
  fun _ _ h ↦ relativeSingularCochainSubobject_anti (hX (by lia))

/-- The stage of the filtration after an empty subset is everything. -/
lemma singularCochainFiltration_eq_top {b : ℤ} (hb : X b = ∅) :
    singularCochainFiltration R k M X (b + 1) = ⊤ :=
  relativeSingularCochainSubobject_eq_top (by rwa [add_sub_cancel_right])

/-- The stage of the filtration after the whole space is zero. -/
lemma singularCochainFiltration_eq_bot {a : ℤ} (ha : X a = Set.univ) :
    singularCochainFiltration R k M X (a + 1) = ⊥ :=
  relativeSingularCochainSubobject_eq_bot (by rwa [add_sub_cancel_right])

variable (R k M) (hX : Monotone X)

/-- **The cohomological spectral sequence of a filtered space.** For an increasing family
`X : ℤ → Set Y` of subsets of a space `Y`, this is the spectral sequence of the decreasing
filtration of the singular cochains of `Y` by the relative cochains of the pairs `(Y, X (p - 1))`,
in the classical cohomological indexing: it starts on page `1`, with differentials
`d_r : E_r^{p,q} ⟶ E_r^{p+r,q-r+1}`. -/
abbrev filteredSpaceCohomologySpectralSequence :=
  CochainComplex.decreasingFiltrationSpectralSequence (singularCochainFiltration R k M X)
    (antitone_singularCochainFiltration hX)

/-- The graded piece `F^p / F^{p+1}` of the filtration of the singular cochains is the extended
relative cochain complex of the pair `(X p, X (p - 1))`. -/
private def cokernelSingularCochainFiltrationIso (p : ℤ) :
    cokernel (Subobject.ofLE _ _ (antitone_singularCochainFiltration (R := R) (k := k) (M := M) hX
        (by lia : p ≤ p + 1))) ≅
      ((TopPair.ofInclusion (hX (by lia : p - 1 ≤ p))).singularCochainComplex R k M).extend
        ComplexShape.embeddingUpNat :=
  Subobject.cokernelOfLEIsoOfEq (by rw [singularCochainFiltration_def, add_sub_cancel_right])
      (singularCochainFiltration_def R k M X p) _
      (relativeSingularCochainSubobject_anti (hX (by lia : p - 1 ≤ p))) ≪≫
    relativeSingularCochainSubobjectCokernelIso R k M _

/-- **The first page of the cohomological spectral sequence of a filtered space.** The object at
`(p, q)` on the first page is the relative singular cohomology `Hⁿ(X p, X (p - 1))`, where
`p + q = n`. -/
def filteredSpaceCohomologySpectralSequenceFirstPageXIso (p q : ℤ) (n : ℕ) (hn : p + q = n) :
    ((filteredSpaceCohomologySpectralSequence R k M hX).page 1).X (p, q) ≅
      (TopPair.ofInclusion (hX (by lia : p - 1 ≤ p))).singularCohomology R k M n :=
  CochainComplex.decreasingFiltrationSpectralSequenceFirstPageXIso _ _ p q ≪≫
    (homologyFunctor _ _ _).mapIso (cokernelSingularCochainFiltrationIso R k M hX p) ≪≫
    extendHomologyIso _ ComplexShape.embeddingUpNat hn.symm

/-- The first page of the cohomological spectral sequence of a filtered space vanishes in
negative total degree `p + q`, since singular cochains are concentrated in nonnegative degrees. -/
lemma isZero_filteredSpaceCohomologySpectralSequence_page_one_X (p q : ℤ) (h : p + q < 0) :
    IsZero (((filteredSpaceCohomologySpectralSequence R k M hX).page 1).X (p, q)) :=
  IsZero.of_iso ((extend_exactAt _ ComplexShape.embeddingUpNat _ fun n hn ↦ by
      have : (n : ℤ) = p + q := hn
      lia).isZero_homology)
    (CochainComplex.decreasingFiltrationSpectralSequenceFirstPageXIso _ _ p q ≪≫
      (homologyFunctor _ _ _).mapIso (cokernelSingularCochainFiltrationIso R k M hX p))

/-- **The abutment of the cohomological spectral sequence of a filtered space** in degree `n` is
the singular cohomology `Hⁿ(Y)`. -/
def filteredSpaceCohomologyAbutmentIso (n : ℕ) :
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        ((antitone_singularCochainFiltration (R := R) (k := k) (M := M) hX).comp
          fun _ _ h ↦ neg_le_neg h))).abutment n ≅
      Y.singularCohomology R k M n :=
  CochainComplex.filtrationAbutmentIso _ _ _ ≪≫
    extendHomologyIso _ ComplexShape.embeddingUpNat rfl

/-- **Strong convergence of the cohomological spectral sequence of a finite filtration of a
space.** If `X b = ∅` and `X a` is all of `Y`, then on every page `r ≥ 1` with `a + 1 ≤ p + r` and
`p - r ≤ b`, the object at `(p, q)` is the graded piece `F^p H / F^{p+1} H` of the filtration of the
abutment in degree `p + q`, which is `H^{p+q}(Y)` by `TauCeti.filteredSpaceCohomologyAbutmentIso`;
its `p`th piece is the image of `H^{p+q}(Y, X (p - 1)) ⟶ H^{p+q}(Y)`. -/
def filteredSpaceCohomologySpectralSequencePageXIsoGradedOfFinite {a b : ℤ}
    (ha : X a = Set.univ) (hb : X b = ∅) (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) (hra : a + 1 ≤ p + r)
    (hrb : p - r ≤ b) :
    ((filteredSpaceCohomologySpectralSequence R k M hX).page r).X (p, q) ≅
      cokernel ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        ((antitone_singularCochainFiltration (R := R) (k := k) (M := M) hX).comp
          fun _ _ h ↦ neg_le_neg h))).abutmentFiltrationMap (-p - 1) (p + q)) :=
  CochainComplex.decreasingFiltrationSpectralSequencePageXIsoGradedOfFinite _ _
    (singularCochainFiltration_eq_bot ha) (singularCochainFiltration_eq_top hb) r hr p q hra
    (by lia)

end TauCeti
