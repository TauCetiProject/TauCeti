/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.MayerVietoris
public import TauCeti.Geometry.Manifold.SmoothSingular.Additivity
public import TauCeti.Geometry.Manifold.SmoothSingular.Contractible
public import TauCeti.Geometry.Manifold.SmoothSingular.MayerVietoris

/-!
# The smoothing theorem for smooth singular chains

Let `M` be a Hausdorff σ-compact smooth manifold over a finite-dimensional real model with corners
`I`. This file proves that the inclusion of the smooth singular chains of `M` into its singular
chains is a quasi-isomorphism, with coefficients in any object `R` of an abelian category in which
countable coproducts exist and are exact, such as a module over a ring
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι`). When `R` is moreover projective,
for instance a field or the integers, it is a chain homotopy equivalence: it has a chosen homotopy
inverse together with both chain homotopies (`TauCeti.smoothSingularChainHomotopyEquiv`). The
homotopy inverses are natural up to homotopy in smooth maps
(`TauCeti.smoothSingularChainHomotopyEquivInvNaturality`). So smooth singular homology computes
singular homology. This is what allows the integration of differential forms over smooth chains,
which only makes sense for smooth simplices, to be compared with singular cohomology.

The proof is a Mayer–Vietoris induction over the open subsets `U` of `M`
(`TauCeti.mayerVietoris_induction_extChartAt`) for the property that the inclusion is a
quasi-isomorphism on `U`:

* on the empty set both complexes vanish
  (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty`);
* a convex chart domain `U = (chartAt H x).source ∩ (extChartAt I x)⁻¹' C`, with `C` convex, is
  smoothly contractible: the chart identifies it with the convex set `C ∩ range I`, which contracts
  onto any of its points along straight lines
  (`TauCeti.exists_contMDiff_contraction_of_convex_extChartAt`), so its smooth and singular chains
  are chain homotopy equivalent
  (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contraction`);
* the property passes to binary unions by the Mayer–Vietoris sequences of smooth and singular
  chains (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup`), and to countable
  disjoint unions by additivity
  (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iSup`).

The case `U = M` is transported along the diffeomorphism of `M` with its top open subset
(`Diffeomorph.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff`). Over projective
coefficients, every chain group of a simplicial set is a coproduct of copies of `R`, hence
projective, and a quasi-isomorphism of bounded below complexes of projective objects is a chain
homotopy equivalence (`ChainComplex.quasiIso_iff_of_projective`).

The smoothness hypothesis `[IsManifold I ∞ M]` is used only by the contractions of the convex chart
domains. Boundary and corners are allowed. As for the additivity of singular chains, `M` is a type
in `Type`, since the disjoint unions of the induction are indexed by `ℕ`.

## Main results

* `Diffeomorph.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff`: the inclusion of smooth
  into singular chains is a quasi-isomorphism on `M` exactly when it is one on a manifold
  diffeomorphic to `M`.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι`: **the smoothing theorem**, the
  inclusion of smooth singular chains into singular chains is a quasi-isomorphism.
* `TauCeti.smoothSingularChainHomotopyEquiv`: for projective coefficients, the inclusion as a chain
  homotopy equivalence.
* `TauCeti.smoothSingularChainHomotopyEquivInvNaturality`: the homotopy inverses commute with
  the maps induced by a smooth map, up to homotopy.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, Theorem 18.7 and its proof.
-/

public section

noncomputable section

open CategoryTheory Limits Set TopologicalSpace Simplicial
open scoped Manifold ContDiff

universe u v w

/-! ### Invariance under diffeomorphisms -/

namespace Diffeomorph

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  {C : Type v} [Category.{w} C] [Preadditive C] [HasCoproducts.{u} C] [CategoryWithHomology C]

/-- The inclusion of smooth singular chains into singular chains is a quasi-isomorphism on `M`
exactly when it is one on a manifold diffeomorphic to `M`: a diffeomorphism induces isomorphisms
of both chain complexes, compatibly with the inclusions. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff (e : M ≃ₘ⟮I, J⟯ N) (R : C) :
    QuasiIso (SSet.chainComplexMap (TauCeti.smoothSingularSubcomplex I M).ι R) ↔
      QuasiIso (SSet.chainComplexMap (TauCeti.smoothSingularSubcomplex J N).ι R) := by
  let f : TopCat.of M ⟶ TopCat.of N := TopCat.ofHom ⟨e, e.continuous⟩
  have : IsIso f := (TopCat.isIso_iff_isHomeomorph f).2 e.toHomeomorph.isHomeomorph
  -- The maps of smooth singular subcomplexes induced by `e` and `e.symm` are inverse to each other.
  have : IsIso (TauCeti.smoothSingularSubcomplexMap e e.contMDiff) :=
    ⟨TauCeti.smoothSingularSubcomplexMap e.symm e.symm.contMDiff, by
      rw [← TauCeti.smoothSingularSubcomplexMap_comp, ← TauCeti.smoothSingularSubcomplexMap_id]
      congr 1
      exact e.symm_comp_self, by
      rw [← TauCeti.smoothSingularSubcomplexMap_comp, ← TauCeti.smoothSingularSubcomplexMap_id]
      congr 1
      exact e.self_comp_symm⟩
  have hchain : SSet.chainComplexMap (TauCeti.smoothSingularSubcomplexMap e e.contMDiff) R ≫
        SSet.chainComplexMap (TauCeti.smoothSingularSubcomplex J N).ι R =
      SSet.chainComplexMap (TauCeti.smoothSingularSubcomplex I M).ι R ≫
        SSet.chainComplexMap (TopCat.toSSet.map f) R := by
    rw [← Functor.map_comp, ← Functor.map_comp, TauCeti.smoothSingularSubcomplexMap_ι]
  rw [← quasiIso_iff_comp_right _ (SSet.chainComplexMap (TopCat.toSSet.map f) R), ← hchain,
    quasiIso_iff_comp_left]

end Diffeomorph

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}

/-! ### The smoothing theorem -/

section Smoothing

variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [FiniteDimensional ℝ E]
  {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{0} C]
  [HasExactColimitsOfShape (Discrete ℕ) C] (R : C)

variable (I M) in
/-- **The smoothing theorem.** On a Hausdorff σ-compact smooth manifold over a finite-dimensional
real model with corners, the inclusion of smooth singular chains into singular chains, with
coefficients in an object `R` of an abelian category with exact countable coproducts, is a
quasi-isomorphism. So smooth singular homology is singular homology. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  have : SecondCountableTopology H := I.isClosedEmbedding.isEmbedding.secondCountableTopology
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  -- Mayer–Vietoris induction over the open subsets of `M`.
  have hall := mayerVietoris_induction_extChartAt I
    (fun U : Opens M ↦ QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R))
    (by
      have : IsEmpty (⊥ : Opens M) := ⟨fun y ↦ y.2⟩
      exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty R)
    (fun x C U _ hCc hCt hU ⟨y₀, hy₀⟩ ↦ by
      obtain ⟨F, hF, h₀, h₁⟩ := exists_contMDiff_contraction_of_convex_extChartAt hCc hCt hU
        ⟨y₀, hy₀⟩
      exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contraction R hF _ h₀ h₁)
    (fun U V hU hV hUV ↦ quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup I R U V hU hV hUV)
    (fun s hs h ↦ quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iSup s C R
      (fun i j hij ↦ hs i j hij) h)
  -- The top open subset is diffeomorphic to `M`.
  let top : (⊤ : Opens M) ≃ₘ⟮I, I⟯ M :=
    { toFun := Subtype.val
      invFun y := ⟨y, trivial⟩
      left_inv _ := rfl
      right_inv _ := rfl
      contMDiff_toFun := contMDiff_subtype_val
      contMDiff_invFun := by
        rw [← ContMDiff.subtypeVal_comp_iff]
        exact contMDiff_id }
  exact (top.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff R).1 (hall ⊤)

omit [HasExactColimitsOfShape (Discrete ℕ) C] in
/-- Each chain group of a simplicial set with projective coefficients is projective, as a
coproduct of copies of the coefficients. -/
private theorem projective_chainComplex_X (X : SSet.{0}) [Projective R] (n : ℕ) :
    Projective ((X.chainComplex R).X n) where
  factors f e _ := ⟨Sigma.desc fun x ↦ Projective.factorThru (X.ιChainComplex x ≫ f) e, by
    ext x
    simp [SSet.ιChainComplex]⟩

variable (I M) in
/-- **The smoothing theorem, as a chain homotopy equivalence.** On a Hausdorff σ-compact smooth
manifold over a finite-dimensional real model with corners, with projective coefficients `R` (for
instance `ℝ` or `ℤ`), the inclusion of smooth singular chains into singular chains is a chain
homotopy equivalence (`TauCeti.smoothSingularChainHomotopyEquiv_hom`). Its homotopy inverse and
the two homotopies are chosen. -/
def smoothSingularChainHomotopyEquiv [Projective R] :
    HomotopyEquiv ((smoothSingularSubcomplex I M : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of M)).chainComplex R) :=
  have := projective_chainComplex_X R (smoothSingularSubcomplex I M : SSet)
  have := projective_chainComplex_X R (TopCat.toSSet.obj (TopCat.of M))
  ((ChainComplex.quasiIso_iff_of_projective _).1
    (quasiIso_chainComplexMap_smoothSingularSubcomplex_ι I M R)).choose

/-- The forward map of the smoothing equivalence is the inclusion of smooth singular chains. -/
@[simp]
theorem smoothSingularChainHomotopyEquiv_hom [Projective R] :
    (smoothSingularChainHomotopyEquiv I M R).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R :=
  have := projective_chainComplex_X R (smoothSingularSubcomplex I M : SSet)
  have := projective_chainComplex_X R (TopCat.toSSet.obj (TopCat.of M))
  ((ChainComplex.quasiIso_iff_of_projective _).1
    (quasiIso_chainComplexMap_smoothSingularSubcomplex_ι I M R)).choose_spec

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [FiniteDimensional ℝ E'] {N : Type} [TopologicalSpace N]
  [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]

/-- **Naturality of the smoothing equivalence.** For a smooth map `f : M → N`, the homotopy
inverses of the smoothing equivalences of `M` and `N` commute, up to chain homotopy, with the maps
of singular and of smooth singular chains induced by `f`. -/
def smoothSingularChainHomotopyEquivInvNaturality [Projective R] {f : M → N}
    (hf : ContMDiff I J ∞ f) :
    Homotopy ((smoothSingularChainHomotopyEquiv I M R).inv ≫
        SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) R)
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R ≫
        (smoothSingularChainHomotopyEquiv J N R).inv) := by
  set eM := smoothSingularChainHomotopyEquiv I M R
  set eN := smoothSingularChainHomotopyEquiv J N R
  set a := SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) R
  set b := SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R
  -- The inclusions of smooth chains intertwine the maps induced by `f`.
  have hcomm : a ≫ eN.hom = eM.hom ≫ b := by
    rw [smoothSingularChainHomotopyEquiv_hom, smoothSingularChainHomotopyEquiv_hom,
      ← Functor.map_comp, ← Functor.map_comp, smoothSingularSubcomplexMap_ι]
  have h : (eM.inv ≫ a) ≫ eN.hom ≫ eN.inv = (eM.inv ≫ eM.hom) ≫ b ≫ eN.inv := by
    simp only [Category.assoc]
    rw [reassoc_of% hcomm]
  -- Insert `i_N ≫ inv_N ≃ 𝟙` after the smooth map and remove `inv_M ≫ i_M ≃ 𝟙` before the singular
  -- map.
  exact (Homotopy.ofEq (Category.comp_id _).symm).trans <|
    (eN.homotopyHomInvId.compLeft _).symm.trans <| (Homotopy.ofEq h).trans <|
      (eM.homotopyInvHomId.compRight _).trans <| Homotopy.ofEq (Category.id_comp _)

end Smoothing

end TauCeti
