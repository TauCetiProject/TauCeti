/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Limits.HasExactLimitsOfShape
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.Geometry.Manifold.SmoothSingular.Basic

import TauCeti.Algebra.Homology.DerivedCategory.KProjective
import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Contraction
import TauCeti.Geometry.Manifold.SmoothSingular.Additivity
import TauCeti.Geometry.Manifold.SmoothSingular.Diffeomorph
import TauCeti.Geometry.Manifold.SmoothSingular.Homotopy
import TauCeti.Geometry.Manifold.SmoothSingular.MayerVietoris
import TauCeti.Geometry.Manifold.Topology
import TauCeti.Topology.MayerVietoris

/-!
# The smoothing theorem for smooth singular chains

Let `M` be a Hausdorff `σ`-compact smooth manifold modelled on a real model with corners
`I : ModelWithCorners ℝ E H` over a finite-dimensional normed vector space `E`. This file proves
Lee's smoothing theorem (Theorem 18.7): the inclusion of smooth singular chains into ordinary
singular chains is a quasi-isomorphism for arbitrary coefficients in an abelian category in which
countable coproducts are exact (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι`),
and a chain homotopy equivalence when the coefficient object `R` is projective
(`TauCeti.smoothSingularChainHomotopyEquiv`), covering in particular coefficients in `ℝ`, in `ℤ`,
or in any projective module over a ring.

Because `M` may have boundary or corners, relative Whitney approximation simplex-by-simplex over
the skeleta is unavailable: a continuous simplex into `[0, ∞)` whose coordinate faces are smooth
need not be homotopic relative to its boundary to a smooth simplex. Instead, the proof proceeds by
two stages of Mayer–Vietoris induction (`TauCeti.mayerVietoris_induction`):

1. **Smoothly contractible spaces.** Whenever `M` admits a smooth contraction `F : ℝ × M → M` from
   the identity to a constant map, `TauCeti.Geometry.Manifold.SmoothSingular.Homotopy` gives an
   explicit chain homotopy equivalence `TauCeti.smoothSingularChainHomotopyEquivOfContMDiff`
   between smooth and continuous singular chains in all degrees simultaneously.
2. **Extended chart domains.** For each `x : M`, the open subsets of `(extChartAt I x).source`
   whose image under `extChartAt I x` is convex in `E` form an intersection-stable basis
   (`ModelWithCorners.isBasis_convex_image_extChartAt`). Every nonempty member of this basis is
   smoothly contractible via straight-line interpolation in chart coordinates reparametrized by
   `Real.smoothTransition` (`TauCeti.exists_contMDiff_contraction_of_starConvex_image_extChartAt`).
   Mayer–Vietoris induction on `(extChartAt I x).source`, combining the binary-union step from
   `TauCeti.Geometry.Manifold.SmoothSingular.MayerVietoris` and the countable disjoint-union step
   from `TauCeti.Geometry.Manifold.SmoothSingular.Additivity`, proves the quasi-isomorphism on all
   open subsets of `(extChartAt I x).source`.
3. **Global manifold.** The open subsets of `M` contained in some `(extChartAt I x).source` form a
   second intersection-stable basis of `M`, and a second Mayer–Vietoris induction extends the
   quasi-isomorphism to all open subsets of `M` and hence to `M` itself.

When `R` is projective in `C`, every term of both chain complexes is projective
(`SSet.projective_chainComplex_X_of_projective`), so the quasi-isomorphism upgrades to a chosen
chain homotopy equivalence `TauCeti.smoothSingularChainHomotopyEquiv` whose inverse is natural up
to a chosen chain homotopy (`TauCeti.smoothSingularChainHomotopyEquivInvNaturality`). Applying
`Hom(-, Y)` yields the dual cochain homotopy equivalence
`TauCeti.smoothSingularCochainHomotopyEquiv` and the cohomology isomorphism
`TauCeti.smoothSingularCohomologyIso`.

## Main definitions and results

* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_opens` and
  `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι`: the smoothing quasi-isomorphism on
  open subsets of `M` and on `M`.
* `TauCeti.smoothSingularHomologyIso`: the induced natural isomorphism between smooth singular
  homology and singular homology.
* `TauCeti.smoothSingularChainHomotopyEquiv`,
  `TauCeti.homologyMap_smoothSingularChainHomotopyEquiv_inv`, and
  `TauCeti.smoothSingularChainHomotopyEquivInvNaturality`: the smoothing chain homotopy equivalence
  for projective coefficients, compatibility of its inverse with `smoothSingularHomologyIso`, and
  the chain homotopy witnessing naturality of its inverse.
* `TauCeti.smoothSingularCochainHomotopyEquiv`,
  `TauCeti.quasiIso_cochainComplexMap_smoothSingularSubcomplex_ι`,
  `TauCeti.smoothSingularCohomologyIso`, and
  `TauCeti.homologyMap_smoothSingularCochainHomotopyEquiv_inv`: the induced cochain homotopy
  equivalence, cochain quasi-isomorphism, cohomology isomorphism, and compatibility of the cochain
  inverse with `smoothSingularCohomologyIso`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, Theorem 18.7.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace Topology
open scoped Manifold ContDiff

universe u v w

namespace TauCeti

/-! ### Mayer–Vietoris induction on extended charts and on manifolds -/

section QuasiIso

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
  {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C]
  [HasExactColimitsOfShape (Discrete ℕ) C]

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] in
private lemma quasiIso_iSup_nat {X : Type u} [TopologicalSpace X] [ChartedSpace H X]
    (R : C) (s : ℕ → Opens X) (hs : ∀ i j, i ≠ j → Disjoint (s i) (s j))
    (h : ∀ n, QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I (s n)).ι R)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(⨆ n, s n)).ι R) := by
  have : HasCoproducts.{0} C := hasCoproducts_shrink
  have : HasExactColimitsOfShape (Discrete (ULift.{u} ℕ)) C :=
    HasExactColimitsOfShape.of_domain_equivalence C
      (Discrete.equivalence (Equiv.ulift.symm : ℕ ≃ ULift.{u} ℕ))
  let s' : ULift.{u} ℕ → Opens X := fun i ↦ s i.down
  have heq : (⨆ n, s n) = ⨆ i, s' i :=
    le_antisymm (iSup_le fun n ↦ le_iSup s' (ULift.up n)) (iSup_le fun i ↦ le_iSup s i.down)
  rw [heq]
  exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iSup s' C R
    (fun i j hij ↦ hs i.down j.down fun hd ↦ hij (ULift.ext hd))
    (fun i ↦ h i.down)

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [HasExactColimitsOfShape (Discrete ℕ) C] in
private lemma quasiIso_iff_of_opens_subset {S U : Opens M} (hU : (U : Set M) ⊆ (S : Set M))
    {V : Opens S} (hUV : ∀ y : S, y ∈ V ↔ y.val ∈ U) (R : C) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R) ↔
      QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R) := by
  let f : U → V := fun z ↦ ⟨⟨z.val, hU z.property⟩, (hUV _).2 z.property⟩
  let g : V → U := fun z ↦ ⟨z.val.val, (hUV z.val).1 z.property⟩
  have hf : ContMDiff I I ∞ f := by
    rw [← ContMDiff.subtypeVal_comp_iff, ← ContMDiff.subtypeVal_comp_iff]
    exact contMDiff_subtypeVal (I := I) (U := U)
  have hg : ContMDiff I I ∞ g := by
    rw [← ContMDiff.subtypeVal_comp_iff]
    exact (contMDiff_subtypeVal (I := I) (U := S)).comp
      (contMDiff_subtypeVal (I := I) (U := V))
  exact ⟨quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff_inv R hf hg
      (fun _ ↦ rfl) (fun _ ↦ rfl),
    quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff_inv R hg hf
      (fun _ ↦ rfl) (fun _ ↦ rfl)⟩

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [HasExactColimitsOfShape (Discrete ℕ) C] in
private lemma quasiIso_of_convex_image_extChartAt (R : C) (x : M)
    {V : Opens (I.extChartAtOpens x)}
    (hV : Convex ℝ ((fun y : I.extChartAtOpens x ↦ extChartAt I x y.val) '' (V : Set _))) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R) := by
  rcases (V : Set (I.extChartAtOpens x)).eq_empty_or_nonempty with hempty | ⟨c₀, hc₀⟩
  · have : IsEmpty V :=
      ⟨fun z ↦ by
          have hz : z.val ∈ (V : Set (I.extChartAtOpens x)) := z.property; rwa [hempty] at hz⟩
    infer_instance
  · let W : Opens M :=
      ⟨Subtype.val '' (V : Set (I.extChartAtOpens x)),
        (I.extChartAtOpens x).isOpen.isOpenMap_subtypeVal _ V.isOpen⟩
    have hW_sub : (W : Set M) ⊆ (extChartAt I x).source := by
      rintro _ ⟨y, -, rfl⟩
      exact y.property
    have hWV : ∀ y : I.extChartAtOpens x, y ∈ V ↔ y.val ∈ W := fun y ↦
      ⟨fun hy ↦ ⟨y, hy, rfl⟩, fun ⟨z, hz, hzy⟩ ↦ Subtype.ext hzy ▸ hz⟩
    have hW_im : extChartAt I x '' (W : Set M) =
        (fun y : I.extChartAtOpens x ↦ extChartAt I x y.val) '' (V : Set _) := by
      rw [Opens.coe_mk, Set.image_image]
    let cW : W := ⟨c₀.val, c₀, hc₀, rfl⟩
    obtain ⟨F, hF, h₀, h₁⟩ := exists_contMDiff_contraction_of_starConvex_image_extChartAt
      (n := ⊤) hW_sub cW ((hW_im.symm ▸ hV).starConvex (Set.mem_image_of_mem _ cW.property))
    exact (quasiIso_iff_of_opens_subset hW_sub hWV R).2
      (quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff R hF cW h₀ h₁)

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] in
private lemma quasiIso_of_subset_extChartAt_source [LocallyCompactSpace M]
    [SecondCountableTopology M] (R : C) (x : M) {U : Opens M}
    (hU : (U : Set M) ⊆ (extChartAt I x).source) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R) := by
  have : LocallyCompactSpace (I.extChartAtOpens x) :=
    (I.extChartAtOpens x).isOpen.locallyCompactSpace
  have hφ_inj : Function.Injective (fun y : I.extChartAtOpens x ↦ extChartAt I x y.val) :=
    fun y₁ y₂ h ↦ Subtype.ext ((extChartAt I x).injOn y₁.property y₂.property h)
  have hW : ∀ V : Opens (I.extChartAtOpens x),
      QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R) :=
    mayerVietoris_induction
      (fun V ↦ QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R))
      {V | Convex ℝ ((fun y : I.extChartAtOpens x ↦ extChartAt I x y.val) '' (V : Set _))}
      (I.isBasis_convex_image_extChartAt x)
      (fun V₁ h₁ V₂ h₂ _ ↦ by
        rw [Set.mem_ofPred_eq, Opens.coe_inf, Set.image_inter hφ_inj]
        exact h₁.inter h₂)
      (by
        have : IsEmpty ↥(⊥ : Opens (I.extChartAtOpens x)) := Subtype.isEmpty_false
        infer_instance)
      (fun V hV _ ↦ quasiIso_of_convex_image_extChartAt R x hV)
      (fun V₁ V₂ ↦ quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup I R V₁ V₂)
      (fun s hs h ↦ quasiIso_iSup_nat R s hs h)
  let U' : Opens (I.extChartAtOpens x) :=
    Opens.comap (ContinuousMap.subtypeVal ((I.extChartAtOpens x : Opens M) : Set M)) U
  have hUU' (y : I.extChartAtOpens x) : y ∈ U' ↔ y.val ∈ U := by
    rw [Opens.mem_comap, ContinuousMap.subtypeVal_apply]
  exact (quasiIso_iff_of_opens_subset hU hUU' R).1 (hW U')

/-- **The smoothing theorem on open subsets.** For any open subset `U` of a Hausdorff `σ`-compact
smooth manifold `M` modelled on a finite-dimensional real model with corners `I`, the inclusion of
smooth singular chains into singular chains with coefficients in `R` is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_opens (R : C) (U : Opens M) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R) := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : SecondCountableTopology H := I.secondCountableTopology
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  exact mayerVietoris_induction
    (fun V ↦ QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R))
    {V : Opens M | ∃ x : M, (V : Set M) ⊆ (extChartAt I x).source}
    (Opens.isBasis_iff_nbhd.2 fun {W x} hx ↦
      ⟨W ⊓ I.extChartAtOpens x, ⟨x, Set.inter_subset_right⟩,
        ⟨hx, mem_extChartAt_source x⟩, inf_le_left⟩)
    (by
      rintro V₁ ⟨x, hx⟩ V₂ - -
      exact ⟨x, Set.inter_subset_left.trans hx⟩)
    (by
      have : IsEmpty ↥(⊥ : Opens M) := Subtype.isEmpty_false
      infer_instance)
    (by
      rintro V ⟨x, hx⟩ -
      exact quasiIso_of_subset_extChartAt_source R x hx)
    (fun V₁ V₂ ↦ quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup I R V₁ V₂)
    (fun s hs h ↦ quasiIso_iSup_nat R s hs h)
    U

/-- **The smoothing theorem (quasi-isomorphism form, Lee Theorem 18.7).** On a Hausdorff
`σ`-compact smooth manifold `M` modelled on a finite-dimensional real model with corners `I`, the
inclusion of smooth singular chains into singular chains with coefficients in `R` is a
quasi-isomorphism whenever countable coproducts are exact in `C`. -/
instance quasiIso_chainComplexMap_smoothSingularSubcomplex_ι (R : C) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  let f : M → ↥(⊤ : Opens M) := fun x ↦ ⟨x, trivial⟩
  have hf : ContMDiff I I ∞ f := by
    rw [← ContMDiff.subtypeVal_comp_iff]
    exact contMDiff_id (I := I)
  exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff_inv R
    hf (contMDiff_subtypeVal (I := I) (U := ⊤))
    (fun _ ↦ rfl) (fun _ ↦ rfl)
    (quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_opens R ⊤)

end QuasiIso

/-! ### Smooth singular homology isomorphism, chain homotopy equivalence, and cohomology -/

section HomotopyEquiv

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
  (N : Type u) [TopologicalSpace N] [ChartedSpace H' N]
  [T2Space N] [SigmaCompactSpace N] [IsManifold J ∞ N]
  {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C]
  [HasExactColimitsOfShape (Discrete ℕ) C] (R : C)

/-- **The smoothing isomorphism on homology.** The inclusion of smooth singular chains into singular
chains induces an isomorphism `Hₙ^∞(M; R) ≅ Hₙ(M; R)` in every degree `n`. -/
def smoothSingularHomologyIso (n : ℕ) :
    (smoothSingularSubcomplex I M : SSet).homology R n ≅
      (TopCat.toSSet.obj (TopCat.of M)).homology R n :=
  asIso (SSet.homologyMap (smoothSingularSubcomplex I M).ι R n)

/-- The forward map of `smoothSingularHomologyIso` is the map on homology induced by the inclusion
of smooth singular simplices. -/
@[simp]
theorem smoothSingularHomologyIso_hom (n : ℕ) :
    (smoothSingularHomologyIso I M R n).hom =
      SSet.homologyMap (smoothSingularSubcomplex I M).ι R n := by
  rw [smoothSingularHomologyIso, asIso_hom]

variable {I M J N} in
/-- `smoothSingularHomologyIso` is natural with respect to smooth maps. -/
@[reassoc]
theorem smoothSingularHomologyIso_hom_naturality {f : M → N}
    (hf : ContMDiff I J ∞ f) (n : ℕ) :
    (smoothSingularHomologyIso I M R n).hom ≫
        SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R n =
      SSet.homologyMap (smoothSingularSubcomplexMap f hf) R n ≫
        (smoothSingularHomologyIso J N R n).hom := by
  rw [smoothSingularHomologyIso_hom, smoothSingularHomologyIso_hom,
    ← SSet.homologyMap_comp, ← SSet.homologyMap_comp, smoothSingularSubcomplexMap_ι]

variable {I M J N} in
/-- The inverse of `smoothSingularHomologyIso` is natural with respect to smooth maps. -/
@[reassoc]
theorem smoothSingularHomologyIso_inv_naturality {f : M → N}
    (hf : ContMDiff I J ∞ f) (n : ℕ) :
    (smoothSingularHomologyIso I M R n).inv ≫
        SSet.homologyMap (smoothSingularSubcomplexMap f hf) R n =
      SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R n ≫
        (smoothSingularHomologyIso J N R n).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv,
    smoothSingularHomologyIso_hom_naturality R hf]

section Projective

variable [Projective R]

/-- **The smoothing theorem (chain homotopy equivalence form, Lee Theorem 18.7).** When `R` is a
projective object of `C` (for instance `R = ModuleCat.of ℝ ℝ` or `R = ModuleCat.of ℤ ℤ`), every
degree of both the smooth and ordinary singular chain complexes is projective, so the inclusion of
smooth singular chains into singular chains is a chain homotopy equivalence. -/
def smoothSingularChainHomotopyEquiv :
    HomotopyEquiv ((smoothSingularSubcomplex I M : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of M)).chainComplex R) :=
  .ofQuasiIsoOfProjective (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R)

/-- The forward map of `smoothSingularChainHomotopyEquiv` is the chain map induced by the inclusion
of smooth singular simplices. -/
@[simp]
theorem smoothSingularChainHomotopyEquiv_hom :
    (smoothSingularChainHomotopyEquiv I M R).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R := by
  rw [smoothSingularChainHomotopyEquiv, HomotopyEquiv.ofQuasiIsoOfProjective_hom]

/-- The map induced on homology by the inverse of `smoothSingularChainHomotopyEquiv` is the inverse
of `smoothSingularHomologyIso`. -/
@[simp]
theorem homologyMap_smoothSingularChainHomotopyEquiv_inv (n : ℕ) :
    HomologicalComplex.homologyMap (smoothSingularChainHomotopyEquiv I M R).inv n =
      (smoothSingularHomologyIso I M R n).inv := by
  rw [smoothSingularChainHomotopyEquiv, HomotopyEquiv.homologyMap_ofQuasiIsoOfProjective_inv,
    smoothSingularHomologyIso]

variable {I M J N} in
/-- The forward map of `smoothSingularChainHomotopyEquiv` commutes strictly with the chain maps
induced by a smooth map `f : M → N`. -/
@[reassoc]
theorem smoothSingularChainHomotopyEquiv_hom_naturality {f : M → N}
    (hf : ContMDiff I J ∞ f) :
    (smoothSingularChainHomotopyEquiv I M R).hom ≫
        SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R =
      SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) R ≫
        (smoothSingularChainHomotopyEquiv J N R).hom := by
  rw [smoothSingularChainHomotopyEquiv_hom, smoothSingularChainHomotopyEquiv_hom,
    ← Functor.map_comp, ← Functor.map_comp, smoothSingularSubcomplexMap_ι]

variable {I M J N} in
/-- **Naturality up to chain homotopy of the smoothing inverse.** For any smooth map `f : M → N`,
composing the smoothing homotopy inverse on `M` with the smooth pushforward along `f` is chain
homotopic to pushing forward singular chains along `f` and then applying the smoothing homotopy
inverse on `N`. -/
def smoothSingularChainHomotopyEquivInvNaturality {f : M → N}
    (hf : ContMDiff I J ∞ f) :
    Homotopy
      ((smoothSingularChainHomotopyEquiv I M R).inv ≫
        SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) R)
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R ≫
        (smoothSingularChainHomotopyEquiv J N R).inv) :=
  let eM := smoothSingularChainHomotopyEquiv I M R
  let eN := smoothSingularChainHomotopyEquiv J N R
  let fS := SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) R
  let fT := SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom ⟨f, hf.continuous⟩)) R
  (Homotopy.ofEq (Category.comp_id (eM.inv ≫ fS)).symm).trans <|
    (eN.homotopyHomInvId.symm.compLeft (eM.inv ≫ fS)).trans <|
      (Homotopy.ofEq (by
        dsimp only [eM, eN, fS, fT]
        rw [Category.assoc, ← Category.assoc _ (smoothSingularChainHomotopyEquiv J N R).hom,
          ← smoothSingularChainHomotopyEquiv_hom_naturality R hf,
          Category.assoc, ← Category.assoc (smoothSingularChainHomotopyEquiv I M R).inv])).trans <|
        (eM.homotopyInvHomId.compRight (fT ≫ eN.inv)).trans <|
          Homotopy.ofEq (Category.id_comp (fT ≫ eN.inv))

/-! ### Cochain homotopy equivalence and singular cohomology comparison -/

variable (k : Type*) [Ring k] [Linear k C] (Y : C)

/-- **The dual smoothing cochain homotopy equivalence.** Applying `Hom(-, Y)` to
`smoothSingularChainHomotopyEquiv` yields a cochain homotopy equivalence from the singular cochain
complex of `M` to the smooth singular cochain complex `Hom(C_*^∞(M; R), Y)`. -/
def smoothSingularCochainHomotopyEquiv :
    HomotopyEquiv ((TopCat.of M).singularCochainComplex R k Y)
      (((smoothSingularSubcomplex I M : SSet).chainComplex R).linearYonedaObj k Y) :=
  (smoothSingularChainHomotopyEquiv I M R).linearYonedaFunctorMap k Y

/-- The forward map of `smoothSingularCochainHomotopyEquiv` is restriction of singular cochains to
smooth singular chains. -/
@[simp]
theorem smoothSingularCochainHomotopyEquiv_hom :
    (smoothSingularCochainHomotopyEquiv I M R k Y).hom =
      SSet.cochainComplexMap (smoothSingularSubcomplex I M).ι := by
  rw [smoothSingularCochainHomotopyEquiv, HomotopyEquiv.linearYonedaFunctorMap_hom,
    smoothSingularChainHomotopyEquiv_hom]

/-- The inverse map of `smoothSingularCochainHomotopyEquiv` is precomposition with the inverse of
`smoothSingularChainHomotopyEquiv`. -/
theorem smoothSingularCochainHomotopyEquiv_inv :
    (smoothSingularCochainHomotopyEquiv I M R k Y).inv =
      (ChainComplex.linearYonedaFunctor k Y).map
        (smoothSingularChainHomotopyEquiv I M R).inv.op := by
  rw [smoothSingularCochainHomotopyEquiv, HomotopyEquiv.linearYonedaFunctorMap_inv]

/-- Restriction from singular cochains to smooth singular cochains is a quasi-isomorphism when the
chain coefficient object `R` is projective. -/
instance quasiIso_cochainComplexMap_smoothSingularSubcomplex_ι :
    QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := Y)
      (smoothSingularSubcomplex I M).ι) := by
  rw [← smoothSingularCochainHomotopyEquiv_hom I M R k Y]
  exact (smoothSingularCochainHomotopyEquiv I M R k Y).quasiIso_hom

variable {I M J N} in
/-- **Naturality up to cochain homotopy of the dual smoothing inverse.** For any smooth map
`f : M → N`, pulling back smooth cochains along `f` and extending to singular cochains on `M` is
cochain homotopic to extending on `N` first and then pulling back singular cochains along `f`. -/
def smoothSingularCochainHomotopyEquivInvNaturality {f : M → N}
    (hf : ContMDiff I J ∞ f) :
    Homotopy
      (SSet.cochainComplexMap (smoothSingularSubcomplexMap f hf) ≫
        (smoothSingularCochainHomotopyEquiv I M R k Y).inv)
      ((smoothSingularCochainHomotopyEquiv J N R k Y).inv ≫
        TopCat.singularCochainComplexMap (TopCat.ofHom ⟨f, hf.continuous⟩)) :=
  (Homotopy.ofEq (by
    rw [smoothSingularCochainHomotopyEquiv_inv, op_comp, Functor.map_comp,
      SSet.cochainComplexMap]
    -- The sides differ only in how the implicit cochain complexes are written: as objects of
    -- `ChainComplex.linearYonedaFunctor k Y`, or as `linearYonedaObj` (for instance
    -- `(TopCat.of M).singularCochainComplex R k Y`); these agree by definition.
    rfl)).trans <|
    ((smoothSingularChainHomotopyEquivInvNaturality R hf).linearYonedaFunctorMap k Y).trans <|
      Homotopy.ofEq (by
        rw [smoothSingularCochainHomotopyEquiv_inv, op_comp, Functor.map_comp,
          TopCat.singularCochainComplexMap, SSet.cochainComplexMap]
        -- As above, the sides differ only in how the implicit cochain complexes are written.
        rfl)

/-- **The smoothing isomorphism on cohomology.** Restriction to smooth singular chains induces an
isomorphism in every degree `n` between the singular cohomology of `M` and the cohomology of the
smooth singular cochain complex `Hom(C_*^∞(M; R), Y)`. -/
def smoothSingularCohomologyIso (n : ℕ) :
    (TopCat.of M).singularCohomology R k Y n ≅
      (((smoothSingularSubcomplex I M : SSet).chainComplex R).linearYonedaObj k Y).homology n :=
  asIso (HomologicalComplex.homologyMap
    (SSet.cochainComplexMap (R := R) (k := k) (M := Y) (smoothSingularSubcomplex I M).ι) n)

/-- The forward map of `smoothSingularCohomologyIso` is the map on cohomology induced by restriction
to smooth singular chains. -/
@[simp]
theorem smoothSingularCohomologyIso_hom (n : ℕ) :
    (smoothSingularCohomologyIso I M R k Y n).hom =
      HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (smoothSingularSubcomplex I M).ι) n := by
  rw [smoothSingularCohomologyIso, asIso_hom]

/-- Restricting the image of a smooth singular cohomology class under the inverse of
`smoothSingularCohomologyIso` back to smooth singular chains recovers the class. -/
@[simp]
theorem homologyMap_cochainComplexMap_smoothSingularCohomologyIso_inv_apply (n : ℕ)
    (x : (((smoothSingularSubcomplex I M : SSet).chainComplex R).linearYonedaObj k Y).homology n) :
    HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (R := R) (k := k) (M := Y) (smoothSingularSubcomplex I M).ι) n
        ((smoothSingularCohomologyIso I M R k Y n).inv x) = x := by
  rw [← smoothSingularCohomologyIso_hom, Iso.inv_hom_id_apply]

/-- The map induced on cohomology by the inverse of `smoothSingularCochainHomotopyEquiv` is the
inverse of `smoothSingularCohomologyIso`. -/
@[simp]
theorem homologyMap_smoothSingularCochainHomotopyEquiv_inv (n : ℕ) :
    HomologicalComplex.homologyMap (smoothSingularCochainHomotopyEquiv I M R k Y).inv n =
      (smoothSingularCohomologyIso I M R k Y n).inv := by
  rw [← cancel_mono (smoothSingularCohomologyIso I M R k Y n).hom, Iso.inv_hom_id,
    smoothSingularCohomologyIso_hom, ← smoothSingularCochainHomotopyEquiv_hom,
    ← HomologicalComplex.homologyMap_comp,
    (smoothSingularCochainHomotopyEquiv I M R k Y).homotopyInvHomId.homologyMap_eq,
    HomologicalComplex.homologyMap_id]

variable {I M J N} in
/-- `smoothSingularCohomologyIso` is contravariantly natural with respect to smooth maps. -/
@[reassoc]
theorem smoothSingularCohomologyIso_hom_naturality {f : M → N}
    (hf : ContMDiff I J ∞ f) (n : ℕ) :
    TopCat.singularCohomologyMap (TopCat.ofHom ⟨f, hf.continuous⟩) n ≫
        (smoothSingularCohomologyIso I M R k Y n).hom =
      (smoothSingularCohomologyIso J N R k Y n).hom ≫
        HomologicalComplex.homologyMap (SSet.cochainComplexMap (smoothSingularSubcomplexMap f hf))
          n := by
  rw [smoothSingularCohomologyIso_hom, smoothSingularCohomologyIso_hom,
    TopCat.singularCohomologyMap, TopCat.singularCochainComplexMap,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    ← SSet.cochainComplexMap_comp, ← SSet.cochainComplexMap_comp, smoothSingularSubcomplexMap_ι]

variable {I M J N} in
/-- The inverse of `smoothSingularCohomologyIso` (from smooth singular cohomology to singular
cohomology) is contravariantly natural with respect to smooth maps. -/
@[reassoc]
theorem smoothSingularCohomologyIso_inv_naturality {f : M → N}
    (hf : ContMDiff I J ∞ f) (n : ℕ) :
    HomologicalComplex.homologyMap (SSet.cochainComplexMap (smoothSingularSubcomplexMap f hf)) n ≫
        (smoothSingularCohomologyIso I M R k Y n).inv =
      (smoothSingularCohomologyIso J N R k Y n).inv ≫
        TopCat.singularCohomologyMap (TopCat.ofHom ⟨f, hf.continuous⟩) n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
    smoothSingularCohomologyIso_hom_naturality R k Y hf]

end Projective

end HomotopyEquiv

end TauCeti
