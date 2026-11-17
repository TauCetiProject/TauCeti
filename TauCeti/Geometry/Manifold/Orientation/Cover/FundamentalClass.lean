/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Degree
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LocalIndex
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.AlgebraicTopology.Singular.Transfer.Sign
public import TauCeti.Geometry.Manifold.Orientation.Cover.Smooth
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
import TauCeti.AlgebraicTopology.Singular.LocalHomology.TopHomology
import TauCeti.Geometry.Manifold.Degree.Homological

/-!
# The fundamental class of a closed manifold with orientation-twisted coefficients

Let `M` be a compact boundaryless smooth manifold of dimension `n + 1`, orientable or not, and let
`π : M' → M` be its orientation double cover, with the deck involution `τ` exchanging the two
orientations over each point. The cover carries a canonical orientation
(`TauCeti.Manifold.OrientationCover.canonicalOrientation`), hence a homological orientation
(`TauCeti.Manifold.OrientationCover.homologicalOrientation`) and a fundamental class
`[M'] ∈ Hₙ₊₁(M'; ℤ)`. The deck involution reverses the canonical orientation, so
`τ_*[M'] = -[M']` (`TauCeti.Manifold.OrientationCover.mapFundamentalClass_deck`).

The orientation local system `o(TM)` of `M` is the sign local system of the cover with respect to
its deck involution: its fibre over `x` is the group of integer functions `f` on the two
orientations of `TₓM` with `f (-ω) = -f ω`
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`,
`TauCeti.VectorBundleOrientationCover.signLocalSystem_def`). Here it is read on the projection of
the cover as a morphism of topological spaces (`TauCeti.Manifold.OrientationCover.projHom`).

Through the identification of the singular homology of `M'` with the homology of `M` twisted by
the permutation local system `ℤ[π⁻¹ x]` of `π`, reading a function on a fibre as the formal sum of
its sheets gives a map `Hₖ(M; o(TM)) → Hₖ(M'; ℤ)`. It is part of the coefficient long exact
sequence of `0 ⟶ o(TM) ⟶ ℤ[π⁻¹ x] ⟶ ℤ ⟶ 0`, whose last map induces `π_*`. Since `π ∘ τ = π`,
the class `π_*[M']` is its own negative, so it vanishes in the torsion-free top homology
`Hₙ₊₁(M; ℤ)`. Hence `[M']` comes from `Hₙ₊₁(M; o(TM))`, from a unique class since
`Hₙ₊₂(M; ℤ) = 0`. This is the **orientation-twisted fundamental class** of `M`
(`TauCeti.Manifold.OrientationCover.twistedFundamentalClass`,
`TauCeti.Manifold.OrientationCover.singularHomologyPermutationIso_inv_twistedFundamentalClass`,
`TauCeti.Manifold.OrientationCover.eq_twistedFundamentalClass`):

`[M]_or ∈ Hₙ₊₁(M; o(TM))`.

It exists whether or not `M` is orientable. Near a point `x` with an orientation `ω` of `TₓM`,
the class `[M']` is a local generator times the formal sum `ω - (-ω)` of the two sheets over `x`,
which is the function on the fibre taking the values `1` at `ω` and `-1` at `-ω`, a generator of
`o(TₓM)`. Antisymmetrization
`f ↦ (ω ↦ f ω - f (-ω))` from `Hₖ(M'; ℤ)` to `Hₖ(M; o(TM))` doubles this generator, and carries
`[M']` to `2 • [M]_or`
(`TauCeti.Manifold.OrientationCover.permutationLocalSystemToSign_coverFundamentalClass`).
The class `[M]_or` has infinite order as soon as `M` is nonempty
(`TauCeti.Manifold.OrientationCover.zsmul_twistedFundamentalClass_ne_zero`).

The fundamental classes of the homological theory have coefficients in `ULift ℤ`, while the
twisted homology of the base has coefficients in the ring `ℤ` itself; the two coefficient modules
are identified by `ULift.moduleEquiv` (`TauCeti.uliftIntHomologyIso`).

## Main definitions

* `TauCeti.Manifold.OrientationCover.homologicalOrientation`: the homological orientation of the
  orientation cover given by its canonical orientation.
* `TauCeti.Manifold.OrientationCover.twistedFundamentalClass`: `[M]_or ∈ Hₙ₊₁(M; o(TM))`.

## Main results

* `TauCeti.Manifold.OrientationCover.mapFundamentalClass_deck`: `τ_*[M'] = -[M']`.
* `TauCeti.Manifold.OrientationCover.singularHomologyPermutationIso_inv_twistedFundamentalClass`:
  returning to the cover carries `[M]_or` to `[M']`.
* `TauCeti.Manifold.OrientationCover.eq_twistedFundamentalClass`: `[M]_or` is the only class
  returning to `[M']`.
* `TauCeti.Manifold.OrientationCover.permutationLocalSystemToSign_coverFundamentalClass`:
  antisymmetrization carries `[M']` to `2 • [M]_or`.
* `TauCeti.Manifold.OrientationCover.zsmul_twistedFundamentalClass_ne_zero`: `[M]_or` has infinite
  order when `M` is nonempty.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.H, the orientation
  local system and the fundamental class of a nonorientable manifold with twisted coefficients.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §12 (twisted coefficients and the orientation double cover).
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Module TauCeti.LocalCoefficientSystem
open scoped Manifold

namespace TauCeti.Manifold.OrientationCover

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] {n : ℕ}
  (hE : finrank ℝ E = n + 1)

/-! ### The fundamental class of the orientation cover -/

variable (M) in
/-- The projection of the orientation double cover, as a morphism of topological spaces. -/
abbrev projHom : TopCat.of (OrientationCover 𝓘(ℝ, E) M) ⟶ TopCat.of M :=
  TopCat.ofHom ⟨VectorBundleOrientationCover.proj, (isCoveringMap_proj 𝓘(ℝ, E) M).continuous⟩

omit [FiniteDimensional ℝ E] [T2Space M] in
variable (E M) in
/-- The projection of the orientation double cover, as a morphism of topological spaces, is a
covering map. -/
theorem isCoveringMap_projHom : IsCoveringMap (projHom (E := E) M) :=
  isCoveringMap_proj 𝓘(ℝ, E) M

omit [T2Space M] in
variable (M) in
/-- The fibres of the orientation double cover are finite: each has two points. -/
theorem finite_preimage_projHom (b : M) : Finite (projHom (E := E) M ⁻¹' {b}) :=
  Set.finite_coe_iff.2 (Set.finite_of_ncard_ne_zero (by
    simp only [projHom, TopCat.hom_ofHom, ContinuousMap.coe_mk]
    rw [VectorBundleOrientationCover.ncard_fiber (Fintype.card_fin _)]
    exact two_ne_zero))

/-- The homological orientation of the orientation cover given by its canonical orientation. -/
def homologicalOrientation :
    HomologicalOrientation (OrientationCover 𝓘(ℝ, E) M) E (n + 1) :=
  (canonicalOrientation.reindex (finCongr hE)).toHomologicalOrientation hE

/-- The homological orientation of the orientation cover is the one of its canonical
orientation. -/
theorem homologicalOrientation_def :
    homologicalOrientation (M := M) hE =
      (canonicalOrientation.reindex (finCongr hE)).toHomologicalOrientation hE :=
  (rfl)

/-- The deck involution of the orientation cover has local index `-1` at every point for the
canonical homological orientation. -/
theorem localIndex_deck (p : OrientationCover 𝓘(ℝ, E) M) :
    (homologicalOrientation hE).localIndex (homologicalOrientation hE)
      ((VectorBundleOrientationCover.deck :
        OrientationCover 𝓘(ℝ, E) M ≃ₜ OrientationCover 𝓘(ℝ, E) M) :
          C(OrientationCover 𝓘(ℝ, E) M, OrientationCover 𝓘(ℝ, E) M)) p = -1 := by
  have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
      (VectorBundleOrientationCover.deck : OrientationCover 𝓘(ℝ, E) M → _) p).IsInvertible :=
    (isOrientationReversingAt_deck p).isInvertible_mfderiv
  exact (TauCeti.Manifold.Orientation.localIndex_toHomologicalOrientation hE hE _ _ _ hinv).trans
    (TauCeti.Manifold.Orientation.orientationSign_of_isOrientationReversingAt
      ((isOrientationReversingAt_deck p).reindex (finCongr hE)))

variable [CompactSpace M]

/-- **The deck involution reverses the fundamental class of the orientation cover**:
`τ_*[M'] = -[M']`. -/
theorem mapFundamentalClass_deck :
    (homologicalOrientation hE).mapFundamentalClass hE
        ((VectorBundleOrientationCover.deck :
        OrientationCover 𝓘(ℝ, E) M ≃ₜ OrientationCover 𝓘(ℝ, E) M) :
          C(OrientationCover 𝓘(ℝ, E) M, OrientationCover 𝓘(ℝ, E) M)) =
      -(homologicalOrientation hE).fundamentalClass hE := by
  set o := homologicalOrientation (M := M) hE
  set τ : C(OrientationCover 𝓘(ℝ, E) M, OrientationCover 𝓘(ℝ, E) M) :=
    ((VectorBundleOrientationCover.deck :
      OrientationCover 𝓘(ℝ, E) M ≃ₜ OrientationCover 𝓘(ℝ, E) M) :
        C(OrientationCover 𝓘(ℝ, E) M, OrientationCover 𝓘(ℝ, E) M))
  rw [← HomologicalOrientation.fundamentalClass_neg]
  refine (-o).eq_fundamentalClass hE fun y ↦ ?_
  -- The fibre of `τ` over `y` is the single point `τ y`, where the local index is `-1`.
  have hfib : τ ⁻¹' {y} = {τ y} := by
    ext q
    simp only [Set.mem_preimage, Set.mem_singleton_iff, τ, ContinuousMap.coe_ofClass]
    exact ⟨fun h ↦ h ▸ (VectorBundleOrientationCover.deck_deck q).symm,
      fun h ↦ h ▸ VectorBundleOrientationCover.deck_deck y⟩
  have hdeg : o.localDegree o hE τ y = -1 := by
    rw [HomologicalOrientation.localDegree_eq_localIndex o o hE hE τ hfib, localIndex_deck]
  refine (singularHomologyToLocalHomology_apply _ y (o.mapFundamentalClass hE τ)).trans ?_
  rw [o.singularHomologyπ_mapFundamentalClass]
  refine (o.localHomologyRestriction_localHomologyMap_fundamentalClassOn o hE τ (K := Set.univ)
    (by simpa using isCompact_univ) (Set.mem_univ y)).trans ?_
  rw [hdeg, neg_one_zsmul, HomologicalOrientation.neg_apply, LocalOrientation.coe_neg]

/-! ### The twisted fundamental class -/

variable (M) in
/-- The fundamental class of the orientation cover, with coefficients in `ℤ`. -/
def coverFundamentalClass :
    ((TopCat.toSSet.obj (TopCat.of (OrientationCover 𝓘(ℝ, E) M))).homology
      (ModuleCat.of ℤ ℤ) (n + 1) : ModuleCat.{0} ℤ) :=
  (uliftIntHomologyIso _ (n + 1)).hom.hom ((homologicalOrientation hE).fundamentalClass hE)

/-- The fundamental class of the orientation cover with coefficients in `ℤ` is the image of its
fundamental class with coefficients in `ULift ℤ`. -/
theorem coverFundamentalClass_def :
    coverFundamentalClass M hE =
      (uliftIntHomologyIso _ (n + 1)).hom.hom ((homologicalOrientation hE).fundamentalClass hE) :=
  (rfl)

omit [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M] in
/-- The deck involution of the orientation cover lies over the base. -/
private theorem deck_comp_projHom :
    TopCat.ofHom ((VectorBundleOrientationCover.deck :
      OrientationCover 𝓘(ℝ, E) M ≃ₜ OrientationCover 𝓘(ℝ, E) M) :
        C(OrientationCover 𝓘(ℝ, E) M, OrientationCover 𝓘(ℝ, E) M)) ≫ projHom M = projHom M :=
  TopCat.hom_ext (ContinuousMap.ext (congrFun VectorBundleOrientationCover.proj_comp_deck))

/-- The deck involution negates the fundamental class of the orientation cover with coefficients
in `ℤ`. -/
theorem homologyMap_deck_coverFundamentalClass :
    (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom ((VectorBundleOrientationCover.deck :
        OrientationCover 𝓘(ℝ, E) M ≃ₜ OrientationCover 𝓘(ℝ, E) M) :
          C(OrientationCover 𝓘(ℝ, E) M, OrientationCover 𝓘(ℝ, E) M))))
            (ModuleCat.of ℤ ℤ) (n + 1)).hom (coverFundamentalClass M hE) =
      -coverFundamentalClass M hE := by
  have hdeck := congrArg (fun φ ↦ φ.hom ((homologicalOrientation hE).fundamentalClass hE))
    (homologyMap_comp_uliftIntHomologyIso_hom
      (TopCat.ofHom ((VectorBundleOrientationCover.deck :
        OrientationCover 𝓘(ℝ, E) M ≃ₜ OrientationCover 𝓘(ℝ, E) M) :
          C(OrientationCover 𝓘(ℝ, E) M, OrientationCover 𝓘(ℝ, E) M))) (n + 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hdeck
  have hτ : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom
      ((VectorBundleOrientationCover.deck :
        OrientationCover 𝓘(ℝ, E) M ≃ₜ OrientationCover 𝓘(ℝ, E) M) :
          C(OrientationCover 𝓘(ℝ, E) M, OrientationCover 𝓘(ℝ, E) M))))
            (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + 1)).hom
        ((homologicalOrientation hE).fundamentalClass hE) =
      -(homologicalOrientation hE).fundamentalClass hE :=
    (HomologicalOrientation.mapFundamentalClass_def _ hE _).symm.trans (mapFundamentalClass_deck hE)
  rw [coverFundamentalClass, ← hdeck, hτ, map_neg]

/-- The projection of the orientation cover kills its fundamental class: `π_*[M'] = 0` in
`Hₙ₊₁(M; ℤ)`. Since `π ∘ τ = π`, the class `π_*[M']` equals its own negative, and the top homology
of a compact manifold is torsion-free. -/
theorem homologyMap_projHom_coverFundamentalClass :
    (SSet.homologyMap (TopCat.toSSet.map (projHom M)) (ModuleCat.of ℤ ℤ) (n + 1)).hom
      (coverFundamentalClass M hE) = 0 := by
  have hneg := congrArg (fun φ ↦ (SSet.homologyMap (TopCat.toSSet.map φ) (ModuleCat.of ℤ ℤ)
    (n + 1)).hom (coverFundamentalClass M hE)) (deck_comp_projHom (E := E) (M := M))
  simp only [Functor.map_comp, SSet.homologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    homologyMap_deck_coverFundamentalClass, map_neg] at hneg
  generalize (SSet.homologyMap (TopCat.toSSet.map (projHom M)) (ModuleCat.of ℤ ℤ) (n + 1)).hom
    (coverFundamentalClass M hE) = c at hneg ⊢
  -- The top homology of a compact manifold is projective, hence torsion-free.
  have := projective_singularHomology_of_compactSpace (ModuleCat.of ℤ ℤ) (M := M) hE le_rfl
  have : Module.Projective ℤ ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ ℤ)
      (n + 1) : ModuleCat.{0} ℤ) :=
    ModuleCat.projective_of_module_projective
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of M))
  have h2 : c + c = 0 := by
    nth_rw 1 [← hneg]
    exact neg_add_cancel c
  exact ((smul_eq_zero (R := ℤ)).1 ((two_smul ℤ c).trans h2)).resolve_left two_ne_zero

variable (M) in
/-- The fundamental class of the orientation cover, as a class of `M` twisted by the permutation
local system, comes from the orientation local system: `π_*[M'] = 0`, and the coefficient long
exact sequence of `0 ⟶ o(TM) ⟶ ℤ[π⁻¹ x] ⟶ ℤ ⟶ 0` applies. -/
private theorem exists_signLocalSystemToPermutation_eq_coverFundamentalClass :
    ∃ g, (twistedHomologyCoefficientMap
      ((isCoveringMap_projHom E M).signLocalSystemToPermutation ℤ
        VectorBundleOrientationCover.proj_comp_deck (finite_preimage_projHom M)) (n + 1)).hom g =
      ((isCoveringMap_projHom E M).singularHomologyPermutationIso ℤ (n + 1)).hom.hom
        (coverFundamentalClass M hE) :=
  (isCoveringMap_projHom E M).exists_twistedHomologyCoefficientMap_signLocalSystemToPermutation_eq
    ℤ VectorBundleOrientationCover.proj_comp_deck VectorBundleOrientationCover.deck_deck
    (finite_preimage_projHom M) VectorBundleOrientationCover.deck_ne_self
    (fun _ _ h ↦ VectorBundleOrientationCover.eq_or_eq_deck (Fintype.card_fin _) h)
    (VectorBundleOrientationCover.surjective_proj (Fintype.card_fin _)) (n + 1)
    (coverFundamentalClass M hE) (homologyMap_projHom_coverFundamentalClass hE)

include hE in
/-- Reading functions on the fibres of the orientation cover as formal sums of sheets is injective
on `Hₙ₊₁(M; o(TM))`, since `Hₙ₊₂(M; ℤ) = 0`. -/
private theorem injective_twistedHomologyCoefficientMap_signLocalSystemToPermutation :
    Function.Injective (twistedHomologyCoefficientMap
      ((isCoveringMap_projHom E M).signLocalSystemToPermutation ℤ
        VectorBundleOrientationCover.proj_comp_deck (finite_preimage_projHom M)) (n + 1)).hom :=
  (isCoveringMap_projHom E M).injective_twistedHomologyCoefficientMap_signLocalSystemToPermutation
    ℤ VectorBundleOrientationCover.proj_comp_deck VectorBundleOrientationCover.deck_deck
    (finite_preimage_projHom M) VectorBundleOrientationCover.deck_ne_self
    (fun _ _ h ↦ VectorBundleOrientationCover.eq_or_eq_deck (Fintype.card_fin _) h)
    (VectorBundleOrientationCover.surjective_proj (Fintype.card_fin _)) (n + 1)
    (isZero_singularHomology_of_compactSpace (ModuleCat.of ℤ ℤ) (M := M) hE (by omega))

variable (M) in
/-- **The orientation-twisted fundamental class** `[M]_or ∈ Hₙ₊₁(M; o(TM))` of a compact
boundaryless manifold, orientable or not: the class which, with each function on a fibre of the
orientation double cover read as the formal sum of its sheets, is the fundamental class `[M']` of
the cover. It exists because `π_*[M'] = 0`, by the coefficient long exact sequence of
`0 ⟶ o(TM) ⟶ ℤ[π⁻¹ x] ⟶ ℤ ⟶ 0`, and is unique because `Hₙ₊₂(M; ℤ) = 0`
(`TauCeti.Manifold.OrientationCover.eq_twistedFundamentalClass`). -/
def twistedFundamentalClass :
    twistedHomology ((isCoveringMap_projHom E M).signLocalSystem ℤ _
      VectorBundleOrientationCover.proj_comp_deck) (n + 1) :=
  (exists_signLocalSystemToPermutation_eq_coverFundamentalClass M hE).choose

/-- **Returning to the cover gives its fundamental class**: reading the twisted fundamental class
`[M]_or` as a class of the orientation cover gives `[M']`. -/
theorem singularHomologyPermutationIso_inv_twistedFundamentalClass :
    ((isCoveringMap_projHom E M).singularHomologyPermutationIso ℤ (n + 1)).inv.hom
        ((twistedHomologyCoefficientMap ((isCoveringMap_projHom E M).signLocalSystemToPermutation ℤ
          VectorBundleOrientationCover.proj_comp_deck
            (finite_preimage_projHom M)) (n + 1)).hom
          (twistedFundamentalClass M hE)) =
      coverFundamentalClass M hE := by
  rw [twistedFundamentalClass,
    (exists_signLocalSystemToPermutation_eq_coverFundamentalClass M hE).choose_spec,
    ← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply]

/-- **Uniqueness of the twisted fundamental class**: a class of `Hₙ₊₁(M; o(TM))` which, read as a
class of the orientation cover, is `[M']` is the twisted fundamental class. -/
theorem eq_twistedFundamentalClass
    {g : twistedHomology ((isCoveringMap_projHom E M).signLocalSystem ℤ _
      VectorBundleOrientationCover.proj_comp_deck) (n + 1)}
    (hg : ((isCoveringMap_projHom E M).singularHomologyPermutationIso ℤ (n + 1)).inv.hom
        ((twistedHomologyCoefficientMap ((isCoveringMap_projHom E M).signLocalSystemToPermutation ℤ
          VectorBundleOrientationCover.proj_comp_deck
            (finite_preimage_projHom M)) (n + 1)).hom g) =
      coverFundamentalClass M hE) :
    g = twistedFundamentalClass M hE :=
  injective_twistedHomologyCoefficientMap_signLocalSystemToPermutation hE
    ((ModuleCat.mono_iff_injective
      ((isCoveringMap_projHom E M).singularHomologyPermutationIso ℤ (n + 1)).inv).1 inferInstance
        (hg.trans (singularHomologyPermutationIso_inv_twistedFundamentalClass hE).symm))

/-- **Antisymmetrizing the fundamental class of the cover gives twice the twisted fundamental
class**: under antisymmetrization `f ↦ (ω ↦ f ω - f (-ω))` from `Hₙ₊₁(M'; ℤ)` to
`Hₙ₊₁(M; o(TM))`, the image of `[M']` is `2 • [M]_or`. Read back on the cover it is
`[M'] - τ_*[M'] = 2 • [M']`. -/
theorem permutationLocalSystemToSign_coverFundamentalClass :
    (twistedHomologyCoefficientMap ((isCoveringMap_projHom E M).permutationLocalSystemToSign ℤ
      VectorBundleOrientationCover.proj_comp_deck VectorBundleOrientationCover.deck_deck)
        (n + 1)).hom
      (((isCoveringMap_projHom E M).singularHomologyPermutationIso ℤ (n + 1)).hom.hom
        (coverFundamentalClass M hE)) =
      (2 : ℤ) • twistedFundamentalClass M hE := by
  refine injective_twistedHomologyCoefficientMap_signLocalSystemToPermutation hE
    ((ModuleCat.mono_iff_injective
      ((isCoveringMap_projHom E M).singularHomologyPermutationIso ℤ (n + 1)).inv).1
        inferInstance ?_)
  have h := congrArg (fun φ ↦ φ.hom (coverFundamentalClass M hE))
    ((isCoveringMap_projHom E M).singularHomologyPermutationIso_hom_comp_toSign_comp_toPermutation
      ℤ VectorBundleOrientationCover.proj_comp_deck VectorBundleOrientationCover.deck_deck
      (finite_preimage_projHom M) (n + 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sub, ModuleCat.hom_id,
    LinearMap.sub_apply, LinearMap.id_apply] at h
  rw [h, map_zsmul, map_zsmul, singularHomologyPermutationIso_inv_twistedFundamentalClass,
    homologyMap_deck_coverFundamentalClass, sub_neg_eq_add, two_zsmul]

/-- **The twisted fundamental class has infinite order** when `M` is nonempty: `k • [M]_or ≠ 0`
for every nonzero integer `k`. -/
theorem zsmul_twistedFundamentalClass_ne_zero [Nonempty M] {k : ℤ} (hk : k ≠ 0) :
    k • twistedFundamentalClass M hE ≠ 0 := by
  intro h
  set o := homologicalOrientation (M := M) hE
  -- Returning to the cover, `k • [M'] = 0`.
  have h2 := congrArg (fun c ↦ ((isCoveringMap_projHom E M).singularHomologyPermutationIso ℤ
    (n + 1)).inv.hom ((twistedHomologyCoefficientMap
      ((isCoveringMap_projHom E M).signLocalSystemToPermutation ℤ
        VectorBundleOrientationCover.proj_comp_deck (finite_preimage_projHom M)) (n + 1)).hom c)) h
  rw [map_zsmul, map_zsmul, singularHomologyPermutationIso_inv_twistedFundamentalClass, map_zero,
    map_zero, coverFundamentalClass, ← map_zsmul] at h2
  have h3 : k • o.fundamentalClass hE = 0 :=
    (ModuleCat.mono_iff_injective (uliftIntHomologyIso _ (n + 1)).hom).1 inferInstance
      (h2.trans (map_zero _).symm)
  -- Its image in the local homology at a point of the cover is `k • o x`.
  obtain ⟨b⟩ := ‹Nonempty M›
  obtain ⟨x, -⟩ := VectorBundleOrientationCover.surjective_proj (F := E)
    (E := (TangentSpace 𝓘(ℝ, E) : M → Type)) (Fintype.card_fin _) b
  have h4 := congrArg (singularHomologyToLocalHomology _ x (n + 1)) h3
  rw [map_zsmul, HomologicalOrientation.singularHomologyToLocalHomology_fundamentalClass,
    map_zero, ← zero_zsmul (o x).val] at h4
  exact hk (o.zsmul_left_injective hE x h4)

/-- The twisted fundamental class of a nonempty manifold is nonzero. -/
theorem twistedFundamentalClass_ne_zero [Nonempty M] : twistedFundamentalClass M hE ≠ 0 := by
  simpa using zsmul_twistedFundamentalClass_ne_zero (M := M) hE one_ne_zero

end TauCeti.Manifold.OrientationCover
