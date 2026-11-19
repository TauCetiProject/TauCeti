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
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

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

When `M` is oriented, by an orientation `o`, the twisted fundamental class is the ordinary one.
The orientation is a continuous section `s : x ↦ (x, oₓ)` of the cover
(`TauCeti.Manifold.OrientationCover.orientationSection`), which trivializes `o(TM)` by
evaluating a function on the two orientations of `TₓM` at `oₓ`. The cover is the union of the
two sheets `s(M)` and `τ(s(M))`; the section preserves the orientations and `τ ∘ s` reverses them,
so their local degrees give `[M'] = s_*[M] - (τ ∘ s)_*[M]`
(`mapFundamentalClass_orientationSection_sub_mapFundamentalClass_deck_comp`).
On the other hand, through the trivialization a class `c` of `M` reads on the cover as
`s_* c - (τ ∘ s)_* c`. By uniqueness of `[M]_or`, the trivialization carries `[M]_or` to the
fundamental class `[M]` of `o`
(`TauCeti.Manifold.OrientationCover.twistedHomologyConstantIso_hom_twistedFundamentalClass`).

## Main definitions

* `TauCeti.Manifold.OrientationCover.homologicalOrientation`: the homological orientation of the
  orientation cover given by its canonical orientation.
* `TauCeti.Manifold.OrientationCover.twistedFundamentalClass`: `[M]_or ∈ Hₙ₊₁(M; o(TM))`.
* `TauCeti.Manifold.OrientationCover.orientationSection`: the section `x ↦ (x, oₓ)` of the
  orientation cover given by an orientation `o`.

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
* `mapFundamentalClass_orientationSection_sub_mapFundamentalClass_deck_comp`:
  for an orientation `o` with section `s`, `[M'] = s_*[M] - (τ ∘ s)_*[M]`.
* `TauCeti.Manifold.OrientationCover.twistedHomologyCoefficientMap_inv_fundamentalClass`: the
  trivialization of `o(TM)` given by `o` carries `[M]` back to `[M]_or`.
* `TauCeti.Manifold.OrientationCover.twistedHomologyConstantIso_hom_twistedFundamentalClass`: the
  trivialization of `o(TM)` given by `o` carries `[M]_or` to the fundamental class of `o`.

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
  rw [o.singularHomologyToLocalHomology_mapFundamentalClass o hE, hdeg, neg_one_zsmul,
    HomologicalOrientation.neg_apply, LocalOrientation.coe_neg]

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

/-! ### The twisted fundamental class of an oriented manifold -/

section Oriented

open TauCeti.Manifold.Orientation

variable (o : Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E)))

/-- The section of the orientation double cover given by an orientation `o` of `M`: it sends `x`
to the point of the cover over `x` recording the orientation `oₓ` of `TₓM`. -/
def orientationSection : C(M, OrientationCover 𝓘(ℝ, E) M) :=
  ⟨fun x ↦ ⟨x, o.toVectorBundleOrientation x⟩,
    o.toVectorBundleOrientation.continuous_mk_cover (Fintype.card_fin _)⟩

omit [T2Space M] [CompactSpace M] in
/-- The section given by an orientation `o` sends `x` to `(x, oₓ)`. -/
@[simp]
theorem orientationSection_apply (x : M) : orientationSection o x = ⟨x, o.orientationAt x⟩ :=
  congrArg (VectorBundleOrientationCover.mk x) (o.toVectorBundleOrientation_apply x)

omit [T2Space M] [CompactSpace M] in
/-- The section given by an orientation is a section of the projection of the cover. -/
theorem orientationSection_mem_preimage_projHom (x : M) :
    orientationSection o x ∈ projHom M ⁻¹' {x} :=
  (rfl)

omit [T2Space M] [CompactSpace M] in
/-- The section given by an orientation `o` preserves orientations, from `o` to the canonical
orientation of the cover: it is smooth, since its composite with the projection, a local
diffeomorphism, is the identity, and the projection carries the canonical orientation at
`(x, oₓ)` to `oₓ`. -/
private theorem isOrientationPreservingAt_orientationSection (x : M) :
    IsOrientationPreservingAt o canonicalOrientation (orientationSection o) x := by
  have hπs : VectorBundleOrientationCover.proj ∘ ⇑(orientationSection o) = id := rfl
  have hs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (orientationSection o) :=
    ContMDiff.of_comp_isLocalDiffeomorph isLocalDiffeomorph_proj (orientationSection o).continuous
      (hπs ▸ contMDiff_id)
  obtain ⟨D, hD⟩ := (isLocalDiffeomorph_proj (I := 𝓘(ℝ, E)) (M := M) (n := 1)).isInvertible_mfderiv
    one_ne_zero (orientationSection o x)
  refine IsOrientationPreservingAt.of_comp (g := VectorBundleOrientationCover.proj)
    ((isOrientationPreservingAt_iff_of_coe_eq _ _ _ _ D hD).2
      ((map_orientationAt_canonicalOrientation _ D hD).trans (o.toVectorBundleOrientation_apply x)))
    ?_ (hs.mdifferentiableAt one_ne_zero)
  rw [hπs]
  exact isOrientationPreservingAt_id o x

omit [CompactSpace M] in
/-- The section given by an orientation has local index `1` everywhere. -/
private theorem localIndex_orientationSection (x : M) :
    ((o.reindex (finCongr hE)).toHomologicalOrientation hE).localIndex (homologicalOrientation hE)
      (orientationSection o) x = 1 := by
  have h := (isOrientationPreservingAt_orientationSection o x).reindex (finCongr hE)
  exact (localIndex_toHomologicalOrientation hE hE _ _ _ h.isInvertible_mfderiv).trans
    (orientationSign_of_isOrientationPreservingAt h)

omit [CompactSpace M] in
/-- The other sheet `τ ∘ s` of the section given by an orientation has local index `-1`
everywhere: the deck involution reverses the canonical orientation. -/
private theorem localIndex_deck_comp_orientationSection (x : M) :
    ((o.reindex (finCongr hE)).toHomologicalOrientation hE).localIndex (homologicalOrientation hE)
      (((VectorBundleOrientationCover.deck :
        OrientationCover 𝓘(ℝ, E) M ≃ₜ OrientationCover 𝓘(ℝ, E) M) :
          C(OrientationCover 𝓘(ℝ, E) M, OrientationCover 𝓘(ℝ, E) M)).comp (orientationSection o))
        x = -1 := by
  have h := ((isOrientationReversingAt_deck (orientationSection o x)).comp_preserving
    (isOrientationPreservingAt_orientationSection o x)).reindex (finCongr hE)
  exact (localIndex_toHomologicalOrientation hE hE _ _ _ h.isInvertible_mfderiv).trans
    (orientationSign_of_isOrientationReversingAt h)

/-- **The fundamental class of the orientation cover of an oriented manifold.** For an
orientation `o` of `M`, the orientation cover is the union of the two sheets `s(M)` and `τ(s(M))`,
where `s` is the section given by `o` and `τ` is the deck involution. Its fundamental class is
`[M'] = s_*[M] - (τ ∘ s)_*[M]`: the section preserves the orientations and `τ ∘ s` reverses
them. -/
theorem mapFundamentalClass_orientationSection_sub_mapFundamentalClass_deck_comp :
    ((o.reindex (finCongr hE)).toHomologicalOrientation hE).mapFundamentalClass hE
        (orientationSection o) -
      ((o.reindex (finCongr hE)).toHomologicalOrientation hE).mapFundamentalClass hE
        (((VectorBundleOrientationCover.deck :
        OrientationCover 𝓘(ℝ, E) M ≃ₜ OrientationCover 𝓘(ℝ, E) M) :
          C(OrientationCover 𝓘(ℝ, E) M, OrientationCover 𝓘(ℝ, E) M)).comp (orientationSection o)) =
      (homologicalOrientation hE).fundamentalClass hE := by
  set oM := (o.reindex (finCongr hE)).toHomologicalOrientation hE
  set s := orientationSection o
  set t := ((VectorBundleOrientationCover.deck :
    OrientationCover 𝓘(ℝ, E) M ≃ₜ OrientationCover 𝓘(ℝ, E) M) :
      C(OrientationCover 𝓘(ℝ, E) M, OrientationCover 𝓘(ℝ, E) M)).comp s
  refine (homologicalOrientation hE).eq_fundamentalClass hE fun y ↦ ?_
  refine (map_sub (singularHomologyToLocalHomology (ModuleCat.of ℤ (ULift.{0} ℤ)) y (n + 1)) _
    _).trans ?_
  rw [oM.singularHomologyToLocalHomology_mapFundamentalClass (homologicalOrientation hE) hE,
    oM.singularHomologyToLocalHomology_mapFundamentalClass (homologicalOrientation hE) hE]
  -- Every point of the cover lies on one of the two sheets, and a point of either sheet over `x`
  -- determines `x` by projection, since `τ` lies over `M`.
  obtain ⟨x, rfl | rfl⟩ : ∃ x, y = s x ∨ y = VectorBundleOrientationCover.deck (s x) :=
    ⟨y.proj, VectorBundleOrientationCover.eq_or_eq_deck (Fintype.card_fin _) rfl⟩
  · have h₁ : s ⁻¹' {s x} = {x} := Set.eq_singleton_iff_unique_mem.2
      ⟨rfl, fun z hz ↦ congrArg VectorBundleOrientationCover.proj hz⟩
    have h₂ : s x ∉ Set.range t := by
      rintro ⟨z, hz⟩
      obtain rfl : z = x := (VectorBundleOrientationCover.proj_deck (s z)).symm.trans
        (congrArg VectorBundleOrientationCover.proj hz)
      exact VectorBundleOrientationCover.deck_ne_self _ hz
    rw [oM.localDegree_eq_localIndex _ hE hE s h₁, localIndex_orientationSection,
      oM.localDegree_eq_zero_of_notMem_range _ hE hE _ h₂, one_zsmul, zero_zsmul, sub_zero]
  · have h₁ : t ⁻¹' {VectorBundleOrientationCover.deck (s x)} = {x} :=
      Set.eq_singleton_iff_unique_mem.2
        ⟨rfl, fun z hz ↦ (VectorBundleOrientationCover.proj_deck (s z)).symm.trans
          ((congrArg VectorBundleOrientationCover.proj hz).trans
            (VectorBundleOrientationCover.proj_deck (s x)))⟩
    have h₂ : VectorBundleOrientationCover.deck (s x) ∉ Set.range s := by
      rintro ⟨z, hz⟩
      obtain rfl : z = x := (congrArg VectorBundleOrientationCover.proj hz).trans
        (VectorBundleOrientationCover.proj_deck (s x))
      exact VectorBundleOrientationCover.deck_ne_self _ hz.symm
    rw [oM.localDegree_eq_zero_of_notMem_range _ hE hE _ h₂,
      oM.localDegree_eq_localIndex _ hE hE t h₁,
      localIndex_deck_comp_orientationSection, zero_zsmul, neg_one_zsmul, zero_sub, neg_neg]

omit [T2Space M] [CompactSpace M] in
/-- Homology with constant coefficients `ULift ℤ` and `ℤ` are identified compatibly with singular
homology: the coefficient map of `ULift ℤ ≅ ℤ` on the constant systems is `uliftIntHomologyIso`. -/
private theorem twistedHomologyCoefficientMap_uliftIntIso_apply (k : ℕ)
    (c : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) k :
      ModuleCat.{0} ℤ)) :
    (twistedHomologyCoefficientMap
      ((LocalCoefficientSystem.constantFunctor (TopCat.of M)).map uliftIntIso.hom) k).hom
        ((twistedHomologyConstantIso (TopCat.of M) (ModuleCat.of ℤ (ULift.{0} ℤ)) k).inv.hom c) =
      (twistedHomologyConstantIso (TopCat.of M) (ModuleCat.of ℤ ℤ) k).inv.hom
        ((uliftIntHomologyIso (TopCat.of M) k).hom.hom c) := by
  have h := ConcreteCategory.congr_hom
    (twistedHomologyConstantIso_hom_naturality (TopCat.of M) uliftIntIso.hom k)
    ((twistedHomologyConstantIso (TopCat.of M) (ModuleCat.of ℤ (ULift.{0} ℤ)) k).inv.hom c)
  -- `h` reads `Z (A (U⁻¹ c)) = F (U (U⁻¹ c))`; apply `Z⁻¹` and cancel `U ∘ U⁻¹`.
  exact (Iso.hom_inv_id_apply _ _).symm.trans (congrArg (twistedHomologyConstantIso _ _ k).inv.hom
    (h.trans ((congrArg _ (Iso.inv_hom_id_apply _ c)).trans
      (congrArg (fun φ ↦ φ.hom c) (uliftIntHomologyIso_hom (TopCat.of M) k).symm))))

omit [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M] in
/-- A section `u` of the orientation cover induces `u_*` on homology through the coefficient map
`r ↦ r • u x`, read on the cover. -/
private theorem singularHomologyPermutationIso_inv_twistedHomologyCoefficientMap_apply (k : ℕ)
    (u : C(M, OrientationCover 𝓘(ℝ, E) M)) (hu : ∀ x, u x ∈ projHom M ⁻¹' {x})
    (d : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ ℤ) k : ModuleCat.{0} ℤ)) :
    ((isCoveringMap_projHom E M).singularHomologyPermutationIso ℤ k).inv.hom
        ((twistedHomologyCoefficientMap
          ((isCoveringMap_projHom E M).permutationLocalSystemSection ℤ u hu) k).hom
            ((twistedHomologyConstantIso (TopCat.of M) (ModuleCat.of ℤ ℤ) k).inv.hom d)) =
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom u)) (ModuleCat.of ℤ ℤ) k).hom d := by
  have h := ConcreteCategory.congr_hom
    ((isCoveringMap_projHom E M).homologyMap_comp_singularHomologyPermutationIso_hom_of_section
      ℤ u hu k) d
  -- `h` reads `P (u_* d) = A (Z⁻¹ d)`; apply `P⁻¹`.
  exact (congrArg ((isCoveringMap_projHom E M).singularHomologyPermutationIso ℤ k).inv.hom
    h.symm).trans (Iso.hom_inv_id_apply _ _)

/-- **The twisted fundamental class of an oriented manifold, from its fundamental class.** An
orientation `o` of `M` trivializes the orientation local system `o(TM)`, by evaluating a function
on the two orientations of `TₓM` at `oₓ`. The twisted fundamental class `[M]_or` is the image of
the fundamental class `[M]` of `o` under the inverse of this trivialization: read on the
orientation cover, that image is `s_*[M] - (τ ∘ s)_*[M] = [M']`, for the section `s` given by `o`
and the deck involution `τ`. -/
theorem twistedHomologyCoefficientMap_inv_fundamentalClass :
    (twistedHomologyCoefficientMap ((isCoveringMap_projHom E M).signLocalSystemIsoOfSection
        (R := ℤ) (hσ := VectorBundleOrientationCover.proj_comp_deck)
        VectorBundleOrientationCover.deck_ne_self
        (fun _ _ h ↦ VectorBundleOrientationCover.eq_or_eq_deck (Fintype.card_fin _) h)
        (orientationSection o) (orientationSection_mem_preimage_projHom o)).inv (n + 1)).hom
        ((twistedHomologyConstantIso (TopCat.of M) (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + 1)).inv.hom
          (((o.reindex (finCongr hE)).toHomologicalOrientation hE).fundamentalClass hE)) =
      twistedFundamentalClass M hE := by
  set hp := isCoveringMap_projHom E M
  set s := orientationSection o
  set t := ((VectorBundleOrientationCover.deck :
    OrientationCover 𝓘(ℝ, E) M ≃ₜ OrientationCover 𝓘(ℝ, E) M) :
      C(OrientationCover 𝓘(ℝ, E) M, OrientationCover 𝓘(ℝ, E) M)).comp s
  have hs := orientationSection_mem_preimage_projHom o
  have ht (x : M) : t x ∈ projHom M ⁻¹' {x} := VectorBundleOrientationCover.proj_deck (s x)
  set c := ((o.reindex (finCongr hE)).toHomologicalOrientation hE).fundamentalClass hE
  set d := (uliftIntHomologyIso (TopCat.of M) (n + 1)).hom.hom c
  -- On coefficients, the inverse trivialization followed by reading functions as formal sums of
  -- sheets is the identification `ULift ℤ ≅ ℤ` followed by the difference of the sections.
  have hφ : (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toModuleIso.hom = uliftIntIso.hom :=
    ModuleCat.hom_ext (LinearMap.ext fun _ ↦ (uliftIntIso_hom_apply _).symm)
  have hcoef := congrArg (twistedHomologyCoefficientMap · (n + 1))
    (hp.signLocalSystemIsoOfSection_inv_comp_signLocalSystemToPermutation ℤ
      VectorBundleOrientationCover.proj_comp_deck (finite_preimage_projHom M)
      VectorBundleOrientationCover.deck_ne_self
      (fun _ _ h ↦ VectorBundleOrientationCover.eq_or_eq_deck (Fintype.card_fin _) h) s t hs ht
      fun _ ↦ rfl)
  simp only [hφ, twistedHomologyCoefficientMap_comp, twistedHomologyCoefficientMap_sub] at hcoef
  have e :=
    (ConcreteCategory.congr_hom hcoef _).trans (congrArg
      (fun y ↦ (twistedHomologyCoefficientMap (hp.permutationLocalSystemSection ℤ s hs) (n + 1) -
        twistedHomologyCoefficientMap (hp.permutationLocalSystemSection ℤ t ht) (n + 1)).hom y)
      (twistedHomologyCoefficientMap_uliftIntIso_apply (n + 1) c))
  -- Read on the cover, the class is `s_* d - t_* d = [M']`, by uniqueness of `[M]_or`.
  refine eq_twistedFundamentalClass hE
    ((congrArg (hp.singularHomologyPermutationIso ℤ (n + 1)).inv.hom
      (e.trans (LinearMap.sub_apply _ _ _))).trans ?_)
  have hulift (u : C(M, OrientationCover 𝓘(ℝ, E) M)) :
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom u)) (ModuleCat.of ℤ ℤ) (n + 1)).hom d =
        (uliftIntHomologyIso _ (n + 1)).hom.hom
          (((o.reindex (finCongr hE)).toHomologicalOrientation hE).mapFundamentalClass hE u) := by
    rw [HomologicalOrientation.mapFundamentalClass_def]
    exact (ConcreteCategory.congr_hom
      (homologyMap_comp_uliftIntHomologyIso_hom (TopCat.ofHom u) (n + 1)) c).symm
  rw [map_sub, singularHomologyPermutationIso_inv_twistedHomologyCoefficientMap_apply,
    singularHomologyPermutationIso_inv_twistedHomologyCoefficientMap_apply, hulift, hulift]
  exact (map_sub (uliftIntHomologyIso _ (n + 1)).hom.hom _ _).symm.trans
    ((congrArg (uliftIntHomologyIso _ (n + 1)).hom.hom
      (mapFundamentalClass_orientationSection_sub_mapFundamentalClass_deck_comp hE o)).trans
        (coverFundamentalClass_def (M := M) hE).symm)

/-- **The twisted fundamental class of an oriented manifold is its fundamental class.** An
orientation `o` of `M` trivializes the orientation local system `o(TM)`, by evaluating a function
on the two orientations of `TₓM` at `oₓ`. Under this trivialization, followed by the
identification of homology with constant coefficients with singular homology, the twisted
fundamental class `[M]_or ∈ Hₙ₊₁(M; o(TM))` is the fundamental class `[M] ∈ Hₙ₊₁(M; ℤ)` of `o`. -/
theorem twistedHomologyConstantIso_hom_twistedFundamentalClass :
    (twistedHomologyConstantIso (TopCat.of M) (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + 1)).hom.hom
        ((twistedHomologyCoefficientMap ((isCoveringMap_projHom E M).signLocalSystemIsoOfSection
          (R := ℤ) (hσ := VectorBundleOrientationCover.proj_comp_deck)
          VectorBundleOrientationCover.deck_ne_self
          (fun _ _ h ↦ VectorBundleOrientationCover.eq_or_eq_deck (Fintype.card_fin _) h)
          (orientationSection o) (orientationSection_mem_preimage_projHom o)).hom (n + 1)).hom
            (twistedFundamentalClass M hE)) =
      ((o.reindex (finCongr hE)).toHomologicalOrientation hE).fundamentalClass hE := by
  rw [← twistedHomologyCoefficientMap_inv_fundamentalClass hE o]
  set triv := (isCoveringMap_projHom E M).signLocalSystemIsoOfSection (R := ℤ)
    (hσ := VectorBundleOrientationCover.proj_comp_deck) VectorBundleOrientationCover.deck_ne_self
    (fun _ _ h ↦ VectorBundleOrientationCover.eq_or_eq_deck (Fintype.card_fin _) h)
    (orientationSection o) (orientationSection_mem_preimage_projHom o)
  have hid := (twistedHomologyCoefficientMap_comp triv.inv triv.hom (n + 1)).symm.trans
    ((congrArg (twistedHomologyCoefficientMap · (n + 1)) triv.inv_hom_id).trans
      (twistedHomologyCoefficientMap_id _ (n + 1)))
  exact (congrArg _ (ConcreteCategory.congr_hom hid _)).trans (Iso.inv_hom_id_apply _ _)

end Oriented

end TauCeti.Manifold.OrientationCover
