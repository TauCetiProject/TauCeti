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
the permutation local system of `π`, antisymmetrization `f ↦ (ω ↦ f ω - f (-ω))` gives a map
`Hₖ(M'; ℤ) → Hₖ(M; o(TM))`. The **orientation-twisted fundamental class** of `M` is the image of
`[M']`
(`TauCeti.Manifold.OrientationCover.twistedFundamentalClass`):

`[M]_or ∈ Hₙ₊₁(M; o(TM))`.

It exists whether or not `M` is orientable. Reading a function on a fibre back as a formal sum of
sheets returns from `Hₙ₊₁(M; o(TM))` to `Hₙ₊₁(M'; ℤ)`, and carries `[M]_or` to
`[M'] - τ_*[M'] = 2 • [M']`
(`TauCeti.Manifold.OrientationCover.singularHomologyPermutationIso_inv_twistedFundamentalClass`).
So `[M]_or` has infinite order as soon as `M` is nonempty
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
  returning to the cover carries `[M]_or` to `2 • [M']`.
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
    rw [show projHom (E := E) M ⁻¹' {b} = VectorBundleOrientationCover.proj ⁻¹' {b} from rfl,
      VectorBundleOrientationCover.ncard_fiber (Fintype.card_fin _)]
    exact two_ne_zero))

/-- The homological orientation of the orientation cover given by its canonical orientation. -/
def homologicalOrientation :
    HomologicalOrientation (OrientationCover 𝓘(ℝ, E) M) E (n + 1) :=
  (canonicalOrientation.reindex (finCongr hE)).toHomologicalOrientation hE

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
  exact (TauCeti.Manifold.Orientation.localIndex_toHomologicalOrientation hE _ _ _ hinv).trans
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

variable (M) in
/-- **The orientation-twisted fundamental class** `[M]_or ∈ Hₙ₊₁(M; o(TM))` of a compact
boundaryless manifold, orientable or not: the image of the fundamental class of the orientation
double cover under antisymmetrization `Hₙ₊₁(M'; ℤ) → Hₙ₊₁(M; o(TM))`. -/
def twistedFundamentalClass :
    twistedHomology ((isCoveringMap_projHom E M).signLocalSystem ℤ _
      VectorBundleOrientationCover.proj_comp_deck) (n + 1) :=
  (twistedHomologyCoefficientMap ((isCoveringMap_projHom E M).permutationLocalSystemToSign ℤ
      VectorBundleOrientationCover.proj_comp_deck VectorBundleOrientationCover.deck_deck)
        (n + 1)).hom
    (((isCoveringMap_projHom E M).singularHomologyPermutationIso ℤ (n + 1)).hom.hom
      (coverFundamentalClass M hE))

/-- **Returning to the cover doubles the fundamental class**: reading the twisted fundamental class
back as a class of the orientation cover gives `[M'] - τ_*[M'] = 2 • [M']`. -/
theorem singularHomologyPermutationIso_inv_twistedFundamentalClass :
    ((isCoveringMap_projHom E M).singularHomologyPermutationIso ℤ (n + 1)).inv.hom
        ((twistedHomologyCoefficientMap ((isCoveringMap_projHom E M).signLocalSystemToPermutation ℤ
          VectorBundleOrientationCover.proj_comp_deck
            (finite_preimage_projHom M)) (n + 1)).hom
          (twistedFundamentalClass M hE)) =
      (2 : ℤ) • coverFundamentalClass M hE := by
  have h := congrArg (fun φ ↦ φ.hom (coverFundamentalClass M hE))
    ((isCoveringMap_projHom E M).singularHomologyPermutationIso_hom_comp_toSign_comp_toPermutation ℤ
      VectorBundleOrientationCover.proj_comp_deck VectorBundleOrientationCover.deck_deck
      (finite_preimage_projHom M) (n + 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sub, ModuleCat.hom_id,
    LinearMap.sub_apply, LinearMap.id_apply] at h
  rw [twistedFundamentalClass, h]
  -- The deck involution negates the fundamental class of the cover.
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
  rw [coverFundamentalClass, ← hdeck, hτ, map_neg, sub_neg_eq_add, two_zsmul]

/-- **The twisted fundamental class has infinite order** when `M` is nonempty: `k • [M]_or ≠ 0`
for every nonzero integer `k`. -/
theorem zsmul_twistedFundamentalClass_ne_zero [Nonempty M] {k : ℤ} (hk : k ≠ 0) :
    k • twistedFundamentalClass M hE ≠ 0 := by
  intro h
  set o := homologicalOrientation (M := M) hE
  -- Returning to the cover, `(2 * k) • [M'] = 0`.
  have h2 := congrArg (fun c ↦ ((isCoveringMap_projHom E M).singularHomologyPermutationIso ℤ
    (n + 1)).inv.hom ((twistedHomologyCoefficientMap
      ((isCoveringMap_projHom E M).signLocalSystemToPermutation ℤ
        VectorBundleOrientationCover.proj_comp_deck (finite_preimage_projHom M)) (n + 1)).hom c)) h
  rw [map_zsmul, map_zsmul, singularHomologyPermutationIso_inv_twistedFundamentalClass, map_zero,
    map_zero, smul_smul, coverFundamentalClass, ← map_zsmul] at h2
  have h3 : (k * 2) • o.fundamentalClass hE = 0 :=
    (ModuleCat.mono_iff_injective (uliftIntHomologyIso _ (n + 1)).hom).1 inferInstance
      (h2.trans (map_zero _).symm)
  -- Its image in the local homology at a point of the cover is `(2 * k) • o x`.
  obtain ⟨b⟩ := ‹Nonempty M›
  obtain ⟨x, -⟩ := VectorBundleOrientationCover.surjective_proj (F := E)
    (E := (TangentSpace 𝓘(ℝ, E) : M → Type)) (Fintype.card_fin _) b
  have h4 := congrArg (singularHomologyToLocalHomology _ x (n + 1)) h3
  rw [map_zsmul, HomologicalOrientation.singularHomologyToLocalHomology_fundamentalClass,
    map_zero, ← zero_zsmul (o x).val] at h4
  exact mul_ne_zero hk two_ne_zero (o.zsmul_left_injective hE x h4)

/-- The twisted fundamental class of a nonempty manifold is nonzero. -/
theorem twistedFundamentalClass_ne_zero [Nonempty M] : twistedFundamentalClass M hE ≠ 0 := by
  simpa using zsmul_twistedFundamentalClass_ne_zero (M := M) hE one_ne_zero

end TauCeti.Manifold.OrientationCover
