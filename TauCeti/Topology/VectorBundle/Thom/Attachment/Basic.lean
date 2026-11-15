/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct
public import TauCeti.Topology.VectorBundle.Attachment
public import TauCeti.Topology.VectorBundle.SphereBundle.Radius
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Attaching disc bundles of positive radii and finite families of disc bundles

Let `Eᵢ → Bᵢ` (`i : ι`, `[Finite ι]`) be a finite family of real vector bundles whose fibre norms
are continuous on their total spaces, and let `rᵢ : Bᵢ → ℝ` be continuous positive radius
functions. Suppose a topological space `Z` is obtained from a closed subset `X` by attaching the
closed disc bundles `D_{rᵢ}(Eᵢ)` along their sphere bundles `S_{rᵢ}(Eᵢ)` through closed embeddings
`fᵢ : (D_{rᵢ}(Eᵢ), S_{rᵢ}(Eᵢ)) ⟶ (Z, X)` whose open disc interiors `fᵢ(D_{rᵢ}(Eᵢ)) \ X` are
pairwise disjoint (while their attaching sphere images inside `X` may overlap arbitrarily).

This file proves that the maps `fᵢ` induce direct-sum decompositions on relative singular homology
and cohomology in every degree, and identifies each summand with the Thom pair `(Eᵢ, (Eᵢ)₀)`:

* **Single disc bundle of radius `r`**
  (`TauCeti.isIso_singularHomologyMap_of_attach_discBundleOfRadius`,
  `TauCeti.isIso_singularCohomologyMap_of_attach_discBundleOfRadius`,
  `TauCeti.singularHomologyIsoThomPairOfAttachDiscBundleOfRadius`,
  `TauCeti.singularCohomologyIsoThomPairOfAttachDiscBundleOfRadius`): attaching `D_r(E)` along
  `S_r(E)` gives `Hₙ(E, E₀) ≅ Hₙ(D_r(E), S_r(E)) ≅ Hₙ(Z, X)` and
  `Hⁿ(Z, X) ≅ Hⁿ(D_r(E), S_r(E)) ≅ Hⁿ(E, E₀)`.
* **Finite family of unit or radius-`r` disc bundles**
  (`TauCeti.isIso_biproductDesc_singularHomologyMap_of_attach_discBundles`,
  `TauCeti.isIso_biproductDesc_singularHomologyMap_of_attach_discBundlesOfRadius`,
  `TauCeti.singularHomologyIsoThomPairsOfAttachDiscBundles`,
  `TauCeti.singularHomologyIsoThomPairsOfAttachDiscBundlesOfRadius`):
  `⨁ᵢ Hₙ(Eᵢ, (Eᵢ)₀; R) ≅ Hₙ(Z, X; R)`, with dual cohomology decompositions
  `Hⁿ(Z, X; R, M) ≅ ⨁ᵢ Hⁿ(Eᵢ, (Eᵢ)₀; R, M)`
  (`TauCeti.singularCohomologyIsoThomPairsOfAttachDiscBundles`,
  `TauCeti.singularCohomologyIsoThomPairsOfAttachDiscBundlesOfRadius`).
* **Ambient strong deformation retract**
  (`TauCeti.singularHomologyIsoThomPairsOfDeformationRetractAttachDiscBundlesOfRadius`): when `Y`
  contains `Z` and strong deformation retracts onto `Z` (as when crossing a Morse–Bott critical
  level `c`, where `{g ≤ c + ε}` strong deformation retracts onto `{g ≤ c - ε}` union the attached
  negative disc bundles), `⨁ᵢ Hₙ(Eᵢ, (Eᵢ)₀; R) ≅ Hₙ(Y, X; R)`.

Dimension additivity, below-rank vanishing, rank-degree `H₀` without orientation, and the classical
Morse point-base specialization are deduced in
`TauCeti.Topology.VectorBundle.Thom.Attachment.Finrank`.

## Proof of the finite-family decomposition

Single-bundle attachment of radius `r` reduces to unit-radius attachment
(`TauCeti.isIso_singularHomologyMap_of_attach_discBundle`) by precomposing with the radial
rescaling isomorphism `(D(E), S(E)) ≅ (D_r(E), S_r(E))` (`TauCeti.discSpherePairIsoOfRadius`).
For a finite family indexed by `Option α`, let `X'` be the union of `X` with the images of the
bundles indexed by `α`. Because each `f (some j)` is a closed embedding and `α` is finite, `X'` is
closed in `Z`, and because distinct open disc interiors do not meet outside `X`, the remaining
bundle `f none` meets `X'` only along its sphere bundle. In the long exact sequence of the triple
`(Z, X', X)`, the map `Hₖ(D(E_none), S(E_none)) ⟶ Hₖ(Z, X)` lifts the isomorphism onto `Hₖ(Z, X')`
in every degree `k`; this splits the triple sequence in both homology and cohomology and forces the
connecting morphisms to vanish without parity or degree restrictions.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press (1963),
  §3 and §5.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §2.1 and §4.D.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set Topology

universe uF w v u

namespace TauCeti

section PairIso

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

@[simps]
private def singularHomologyMapIso {P Q : TopPair.{w}} (e : P ≅ Q) (R : C) (n : ℕ) :
    P.singularHomology R n ≅ Q.singularHomology R n where
  hom := TopPair.singularHomologyMap e.hom R n
  inv := TopPair.singularHomologyMap e.inv R n
  hom_inv_id := by
    rw [← TopPair.singularHomologyMap_comp, e.hom_inv_id, TopPair.singularHomologyMap_id]
  inv_hom_id := by
    rw [← TopPair.singularHomologyMap_comp, e.inv_hom_id, TopPair.singularHomologyMap_id]

@[simps]
private def singularCohomologyMapIso {P Q : TopPair.{w}} (e : P ≅ Q) (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    Q.singularCohomology R k M n ≅ P.singularCohomology R k M n where
  hom := TopPair.singularCohomologyMap e.hom n
  inv := TopPair.singularCohomologyMap e.inv n
  hom_inv_id := by
    rw [← TopPair.singularCohomologyMap_comp, e.inv_hom_id, TopPair.singularCohomologyMap_id]
  inv_hom_id := by
    rw [← TopPair.singularCohomologyMap_comp, e.hom_inv_id, TopPair.singularCohomologyMap_id]

end PairIso

/-! ### Attaching a single disc bundle of prescribed radius -/

section SingleBundle

variable {B : Type w} {F : Type uF} {E : B → Type w} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [∀ b, NormedAddCommGroup (E b)]
  [∀ b, NormedSpace ℝ (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℝ F E] {Z : Type w} [TopologicalSpace Z] {X : Set Z}

section Radius

variable (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)
  {r : B → ℝ} (hr : Continuous r) (hrpos : ∀ b, 0 < r b)
  {f : discSpherePairOfRadius F E r ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
  (hf : IsClosedEmbedding (TopPair.Hom.fst f)) (hX : IsClosed X)
  (hfX : ∀ v : discBundleOfRadius F E r,
    TopPair.Hom.fst f v ∈ X → (v : TotalSpace F E) ∈ sphereBundleOfRadius F E r)
  (hfcover : X ∪ range (TopPair.Hom.fst f) = univ)

include hr hrpos in
private lemma rescaledAttach_fst_apply (v : discBundle F E) :
    (TopPair.Hom.fst ((discSpherePairIsoOfRadius F E hr hrpos).hom ≫ f) v : Z) =
      TopPair.Hom.fst f (discBundleHomeomorphOfRadius F E hr hrpos v) :=
  (ConcreteCategory.comp_apply
    (TopPair.Hom.fst (discSpherePairIsoOfRadius F E hr hrpos).hom) (TopPair.Hom.fst f) v).trans
    (congrArg (TopPair.Hom.fst f) (discSpherePairIsoOfRadius_hom_fst_apply F E hr hrpos v))

include hr hrpos in
private lemma mem_range_fst_rescaledAttach {z : Z} :
    z ∈ (range (TopPair.Hom.fst ((discSpherePairIsoOfRadius F E hr hrpos).hom ≫ f)) : Set Z) ↔
      z ∈ (range (TopPair.Hom.fst f) : Set Z) :=
  ⟨fun ⟨v, hv⟩ ↦ ⟨discBundleHomeomorphOfRadius F E hr hrpos v,
      (rescaledAttach_fst_apply hr hrpos (f := f) v).symm.trans hv⟩,
   fun ⟨w, hw⟩ ↦ ⟨(discBundleHomeomorphOfRadius F E hr hrpos).symm w,
      (rescaledAttach_fst_apply hr hrpos (f := f) _).trans <|
        (congrArg (TopPair.Hom.fst f)
          ((discBundleHomeomorphOfRadius F E hr hrpos).apply_symm_apply w)).trans hw⟩⟩

include hr hrpos hf in
private lemma isClosedEmbedding_rescaledAttach :
    IsClosedEmbedding
      (TopPair.Hom.fst ((discSpherePairIsoOfRadius F E hr hrpos).hom ≫ f)) := by
  have hfn : (⇑(TopPair.Hom.fst ((discSpherePairIsoOfRadius F E hr hrpos).hom ≫ f)) :
      discBundle F E → Z) =
      ⇑(TopPair.Hom.fst f) ∘ ⇑(discBundleHomeomorphOfRadius F E hr hrpos) :=
    funext (rescaledAttach_fst_apply hr hrpos)
  exact hfn ▸ hf.comp (discBundleHomeomorphOfRadius F E hr hrpos).isClosedEmbedding

include hr hrpos hfX in
private lemma mem_sphereBundle_of_rescaledAttach_mem (v : discBundle F E)
    (hv : TopPair.Hom.fst ((discSpherePairIsoOfRadius F E hr hrpos).hom ≫ f) v ∈ X) :
    (v : TotalSpace F E) ∈ sphereBundle F E := by
  have hv' : TopPair.Hom.fst f (discBundleHomeomorphOfRadius F E hr hrpos v) ∈ X :=
    rescaledAttach_fst_apply hr hrpos (f := f) v ▸ hv
  have hs := mem_sphereBundleOfRadius.1 (hfX _ hv')
  rw [coe_discBundleHomeomorphOfRadius_apply] at hs
  dsimp only [TotalSpace.mk'] at hs
  rw [norm_smul, Real.norm_of_nonneg (hrpos v.1.proj).le] at hs
  exact mem_sphereBundle.2 ((mul_right_eq_self₀.1 hs).resolve_right (hrpos v.1.proj).ne')

include hr hrpos hfcover in
private lemma cover_of_rescaledAttach :
    X ∪ range (TopPair.Hom.fst ((discSpherePairIsoOfRadius F E hr hrpos).hom ≫ f)) = univ :=
  eq_univ_of_forall fun z ↦
    (eq_univ_iff_forall.1 hfcover z).imp_right (mem_range_fst_rescaledAttach hr hrpos).2

include hnorm hr hrpos hf hX hfX hfcover in
/-- **Attaching a disc bundle of positive continuous radius induces isomorphisms on relative
homology.** Let `E → B` be a real vector bundle with continuous fibre norm and `r : B → ℝ` a
continuous positive radius. If `Z` is obtained from a closed subset `X` by attaching `D_r(E)`
along `S_r(E)` via `f : (D_r(E), S_r(E)) ⟶ (Z, X)`, then `f` induces isomorphisms
`Hₙ(D_r(E), S_r(E)) ≅ Hₙ(Z, X)` in every degree. -/
theorem isIso_singularHomologyMap_of_attach_discBundleOfRadius
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ) :
    IsIso (TopPair.singularHomologyMap f R n) := by
  let e := singularHomologyMapIso (discSpherePairIsoOfRadius F E hr hrpos) R n
  have hg : IsIso (e.hom ≫ TopPair.singularHomologyMap f R n) := by
    rw [singularHomologyMapIso_hom, ← TopPair.singularHomologyMap_comp]
    exact isIso_singularHomologyMap_of_attach_discBundle hnorm hX R n
      (isClosedEmbedding_rescaledAttach hr hrpos hf)
      (mem_sphereBundle_of_rescaledAttach_mem hr hrpos hfX)
      (cover_of_rescaledAttach hr hrpos hfcover)
  exact IsIso.of_isIso_comp_left e.hom _

include hnorm hr hrpos hf hX hfX hfcover in
/-- **Attaching a disc bundle of positive continuous radius induces isomorphisms on relative
cohomology.** Under the hypotheses of
`TauCeti.isIso_singularHomologyMap_of_attach_discBundleOfRadius`, `f` induces isomorphisms
`Hⁿ(Z, X) ≅ Hⁿ(D_r(E), S_r(E))` in every degree. -/
theorem isIso_singularCohomologyMap_of_attach_discBundleOfRadius
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n) := by
  let e := singularCohomologyMapIso (discSpherePairIsoOfRadius F E hr hrpos) R k M n
  have hg : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n ≫ e.hom) := by
    rw [singularCohomologyMapIso_hom, ← TopPair.singularCohomologyMap_comp]
    exact isIso_singularCohomologyMap_of_attach_discBundle hnorm hX R n k M
      (isClosedEmbedding_rescaledAttach hr hrpos hf)
      (mem_sphereBundle_of_rescaledAttach_mem hr hrpos hfX)
      (cover_of_rescaledAttach hr hrpos hfcover)
  exact IsIso.of_isIso_comp_right _ e.hom

/-- **Thom-pair homology of a single radius-`r` disc-bundle attachment**: `Hₙ(E, E₀) ≅ Hₙ(Z, X)`,
formed from the zig-zag `(E, E₀) ← (D_r(E), S_r(E)) → (Z, X)`. -/
def singularHomologyIsoThomPairOfAttachDiscBundleOfRadius
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ) :
    (thomPair F E).singularHomology R n ≅
      (TopPair.ofSubset (X := TopCat.of Z) X).singularHomology R n :=
  (@asIso _ _ _ _ (TopPair.singularHomologyMap
      (discSpherePairOfRadiusMap F E fun b ↦ (hrpos b).ne') R n)
    (isIso_singularHomologyMap_discSpherePairOfRadiusMap F E hnorm hr hrpos R n)).symm ≪≫
  @asIso _ _ _ _ (TopPair.singularHomologyMap f R n)
    (isIso_singularHomologyMap_of_attach_discBundleOfRadius hnorm hr hrpos hf hX hfX hfcover R n)

@[reassoc (attr := simp)]
theorem singularHomologyMap_discSpherePairOfRadiusMap_comp_isoThomPair_hom
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ) :
    TopPair.singularHomologyMap (discSpherePairOfRadiusMap F E fun b ↦ (hrpos b).ne') R n ≫
        (singularHomologyIsoThomPairOfAttachDiscBundleOfRadius
          hnorm hr hrpos hf hX hfX hfcover R n).hom =
      TopPair.singularHomologyMap f R n := by
  have := isIso_singularHomologyMap_discSpherePairOfRadiusMap F E hnorm hr hrpos R n
  have := isIso_singularHomologyMap_of_attach_discBundleOfRadius
    hnorm hr hrpos hf hX hfX hfcover R n
  simp [singularHomologyIsoThomPairOfAttachDiscBundleOfRadius]

@[reassoc (attr := simp)]
theorem singularHomologyMap_attach_comp_isoThomPairOfRadius_inv
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ) :
    TopPair.singularHomologyMap f R n ≫
        (singularHomologyIsoThomPairOfAttachDiscBundleOfRadius
          hnorm hr hrpos hf hX hfX hfcover R n).inv =
      TopPair.singularHomologyMap (discSpherePairOfRadiusMap F E fun b ↦ (hrpos b).ne') R n := by
  have := isIso_singularHomologyMap_discSpherePairOfRadiusMap F E hnorm hr hrpos R n
  have := isIso_singularHomologyMap_of_attach_discBundleOfRadius
    hnorm hr hrpos hf hX hfX hfcover R n
  simp [singularHomologyIsoThomPairOfAttachDiscBundleOfRadius]

/-- **Thom-pair cohomology of a single radius-`r` disc-bundle attachment**: `Hⁿ(Z, X) ≅ Hⁿ(E, E₀)`,
formed from the zig-zag `(E, E₀) ← (D_r(E), S_r(E)) → (Z, X)`. -/
def singularCohomologyIsoThomPairOfAttachDiscBundleOfRadius
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    (TopPair.ofSubset (X := TopCat.of Z) X).singularCohomology R k M n ≅
      (thomPair F E).singularCohomology R k M n :=
  @asIso _ _ _ _ (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n)
    (isIso_singularCohomologyMap_of_attach_discBundleOfRadius
      hnorm hr hrpos hf hX hfX hfcover R k M n) ≪≫
  (@asIso _ _ _ _ (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (discSpherePairOfRadiusMap F E fun b ↦ (hrpos b).ne') n)
    (isIso_singularCohomologyMap_discSpherePairOfRadiusMap F E hnorm hr hrpos R k M n)).symm

@[reassoc (attr := simp)]
theorem singularCohomologyIsoThomPairOfAttachDiscBundleOfRadius_hom_comp
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    (singularCohomologyIsoThomPairOfAttachDiscBundleOfRadius
        hnorm hr hrpos hf hX hfX hfcover R k M n).hom ≫
      TopPair.singularCohomologyMap
        (discSpherePairOfRadiusMap F E fun b ↦ (hrpos b).ne') n =
      TopPair.singularCohomologyMap f n := by
  have := isIso_singularCohomologyMap_discSpherePairOfRadiusMap F E hnorm hr hrpos R k M n
  have := isIso_singularCohomologyMap_of_attach_discBundleOfRadius
    hnorm hr hrpos hf hX hfX hfcover R k M n
  simp [singularCohomologyIsoThomPairOfAttachDiscBundleOfRadius]

@[reassoc (attr := simp)]
theorem singularCohomologyIsoThomPairOfAttachDiscBundleOfRadius_inv_comp
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    (singularCohomologyIsoThomPairOfAttachDiscBundleOfRadius
        hnorm hr hrpos hf hX hfX hfcover R k M n).inv ≫
      TopPair.singularCohomologyMap f n =
      TopPair.singularCohomologyMap
        (discSpherePairOfRadiusMap F E fun b ↦ (hrpos b).ne') n := by
  have := isIso_singularCohomologyMap_discSpherePairOfRadiusMap F E hnorm hr hrpos R k M n
  have := isIso_singularCohomologyMap_of_attach_discBundleOfRadius
    hnorm hr hrpos hf hX hfX hfcover R k M n
  simp [singularCohomologyIsoThomPairOfAttachDiscBundleOfRadius]

end Radius

section UnitRadius

variable (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)
  {f : discSpherePair F E ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
  (hf : IsClosedEmbedding (TopPair.Hom.fst f)) (hX : IsClosed X)
  (hfX : ∀ v : discBundle F E, TopPair.Hom.fst f v ∈ X → (v : TotalSpace F E) ∈ sphereBundle F E)
  (hfcover : X ∪ range (TopPair.Hom.fst f) = univ)

/-- **Thom-pair homology of a single unit disc-bundle attachment**: `Hₙ(E, E₀) ≅ Hₙ(Z, X)`, formed
from `(E, E₀) ← (D(E), S(E)) → (Z, X)`. -/
def singularHomologyIsoThomPairOfAttachDiscBundle
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ) :
    (thomPair F E).singularHomology R n ≅
      (TopPair.ofSubset (X := TopCat.of Z) X).singularHomology R n :=
  (@asIso _ _ _ _ (TopPair.singularHomologyMap (discSpherePairMap F E) R n)
    (isIso_singularHomologyMap_discSpherePairMap F E hnorm R n)).symm ≪≫
  @asIso _ _ _ _ (TopPair.singularHomologyMap f R n)
    (isIso_singularHomologyMap_of_attach_discBundle hnorm hX R n hf hfX hfcover)

@[reassoc (attr := simp)]
theorem singularHomologyMap_discSpherePairMap_comp_isoThomPair_hom
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ) :
    TopPair.singularHomologyMap (discSpherePairMap F E) R n ≫
        (singularHomologyIsoThomPairOfAttachDiscBundle hnorm hf hX hfX hfcover R n).hom =
      TopPair.singularHomologyMap f R n := by
  have := isIso_singularHomologyMap_discSpherePairMap F E hnorm R n
  have := isIso_singularHomologyMap_of_attach_discBundle hnorm hX R n hf hfX hfcover
  simp [singularHomologyIsoThomPairOfAttachDiscBundle]

@[reassoc (attr := simp)]
theorem singularHomologyMap_attach_comp_isoThomPair_inv
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ) :
    TopPair.singularHomologyMap f R n ≫
        (singularHomologyIsoThomPairOfAttachDiscBundle hnorm hf hX hfX hfcover R n).inv =
      TopPair.singularHomologyMap (discSpherePairMap F E) R n := by
  have := isIso_singularHomologyMap_discSpherePairMap F E hnorm R n
  have := isIso_singularHomologyMap_of_attach_discBundle hnorm hX R n hf hfX hfcover
  simp [singularHomologyIsoThomPairOfAttachDiscBundle]

/-- **Thom-pair cohomology of a single unit disc-bundle attachment**: `Hⁿ(Z, X) ≅ Hⁿ(E, E₀)`,
formed from `(E, E₀) ← (D(E), S(E)) → (Z, X)`. -/
def singularCohomologyIsoThomPairOfAttachDiscBundle
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    (TopPair.ofSubset (X := TopCat.of Z) X).singularCohomology R k M n ≅
      (thomPair F E).singularCohomology R k M n :=
  @asIso _ _ _ _ (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n)
    (isIso_singularCohomologyMap_of_attach_discBundle hnorm hX R n k M hf hfX hfcover) ≪≫
  (@asIso _ _ _ _ (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (discSpherePairMap F E) n)
    (isIso_singularCohomologyMap_discSpherePairMap F E hnorm R k M n)).symm

@[reassoc (attr := simp)]
theorem singularCohomologyIsoThomPairOfAttachDiscBundle_hom_comp
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    (singularCohomologyIsoThomPairOfAttachDiscBundle hnorm hf hX hfX hfcover R k M n).hom ≫
      TopPair.singularCohomologyMap (discSpherePairMap F E) n =
      TopPair.singularCohomologyMap f n := by
  have := isIso_singularCohomologyMap_discSpherePairMap F E hnorm R k M n
  have := isIso_singularCohomologyMap_of_attach_discBundle hnorm hX R n k M hf hfX hfcover
  simp [singularCohomologyIsoThomPairOfAttachDiscBundle]

@[reassoc (attr := simp)]
theorem singularCohomologyIsoThomPairOfAttachDiscBundle_inv_comp
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    (singularCohomologyIsoThomPairOfAttachDiscBundle hnorm hf hX hfX hfcover R k M n).inv ≫
      TopPair.singularCohomologyMap f n =
      TopPair.singularCohomologyMap (discSpherePairMap F E) n := by
  have := isIso_singularCohomologyMap_discSpherePairMap F E hnorm R k M n
  have := isIso_singularCohomologyMap_of_attach_discBundle hnorm hX R n k M hf hfX hfcover
  simp [singularCohomologyIsoThomPairOfAttachDiscBundle]

end UnitRadius

end SingleBundle

/-! ### Splitting relative homology and cohomology across a triple -/

section TripleSplitting

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- In a triple `T = (Z, X', X)`, if morphisms into `Hₙ(Z, X)` and `Hₙ₊₁(Z, X)` compose with
`H_*(Z, X) ⟶ H_*(Z, X')` to isomorphisms, then `B₀ ⊞ Hₙ(X', X) ⟶ Hₙ(Z, X)` is an isomorphism. -/
private theorem isIso_biprod_desc_triple_singularHomology (T : TopTriple.{w}) (R : C) (n : ℕ)
    {B₀ B₁ : C}
    (s₀ : B₀ ⟶ (TopTriple.totalPair.obj T).singularHomology R n)
    (s₁ : B₁ ⟶ (TopTriple.totalPair.obj T).singularHomology R (n + 1))
    (hs₀ : IsIso (s₀ ≫ TopPair.singularHomologyMap (TopTriple.totalToOuter.app T) R n))
    (hs₁ : IsIso (s₁ ≫ TopPair.singularHomologyMap (TopTriple.totalToOuter.app T) R (n + 1))) :
    IsIso (biprod.desc s₀ (TopPair.singularHomologyMap (TopTriple.innerToTotal.app T) R n)) := by
  let i₀ := TopPair.singularHomologyMap (TopTriple.innerToTotal.app T) R n
  let q₀ := TopPair.singularHomologyMap (TopTriple.totalToOuter.app T) R n
  let q₁ := TopPair.singularHomologyMap (TopTriple.totalToOuter.app T) R (n + 1)
  -- The section in degree `n + 1` forces the connecting map `Hₙ₊₁(Z, X') ⟶ Hₙ(X', X)` to vanish.
  have hδ : T.singularHomologyδ R (n + 1) n rfl = 0 := by
    calc T.singularHomologyδ R (n + 1) n rfl
        = (inv (s₁ ≫ q₁) ≫ (s₁ ≫ q₁)) ≫ T.singularHomologyδ R (n + 1) n rfl := by
            rw [IsIso.inv_hom_id, Category.id_comp]
      _ = inv (s₁ ≫ q₁) ≫ s₁ ≫ (q₁ ≫ T.singularHomologyδ R (n + 1) n rfl) := by
            simp only [Category.assoc]
      _ = 0 := by rw [T.comp_singularHomologyδ R (n + 1) n rfl, comp_zero, comp_zero]
  have hmono : Mono i₀ := (T.singularHomology_exact_inner R (n + 1) n rfl).mono_g hδ
  let S := ShortComplex.mk i₀ q₀ (T.singularHomologyMap_innerToTotal_comp_totalToOuter R n)
  let s' : S.X₃ ⟶ S.X₂ := inv (s₀ ≫ q₀) ≫ s₀
  have hs' : s' ≫ S.g = 𝟙 _ := by
    dsimp only [S, s']
    rw [Category.assoc]
    exact IsIso.inv_hom_id (s₀ ≫ q₀)
  let spl := ShortComplex.Splitting.ofExactOfSection S (T.singularHomology_exact_total R n)
    s' hs' hmono
  have hspl : IsIso (biprod.desc i₀ s') := spl.isoBinaryBiproduct.isIso_inv
  have hfac : (biprod.braiding' B₀ S.X₁).hom ≫
      (biprod.mapIso (Iso.refl _) (asIso (s₀ ≫ q₀))).hom ≫ biprod.desc i₀ s' =
      biprod.desc s₀ i₀ :=
    biprod.hom_ext' _ _ (by simp [s']) (by simp)
  rw [← hfac]
  infer_instance

private abbrev tripleSingularCochainShortComplex (T : TopTriple.{w}) (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) :
    ShortComplex (CochainComplex (ModuleCat.{v} k) ℕ) :=
  ShortComplex.mk
    (TopPair.singularCochainComplexMap (R := R) (k := k) (M := M) (TopTriple.totalToOuter.app T))
    (TopPair.singularCochainComplexMap (R := R) (k := k) (M := M) (TopTriple.innerToTotal.app T))
    (((T.singularChainComplexShortComplex R).op.map
      (TauCeti.ChainComplex.linearYonedaFunctor k M)).zero)

/-- The relative singular cochain sequence `0 ⟶ C*(Z, X') ⟶ C*(Z, X) ⟶ C*(X', X) ⟶ 0` of a triple
is short exact because the relative chain sequence is degreewise split. -/
private theorem shortExact_tripleSingularCochainShortComplex (T : TopTriple.{w}) (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) :
    (tripleSingularCochainShortComplex T R k M).ShortExact := by
  have : ∀ i, IsSplitMono ((T.singularChainComplexShortComplex R).f.f i) := fun i ↦ by
    let P := TopPair.toSSetPair.obj (TopTriple.outerPair.obj T)
    have hsec : ((SSetPair.chainComplexXSplitting R P i).s ≫
          ((TopTriple.totalPair.obj T).singularChainComplexπ R).f i) ≫
        (TopPair.singularChainComplexMap (TopTriple.totalToOuter.app T) R).f i = 𝟙 _ :=
      (Category.assoc _ _ _).trans <|
        (congrArg ((SSetPair.chainComplexXSplitting R P i).s ≫ ·)
          ((HomologicalComplex.comp_f _ _ i).symm.trans
            (congrArg (fun φ ↦ φ.f i) (T.singularChainComplexπ_comp_totalToOuter R)))).trans
          (SSetPair.chainComplexXSplitting R P i).s_g
    have : IsSplitEpi ((T.singularChainComplexShortComplex R).g.f i) :=
      IsSplitEpi.mk' ⟨_, hsec⟩
    exact ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
      (T.shortExact_singularChainComplexShortComplex R) i).isSplitMono_f_iff_isSplitEpi_g.2 this
  exact TauCeti.ChainComplex.shortExact_map_linearYonedaFunctor k M
    (T.shortExact_singularChainComplexShortComplex R)

/-- Dual to `isIso_biprod_desc_triple_singularHomology`: in cohomology, if morphisms out of
`Hⁿ(Z, X)` and `Hⁿ⁺¹(Z, X)` compose with `H*(Z, X') ⟶ H*(Z, X)` to isomorphisms, then
`Hⁿ(Z, X) ⟶ B⁰ ⊞ Hⁿ(X', X)` is an isomorphism. -/
private theorem isIso_biprod_lift_triple_singularCohomology (T : TopTriple.{w}) (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) {B₀ B₁ : ModuleCat.{v} k}
    (p₀ : (TopTriple.totalPair.obj T).singularCohomology R k M n ⟶ B₀)
    (p₁ : (TopTriple.totalPair.obj T).singularCohomology R k M (n + 1) ⟶ B₁)
    (hp₀ : IsIso (TopPair.singularCohomologyMap (TopTriple.totalToOuter.app T) n ≫ p₀))
    (hp₁ : IsIso (TopPair.singularCohomologyMap (TopTriple.totalToOuter.app T) (n + 1) ≫ p₁)) :
    IsIso (biprod.lift p₀
      (TopPair.singularCohomologyMap (TopTriple.innerToTotal.app T) n)) := by
  have hCS := shortExact_tripleSingularCochainShortComplex T R k M
  let q₀ := TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
    (TopTriple.totalToOuter.app T) n
  let q₁ := TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
    (TopTriple.totalToOuter.app T) (n + 1)
  let i₀ := TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
    (TopTriple.innerToTotal.app T) n
  -- The retraction in degree `n + 1` forces `Hⁿ(X', X) ⟶ Hⁿ⁺¹(Z, X')` to vanish.
  have hδ : hCS.δ n (n + 1) (by simp) = 0 := by
    have hd : hCS.δ n (n + 1) (by simp) ≫ q₁ = 0 := hCS.δ_comp n (n + 1) (by simp)
    calc hCS.δ n (n + 1) (by simp)
        = hCS.δ n (n + 1) (by simp) ≫ ((q₁ ≫ p₁) ≫ inv (q₁ ≫ p₁)) := by
            rw [IsIso.hom_inv_id, Category.comp_id]
      _ = (hCS.δ n (n + 1) (by simp) ≫ q₁) ≫ p₁ ≫ inv (q₁ ≫ p₁) := by
            rw [Category.assoc, Category.assoc]
      _ = 0 := by rw [hd, zero_comp]
  have hepi : Epi i₀ := (hCS.homology_exact₃ n (n + 1) (by simp)).epi_f hδ
  let r' : (TopTriple.totalPair.obj T).singularCohomology R k M n ⟶
      (TopTriple.outerPair.obj T).singularCohomology R k M n := p₀ ≫ inv (q₀ ≫ p₀)
  have hr' : q₀ ≫ r' = 𝟙 _ := by
    dsimp only [r']
    rw [← Category.assoc]
    exact IsIso.hom_inv_id (q₀ ≫ p₀)
  let spl := ShortComplex.Splitting.ofExactOfRetraction _ (hCS.homology_exact₂ n) r' hr' hepi
  have hspl : IsIso (biprod.lift r' i₀) := spl.isoBinaryBiproduct.isIso_hom
  have hfac : biprod.lift r' i₀ ≫ (biprod.mapIso (asIso (q₀ ≫ p₀)) (Iso.refl _)).hom =
      biprod.lift p₀ i₀ :=
    biprod.hom_ext _ _ (by simp [r', biprod.lift_fst_assoc]) (by simp)
  rw [← hfac]
  infer_instance

private theorem isZero_singularCohomology_ofSubset_of_eq_univ
    {Z : Type w} [TopologicalSpace Z] {X : Set Z} (hX : X = univ) (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    IsZero ((TopPair.ofSubset (X := TopCat.of Z) X).singularCohomology R k M n) := by
  have hiso : IsIso (TopPair.ofSubset (X := TopCat.of Z) X).map :=
    ⟨TopCat.ofHom ⟨fun z ↦ ⟨z, hX.symm ▸ mem_univ z⟩, by fun_prop⟩, rfl, rfl⟩
  let S := (TopPair.ofSubset (X := TopCat.of Z) X).singularCochainComplexShortComplex R k M
  have hS := (TopPair.ofSubset (X := TopCat.of Z) X).shortExact_singularCochainComplexShortComplex
    R k M
  have : IsIso S.g := by
    rw [TopPair.singularCochainComplexShortComplex_g_eq]
    exact ⟨TopCat.singularCochainComplexMap (inv (TopPair.ofSubset (X := TopCat.of Z) X).map),
      by rw [← TopCat.singularCochainComplexMap_comp, IsIso.inv_hom_id,
        TopCat.singularCochainComplexMap_id],
      by rw [← TopCat.singularCochainComplexMap_comp, IsIso.hom_inv_id,
        TopCat.singularCochainComplexMap_id]⟩
  have hf0 : S.f = 0 := (cancel_mono S.g).1 (S.zero.trans zero_comp.symm)
  have := hS.mono_f
  have hid : 𝟙 S.X₁ = 0 := (cancel_mono S.f).1 (by rw [Category.id_comp, hf0, zero_comp])
  exact (HomologicalComplex.homologyFunctor _ _ n).map_isZero ((IsZero.iff_id_eq_zero _).2 hid)

end TripleSplitting

/-! ### Attaching a finite family of disc bundles -/

section FiniteFamily

private lemma biproductOptionIso_hom_comp_biprod_desc
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
    [HasFiniteBiproducts C] {α : Type*} [Finite α] (M : Option α → C) {W Y : C}
    (hsomeIso : (⨁ fun j ↦ M (some j)) ≅ W)
    (g₀ : M none ⟶ Y) (g₁ : W ⟶ Y) (φ : ∀ i, M i ⟶ Y) (h0 : g₀ = φ none)
    (hs : ∀ j, biproduct.ι (fun j ↦ M (some j)) j ≫ hsomeIso.hom ≫ g₁ = φ (some j)) :
    (biproductOptionIso M).hom ≫ (biprod.mapIso (Iso.refl (M none)) hsomeIso).hom ≫
      biprod.desc g₀ g₁ = biproduct.desc φ := by
  rw [← Iso.eq_inv_comp]
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [biprod.mapIso_hom, Iso.refl_hom, biprod.inl_map_assoc, Category.id_comp,
      biprod.inl_desc, ← Category.assoc, biprod_inl_biproductOptionIso_inv, biproduct.ι_desc, h0]
  · rw [biprod.mapIso_hom, biprod.inr_map_assoc, biprod.inr_desc]
    refine biproduct.hom_ext' _ _ fun j ↦ ?_
    calc biproduct.ι (fun j ↦ M (some j)) j ≫ hsomeIso.hom ≫ g₁
        = φ (some j) := hs j
      _ = biproduct.ι M (some j) ≫ biproduct.desc φ := (biproduct.ι_desc φ (some j)).symm
      _ = (biproduct.ι (fun j ↦ M (some j)) j ≫ biprod.inr ≫ (biproductOptionIso M).inv) ≫
            biproduct.desc φ := by
          rw [biproduct_ι_biprod_inr_biproductOptionIso_inv]
      _ = biproduct.ι (fun j ↦ M (some j)) j ≫ biprod.inr ≫ (biproductOptionIso M).inv ≫
            biproduct.desc φ := by
          simp only [Category.assoc]

private lemma biprod_lift_comp_biproductOptionIso_inv
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
    [HasFiniteBiproducts C] {α : Type*} [Finite α] (N : Option α → C) {X W : C}
    (hsomeIso : W ≅ ⨁ fun j ↦ N (some j))
    (p₀ : X ⟶ N none) (p₁ : X ⟶ W) (ψ : ∀ i, X ⟶ N i) (h0 : p₀ = ψ none)
    (hs : ∀ j, p₁ ≫ hsomeIso.hom ≫ biproduct.π (fun j ↦ N (some j)) j = ψ (some j)) :
    biprod.lift p₀ p₁ ≫ (biprod.mapIso (Iso.refl (N none)) hsomeIso).hom ≫
      (biproductOptionIso N).inv = biproduct.lift ψ := by
  rw [← Category.assoc, Iso.comp_inv_eq]
  refine biprod.hom_ext _ _ ?_ (biproduct.hom_ext _ _ fun j ↦ ?_)
  · simp only [Category.assoc, biprod.mapIso_hom, Iso.refl_hom, biprod.map_fst, Category.comp_id,
      biprod.lift_fst, biproductOptionIso_hom_fst, biproduct.lift_π, h0]
  · calc ((biprod.lift p₀ p₁ ≫ (biprod.mapIso (Iso.refl (N none)) hsomeIso).hom) ≫
          biprod.snd) ≫ biproduct.π (fun j ↦ N (some j)) j
        = p₁ ≫ hsomeIso.hom ≫ biproduct.π (fun j ↦ N (some j)) j := by
          simp only [Category.assoc, biprod.mapIso_hom, biprod.map_snd_assoc,
            biprod.lift_snd_assoc]
      _ = ψ (some j) := hs j
      _ = biproduct.lift ψ ≫ biproduct.π N (some j) := (biproduct.lift_π ψ (some j)).symm
      _ = biproduct.lift ψ ≫ (biproductOptionIso N).hom ≫ biprod.snd ≫
            biproduct.π (fun j ↦ N (some j)) j := by
          rw [biproductOptionIso_hom_snd_π]
      _ = ((biproduct.lift ψ ≫ (biproductOptionIso N).hom) ≫ biprod.snd) ≫
            biproduct.π (fun j ↦ N (some j)) j := by
          simp only [Category.assoc]

section OptionStep

variable {α : Type*}
  {B : Option α → Type w} {F : Option α → Type uF} {E : ∀ i, B i → Type w}
  [∀ i b, NormedAddCommGroup (E i b)] [∀ i, TopologicalSpace (TotalSpace (F i) (E i))]
  {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  (f : ∀ i, discSpherePair (F i) (E i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X)

/-- In the `Option α` induction step, `X'` adds the disc bundles indexed by `some j` to `X`. -/
private def intermediateSubset : Set Z :=
  X ∪ ⋃ j : α, range (TopPair.Hom.fst (f (some j)))

private lemma subset_intermediateSubset : X ⊆ intermediateSubset f :=
  subset_union_left

private lemma isClosed_intermediateSubset [Finite α]
    (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))) (hX : IsClosed X) :
    IsClosed (intermediateSubset f) :=
  hX.union (isClosed_iUnion_of_finite fun j ↦ (hf (some j)).isClosed_range)

/-- Corestriction of `f (some j)` to `(X', X)` in the `Option α` induction step. -/
private def restrictAttachSome (j : α) :
    discSpherePair (F (some j)) (E (some j)) ⟶
      TopPair.ofSubset (X := TopCat.of (intermediateSubset f)) (Subtype.val ⁻¹' X) :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun v ↦ ⟨TopPair.Hom.fst (f (some j)) v, Or.inr (mem_iUnion.2 ⟨j, v, rfl⟩)⟩,
      Continuous.subtype_mk (TopPair.Hom.fst (f (some j))).hom.continuous _⟩)
    (TopCat.ofHom ⟨fun v ↦ ⟨⟨(TopPair.Hom.snd (f (some j)) v).1,
        Or.inl (TopPair.Hom.snd (f (some j)) v).2⟩, (TopPair.Hom.snd (f (some j)) v).2⟩,
      Continuous.subtype_mk (Continuous.subtype_mk
        (continuous_subtype_val.comp (TopPair.Hom.snd (f (some j))).hom.continuous) _) _⟩)
    (TopCat.ext fun v ↦ Subtype.ext (TopPair.Hom.w_apply (f (some j)) v))

private def innerPairIso :
    TopPair.ofSubset (X := TopCat.of (intermediateSubset f)) (Subtype.val ⁻¹' X) ≅
      TopTriple.innerPair.obj
        (TopTriple.ofSubset (X := TopCat.of Z) (subset_intermediateSubset f)) :=
  TopPair.ofSubsetPreimageValIso (X := TopCat.of Z) (subset_intermediateSubset f)

private lemma restrictAttachSome_comp_innerToTotal (j : α) :
    restrictAttachSome f j ≫ (innerPairIso f).hom ≫
        TopTriple.innerToTotal.app
          (TopTriple.ofSubset (X := TopCat.of Z) (subset_intermediateSubset f)) =
      (f (some j) : _ ⟶ TopTriple.totalPair.obj
        (TopTriple.ofSubset (X := TopCat.of Z) (subset_intermediateSubset f))) :=
  TopPair.hom_ext_of_fst _ <| TopCat.ext fun v ↦
    (ConcreteCategory.comp_apply _ _ v).trans <|
      (ConcreteCategory.comp_apply _ _ _).trans <|
        (congrArg (TopPair.Hom.fst (TopTriple.innerToTotal.app _))
          (TopPair.ofSubsetPreimageValIso_hom_fst_apply _)).trans rfl

private lemma isClosedEmbedding_restrictAttachSome [Finite α]
    (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))) (hX : IsClosed X) (j : α) :
    IsClosedEmbedding (TopPair.Hom.fst (restrictAttachSome f j)) := by
  have hval := (isClosed_intermediateSubset f hf hX).isClosedEmbedding_subtypeVal
  refine (hval.of_comp_iff (f := TopPair.Hom.fst (restrictAttachSome f j))).1 ?_
  exact hf (some j)

private lemma mem_sphereBundle_restrictAttachSome
    (hfX : ∀ i (v : discBundle (F i) (E i)),
      TopPair.Hom.fst (f i) v ∈ X → (v : TotalSpace (F i) (E i)) ∈ sphereBundle (F i) (E i))
    (j : α) (v : discBundle (F (some j)) (E (some j)))
    (hv : TopPair.Hom.fst (restrictAttachSome f j) v ∈ (Subtype.val ⁻¹' X : Set _)) :
    (v : TotalSpace (F (some j)) (E (some j))) ∈ sphereBundle (F (some j)) (E (some j)) :=
  hfX (some j) v hv

private lemma pairwise_disjoint_restrictAttachSome
    (hdisj : Pairwise fun i j ↦
      Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X)) :
    Pairwise fun j₁ j₂ ↦
      Disjoint (range (TopPair.Hom.fst (restrictAttachSome f j₁)) \ Subtype.val ⁻¹' X)
        (range (TopPair.Hom.fst (restrictAttachSome f j₂)) \ Subtype.val ⁻¹' X) := by
  intro j₁ j₂ hj
  refine disjoint_left.2 ?_
  rintro ⟨z, hz⟩ ⟨⟨v, hv⟩, hzX⟩ ⟨⟨w, hw⟩, -⟩
  have hv' : TopPair.Hom.fst (f (some j₁)) v = z := congrArg Subtype.val hv
  have hw' : TopPair.Hom.fst (f (some j₂)) w = z := congrArg Subtype.val hw
  exact disjoint_left.1 (hdisj ((Option.some_injective α).ne hj))
    ⟨⟨v, hv'⟩, hzX⟩ ⟨⟨w, hw'⟩, hzX⟩

private lemma cover_restrictAttachSome :
    (Subtype.val ⁻¹' X : Set (intermediateSubset f)) ∪
      ⋃ j : α, range (TopPair.Hom.fst (restrictAttachSome f j)) = univ := by
  refine eq_univ_of_forall fun ⟨z, hz⟩ ↦ ?_
  rcases hz with hzX | hzU
  · exact Or.inl hzX
  · obtain ⟨j, v, rfl⟩ := mem_iUnion.1 hzU
    exact Or.inr (mem_iUnion.2 ⟨j, v, rfl⟩)

private lemma mem_sphereBundle_attachNone
    (hfX : ∀ i (v : discBundle (F i) (E i)),
      TopPair.Hom.fst (f i) v ∈ X → (v : TotalSpace (F i) (E i)) ∈ sphereBundle (F i) (E i))
    (hdisj : Pairwise fun i j ↦
      Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X))
    (v : discBundle (F none) (E none))
    (hv : TopPair.Hom.fst ((f none : _ ⟶ TopTriple.totalPair.obj
        (TopTriple.ofSubset (X := TopCat.of Z) (subset_intermediateSubset f))) ≫
      TopTriple.totalToOuter.app
        (TopTriple.ofSubset (X := TopCat.of Z) (subset_intermediateSubset f))) v ∈
          intermediateSubset f) :
    (v : TotalSpace (F none) (E none)) ∈ sphereBundle (F none) (E none) := by
  have hv' : TopPair.Hom.fst (f none) v ∈ intermediateSubset f := hv
  rcases hv' with hvX | hvU
  · exact hfX none v hvX
  · obtain ⟨j, w, hw⟩ := mem_iUnion.1 hvU
    refine hfX none v (by_contra fun hnX ↦ ?_)
    exact disjoint_left.1 (hdisj (Option.some_ne_none j).symm) ⟨⟨v, rfl⟩, hnX⟩ ⟨⟨w, hw⟩, hnX⟩

private lemma cover_attachNone
    (hfcover : X ∪ ⋃ i : Option α, range (TopPair.Hom.fst (f i)) = univ) :
    intermediateSubset f ∪
      range (TopPair.Hom.fst ((f none : _ ⟶ TopTriple.totalPair.obj
          (TopTriple.ofSubset (X := TopCat.of Z) (subset_intermediateSubset f))) ≫
        TopTriple.totalToOuter.app
          (TopTriple.ofSubset (X := TopCat.of Z) (subset_intermediateSubset f)))) = univ := by
  refine eq_univ_of_forall fun z ↦ ?_
  rcases eq_univ_iff_forall.1 hfcover z with hzX | hzU
  · exact Or.inl (Or.inl hzX)
  · obtain ⟨i, v, rfl⟩ := mem_iUnion.1 hzU
    cases i with
    | none => exact Or.inr ⟨v, rfl⟩
    | some j => exact Or.inl (Or.inr (mem_iUnion.2 ⟨j, v, rfl⟩))

private theorem isIso_biproductDesc_option [Finite α]
    [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    [∀ i b, NormedSpace ℝ (E i b)] [∀ i, FiberBundle (F i) (E i)]
    [∀ i, VectorBundle ℝ (F i) (E i)]
    (hnorm : ∀ i, Continuous fun v : TotalSpace (F i) (E i) ↦ ‖v.2‖)
    {f : ∀ i, discSpherePair (F i) (E i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
    (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))) (hX : IsClosed X)
    (hfX : ∀ i (v : discBundle (F i) (E i)),
      TopPair.Hom.fst (f i) v ∈ X → (v : TotalSpace (F i) (E i)) ∈ sphereBundle (F i) (E i))
    (hdisj : Pairwise fun i j ↦
      Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X))
    (hfcover : X ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] [HasFiniteBiproducts C]
    (R : C) (n : ℕ)
    (hsome0 : IsIso (biproduct.desc fun j : α ↦
      TopPair.singularHomologyMap (restrictAttachSome f j) R n)) :
    IsIso (biproduct.desc fun i ↦ TopPair.singularHomologyMap (f i) R n) := by
  let T := TopTriple.ofSubset (X := TopCat.of Z) (subset_intermediateSubset f)
  let f' : ∀ i, discSpherePair (F i) (E i) ⟶ TopTriple.totalPair.obj T := f
  have hnone : ∀ m, IsIso (TopPair.singularHomologyMap (f' none) R m ≫
      TopPair.singularHomologyMap (TopTriple.totalToOuter.app T) R m) := fun m ↦ by
    rw [← TopPair.singularHomologyMap_comp (f' none) R (TopTriple.totalToOuter.app T) m]
    exact isIso_singularHomologyMap_of_attach_discBundle (hnorm none)
      (isClosed_intermediateSubset f hf hX) R m (hf none)
      (mem_sphereBundle_attachNone f hfX hdisj) (cover_attachNone f hfcover)
  have hsplit := isIso_biprod_desc_triple_singularHomology T R n
    (TopPair.singularHomologyMap (f' none) R n)
    (TopPair.singularHomologyMap (f' none) R (n + 1)) (hnone n) (hnone (n + 1))
  let hsomeIso :=
    asIso (biproduct.desc fun j ↦ TopPair.singularHomologyMap (restrictAttachSome f j) R n) ≪≫
      singularHomologyMapIso (innerPairIso f) R n
  have hfac := biproductOptionIso_hom_comp_biprod_desc
    (fun i ↦ (discSpherePair (F i) (E i)).singularHomology R n) hsomeIso
    (TopPair.singularHomologyMap (f' none) R n)
    (TopPair.singularHomologyMap (TopTriple.innerToTotal.app T) R n)
    (fun i ↦ TopPair.singularHomologyMap (f' i) R n) rfl fun j ↦ by
      rw [Iso.trans_hom, asIso_hom, singularHomologyMapIso_hom, Category.assoc,
        biproduct.ι_desc_assoc, ← TopPair.singularHomologyMap_comp,
        ← TopPair.singularHomologyMap_comp, restrictAttachSome_comp_innerToTotal]
  have hiso : IsIso (biproduct.desc fun i ↦ TopPair.singularHomologyMap (f' i) R n) := by
    rw [← hfac]; infer_instance
  exact hiso

private theorem isIso_biproductLift_option [Finite α]
    [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    [∀ i b, NormedSpace ℝ (E i b)] [∀ i, FiberBundle (F i) (E i)]
    [∀ i, VectorBundle ℝ (F i) (E i)]
    (hnorm : ∀ i, Continuous fun v : TotalSpace (F i) (E i) ↦ ‖v.2‖)
    {f : ∀ i, discSpherePair (F i) (E i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
    (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))) (hX : IsClosed X)
    (hfX : ∀ i (v : discBundle (F i) (E i)),
      TopPair.Hom.fst (f i) v ∈ X → (v : TotalSpace (F i) (E i)) ∈ sphereBundle (F i) (E i))
    (hdisj : Pairwise fun i j ↦
      Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X))
    (hfcover : X ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ)
    (hsome0 : IsIso (biproduct.lift fun j : α ↦
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (restrictAttachSome f j) n)) :
    IsIso (biproduct.lift fun i ↦
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (f i) n) := by
  let T := TopTriple.ofSubset (X := TopCat.of Z) (subset_intermediateSubset f)
  let f' : ∀ i, discSpherePair (F i) (E i) ⟶ TopTriple.totalPair.obj T := f
  have hnone : ∀ m, IsIso
      (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
          (TopTriple.totalToOuter.app T) m ≫
        TopPair.singularCohomologyMap (f' none) m) := fun m ↦ by
    rw [← TopPair.singularCohomologyMap_comp (R := R) (k := k) (M := M)
      (f' none) (TopTriple.totalToOuter.app T) m]
    exact isIso_singularCohomologyMap_of_attach_discBundle (hnorm none)
      (isClosed_intermediateSubset f hf hX) R m k M (hf none)
      (mem_sphereBundle_attachNone f hfX hdisj) (cover_attachNone f hfcover)
  have hsplit := isIso_biprod_lift_triple_singularCohomology T R k M n
    (TopPair.singularCohomologyMap (f' none) n)
    (TopPair.singularCohomologyMap (f' none) (n + 1)) (hnone n) (hnone (n + 1))
  let hsomeIso :=
    singularCohomologyMapIso (innerPairIso f) R k M n ≪≫
      asIso (biproduct.lift fun j ↦
        TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (restrictAttachSome f j) n)
  have hfac := biprod_lift_comp_biproductOptionIso_inv
    (fun i ↦ (discSpherePair (F i) (E i)).singularCohomology R k M n) hsomeIso
    (TopPair.singularCohomologyMap (f' none) n)
    (TopPair.singularCohomologyMap (TopTriple.innerToTotal.app T) n)
    (fun i ↦ TopPair.singularCohomologyMap (f' i) n) rfl fun j ↦ by
      rw [Iso.trans_hom, singularCohomologyMapIso_hom, asIso_hom, Category.assoc,
        biproduct.lift_π, ← TopPair.singularCohomologyMap_comp,
        ← TopPair.singularCohomologyMap_comp, Category.assoc, restrictAttachSome_comp_innerToTotal]
  have hiso : IsIso (biproduct.lift fun i ↦
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (f' i) n) := by
    rw [← hfac]; infer_instance
  exact hiso

end OptionStep

section UnitRadius

private theorem isIso_biproductDesc_of_equiv {α β : Type*} [Finite α] [Finite β] (e : α ≃ β)
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasFiniteBiproducts C]
    {M : β → C} {Y : C} {φ : ∀ b, M b ⟶ Y}
    (h : IsIso (biproduct.desc fun a ↦ φ (e a))) :
    IsIso (biproduct.desc φ) := by
  let wIso : (⨁ fun a ↦ M (e a)) ≅ ⨁ M := biproduct.whiskerEquiv e fun _ ↦ Iso.refl _
  have hfac : wIso.hom ≫ biproduct.desc φ = biproduct.desc fun a ↦ φ (e a) :=
    biproduct.hom_ext' _ _ fun a ↦ by simp [wIso]
  have : IsIso (wIso.hom ≫ biproduct.desc φ) := by rw [hfac]; exact h
  exact IsIso.of_isIso_comp_left wIso.hom _

private theorem isIso_biproductLift_of_equiv {α β : Type*} [Finite α] [Finite β] (e : α ≃ β)
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasFiniteBiproducts C]
    {X : C} {M : β → C} {ψ : ∀ b, X ⟶ M b}
    (h : IsIso (biproduct.lift fun a ↦ ψ (e a))) :
    IsIso (biproduct.lift ψ) := by
  let wIso : ⨁ M ≅ ⨁ fun a ↦ M (e a) :=
    biproduct.whiskerEquiv e.symm fun b ↦ eqToIso (congrArg M (e.apply_symm_apply b))
  have hfac : biproduct.lift (fun a ↦ ψ (e a)) ≫ wIso.inv = biproduct.lift ψ :=
    biproduct.hom_ext _ _ fun b ↦ by
      obtain ⟨a, rfl⟩ := e.surjective b
      rw [Category.assoc, biproduct.whiskerEquiv_inv_eq_lift]
      simp
  have : IsIso (biproduct.lift (fun a ↦ ψ (e a)) ≫ wIso.inv) := inferInstance
  rwa [hfac] at this

private lemma cover_comp_equiv {α β : Type*} (e : α ≃ β)
    {Z : Type w} [TopologicalSpace Z] {X : Set Z} {P : β → TopPair.{w}}
    {f : ∀ b, P b ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
    (h : X ∪ ⋃ b, range (TopPair.Hom.fst (f b)) = univ) :
    X ∪ ⋃ a, range (TopPair.Hom.fst (f (e a))) = univ :=
  eq_univ_of_forall fun z ↦ (eq_univ_iff_forall.1 h z).imp_right fun hz ↦ by
    obtain ⟨b, hb⟩ := mem_iUnion.1 hz
    obtain ⟨a, rfl⟩ := e.surjective b
    exact mem_iUnion.2 ⟨a, hb⟩

private theorem isIso_biproductDesc_fin
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] [HasFiniteBiproducts C]
    (R : C) (n : ℕ) :
    ∀ (m : ℕ) {Z : Type w} [TopologicalSpace Z] {X : Set Z}
      {B : Fin m → Type w} {F : Fin m → Type uF} {E : ∀ i, B i → Type w}
      [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
      [∀ i b, NormedAddCommGroup (E i b)] [∀ i b, NormedSpace ℝ (E i b)]
      [∀ i, TopologicalSpace (TotalSpace (F i) (E i))] [∀ i, FiberBundle (F i) (E i)]
      [∀ i, VectorBundle ℝ (F i) (E i)]
      (_ : ∀ i, Continuous fun v : TotalSpace (F i) (E i) ↦ ‖v.2‖)
      {f : ∀ i, discSpherePair (F i) (E i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
      (_ : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))) (_ : IsClosed X)
      (_ : ∀ i (v : discBundle (F i) (E i)),
        TopPair.Hom.fst (f i) v ∈ X → (v : TotalSpace (F i) (E i)) ∈ sphereBundle (F i) (E i))
      (_ : Pairwise fun i j ↦
        Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X))
      (_ : X ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ),
      IsIso (biproduct.desc fun i ↦ TopPair.singularHomologyMap (f i) R n)
  | 0, Z, _, X, _, _, _, _, _, _, _, _, _, _, _, _, f, _, _, _, _, hfcover => by
    have hXuniv : X = univ := by simpa using hfcover
    have hsurj : Function.Surjective (TopPair.ofSubset (X := TopCat.of Z) X).map :=
      fun z ↦ ⟨⟨z, hXuniv.symm ▸ mem_univ z⟩, rfl⟩
    have htgt := TopPair.isZero_singularHomology_of_surjective_map
      (TopPair.ofSubset (X := TopCat.of Z) X) R hsurj n
    exact isIso_of_source_target_iso_zero _ (isZero_biproduct_of_isEmpty _).isoZero htgt.isoZero
  | m + 1, Z, _, X, B, F, E, _, _, _, _, _, _, _, _, hnorm, f, hf, hX, hfX, hdisj, hfcover => by
    let e := (finSuccEquiv m).symm
    refine isIso_biproductDesc_of_equiv e ?_
    let f' := fun i : Option (Fin m) ↦ f (e i)
    have hf' : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f' i)) := fun i ↦ hf (e i)
    have hfX' : ∀ i (v : discBundle (F (e i)) (E (e i))),
        TopPair.Hom.fst (f' i) v ∈ X →
          (v : TotalSpace (F (e i)) (E (e i))) ∈ sphereBundle (F (e i)) (E (e i)) :=
      fun i ↦ hfX (e i)
    have hdisj' : Pairwise fun i j ↦
        Disjoint (range (TopPair.Hom.fst (f' i)) \ X) (range (TopPair.Hom.fst (f' j)) \ X) :=
      fun _ _ hne ↦ hdisj (e.injective.ne hne)
    exact isIso_biproductDesc_option (fun i ↦ hnorm (e i)) hf' hX hfX' hdisj'
      (cover_comp_equiv e hfcover) R n
      (isIso_biproductDesc_fin R n m (fun j ↦ hnorm (e (some j)))
        (isClosedEmbedding_restrictAttachSome f' hf' hX) (hX.preimage continuous_subtype_val)
        (mem_sphereBundle_restrictAttachSome f' hfX')
        (pairwise_disjoint_restrictAttachSome f' hdisj') (cover_restrictAttachSome f'))

private theorem isIso_biproductLift_fin
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    ∀ (m : ℕ) {Z : Type w} [TopologicalSpace Z] {X : Set Z}
      {B : Fin m → Type w} {F : Fin m → Type uF} {E : ∀ i, B i → Type w}
      [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
      [∀ i b, NormedAddCommGroup (E i b)] [∀ i b, NormedSpace ℝ (E i b)]
      [∀ i, TopologicalSpace (TotalSpace (F i) (E i))] [∀ i, FiberBundle (F i) (E i)]
      [∀ i, VectorBundle ℝ (F i) (E i)]
      (_ : ∀ i, Continuous fun v : TotalSpace (F i) (E i) ↦ ‖v.2‖)
      {f : ∀ i, discSpherePair (F i) (E i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
      (_ : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))) (_ : IsClosed X)
      (_ : ∀ i (v : discBundle (F i) (E i)),
        TopPair.Hom.fst (f i) v ∈ X → (v : TotalSpace (F i) (E i)) ∈ sphereBundle (F i) (E i))
      (_ : Pairwise fun i j ↦
        Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X))
      (_ : X ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ),
      IsIso (biproduct.lift fun i ↦
        TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (f i) n)
  | 0, Z, _, X, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hfcover => by
    have hXuniv : X = univ := by simpa using hfcover
    have hsrc := isZero_singularCohomology_ofSubset_of_eq_univ hXuniv R k M n
    exact isIso_of_source_target_iso_zero _ hsrc.isoZero (isZero_biproduct_of_isEmpty _).isoZero
  | m + 1, Z, _, X, B, F, E, _, _, _, _, _, _, _, _, hnorm, f, hf, hX, hfX, hdisj, hfcover => by
    let e := (finSuccEquiv m).symm
    refine isIso_biproductLift_of_equiv e ?_
    let f' := fun i : Option (Fin m) ↦ f (e i)
    have hf' : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f' i)) := fun i ↦ hf (e i)
    have hfX' : ∀ i (v : discBundle (F (e i)) (E (e i))),
        TopPair.Hom.fst (f' i) v ∈ X →
          (v : TotalSpace (F (e i)) (E (e i))) ∈ sphereBundle (F (e i)) (E (e i)) :=
      fun i ↦ hfX (e i)
    have hdisj' : Pairwise fun i j ↦
        Disjoint (range (TopPair.Hom.fst (f' i)) \ X) (range (TopPair.Hom.fst (f' j)) \ X) :=
      fun _ _ hne ↦ hdisj (e.injective.ne hne)
    exact isIso_biproductLift_option (fun i ↦ hnorm (e i)) hf' hX hfX' hdisj'
      (cover_comp_equiv e hfcover) R k M n
      (isIso_biproductLift_fin R k M n m (fun j ↦ hnorm (e (some j)))
        (isClosedEmbedding_restrictAttachSome f' hf' hX) (hX.preimage continuous_subtype_val)
        (mem_sphereBundle_restrictAttachSome f' hfX')
        (pairwise_disjoint_restrictAttachSome f' hdisj') (cover_restrictAttachSome f'))

/-- **Attaching a finite family of unit disc bundles induces direct-sum isomorphisms on relative
singular homology.** Let `Eᵢ → Bᵢ` (`i : ι`, `[Finite ι]`) be real vector bundles with continuous
fibre norms, `X` a closed subset of `Z`, and `fᵢ : (D(Eᵢ), S(Eᵢ)) ⟶ (Z, X)` closed embeddings
whose images meet `X` only along `S(Eᵢ)`, whose open disc interiors `fᵢ(D(Eᵢ)) \ X` are pairwise
disjoint, and which together with `X` cover `Z`. Then
`⨁ᵢ Hₙ(D(Eᵢ), S(Eᵢ); R) ⟶ Hₙ(Z, X; R)` is an isomorphism in every degree. -/
theorem isIso_biproductDesc_singularHomologyMap_of_attach_discBundles
    {ι : Type*} [Finite ι]
    {B : ι → Type w} {F : ι → Type uF} {E : ∀ i, B i → Type w}
    [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    [∀ i b, NormedAddCommGroup (E i b)] [∀ i b, NormedSpace ℝ (E i b)]
    [∀ i, TopologicalSpace (TotalSpace (F i) (E i))] [∀ i, FiberBundle (F i) (E i)]
    [∀ i, VectorBundle ℝ (F i) (E i)]
    (hnorm : ∀ i, Continuous fun v : TotalSpace (F i) (E i) ↦ ‖v.2‖)
    {Z : Type w} [TopologicalSpace Z] {X : Set Z}
    {f : ∀ i, discSpherePair (F i) (E i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
    (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))) (hX : IsClosed X)
    (hfX : ∀ i (v : discBundle (F i) (E i)),
      TopPair.Hom.fst (f i) v ∈ X → (v : TotalSpace (F i) (E i)) ∈ sphereBundle (F i) (E i))
    (hdisj : Pairwise fun i j ↦
      Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X))
    (hfcover : X ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] [HasFiniteBiproducts C]
    (R : C) (n : ℕ) :
    IsIso (biproduct.desc fun i ↦ TopPair.singularHomologyMap (f i) R n) := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  exact isIso_biproductDesc_of_equiv e.symm <|
    isIso_biproductDesc_fin R n m (fun j ↦ hnorm (e.symm j)) (fun j ↦ hf (e.symm j)) hX
      (fun j ↦ hfX (e.symm j)) (fun _ _ hne ↦ hdisj (e.symm.injective.ne hne))
      (cover_comp_equiv e.symm hfcover)

/-- **Attaching a finite family of unit disc bundles induces direct-sum isomorphisms on relative
singular cohomology.** Under the hypotheses of
`TauCeti.isIso_biproductDesc_singularHomologyMap_of_attach_discBundles`,
`Hⁿ(Z, X) ⟶ ⨁ᵢ Hⁿ(D(Eᵢ), S(Eᵢ))` is an isomorphism in every degree. -/
theorem isIso_biproductLift_singularCohomologyMap_of_attach_discBundles
    {ι : Type*} [Finite ι]
    {B : ι → Type w} {F : ι → Type uF} {E : ∀ i, B i → Type w}
    [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    [∀ i b, NormedAddCommGroup (E i b)] [∀ i b, NormedSpace ℝ (E i b)]
    [∀ i, TopologicalSpace (TotalSpace (F i) (E i))] [∀ i, FiberBundle (F i) (E i)]
    [∀ i, VectorBundle ℝ (F i) (E i)]
    (hnorm : ∀ i, Continuous fun v : TotalSpace (F i) (E i) ↦ ‖v.2‖)
    {Z : Type w} [TopologicalSpace Z] {X : Set Z}
    {f : ∀ i, discSpherePair (F i) (E i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
    (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))) (hX : IsClosed X)
    (hfX : ∀ i (v : discBundle (F i) (E i)),
      TopPair.Hom.fst (f i) v ∈ X → (v : TotalSpace (F i) (E i)) ∈ sphereBundle (F i) (E i))
    (hdisj : Pairwise fun i j ↦
      Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X))
    (hfcover : X ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    IsIso (biproduct.lift fun i ↦
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (f i) n) := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  exact isIso_biproductLift_of_equiv e.symm <|
    isIso_biproductLift_fin R k M n m (fun j ↦ hnorm (e.symm j)) (fun j ↦ hf (e.symm j)) hX
      (fun j ↦ hfX (e.symm j)) (fun _ _ hne ↦ hdisj (e.symm.injective.ne hne))
      (cover_comp_equiv e.symm hfcover)

end UnitRadius

section Radius

variable {ι : Type*} [Finite ι]
  {B : ι → Type w} {F : ι → Type uF} {E : ∀ i, B i → Type w}
  [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  [∀ i b, NormedAddCommGroup (E i b)] [∀ i b, NormedSpace ℝ (E i b)]
  [∀ i, TopologicalSpace (TotalSpace (F i) (E i))] [∀ i, FiberBundle (F i) (E i)]
  [∀ i, VectorBundle ℝ (F i) (E i)]
  (hnorm : ∀ i, Continuous fun v : TotalSpace (F i) (E i) ↦ ‖v.2‖)
  {r : ∀ i, B i → ℝ} (hr : ∀ i, Continuous (r i)) (hrpos : ∀ i b, 0 < r i b)
  {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  {f : ∀ i, discSpherePairOfRadius (F i) (E i) (r i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
  (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))) (hX : IsClosed X)
  (hfX : ∀ i (v : discBundleOfRadius (F i) (E i) (r i)),
    TopPair.Hom.fst (f i) v ∈ X →
      (v : TotalSpace (F i) (E i)) ∈ sphereBundleOfRadius (F i) (E i) (r i))
  (hdisj : Pairwise fun i j ↦
    Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X))
  (hfcover : X ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ)

omit [Finite ι] in
include hr hrpos hdisj in
private lemma pairwise_disjoint_rescaledFamily :
    Pairwise fun i j ↦
      Disjoint
        (range (TopPair.Hom.fst
          ((discSpherePairIsoOfRadius (F i) (E i) (hr i) (hrpos i)).hom ≫ f i)) \ X)
        (range (TopPair.Hom.fst
          ((discSpherePairIsoOfRadius (F j) (E j) (hr j) (hrpos j)).hom ≫ f j)) \ X) :=
  fun i j hij ↦ disjoint_left.2 fun _ ⟨hz₁, hzX⟩ ⟨hz₂, _⟩ ↦
    disjoint_left.1 (hdisj hij)
      ⟨(mem_range_fst_rescaledAttach (hr i) (hrpos i)).1 hz₁, hzX⟩
      ⟨(mem_range_fst_rescaledAttach (hr j) (hrpos j)).1 hz₂, hzX⟩

omit [Finite ι] in
include hr hrpos hfcover in
private lemma cover_rescaledFamily :
    X ∪ ⋃ i, range (TopPair.Hom.fst
      ((discSpherePairIsoOfRadius (F i) (E i) (hr i) (hrpos i)).hom ≫ f i)) = univ :=
  eq_univ_of_forall fun z ↦ (eq_univ_iff_forall.1 hfcover z).imp_right fun hz ↦ by
    obtain ⟨i, hzi⟩ := mem_iUnion.1 hz
    exact mem_iUnion.2 ⟨i, (mem_range_fst_rescaledAttach (hr i) (hrpos i)).2 hzi⟩

include hnorm hr hrpos hf hX hfX hdisj hfcover in
/-- **Attaching a finite family of disc bundles of positive continuous radii induces direct-sum
isomorphisms on relative singular homology**:
`⨁ᵢ Hₙ(D_{rᵢ}(Eᵢ), S_{rᵢ}(Eᵢ); R) ≅ Hₙ(Z, X; R)`. -/
theorem isIso_biproductDesc_singularHomologyMap_of_attach_discBundlesOfRadius
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] [HasFiniteBiproducts C]
    (R : C) (n : ℕ) :
    IsIso (biproduct.desc fun i ↦ TopPair.singularHomologyMap (f i) R n) := by
  let g := fun i ↦ (discSpherePairIsoOfRadius (F i) (E i) (hr i) (hrpos i)).hom ≫ f i
  have hg : IsIso (biproduct.desc fun i ↦ TopPair.singularHomologyMap (g i) R n) :=
    isIso_biproductDesc_singularHomologyMap_of_attach_discBundles hnorm
      (fun i ↦ isClosedEmbedding_rescaledAttach (hr i) (hrpos i) (hf i)) hX
      (fun i ↦ mem_sphereBundle_of_rescaledAttach_mem (hr i) (hrpos i) (hfX i))
      (pairwise_disjoint_rescaledFamily hr hrpos hdisj)
      (cover_rescaledFamily hr hrpos hfcover) R n
  let rescaleIso : (⨁ fun i ↦ (discSpherePair (F i) (E i)).singularHomology R n) ≅
      (⨁ fun i ↦ (discSpherePairOfRadius (F i) (E i) (r i)).singularHomology R n) :=
    biproduct.mapIso fun i ↦
      singularHomologyMapIso (discSpherePairIsoOfRadius (F i) (E i) (hr i) (hrpos i)) R n
  have hfac : rescaleIso.hom ≫ biproduct.desc (fun i ↦ TopPair.singularHomologyMap (f i) R n) =
      biproduct.desc (fun i ↦ TopPair.singularHomologyMap (g i) R n) := by
    simp [rescaleIso, g, TopPair.singularHomologyMap_comp]
  have : IsIso
      (rescaleIso.hom ≫ biproduct.desc (fun i ↦ TopPair.singularHomologyMap (f i) R n)) := by
    rw [hfac]; exact hg
  exact IsIso.of_isIso_comp_left rescaleIso.hom _

include hnorm hr hrpos hf hX hfX hdisj hfcover in
/-- **Attaching a finite family of disc bundles of positive continuous radii induces direct-sum
isomorphisms on relative singular cohomology**:
`Hⁿ(Z, X; R, M) ≅ ⨁ᵢ Hⁿ(D_{rᵢ}(Eᵢ), S_{rᵢ}(Eᵢ); R, M)`. -/
theorem isIso_biproductLift_singularCohomologyMap_of_attach_discBundlesOfRadius
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    IsIso (biproduct.lift fun i ↦
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (f i) n) := by
  let g := fun i ↦ (discSpherePairIsoOfRadius (F i) (E i) (hr i) (hrpos i)).hom ≫ f i
  have hg : IsIso (biproduct.lift fun i ↦
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (g i) n) :=
    isIso_biproductLift_singularCohomologyMap_of_attach_discBundles hnorm
      (fun i ↦ isClosedEmbedding_rescaledAttach (hr i) (hrpos i) (hf i)) hX
      (fun i ↦ mem_sphereBundle_of_rescaledAttach_mem (hr i) (hrpos i) (hfX i))
      (pairwise_disjoint_rescaledFamily hr hrpos hdisj)
      (cover_rescaledFamily hr hrpos hfcover) R k M n
  let rescaleIso :
      (⨁ fun i ↦ (discSpherePairOfRadius (F i) (E i) (r i)).singularCohomology R k M n) ≅
        (⨁ fun i ↦ (discSpherePair (F i) (E i)).singularCohomology R k M n) :=
    biproduct.mapIso fun i ↦
      singularCohomologyMapIso (discSpherePairIsoOfRadius (F i) (E i) (hr i) (hrpos i)) R k M n
  have hfac : biproduct.lift (fun i ↦
        TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (f i) n) ≫ rescaleIso.hom =
      biproduct.lift (fun i ↦ TopPair.singularCohomologyMap (g i) n) := by
    simp [rescaleIso, g, TopPair.singularCohomologyMap_comp]
  have : IsIso (biproduct.lift (fun i ↦
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (f i) n) ≫ rescaleIso.hom) := by
    rw [hfac]; exact hg
  exact IsIso.of_isIso_comp_right _ rescaleIso.hom

end Radius

end FiniteFamily

/-! ### Thom-pair decompositions and ambient strong deformation retracts -/

section ThomDecomposition

section UnitRadius

variable {ι : Type*} [Finite ι]
  {B : ι → Type w} {F : ι → Type uF} {E : ∀ i, B i → Type w}
  [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  [∀ i b, NormedAddCommGroup (E i b)] [∀ i b, NormedSpace ℝ (E i b)]
  [∀ i, TopologicalSpace (TotalSpace (F i) (E i))] [∀ i, FiberBundle (F i) (E i)]
  [∀ i, VectorBundle ℝ (F i) (E i)]
  (hnorm : ∀ i, Continuous fun v : TotalSpace (F i) (E i) ↦ ‖v.2‖)
  {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  {f : ∀ i, discSpherePair (F i) (E i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
  (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))) (hX : IsClosed X)
  (hfX : ∀ i (v : discBundle (F i) (E i)),
    TopPair.Hom.fst (f i) v ∈ X → (v : TotalSpace (F i) (E i)) ∈ sphereBundle (F i) (E i))
  (hdisj : Pairwise fun i j ↦
    Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X))
  (hfcover : X ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ)

/-- **Thom-pair homology decomposition of a finite unit disc-bundle attachment**:
`⨁ᵢ Hₙ(Eᵢ, (Eᵢ)₀; R) ≅ Hₙ(Z, X; R)`. -/
def singularHomologyIsoThomPairsOfAttachDiscBundles
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] [HasFiniteBiproducts C]
    (R : C) (n : ℕ) :
    (⨁ fun i ↦ (thomPair (F i) (E i)).singularHomology R n) ≅
      (TopPair.ofSubset (X := TopCat.of Z) X).singularHomology R n :=
  (biproduct.mapIso fun i ↦ (@asIso _ _ _ _
      (TopPair.singularHomologyMap (discSpherePairMap (F i) (E i)) R n)
      (isIso_singularHomologyMap_discSpherePairMap (F i) (E i) (hnorm i) R n)).symm) ≪≫
  @asIso _ _ _ _ (biproduct.desc fun i ↦ TopPair.singularHomologyMap (f i) R n)
    (isIso_biproductDesc_singularHomologyMap_of_attach_discBundles hnorm hf hX hfX hdisj hfcover
      R n)

@[reassoc (attr := simp)]
theorem singularHomologyMap_discSpherePairMap_comp_ι_isoThomPairs_hom
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] [HasFiniteBiproducts C]
    (R : C) (n : ℕ) (i : ι) :
    TopPair.singularHomologyMap (discSpherePairMap (F i) (E i)) R n ≫
        biproduct.ι (fun j ↦ (thomPair (F j) (E j)).singularHomology R n) i ≫
          (singularHomologyIsoThomPairsOfAttachDiscBundles
            hnorm hf hX hfX hdisj hfcover R n).hom =
      TopPair.singularHomologyMap (f i) R n := by
  have := isIso_singularHomologyMap_discSpherePairMap (F i) (E i) (hnorm i) R n
  have := isIso_biproductDesc_singularHomologyMap_of_attach_discBundles
    hnorm hf hX hfX hdisj hfcover R n
  simp [singularHomologyIsoThomPairsOfAttachDiscBundles]

/-- **Thom-pair cohomology decomposition of a finite unit disc-bundle attachment**:
`Hⁿ(Z, X; R, M) ≅ ⨁ᵢ Hⁿ(Eᵢ, (Eᵢ)₀; R, M)`. -/
def singularCohomologyIsoThomPairsOfAttachDiscBundles
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    (TopPair.ofSubset (X := TopCat.of Z) X).singularCohomology R k M n ≅
      ⨁ fun i ↦ (thomPair (F i) (E i)).singularCohomology R k M n :=
  @asIso _ _ _ _ (biproduct.lift fun i ↦
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (f i) n)
    (isIso_biproductLift_singularCohomologyMap_of_attach_discBundles
      hnorm hf hX hfX hdisj hfcover R k M n) ≪≫
  biproduct.mapIso fun i ↦ (@asIso _ _ _ _
      (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
        (discSpherePairMap (F i) (E i)) n)
      (isIso_singularCohomologyMap_discSpherePairMap (F i) (E i) (hnorm i) R k M n)).symm

@[reassoc (attr := simp)]
theorem singularCohomologyIsoThomPairsOfAttachDiscBundles_hom_comp_π_comp
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) (i : ι) :
    (singularCohomologyIsoThomPairsOfAttachDiscBundles
        hnorm hf hX hfX hdisj hfcover R k M n).hom ≫
      biproduct.π (fun j ↦ (thomPair (F j) (E j)).singularCohomology R k M n) i ≫
      TopPair.singularCohomologyMap (discSpherePairMap (F i) (E i)) n =
      TopPair.singularCohomologyMap (f i) n := by
  have := isIso_singularCohomologyMap_discSpherePairMap (F i) (E i) (hnorm i) R k M n
  have := isIso_biproductLift_singularCohomologyMap_of_attach_discBundles
    hnorm hf hX hfX hdisj hfcover R k M n
  simp [singularCohomologyIsoThomPairsOfAttachDiscBundles]

end UnitRadius

section Radius

variable {ι : Type*} [Finite ι]
  {B : ι → Type w} {F : ι → Type uF} {E : ∀ i, B i → Type w}
  [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  [∀ i b, NormedAddCommGroup (E i b)] [∀ i b, NormedSpace ℝ (E i b)]
  [∀ i, TopologicalSpace (TotalSpace (F i) (E i))] [∀ i, FiberBundle (F i) (E i)]
  [∀ i, VectorBundle ℝ (F i) (E i)]
  (hnorm : ∀ i, Continuous fun v : TotalSpace (F i) (E i) ↦ ‖v.2‖)
  {r : ∀ i, B i → ℝ} (hr : ∀ i, Continuous (r i)) (hrpos : ∀ i b, 0 < r i b)
  {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  {f : ∀ i, discSpherePairOfRadius (F i) (E i) (r i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
  (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))) (hX : IsClosed X)
  (hfX : ∀ i (v : discBundleOfRadius (F i) (E i) (r i)),
    TopPair.Hom.fst (f i) v ∈ X →
      (v : TotalSpace (F i) (E i)) ∈ sphereBundleOfRadius (F i) (E i) (r i))
  (hdisj : Pairwise fun i j ↦
    Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X))
  (hfcover : X ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ)

/-- **Thom-pair homology decomposition of a finite radius-`r` disc-bundle attachment**:
`⨁ᵢ Hₙ(Eᵢ, (Eᵢ)₀; R) ≅ Hₙ(Z, X; R)`. -/
def singularHomologyIsoThomPairsOfAttachDiscBundlesOfRadius
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] [HasFiniteBiproducts C]
    (R : C) (n : ℕ) :
    (⨁ fun i ↦ (thomPair (F i) (E i)).singularHomology R n) ≅
      (TopPair.ofSubset (X := TopCat.of Z) X).singularHomology R n :=
  (biproduct.mapIso fun i ↦ (@asIso _ _ _ _
      (TopPair.singularHomologyMap
        (discSpherePairOfRadiusMap (F i) (E i) fun b ↦ (hrpos i b).ne') R n)
      (isIso_singularHomologyMap_discSpherePairOfRadiusMap
        (F i) (E i) (hnorm i) (hr i) (hrpos i) R n)).symm) ≪≫
  @asIso _ _ _ _ (biproduct.desc fun i ↦ TopPair.singularHomologyMap (f i) R n)
    (isIso_biproductDesc_singularHomologyMap_of_attach_discBundlesOfRadius
      hnorm hr hrpos hf hX hfX hdisj hfcover R n)

@[reassoc (attr := simp)]
theorem singularHomologyMap_discSpherePairOfRadiusMap_comp_ι_isoThomPairs_hom
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] [HasFiniteBiproducts C]
    (R : C) (n : ℕ) (i : ι) :
    TopPair.singularHomologyMap
          (discSpherePairOfRadiusMap (F i) (E i) fun b ↦ (hrpos i b).ne') R n ≫
        biproduct.ι (fun j ↦ (thomPair (F j) (E j)).singularHomology R n) i ≫
          (singularHomologyIsoThomPairsOfAttachDiscBundlesOfRadius
            hnorm hr hrpos hf hX hfX hdisj hfcover R n).hom =
      TopPair.singularHomologyMap (f i) R n := by
  have := isIso_singularHomologyMap_discSpherePairOfRadiusMap
    (F i) (E i) (hnorm i) (hr i) (hrpos i) R n
  have := isIso_biproductDesc_singularHomologyMap_of_attach_discBundlesOfRadius
    hnorm hr hrpos hf hX hfX hdisj hfcover R n
  simp [singularHomologyIsoThomPairsOfAttachDiscBundlesOfRadius]

/-- **Thom-pair cohomology decomposition of a finite radius-`r` disc-bundle attachment**:
`Hⁿ(Z, X; R, M) ≅ ⨁ᵢ Hⁿ(Eᵢ, (Eᵢ)₀; R, M)`. -/
def singularCohomologyIsoThomPairsOfAttachDiscBundlesOfRadius
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    (TopPair.ofSubset (X := TopCat.of Z) X).singularCohomology R k M n ≅
      ⨁ fun i ↦ (thomPair (F i) (E i)).singularCohomology R k M n :=
  @asIso _ _ _ _ (biproduct.lift fun i ↦
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (f i) n)
    (isIso_biproductLift_singularCohomologyMap_of_attach_discBundlesOfRadius
      hnorm hr hrpos hf hX hfX hdisj hfcover R k M n) ≪≫
  biproduct.mapIso fun i ↦ (@asIso _ _ _ _
      (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
        (discSpherePairOfRadiusMap (F i) (E i) fun b ↦ (hrpos i b).ne') n)
      (isIso_singularCohomologyMap_discSpherePairOfRadiusMap
        (F i) (E i) (hnorm i) (hr i) (hrpos i) R k M n)).symm

@[reassoc (attr := simp)]
theorem singularCohomologyIsoThomPairsOfAttachDiscBundlesOfRadius_hom_comp_π_comp
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) (i : ι) :
    (singularCohomologyIsoThomPairsOfAttachDiscBundlesOfRadius
        hnorm hr hrpos hf hX hfX hdisj hfcover R k M n).hom ≫
      biproduct.π (fun j ↦ (thomPair (F j) (E j)).singularCohomology R k M n) i ≫
      TopPair.singularCohomologyMap
        (discSpherePairOfRadiusMap (F i) (E i) fun b ↦ (hrpos i b).ne') n =
      TopPair.singularCohomologyMap (f i) n := by
  have := isIso_singularCohomologyMap_discSpherePairOfRadiusMap
    (F i) (E i) (hnorm i) (hr i) (hrpos i) R k M n
  have := isIso_biproductLift_singularCohomologyMap_of_attach_discBundlesOfRadius
    hnorm hr hrpos hf hX hfX hdisj hfcover R k M n
  simp [singularCohomologyIsoThomPairsOfAttachDiscBundlesOfRadius]

end Radius

section DeformationRetract

variable {ι : Type*} [Finite ι]
  {B : ι → Type w} {F : ι → Type uF} {E : ∀ i, B i → Type w}
  [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  [∀ i b, NormedAddCommGroup (E i b)] [∀ i b, NormedSpace ℝ (E i b)]
  [∀ i, TopologicalSpace (TotalSpace (F i) (E i))] [∀ i, FiberBundle (F i) (E i)]
  [∀ i, VectorBundle ℝ (F i) (E i)]
  (hnorm : ∀ i, Continuous fun v : TotalSpace (F i) (E i) ↦ ‖v.2‖)
  {r : ∀ i, B i → ℝ} (hr : ∀ i, Continuous (r i)) (hrpos : ∀ i b, 0 < r i b)
  {M : Type w} [TopologicalSpace M] {X Z Y : Set M} (hXZ : X ⊆ Z) (hZY : Z ⊆ Y)
  {f : ∀ i, discSpherePairOfRadius (F i) (E i) (r i) ⟶ TopPair.ofInclusion (X := TopCat.of M) hXZ}
  (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i)))
  (hX : IsClosed (Subtype.val ⁻¹' X : Set Z))
  (hfX : ∀ i (v : discBundleOfRadius (F i) (E i) (r i)),
    TopPair.Hom.fst (f i) v ∈ (Subtype.val ⁻¹' X : Set Z) →
      (v : TotalSpace (F i) (E i)) ∈ sphereBundleOfRadius (F i) (E i) (r i))
  (hdisj : Pairwise fun i j ↦
    Disjoint (range (TopPair.Hom.fst (f i)) \ Subtype.val ⁻¹' X)
      (range (TopPair.Hom.fst (f j)) \ Subtype.val ⁻¹' X))
  (hfcover : (Subtype.val ⁻¹' X : Set Z) ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ)
  (ret : C(Y, Z))
  (G : ((ContinuousMap.inclusion hZY).comp ret).HomotopyRel (ContinuousMap.id Y)
    {y | (y : M) ∈ Z})

omit [Finite ι] [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)]
  [∀ i, NormedSpace ℝ (F i)] [∀ i b, NormedSpace ℝ (E i b)] [∀ i, FiberBundle (F i) (E i)]
  [∀ i, VectorBundle ℝ (F i) (E i)] in
private lemma comp_ofSubsetPreimageValIso_inv_fst_apply (i : ι)
    (v : discBundleOfRadius (F i) (E i) (r i)) :
    (TopPair.Hom.fst (f i ≫ (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) hXZ).inv) v : Z) =
      TopPair.Hom.fst (f i) v :=
  (ConcreteCategory.comp_apply (TopPair.Hom.fst (f i))
    (TopPair.Hom.fst (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) hXZ).inv) v).trans
    (TopPair.ofSubsetPreimageValIso_inv_fst_apply (TopPair.Hom.fst (f i) v))

omit [Finite ι] [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)]
  [∀ i, NormedSpace ℝ (F i)] [∀ i b, NormedSpace ℝ (E i b)] [∀ i, FiberBundle (F i) (E i)]
  [∀ i, VectorBundle ℝ (F i) (E i)] in
private lemma mem_range_fst_comp_ofSubsetPreimageValIso_inv (i : ι) {z : Z} :
    z ∈ (range (TopPair.Hom.fst
      (f i ≫ (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) hXZ).inv)) : Set Z) ↔
      z ∈ (range (TopPair.Hom.fst (f i)) : Set Z) :=
  ⟨fun ⟨v, hv⟩ ↦ ⟨v, (comp_ofSubsetPreimageValIso_inv_fst_apply hXZ (f := f) i v).symm.trans hv⟩,
   fun ⟨v, hv⟩ ↦ ⟨v, (comp_ofSubsetPreimageValIso_inv_fst_apply hXZ (f := f) i v).trans hv⟩⟩

omit [Finite ι] [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)]
  [∀ i, NormedSpace ℝ (F i)] [∀ i b, NormedSpace ℝ (E i b)] [∀ i, FiberBundle (F i) (E i)]
  [∀ i, VectorBundle ℝ (F i) (E i)] in
include hf in
private lemma isClosedEmbedding_comp_ofSubsetPreimageValIso_inv (i : ι) :
    IsClosedEmbedding
      (TopPair.Hom.fst (f i ≫ (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) hXZ).inv)) := by
  have hfn : (⇑(TopPair.Hom.fst
      (f i ≫ (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) hXZ).inv)) :
      discBundleOfRadius (F i) (E i) (r i) → Z) = ⇑(TopPair.Hom.fst (f i)) :=
    funext (comp_ofSubsetPreimageValIso_inv_fst_apply hXZ i)
  exact hfn ▸ hf i

omit [Finite ι] [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)]
  [∀ i, NormedSpace ℝ (F i)] [∀ i b, NormedSpace ℝ (E i b)] [∀ i, FiberBundle (F i) (E i)]
  [∀ i, VectorBundle ℝ (F i) (E i)] in
include hfX in
private lemma mem_sphereBundle_comp_ofSubsetPreimageValIso_inv (i : ι)
    (v : discBundleOfRadius (F i) (E i) (r i))
    (hv : TopPair.Hom.fst
      (f i ≫ (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) hXZ).inv) v ∈
        (Subtype.val ⁻¹' X : Set Z)) :
    (v : TotalSpace (F i) (E i)) ∈ sphereBundleOfRadius (F i) (E i) (r i) :=
  hfX i v (comp_ofSubsetPreimageValIso_inv_fst_apply hXZ (f := f) i v ▸ hv)

omit [Finite ι] [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)]
  [∀ i, NormedSpace ℝ (F i)] [∀ i b, NormedSpace ℝ (E i b)] [∀ i, FiberBundle (F i) (E i)]
  [∀ i, VectorBundle ℝ (F i) (E i)] in
include hdisj in
private lemma pairwise_disjoint_comp_ofSubsetPreimageValIso_inv :
    Pairwise fun i j ↦
      Disjoint
        (range (TopPair.Hom.fst
          (f i ≫ (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) hXZ).inv)) \
          (Subtype.val ⁻¹' X : Set Z))
        (range (TopPair.Hom.fst
          (f j ≫ (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) hXZ).inv)) \
          (Subtype.val ⁻¹' X : Set Z)) :=
  fun i j hij ↦ disjoint_left.2 fun _ ⟨hz₁, hzX⟩ ⟨hz₂, _⟩ ↦
    disjoint_left.1 (hdisj hij)
      ⟨(mem_range_fst_comp_ofSubsetPreimageValIso_inv hXZ i).1 hz₁, hzX⟩
      ⟨(mem_range_fst_comp_ofSubsetPreimageValIso_inv hXZ j).1 hz₂, hzX⟩

omit [Finite ι] [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)]
  [∀ i, NormedSpace ℝ (F i)] [∀ i b, NormedSpace ℝ (E i b)] [∀ i, FiberBundle (F i) (E i)]
  [∀ i, VectorBundle ℝ (F i) (E i)] in
include hfcover in
private lemma cover_comp_ofSubsetPreimageValIso_inv :
    (Subtype.val ⁻¹' X : Set Z) ∪
      ⋃ i, range (TopPair.Hom.fst
        (f i ≫ (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) hXZ).inv)) = univ :=
  eq_univ_of_forall fun z ↦ (eq_univ_iff_forall.1 hfcover z).imp_right fun hz ↦ by
    obtain ⟨i, hzi⟩ := mem_iUnion.1 hz
    exact mem_iUnion.2 ⟨i, (mem_range_fst_comp_ofSubsetPreimageValIso_inv hXZ i).2 hzi⟩

/-- **Thom-pair homology across an ambient strong deformation retract onto an attached disc-bundle
complex.** Let `X ⊆ Z ⊆ Y` be nested subsets of `M` such that `X` is closed in `Z`, `Z` is obtained
from `X` by attaching a finite family of disc bundles `D_{rᵢ}(Eᵢ)` along `S_{rᵢ}(Eᵢ)`, and `Y`
strong deformation retracts onto `Z`. Then `⨁ᵢ Hₙ(Eᵢ, (Eᵢ)₀; R) ≅ Hₙ(Y, X; R)`. Across a Morse–Bott
critical level `c`, taking `X = {g ≤ c - ε}`, `Y = {g ≤ c + ε}` and `Z` the lower sublevel union the
attached negative disc bundles computes the relative homology of the sublevel pair. -/
def singularHomologyIsoThomPairsOfDeformationRetractAttachDiscBundlesOfRadius
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] [HasFiniteBiproducts C]
    (R : C) (n : ℕ) :
    (⨁ fun i ↦ (thomPair (F i) (E i)).singularHomology R n) ≅
      (TopPair.ofInclusion (X := TopCat.of M) (hXZ.trans hZY)).singularHomology R n :=
  singularHomologyIsoThomPairsOfAttachDiscBundlesOfRadius (Z := Z) (X := Subtype.val ⁻¹' X)
      (f := fun i ↦ f i ≫ (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) hXZ).inv)
      hnorm hr hrpos (isClosedEmbedding_comp_ofSubsetPreimageValIso_inv hXZ hf) hX
      (mem_sphereBundle_comp_ofSubsetPreimageValIso_inv hXZ hfX)
      (pairwise_disjoint_comp_ofSubsetPreimageValIso_inv hXZ hdisj)
      (cover_comp_ofSubsetPreimageValIso_inv hXZ hfcover) R n ≪≫
    singularHomologyMapIso (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) hXZ) R n ≪≫
    @asIso _ _ _ _ _
      (TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel
        (X := TopCat.of M) hXZ hZY ret G R n)

@[reassoc (attr := simp)]
theorem singularHomologyMap_discSpherePairOfRadiusMap_comp_ι_isoDeformationRetract_hom
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] [HasFiniteBiproducts C]
    (R : C) (n : ℕ) (i : ι) :
    TopPair.singularHomologyMap
          (discSpherePairOfRadiusMap (F i) (E i) fun b ↦ (hrpos i b).ne') R n ≫
        biproduct.ι (fun j ↦ (thomPair (F j) (E j)).singularHomology R n) i ≫
          (singularHomologyIsoThomPairsOfDeformationRetractAttachDiscBundlesOfRadius
            hnorm hr hrpos hXZ hZY hf hX hfX hdisj hfcover ret G R n).hom =
      TopPair.singularHomologyMap
        (f i ≫ TopPair.ofInclusionMap hXZ (hXZ.trans hZY) (ContinuousMap.inclusion hZY)
          fun _ hx ↦ by simpa using hx) R n := by
  have := TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel
    (X := TopCat.of M) hXZ hZY ret G R n
  rw [singularHomologyIsoThomPairsOfDeformationRetractAttachDiscBundlesOfRadius, Iso.trans_hom,
    Iso.trans_hom, singularHomologyMapIso_hom, asIso_hom,
    singularHomologyMap_discSpherePairOfRadiusMap_comp_ι_isoThomPairs_hom_assoc,
    ← TopPair.singularHomologyMap_comp_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    ← TopPair.singularHomologyMap_comp]

end DeformationRetract

end ThomDecomposition

end TauCeti
