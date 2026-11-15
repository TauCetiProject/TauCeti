/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Basic
public import Mathlib.Topology.Compactness.LocallyFinite
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Topology.LocallyFinite.Basic

/-!
# Locally finite singular chains and Borel–Moore homology

A locally finite singular `k`-chain of a space `X` with coefficients in a local coefficient system
`L` assigns to every singular `k`-simplex `σ` a coefficient in the fibre of `L` at the initial
vertex of `σ`, such that every point of `X` has a neighbourhood meeting the images of only finitely
many simplices with nonzero coefficient. Unlike the ordinary twisted chains of
`TauCeti.LocalCoefficientSystem.twistedChainComplex`, infinitely many coefficients may be nonzero.

A map `A` of twisted chains that moves each simplex along a proper map (`IsProperlySupported`)
extends to locally finite chains by applying it simplex by simplex (`extendLocallyFinite`): the
coefficient of the extension on `ρ` is the sum over all `σ` of the coefficient on `ρ` of `A` applied
to the chain supported on `σ`. Properness makes this sum finite and the result locally finite, and
extension takes composites to composites (`extendLocallyFiniteFun_extendLocallyFiniteFun`).

The boundary of a locally finite chain is the extension of the twisted boundary, which only
involves faces. The coefficient of the boundary on a `k`-simplex `ρ` is the sum, over the
`(k + 1)`-simplices `σ` having `ρ` as a face, of the transported coefficients of `σ`. It squares to
zero because the ordinary twisted boundary does. A family of finite chains supported in a locally
finite family of sets has a locally finite sum, and the boundary of the sum is the sum of the
boundaries.

Borel–Moore homology with local coefficients is the homology of this complex. Finite chains are
locally finite, and including them is a chain map from the twisted chain complex; on a compact space
every locally finite chain is finite, so this inclusion is an isomorphism there.

## Main declarations

* `TauCeti.LocalCoefficientSystem.IsLocallyFiniteChain`: local finiteness of a family of simplex
  coefficients, and `locallyFiniteChains` the module of locally finite chains.
* `TauCeti.LocalCoefficientSystem.IsProperlySupported`: maps of twisted chains moving simplices
  along a proper map, and `extendLocallyFinite` their extension to locally finite chains.
* `TauCeti.LocalCoefficientSystem.locallyFiniteBoundary`: the boundary of locally finite chains,
  with `locallyFiniteBoundary_comp_locallyFiniteBoundary` stating that it squares to zero.
* `TauCeti.LocalCoefficientSystem.locallyFiniteSum`: the locally finite sum of a family of finite
  chains supported in a locally finite family of sets, with
  `locallyFiniteBoundary_locallyFiniteSum` stating that its boundary is the sum of the
  boundaries.
* `TauCeti.LocalCoefficientSystem.locallyFiniteChainComplex` and `borelMooreHomology`: the complex
  of locally finite chains and its homology.
* `TauCeti.LocalCoefficientSystem.toLocallyFiniteChainComplex`: the inclusion of twisted chains,
  and `twistedHomologyToBorelMooreHomology` the induced map on homology.
* `TauCeti.LocalCoefficientSystem.isIso_toLocallyFiniteChainComplex`: on a compact space the
  inclusion is an isomorphism of chain complexes, and `twistedHomologyIsoBorelMooreHomology` the
  resulting isomorphism of homology.

## References

* A. Borel and J. C. Moore, *Homology theory for locally compact spaces*, Michigan Math. J. 7
  (1960), 137–159.
* G. E. Bredon, *Sheaf Theory*, 2nd ed., Graduate Texts in Mathematics 170, Chapter V.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H.
-/

public section

noncomputable section

open CategoryTheory Limits SimplexCategory Topology

open scoped Simplicial

universe u v w

namespace TauCeti

namespace LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}}
variable (L : LocalCoefficientSystem.{u, v, max v w} R X)

section LocallyFinite

variable {k : ℕ}

/-- A family of coefficients on the singular `k`-simplices of `X` is locally finite when every
point of `X` has a neighbourhood meeting the images of only finitely many simplices with nonzero
coefficient. -/
def IsLocallyFiniteChain (c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex σ)) :
    Prop :=
  LocallyFinite fun σ ↦ {x | c σ ≠ 0 ∧ x ∈ Set.range (TopCat.simplexMap σ)}

variable {L}

/-- Local finiteness of a chain is local finiteness of the family of images of the simplices with
nonzero coefficient. -/
lemma isLocallyFiniteChain_iff_locallyFinite
    {c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex σ)} :
    IsLocallyFiniteChain L c ↔
      LocallyFinite fun σ ↦ {x | c σ ≠ 0 ∧ x ∈ Set.range (TopCat.simplexMap σ)} :=
  Iff.rfl

/-- A chain is locally finite exactly when every point has a neighbourhood meeting the images of
only finitely many simplices with nonzero coefficient. -/
lemma isLocallyFiniteChain_iff
    {c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex σ)} :
    IsLocallyFiniteChain L c ↔ ∀ x : X, ∃ U ∈ 𝓝 x,
      {σ | c σ ≠ 0 ∧ (Set.range (TopCat.simplexMap σ) ∩ U).Nonempty}.Finite := by
  rw [isLocallyFiniteChain_iff_locallyFinite]
  refine forall_congr' fun x ↦ exists_congr fun U ↦ and_congr_right fun _ ↦ ?_
  refine iff_of_eq (congrArg Set.Finite (Set.ext fun σ ↦ ?_))
  simp only [Set.mem_ofPred_eq, Set.Nonempty, Set.mem_inter_iff]
  exact ⟨fun ⟨y, ⟨hc, hy⟩, hU⟩ ↦ ⟨hc, y, hy, hU⟩, fun ⟨hc, y, hy, hU⟩ ↦ ⟨y, ⟨hc, hy⟩, hU⟩⟩

/-- Only finitely many simplices with nonzero coefficient in a locally finite chain pass through a
given point. -/
lemma IsLocallyFiniteChain.finite_setOf_mem_range
    {c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex σ)}
    (hc : IsLocallyFiniteChain L c) (x : X) :
    {σ | c σ ≠ 0 ∧ x ∈ Set.range (TopCat.simplexMap σ)}.Finite :=
  LocallyFinite.point_finite (isLocallyFiniteChain_iff_locallyFinite.1 hc) x

/-- A chain with finitely many nonzero coefficients is locally finite. -/
lemma isLocallyFiniteChain_of_finite
    {c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex σ)}
    (hc : {σ | c σ ≠ 0}.Finite) : IsLocallyFiniteChain L c :=
  isLocallyFiniteChain_iff.2 fun _ ↦ ⟨Set.univ, Filter.univ_mem, hc.subset fun _ h ↦ h.1⟩

/-- A compact set meets the images of only finitely many simplices with nonzero coefficient in a
locally finite chain. -/
lemma IsLocallyFiniteChain.finite_setOf_inter_nonempty
    {c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex σ)}
    (hc : IsLocallyFiniteChain L c) {K : Set X} (hK : IsCompact K) :
    {σ | c σ ≠ 0 ∧ (Set.range (TopCat.simplexMap σ) ∩ K).Nonempty}.Finite :=
  (LocallyFinite.finite_nonempty_inter_compact (isLocallyFiniteChain_iff_locallyFinite.1 hc)
    hK).subset fun _ ⟨hσ, y, hy, hyK⟩ ↦ ⟨y, ⟨hσ, hy⟩, hyK⟩

/-- On a compact space a locally finite chain has only finitely many nonzero coefficients. -/
lemma IsLocallyFiniteChain.finite_setOf_ne_zero [CompactSpace X]
    {c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex σ)}
    (hc : IsLocallyFiniteChain L c) : {σ | c σ ≠ 0}.Finite :=
  (hc.finite_setOf_inter_nonempty isCompact_univ).subset fun σ hσ ↦
    ⟨hσ, TopCat.simplexMap σ (toTopInitialVertex _), ⟨_, rfl⟩, Set.mem_univ _⟩

variable (L k)

/-- The module of locally finite singular `k`-chains of `X` with coefficients in `L`. -/
def locallyFiniteChains :
    Submodule R (∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex σ)) where
  carrier := {c | IsLocallyFiniteChain L c}
  add_mem' {c c'} hc hc' := by
    simp only [Set.mem_ofPred_eq, isLocallyFiniteChain_iff] at hc hc' ⊢
    intro x
    obtain ⟨U, hU, hfin⟩ := hc x
    obtain ⟨U', hU', hfin'⟩ := hc' x
    refine ⟨U ∩ U', Filter.inter_mem hU hU', (hfin.union hfin').subset ?_⟩
    rintro σ ⟨h, y, hy, hyU, hyU'⟩
    by_cases h' : c σ = 0
    · exact Or.inr ⟨fun h'' ↦ h (by simp [h', h'']), y, hy, hyU'⟩
    · exact Or.inl ⟨h', y, hy, hyU⟩
  zero_mem' := isLocallyFiniteChain_of_finite (by simp)
  smul_mem' a c hc := LocallyFinite.subset (isLocallyFiniteChain_iff_locallyFinite.1 hc)
    fun σ y ⟨h, hy⟩ ↦ ⟨fun h' ↦ h (by simp [h']), hy⟩

variable {L k}

/-- A family of coefficients is a locally finite chain exactly when it is locally finite. -/
@[simp]
lemma mem_locallyFiniteChains
    {c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex σ)} :
    c ∈ locallyFiniteChains L k ↔ IsLocallyFiniteChain L c :=
  Iff.rfl

end LocallyFinite

section Extension

/-! A map `A` of twisted chains which moves each simplex along a proper map extends to locally
finite chains by applying it simplex by simplex: the coefficient of the extension on `ρ` is the sum
over all `σ` of the coefficient on `ρ` of `A` applied to the chain supported on `σ`. Extension takes
composites to composites. The locally finite boundary below is the extension of the twisted
boundary. -/

variable {L} {Y Z : TopCat.{v}} {K : LocalCoefficientSystem.{u, v, max v w} R Y}
  {J : LocalCoefficientSystem.{u, v, max v w} R Z} {a b e : ℕ}

/-- The coefficient on `ρ` of the image under `A` of the chain supported on `σ`. -/
def matrixCoeff (A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b)
    (ρ : (TopCat.toSSet.obj Y) _⦋b⦌) (σ : (TopCat.toSSet.obj X) _⦋a⦌) :
    L.obj (initialVertex σ) →ₗ[R] K.obj (initialVertex ρ) :=
  (ιTwistedChainComplex L a σ ≫ A ≫ twistedChainComplexCoeff K ρ).hom

/-- The coefficient on `ρ` of `A` applied to the chain supported on `σ` with coefficient `x`. -/
lemma matrixCoeff_apply (A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b)
    (ρ : (TopCat.toSSet.obj Y) _⦋b⦌) (σ : (TopCat.toSSet.obj X) _⦋a⦌)
    (x : L.obj (initialVertex σ)) :
    matrixCoeff A ρ σ x =
      (twistedChainComplexCoeff K ρ).hom (A.hom ((ιTwistedChainComplex L a σ).hom x)) :=
  (rfl)

/-- A map of twisted chains moves simplices along `g` when the image of a chain supported on a
simplex `σ` only involves simplices whose image lies in the image of `σ` under `g`. -/
def MovesAlong (g : X ⟶ Y)
    (A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b) : Prop :=
  ∀ ρ σ (x : L.obj (initialVertex σ)), matrixCoeff A ρ σ x ≠ 0 →
    Set.range (TopCat.simplexMap ρ) ⊆ g.hom '' Set.range (TopCat.simplexMap σ)

/-- A map of twisted chains is properly supported when it moves simplices along a proper map. -/
def IsProperlySupported
    (A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b) : Prop :=
  ∃ g : X ⟶ Y, IsProperMap g.hom ∧ MovesAlong g A

/-- A map of twisted chains moves simplices along `g` exactly when the image of a chain supported
on a simplex `σ` only involves simplices whose image lies in the image of `σ` under `g`. -/
lemma movesAlong_iff {g : X ⟶ Y}
    {A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b} :
    MovesAlong g A ↔ ∀ ρ σ (x : L.obj (initialVertex σ)), matrixCoeff A ρ σ x ≠ 0 →
      Set.range (TopCat.simplexMap ρ) ⊆ g.hom '' Set.range (TopCat.simplexMap σ) :=
  Iff.rfl

/-- A map of twisted chains is properly supported exactly when it moves simplices along some
proper map. -/
lemma isProperlySupported_iff
    {A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b} :
    IsProperlySupported A ↔ ∃ g : X ⟶ Y, IsProperMap g.hom ∧ MovesAlong g A :=
  Iff.rfl

/-- A map of twisted chains moving simplices along a proper map is properly supported. -/
lemma IsProperlySupported.of_movesAlong {g : X ⟶ Y}
    {A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b} (hg : IsProperMap g.hom)
    (h : MovesAlong g A) : IsProperlySupported A :=
  ⟨g, hg, h⟩

/-- The coefficients of the chain obtained by applying `A` simplex by simplex. -/
def extendLocallyFiniteFun (A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b)
    (c : ∀ σ : (TopCat.toSSet.obj X) _⦋a⦌, L.obj (initialVertex σ))
    (ρ : (TopCat.toSSet.obj Y) _⦋b⦌) : K.obj (initialVertex ρ) :=
  ∑ᶠ σ, matrixCoeff A ρ σ (c σ)

/-- The coefficient on `ρ` of the chain obtained by applying `A` simplex by simplex is the sum of
the coefficients on `ρ` of the images of the chains supported on single simplices. -/
lemma extendLocallyFiniteFun_apply (A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b)
    (c : ∀ σ : (TopCat.toSSet.obj X) _⦋a⦌, L.obj (initialVertex σ))
    (ρ : (TopCat.toSSet.obj Y) _⦋b⦌) :
    extendLocallyFiniteFun A c ρ = ∑ᶠ σ, matrixCoeff A ρ σ (c σ) :=
  (rfl)

/-- Summing the coefficients of `A` against the coefficients of a twisted chain `y` gives the
coefficients of `A y`. -/
lemma finsum_matrixCoeff (A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b)
    (y : (twistedChainComplex L).X a) (ρ : (TopCat.toSSet.obj Y) _⦋b⦌) :
    ∑ᶠ σ, matrixCoeff A ρ σ ((twistedChainComplexCoeff L σ).hom y) =
      (twistedChainComplexCoeff K ρ).hom (A.hom y) := by
  have h := map_finsum ((twistedChainComplexCoeff K ρ).hom ∘ₗ A.hom)
    (f := fun σ ↦ (ιTwistedChainComplex L a σ).hom ((twistedChainComplexCoeff L σ).hom y))
    ((finite_support_twistedChainComplexCoeff L y).subset fun σ hσ h ↦
      hσ (by simp only [h, map_zero]))
  simp only [LinearMap.comp_apply, finsum_ιTwistedChainComplex_twistedChainComplexCoeff] at h
  simp only [matrixCoeff_apply]
  exact h.symm

/-- The coefficients of a composite are the sums of products of the coefficients. -/
private lemma matrixCoeff_comp_apply
    (A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b)
    (B : (twistedChainComplex K).X b ⟶ (twistedChainComplex J).X e)
    (ρ : (TopCat.toSSet.obj Z) _⦋e⦌) (σ : (TopCat.toSSet.obj X) _⦋a⦌)
    (x : L.obj (initialVertex σ)) :
    matrixCoeff (A ≫ B) ρ σ x =
      ∑ᶠ τ, matrixCoeff B ρ τ (matrixCoeff A τ σ x) :=
  (finsum_matrixCoeff B (A.hom ((ιTwistedChainComplex L a σ).hom x)) ρ).symm

/-- Applying `A` to a chain supported on one simplex gives a chain with finitely many nonzero
coefficients. -/
private lemma finite_setOf_matrixCoeff_ne_zero
    (A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b)
    (σ : (TopCat.toSSet.obj X) _⦋a⦌) (x : L.obj (initialVertex σ)) :
    {ρ | matrixCoeff A ρ σ x ≠ 0}.Finite :=
  (finite_support_twistedChainComplexCoeff K (A.hom ((ιTwistedChainComplex L a σ).hom x))).subset
    fun _ hρ ↦ hρ

/-- Composites of maps moving simplices along `g` and `g'` move simplices along `g ≫ g'`. -/
lemma MovesAlong.comp {g : X ⟶ Y} {g' : Y ⟶ Z}
    {A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b}
    {B : (twistedChainComplex K).X b ⟶ (twistedChainComplex J).X e}
    (hA : MovesAlong g A) (hB : MovesAlong g' B) : MovesAlong (g ≫ g') (A ≫ B) := by
  intro ρ σ x hx
  rw [matrixCoeff_comp_apply] at hx
  obtain ⟨τ, hτ⟩ := not_forall.1 (mt finsum_eq_zero_of_forall_eq_zero hx)
  refine (hB ρ τ _ hτ).trans ?_
  rw [TopCat.hom_comp, ContinuousMap.coe_comp, Set.image_comp]
  exact Set.image_mono (hA τ σ x fun h ↦ hτ (by simp only [h, map_zero]))

/-- Composites of properly supported maps are properly supported. -/
lemma IsProperlySupported.comp
    {A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b}
    {B : (twistedChainComplex K).X b ⟶ (twistedChainComplex J).X e}
    (hA : IsProperlySupported A) (hB : IsProperlySupported B) : IsProperlySupported (A ≫ B) :=
  let ⟨g, hg, hgA⟩ := hA
  let ⟨g', hg', hgB⟩ := hB
  .of_movesAlong (by simpa using hg'.comp hg) (hgA.comp hgB)

/-- The identity moves simplices along the identity. -/
lemma isProperlySupported_id : IsProperlySupported (𝟙 ((twistedChainComplex L).X a)) := by
  refine .of_movesAlong (g := 𝟙 X) isProperMap_id fun ρ σ x hx ↦ ?_
  obtain rfl : σ = ρ := by
    by_contra hne
    exact hx (by
      simp [matrixCoeff_apply, twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne L hne])
  simp

variable {A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b}
  {c : ∀ σ : (TopCat.toSSet.obj X) _⦋a⦌, L.obj (initialVertex σ)}

/-- Each coefficient of the extension of a properly supported map to a locally finite chain is a
finite sum. -/
private lemma IsProperlySupported.finite_support (hA : IsProperlySupported A)
    (hc : IsLocallyFiniteChain L c) (ρ : (TopCat.toSSet.obj Y) _⦋b⦌) :
    (Function.support fun σ ↦ matrixCoeff A ρ σ (c σ)).Finite := by
  obtain ⟨g, hg, hgA⟩ := hA
  refine (hc.finite_setOf_inter_nonempty (hg.isCompact_preimage
    (isCompact_singleton (x := TopCat.simplexMap ρ (toTopInitialVertex _))))).subset
    fun σ hσ ↦ ?_
  obtain ⟨z, hz, hgz⟩ := hgA ρ σ (c σ) hσ ⟨_, rfl⟩
  exact ⟨fun h ↦ hσ (by simp only [h, map_zero]), z, hz, hgz⟩

/-- The extension of a properly supported map to a locally finite chain is locally finite. -/
private lemma IsProperlySupported.isLocallyFiniteChain_extendLocallyFiniteFun
    (hA : IsProperlySupported A) (hc : IsLocallyFiniteChain L c) :
    IsLocallyFiniteChain K (extendLocallyFiniteFun A c) := by
  obtain ⟨g, hg, hgA⟩ := hA
  have himg := (isLocallyFiniteChain_iff_locallyFinite.1 hc).image_of_isClosedMap hg.isClosedMap
    fun _ ↦ hg.isCompact_preimage isCompact_singleton
  rw [isLocallyFiniteChain_iff]
  intro y
  obtain ⟨V, hV, hfin⟩ := himg y
  refine ⟨V, hV, (hfin.biUnion fun σ _ ↦ finite_setOf_matrixCoeff_ne_zero A σ (c σ)).subset ?_⟩
  rintro ρ ⟨hρ, z, hz, hzV⟩
  obtain ⟨σ, hσ⟩ := not_forall.1 (mt finsum_eq_zero_of_forall_eq_zero hρ)
  obtain ⟨w, hw, rfl⟩ := hgA ρ σ (c σ) hσ hz
  have hcσ : c σ ≠ 0 := fun h ↦ hσ (by simp only [h, map_zero])
  exact Set.mem_biUnion (x := σ) ⟨_, ⟨w, ⟨hcσ, hw⟩, rfl⟩, hzV⟩ hσ

/-- Extension to a locally finite chain respects addition of properly supported operators.
The two operators need not move simplices along the same proper map. -/
lemma extendLocallyFiniteFun_add
    {B : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b}
    (hA : IsProperlySupported A) (hB : IsProperlySupported B)
    (hc : IsLocallyFiniteChain L c) :
    extendLocallyFiniteFun (A + B) c =
      extendLocallyFiniteFun A c + extendLocallyFiniteFun B c := by
  funext ρ
  simp only [extendLocallyFiniteFun, matrixCoeff_apply, ModuleCat.hom_add,
    LinearMap.add_apply, map_add, Pi.add_apply]
  exact finsum_add_distrib (hA.finite_support hc ρ) (hB.finite_support hc ρ)

/-- Extension to a locally finite chain respects subtraction of properly supported operators. -/
lemma extendLocallyFiniteFun_sub
    {B : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b}
    (hA : IsProperlySupported A) (hB : IsProperlySupported B)
    (hc : IsLocallyFiniteChain L c) :
    extendLocallyFiniteFun (A - B) c =
      extendLocallyFiniteFun A c - extendLocallyFiniteFun B c := by
  funext ρ
  simp only [extendLocallyFiniteFun, matrixCoeff_apply, ModuleCat.hom_sub,
    LinearMap.sub_apply, map_sub, Pi.sub_apply]
  exact finsum_sub_distrib (hA.finite_support hc ρ) (hB.finite_support hc ρ)

/-- The extension of a properly supported map to locally finite chains, applying it simplex by
simplex. -/
def extendLocallyFinite (hA : IsProperlySupported A) :
    locallyFiniteChains L a →ₗ[R] locallyFiniteChains K b where
  toFun c := ⟨extendLocallyFiniteFun A c, mem_locallyFiniteChains.2 <|
    hA.isLocallyFiniteChain_extendLocallyFiniteFun (mem_locallyFiniteChains.1 c.2)⟩
  map_add' c c' := Subtype.ext <| funext fun ρ ↦ by
    simp only [Submodule.coe_add, Pi.add_apply, extendLocallyFiniteFun, map_add]
    exact finsum_add_distrib (hA.finite_support (mem_locallyFiniteChains.1 c.2) ρ)
      (hA.finite_support (mem_locallyFiniteChains.1 c'.2) ρ)
  map_smul' r c := Subtype.ext <| funext fun ρ ↦ by
    simp only [SetLike.val_smul, Pi.smul_apply, extendLocallyFiniteFun, map_smul, RingHom.id_apply]
    exact (smul_finsum' r (hA.finite_support (mem_locallyFiniteChains.1 c.2) ρ)).symm

/-- The underlying coefficients of the extension of a properly supported map. -/
@[simp]
lemma coe_extendLocallyFinite (hA : IsProperlySupported A) (c : locallyFiniteChains L a) :
    (extendLocallyFinite hA c : ∀ ρ : (TopCat.toSSet.obj Y) _⦋b⦌, K.obj (initialVertex ρ)) =
      extendLocallyFiniteFun A c :=
  (rfl)

/-- Extension preserves an additive identity among properly supported operators, even when the
operators move simplices along different proper maps. -/
lemma extendLocallyFinite_eq_add
    {B C : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b}
    (hA : IsProperlySupported A) (hB : IsProperlySupported B) (hC : IsProperlySupported C)
    (h : A = B + C) :
    extendLocallyFinite hA = extendLocallyFinite hB + extendLocallyFinite hC := by
  refine LinearMap.ext fun ⟨c, hc⟩ ↦ Subtype.ext ?_
  simp only [LinearMap.add_apply, Submodule.coe_add, coe_extendLocallyFinite]
  rw [h, extendLocallyFiniteFun_add hB hC (mem_locallyFiniteChains.mp hc)]

/-- Extension preserves a difference-equals-sum identity among properly supported operators.
No common proper map controlling all four operators is required. -/
lemma extendLocallyFinite_sub_eq_add
    {B C D : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b}
    (hA : IsProperlySupported A) (hB : IsProperlySupported B)
    (hC : IsProperlySupported C) (hD : IsProperlySupported D) (h : A - B = C + D) :
    extendLocallyFinite hA - extendLocallyFinite hB =
      extendLocallyFinite hC + extendLocallyFinite hD := by
  refine LinearMap.ext fun ⟨c, hc⟩ ↦ Subtype.ext ?_
  replace hc := mem_locallyFiniteChains.mp hc
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Submodule.coe_sub, Submodule.coe_add,
    coe_extendLocallyFinite]
  rw [← extendLocallyFiniteFun_sub hA hB hc, h, extendLocallyFiniteFun_add hC hD hc]

/-- Extending a composite is the composite of the extensions. -/
lemma extendLocallyFiniteFun_extendLocallyFiniteFun
    {B : (twistedChainComplex K).X b ⟶ (twistedChainComplex J).X e}
    (hA : IsProperlySupported A) (hB : IsProperlySupported B) (hc : IsLocallyFiniteChain L c) :
    extendLocallyFiniteFun B (extendLocallyFiniteFun A c) = extendLocallyFiniteFun (A ≫ B) c := by
  obtain ⟨g, hg, hgA⟩ := hA
  obtain ⟨g', hg', hgB⟩ := hB
  funext ρ
  -- Every nonzero term involves a simplex `σ` of `c` meeting the fibre of `g' ∘ g` over a point
  -- of `ρ`; there are finitely many of them.
  set S := (hc.finite_setOf_inter_nonempty ((hg'.comp hg).isCompact_preimage
    (isCompact_singleton (x := TopCat.simplexMap ρ (toTopInitialVertex _))))).toFinset
  have hsupp : ∀ τ σ, matrixCoeff B ρ τ (matrixCoeff A τ σ (c σ)) ≠ 0 → σ ∈ S := by
    intro τ σ h
    have hA' : matrixCoeff A τ σ (c σ) ≠ 0 := fun h' ↦ h (by simp only [h', map_zero])
    obtain ⟨q, hq, hgq⟩ := hgB ρ τ _ h ⟨_, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hgA τ σ (c σ) hA' hq
    exact (Set.Finite.mem_toFinset _).2 ⟨fun h' ↦ hA' (by simp only [h', map_zero]), z, hz, hgq⟩
  have hτ : ∀ σ ∈ S, (Function.support fun τ ↦
      matrixCoeff B ρ τ (matrixCoeff A τ σ (c σ))).Finite := fun σ _ ↦
    (finite_setOf_matrixCoeff_ne_zero A σ (c σ)).subset fun τ hτ h ↦ hτ (by simp only [h, map_zero])
  simp only [extendLocallyFiniteFun]
  rw [finsum_congr fun τ ↦ map_finsum _
      (IsProperlySupported.finite_support ⟨g, hg, hgA⟩ hc τ),
    finsum_congr fun τ ↦ finsum_eq_sum_of_support_subset _ fun σ hσ ↦ hsupp τ σ hσ,
    ← sum_finsum_comm _ _ hτ, finsum_eq_sum_of_support_subset _ fun σ hσ ↦ ?_]
  · exact Finset.sum_congr rfl fun σ _ ↦ (matrixCoeff_comp_apply A B ρ σ (c σ)).symm
  · rw [Function.mem_support, matrixCoeff_comp_apply] at hσ
    obtain ⟨τ, hτ⟩ := not_forall.1 (mt finsum_eq_zero_of_forall_eq_zero hσ)
    exact hsupp τ σ hτ

/-- Extending a composite of properly supported maps gives the composite of the extensions. -/
lemma extendLocallyFinite_comp {B : (twistedChainComplex K).X b ⟶ (twistedChainComplex J).X e}
    (hA : IsProperlySupported A) (hB : IsProperlySupported B) :
    extendLocallyFinite hB ∘ₗ extendLocallyFinite hA = extendLocallyFinite (hA.comp hB) :=
  LinearMap.ext fun c ↦ Subtype.ext <|
    extendLocallyFiniteFun_extendLocallyFiniteFun hA hB (mem_locallyFiniteChains.1 c.2)

/-- Extending the identity gives the identity. -/
@[simp]
lemma extendLocallyFiniteFun_id :
    extendLocallyFiniteFun (𝟙 ((twistedChainComplex L).X a)) c = c :=
  funext fun ρ ↦ by
    rw [extendLocallyFiniteFun_apply, finsum_eq_single _ ρ fun σ hσ ↦ by
      simp [matrixCoeff_apply, twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne L hσ]]
    simp [matrixCoeff_apply]

/-- The extension of the identity is the identity. -/
@[simp]
lemma extendLocallyFinite_id (h : IsProperlySupported (𝟙 ((twistedChainComplex L).X a))) :
    extendLocallyFinite h = LinearMap.id :=
  LinearMap.ext fun c ↦ Subtype.ext <| (coe_extendLocallyFinite h c).trans extendLocallyFiniteFun_id

/-- The twisted boundary moves simplices along the identity: it only involves faces. -/
lemma movesAlong_d (k : ℕ) : MovesAlong (𝟙 X) ((twistedChainComplex L).d (k + 1) k) := by
  intro ρ σ x hx
  obtain ⟨i, rfl⟩ :
      ∃ i : Fin (k + 2), (TopCat.toSSet.obj X).map (SimplexCategory.δ i).op σ = ρ := by
    by_contra! hne
    exact hx (by
      simp [matrixCoeff, ιTwistedChainComplex_d_twistedChainComplexCoeff_of_forall_ne L hne])
  rw [TopCat.hom_id, ContinuousMap.coe_id, Set.image_id]
  exact TopCat.range_simplexMap_map_subset _ σ

/-- The twisted boundary is properly supported: it moves simplices along the identity. -/
lemma isProperlySupported_d (k : ℕ) :
    IsProperlySupported ((twistedChainComplex L).d (k + 1) k) :=
  .of_movesAlong isProperMap_id (movesAlong_d k)

end Extension

section LocallyFiniteBoundary

variable {L} {k : ℕ}

variable (L) in
/-- The coefficients of the boundary of a family of coefficients on singular `(k + 1)`-simplices.
The coefficient on a `k`-simplex `ρ` is the sum, over all `(k + 1)`-simplices `σ`, of the
coefficient on `ρ` of the twisted boundary of the chain supported on `σ` with coefficient `c σ`. -/
def locallyFiniteBoundaryFun (c : ∀ σ : (TopCat.toSSet.obj X) _⦋k + 1⦌, L.obj (initialVertex σ))
    (ρ : (TopCat.toSSet.obj X) _⦋k⦌) : L.obj (initialVertex ρ) :=
  extendLocallyFiniteFun ((twistedChainComplex L).d (k + 1) k) c ρ

/-- The locally finite boundary is the extension of the twisted boundary. -/
lemma extendLocallyFiniteFun_d (c : ∀ σ : (TopCat.toSSet.obj X) _⦋k + 1⦌, L.obj (initialVertex σ)) :
    extendLocallyFiniteFun ((twistedChainComplex L).d (k + 1) k) c = locallyFiniteBoundaryFun L c :=
  (rfl)

/-- The boundary of a locally finite chain is locally finite. -/
lemma IsLocallyFiniteChain.locallyFiniteBoundaryFun
    {c : ∀ σ : (TopCat.toSSet.obj X) _⦋k + 1⦌, L.obj (initialVertex σ)}
    (hc : IsLocallyFiniteChain L c) :
    IsLocallyFiniteChain L (locallyFiniteBoundaryFun L c) :=
  (isProperlySupported_d k).isLocallyFiniteChain_extendLocallyFiniteFun hc

variable (L k) in
/-- The boundary of locally finite singular `(k + 1)`-chains with coefficients in `L`. -/
def locallyFiniteBoundary : locallyFiniteChains L (k + 1) →ₗ[R] locallyFiniteChains L k :=
  extendLocallyFinite (isProperlySupported_d k)

/-- The locally finite boundary is the extension of the twisted boundary as a linear map. -/
lemma locallyFiniteBoundary_def :
    locallyFiniteBoundary L k = extendLocallyFinite (isProperlySupported_d k) := (rfl)

/-- The underlying coefficients of the boundary of a locally finite chain. -/
@[simp]
lemma coe_locallyFiniteBoundary (c : locallyFiniteChains L (k + 1)) :
    (locallyFiniteBoundary L k c : ∀ τ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex τ)) =
      locallyFiniteBoundaryFun L c :=
  (rfl)

/-- The coefficient of the boundary of a family of coefficients on a `k`-simplex `ρ` is the sum,
over all `(k + 1)`-simplices `σ`, of the coefficient on `ρ` of the twisted boundary of the chain
supported on `σ`. For a locally finite family only finitely many terms are nonzero. -/
lemma locallyFiniteBoundaryFun_apply
    (c : ∀ σ : (TopCat.toSSet.obj X) _⦋k + 1⦌, L.obj (initialVertex σ))
    (ρ : (TopCat.toSSet.obj X) _⦋k⦌) :
    locallyFiniteBoundaryFun L c ρ =
      ∑ᶠ σ, (twistedChainComplexCoeff L ρ).hom (((twistedChainComplex L).d (k + 1) k).hom
        ((ιTwistedChainComplex L (k + 1) σ).hom (c σ))) := by
  simp only [locallyFiniteBoundaryFun, extendLocallyFiniteFun, matrixCoeff_apply]

/-- The boundary of locally finite chains squares to zero. -/
@[simp]
lemma locallyFiniteBoundary_comp_locallyFiniteBoundary :
    locallyFiniteBoundary L k ∘ₗ locallyFiniteBoundary L (k + 1) = 0 := by
  refine LinearMap.ext fun ⟨c, hc⟩ ↦ Subtype.ext ?_
  rw [LinearMap.comp_apply, coe_locallyFiniteBoundary, coe_locallyFiniteBoundary,
    ← extendLocallyFiniteFun_d, ← extendLocallyFiniteFun_d,
    extendLocallyFiniteFun_extendLocallyFiniteFun (isProperlySupported_d _)
      (isProperlySupported_d _) hc,
    HomologicalComplex.d_comp_d]
  funext ρ
  simp [extendLocallyFiniteFun, matrixCoeff_apply]

end LocallyFiniteBoundary

section LocallyFiniteSum

/-! A family of finite chains whose supports form a locally finite family of sets has a locally
finite sum, obtained by adding coefficients simplex by simplex. The boundary of the sum is the sum
of the boundaries. -/

variable {L} {k : ℕ} {ι : Type*}

/-- The coefficients of the sum of a family of twisted chains: the coefficient on `ρ` is the sum
of the coefficients on `ρ` of the members of the family. It is a locally finite chain when the
supports of the members form a locally finite family
(`isLocallyFiniteChain_locallyFiniteSumFun`). -/
def locallyFiniteSumFun (y : ι → (twistedChainComplex L).X k)
    (ρ : (TopCat.toSSet.obj X) _⦋k⦌) : L.obj (initialVertex ρ) :=
  ∑ᶠ j, (twistedChainComplexCoeff L ρ).hom (y j)

/-- The coefficient on `ρ` of the sum of a family of twisted chains is the sum of their
coefficients on `ρ`. -/
lemma locallyFiniteSumFun_apply (y : ι → (twistedChainComplex L).X k)
    (ρ : (TopCat.toSSet.obj X) _⦋k⦌) :
    locallyFiniteSumFun y ρ = ∑ᶠ j, (twistedChainComplexCoeff L ρ).hom (y j) :=
  (rfl)

variable {y : ι → (twistedChainComplex L).X k} {A : ι → Set X}

/-- If the members of a family of twisted chains are supported in the members of a locally finite
family of sets, only finitely many of them have a nonzero coefficient on a given simplex. -/
lemma finite_setOf_twistedChainComplexCoeff_ne_zero (hA : LocallyFinite A)
    (hy : ∀ j σ, (twistedChainComplexCoeff L σ).hom (y j) ≠ 0 →
      Set.range (TopCat.simplexMap σ) ⊆ A j)
    (ρ : (TopCat.toSSet.obj X) _⦋k⦌) :
    {j | (twistedChainComplexCoeff L ρ).hom (y j) ≠ 0}.Finite :=
  (hA.point_finite (TopCat.simplexMap ρ (toTopInitialVertex _))).subset fun j hj ↦
    hy j ρ hj ⟨_, rfl⟩

/-- The sum of a family of twisted chains supported in the members of a locally finite family of
sets is a locally finite chain. -/
lemma isLocallyFiniteChain_locallyFiniteSumFun (hA : LocallyFinite A)
    (hy : ∀ j σ, (twistedChainComplexCoeff L σ).hom (y j) ≠ 0 →
      Set.range (TopCat.simplexMap σ) ⊆ A j) :
    IsLocallyFiniteChain L (locallyFiniteSumFun y) := by
  rw [isLocallyFiniteChain_iff]
  intro x
  obtain ⟨U, hU, hfin⟩ := hA x
  refine ⟨U, hU, (hfin.biUnion fun j _ ↦ finite_support_twistedChainComplexCoeff L (y j)).subset ?_⟩
  rintro σ ⟨hσ, z, hz, hzU⟩
  obtain ⟨j, hj⟩ := not_forall.1 (mt finsum_eq_zero_of_forall_eq_zero hσ)
  exact Set.mem_biUnion (x := j) ⟨z, hy j σ hj hz, hzU⟩ hj

/-- The boundary of the sum of a family of twisted chains supported in the members of a locally
finite family of sets is the sum of their boundaries. -/
lemma locallyFiniteBoundaryFun_locallyFiniteSumFun {y : ι → (twistedChainComplex L).X (k + 1)}
    (hA : LocallyFinite A)
    (hy : ∀ j σ, (twistedChainComplexCoeff L σ).hom (y j) ≠ 0 →
      Set.range (TopCat.simplexMap σ) ⊆ A j) :
    locallyFiniteBoundaryFun L (locallyFiniteSumFun y) =
      locallyFiniteSumFun fun j ↦ ((twistedChainComplex L).d (k + 1) k).hom (y j) := by
  funext ρ
  -- Every nonzero term involves a member of the family whose support contains the initial vertex
  -- of `ρ`; there are finitely many of them.
  set J := (hA.point_finite (TopCat.simplexMap ρ (toTopInitialVertex _))).toFinset
  have hJ : ∀ σ j, matrixCoeff ((twistedChainComplex L).d (k + 1) k) ρ σ
      ((twistedChainComplexCoeff L σ).hom (y j)) ≠ 0 → j ∈ J := by
    intro σ j h
    have hσ : (twistedChainComplexCoeff L σ).hom (y j) ≠ 0 := fun h' ↦ h (by simp [h'])
    obtain ⟨w, hw, hwρ⟩ := movesAlong_d k ρ σ _ h ⟨_, rfl⟩
    rw [TopCat.hom_id, ContinuousMap.coe_id, id] at hwρ
    exact (Set.Finite.mem_toFinset _).2 (hwρ ▸ hy j σ hσ hw)
  have hfin : ∀ j ∈ J, (Function.support fun σ ↦
      matrixCoeff ((twistedChainComplex.{u, v, w} L).d (k + 1) k) ρ σ
        ((twistedChainComplexCoeff L σ).hom (y j))).Finite := fun j _ ↦
    (finite_support_twistedChainComplexCoeff L (y j)).subset fun σ hσ h ↦
      hσ (by simp only [h, map_zero])
  simp only [locallyFiniteBoundaryFun, extendLocallyFiniteFun, locallyFiniteSumFun]
  rw [finsum_congr fun σ ↦ map_finsum _
      (finite_setOf_twistedChainComplexCoeff_ne_zero hA hy σ),
    finsum_congr fun σ ↦ finsum_eq_sum_of_support_subset _ fun j hj ↦ hJ σ j hj,
    ← sum_finsum_comm _ _ hfin, finsum_eq_sum_of_support_subset _ fun j hj ↦ ?_]
  · exact Finset.sum_congr rfl fun j _ ↦ finsum_matrixCoeff _ _ _
  · rw [Function.mem_support, ← finsum_matrixCoeff] at hj
    obtain ⟨σ, hσ⟩ := not_forall.1 (mt finsum_eq_zero_of_forall_eq_zero hj)
    exact hJ σ j hσ

/-- The sum of a family of twisted chains supported in the members of a locally finite family of
sets, as a locally finite chain. -/
def locallyFiniteSum (hA : LocallyFinite A)
    (hy : ∀ j σ, (twistedChainComplexCoeff L σ).hom (y j) ≠ 0 →
      Set.range (TopCat.simplexMap σ) ⊆ A j) :
    locallyFiniteChains L k :=
  ⟨locallyFiniteSumFun y, isLocallyFiniteChain_locallyFiniteSumFun hA hy⟩

/-- The underlying coefficients of the locally finite sum of a family of twisted chains. -/
@[simp]
lemma coe_locallyFiniteSum (hA : LocallyFinite A)
    (hy : ∀ j σ, (twistedChainComplexCoeff L σ).hom (y j) ≠ 0 →
      Set.range (TopCat.simplexMap σ) ⊆ A j) :
    (locallyFiniteSum hA hy : ∀ ρ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex ρ)) =
      locallyFiniteSumFun y :=
  (rfl)

/-- The boundary of the locally finite sum of a family of twisted chains supported in the members
of a locally finite family of sets is the locally finite sum of their boundaries. -/
lemma locallyFiniteBoundary_locallyFiniteSum {y : ι → (twistedChainComplex L).X (k + 1)}
    (hA : LocallyFinite A)
    (hy : ∀ j σ, (twistedChainComplexCoeff L σ).hom (y j) ≠ 0 →
      Set.range (TopCat.simplexMap σ) ⊆ A j) :
    locallyFiniteBoundary L k (locallyFiniteSum hA hy) =
      locallyFiniteSum hA fun j _ ↦
        range_simplexMap_subset_of_twistedChainComplexCoeff_d_ne_zero L (hy j) :=
  Subtype.ext (locallyFiniteBoundaryFun_locallyFiniteSumFun hA hy)

end LocallyFiniteSum

section Complex

/-- The chain complex of locally finite singular chains of `X` with coefficients in `L`. -/
def locallyFiniteChainComplex : ChainComplex (ModuleCat.{max v w} R) ℕ :=
  ChainComplex.of (fun k ↦ ModuleCat.of R (locallyFiniteChains L k))
    (fun k ↦ ModuleCat.ofHom (locallyFiniteBoundary L k))
    fun k ↦ ModuleCat.hom_ext (locallyFiniteBoundary_comp_locallyFiniteBoundary (L := L) (k := k))

/-- The degree-`k` term of the locally finite chain complex is the module of locally finite
`k`-chains. -/
lemma locallyFiniteChainComplex_X (k : ℕ) :
    (locallyFiniteChainComplex L).X k = ModuleCat.of R (locallyFiniteChains L k) :=
  (rfl)

/-- The differential of the locally finite chain complex is the locally finite boundary. -/
@[simp]
lemma locallyFiniteChainComplex_d (k : ℕ) :
    (locallyFiniteChainComplex L).d (k + 1) k =
      eqToHom (locallyFiniteChainComplex_X L (k + 1)) ≫
        ModuleCat.ofHom (locallyFiniteBoundary L k) ≫
          eqToHom (locallyFiniteChainComplex_X L k).symm := by
  simp only [locallyFiniteChainComplex, ChainComplex.of_d]
  rfl

/-- Borel–Moore homology of `X` with coefficients in the local coefficient system `L`: the
homology of the complex of locally finite singular chains. -/
abbrev borelMooreHomology (k : ℕ) : ModuleCat.{max v w} R :=
  (locallyFiniteChainComplex L).homology k

end Complex

section Comparison

variable {k : ℕ}

open Classical in
/-- The locally finite chain supported on a single simplex. -/
private def singleChain (σ : (TopCat.toSSet.obj X) _⦋k⦌) :
    L.obj (initialVertex σ) →ₗ[R] locallyFiniteChains L k :=
  LinearMap.codRestrict _ (LinearMap.single R (fun τ ↦ L.obj (initialVertex τ)) σ) fun x ↦
    mem_locallyFiniteChains.2 <| isLocallyFiniteChain_of_finite <|
      (Set.finite_singleton σ).subset fun τ hτ ↦
        Set.mem_singleton_iff.2 <| by_contra fun h ↦ hτ <| by
          rw [LinearMap.coe_single, Pi.single_eq_of_ne h]

open Classical in
private lemma coe_singleChain_apply (σ : (TopCat.toSSet.obj X) _⦋k⦌)
    (x : L.obj (initialVertex σ)) :
    (singleChain L σ x : ∀ τ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex τ)) =
      Pi.single σ x := by
  rw [singleChain, LinearMap.codRestrict_apply, LinearMap.coe_single]

variable (k) in
/-- The inclusion of twisted chains into locally finite chains, sending a finite chain to its
family of coefficients. -/
def toLocallyFiniteChains :
    (twistedChainComplex L).X k ⟶ ModuleCat.of R (locallyFiniteChains L k) :=
  twistedChainComplexDesc L fun σ ↦ ModuleCat.ofHom (singleChain L σ)

/-- The locally finite chain underlying a twisted chain has the same coefficients. -/
@[simp]
lemma toLocallyFiniteChains_apply (y : (twistedChainComplex L).X k)
    (ρ : (TopCat.toSSet.obj X) _⦋k⦌) :
    ((toLocallyFiniteChains L k).hom y : ∀ τ : (TopCat.toSSet.obj X) _⦋k⦌,
      L.obj (initialVertex τ)) ρ = (twistedChainComplexCoeff L ρ).hom y := by
  classical
  let π : ModuleCat.of R (locallyFiniteChains L k) ⟶ L.obj (initialVertex ρ) :=
    ModuleCat.ofHom ((LinearMap.proj ρ).comp (locallyFiniteChains L k).subtype)
  suffices toLocallyFiniteChains L k ≫ π = twistedChainComplexCoeff L ρ from
    congrArg (fun f ↦ f.hom y) this
  refine twistedChainComplex_hom_ext L fun σ ↦ ModuleCat.hom_ext <| LinearMap.ext fun x ↦ ?_
  simp only [toLocallyFiniteChains, ιTwistedChainComplex_twistedChainComplexDesc_assoc,
    ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, π, Submodule.subtype_apply,
    LinearMap.proj_apply, coe_singleChain_apply]
  by_cases h : σ = ρ
  · subst h
    simp
  · rw [Pi.single_eq_of_ne' h, twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne L h]

variable {L} in
/-- On a finite chain, the extension of a map of twisted chains is that map. -/
lemma extendLocallyFiniteFun_toLocallyFiniteChains {Y : TopCat.{v}}
    {K : LocalCoefficientSystem.{u, v, max v w} R Y} {b : ℕ}
    (A : (twistedChainComplex L).X k ⟶ (twistedChainComplex K).X b)
    (y : (twistedChainComplex L).X k) :
    extendLocallyFiniteFun A ((toLocallyFiniteChains L k).hom y : ∀ σ, L.obj (initialVertex σ)) =
      ((toLocallyFiniteChains K b).hom (A.hom y) : ∀ ρ, K.obj (initialVertex ρ)) :=
  funext fun ρ ↦ by
    rw [extendLocallyFiniteFun_apply, toLocallyFiniteChains_apply, ← finsum_matrixCoeff A y ρ]
    exact finsum_congr fun σ ↦ by rw [toLocallyFiniteChains_apply]

/-- Each twisted chain is sent to a locally finite chain with the same coefficients, and this
commutes with the boundaries. -/
@[reassoc]
lemma toLocallyFiniteChains_comp_locallyFiniteBoundary :
    toLocallyFiniteChains L (k + 1) ≫ ModuleCat.ofHom (locallyFiniteBoundary L k) =
      (twistedChainComplex L).d (k + 1) k ≫ toLocallyFiniteChains L k := by
  classical
  refine twistedChainComplex_hom_ext L fun σ ↦ ModuleCat.hom_ext <| LinearMap.ext fun x ↦
    Subtype.ext <| funext fun ρ ↦ ?_
  simp only [toLocallyFiniteChains, ιTwistedChainComplex_twistedChainComplexDesc_assoc,
    ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, coe_locallyFiniteBoundary,
    locallyFiniteBoundaryFun_apply, coe_singleChain_apply]
  rw [← toLocallyFiniteChains, toLocallyFiniteChains_apply,
    finsum_eq_single _ σ fun τ hτ ↦ by rw [Pi.single_eq_of_ne hτ, map_zero, map_zero, map_zero],
    Pi.single_eq_same]

/-- The chain map from twisted chains to locally finite chains. -/
def toLocallyFiniteChainComplex : twistedChainComplex L ⟶ locallyFiniteChainComplex L where
  f k := toLocallyFiniteChains L k ≫ eqToHom (locallyFiniteChainComplex_X L k).symm
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    simp [locallyFiniteChainComplex_d, ← toLocallyFiniteChains_comp_locallyFiniteBoundary_assoc]

/-- The components of the chain map to locally finite chains are the inclusions of finite
chains. -/
@[simp]
lemma toLocallyFiniteChainComplex_f (k : ℕ) :
    (toLocallyFiniteChainComplex L).f k =
      toLocallyFiniteChains L k ≫ eqToHom (locallyFiniteChainComplex_X L k).symm :=
  (rfl)

variable (k) in
/-- The map from twisted singular homology to Borel–Moore homology induced by regarding finite
chains as locally finite chains. -/
abbrev twistedHomologyToBorelMooreHomology : twistedHomology L k ⟶ borelMooreHomology L k :=
  HomologicalComplex.homologyMap (toLocallyFiniteChainComplex L) k

/-- On a compact space, every locally finite chain comes from a unique twisted chain. -/
lemma bijective_toLocallyFiniteChains [CompactSpace X] :
    Function.Bijective (toLocallyFiniteChains L k).hom := by
  classical
  refine ⟨fun y y' h ↦ twistedChainComplex_ext_coeff L fun ρ ↦ ?_, fun ⟨c, hc⟩ ↦ ?_⟩
  · rw [← toLocallyFiniteChains_apply, ← toLocallyFiniteChains_apply, h]
  · let S := (IsLocallyFiniteChain.finite_setOf_ne_zero (mem_locallyFiniteChains.1 hc)).toFinset
    refine ⟨∑ σ ∈ S, (ιTwistedChainComplex L k σ).hom (c σ), Subtype.ext <| funext fun ρ ↦ ?_⟩
    rw [toLocallyFiniteChains_apply]
    exact twistedChainComplexCoeff_sum_ιTwistedChainComplex_apply L c fun hρ ↦ by
      simpa [S] using hρ

/-- On a compact space, the inclusion of twisted chains into locally finite chains is an
isomorphism of chain complexes. -/
instance isIso_toLocallyFiniteChainComplex [CompactSpace X] :
    IsIso (toLocallyFiniteChainComplex L) := by
  have (k : ℕ) : IsIso ((toLocallyFiniteChainComplex L).f k) := by
    rw [toLocallyFiniteChainComplex_f]
    have := (ConcreteCategory.isIso_iff_bijective _).2 (bijective_toLocallyFiniteChains L (k := k))
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

variable (k) in
/-- On a compact space, twisted singular homology is isomorphic to Borel–Moore homology, through
the map induced by regarding finite chains as locally finite chains. -/
def twistedHomologyIsoBorelMooreHomology [CompactSpace X] :
    twistedHomology L k ≅ borelMooreHomology L k :=
  asIso (twistedHomologyToBorelMooreHomology L k)

/-- The isomorphism between twisted singular homology and Borel–Moore homology on a compact space
is induced by the inclusion of finite chains. -/
@[simp]
lemma twistedHomologyIsoBorelMooreHomology_hom [CompactSpace X] :
    (twistedHomologyIsoBorelMooreHomology L k).hom = twistedHomologyToBorelMooreHomology L k :=
  (rfl)

end Comparison

end LocalCoefficientSystem

end TauCeti
