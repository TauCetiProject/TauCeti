/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Basic
public import TauCeti.Topology.LocallyFinite
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Functoriality of Borel–Moore homology with local coefficients

Locally finite singular chains are covariant for proper maps and for morphisms of local coefficient
systems. A proper map `f : X ⟶ Y` and a local coefficient system `L` on `Y` give a chain map
`locallyFiniteChainComplexMap f hf L` from the locally finite chains of `X` with coefficients in the
pullback `f⁎L` to those of `Y` with coefficients in `L`. It sends a chain `∑ c_σ σ` to
`∑ c_σ (f ∘ σ)`: the coefficient on a simplex `ρ` of `Y` is the sum of the coefficients of the
simplices `σ` with `f ∘ σ = ρ`. These all meet the fibre of `f` over a point of `ρ`, which is
compact, so the sum is finite. Images of a locally finite family of sets under a closed map with
compact fibres form a locally finite family (`LocallyFinite.image_of_isClosedMap`), so the
pushed-forward chain is again locally finite. Properness is needed: the map from `ℝ` to a point
sends each of the infinitely many intervals `[n, n + 1]` of a locally finite chain of `ℝ` to the
same constant simplex.

A morphism of local coefficient systems `η : L ⟶ K` acts on locally finite chains coefficientwise,
giving `locallyFiniteChainComplexCoefficientMap η`.

Both constructions extend the corresponding maps of ordinary twisted chains: the inclusion
`toLocallyFiniteChainComplex` of finite chains into locally finite chains is natural for them. They
satisfy the identity and composition laws of their twisted counterparts, and the proper pushforward
is natural in the coefficient system. On homology they give `borelMooreHomologyMap` and
`borelMooreHomologyCoefficientMap`.

## Main declarations

* `TauCeti.LocalCoefficientSystem.locallyFiniteChainsMap`: the proper pushforward of locally
  finite chains, `locallyFiniteChainComplexMap` the chain map it forms and
  `borelMooreHomologyMap` the induced map on Borel–Moore homology.
* `TauCeti.LocalCoefficientSystem.locallyFiniteChainsCoefficientMap`: the change of coefficients
  of locally finite chains, with `locallyFiniteChainComplexCoefficientMap` and
  `borelMooreHomologyCoefficientMap`.
* `TauCeti.LocalCoefficientSystem.toLocallyFiniteChainComplex_comp_locallyFiniteChainComplexMap`
  and `toLocallyFiniteChainComplex_comp_locallyFiniteChainComplexCoefficientMap`: the inclusion of
  finite chains is natural for both.

## Implementation notes

All these maps are built uniformly. A map `A` of twisted chains which moves each simplex along a
proper map extends to locally finite chains by applying it simplex by simplex: the coefficient of
the extension on `ρ` is the sum over all `σ` of the coefficient on `ρ` of `A` applied to the chain
supported on `σ`. The locally finite boundary is the extension of the twisted boundary, and
extension takes composites to composites, so the extension of a chain map is a chain map.

## References

* A. Borel and J. C. Moore, *Homology theory for locally compact spaces*, Michigan Math. J. 7
  (1960), 137–159.
* G. E. Bredon, *Sheaf Theory*, 2nd ed., Graduate Texts in Mathematics 170, Chapter V.
-/

public section

noncomputable section

open CategoryTheory Limits SimplexCategory Topology

open scoped Simplicial

universe u v w

namespace TauCeti

namespace LocalCoefficientSystem

variable {R : Type u} [Ring R] {X Y Z : TopCat.{v}}

section Extension

variable {L : LocalCoefficientSystem.{u, v, max v w} R X}
  {K : LocalCoefficientSystem.{u, v, max v w} R Y}
  {J : LocalCoefficientSystem.{u, v, max v w} R Z} {a b e : ℕ}

/-- The coefficient on `ρ` of the image under `A` of the chain supported on `σ`. -/
private def matrixCoeff (A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b)
    (ρ : (TopCat.toSSet.obj Y) _⦋b⦌) (σ : (TopCat.toSSet.obj X) _⦋a⦌) :
    L.obj (initialVertex σ) →ₗ[R] K.obj (initialVertex ρ) :=
  (ιTwistedChainComplex L a σ ≫ A ≫ twistedChainComplexCoeff K ρ).hom

private lemma matrixCoeff_apply (A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b)
    (ρ : (TopCat.toSSet.obj Y) _⦋b⦌) (σ : (TopCat.toSSet.obj X) _⦋a⦌)
    (x : L.obj (initialVertex σ)) :
    matrixCoeff A ρ σ x =
      (twistedChainComplexCoeff K ρ).hom (A.hom ((ιTwistedChainComplex L a σ).hom x)) :=
  (rfl)

/-- A map of twisted chains moves simplices along `g` when the image of a chain supported on a
simplex `σ` only involves simplices whose image lies in the image of `σ` under `g`. -/
private def MovesAlong (g : X ⟶ Y)
    (A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b) : Prop :=
  ∀ ρ σ (x : L.obj (initialVertex σ)), matrixCoeff A ρ σ x ≠ 0 →
    Set.range (TopCat.simplexMap ρ) ⊆ g.hom '' Set.range (TopCat.simplexMap σ)

/-- A map of twisted chains is properly supported when it moves simplices along a proper map. -/
private def IsProperlySupported
    (A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b) : Prop :=
  ∃ g : X ⟶ Y, IsProperMap g.hom ∧ MovesAlong g A

/-- The coefficients of the chain obtained by applying `A` simplex by simplex. -/
private def extendFun (A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b)
    (c : ∀ σ : (TopCat.toSSet.obj X) _⦋a⦌, L.obj (initialVertex σ))
    (ρ : (TopCat.toSSet.obj Y) _⦋b⦌) : K.obj (initialVertex ρ) :=
  ∑ᶠ σ, matrixCoeff A ρ σ (c σ)

/-- Summing the coefficients of `A` against the coefficients of a twisted chain `y` gives the
coefficients of `A y`. -/
private lemma finsum_matrixCoeff (A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b)
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
private lemma MovesAlong.comp {g : X ⟶ Y} {g' : Y ⟶ Z}
    {A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b}
    {B : (twistedChainComplex K).X b ⟶ (twistedChainComplex J).X e}
    (hA : MovesAlong g A) (hB : MovesAlong g' B) : MovesAlong (g ≫ g') (A ≫ B) := by
  intro ρ σ x hx
  rw [matrixCoeff_comp_apply] at hx
  obtain ⟨τ, hτ⟩ : ∃ τ, matrixCoeff B ρ τ (matrixCoeff A τ σ x) ≠ 0 := by
    by_contra! h
    exact hx (finsum_eq_zero_of_forall_eq_zero h)
  refine (hB ρ τ _ hτ).trans ?_
  rw [TopCat.hom_comp, ContinuousMap.coe_comp, Set.image_comp]
  exact Set.image_mono (hA τ σ x fun h ↦ hτ (by simp only [h, map_zero]))

/-- Composites of properly supported maps are properly supported. -/
private lemma IsProperlySupported.comp
    {A : (twistedChainComplex L).X a ⟶ (twistedChainComplex K).X b}
    {B : (twistedChainComplex K).X b ⟶ (twistedChainComplex J).X e}
    (hA : IsProperlySupported A) (hB : IsProperlySupported B) : IsProperlySupported (A ≫ B) :=
  let ⟨g, hg, hgA⟩ := hA
  let ⟨g', hg', hgB⟩ := hB
  ⟨g ≫ g', by simpa using hg'.comp hg, hgA.comp hgB⟩

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
private lemma IsProperlySupported.isLocallyFiniteChain_extendFun (hA : IsProperlySupported A)
    (hc : IsLocallyFiniteChain L c) : IsLocallyFiniteChain K (extendFun A c) := by
  obtain ⟨g, hg, hgA⟩ := hA
  have himg := (isLocallyFiniteChain_iff_locallyFinite.1 hc).image_of_isClosedMap hg.isClosedMap
    fun _ ↦ hg.isCompact_preimage isCompact_singleton
  rw [isLocallyFiniteChain_iff]
  intro y
  obtain ⟨V, hV, hfin⟩ := himg y
  refine ⟨V, hV, (hfin.biUnion fun σ _ ↦ finite_setOf_matrixCoeff_ne_zero A σ (c σ)).subset ?_⟩
  rintro ρ ⟨hρ, z, hz, hzV⟩
  obtain ⟨σ, hσ⟩ : ∃ σ, matrixCoeff A ρ σ (c σ) ≠ 0 := by
    by_contra! h
    exact hρ (finsum_eq_zero_of_forall_eq_zero h)
  obtain ⟨w, hw, rfl⟩ := hgA ρ σ (c σ) hσ hz
  have hcσ : c σ ≠ 0 := fun h ↦ hσ (by simp only [h, map_zero])
  exact Set.mem_biUnion (x := σ) ⟨_, ⟨w, ⟨hcσ, hw⟩, rfl⟩, hzV⟩ hσ

/-- The extension of a properly supported map to locally finite chains, applying it simplex by
simplex. -/
private def extend (hA : IsProperlySupported A) :
    locallyFiniteChains L a →ₗ[R] locallyFiniteChains K b where
  toFun c := ⟨extendFun A c, mem_locallyFiniteChains.2 <|
    hA.isLocallyFiniteChain_extendFun (mem_locallyFiniteChains.1 c.2)⟩
  map_add' c c' := Subtype.ext <| funext fun ρ ↦ by
    simp only [Submodule.coe_add, Pi.add_apply, extendFun, map_add]
    exact finsum_add_distrib (hA.finite_support (mem_locallyFiniteChains.1 c.2) ρ)
      (hA.finite_support (mem_locallyFiniteChains.1 c'.2) ρ)
  map_smul' r c := Subtype.ext <| funext fun ρ ↦ by
    simp only [SetLike.val_smul, Pi.smul_apply, extendFun, map_smul, RingHom.id_apply]
    exact (smul_finsum' r (hA.finite_support (mem_locallyFiniteChains.1 c.2) ρ)).symm

@[simp]
private lemma coe_extend (hA : IsProperlySupported A) (c : locallyFiniteChains L a) :
    (extend hA c : ∀ ρ : (TopCat.toSSet.obj Y) _⦋b⦌, K.obj (initialVertex ρ)) = extendFun A c :=
  (rfl)

/-- Extending a composite is the composite of the extensions. -/
private lemma extendFun_extendFun
    {B : (twistedChainComplex K).X b ⟶ (twistedChainComplex J).X e}
    (hA : IsProperlySupported A) (hB : IsProperlySupported B) (hc : IsLocallyFiniteChain L c) :
    extendFun B (extendFun A c) = extendFun (A ≫ B) c := by
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
  simp only [extendFun]
  rw [finsum_congr fun τ ↦ map_finsum _
      (IsProperlySupported.finite_support ⟨g, hg, hgA⟩ hc τ),
    finsum_congr fun τ ↦ finsum_eq_sum_of_support_subset _ fun σ hσ ↦ hsupp τ σ hσ,
    ← sum_finsum_comm _ _ hτ, finsum_eq_sum_of_support_subset _ fun σ hσ ↦ ?_]
  · exact Finset.sum_congr rfl fun σ _ ↦ (matrixCoeff_comp_apply A B ρ σ (c σ)).symm
  · obtain ⟨τ, hτ⟩ : ∃ τ, matrixCoeff B ρ τ (matrixCoeff A τ σ (c σ)) ≠ 0 := by
      by_contra! h
      exact hσ (by simp only [matrixCoeff_comp_apply]; exact finsum_eq_zero_of_forall_eq_zero h)
    exact hsupp τ σ hτ

/-- On a finite chain, the extension of `A` is `A`. -/
private lemma extendFun_toLocallyFiniteChains (y : (twistedChainComplex L).X a) :
    extendFun A ((toLocallyFiniteChains L a).hom y : ∀ σ, L.obj (initialVertex σ)) =
      ((toLocallyFiniteChains K b).hom (A.hom y) : ∀ ρ, K.obj (initialVertex ρ)) :=
  funext fun ρ ↦ by
    rw [extendFun, toLocallyFiniteChains_apply, ← finsum_matrixCoeff A y ρ]
    exact finsum_congr fun σ ↦ by rw [toLocallyFiniteChains_apply]

/-- Extending the identity gives the identity. -/
private lemma extendFun_id :
    extendFun (𝟙 ((twistedChainComplex L).X a)) c = c :=
  funext fun ρ ↦ by
    rw [extendFun, finsum_eq_single _ ρ fun σ hσ ↦ by
      simp [matrixCoeff_apply, twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne L hσ]]
    simp [matrixCoeff_apply]

/-- The identity moves simplices along the identity. -/
private lemma isProperlySupported_id : IsProperlySupported (𝟙 ((twistedChainComplex L).X a)) := by
  refine ⟨𝟙 X, isProperMap_id, fun ρ σ x hx ↦ ?_⟩
  obtain rfl : σ = ρ := by
    by_contra hne
    exact hx (by
      simp [matrixCoeff_apply, twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne L hne])
  simp

/-- The twisted boundary moves simplices along the identity: it only involves faces. -/
private lemma isProperlySupported_d (k : ℕ) :
    IsProperlySupported ((twistedChainComplex L).d (k + 1) k) := by
  refine ⟨𝟙 X, isProperMap_id, fun ρ σ x hx ↦ ?_⟩
  obtain ⟨i, rfl⟩ :
      ∃ i : Fin (k + 2), (TopCat.toSSet.obj X).map (SimplexCategory.δ i).op σ = ρ := by
    by_contra! hne
    exact hx (by
      rw [matrixCoeff, ιTwistedChainComplex_d_twistedChainComplexCoeff_of_forall_ne L hne]
      rfl)
  rw [TopCat.hom_id, ContinuousMap.coe_id, Set.image_id]
  exact TopCat.range_simplexMap_map_subset _ σ

/-- The locally finite boundary is the extension of the twisted boundary. -/
private lemma extendFun_d (k : ℕ) (c : ∀ σ : (TopCat.toSSet.obj X) _⦋k + 1⦌,
    L.obj (initialVertex σ)) :
    extendFun ((twistedChainComplex L).d (k + 1) k) c = locallyFiniteBoundaryFun L c :=
  funext fun ρ ↦ by
    rw [extendFun, locallyFiniteBoundaryFun_apply]
    rfl

/-- The extensions of the components of a properly supported chain map commute with the locally
finite boundaries. -/
private lemma locallyFiniteBoundary_comp_extend (φ : twistedChainComplex L ⟶ twistedChainComplex K)
    (hφ : ∀ k, IsProperlySupported (φ.f k)) (k : ℕ) :
    locallyFiniteBoundary K k ∘ₗ extend (hφ (k + 1)) =
      extend (hφ k) ∘ₗ locallyFiniteBoundary L k := by
  refine LinearMap.ext fun ⟨c, hc⟩ ↦ Subtype.ext ?_
  replace hc := mem_locallyFiniteChains.1 hc
  simp only [LinearMap.comp_apply, coe_locallyFiniteBoundary, coe_extend]
  rw [← extendFun_d, ← extendFun_d, extendFun_extendFun (hφ (k + 1)) (isProperlySupported_d k) hc,
    extendFun_extendFun (isProperlySupported_d k) (hφ k) hc, φ.comm]

/-- The chain map of locally finite chains extending a properly supported chain map. -/
private def extendChainMap (φ : twistedChainComplex L ⟶ twistedChainComplex K)
    (hφ : ∀ k, IsProperlySupported (φ.f k)) :
    locallyFiniteChainComplex L ⟶ locallyFiniteChainComplex K :=
  ChainComplex.ofHom (fun k ↦ eqToHom (locallyFiniteChainComplex_X L k) ≫
      ModuleCat.ofHom (extend (hφ k)) ≫ eqToHom (locallyFiniteChainComplex_X K k).symm)
    fun k ↦ by
      have key : ModuleCat.ofHom (extend (hφ (k + 1))) ≫
          ModuleCat.ofHom (locallyFiniteBoundary K k) =
            ModuleCat.ofHom (locallyFiniteBoundary L k) ≫ ModuleCat.ofHom (extend (hφ k)) := by
        rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp, locallyFiniteBoundary_comp_extend]
      simp only [locallyFiniteChainComplex_d, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp, reassoc_of% key]

private lemma extendChainMap_f (φ : twistedChainComplex L ⟶ twistedChainComplex K)
    (hφ : ∀ k, IsProperlySupported (φ.f k)) (k : ℕ) :
    (extendChainMap φ hφ).f k = eqToHom (locallyFiniteChainComplex_X L k) ≫
      ModuleCat.ofHom (extend (hφ k)) ≫ eqToHom (locallyFiniteChainComplex_X K k).symm :=
  (rfl)

private lemma extendChainMap_congr {φ φ' : twistedChainComplex L ⟶ twistedChainComplex K}
    (hφ : ∀ k, IsProperlySupported (φ.f k)) (hφ' : ∀ k, IsProperlySupported (φ'.f k))
    (h : φ = φ') : extendChainMap φ hφ = extendChainMap φ' hφ' := by
  subst h
  rfl

private lemma extendChainMap_id
    (h : ∀ k, IsProperlySupported (HomologicalComplex.Hom.f (𝟙 (twistedChainComplex L)) k)) :
    extendChainMap (𝟙 _) h = 𝟙 _ := by
  ext k : 1
  have : extend (h k) = LinearMap.id :=
    LinearMap.ext fun c ↦ Subtype.ext <| (coe_extend _ c).trans <| by
      rw [HomologicalComplex.id_f]
      exact extendFun_id
  rw [extendChainMap_f, this, HomologicalComplex.id_f]
  simp

private lemma isProperlySupported_comp_f {φ : twistedChainComplex L ⟶ twistedChainComplex K}
    {ψ : twistedChainComplex K ⟶ twistedChainComplex J}
    (hφ : ∀ k, IsProperlySupported (φ.f k)) (hψ : ∀ k, IsProperlySupported (ψ.f k)) (k : ℕ) :
    IsProperlySupported ((φ ≫ ψ).f k) := by
  rw [HomologicalComplex.comp_f]
  exact (hφ k).comp (hψ k)

private lemma extendChainMap_comp {φ : twistedChainComplex L ⟶ twistedChainComplex K}
    {ψ : twistedChainComplex K ⟶ twistedChainComplex J}
    (hφ : ∀ k, IsProperlySupported (φ.f k)) (hψ : ∀ k, IsProperlySupported (ψ.f k)) :
    extendChainMap φ hφ ≫ extendChainMap ψ hψ =
      extendChainMap (φ ≫ ψ) (isProperlySupported_comp_f hφ hψ) := by
  ext k : 1
  have : extend (hψ k) ∘ₗ extend (hφ k) = extend (isProperlySupported_comp_f hφ hψ k) :=
    LinearMap.ext fun ⟨c, hc⟩ ↦ Subtype.ext <|
      (extendFun_extendFun (hφ k) (hψ k) (mem_locallyFiniteChains.1 hc)).trans
        (by rw [coe_extend, HomologicalComplex.comp_f])
  rw [HomologicalComplex.comp_f, extendChainMap_f, extendChainMap_f, extendChainMap_f, ← this,
    ModuleCat.ofHom_comp]
  simp

private lemma toLocallyFiniteChainComplex_comp_extendChainMap
    (φ : twistedChainComplex L ⟶ twistedChainComplex K) (hφ : ∀ k, IsProperlySupported (φ.f k)) :
    toLocallyFiniteChainComplex L ≫ extendChainMap φ hφ = φ ≫ toLocallyFiniteChainComplex K := by
  ext k : 1
  have key : toLocallyFiniteChains L k ≫ ModuleCat.ofHom (extend (hφ k)) =
      φ.f k ≫ toLocallyFiniteChains K k :=
    ModuleCat.hom_ext <| LinearMap.ext fun y ↦ Subtype.ext <|
      extendFun_toLocallyFiniteChains (A := φ.f k) y
  simp only [HomologicalComplex.comp_f, toLocallyFiniteChainComplex_f, extendChainMap_f,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, reassoc_of% key]

end Extension

section Coefficients

variable {L K J : LocalCoefficientSystem.{u, v, max v w} R X}

private lemma isProperlySupported_twistedChainComplexCoefficientMap_f (η : L ⟶ K) (k : ℕ) :
    IsProperlySupported ((twistedChainComplexCoefficientMap η).f k) := by
  refine ⟨𝟙 X, isProperMap_id, fun ρ σ x hx ↦ ?_⟩
  obtain rfl : σ = ρ := by
    by_contra hne
    exact hx (by
      simp [matrixCoeff_apply, twistedChainComplexCoefficientMap_f_ι_apply,
        twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne K hne])
  simp

/-- The map of locally finite chains induced by a morphism of local coefficient systems, acting on
each coefficient. -/
def locallyFiniteChainsCoefficientMap (η : L ⟶ K) (k : ℕ) :
    locallyFiniteChains L k →ₗ[R] locallyFiniteChains K k :=
  extend (isProperlySupported_twistedChainComplexCoefficientMap_f η k)

/-- A morphism of local coefficient systems acts on each coefficient of a locally finite chain
through its component at the initial vertex of the simplex. -/
@[simp]
lemma coe_locallyFiniteChainsCoefficientMap_apply (η : L ⟶ K) {k : ℕ} (c : locallyFiniteChains L k)
    (σ : (TopCat.toSSet.obj X) _⦋k⦌) :
    (locallyFiniteChainsCoefficientMap η k c : ∀ τ, K.obj (initialVertex τ)) σ =
      (η.app (initialVertex σ)).hom ((c : ∀ τ, L.obj (initialVertex τ)) σ) := by
  rw [locallyFiniteChainsCoefficientMap, coe_extend, extendFun,
    finsum_eq_single _ σ fun τ hτ ↦ by
      simp [matrixCoeff_apply, twistedChainComplexCoefficientMap_f_ι_apply,
        twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne K hτ]]
  simp [matrixCoeff_apply, twistedChainComplexCoefficientMap_f_ι_apply]

/-- The chain map of locally finite chains induced by a morphism of local coefficient systems. -/
def locallyFiniteChainComplexCoefficientMap (η : L ⟶ K) :
    locallyFiniteChainComplex L ⟶ locallyFiniteChainComplex K :=
  extendChainMap (twistedChainComplexCoefficientMap η)
    (isProperlySupported_twistedChainComplexCoefficientMap_f η)

/-- In each degree, the coefficient chain map is `locallyFiniteChainsCoefficientMap`. -/
@[simp]
lemma locallyFiniteChainComplexCoefficientMap_f (η : L ⟶ K) (k : ℕ) :
    (locallyFiniteChainComplexCoefficientMap η).f k =
      eqToHom (locallyFiniteChainComplex_X L k) ≫
        ModuleCat.ofHom (locallyFiniteChainsCoefficientMap η k) ≫
          eqToHom (locallyFiniteChainComplex_X K k).symm :=
  (rfl)

/-- The identity morphism of coefficient systems induces the identity of locally finite chains. -/
@[simp]
lemma locallyFiniteChainComplexCoefficientMap_id :
    locallyFiniteChainComplexCoefficientMap (𝟙 L) = 𝟙 _ := by
  rw [locallyFiniteChainComplexCoefficientMap,
    extendChainMap_congr _ (fun k ↦ by rw [HomologicalComplex.id_f]; exact isProperlySupported_id)
      (twistedChainComplexCoefficientMap_id L), extendChainMap_id]

/-- A composite of morphisms of coefficient systems induces the composite of the maps of locally
finite chains. -/
@[simp, reassoc]
lemma locallyFiniteChainComplexCoefficientMap_comp (η : L ⟶ K) (θ : K ⟶ J) :
    locallyFiniteChainComplexCoefficientMap (η ≫ θ) =
      locallyFiniteChainComplexCoefficientMap η ≫ locallyFiniteChainComplexCoefficientMap θ := by
  rw [locallyFiniteChainComplexCoefficientMap, locallyFiniteChainComplexCoefficientMap,
    locallyFiniteChainComplexCoefficientMap, extendChainMap_comp]
  exact extendChainMap_congr _ _ (twistedChainComplexCoefficientMap_comp η θ)

/-- Regarding finite chains as locally finite chains commutes with changing the coefficients. -/
@[reassoc]
lemma toLocallyFiniteChainComplex_comp_locallyFiniteChainComplexCoefficientMap (η : L ⟶ K) :
    toLocallyFiniteChainComplex L ≫ locallyFiniteChainComplexCoefficientMap η =
      twistedChainComplexCoefficientMap η ≫ toLocallyFiniteChainComplex K :=
  toLocallyFiniteChainComplex_comp_extendChainMap _ _

/-- The map on Borel–Moore homology induced by a morphism of local coefficient systems. -/
abbrev borelMooreHomologyCoefficientMap (η : L ⟶ K) (k : ℕ) :
    borelMooreHomology L k ⟶ borelMooreHomology K k :=
  HomologicalComplex.homologyMap (locallyFiniteChainComplexCoefficientMap η) k

/-- The homology form of `locallyFiniteChainComplexCoefficientMap_id`. -/
@[simp]
lemma borelMooreHomologyCoefficientMap_id (k : ℕ) :
    borelMooreHomologyCoefficientMap (𝟙 L) k = 𝟙 _ := by
  simp [borelMooreHomologyCoefficientMap]

/-- The homology form of `locallyFiniteChainComplexCoefficientMap_comp`. -/
@[simp, reassoc]
lemma borelMooreHomologyCoefficientMap_comp (η : L ⟶ K) (θ : K ⟶ J) (k : ℕ) :
    borelMooreHomologyCoefficientMap (η ≫ θ) k =
      borelMooreHomologyCoefficientMap η k ≫ borelMooreHomologyCoefficientMap θ k := by
  simp [borelMooreHomologyCoefficientMap, HomologicalComplex.homologyMap_comp]

end Coefficients

section Map

variable (f : X ⟶ Y) (hf : IsProperMap f.hom) (L : LocalCoefficientSystem.{u, v, max v w} R Y)

include hf in
private lemma isProperlySupported_twistedChainComplexMap_f (k : ℕ) :
    IsProperlySupported ((twistedChainComplexMap f L).f k) := by
  refine ⟨f, hf, fun ρ σ x hx ↦ ?_⟩
  obtain rfl : (TopCat.toSSet.map f).app _ σ = ρ := by
    by_contra hne
    exact hx (by
      rw [matrixCoeff_apply, twistedChainComplexMap_f_ι_apply]
      exact twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne L hne x)
  rw [TopCat.simplexMap_app, ContinuousMap.coe_comp, Set.range_comp]

variable (k : ℕ)

include hf in
/-- The pushforward of locally finite chains along a proper map `f`, from chains with coefficients
in the pullback of `L` to chains with coefficients in `L`. -/
def locallyFiniteChainsMap :
    locallyFiniteChains ((pullback f.hom).obj L) k →ₗ[R] locallyFiniteChains L k :=
  extend (isProperlySupported_twistedChainComplexMap_f f hf L k)

/-- The coefficient of the pushforward of a locally finite chain on a simplex `ρ` is the sum of the
coefficients of the simplices `σ` with `f ∘ σ = ρ`. -/
lemma coe_locallyFiniteChainsMap_apply (c : locallyFiniteChains ((pullback f.hom).obj L) k)
    (ρ : (TopCat.toSSet.obj Y) _⦋k⦌) :
    (locallyFiniteChainsMap f hf L k c : ∀ τ, L.obj (initialVertex τ)) ρ =
      ∑ᶠ σ, (twistedChainComplexCoeff L ρ).hom ((ιTwistedChainComplex L k
        ((TopCat.toSSet.map f).app _ σ)).hom ((c : ∀ τ, ((pullback f.hom).obj L).obj
          (initialVertex τ)) σ)) := by
  rw [locallyFiniteChainsMap, coe_extend, extendFun]
  simp only [matrixCoeff_apply, twistedChainComplexMap_f_ι_apply]

include hf in
/-- The chain map of locally finite chains induced by a proper map. -/
def locallyFiniteChainComplexMap :
    locallyFiniteChainComplex ((pullback f.hom).obj L) ⟶ locallyFiniteChainComplex L :=
  extendChainMap (twistedChainComplexMap f L) (isProperlySupported_twistedChainComplexMap_f f hf L)

/-- In each degree, the chain map induced by a proper map is `locallyFiniteChainsMap`. -/
@[simp]
lemma locallyFiniteChainComplexMap_f :
    (locallyFiniteChainComplexMap f hf L).f k =
      eqToHom (locallyFiniteChainComplex_X _ k) ≫
        ModuleCat.ofHom (locallyFiniteChainsMap f hf L k) ≫
          eqToHom (locallyFiniteChainComplex_X L k).symm :=
  (rfl)

/-- Regarding finite chains as locally finite chains commutes with pushing forward along a proper
map. -/
@[reassoc]
lemma toLocallyFiniteChainComplex_comp_locallyFiniteChainComplexMap :
    toLocallyFiniteChainComplex _ ≫ locallyFiniteChainComplexMap f hf L =
      twistedChainComplexMap f L ≫ toLocallyFiniteChainComplex L :=
  toLocallyFiniteChainComplex_comp_extendChainMap _ _

/-- The map on Borel–Moore homology induced by a proper map. -/
abbrev borelMooreHomologyMap :
    borelMooreHomology ((pullback f.hom).obj L) k ⟶ borelMooreHomology L k :=
  HomologicalComplex.homologyMap (locallyFiniteChainComplexMap f hf L) k

/-- The proper pushforward of locally finite chains is natural in the coefficient system. -/
@[reassoc]
lemma locallyFiniteChainComplexMap_naturality {L K : LocalCoefficientSystem.{u, v, max v w} R Y}
    (η : L ⟶ K) :
    locallyFiniteChainComplexMap f hf L ≫ locallyFiniteChainComplexCoefficientMap η =
      locallyFiniteChainComplexCoefficientMap ((pullback f.hom).map η) ≫
        locallyFiniteChainComplexMap f hf K := by
  rw [locallyFiniteChainComplexMap, locallyFiniteChainComplexMap,
    locallyFiniteChainComplexCoefficientMap, locallyFiniteChainComplexCoefficientMap,
    extendChainMap_comp, extendChainMap_comp]
  exact extendChainMap_congr _ _ (twistedChainComplexMap_naturality f η)

/-- The homology form of `locallyFiniteChainComplexMap_naturality`. -/
@[reassoc]
lemma borelMooreHomologyMap_naturality {L K : LocalCoefficientSystem.{u, v, max v w} R Y}
    (η : L ⟶ K) :
    borelMooreHomologyMap f hf L k ≫ borelMooreHomologyCoefficientMap η k =
      borelMooreHomologyCoefficientMap ((pullback f.hom).map η) k ≫
        borelMooreHomologyMap f hf K k := by
  simp only [← HomologicalComplex.homologyMap_comp, locallyFiniteChainComplexMap_naturality]

end Map

section MapComp

/-- The identity map induces on locally finite chains the map coming from the identification of a
coefficient system with its pullback along the identity. -/
@[simp]
lemma locallyFiniteChainComplexMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X) :
    locallyFiniteChainComplexMap (𝟙 X) isProperMap_id L =
      locallyFiniteChainComplexCoefficientMap ((pullbackIdIso X).hom.app L) :=
  extendChainMap_congr _ _ (twistedChainComplexMap_id L)

/-- A composite of proper maps induces on locally finite chains the composite of the two induced
maps, after the identification of the pullback along the composite with the iterated pullback. -/
@[reassoc]
lemma locallyFiniteChainComplexMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsProperMap f.hom)
    (hg : IsProperMap g.hom) (hfg : IsProperMap (f ≫ g).hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R Z) :
    locallyFiniteChainComplexMap (f ≫ g) hfg L =
      locallyFiniteChainComplexCoefficientMap ((pullbackCompIso f.hom g.hom).hom.app L) ≫
        locallyFiniteChainComplexMap f hf ((pullback g.hom).obj L) ≫
          locallyFiniteChainComplexMap g hg L := by
  rw [locallyFiniteChainComplexMap, locallyFiniteChainComplexMap, locallyFiniteChainComplexMap,
    locallyFiniteChainComplexCoefficientMap, extendChainMap_comp, extendChainMap_comp]
  exact extendChainMap_congr _ _ (twistedChainComplexMap_comp f g L)

/-- The homology form of `locallyFiniteChainComplexMap_id`. -/
@[simp]
lemma borelMooreHomologyMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X) (k : ℕ) :
    borelMooreHomologyMap (𝟙 X) isProperMap_id L k =
      borelMooreHomologyCoefficientMap ((pullbackIdIso X).hom.app L) k := by
  simp only [borelMooreHomologyMap, borelMooreHomologyCoefficientMap,
    locallyFiniteChainComplexMap_id]

/-- The homology form of `locallyFiniteChainComplexMap_comp`. -/
@[reassoc]
lemma borelMooreHomologyMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsProperMap f.hom)
    (hg : IsProperMap g.hom) (hfg : IsProperMap (f ≫ g).hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R Z) (k : ℕ) :
    borelMooreHomologyMap (f ≫ g) hfg L k =
      borelMooreHomologyCoefficientMap ((pullbackCompIso f.hom g.hom).hom.app L) k ≫
        borelMooreHomologyMap f hf ((pullback g.hom).obj L) k ≫ borelMooreHomologyMap g hg L k := by
  simp only [borelMooreHomologyMap, borelMooreHomologyCoefficientMap,
    locallyFiniteChainComplexMap_comp f g hf hg hfg, HomologicalComplex.homologyMap_comp]

end MapComp

end LocalCoefficientSystem

end TauCeti
