/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Topology.Compactness.LocallyFinite

/-!
# Locally finite singular chains and Borel–Moore homology

A locally finite singular `k`-chain of a space `X` with coefficients in a local coefficient system
`L` assigns to every singular `k`-simplex `σ` a coefficient in the fibre of `L` at the initial
vertex of `σ`, such that every point of `X` has a neighbourhood meeting the images of only finitely
many simplices with nonzero coefficient. Unlike the ordinary twisted chains of
`TauCeti.LocalCoefficientSystem.twistedChainComplex`, infinitely many coefficients may be nonzero.

The boundary of such a chain is computed one face at a time. The coefficient of the boundary on a
`k`-simplex `ρ` is the sum, over the `(k + 1)`-simplices `σ` having `ρ` as a face, of the
transported coefficients of `σ`; local finiteness at a point of the image of `ρ` makes this sum
finite. Every simplex contributing to the boundary near a point is a face of a simplex of the
original chain near that point, so the boundary is again locally finite. The boundary is described
through the coefficients of the ordinary twisted boundary, and it squares to zero because the
ordinary twisted boundary does.

Borel–Moore homology with local coefficients is the homology of this complex. Finite chains are
locally finite, and including them is a chain map from the twisted chain complex; on a compact space
every locally finite chain is finite, so this inclusion is an isomorphism there.

## Main declarations

* `TauCeti.LocalCoefficientSystem.twistedChainComplexCoeff`: the coefficient of a twisted chain on a
  singular simplex; by `twistedChainComplex_ext_coeff` a twisted chain is determined by its
  coefficients.
* `TauCeti.LocalCoefficientSystem.IsLocallyFiniteChain`: local finiteness of a family of simplex
  coefficients, and `locallyFiniteChains` the module of locally finite chains.
* `TauCeti.LocalCoefficientSystem.locallyFiniteBoundary`: the boundary of locally finite chains,
  with `locallyFiniteBoundary_comp_locallyFiniteBoundary` stating that it squares to zero.
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

section Coeff

variable {k : ℕ}

open Classical in
/-- The coefficient of a twisted chain on a singular `k`-simplex `ρ`: the projection of the
coproduct of simplex fibres onto the summand of `ρ`. -/
def twistedChainComplexCoeff (ρ : (TopCat.toSSet.obj X) _⦋k⦌) :
    (twistedChainComplex L).X k ⟶ L.obj (initialVertex ρ) :=
  twistedChainComplexDesc L fun σ ↦ if h : σ = ρ then eqToHom (by rw [h]) else 0

/-- The coefficient on `ρ` of a chain supported on `ρ` is its coefficient. -/
@[reassoc (attr := simp)]
lemma ιTwistedChainComplex_twistedChainComplexCoeff (ρ : (TopCat.toSSet.obj X) _⦋k⦌) :
    ιTwistedChainComplex L k ρ ≫ twistedChainComplexCoeff L ρ = 𝟙 _ := by
  simp [twistedChainComplexCoeff]

/-- The coefficient on `ρ` of a chain supported on a different simplex vanishes. -/
lemma ιTwistedChainComplex_twistedChainComplexCoeff_of_ne {σ ρ : (TopCat.toSSet.obj X) _⦋k⦌}
    (h : σ ≠ ρ) : ιTwistedChainComplex L k σ ≫ twistedChainComplexCoeff L ρ = 0 := by
  simp [twistedChainComplexCoeff, h]

/-- The coefficient on `ρ` of a chain supported on `ρ` is its coefficient. -/
@[simp]
lemma twistedChainComplexCoeff_ιTwistedChainComplex_apply (ρ : (TopCat.toSSet.obj X) _⦋k⦌)
    (x : L.obj (initialVertex ρ)) :
    (twistedChainComplexCoeff L ρ).hom ((ιTwistedChainComplex L k ρ).hom x) = x :=
  congrArg (fun f ↦ f.hom x) (ιTwistedChainComplex_twistedChainComplexCoeff L ρ)

/-- The coefficient on `ρ` of a chain supported on a different simplex vanishes. -/
lemma twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne
    {σ ρ : (TopCat.toSSet.obj X) _⦋k⦌} (h : σ ≠ ρ) (x : L.obj (initialVertex σ)) :
    (twistedChainComplexCoeff L ρ).hom ((ιTwistedChainComplex L k σ).hom x) = 0 :=
  congrArg (fun f ↦ f.hom x) (ιTwistedChainComplex_twistedChainComplexCoeff_of_ne L h)

/-- Summing a family of additive maps out of the simplex fibres against the coefficients of a
finite sum of chains, each supported on one simplex, applies the maps summand by summand. -/
lemma finsum_twistedChainComplexCoeff_sum {M : Type*} [AddCommMonoid M]
    (g : ∀ τ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex τ) →+ M) {ι : Type*}
    (s : Finset ι) (σ : ι → (TopCat.toSSet.obj X) _⦋k⦌) (x : ∀ i, L.obj (initialVertex (σ i))) :
    ∑ᶠ τ, g τ ((twistedChainComplexCoeff L τ).hom (∑ i ∈ s, (ιTwistedChainComplex L k (σ i)).hom
      (x i))) = ∑ i ∈ s, g (σ i) (x i) := by
  have hsingle : ∀ i, ∑ᶠ τ, g τ ((twistedChainComplexCoeff L τ).hom
      ((ιTwistedChainComplex L k (σ i)).hom (x i))) = g (σ i) (x i) := fun i ↦ by
    rw [finsum_eq_single _ (σ i) fun τ hτ ↦ by
      rw [twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne L (Ne.symm hτ), map_zero],
      twistedChainComplexCoeff_ιTwistedChainComplex_apply]
  simp_rw [map_sum]
  rw [← sum_finsum_comm _ _ fun i _ ↦ (Set.finite_singleton (σ i)).subset fun τ hτ ↦
    Set.mem_singleton_iff.2 <| by_contra fun h ↦ hτ <| by
      simp only [twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne L (Ne.symm h),
        map_zero]]
  exact Finset.sum_congr rfl fun i _ ↦ hsingle i

open Classical in
/-- The coefficient projections factor through the identification of a degree of the twisted
chain complex with the direct sum of the simplex fibres. -/
private lemma twistedChainComplexCoeff_eq_component (ρ : (TopCat.toSSet.obj X) _⦋k⦌) :
    twistedChainComplexCoeff L ρ =
      (eqToIso (twistedChainComplex_X L k) ≪≫ ModuleCat.coprodIsoDirectSum _).hom ≫
        ModuleCat.ofHom (DirectSum.component R _
          (fun σ : (TopCat.toSSet.obj X) _⦋k⦌ ↦ L.obj (initialVertex σ)) ρ) := by
  refine twistedChainComplex_hom_ext L fun σ ↦ ?_
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, ιTwistedChainComplex_eqToHom_assoc]
  rw [← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom, ← ModuleCat.ofHom_comp]
  by_cases h : σ = ρ
  · subst h
    simp
  · simp [ιTwistedChainComplex_twistedChainComplexCoeff_of_ne L h, DirectSum.component_comp_lof, h]

/-- A twisted chain is determined by its coefficients. -/
lemma twistedChainComplex_ext_coeff {y y' : (twistedChainComplex L).X k}
    (h : ∀ ρ, (twistedChainComplexCoeff L ρ).hom y = (twistedChainComplexCoeff L ρ).hom y') :
    y = y' := by
  classical
  let e := eqToIso (twistedChainComplex_X L k) ≪≫ ModuleCat.coprodIsoDirectSum
    (fun σ : (TopCat.toSSet.obj X) _⦋k⦌ ↦ L.obj (initialVertex σ))
  refine (ModuleCat.mono_iff_injective e.hom).1 inferInstance
    (DirectSum.ext_component R fun ρ ↦ ?_)
  simpa only [twistedChainComplexCoeff_eq_component, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom] using h ρ

end Coeff

section Boundary

variable {k : ℕ}

/-- The component of the twisted boundary from the summand of a `(k + 1)`-simplex `σ` to the
summand of a `k`-simplex `ρ`. -/
private abbrev boundaryCoeff (ρ : (TopCat.toSSet.obj X) _⦋k⦌)
    (σ : (TopCat.toSSet.obj X) _⦋k + 1⦌) : L.obj (initialVertex σ) ⟶ L.obj (initialVertex ρ) :=
  ιTwistedChainComplex L (k + 1) σ ≫ (twistedChainComplex L).d (k + 1) k ≫
    twistedChainComplexCoeff L ρ

/-- The twisted boundary of a chain supported on `σ` is a signed sum of chains supported on the
faces of `σ`. -/
private lemma d_ιTwistedChainComplex_apply (σ : (TopCat.toSSet.obj X) _⦋k + 1⦌)
    (x : L.obj (initialVertex σ)) :
    ((twistedChainComplex L).d (k + 1) k).hom ((ιTwistedChainComplex L (k + 1) σ).hom x) =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        (ιTwistedChainComplex L k ((TopCat.toSSet.obj X).map (SimplexCategory.δ i).op σ)).hom
          ((L.map (vertexTransport (SimplexCategory.δ i).op σ)).hom x) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ιTwistedChainComplex_d]
  simp

/-- A boundary component vanishes unless `ρ` is a face of `σ`. -/
private lemma exists_map_δ_eq_of_boundaryCoeff_apply_ne_zero {ρ : (TopCat.toSSet.obj X) _⦋k⦌}
    {σ : (TopCat.toSSet.obj X) _⦋k + 1⦌} {x : L.obj (initialVertex σ)}
    (h : (boundaryCoeff L ρ σ).hom x ≠ 0) :
    ∃ i : Fin (k + 2), (TopCat.toSSet.obj X).map (SimplexCategory.δ i).op σ = ρ := by
  by_contra! hne
  refine h ?_
  simp only [boundaryCoeff, ModuleCat.hom_comp, LinearMap.comp_apply,
    d_ιTwistedChainComplex_apply, map_sum, map_zsmul]
  exact Finset.sum_eq_zero fun i _ ↦ by
    rw [twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne L (hne i), smul_zero]

end Boundary

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

section LocallyFiniteBoundary

variable {L} {k : ℕ}

/-- The point of the image of a simplex given by its initial vertex. -/
private abbrev basePoint (ρ : (TopCat.toSSet.obj X) _⦋k⦌) : X :=
  TopCat.simplexMap ρ (toTopInitialVertex _)

private lemma basePoint_mem_range_of_map_δ_eq {ρ : (TopCat.toSSet.obj X) _⦋k⦌}
    {σ : (TopCat.toSSet.obj X) _⦋k + 1⦌} {i : Fin (k + 2)}
    (h : (TopCat.toSSet.obj X).map (SimplexCategory.δ i).op σ = ρ) :
    basePoint ρ ∈ Set.range (TopCat.simplexMap σ) := by
  subst h
  exact ⟨_, rfl⟩

private lemma range_subset_of_map_δ_eq {ρ : (TopCat.toSSet.obj X) _⦋k⦌}
    {σ : (TopCat.toSSet.obj X) _⦋k + 1⦌} {i : Fin (k + 2)}
    (h : (TopCat.toSSet.obj X).map (SimplexCategory.δ i).op σ = ρ) :
    Set.range (TopCat.simplexMap ρ) ⊆ Set.range (TopCat.simplexMap σ) := by
  subst h
  rintro _ ⟨z, rfl⟩
  exact ⟨_, rfl⟩

/-- The terms of the boundary of a locally finite chain on a fixed simplex have finite support. -/
private lemma finite_support_boundaryCoeff
    {c : ∀ σ : (TopCat.toSSet.obj X) _⦋k + 1⦌, L.obj (initialVertex σ)}
    (hc : IsLocallyFiniteChain L c) (ρ : (TopCat.toSSet.obj X) _⦋k⦌) :
    (Function.support fun σ ↦ (boundaryCoeff L ρ σ).hom (c σ)).Finite := by
  refine (hc.finite_setOf_mem_range (basePoint ρ)).subset fun σ hσ ↦ ?_
  obtain ⟨i, hi⟩ := exists_map_δ_eq_of_boundaryCoeff_apply_ne_zero L hσ
  refine ⟨fun h ↦ hσ ?_, basePoint_mem_range_of_map_δ_eq hi⟩
  simp [h]

variable (L) in
/-- The coefficients of the boundary of a family of coefficients on singular `(k + 1)`-simplices.
The coefficient on a `k`-simplex `ρ` is the sum, over all `(k + 1)`-simplices `σ`, of the
coefficient on `ρ` of the twisted boundary of the chain supported on `σ` with coefficient `c σ`. -/
def locallyFiniteBoundaryFun (c : ∀ σ : (TopCat.toSSet.obj X) _⦋k + 1⦌, L.obj (initialVertex σ))
    (ρ : (TopCat.toSSet.obj X) _⦋k⦌) : L.obj (initialVertex ρ) :=
  ∑ᶠ σ, (twistedChainComplexCoeff L ρ).hom (((twistedChainComplex L).d (k + 1) k).hom
    ((ιTwistedChainComplex L (k + 1) σ).hom (c σ)))

private lemma locallyFiniteBoundaryFun_eq
    (c : ∀ σ : (TopCat.toSSet.obj X) _⦋k + 1⦌, L.obj (initialVertex σ))
    (ρ : (TopCat.toSSet.obj X) _⦋k⦌) :
    locallyFiniteBoundaryFun L c ρ = ∑ᶠ σ, (boundaryCoeff L ρ σ).hom (c σ) :=
  (rfl)

/-- The boundary of a locally finite chain is locally finite. -/
lemma IsLocallyFiniteChain.locallyFiniteBoundaryFun
    {c : ∀ σ : (TopCat.toSSet.obj X) _⦋k + 1⦌, L.obj (initialVertex σ)}
    (hc : IsLocallyFiniteChain L c) :
    IsLocallyFiniteChain L (locallyFiniteBoundaryFun L c) := by
  rw [isLocallyFiniteChain_iff] at hc ⊢
  intro x
  obtain ⟨U, hU, hfin⟩ := hc x
  refine ⟨U, hU, (hfin.biUnion fun σ _ ↦ Set.finite_range fun i : Fin (k + 2) ↦
    (TopCat.toSSet.obj X).map (SimplexCategory.δ i).op σ).subset ?_⟩
  rintro ρ ⟨hρ, y, hy, hyU⟩
  obtain ⟨σ, hσ⟩ : ∃ σ, (boundaryCoeff L ρ σ).hom (c σ) ≠ 0 := by
    by_contra! h
    exact hρ (by rw [locallyFiniteBoundaryFun_eq]; exact finsum_eq_zero_of_forall_eq_zero h)
  obtain ⟨i, hi⟩ := exists_map_δ_eq_of_boundaryCoeff_apply_ne_zero L hσ
  exact Set.mem_biUnion (x := σ) ⟨fun h ↦ hσ (by simp [h]),
    y, range_subset_of_map_δ_eq hi hy, hyU⟩ ⟨i, hi⟩

variable (L k) in
/-- The boundary of locally finite singular `(k + 1)`-chains with coefficients in `L`. -/
def locallyFiniteBoundary : locallyFiniteChains L (k + 1) →ₗ[R] locallyFiniteChains L k where
  toFun c := ⟨locallyFiniteBoundaryFun L c,
    (mem_locallyFiniteChains.1 c.2).locallyFiniteBoundaryFun⟩
  map_add' c c' := Subtype.ext <| funext fun ρ ↦ by
    simp only [Submodule.coe_add, Pi.add_apply, locallyFiniteBoundaryFun_eq, map_add]
    exact finsum_add_distrib (finite_support_boundaryCoeff c.2 ρ)
      (finite_support_boundaryCoeff c'.2 ρ)
  map_smul' a c := Subtype.ext <| funext fun ρ ↦ by
    simp only [SetLike.val_smul, Pi.smul_apply, locallyFiniteBoundaryFun_eq, map_smul,
      RingHom.id_apply]
    exact (smul_finsum' a (finite_support_boundaryCoeff c.2 ρ)).symm

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
        ((ιTwistedChainComplex L (k + 1) σ).hom (c σ))) :=
  (rfl)

/-- Composing boundary components through all intermediate simplices gives the corresponding
component of the square of the twisted boundary, which vanishes. -/
private lemma finsum_boundaryCoeff_boundaryCoeff (ρ : (TopCat.toSSet.obj X) _⦋k⦌)
    (σ : (TopCat.toSSet.obj X) _⦋k + 1 + 1⦌) (x : L.obj (initialVertex σ)) :
    ∑ᶠ τ, (boundaryCoeff L ρ τ).hom ((boundaryCoeff L τ σ).hom x) = 0 := by
  have h := d_ιTwistedChainComplex_apply L σ x
  simp_rw [← map_zsmul] at h
  calc ∑ᶠ τ, (boundaryCoeff L ρ τ).hom ((boundaryCoeff L τ σ).hom x)
      = ∑ᶠ τ, (boundaryCoeff L ρ τ).hom ((twistedChainComplexCoeff L τ).hom
          (∑ i : Fin (k + 1 + 2), (ιTwistedChainComplex L (k + 1)
            ((TopCat.toSSet.obj X).map (SimplexCategory.δ i).op σ)).hom
              ((L.map (vertexTransport (SimplexCategory.δ i).op σ)).hom ((-1 : ℤ) ^ (i : ℕ) • x))))
        := by
        simp only [boundaryCoeff, ModuleCat.hom_comp, LinearMap.comp_apply]
        rw [h]
    _ = ∑ i : Fin (k + 1 + 2), (boundaryCoeff L ρ
          ((TopCat.toSSet.obj X).map (SimplexCategory.δ i).op σ)).hom
            ((L.map (vertexTransport (SimplexCategory.δ i).op σ)).hom ((-1 : ℤ) ^ (i : ℕ) • x)) :=
        finsum_twistedChainComplexCoeff_sum L (fun τ ↦ (boundaryCoeff L ρ τ).hom.toAddMonoidHom)
          _ _ _
    _ = (twistedChainComplexCoeff L ρ).hom (((twistedChainComplex L).d (k + 1) k).hom
          (((twistedChainComplex L).d (k + 1 + 1) (k + 1)).hom
            ((ιTwistedChainComplex L (k + 1 + 1) σ).hom x))) := by
        simp only [boundaryCoeff, ModuleCat.hom_comp, LinearMap.comp_apply, h, map_sum]
    _ = 0 := by
        rw [← LinearMap.comp_apply (((twistedChainComplex L).d (k + 1) k).hom),
          ← ModuleCat.hom_comp, HomologicalComplex.d_comp_d]
        simp

/-- The boundary of locally finite chains squares to zero. -/
@[simp]
lemma locallyFiniteBoundary_comp_locallyFiniteBoundary :
    locallyFiniteBoundary L k ∘ₗ locallyFiniteBoundary L (k + 1) = 0 := by
  refine LinearMap.ext fun ⟨c, hc⟩ ↦ Subtype.ext <| funext fun ρ ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero, Pi.zero_apply,
    coe_locallyFiniteBoundary]
  set F := (hc.finite_setOf_mem_range (basePoint ρ)).toFinset
  have hzero : ∀ τ σ, (boundaryCoeff L τ σ).hom (c σ) = 0 →
      (boundaryCoeff L ρ τ).hom ((boundaryCoeff L τ σ).hom (c σ)) = 0 := fun τ σ h ↦ by
    rw [h, map_zero]
  -- Every nonzero term involves a simplex `σ` of the chain through the initial vertex of `ρ`.
  have hsupp : ∀ τ σ, (boundaryCoeff L ρ τ).hom ((boundaryCoeff L τ σ).hom (c σ)) ≠ 0 →
      σ ∈ F := fun τ σ h ↦ by
    obtain ⟨i, hi⟩ := exists_map_δ_eq_of_boundaryCoeff_apply_ne_zero L h
    have h' : (boundaryCoeff L τ σ).hom (c σ) ≠ 0 := fun h' ↦ h (hzero τ σ h')
    obtain ⟨j, hj⟩ := exists_map_δ_eq_of_boundaryCoeff_apply_ne_zero L h'
    refine (Set.Finite.mem_toFinset _).2 ⟨fun hσ ↦ h' (by simp [hσ]), ?_⟩
    exact range_subset_of_map_δ_eq hj (basePoint_mem_range_of_map_δ_eq hi)
  simp_rw [locallyFiniteBoundaryFun_eq]
  rw [finsum_congr fun τ ↦ map_finsum _ (finite_support_boundaryCoeff hc τ),
    finsum_congr fun τ ↦ finsum_eq_sum_of_support_subset _ fun σ hσ ↦ hsupp τ σ hσ,
    ← sum_finsum_comm]
  · exact Finset.sum_eq_zero fun σ _ ↦ finsum_boundaryCoeff_boundaryCoeff ρ σ (c σ)
  · refine fun σ _ ↦ (Set.finite_range fun j : Fin (k + 1 + 2) ↦
      (TopCat.toSSet.obj X).map (SimplexCategory.δ j).op σ).subset fun τ hτ ↦ ?_
    exact exists_map_δ_eq_of_boundaryCoeff_apply_ne_zero L (x := c σ) fun h' ↦
      hτ (hzero τ σ h')

end LocallyFiniteBoundary

section Complex

/-- The chain complex of locally finite singular chains of `X` with coefficients in `L`. -/
-- The body is exposed so that each degree is, by definition, the module of locally finite chains:
-- the statement of `locallyFiniteChainComplex_d` and maps into the complex depend on this.
@[expose]
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
    (locallyFiniteChainComplex L).d (k + 1) k = ModuleCat.ofHom (locallyFiniteBoundary L k) :=
  ChainComplex.of_d (fun k ↦ ModuleCat.of R (locallyFiniteChains L k))
    (fun k ↦ ModuleCat.ofHom (locallyFiniteBoundary L k)) k

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

/-- Each twisted chain is sent to a locally finite chain with the same coefficients, and this
commutes with the boundaries. -/
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
  f k := toLocallyFiniteChains L k
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [locallyFiniteChainComplex_d]
    exact toLocallyFiniteChains_comp_locallyFiniteBoundary L

/-- The components of the chain map to locally finite chains are the inclusions of finite
chains. -/
@[simp]
lemma toLocallyFiniteChainComplex_f (k : ℕ) :
    (toLocallyFiniteChainComplex L).f k = toLocallyFiniteChains L k :=
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
    rw [toLocallyFiniteChains_apply, map_sum]
    by_cases hρ : ρ ∈ S
    · rw [Finset.sum_eq_single_of_mem ρ hρ fun σ _ h ↦
        twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne L h _,
        twistedChainComplexCoeff_ιTwistedChainComplex_apply]
    · rw [Finset.sum_eq_zero fun σ hσ ↦ twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne
        L (fun (h : σ = ρ) ↦ hρ (h ▸ hσ)) _]
      exact (by simpa [S] using hρ : c ρ = 0).symm

/-- On a compact space, the inclusion of twisted chains into locally finite chains is an
isomorphism of chain complexes. -/
instance isIso_toLocallyFiniteChainComplex [CompactSpace X] :
    IsIso (toLocallyFiniteChainComplex L) := by
  have (k : ℕ) : IsIso ((toLocallyFiniteChainComplex L).f k) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_toLocallyFiniteChains L)
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
