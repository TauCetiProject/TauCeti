/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Basic

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

* `TauCeti.LocalCoefficientSystem.extendLocallyFiniteChainMap`: the chain map of locally finite
  chains extending a chain map of twisted chains with properly supported components.
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

All these maps are built uniformly with `extendLocallyFinite`, which applies a properly supported
map of twisted chains to locally finite chains simplex by simplex. The locally finite boundary is
the extension of the twisted boundary, and extension takes composites to composites, so the
extension of a chain map is a chain map (`extendLocallyFiniteChainMap`).

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
  {J : LocalCoefficientSystem.{u, v, max v w} R Z}

/-- The extensions of the components of a properly supported chain map commute with the locally
finite boundaries. -/
lemma locallyFiniteBoundary_comp_extendLocallyFinite
    (φ : twistedChainComplex L ⟶ twistedChainComplex K)
    (hφ : ∀ k, IsProperlySupported (φ.f k)) (k : ℕ) :
    locallyFiniteBoundary K k ∘ₗ extendLocallyFinite (hφ (k + 1)) =
      extendLocallyFinite (hφ k) ∘ₗ locallyFiniteBoundary L k := by
  refine LinearMap.ext fun ⟨c, hc⟩ ↦ Subtype.ext ?_
  replace hc := mem_locallyFiniteChains.1 hc
  simp only [LinearMap.comp_apply, coe_locallyFiniteBoundary, coe_extendLocallyFinite]
  rw [← extendLocallyFiniteFun_d, ← extendLocallyFiniteFun_d,
    extendLocallyFiniteFun_extendLocallyFiniteFun (hφ (k + 1)) (isProperlySupported_d k) hc,
    extendLocallyFiniteFun_extendLocallyFiniteFun (isProperlySupported_d k) (hφ k) hc, φ.comm]

/-- The chain map of locally finite chains extending a chain map of twisted chains whose components
are properly supported. -/
def extendLocallyFiniteChainMap (φ : twistedChainComplex L ⟶ twistedChainComplex K)
    (hφ : ∀ k, IsProperlySupported (φ.f k)) :
    locallyFiniteChainComplex L ⟶ locallyFiniteChainComplex K :=
  ChainComplex.ofHom (fun k ↦ eqToHom (locallyFiniteChainComplex_X L k) ≫
      ModuleCat.ofHom (extendLocallyFinite (hφ k)) ≫
        eqToHom (locallyFiniteChainComplex_X K k).symm)
    fun k ↦ by
      have key : ModuleCat.ofHom (extendLocallyFinite (hφ (k + 1))) ≫
          ModuleCat.ofHom (locallyFiniteBoundary K k) =
            ModuleCat.ofHom (locallyFiniteBoundary L k) ≫
              ModuleCat.ofHom (extendLocallyFinite (hφ k)) := by
        rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp,
          locallyFiniteBoundary_comp_extendLocallyFinite]
      simp only [locallyFiniteChainComplex_d, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp, reassoc_of% key]

/-- In each degree, the extension of a properly supported chain map is `extendLocallyFinite`. -/
lemma extendLocallyFiniteChainMap_f (φ : twistedChainComplex L ⟶ twistedChainComplex K)
    (hφ : ∀ k, IsProperlySupported (φ.f k)) (k : ℕ) :
    (extendLocallyFiniteChainMap φ hφ).f k = eqToHom (locallyFiniteChainComplex_X L k) ≫
      ModuleCat.ofHom (extendLocallyFinite (hφ k)) ≫
        eqToHom (locallyFiniteChainComplex_X K k).symm :=
  (rfl)

/-- The extension of a properly supported chain map depends only on the chain map. -/
lemma extendLocallyFiniteChainMap_congr {φ φ' : twistedChainComplex L ⟶ twistedChainComplex K}
    (hφ : ∀ k, IsProperlySupported (φ.f k)) (hφ' : ∀ k, IsProperlySupported (φ'.f k))
    (h : φ = φ') : extendLocallyFiniteChainMap φ hφ = extendLocallyFiniteChainMap φ' hφ' := by
  subst h
  rfl

/-- The extension of the identity chain map is the identity. -/
@[simp]
lemma extendLocallyFiniteChainMap_id
    (h : ∀ k, IsProperlySupported (HomologicalComplex.Hom.f (𝟙 (twistedChainComplex L)) k)) :
    extendLocallyFiniteChainMap (𝟙 _) h = 𝟙 _ := by
  ext k : 1
  have : extendLocallyFinite (h k) = LinearMap.id := extendLocallyFinite_id (h k)
  rw [extendLocallyFiniteChainMap_f, this, HomologicalComplex.id_f]
  simp

/-- The components of a composite of properly supported chain maps are properly supported. -/
lemma isProperlySupported_comp_f {φ : twistedChainComplex L ⟶ twistedChainComplex K}
    {ψ : twistedChainComplex K ⟶ twistedChainComplex J}
    (hφ : ∀ k, IsProperlySupported (φ.f k)) (hψ : ∀ k, IsProperlySupported (ψ.f k)) (k : ℕ) :
    IsProperlySupported ((φ ≫ ψ).f k) := by
  rw [HomologicalComplex.comp_f]
  exact (hφ k).comp (hψ k)

/-- The extension of a composite of properly supported chain maps is the composite of the
extensions. -/
@[reassoc]
lemma extendLocallyFiniteChainMap_comp {φ : twistedChainComplex L ⟶ twistedChainComplex K}
    {ψ : twistedChainComplex K ⟶ twistedChainComplex J}
    (hφ : ∀ k, IsProperlySupported (φ.f k)) (hψ : ∀ k, IsProperlySupported (ψ.f k)) :
    extendLocallyFiniteChainMap φ hφ ≫ extendLocallyFiniteChainMap ψ hψ =
      extendLocallyFiniteChainMap (φ ≫ ψ) (isProperlySupported_comp_f hφ hψ) := by
  ext k : 1
  have : extendLocallyFinite (hψ k) ∘ₗ extendLocallyFinite (hφ k) =
      extendLocallyFinite (isProperlySupported_comp_f hφ hψ k) :=
    extendLocallyFinite_comp (hφ k) (hψ k)
  rw [HomologicalComplex.comp_f, extendLocallyFiniteChainMap_f, extendLocallyFiniteChainMap_f,
    extendLocallyFiniteChainMap_f, ← this, ModuleCat.ofHom_comp]
  simp

/-- Regarding finite chains as locally finite chains commutes with extending a properly supported
chain map. -/
@[reassoc]
lemma toLocallyFiniteChainComplex_comp_extendLocallyFiniteChainMap
    (φ : twistedChainComplex L ⟶ twistedChainComplex K) (hφ : ∀ k, IsProperlySupported (φ.f k)) :
    toLocallyFiniteChainComplex L ≫ extendLocallyFiniteChainMap φ hφ =
      φ ≫ toLocallyFiniteChainComplex K := by
  ext k : 1
  have key : toLocallyFiniteChains L k ≫ ModuleCat.ofHom (extendLocallyFinite (hφ k)) =
      φ.f k ≫ toLocallyFiniteChains K k :=
    ModuleCat.hom_ext <| LinearMap.ext fun y ↦ Subtype.ext <| by
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        coe_extendLocallyFinite]
      exact extendLocallyFiniteFun_toLocallyFiniteChains (φ.f k) y
  simp only [HomologicalComplex.comp_f, toLocallyFiniteChainComplex_f,
    extendLocallyFiniteChainMap_f, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, reassoc_of% key]

end Extension

section Coefficients

variable {L K J : LocalCoefficientSystem.{u, v, max v w} R X}

/-- Changing coefficients does not move the underlying simplices, so each component is properly
supported. -/
lemma isProperlySupported_twistedChainComplexCoefficientMap_f (η : L ⟶ K) (k : ℕ) :
    IsProperlySupported ((twistedChainComplexCoefficientMap η).f k) := by
  refine .of_movesAlong (g := 𝟙 X) isProperMap_id (movesAlong_iff.2 fun ρ σ x hx ↦ ?_)
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
  extendLocallyFinite (isProperlySupported_twistedChainComplexCoefficientMap_f η k)

/-- A morphism of local coefficient systems acts on each coefficient of a locally finite chain
through its component at the initial vertex of the simplex. -/
@[simp]
lemma coe_locallyFiniteChainsCoefficientMap_apply (η : L ⟶ K) {k : ℕ} (c : locallyFiniteChains L k)
    (σ : (TopCat.toSSet.obj X) _⦋k⦌) :
    (locallyFiniteChainsCoefficientMap η k c : ∀ τ, K.obj (initialVertex τ)) σ =
      (η.app (initialVertex σ)).hom ((c : ∀ τ, L.obj (initialVertex τ)) σ) := by
  rw [locallyFiniteChainsCoefficientMap, coe_extendLocallyFinite, extendLocallyFiniteFun_apply,
    finsum_eq_single _ σ fun τ hτ ↦ by
      simp [matrixCoeff_apply, twistedChainComplexCoefficientMap_f_ι_apply,
        twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne K hτ]]
  simp [matrixCoeff_apply, twistedChainComplexCoefficientMap_f_ι_apply]

/-- The chain map of locally finite chains induced by a morphism of local coefficient systems. -/
def locallyFiniteChainComplexCoefficientMap (η : L ⟶ K) :
    locallyFiniteChainComplex L ⟶ locallyFiniteChainComplex K :=
  extendLocallyFiniteChainMap (twistedChainComplexCoefficientMap η)
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
    extendLocallyFiniteChainMap_congr _
      (fun k ↦ by rw [HomologicalComplex.id_f]; exact isProperlySupported_id)
      (twistedChainComplexCoefficientMap_id L), extendLocallyFiniteChainMap_id]

/-- A composite of morphisms of coefficient systems induces the composite of the maps of locally
finite chains. -/
@[simp, reassoc]
lemma locallyFiniteChainComplexCoefficientMap_comp (η : L ⟶ K) (θ : K ⟶ J) :
    locallyFiniteChainComplexCoefficientMap (η ≫ θ) =
      locallyFiniteChainComplexCoefficientMap η ≫ locallyFiniteChainComplexCoefficientMap θ := by
  rw [locallyFiniteChainComplexCoefficientMap, locallyFiniteChainComplexCoefficientMap,
    locallyFiniteChainComplexCoefficientMap, extendLocallyFiniteChainMap_comp]
  exact extendLocallyFiniteChainMap_congr _ _ (twistedChainComplexCoefficientMap_comp η θ)

/-- Regarding finite chains as locally finite chains commutes with changing the coefficients. -/
@[reassoc]
lemma toLocallyFiniteChainComplex_comp_locallyFiniteChainComplexCoefficientMap (η : L ⟶ K) :
    toLocallyFiniteChainComplex L ≫ locallyFiniteChainComplexCoefficientMap η =
      twistedChainComplexCoefficientMap η ≫ toLocallyFiniteChainComplex K :=
  toLocallyFiniteChainComplex_comp_extendLocallyFiniteChainMap _ _

/-- Change of coefficients on locally finite chains is the extension of change of coefficients
on finite chains. -/
lemma locallyFiniteChainComplexCoefficientMap_eq_extendLocallyFiniteChainMap (η : L ⟶ K) :
    locallyFiniteChainComplexCoefficientMap η =
      extendLocallyFiniteChainMap (twistedChainComplexCoefficientMap η)
        (isProperlySupported_twistedChainComplexCoefficientMap_f η) := (rfl)

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
/-- Pushforward along a proper map has properly supported components on twisted chains. -/
lemma isProperlySupported_twistedChainComplexMap_f (k : ℕ) :
    IsProperlySupported ((twistedChainComplexMap f L).f k) := by
  refine .of_movesAlong hf (movesAlong_iff.2 fun ρ σ x hx ↦ ?_)
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
  extendLocallyFinite (isProperlySupported_twistedChainComplexMap_f f hf L k)

/-- The coefficient of the pushforward of a locally finite chain on a simplex `ρ` is the sum of the
coefficients of the simplices `σ` with `f ∘ σ = ρ`. -/
lemma coe_locallyFiniteChainsMap_apply (c : locallyFiniteChains ((pullback f.hom).obj L) k)
    (ρ : (TopCat.toSSet.obj Y) _⦋k⦌) :
    (locallyFiniteChainsMap f hf L k c : ∀ τ, L.obj (initialVertex τ)) ρ =
      ∑ᶠ σ, (twistedChainComplexCoeff L ρ).hom ((ιTwistedChainComplex L k
        ((TopCat.toSSet.map f).app _ σ)).hom ((c : ∀ τ, ((pullback f.hom).obj L).obj
          (initialVertex τ)) σ)) := by
  rw [locallyFiniteChainsMap, coe_extendLocallyFinite, extendLocallyFiniteFun_apply]
  simp only [matrixCoeff_apply, twistedChainComplexMap_f_ι_apply]

include hf in
/-- The chain map of locally finite chains induced by a proper map. -/
def locallyFiniteChainComplexMap :
    locallyFiniteChainComplex ((pullback f.hom).obj L) ⟶ locallyFiniteChainComplex L :=
  extendLocallyFiniteChainMap (twistedChainComplexMap f L)
    (isProperlySupported_twistedChainComplexMap_f f hf L)

/-- In each degree, the chain map induced by a proper map is `locallyFiniteChainsMap`. -/
@[simp]
lemma locallyFiniteChainComplexMap_f :
    (locallyFiniteChainComplexMap f hf L).f k =
      eqToHom (locallyFiniteChainComplex_X _ k) ≫
        ModuleCat.ofHom (locallyFiniteChainsMap f hf L k) ≫
          eqToHom (locallyFiniteChainComplex_X L k).symm :=
  (rfl)

/-- Proper pushforward on locally finite chains is the extension of pushforward on finite
chains. -/
lemma locallyFiniteChainComplexMap_eq_extendLocallyFiniteChainMap :
    locallyFiniteChainComplexMap f hf L =
      extendLocallyFiniteChainMap (twistedChainComplexMap f L)
        (isProperlySupported_twistedChainComplexMap_f f hf L) := (rfl)

/-- Regarding finite chains as locally finite chains commutes with pushing forward along a proper
map. -/
@[reassoc]
lemma toLocallyFiniteChainComplex_comp_locallyFiniteChainComplexMap :
    toLocallyFiniteChainComplex _ ≫ locallyFiniteChainComplexMap f hf L =
      twistedChainComplexMap f L ≫ toLocallyFiniteChainComplex L :=
  toLocallyFiniteChainComplex_comp_extendLocallyFiniteChainMap _ _

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
    extendLocallyFiniteChainMap_comp, extendLocallyFiniteChainMap_comp]
  exact extendLocallyFiniteChainMap_congr _ _ (twistedChainComplexMap_naturality f η)

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
  extendLocallyFiniteChainMap_congr _ _ (twistedChainComplexMap_id L)

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
    locallyFiniteChainComplexCoefficientMap, extendLocallyFiniteChainMap_comp,
    extendLocallyFiniteChainMap_comp]
  exact extendLocallyFiniteChainMap_congr _ _ (twistedChainComplexMap_comp f g L)

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
