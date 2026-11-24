/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Pushforward
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Relative
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Twist

/-!
# The equivariant cap product with a semi-invariant cocycle

Let a group `G` act on a pair `(X, A)` with an equivariant embedding and on a space `Y`, and let
`p₀ : X ⟶ Y` be equivariant. The relative singular chains of `(X, A)` and the singular chains of `Y`
with coefficients in a commutative ring `k` are complexes of representations of `G`
(`TopPair.singularChainsRep`, `TauCeti.singularChainsRep`). Capping with a relative cocycle `φ` of
degree `n` and pushing forward along `p₀` is a chain map from the relative chains of `(X, A)` to the
chains of `Y` placed `n` degrees higher (`TopPair.pushforwardCapChainMap`), but it is not
equivariant unless `φ` is invariant. This file makes it equivariant when `φ` is semi-invariant: if
`φ`, pulled back to `X`, satisfies `φ(g • c) = χ(g) φ(c)` for a character `χ : G →* kˣ`
(`TopPair.IsSemiInvariantCocycle`), then `p₀_*(g • x ⌢ φ) = χ(g) g • p₀_*(x ⌢ φ)` by naturality
of the cap product, so the cap product is a chain map of complexes of representations

`C(X, A; k) ⟶ (k_χ ⊗ C(Y; k))[n]`

to the chains of `Y` twisted by the one-dimensional representation `k_χ` of `χ` and placed `n`
degrees higher (`TopPair.singularChainsRepCap`).

Forgetting the action of `G`, it is the pushed-forward cap product
(`TopPair.map_singularChainsRepCap_comp_singularChainsRepTwistExtendForget₂Iso_hom`), through the
identifications of the underlying complexes with the relative singular chains of `(X, A)`
(`TopPair.singularChainsRepForget₂Iso`) and with the shifted singular chains of `Y`
(`TauCeti.singularChainsRepTwistExtendForget₂Iso`). Since forgetting the action detects
quasi-isomorphisms, the equivariant cap product is a quasi-isomorphism exactly when
`TopPair.pushforwardCapChainMap` is one (`TopPair.quasiIso_singularChainsRepCap_iff`), for
instance when the relative homology of `(X, A)` vanishes below `n` and `x ↦ p₀_*(x ⌢ [φ])` is an
isomorphism in every degree (`TopPair.quasiIso_pushforwardCapChainMap`), as for the Thom pair of a
vector bundle and a cocycle representing a Thom class. If `G` acts freely on `Y`, the twisted
chains of `Y` are projective representations
(`TauCeti.projective_tensorLeft_singularChainsRep_X`). If moreover `(X, A)` maps to a pair
`(B, B₀)` by quotient covering maps `X ⟶ B` and `A ⟶ B₀`, such a quasi-isomorphism computes the
homology of `(B, B₀)` with twisted coefficients
(`TopPair.twistedHomologyIsoHomologyCoinvariantsTensorObj`).

The intended use is the orientation double cover of a vector bundle `E → B` of rank `r`, with
`G = ℤˣ` acting by the deck involution and `χ` the sign character. A Thom cocycle of the pulled-back
bundle which the deck involution negates is semi-invariant, and the equivariant cap product with it
is the chain map which, after descent, identifies `H_{q+r}(E, E₀; k)` with `H_q(B; o(E) ⊗ k)`, the
homology of the base with coefficients in the orientation system. That identification is not
proved in this file.

## Main definitions

* `TopPair.IsSemiInvariantCocycle`: a relative cocycle which, pulled back to the ambient space,
  satisfies `φ(g • c) = χ(g) φ(c)`.
* `TopPair.singularChainsRepCap`: the equivariant cap product with a semi-invariant relative
  cocycle, followed by the push-forward along an equivariant map.

## Main results

* `TopPair.map_singularChainsRepCap_comp_singularChainsRepTwistExtendForget₂Iso_hom`: forgetting
  the action, the equivariant cap product is `TopPair.pushforwardCapChainMap`.
* `TopPair.quasiIso_singularChainsRepCap_iff`: it is a quasi-isomorphism if and only if
  `TopPair.pushforwardCapChainMap` is one.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Sections I.4, II.4 and III.1.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Sections 3.3 and 3.H.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 and §12.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex TauCeti

universe u

namespace TopPair

variable (P : TopPair.{u}) {k : Type u} [CommRing k] {Y : TopCat.{u}} (p₀ : P.fst ⟶ Y) (n : ℕ)
  (φ : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).cycles n)

variable {P n} in
/-- A relative cocycle `φ` of degree `n` of a pair `(X, A)` is **semi-invariant** for an action of
`G` on `X` and a character `χ : G →* kˣ` if, pulled back to `X`, it satisfies `φ(g • c) = χ(g) φ(c)`
for every `g : G` and every singular `n`-chain `c` of `X`. -/
def IsSemiInvariantCocycle {G : Type u} [Monoid G] [MulAction G P.fst] [ContinuousConstSMul G P.fst]
    (χ : G →* kˣ)
    (φ : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).cycles n) : Prop :=
  ∀ g : G, ((singularChains k).map
      (TopCat.ofHom ⟨(g • · : P.fst → P.fst), continuous_const_smul g⟩)).f n ≫
      (P.singularChainComplexπ (ModuleCat.of k k)).f n ≫
        (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n φ =
    (χ g : k) • ((P.singularChainComplexπ (ModuleCat.of k k)).f n ≫
        (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n φ)

variable {P n} in
/-- Characterization of `TopPair.IsSemiInvariantCocycle`: the pull-back of `φ` to the ambient space
satisfies `φ(g • c) = χ(g) φ(c)`. -/
theorem isSemiInvariantCocycle_iff {G : Type u} [Monoid G] [MulAction G P.fst]
    [ContinuousConstSMul G P.fst] (χ : G →* kˣ)
    (φ : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).cycles n) :
    IsSemiInvariantCocycle χ φ ↔ ∀ g : G, ((singularChains k).map
      (TopCat.ofHom ⟨(g • · : P.fst → P.fst), continuous_const_smul g⟩)).f n ≫
      (P.singularChainComplexπ (ModuleCat.of k k)).f n ≫
        (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n φ =
    (χ g : k) • ((P.singularChainComplexπ (ModuleCat.of k k)).f n ≫
        (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n φ) :=
  Iff.rfl

/-- The relative cocycle `φ` pulled back to a cocycle of the ambient space along the quotient onto
the relative chains. -/
private def pulledCocycle :
    (((TopCat.toSSet.obj P.fst).chainComplex (𝟙_ (ModuleCat.{u} k))).linearYonedaObj k
      (𝟙_ (ModuleCat.{u} k))).cycles n :=
  HomologicalComplex.cyclesMap ((ChainComplex.linearYonedaFunctor k (ModuleCat.of k k)).map
    (P.singularChainComplexπ (ModuleCat.of k k)).op) n φ

/-- The pulled-back cocycle is the precomposition of `φ` with the quotient onto the relative
chains: `ChainComplex.iCycles_cyclesMap_linearYonedaFunctor_map_apply`, stated with the coefficients
`𝟙_ (ModuleCat k)` of the cap product, where the general lemma does not rewrite. -/
private theorem iCycles_pulledCocycle :
    (((TopCat.toSSet.obj P.fst).chainComplex (𝟙_ (ModuleCat.{u} k))).linearYonedaObj k
      (𝟙_ (ModuleCat.{u} k))).iCycles n (pulledCocycle P n φ) =
      (P.singularChainComplexπ (ModuleCat.of k k)).f n ≫
        (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n φ :=
  ChainComplex.iCycles_cyclesMap_linearYonedaFunctor_map_apply _ n φ

/-- Capping a singular `(q + n)`-chain of the ambient space with the pulled-back cocycle and pushing
forward along `p₀`. -/
private def capComponent (q : ℕ) :
    ((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of k k)).X (q + n) ⟶
      ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of k k)).X q :=
  ChainComplex.capChain k (P.fst.alexanderWhitneyDiagonal (λ_ (ModuleCat.of k k)).inv)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of k k)).hom ≫
      SSet.chainComplexMap (TopCat.toSSet.map p₀) (ModuleCat.of k k)) n q (q + n) (by omega)
    ((((TopCat.toSSet.obj P.fst).chainComplex (𝟙_ (ModuleCat.{u} k))).linearYonedaObj k
      (𝟙_ (ModuleCat.{u} k))).iCycles n (pulledCocycle P n φ))

/-- On the image of a singular chain of the ambient space, `TopPair.pushforwardCapChainMap` in
degree `q + n` is `(-1)^(n q)` times `capComponent`. -/
private theorem singularChainComplexπ_f_pushforwardCapChainMap_f (q : ℕ) :
    (P.singularChainComplexπ (ModuleCat.of k k)).f (q + n) ≫
        (P.pushforwardCapChainMap p₀ (ModuleCat.of k k) n
          ((P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n φ)
          (ChainComplex.d_comp_linearYonedaObj_iCycles n (n + 1) φ)).f (q + n) =
      (((-1 : ℤ) ^ (n * q)) • capComponent P p₀ n φ q) ≫
        (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of k k)).extendXIso
          (ComplexShape.embeddingDownNatAdd n) (ComplexShape.embeddingDownNatAdd_f n q)).inv := by
  -- capping a relative chain with `φ` is capping a lift of it with `φ` pulled back
  have h₁ := ChainComplex.capChain_naturality (k := k) (P.alexanderWhitneyDiagonal
      (λ_ (ModuleCat.of k k)).inv)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of k k)).hom ≫
      SSet.chainComplexMap (TopCat.toSSet.map p₀) (ModuleCat.of k k))
    (P.fst.alexanderWhitneyDiagonal (λ_ (ModuleCat.of k k)).inv)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of k k)).hom ≫
      SSet.chainComplexMap (TopCat.toSSet.map p₀) (ModuleCat.of k k))
    (P.singularChainComplexπ (ModuleCat.of k k)) (P.singularChainComplexπ (ModuleCat.of k k))
    (𝟙 _) (𝟙 _) (singularChainComplexπ_alexanderWhitneyDiagonal P _) (by simp) n q (q + n)
    (by omega) ((P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n φ)
  rw [HomologicalComplex.id_f, Category.comp_id] at h₁
  rw [capComponent, pushforwardCapChainMap_def P p₀ (ModuleCat.of k k) n _
      (ChainComplex.d_comp_linearYonedaObj_iCycles n (n + 1) φ),
    ChainComplex.capChainMap_f _ _ (ChainComplex.d_comp_linearYonedaObj_iCycles n (n + 1) φ) q
      (q + n) (by omega), Preadditive.comp_zsmul, Preadditive.zsmul_comp, ← Category.assoc]
  congr 2
  -- `h₁` is stated for cochains on the chains with coefficients `𝟙_ (ModuleCat k)` of the cap
  -- product, which is `ModuleCat.of k k` only after unfolding, so it closes the goal by `exact`
  exact h₁.symm.trans (congrArg _ (iCycles_pulledCocycle P n φ).symm)

variable {P p₀ n φ} in
/-- **The cap product with a semi-invariant cocycle is semi-invariant.** If the cochain `φ`,
pulled back to the ambient space, satisfies `φ(g • c) = χ(g) φ(c)` and `p₀` is equivariant, then
capping with `φ` and pushing forward along `p₀` satisfies `cap(g • c) = χ(g) g • cap(c)`. -/
private theorem capComponent_smul {G : Type u} [Group G] [MulAction G P.fst]
    [ContinuousConstSMul G P.fst] [MulAction G Y] [ContinuousConstSMul G Y]
    (hp₀ : ∀ (g : G) x, p₀ (g • x) = g • p₀ x) (χ : G →* kˣ)
    (hφ : IsSemiInvariantCocycle χ φ)
    (g : G) (q : ℕ) :
    (SSet.chainComplexMap (TopCat.toSSet.map
        (TopCat.ofHom ⟨(g • · : P.fst → P.fst), continuous_const_smul g⟩)) (ModuleCat.of k k)).f
          (q + n) ≫ capComponent P p₀ n φ q =
      (χ g : k) • (capComponent P p₀ n φ q ≫ (SSet.chainComplexMap (TopCat.toSSet.map
        (TopCat.ofHom ⟨(g • · : Y → Y), continuous_const_smul g⟩)) (ModuleCat.of k k)).f q) := by
  have hp : TopCat.ofHom ⟨(g • · : P.fst → P.fst), continuous_const_smul g⟩ ≫ p₀ =
      p₀ ≫ TopCat.ofHom ⟨(g • · : Y → Y), continuous_const_smul g⟩ :=
    ConcreteCategory.hom_ext _ _ fun x ↦ hp₀ g x
  have hc : SSet.chainComplexMap (TopCat.toSSet.map p₀) (ModuleCat.of k k) ≫
      SSet.chainComplexMap (TopCat.toSSet.map
        (TopCat.ofHom ⟨(g • · : Y → Y), continuous_const_smul g⟩)) (ModuleCat.of k k) =
      SSet.chainComplexMap (TopCat.toSSet.map
        (TopCat.ofHom ⟨(g • · : P.fst → P.fst), continuous_const_smul g⟩)) (ModuleCat.of k k) ≫
      SSet.chainComplexMap (TopCat.toSSet.map p₀) (ModuleCat.of k k) := by
    simp only [SSet.chainComplexMap, ← Functor.map_comp, hp]
  have hψ : (SSet.chainComplexMap (TopCat.toSSet.map
      (TopCat.ofHom ⟨(g • · : P.fst → P.fst), continuous_const_smul g⟩)) (ModuleCat.of k k)).f n ≫
        (((TopCat.toSSet.obj P.fst).chainComplex (𝟙_ (ModuleCat.{u} k))).linearYonedaObj k
          (𝟙_ (ModuleCat.{u} k))).iCycles n (pulledCocycle P n φ) =
      (χ g : k) • (((TopCat.toSSet.obj P.fst).chainComplex (𝟙_ (ModuleCat.{u} k))).linearYonedaObj
          k (𝟙_ (ModuleCat.{u} k))).iCycles n (pulledCocycle P n φ) := by
    rw [iCycles_pulledCocycle]
    exact (isSemiInvariantCocycle_iff χ φ).1 hφ g
  have := ChainComplex.capChain_naturality (k := k)
    (P.fst.alexanderWhitneyDiagonal (λ_ (ModuleCat.of k k)).inv)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of k k)).hom ≫
      SSet.chainComplexMap (TopCat.toSSet.map p₀) (ModuleCat.of k k))
    (P.fst.alexanderWhitneyDiagonal (λ_ (ModuleCat.of k k)).inv)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of k k)).hom ≫
      SSet.chainComplexMap (TopCat.toSSet.map p₀) (ModuleCat.of k k))
    (SSet.chainComplexMap (TopCat.toSSet.map
      (TopCat.ofHom ⟨(g • · : P.fst → P.fst), continuous_const_smul g⟩)) (ModuleCat.of k k))
    (SSet.chainComplexMap (TopCat.toSSet.map
      (TopCat.ofHom ⟨(g • · : P.fst → P.fst), continuous_const_smul g⟩)) (ModuleCat.of k k))
    (SSet.chainComplexMap (TopCat.toSSet.map
      (TopCat.ofHom ⟨(g • · : P.fst → P.fst), continuous_const_smul g⟩)) (ModuleCat.of k k))
    (SSet.chainComplexMap (TopCat.toSSet.map
      (TopCat.ofHom ⟨(g • · : Y → Y), continuous_const_smul g⟩)) (ModuleCat.of k k))
    (TopCat.alexanderWhitneyDiagonal_naturality _ _) (by
      rw [Category.assoc, hc, ← Category.assoc, ← SSet.chainComplexPairing_naturality,
        Category.assoc]) n q (q + n) (by omega)
    ((((TopCat.toSSet.obj P.fst).chainComplex (𝟙_ (ModuleCat.{u} k))).linearYonedaObj k
      (𝟙_ (ModuleCat.{u} k))).iCycles n (pulledCocycle P n φ))
  rw [hψ] at this
  -- `χ g` acts on the pulled-back cocycle through the module of cochains on the chains with
  -- coefficients `𝟙_ (ModuleCat k)`, which is the `k`-module structure of the domain of the cap
  -- product only after unfolding, so `map_smul` is applied by `exact`
  refine this.symm.trans ?_
  rw [← Linear.smul_comp]
  exact congrArg (· ≫ _) (map_smul _ _ _)

/-- The cap product `capComponent` with the sign `(-1)^(n q)` of `TopPair.pushforwardCapChainMap`
in degree `q + n`. -/
private def signedCapComponent (q : ℕ) :
    ((singularChains k).obj P.fst).X (q + n) ⟶ ((singularChains k).obj Y).X q :=
  ((-1 : ℤ) ^ (n * q)) • capComponent P p₀ n φ q

/-- The sign-corrected cap products commute with the boundaries: they are the components of the
chain map `TauCeti.ChainComplex.capChainMap` of the cocycle `φ` pulled back to the ambient space. -/
private theorem signedCapComponent_comp_d (q : ℕ) :
    signedCapComponent P p₀ n φ (q + 1) ≫ ((singularChains k).obj Y).d (q + 1) q =
      ((singularChains k).obj P.fst).d (q + 1 + n) (q + n) ≫ signedCapComponent P p₀ n φ q := by
  have hψ := ChainComplex.d_comp_linearYonedaObj_iCycles n (n + 1) (pulledCocycle P n φ)
  have h := (ChainComplex.capChainMap k
    (P.fst.alexanderWhitneyDiagonal (λ_ (ModuleCat.of k k)).inv)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of k k)).hom ≫
      SSet.chainComplexMap (TopCat.toSSet.map p₀) (ModuleCat.of k k)) n _ hψ).comm
    (q + 1 + n) (q + n)
  rw [ChainComplex.capChainMap_f _ _ hψ (q + 1) _ (by omega),
    ChainComplex.capChainMap_f _ _ hψ q _ (by omega),
    HomologicalComplex.extend_d_eq _ _ (ComplexShape.embeddingDownNatAdd_f n (q + 1))
      (ComplexShape.embeddingDownNatAdd_f n q)] at h
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Preadditive.zsmul_comp] at h
  -- `(singularChains k).obj X` is `(TopCat.toSSet.obj X).chainComplex (ModuleCat.of k k)` and
  -- `signedCapComponent` is `(-1)^(n q) • capComponent` only after unfolding, which `rw` does not
  -- see through, so the cancellation is applied by `refine` and `h` closes the goal by `exact`
  refine (cancel_mono (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of k k)).extendXIso
    (ComplexShape.embeddingDownNatAdd n) (ComplexShape.embeddingDownNatAdd_f n q)).inv).1 ?_
  exact h

variable {P p₀ n φ} in
/-- The sign-corrected cap products with a semi-invariant cocycle are semi-invariant:
`cap(g • c) = χ(g) g • cap(c)`. -/
private theorem signedCapComponent_apply_smul {G : Type u} [Group G] [MulAction G P.fst]
    [ContinuousConstSMul G P.fst] [MulAction G Y] [ContinuousConstSMul G Y]
    (hp₀ : ∀ (g : G) x, p₀ (g • x) = g • p₀ x) (χ : G →* kˣ)
    (hφ : IsSemiInvariantCocycle χ φ)
    (g : G) (q : ℕ) (c : ((singularChains k).obj P.fst).X (q + n)) :
    (signedCapComponent P p₀ n φ q).hom (singularChainsRepresentation k P.fst G (q + n) g c) =
      (χ g : k) •
        singularChainsRepresentation k Y G q g ((signedCapComponent P p₀ n φ q).hom c) := by
  rw [singularChainsRepresentation_apply, singularChainsRepresentation_apply]
  -- `singularChainsRepresentation` acts by `((singularChains k).map _).f`, which is the
  -- push-forward `(SSet.chainComplexMap (TopCat.toSSet.map _) (ModuleCat.of k k)).f` of
  -- `capComponent_smul` only after unfolding `singularChains`, so the goal is restated in that form
  revert c
  change ∀ c : ((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of k k)).X (q + n),
    ((-1 : ℤ) ^ (n * q) • capComponent P p₀ n φ q).hom
      (((SSet.chainComplexMap (TopCat.toSSet.map
        (TopCat.ofHom ⟨(g • · : P.fst → P.fst), continuous_const_smul g⟩)) (ModuleCat.of k k)).f
          (q + n)).hom c) =
    (χ g : k) • ((SSet.chainComplexMap (TopCat.toSSet.map
        (TopCat.ofHom ⟨(g • · : Y → Y), continuous_const_smul g⟩)) (ModuleCat.of k k)).f q).hom
      (((-1 : ℤ) ^ (n * q) • capComponent P p₀ n φ q).hom c)
  intro c
  rw [ModuleCat.hom_zsmul, LinearMap.smul_apply, LinearMap.smul_apply, ← LinearMap.comp_apply,
    ← ModuleCat.hom_comp, capComponent_smul hp₀ χ hφ g q, ModuleCat.hom_smul, LinearMap.smul_apply,
    ModuleCat.hom_comp, LinearMap.comp_apply, map_zsmul, smul_comm]

/-- The cap product with a relative cocycle vanishes on the chains of the subspace. -/
private theorem map_f_comp_signedCapComponent (q : ℕ) :
    ((singularChains k).map P.map).f (q + n) ≫ signedCapComponent P p₀ n φ q = 0 := by
  refine (cancel_mono (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of k k)).extendXIso
    (ComplexShape.embeddingDownNatAdd n) (ComplexShape.embeddingDownNatAdd_f n q)).inv).1 ?_
  -- the chains of the subspace vanish in the relative chains. The push-forward
  -- `(singularChains k).map P.map` is `SSet.chainComplexMap (TopPair.toSSetPair.obj P).hom _` of
  -- `chainComplex_condition_f` only after unfolding `singularChainComplexFunctor` and
  -- `TopPair.toSSetPair`, which `rw` does not see through, so the steps are assembled in term mode
  exact (Category.assoc _ _ _).trans ((congrArg (((singularChains k).map P.map).f (q + n) ≫ ·)
    (singularChainComplexπ_f_pushforwardCapChainMap_f P p₀ n φ q).symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
        ((TopPair.toSSetPair.obj P).chainComplex_condition_f (ModuleCat.of k k) (q + n))).trans
          (Limits.zero_comp.trans Limits.zero_comp.symm))))

section Rep

variable {G : Type u} [Group G] [MulAction G P.fst] [ContinuousConstSMul G P.fst] [MulAction G Y]
  [ContinuousConstSMul G Y] {p₀} (hp₀ : ∀ (g : G) x, p₀ (g • x) = g • p₀ x) (χ : G →* kˣ) {n φ}
  (hφ : IsSemiInvariantCocycle χ φ)

include hp₀ hφ in
/-- The sign-corrected cap product in degree `q + n`, as an equivariant map from the singular
chains of the ambient space to the singular chains of `Y` twisted by the character `χ`. -/
private def capRep (q : ℕ) :
    (TauCeti.singularChainsRep k P.fst G).X (q + n) ⟶
      Rep.of (Representation.ofLinearCharacter χ) ⊗ (TauCeti.singularChainsRep k Y G).X q :=
  Rep.ofHom
    { toLinearMap := TensorProduct.mk k k (((singularChains k).obj Y).X q) 1 ∘ₗ
        (signedCapComponent P p₀ n φ q).hom
      isIntertwining' g := LinearMap.ext fun c ↦ by
        -- the carriers of the representations are those of the singular chain modules, with module
        -- structures that agree only after unfolding, so the composite is evaluated by `change`
        change (1 : k) ⊗ₜ[k] (signedCapComponent P p₀ n φ q).hom
            (singularChainsRepresentation k P.fst G (q + n) g c) =
          (Representation.ofLinearCharacter χ).tprod (singularChainsRepresentation k Y G q) g
            ((1 : k) ⊗ₜ[k] (signedCapComponent P p₀ n φ q).hom c)
        rw [signedCapComponent_apply_smul hp₀ χ hφ,
          Representation.tprod_apply, TensorProduct.map_tmul,
          Representation.ofLinearCharacter_apply, mul_one, ← TensorProduct.smul_tmul, smul_eq_mul,
          mul_one] }

include hp₀ hφ in
/-- The equivariant sign-corrected cap products commute with the boundaries. -/
private theorem capRep_comp_d (q : ℕ) :
    capRep P hp₀ χ hφ (q + 1) ≫ (Rep.of (Representation.ofLinearCharacter χ) ◁
        (TauCeti.singularChainsRep k Y G).d (q + 1) q) =
      (TauCeti.singularChainsRep k P.fst G).d (q + 1 + n) (q + n) ≫ capRep P hp₀ χ hφ q := by
  have h := signedCapComponent_comp_d P p₀ n φ q
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun c ↦ ?_))
  -- evaluate both composites on `c`: the carriers are those of the singular chain modules
  change (1 : k) ⊗ₜ[k] ((TauCeti.singularChainsRep k Y G).d (q + 1) q).hom
      ((signedCapComponent P p₀ n φ (q + 1)).hom c) =
    (1 : k) ⊗ₜ[k] (signedCapComponent P p₀ n φ q).hom
      (((TauCeti.singularChainsRep k P.fst G).d (q + 1 + n) (q + n)).hom c)
  rw [singularChainsRep_d_hom_apply, singularChainsRep_d_hom_apply k P.fst G _ _ c]
  exact congrArg ((1 : k) ⊗ₜ[k] ·) (ConcreteCategory.congr_hom h c)

include hp₀ hφ in
/-- The equivariant sign-corrected cap products, as a chain map from the singular chains of the
ambient space in the degrees at least `n` to the singular chains of `Y` twisted by `χ`. -/
private def capRestrictionHom :
    (TauCeti.singularChainsRep k P.fst G).restriction (ComplexShape.embeddingDownNatAdd n) ⟶
      ((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex _).obj
        (TauCeti.singularChainsRep k Y G) where
  f q := ((TauCeti.singularChainsRep k P.fst G).restrictionXIso _
    (ComplexShape.embeddingDownNatAdd_f n q)).hom ≫ capRep P hp₀ χ hφ q
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rw [HomologicalComplex.restriction_d_eq _ _ (ComplexShape.embeddingDownNatAdd_f n (j + 1))
      (ComplexShape.embeddingDownNatAdd_f n j), Functor.mapHomologicalComplex_obj_d]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact congrArg (_ ≫ ·) (capRep_comp_d P hp₀ χ hφ j)

include hp₀ hφ in
/-- The equivariant sign-corrected cap products, as a chain map from the singular chains of the
ambient space to the singular chains of `Y` twisted by `χ` and shifted up by `n`. -/
private def capAmbient :
    TauCeti.singularChainsRep k P.fst G ⟶
      (((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex _).obj
        (TauCeti.singularChainsRep k Y G)).extend (ComplexShape.embeddingDownNatAdd n) :=
  (ComplexShape.embeddingDownNatAdd n).liftExtend (capRestrictionHom P hp₀ χ hφ)
    fun _ hj ↦ hj.false_of_isTruncLE.elim

include hp₀ hφ in
/-- In degree `q + n`, `capAmbient` is `capRep` followed by the identification of the twisted chains
of `Y` in degree `q` with the shifted complex in degree `q + n`. -/
private theorem capAmbient_f (q : ℕ) :
    (capAmbient P hp₀ χ hφ).f (q + n) = capRep P hp₀ χ hφ q ≫
      ((((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex _).obj
        (TauCeti.singularChainsRep k Y G)).extendXIso (ComplexShape.embeddingDownNatAdd n)
          (ComplexShape.embeddingDownNatAdd_f n q)).inv := by
  refine ((ComplexShape.embeddingDownNatAdd n).liftExtend_f _ _
    (ComplexShape.embeddingDownNatAdd_f n q)).trans ?_
  simp only [capRestrictionHom, Category.assoc, Iso.inv_hom_id_assoc]

variable [MulAction G P.snd] [ContinuousConstSMul G P.snd]
  (hP : ∀ (g : G) x, P.map (g • x) = g • P.map x)

include hp₀ hφ in
/-- The equivariant cap product vanishes on the chains of the subspace. -/
private theorem singularChainsRepι_comp_capAmbient :
    P.singularChainsRepι k G hP ≫ capAmbient P hp₀ χ hφ = 0 := by
  ext m : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
  rcases lt_or_ge m n with hm | hm
  · exact (HomologicalComplex.isZero_extend_embeddingDownNatAdd_X _ hm).eq_of_tgt _ _
  · obtain ⟨q, rfl⟩ : ∃ q, m = q + n := ⟨m - n, by omega⟩
    rw [capAmbient_f, ← Category.assoc]
    convert Limits.zero_comp
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun c ↦ ?_))
    -- evaluate on `c`: the cap product vanishes on the image of the chains of the subspace
    change (capRep P hp₀ χ hφ q).hom (((P.singularChainsRepι k G hP).f (q + n)).hom c) = 0
    rw [singularChainsRepι_f_hom_apply P k hP (q + n) c]
    -- the underlying linear map of `capRep` is `c ↦ 1 ⊗ signedCapComponent c`, by its definition
    change (1 : k) ⊗ₜ[k] (signedCapComponent P p₀ n φ q).hom
        (((singularChains k).map P.map).f (q + n) c) = 0
    rw [← TensorProduct.tmul_zero (R := k) (((singularChains k).obj Y).X q) (1 : k)]
    exact congrArg ((1 : k) ⊗ₜ[k] ·) (ConcreteCategory.congr_hom
      (map_f_comp_signedCapComponent P p₀ n φ q) c)

include hp₀ hφ in
/-- **The equivariant cap product with a semi-invariant cocycle.** Let `G` act on a pair `(X, A)`
with an equivariant embedding and on a space `Y`, let `p₀ : X ⟶ Y` be equivariant, and let `φ` be a
relative cocycle of degree `n` which, pulled back to `X`, satisfies `φ(g • c) = χ(g) φ(c)` for a
character `χ : G →* kˣ`. Then `x ↦ (-1)^(n q) p₀_*(x ⌢ φ)` in degree `q + n` is a chain map of
complexes of representations from the relative chains of `(X, A)` to the singular chains of `Y`
twisted by `χ` and placed `n` degrees higher: `TopPair.pushforwardCapChainMap`, made equivariant. -/
def singularChainsRepCap :
    P.singularChainsRep k G hP ⟶
      (((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex _).obj
        (TauCeti.singularChainsRep k Y G)).extend (ComplexShape.embeddingDownNatAdd n) :=
  (CokernelCofork.IsColimit.desc' (P.isColimitCokernelCoforkSingularChainsRep k G hP)
    (capAmbient P hp₀ χ hφ) (singularChainsRepι_comp_capAmbient P hp₀ χ hφ hP)).val

include hp₀ hφ in
/-- On the equivariant chains of the ambient space, `singularChainsRepCap` is `capAmbient`. -/
private theorem singularChainsRepπ_singularChainsRepCap :
    P.singularChainsRepπ k G hP ≫ P.singularChainsRepCap hp₀ χ hφ hP =
      capAmbient P hp₀ χ hφ :=
  (CokernelCofork.IsColimit.desc' (P.isColimitCokernelCoforkSingularChainsRep k G hP)
    (capAmbient P hp₀ χ hφ) (singularChainsRepι_comp_capAmbient P hp₀ χ hφ hP)).property

include hp₀ hφ in
/-- **Forgetting the action, `singularChainsRepCap` is `TopPair.pushforwardCapChainMap`.** Under the
identifications of the underlying complexes with the relative singular chains of `(X, A)` and with
the shifted singular chains of `Y`, the equivariant cap product is the pushed-forward cap product
with `φ`. -/
theorem map_singularChainsRepCap_comp_singularChainsRepTwistExtendForget₂Iso_hom :
    ((forget₂ (Rep.{u} k G) (ModuleCat.{u} k)).mapHomologicalComplex _).map
        (P.singularChainsRepCap hp₀ χ hφ hP) ≫
        (singularChainsRepTwistExtendForget₂Iso k Y χ n).hom =
      (P.singularChainsRepForget₂Iso k G hP).hom ≫
        P.pushforwardCapChainMap p₀ (ModuleCat.of k k) n
            ((P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n φ)
            (ChainComplex.d_comp_linearYonedaObj_iCycles n (n + 1) φ) := by
  rw [← cancel_epi (((forget₂ (Rep.{u} k G) (ModuleCat.{u} k)).mapHomologicalComplex _).map
      (P.singularChainsRepπ k G hP)), ← Functor.map_comp_assoc,
    singularChainsRepπ_singularChainsRepCap, ← Category.assoc,
    map_singularChainsRepπ_singularChainsRepForget₂Iso_hom]
  ext m : 1
  -- the forgetful identification of the ambient chains has identity components. Its target
  -- `(singularChains k).obj P.fst` is `(TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of k k)`,
  -- the source of `P.singularChainComplexπ`, only after unfolding `singularChainComplexFunctor`,
  -- which `rw` and `simp` do not see through, so this step is assembled in term mode
  refine Eq.trans ?_ ((HomologicalComplex.comp_f _ _ m).trans (congrArg (· ≫ _)
    ((HomologicalComplex.comp_f _ _ m).trans ((congrArg (· ≫ _)
      (TauCeti.singularChainsRepForget₂Iso_hom_f k P.fst G m)).trans
        (Category.id_comp _))))).symm
  rw [HomologicalComplex.comp_f]
  rcases lt_or_ge m n with hm | hm
  · exact (HomologicalComplex.isZero_extend_embeddingDownNatAdd_X _ hm).eq_of_tgt _ _
  · obtain ⟨q, rfl⟩ : ∃ q, m = q + n := ⟨m - n, by omega⟩
    refine Eq.trans ?_ (singularChainComplexπ_f_pushforwardCapChainMap_f P p₀ n φ q).symm
    rw [Functor.mapHomologicalComplex_map_f, capAmbient_f,
      singularChainsRepTwistExtendForget₂Iso_hom_f]
    simp only [Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    -- forgetting the twist sends `1 ⊗ c` to `c`
    have hc : (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)).map (capRep P hp₀ χ hφ q) ≫
        (singularChainsRepTwistForget₂Iso k Y χ).hom.f q = signedCapComponent P p₀ n φ q := by
      refine ModuleCat.hom_ext (LinearMap.ext fun c ↦ ?_)
      rw [singularChainsRepTwistForget₂Iso_hom_f]
      change TensorProduct.lid k _ ((1 : k) ⊗ₜ[k] (signedCapComponent P p₀ n φ q).hom c) = _
      rw [TensorProduct.lid_tmul, one_smul]
      -- the two sides differ only in the carrier of the forgotten representation
      rfl
    rw [← Category.assoc, hc]
    -- `signedCapComponent` is `(-1)^(n q) • capComponent` by definition
    rfl

include hp₀ hφ in
/-- **When the equivariant cap product is a quasi-isomorphism.** The equivariant cap product
`singularChainsRepCap` with a semi-invariant relative cocycle `φ` of degree `n` is a
quasi-isomorphism of complexes of representations if and only if the pushed-forward cap product
`TopPair.pushforwardCapChainMap` with `φ` is a quasi-isomorphism, as forgetting the action detects
quasi-isomorphisms. -/
theorem quasiIso_singularChainsRepCap_iff :
    QuasiIso (P.singularChainsRepCap hp₀ χ hφ hP) ↔
      QuasiIso (P.pushforwardCapChainMap p₀ (ModuleCat.of k k) n
        ((P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n φ)
        (ChainComplex.d_comp_linearYonedaObj_iCycles n (n + 1) φ)) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
      (forget₂ (Rep.{u} k G) (ModuleCat.{u} k))]
  exact quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk (P.singularChainsRepForget₂Iso k G hP)
    (singularChainsRepTwistExtendForget₂Iso k Y χ n)
    (map_singularChainsRepCap_comp_singularChainsRepTwistExtendForget₂Iso_hom P hp₀ χ hφ hP).symm)

end Rep

end TopPair
