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

The equivariant cap product depends on `φ` only up to semi-invariant coboundaries. If
`φ' = φ + δη` for a relative cochain `η` of degree `n - 1` which is semi-invariant in the same sense
(`TopPair.IsSemiInvariantCochain`), the boundary formula `∂(x ⌢ η) = ±(∂x ⌢ η - x ⌢ δη)`
(`TauCeti.ChainComplex.capChain_d_comp`) makes capping with `η` a homotopy between the
equivariant cap products with `φ'` and with `φ`, by equivariant maps
(`TopPair.singularChainsRepCapHomotopy`). Any additive functor, such as coinvariants, then takes
them to homotopic chain maps, so what is computed after descent depends only on the class of `φ`
among semi-invariant cocycles.

The intended use is the orientation double cover of a vector bundle `E → B` of rank `r`, with
`G = ℤˣ` acting by the deck involution and `χ` the sign character. A Thom cocycle of the pulled-back
bundle which the deck involution negates is semi-invariant, and the equivariant cap product with it
is the chain map which, after descent, identifies `H_{q+r}(E, E₀; k)` with `H_q(B; o(E) ⊗ k)`, the
homology of the base with coefficients in the orientation system. That identification is not
proved in this file.

## Main definitions

* `TopPair.IsSemiInvariantCochain`: a relative cochain which, pulled back to the ambient space,
  satisfies `ψ(g • c) = χ(g) ψ(c)`, and `TopPair.IsSemiInvariantCocycle`: a relative cocycle whose
  underlying cochain is semi-invariant.
* `TopPair.singularChainsRepCap`: the equivariant cap product with a semi-invariant relative
  cocycle, followed by the push-forward along an equivariant map.
* `TopPair.singularChainsRepCapHomotopy`: the homotopy between the equivariant cap products with
  semi-invariant cocycles which differ by the coboundary of a semi-invariant cochain.

## Main results

* `TopPair.IsSemiInvariantCocycle.cyclesMap_singularCochainComplexMap`: semi-invariant cocycles pull
  back to semi-invariant cocycles along maps of pairs which are equivariant along a homomorphism of
  the acting monoids.
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
/-- A relative cochain `ψ` of degree `n` of a pair `(X, A)` is **semi-invariant** for an action of
`G` on `X` and a character `χ : G →* kˣ` if, pulled back to `X`, it satisfies `ψ(g • c) = χ(g) ψ(c)`
for every `g : G` and every singular `n`-chain `c` of `X`. -/
def IsSemiInvariantCochain {G : Type u} [Monoid G] [MulAction G P.fst]
    [ContinuousConstSMul G P.fst] (χ : G →* kˣ)
    (ψ : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X n) : Prop :=
  ∀ g : G, ((singularChains k).map
      (TopCat.ofHom ⟨(g • · : P.fst → P.fst), continuous_const_smul g⟩)).f n ≫
      (P.singularChainComplexπ (ModuleCat.of k k)).f n ≫ ψ =
    (χ g : k) • ((P.singularChainComplexπ (ModuleCat.of k k)).f n ≫ ψ)

variable {P n} in
/-- Characterization of `TopPair.IsSemiInvariantCochain`: the pull-back of `ψ` to the ambient space
satisfies `ψ(g • c) = χ(g) ψ(c)`. -/
theorem isSemiInvariantCochain_iff {G : Type u} [Monoid G] [MulAction G P.fst]
    [ContinuousConstSMul G P.fst] (χ : G →* kˣ)
    (ψ : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X n) :
    IsSemiInvariantCochain χ ψ ↔ ∀ g : G, ((singularChains k).map
      (TopCat.ofHom ⟨(g • · : P.fst → P.fst), continuous_const_smul g⟩)).f n ≫
      (P.singularChainComplexπ (ModuleCat.of k k)).f n ≫ ψ =
    (χ g : k) • ((P.singularChainComplexπ (ModuleCat.of k k)).f n ≫ ψ) :=
  Iff.rfl

variable {P n} in
/-- A relative cocycle `φ` of degree `n` of a pair `(X, A)` is **semi-invariant** for an action of
`G` on `X` and a character `χ : G →* kˣ` if, pulled back to `X`, it satisfies `φ(g • c) = χ(g) φ(c)`
for every `g : G` and every singular `n`-chain `c` of `X`: its underlying cochain is
semi-invariant (`TopPair.IsSemiInvariantCochain`). -/
def IsSemiInvariantCocycle {G : Type u} [Monoid G] [MulAction G P.fst] [ContinuousConstSMul G P.fst]
    (χ : G →* kˣ)
    (φ : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).cycles n) : Prop :=
  IsSemiInvariantCochain χ
    ((P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n φ)

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

variable {P n} in
/-- A relative cocycle is semi-invariant exactly when its underlying cochain is. -/
theorem isSemiInvariantCocycle_iff_isSemiInvariantCochain {G : Type u} [Monoid G]
    [MulAction G P.fst] [ContinuousConstSMul G P.fst] (χ : G →* kˣ)
    (φ : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).cycles n) :
    IsSemiInvariantCocycle χ φ ↔ IsSemiInvariantCochain χ
      ((P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n φ) :=
  Iff.rfl

variable {P n} in
/-- **Semi-invariant cocycles pull back along equivariant maps.** Let `f : P ⟶ P'` be a map of
pairs whose ambient map satisfies `f(g • x) = ρ(g) • f(x)` for a homomorphism `ρ : G →* H`. If a
relative cocycle `φ` of `P'` is semi-invariant for a character `χ` of `H`, then its pull-back
`f^* φ` to `P` is semi-invariant for the character `χ ∘ ρ` of `G`. -/
theorem IsSemiInvariantCocycle.cyclesMap_singularCochainComplexMap {P' : TopPair.{u}}
    {G H : Type u} [Monoid G] [Monoid H] [MulAction G P.fst] [ContinuousConstSMul G P.fst]
    [MulAction H P'.fst] [ContinuousConstSMul H P'.fst] (f : P ⟶ P') (ρ : G →* H)
    (hf : ∀ (g : G) x, Hom.fst f (g • x) = ρ g • Hom.fst f x) {χ : H →* kˣ}
    {φ : (P'.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).cycles n}
    (hφ : IsSemiInvariantCocycle χ φ) :
    IsSemiInvariantCocycle (χ.comp ρ)
      (HomologicalComplex.cyclesMap (singularCochainComplexMap f) n φ) := by
  intro g
  have hi : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n
      (HomologicalComplex.cyclesMap (singularCochainComplexMap f) n φ) =
      (singularChainComplexMap f (ModuleCat.of k k)).f n ≫
        (P'.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n φ :=
    congr(ModuleCat.Hom.hom $(HomologicalComplex.cyclesMap_i (singularCochainComplexMap f) n) φ)
  -- the quotient onto the relative chains is natural in `f`; the composites of
  -- `singularChainComplexπ_pair_naturality` are formed in the category of chain complexes of the
  -- singular simplicial set, so its component in degree `n` is restated here
  have hπ : ((singularChains k).map (Hom.fst f)).f n ≫
      (P'.singularChainComplexπ (ModuleCat.of k k)).f n =
      (P.singularChainComplexπ (ModuleCat.of k k)).f n ≫
        (singularChainComplexMap f (ModuleCat.of k k)).f n :=
    HomologicalComplex.congr_hom (singularChainComplexπ_pair_naturality f (ModuleCat.of k k)) n
  -- acting by `g` and then mapping by `f` is mapping by `f` and then acting by `ρ g`
  have hg : TopCat.ofHom ⟨(g • · : P.fst → P.fst), continuous_const_smul g⟩ ≫ Hom.fst f =
      Hom.fst f ≫ TopCat.ofHom ⟨(ρ g • · : P'.fst → P'.fst), continuous_const_smul (ρ g)⟩ :=
    ConcreteCategory.hom_ext _ _ fun x ↦ hf g x
  have hc := congrArg (fun h ↦ ((singularChains k).map h).f n) hg
  simp only [Functor.map_comp, HomologicalComplex.comp_f] at hc
  have hπ' : (P.singularChainComplexπ (ModuleCat.of k k)).f n ≫
      (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n
        (HomologicalComplex.cyclesMap (singularCochainComplexMap f) n φ) =
      ((singularChains k).map (Hom.fst f)).f n ≫ (P'.singularChainComplexπ (ModuleCat.of k k)).f n ≫
        (P'.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n φ := by
    rw [hi]
    exact (congrArg (· ≫ _) hπ).symm
  -- `erw`: the composites in `IsSemiInvariantCocycle` are formed in the category of chain
  -- complexes of the singular simplicial set rather than in `ModuleCat k`, as for `hπ`; the closing
  -- `rfl` evaluates `χ.comp ρ` at `g`
  erw [hπ', ← Category.assoc, hc, Category.assoc, hφ (ρ g), Linear.comp_smul]
  rfl

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

variable {n} in
/-- A relative cochain `ψ` pulled back to a cochain of the ambient space along the quotient onto
the relative chains, with the coefficients `𝟙_ (ModuleCat k)` of the cap product. -/
private def pulledCochain
    (ψ : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X n) :
    ((TopCat.toSSet.obj P.fst).chainComplex (𝟙_ (ModuleCat.{u} k))).X n ⟶ 𝟙_ (ModuleCat.{u} k) :=
  (P.singularChainComplexπ (ModuleCat.of k k)).f n ≫ ψ

variable {n} in
/-- Capping a singular `m`-chain of the ambient space, `m = n + q`, with a relative cochain `ψ` of
degree `n` pulled back to the ambient space, and pushing forward along `p₀`. -/
private def capComponent
    (ψ : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X n)
    (q m : ℕ) (h : n + q = m) :
    ((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of k k)).X m ⟶
      ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of k k)).X q :=
  ChainComplex.capChain k (P.fst.alexanderWhitneyDiagonal (λ_ (ModuleCat.of k k)).inv)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of k k)).hom ≫
      SSet.chainComplexMap (TopCat.toSSet.map p₀) (ModuleCat.of k k)) n q m h
    (pulledCochain P ψ)

variable {n} in
/-- Capping a relative chain with a relative cochain `ψ` along the relative Alexander–Whitney
diagonal is capping a lift of it to the ambient space with `ψ` pulled back. -/
private theorem singularChainComplexπ_f_capChain
    (ψ : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X n) (q m : ℕ)
    (h : n + q = m) :
    (P.singularChainComplexπ (ModuleCat.of k k)).f m ≫
        ChainComplex.capChain k (P.alexanderWhitneyDiagonal (λ_ (ModuleCat.of k k)).inv)
          ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of k k)).hom ≫
            SSet.chainComplexMap (TopCat.toSSet.map p₀) (ModuleCat.of k k)) n q m h ψ =
      capComponent P p₀ ψ q m h := by
  have h₁ := ChainComplex.capChain_naturality (k := k) (P.alexanderWhitneyDiagonal
      (λ_ (ModuleCat.of k k)).inv)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of k k)).hom ≫
      SSet.chainComplexMap (TopCat.toSSet.map p₀) (ModuleCat.of k k))
    (P.fst.alexanderWhitneyDiagonal (λ_ (ModuleCat.of k k)).inv)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of k k)).hom ≫
      SSet.chainComplexMap (TopCat.toSSet.map p₀) (ModuleCat.of k k))
    (P.singularChainComplexπ (ModuleCat.of k k)) (P.singularChainComplexπ (ModuleCat.of k k))
    (𝟙 _) (𝟙 _) (singularChainComplexπ_alexanderWhitneyDiagonal P _) (by simp) n q m h ψ
  rw [HomologicalComplex.id_f, Category.comp_id] at h₁
  -- `h₁` caps with `π ≫ ψ` on the chains with coefficients `ModuleCat.of k k`, which is the pulled
  -- back cochain of `capComponent` on the chains with coefficients `𝟙_ (ModuleCat k)` only after
  -- unfolding, so it closes the goal by `exact`
  exact h₁.symm

/-- On the image of a singular chain of the ambient space, `TopPair.pushforwardCapChainMap` in
degree `q + n` is `(-1)^(n q)` times `capComponent`. -/
private theorem singularChainComplexπ_f_pushforwardCapChainMap_f (q : ℕ) :
    (P.singularChainComplexπ (ModuleCat.of k k)).f (q + n) ≫
        (P.pushforwardCapChainMap p₀ (ModuleCat.of k k) n
          ((P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n φ)
          (ChainComplex.d_comp_linearYonedaObj_iCycles n (n + 1) φ)).f (q + n) =
      (((-1 : ℤ) ^ (n * q)) • capComponent P p₀
          ((P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n φ) q (q + n)
          (n.add_comm q)) ≫
        (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of k k)).extendXIso
          (ComplexShape.embeddingDownNatAdd n) (ComplexShape.embeddingDownNatAdd_f n q)).inv := by
  rw [pushforwardCapChainMap_def P p₀ (ModuleCat.of k k) n _
      (ChainComplex.d_comp_linearYonedaObj_iCycles n (n + 1) φ),
    ChainComplex.capChainMap_f _ _ (ChainComplex.d_comp_linearYonedaObj_iCycles n (n + 1) φ) q
      (q + n) (by omega), Preadditive.comp_zsmul, Preadditive.zsmul_comp, ← Category.assoc]
  congr 2
  exact singularChainComplexπ_f_capChain P p₀ _ q (q + n) (n.add_comm q)

variable {P p₀ n} in
/-- **The cap product with a semi-invariant cochain is semi-invariant.** If the cochain `ψ`,
pulled back to the ambient space, satisfies `ψ(g • c) = χ(g) ψ(c)` and `p₀` is equivariant, then
capping with `ψ` and pushing forward along `p₀` satisfies `cap(g • c) = χ(g) g • cap(c)`. -/
private theorem capComponent_smul {G : Type u} [Group G] [MulAction G P.fst]
    [ContinuousConstSMul G P.fst] [MulAction G Y] [ContinuousConstSMul G Y]
    (hp₀ : ∀ (g : G) x, p₀ (g • x) = g • p₀ x) (χ : G →* kˣ)
    {ψ : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X n}
    (hψ : IsSemiInvariantCochain χ ψ) (g : G) (q m : ℕ) (h : n + q = m) :
    (SSet.chainComplexMap (TopCat.toSSet.map
        (TopCat.ofHom ⟨(g • · : P.fst → P.fst), continuous_const_smul g⟩)) (ModuleCat.of k k)).f
          m ≫ capComponent P p₀ ψ q m h =
      (χ g : k) • (capComponent P p₀ ψ q m h ≫ (SSet.chainComplexMap (TopCat.toSSet.map
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
  -- the semi-invariance of `ψ` is stated on the chains with coefficients `ModuleCat.of k k`, which
  -- are those of the pulled-back cochain only after unfolding, so it is applied by `exact`
  have hψ' : (SSet.chainComplexMap (TopCat.toSSet.map
      (TopCat.ofHom ⟨(g • · : P.fst → P.fst), continuous_const_smul g⟩)) (ModuleCat.of k k)).f n ≫
        pulledCochain P ψ = (χ g : k) • pulledCochain P ψ :=
    hψ g
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
        Category.assoc]) n q m h (pulledCochain P ψ)
  rw [hψ'] at this
  -- `χ g` acts on the pulled-back cochain through the module of cochains on the chains with
  -- coefficients `𝟙_ (ModuleCat k)`, which is the `k`-module structure of the domain of the cap
  -- product only after unfolding, so `map_smul` is applied by `exact`
  refine this.symm.trans ?_
  rw [← Linear.smul_comp]
  exact congrArg (· ≫ _) (map_smul _ _ _)

variable {n} in
/-- The cap product `capComponent` with the sign `(-1)^(n q)` of `TopPair.pushforwardCapChainMap`
in degree `m = n + q`. -/
private def signedCapComponent
    (ψ : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X n) (q m : ℕ)
    (h : n + q = m) :
    ((singularChains k).obj P.fst).X m ⟶ ((singularChains k).obj Y).X q :=
  ((-1 : ℤ) ^ (n * q)) • capComponent P p₀ ψ q m h

/-- The sign-corrected cap products with a cocycle commute with the boundaries: they are the
components of the chain map `TauCeti.ChainComplex.capChainMap` of the cocycle `φ` pulled back to
the ambient space. -/
private theorem signedCapComponent_comp_d (q : ℕ) :
    signedCapComponent P p₀
        ((P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n φ) (q + 1)
        (q + 1 + n) (n.add_comm _) ≫ ((singularChains k).obj Y).d (q + 1) q =
      ((singularChains k).obj P.fst).d (q + 1 + n) (q + n) ≫ signedCapComponent P p₀
        ((P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n φ) q (q + n)
        (n.add_comm q) := by
  -- the pulled-back cochain is a cocycle: it is the underlying cochain of the cocycle
  -- `pulledCocycle`, read on the chains with coefficients `𝟙_ (ModuleCat k)` of the cap product
  have hψ : ((TopCat.toSSet.obj P.fst).chainComplex (𝟙_ (ModuleCat.{u} k))).d (n + 1) n ≫
      pulledCochain P ((P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n
        φ) = 0 := by
    have := ChainComplex.d_comp_linearYonedaObj_iCycles n (n + 1) (pulledCocycle P n φ)
    rw [iCycles_pulledCocycle] at this
    exact this
  have h := (ChainComplex.capChainMap k
    (P.fst.alexanderWhitneyDiagonal (λ_ (ModuleCat.of k k)).inv)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of k k)).hom ≫
      SSet.chainComplexMap (TopCat.toSSet.map p₀) (ModuleCat.of k k)) n
      (pulledCochain P ((P.singularCochainComplex (ModuleCat.of k k) k
        (ModuleCat.of k k)).iCycles n φ)) hψ).comm (q + 1 + n) (q + n)
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

variable {P p₀ n} in
/-- The sign-corrected cap products with a semi-invariant cochain are semi-invariant:
`cap(g • c) = χ(g) g • cap(c)`. -/
private theorem signedCapComponent_apply_smul {G : Type u} [Group G] [MulAction G P.fst]
    [ContinuousConstSMul G P.fst] [MulAction G Y] [ContinuousConstSMul G Y]
    (hp₀ : ∀ (g : G) x, p₀ (g • x) = g • p₀ x) (χ : G →* kˣ)
    {ψ : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X n}
    (hψ : IsSemiInvariantCochain χ ψ)
    (g : G) (q m : ℕ) (h : n + q = m) (c : ((singularChains k).obj P.fst).X m) :
    (signedCapComponent P p₀ ψ q m h).hom (singularChainsRepresentation k P.fst G m g c) =
      (χ g : k) •
        singularChainsRepresentation k Y G q g ((signedCapComponent P p₀ ψ q m h).hom c) := by
  rw [singularChainsRepresentation_apply, singularChainsRepresentation_apply]
  -- `singularChainsRepresentation` acts by `((singularChains k).map _).f`, which is the
  -- push-forward `(SSet.chainComplexMap (TopCat.toSSet.map _) (ModuleCat.of k k)).f` of
  -- `capComponent_smul` only after unfolding `singularChains`, so the goal is restated in that form
  revert c
  change ∀ c : ((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of k k)).X m,
    ((-1 : ℤ) ^ (n * q) • capComponent P p₀ ψ q m h).hom
      (((SSet.chainComplexMap (TopCat.toSSet.map
        (TopCat.ofHom ⟨(g • · : P.fst → P.fst), continuous_const_smul g⟩)) (ModuleCat.of k k)).f
          m).hom c) =
    (χ g : k) • ((SSet.chainComplexMap (TopCat.toSSet.map
        (TopCat.ofHom ⟨(g • · : Y → Y), continuous_const_smul g⟩)) (ModuleCat.of k k)).f q).hom
      (((-1 : ℤ) ^ (n * q) • capComponent P p₀ ψ q m h).hom c)
  intro c
  rw [ModuleCat.hom_zsmul, LinearMap.smul_apply, LinearMap.smul_apply, ← LinearMap.comp_apply,
    ← ModuleCat.hom_comp, capComponent_smul hp₀ χ hψ g q m h, ModuleCat.hom_smul,
    LinearMap.smul_apply,
    ModuleCat.hom_comp, LinearMap.comp_apply, map_zsmul, smul_comm]

variable {n} in
/-- The cap product with a relative cochain vanishes on the chains of the subspace. -/
private theorem map_f_comp_signedCapComponent
    (ψ : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X n) (q m : ℕ)
    (h : n + q = m) :
    ((singularChains k).map P.map).f m ≫ signedCapComponent P p₀ ψ q m h = 0 := by
  -- the chains of the subspace vanish in the relative chains. The push-forward
  -- `(singularChains k).map P.map` is `SSet.chainComplexMap (TopPair.toSSetPair.obj P).hom _` of
  -- `chainComplex_condition_f` only after unfolding `singularChainComplexFunctor` and
  -- `TopPair.toSSetPair`, which `rw` does not see through, so the steps are assembled in term mode
  have h₀ : ((singularChains k).map P.map).f m ≫ capComponent P p₀ ψ q m h = 0 :=
    (congrArg (((singularChains k).map P.map).f m ≫ ·)
    (singularChainComplexπ_f_capChain P p₀ ψ q m h).symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
        ((TopPair.toSSetPair.obj P).chainComplex_condition_f (ModuleCat.of k k) m)).trans
          Limits.zero_comp))
  -- `signedCapComponent` is `(-1)^(n q) • capComponent` by definition
  exact (Preadditive.comp_zsmul _ _ _).trans ((congrArg _ h₀).trans (zsmul_zero _))

variable {P p₀} in
/-- **Capping with a coboundary, componentwise.** If `ψ' = ψ + η ∘ ∂` for relative cochains `ψ`,
`ψ'` of degree `r + 1` and `η` of degree `r`, then in degree `q + r + 1` the sign-corrected cap
products satisfy `cap_ψ' - cap_ψ = (-1)^q ∂ ≫ cap_η + (-1)^(q + 1) cap_η ≫ ∂`. -/
private theorem signedCapComponent_sub_signedCapComponent {r : ℕ}
    {ψ ψ' : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X (r + 1)}
    (η : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X r)
    (h : ψ' = ψ + (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).d r (r + 1) η)
    (q : ℕ) :
    signedCapComponent P p₀ ψ' q (q + r + 1) (by omega) -
        signedCapComponent P p₀ ψ q (q + r + 1) (by omega) =
      ((-1 : ℤ) ^ q) • (((singularChains k).obj P.fst).d (q + r + 1) (q + r) ≫
          signedCapComponent P p₀ η q (q + r) (by omega)) +
        ((-1 : ℤ) ^ (q + 1)) • (signedCapComponent P p₀ η (q + 1) (q + r + 1) (by omega) ≫
          ((singularChains k).obj Y).d (q + 1) q) := by
  -- pulled back to the ambient space, `ψ'` is `ψ` plus the coboundary of the pull-back of `η`
  have hpull : pulledCochain P ψ' = pulledCochain P ψ +
      ((TopCat.toSSet.obj P.fst).chainComplex (𝟙_ (ModuleCat.{u} k))).d (r + 1) r ≫
        pulledCochain P η := by
    rw [pulledCochain, pulledCochain, pulledCochain, h]
    -- the ambient chains with coefficients `𝟙_ (ModuleCat k)` are the source of the quotient map
    -- only after unfolding, so the distributivity and naturality steps are applied by `exact`
    exact (Preadditive.comp_add _ _ _ _ _ _).trans (congrArg (_ + ·)
      ((P.singularChainComplexπ (ModuleCat.of k k)).comm_assoc (r + 1) r η))
  have hd := ChainComplex.capChain_d_comp (k := k)
    (P.fst.alexanderWhitneyDiagonal (λ_ (ModuleCat.of k k)).inv)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of k k)).hom ≫
      SSet.chainComplexMap (TopCat.toSSet.map p₀) (ModuleCat.of k k)) r q (q + r) (by omega)
    (pulledCochain P η)
  -- the signs: `(-1)^((r + 1) q) = (-1)^q (-1)^(r q)` and
  -- `-(-1)^((r + 1) q) (-1)^r = (-1)^(q + 1) (-1)^(r (q + 1))`
  have hsign : ∀ {X X' Y Y' : ModuleCat.{u} k} (A B : X ⟶ Y) (dX : X ⟶ X') (c : X' ⟶ Y)
      (c' : X ⟶ Y') (dY : Y' ⟶ Y), B = dX ≫ c - ((-1 : ℤ) ^ r) • (c' ≫ dY) →
      ((-1 : ℤ) ^ ((r + 1) * q)) • (A + B) - ((-1 : ℤ) ^ ((r + 1) * q)) • A =
        ((-1 : ℤ) ^ q) • (dX ≫ (((-1 : ℤ) ^ (r * q)) • c)) +
          ((-1 : ℤ) ^ (q + 1)) • ((((-1 : ℤ) ^ (r * (q + 1))) • c') ≫ dY) := by
    intro X X' Y Y' A B dX c c' dY hB
    rw [← smul_sub, add_sub_cancel_left, hB]
    simp only [smul_sub, Preadditive.comp_zsmul, Preadditive.zsmul_comp, smul_smul]
    rw [sub_eq_add_neg, ← neg_smul]
    congr 2 <;> ring
  simp only [signedCapComponent, capComponent]
  rw [hpull, map_add]
  -- the chains `(singularChains k).obj X` are `(TopCat.toSSet.obj X).chainComplex _` only after
  -- unfolding, so the sign computation is applied by `exact`
  exact hsign _ _ _ _ _ _ hd

section Rep

variable {G : Type u} [Group G] [MulAction G P.fst] [ContinuousConstSMul G P.fst] [MulAction G Y]
  [ContinuousConstSMul G Y] {p₀} (hp₀ : ∀ (g : G) x, p₀ (g • x) = g • p₀ x) (χ : G →* kˣ) {n φ}
  (hφ : IsSemiInvariantCocycle χ φ)

include hp₀ in
/-- The sign-corrected cap product with a semi-invariant cochain `ψ` in degree `m = n + q`, as an
equivariant map from the singular chains of the ambient space to the singular chains of `Y` twisted
by the character `χ`. -/
private def capRep {ψ : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X n}
    (hψ : IsSemiInvariantCochain χ ψ) (q m : ℕ) (h : n + q = m) :
    (TauCeti.singularChainsRep k P.fst G).X m ⟶
      Rep.of (Representation.ofLinearCharacter χ) ⊗ (TauCeti.singularChainsRep k Y G).X q :=
  Rep.ofHom
    { toLinearMap := TensorProduct.mk k k (((singularChains k).obj Y).X q) 1 ∘ₗ
        (signedCapComponent P p₀ ψ q m h).hom
      isIntertwining' g := LinearMap.ext fun c ↦ by
        -- the carriers of the representations are those of the singular chain modules, with module
        -- structures that agree only after unfolding, so the composite is evaluated by `change`
        change (1 : k) ⊗ₜ[k] (signedCapComponent P p₀ ψ q m h).hom
            (singularChainsRepresentation k P.fst G m g c) =
          (Representation.ofLinearCharacter χ).tprod (singularChainsRepresentation k Y G q) g
            ((1 : k) ⊗ₜ[k] (signedCapComponent P p₀ ψ q m h).hom c)
        rw [signedCapComponent_apply_smul hp₀ χ hψ,
          Representation.tprod_apply, TensorProduct.map_tmul,
          Representation.ofLinearCharacter_apply, mul_one, ← TensorProduct.smul_tmul, smul_eq_mul,
          mul_one] }

include hp₀ hφ in
/-- The equivariant sign-corrected cap products commute with the boundaries. -/
private theorem capRep_comp_d (q : ℕ) :
    capRep P hp₀ χ hφ (q + 1) (q + 1 + n) (n.add_comm _) ≫
      (Rep.of (Representation.ofLinearCharacter χ) ◁
        (TauCeti.singularChainsRep k Y G).d (q + 1) q) =
      (TauCeti.singularChainsRep k P.fst G).d (q + 1 + n) (q + n) ≫
        capRep P hp₀ χ hφ q (q + n) (n.add_comm q) := by
  have h := signedCapComponent_comp_d P p₀ n φ q
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun c ↦ ?_))
  -- evaluate both composites on `c`: the carriers are those of the singular chain modules
  change (1 : k) ⊗ₜ[k] ((TauCeti.singularChainsRep k Y G).d (q + 1) q).hom
      ((signedCapComponent P p₀ _ (q + 1) (q + 1 + n) (n.add_comm _)).hom c) =
    (1 : k) ⊗ₜ[k] (signedCapComponent P p₀ _ q (q + n) (n.add_comm q)).hom
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
    (ComplexShape.embeddingDownNatAdd_f n q)).hom ≫ capRep P hp₀ χ hφ q (q + n) (n.add_comm q)
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
    (capAmbient P hp₀ χ hφ).f (q + n) = capRep P hp₀ χ hφ q (q + n) (n.add_comm q) ≫
      ((((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex _).obj
        (TauCeti.singularChainsRep k Y G)).extendXIso (ComplexShape.embeddingDownNatAdd n)
          (ComplexShape.embeddingDownNatAdd_f n q)).inv := by
  refine ((ComplexShape.embeddingDownNatAdd n).liftExtend_f _ _
    (ComplexShape.embeddingDownNatAdd_f n q)).trans ?_
  simp only [capRestrictionHom, Category.assoc, Iso.inv_hom_id_assoc]

variable [MulAction G P.snd] [ContinuousConstSMul G P.snd]
  (hP : ∀ (g : G) x, P.map (g • x) = g • P.map x)

include hp₀ in
/-- The equivariant cap product with a relative cochain vanishes on the chains of the subspace. -/
private theorem singularChainsRepι_f_comp_capRep
    {ψ : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X n}
    (hψ : IsSemiInvariantCochain χ ψ) (q m : ℕ) (h : n + q = m) :
    (P.singularChainsRepι k G hP).f m ≫ capRep P hp₀ χ hψ q m h = 0 := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun c ↦ ?_))
  -- evaluate on `c`: the cap product vanishes on the image of the chains of the subspace
  change (capRep P hp₀ χ hψ q m h).hom (((P.singularChainsRepι k G hP).f m).hom c) = 0
  rw [singularChainsRepι_f_hom_apply P k hP m c]
  -- the underlying linear map of `capRep` is `c ↦ 1 ⊗ signedCapComponent c`, by its definition
  change (1 : k) ⊗ₜ[k] (signedCapComponent P p₀ ψ q m h).hom
      (((singularChains k).map P.map).f m c) = 0
  rw [← TensorProduct.tmul_zero (R := k) (((singularChains k).obj Y).X q) (1 : k)]
  exact congrArg ((1 : k) ⊗ₜ[k] ·) (ConcreteCategory.congr_hom
    (map_f_comp_signedCapComponent P p₀ ψ q m h) c)

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
    exact singularChainsRepι_f_comp_capRep P hp₀ χ hP hφ q (q + n) (n.add_comm q)

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
    have hc : (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)).map
        (capRep P hp₀ χ hφ q (q + n) (n.add_comm q)) ≫
        (singularChainsRepTwistForget₂Iso k Y χ).hom.f q = signedCapComponent P p₀
          ((P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n φ) q
            (q + n) (n.add_comm q) := by
      refine ModuleCat.hom_ext (LinearMap.ext fun c ↦ ?_)
      rw [singularChainsRepTwistForget₂Iso_hom_f]
      change TensorProduct.lid k _
        ((1 : k) ⊗ₜ[k] (signedCapComponent P p₀ _ q (q + n) (n.add_comm q)).hom c) = _
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

section Homotopy

variable {r : ℕ}

omit [MulAction G P.snd] [ContinuousConstSMul G P.snd] in
include hp₀ in
/-- **Capping with a coboundary, equivariantly.** If `ψ' = ψ + η ∘ ∂` for semi-invariant relative
cochains `ψ`, `ψ'` of degree `r + 1` and `η` of degree `r`, then in degree `q + r + 1` the
equivariant cap products satisfy `cap_ψ' - cap_ψ = (-1)^q ∂ ≫ cap_η + (-1)^(q + 1) cap_η ≫ ∂`. -/
private theorem capRep_sub_capRep
    {ψ ψ' : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X (r + 1)}
    {η : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X r}
    (hψ : IsSemiInvariantCochain χ ψ) (hψ' : IsSemiInvariantCochain χ ψ')
    (hη : IsSemiInvariantCochain χ η)
    (h : ψ' = ψ + (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).d r (r + 1) η)
    (q : ℕ) :
    capRep P hp₀ χ hψ' q (q + r + 1) (by omega) - capRep P hp₀ χ hψ q (q + r + 1) (by omega) =
      ((-1 : ℤ) ^ q) • ((TauCeti.singularChainsRep k P.fst G).d (q + r + 1) (q + r) ≫
          capRep P hp₀ χ hη q (q + r) (by omega)) +
        ((-1 : ℤ) ^ (q + 1)) • (capRep P hp₀ χ hη (q + 1) (q + r + 1) (by omega) ≫
          (Rep.of (Representation.ofLinearCharacter χ) ◁
            (TauCeti.singularChainsRep k Y G).d (q + 1) q)) := by
  have hs := signedCapComponent_sub_signedCapComponent (p₀ := p₀) η h q
  refine Rep.hom_ext (DFunLike.ext _ _ fun c ↦ ?_)
  simp only [Rep.sub_hom, Rep.add_hom, Rep.zsmul_hom, Rep.hom_comp,
    Representation.IntertwiningMap.coe_sub, Representation.IntertwiningMap.coe_add,
    Representation.IntertwiningMap.coe_zsmul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    Representation.IntertwiningMap.comp_apply]
  -- evaluate both sides on `c`: the carriers are those of the singular chain modules, and the
  -- underlying linear map of `capRep` is `c ↦ 1 ⊗ signedCapComponent c`, by its definition
  change (1 : k) ⊗ₜ[k] (signedCapComponent P p₀ ψ' q (q + r + 1) (by omega)).hom c -
      (1 : k) ⊗ₜ[k] (signedCapComponent P p₀ ψ q (q + r + 1) (by omega)).hom c = _
  change _ = ((-1 : ℤ) ^ q) • ((1 : k) ⊗ₜ[k] (signedCapComponent P p₀ η q (q + r) (by omega)).hom
        (((TauCeti.singularChainsRep k P.fst G).d (q + r + 1) (q + r)).hom c)) + _
  change _ = _ + ((-1 : ℤ) ^ (q + 1)) • ((1 : k) ⊗ₜ[k]
        ((TauCeti.singularChainsRep k Y G).d (q + 1) q).hom
          ((signedCapComponent P p₀ η (q + 1) (q + r + 1) (by omega)).hom c))
  rw [singularChainsRep_d_hom_apply, singularChainsRep_d_hom_apply k P.fst G _ _ c]
  -- read `c` as a singular chain, the carrier of the representation only after unfolding
  revert c
  change ∀ c : ((singularChains k).obj P.fst).X (q + r + 1),
    (1 : k) ⊗ₜ[k] (signedCapComponent P p₀ ψ' q (q + r + 1) (by omega)).hom c -
        (1 : k) ⊗ₜ[k] (signedCapComponent P p₀ ψ q (q + r + 1) (by omega)).hom c =
      ((-1 : ℤ) ^ q) • ((1 : k) ⊗ₜ[k] (signedCapComponent P p₀ η q (q + r) (by omega)).hom
          (((singularChains k).obj P.fst).d (q + r + 1) (q + r) c)) +
        ((-1 : ℤ) ^ (q + 1)) • ((1 : k) ⊗ₜ[k] ((singularChains k).obj Y).d (q + 1) q
          ((signedCapComponent P p₀ η (q + 1) (q + r + 1) (by omega)).hom c))
  intro c
  rw [← TensorProduct.tmul_sub, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_smul,
    ← TensorProduct.tmul_add]
  refine congrArg ((1 : k) ⊗ₜ[k] ·) ?_
  simpa using ConcreteCategory.congr_hom hs c

include hp₀ in
/-- The component in degree `i` of the equivariant null-homotopy capping with a semi-invariant
cochain `η` of degree `r`, on the singular chains of the ambient space: for `i = r + q` it is
`(-1)^q` times the equivariant cap product with `η`, read in degree `i + 1` of the twisted chains of
`Y` placed `r + 1` degrees higher, and it is zero below `r`. -/
private def capHomotopyAmbient
    {η : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X r}
    (hη : IsSemiInvariantCochain χ η) (i : ℕ) :
    (TauCeti.singularChainsRep k P.fst G).X i ⟶
      ((((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex _).obj
        (TauCeti.singularChainsRep k Y G)).extend
          (ComplexShape.embeddingDownNatAdd (r + 1))).X (i + 1) :=
  if hi : r ≤ i then
    ((-1 : ℤ) ^ (i - r)) • (capRep P hp₀ χ hη (i - r) i (by omega) ≫
      ((((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex _).obj
        (TauCeti.singularChainsRep k Y G)).extendXIso (ComplexShape.embeddingDownNatAdd (r + 1))
          (i := i - r) (by rw [ComplexShape.embeddingDownNatAdd_f]; omega)).inv)
  else 0

omit [MulAction G P.snd] [ContinuousConstSMul G P.snd] in
private theorem capHomotopyAmbient_eq
    {η : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X r}
    (hη : IsSemiInvariantCochain χ η) (q i : ℕ) (h : r + q = i) :
    capHomotopyAmbient P hp₀ χ hη i = ((-1 : ℤ) ^ q) • (capRep P hp₀ χ hη q i h ≫
      ((((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex _).obj
        (TauCeti.singularChainsRep k Y G)).extendXIso (ComplexShape.embeddingDownNatAdd (r + 1))
          (i := q) (by rw [ComplexShape.embeddingDownNatAdd_f]; omega)).inv) := by
  obtain rfl : q = i - r := by omega
  rw [capHomotopyAmbient]
  split_ifs with hi
  · rfl
  · omega

private theorem singularChainsRepι_f_comp_capHomotopyAmbient
    {η : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X r}
    (hη : IsSemiInvariantCochain χ η) (i : ℕ) :
    (P.singularChainsRepι k G hP).f i ≫ capHomotopyAmbient P hp₀ χ hη i = 0 := by
  by_cases hi : r ≤ i
  · rw [capHomotopyAmbient_eq P hp₀ χ hη (i - r) i (by omega), Preadditive.comp_zsmul,
      ← Category.assoc, singularChainsRepι_f_comp_capRep, Limits.zero_comp, smul_zero]
  · rw [capHomotopyAmbient, dite_eq_right_of_eq_false (eq_false hi), Limits.comp_zero]

/-- In each degree, the equivariant relative chains are the cokernel of the chains of the
subspace. -/
private def isColimitCokernelCoforkSingularChainsRepX (i : ℕ) :
    IsColimit (CokernelCofork.ofπ ((P.singularChainsRepπ k G hP).f i) (by
      rw [← HomologicalComplex.comp_f, singularChainsRepι_comp_singularChainsRepπ,
        HomologicalComplex.zero_f])) :=
  CokernelCofork.mapIsColimit _ (P.isColimitCokernelCoforkSingularChainsRep k G hP)
    (HomologicalComplex.eval _ _ i)

include hp₀ in
/-- The component in degree `i` of the equivariant null-homotopy capping with a semi-invariant
relative cochain `η`, on the relative chains: `capHomotopyAmbient` vanishes on the chains of the
subspace, so it descends to their cokernel. -/
private def capHomotopyRel
    {η : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X r}
    (hη : IsSemiInvariantCochain χ η) (i : ℕ) :
    (P.singularChainsRep k G hP).X i ⟶
      ((((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex _).obj
        (TauCeti.singularChainsRep k Y G)).extend
          (ComplexShape.embeddingDownNatAdd (r + 1))).X (i + 1) :=
  (CokernelCofork.IsColimit.desc' (isColimitCokernelCoforkSingularChainsRepX P hP i)
    (capHomotopyAmbient P hp₀ χ hη i)
    (singularChainsRepι_f_comp_capHomotopyAmbient P hp₀ χ hP hη i)).val

@[reassoc]
private theorem singularChainsRepπ_f_capHomotopyRel
    {η : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X r}
    (hη : IsSemiInvariantCochain χ η) (i : ℕ) :
    (P.singularChainsRepπ k G hP).f i ≫ capHomotopyRel P hp₀ χ hP hη i =
      capHomotopyAmbient P hp₀ χ hη i :=
  (CokernelCofork.IsColimit.desc' (isColimitCokernelCoforkSingularChainsRepX P hP i)
    (capHomotopyAmbient P hp₀ χ hη i)
    (singularChainsRepι_f_comp_capHomotopyAmbient P hp₀ χ hP hη i)).property

include hp₀ in
/-- In degree `q + r + 1`, the difference of the equivariant cap products with cohomologous
semi-invariant cocycles is the null-homotopic map of `capHomotopyRel`, after the quotient onto the
relative chains. -/
private theorem singularChainsRepCap_sub_singularChainsRepCap
    {φ φ' : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).cycles (r + 1)}
    {η : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X r}
    (hφ : IsSemiInvariantCocycle χ φ) (hφ' : IsSemiInvariantCocycle χ φ')
    (hη : IsSemiInvariantCochain χ η)
    (h : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles (r + 1) φ' =
      (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles (r + 1) φ +
        (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).d r (r + 1) η) :
    P.singularChainsRepCap hp₀ χ hφ' hP - P.singularChainsRepCap hp₀ χ hφ hP =
      _root_.Homotopy.nullHomotopicMap' (fun i j (hij : i + 1 = j) ↦
        capHomotopyRel P hp₀ χ hP hη i ≫ (HomologicalComplex.XIsoOfEq _ hij).hom) := by
  ext m : 1
  rw [← cancel_epi ((P.singularChainsRepπ k G hP).f m)]
  by_cases hm : r + 1 ≤ m
  · obtain ⟨q, rfl⟩ : ∃ q, m = q + r + 1 := ⟨m - r - 1, by omega⟩
    -- in degree `q + r + 1` both cap products are `capRep`, read in the shifted complex
    have e : ∀ {ψ : (P.singularCochainComplex (ModuleCat.of k k) k
        (ModuleCat.of k k)).cycles (r + 1)} (hψ : IsSemiInvariantCocycle χ ψ),
        (P.singularChainsRepπ k G hP).f (q + r + 1) ≫
          (P.singularChainsRepCap hp₀ χ hψ hP).f (q + r + 1) =
        capRep P hp₀ χ hψ q (q + r + 1) (by omega) ≫
          ((((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex
            _).obj (TauCeti.singularChainsRep k Y G)).extendXIso
              (ComplexShape.embeddingDownNatAdd (r + 1)) (i := q)
                (by rw [ComplexShape.embeddingDownNatAdd_f]; omega)).inv := fun hψ ↦
      (HomologicalComplex.comp_f _ _ _).symm.trans
        ((congrArg (fun f ↦ HomologicalComplex.Hom.f f (q + r + 1))
          (singularChainsRepπ_singularChainsRepCap P hp₀ χ hψ hP)).trans
            (capAmbient_f P hp₀ χ hψ q))
    rw [_root_.Homotopy.nullHomotopicMap'_f (k₀ := q + r) (k₂ := q + r + 1 + 1) rfl rfl,
      HomologicalComplex.sub_f_apply, Preadditive.comp_sub, e hφ', e hφ,
      HomologicalComplex.XIsoOfEq_rfl, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Iso.refl_hom, Category.comp_id, Category.comp_id, Preadditive.comp_add,
      HomologicalComplex.Hom.comm_assoc, singularChainsRepπ_f_capHomotopyRel,
      singularChainsRepπ_f_capHomotopyRel_assoc,
      capHomotopyAmbient_eq P hp₀ χ hη q (q + r) (by omega),
      capHomotopyAmbient_eq P hp₀ χ hη (q + 1) (q + r + 1) (by omega),
      HomologicalComplex.extend_d_eq _ _ (i := q + 1) (j := q)
        (by rw [ComplexShape.embeddingDownNatAdd_f]; omega)
        (by rw [ComplexShape.embeddingDownNatAdd_f]; omega),
      ← Preadditive.sub_comp, capRep_sub_capRep P hp₀ χ hφ hφ' hη h q]
    simp only [Preadditive.add_comp, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
      Category.assoc, Iso.inv_hom_id_assoc, Functor.mapHomologicalComplex_obj_d]
    -- the differential of the twisted chains is `(tensorLeft k_χ).map d`, which is `k_χ ◁ d` by
    -- definition
    rfl
  · -- Below `r + 1` the shifted complex is zero.
    exact (HomologicalComplex.isZero_extend_embeddingDownNatAdd_X _ (by omega)).eq_of_tgt _ _

include hp₀ in
/-- **Capping with cohomologous semi-invariant cocycles gives equivariantly homotopic chain
maps.** Let `φ` and `φ'` be semi-invariant relative cocycles of degree `n = r + 1` with
`φ' = φ + δη` for a semi-invariant relative cochain `η` of degree `r`. Then the equivariant cap
products `TopPair.singularChainsRepCap` with `φ'` and with `φ` are homotopic as chain maps of
complexes of representations, by the homotopy which caps with `η`. Hence every additive functor,
for instance coinvariants, takes them to homotopic chain maps. -/
def singularChainsRepCapHomotopy {n : ℕ} (hrn : r + 1 = n)
    {φ φ' : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).cycles n}
    {η : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X r}
    (hφ : IsSemiInvariantCocycle χ φ) (hφ' : IsSemiInvariantCocycle χ φ')
    (hη : IsSemiInvariantCochain χ η)
    (h : (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n φ' =
      (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles n φ +
        (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).d r n η) :
    _root_.Homotopy (P.singularChainsRepCap hp₀ χ hφ' hP) (P.singularChainsRepCap hp₀ χ hφ hP) := by
  subst hrn
  exact _root_.Homotopy.equivSubZero.symm
    ((_root_.Homotopy.ofEq
      (singularChainsRepCap_sub_singularChainsRepCap P hp₀ χ hP hφ hφ' hη h)).trans
      (_root_.Homotopy.nullHomotopy' _))

end Homotopy

end Rep

end TopPair
