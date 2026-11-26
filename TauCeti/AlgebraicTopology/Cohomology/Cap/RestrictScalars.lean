/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Cochains.Basic
public import TauCeti.AlgebraicTopology.Singular.Coefficients.RestrictScalars

/-!
# Cap products under a change of coefficient ring

Let `f : R →+* k` be a homomorphism of commutative rings and write `G` for restriction of scalars
`ModuleCat k ⥤ ModuleCat R` along `f`. Given a map `c : T ⟶ G k` from an `R`-module `T`, singular
chains over `R` with coefficients in `T` map to singular chains over `k`
(`TopCat.restrictScalarsChainMap`, `TopCat.restrictScalarsHomologyMap`). Dually, a `k`-valued
cochain `φ` over `k` restricts to a cochain over `R` with values in `G k`, `σ ⊗ t ↦ φ(σ) c t`
(`TopCat.restrictScalarsCochainMap`). On cohomology this gives

`TopCat.restrictScalarsCohomologyMap : G Hᵖ(X; k) ⟶ Hᵖ(X; T, G k)`,

where the cohomology on the right is computed from chains over `R` with coefficients in `T` and
cochain values in `G k`. Unlike `TauCeti.singularCohomologyIntegralIso`, which compares the
cohomologies of chains over `k` and over `ℤ` as abelian groups, the cohomology over `k` here keeps
its `k`-linear structure, so that it is the source of `TopCat.singularCapLinearMap`.

The main result is that the cap product is compatible with these maps
(`TopCat.restrictScalarsHomologyMap_comp_map_singularCap`): for `x ∈ Hₙ(X; T)` and
`α ∈ Hᵖ(X; k)`,

`f_*(x) ⌢ α = f_*(x ⌢ f^*α)`,

where on the left the cap product is over `k` along the unitors of `k`, and on the right it is
over `R` along the right unitors of `T` and of `G k`. At the chain level both sides send a
simplex `σ` with coefficient `t` to its back face with coefficient `φ(front face of σ) c t`
(`TopCat.restrictScalarsChainMap_f_comp_map_capChain`).

For `T = ULift R` and `c` the map `x ↦ f x.down` (`ModuleCat.uliftUnitToRestrictScalars`), a
cochain over `k` is determined by its values on simplices, and so is a cochain over `R` on chains
with coefficients in `ULift R`; hence the cochain comparison and the cohomology comparison are
isomorphisms (`TopCat.bijective_restrictScalarsCochainMap_f`). With the compatibility of cap
products, this transports Poincaré duality from integral chains to chains over any commutative
ring.

## Main definitions and results

* `TopCat.restrictScalarsCochainMap`, `TopCat.restrictScalarsCohomologyMap`: the comparison of
  cochains and of cohomology.
* `TopCat.restrictScalarsHomologyMap_comp_map_singularCap`: the cap product commutes with the
  comparisons.
* `TopCat.bijective_restrictScalarsCochainMap_f`: for `ULift R` and the map induced by `f`, the
  cochain comparison is bijective in each degree, so the cohomology comparison is an isomorphism.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (cap products) and Section 3.A (change of coefficients).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex Simplicial

universe w

namespace TopCat

variable (X : TopCat.{w}) {R k : Type w} [CommRing R] [CommRing k] (f : R →+* k)
  {T : ModuleCat.{w} R} (c : T ⟶ (ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{w} k)))

/-! ### Cochains and cohomology -/

/-- The cochain map restricting a `k`-valued cochain over `k` to a cochain over `R` with
coefficients in `T`: it precomposes with `TopCat.restrictScalarsChainMap`. -/
def restrictScalarsCochainMap :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex _).obj
        (X.singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))) ⟶
      X.singularCochainComplex T R ((ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{w} k))) where
  f p := ModuleCat.ofHom (X := (ModuleCat.restrictScalars f).obj
      ((X.singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))).X p))
    { toFun φ := (X.restrictScalarsChainMap f c).f p ≫ (ModuleCat.restrictScalars f).map φ
      -- `G.map` is the identity on elements, so both laws hold pointwise by definition.
      map_add' φ ψ := by
        ext x
        rfl
      map_smul' r φ := by
        ext x
        rfl }
  comm' i j _ := by
    ext φ
    -- Both sides are the cochain `d ≫ θ ≫ G φ`, read through the definitional unfolding of the
    -- differentials of the two Hom complexes.
    have key (φ' : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).X i ⟶ 𝟙_ _) :
        ((toSSet.obj X).chainComplex T).d j i ≫ (X.restrictScalarsChainMap f c).f i ≫
            (ModuleCat.restrictScalars f).map φ' =
          (X.restrictScalarsChainMap f c).f j ≫ (ModuleCat.restrictScalars f).map
            (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).d j i ≫ φ') := by
      rw [Functor.map_comp, ← Category.assoc, ← Category.assoc,
        ← HomologicalComplex.Hom.comm, Functor.mapHomologicalComplex_obj_d]
    exact key φ

/-- The cochain comparison precomposes a cochain with the chain comparison. -/
lemma restrictScalarsCochainMap_f_apply (p : ℕ)
    (φ : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).X p ⟶ 𝟙_ (ModuleCat.{w} k)) :
    (X.restrictScalarsCochainMap f c).f p φ =
      (X.restrictScalarsChainMap f c).f p ≫ (ModuleCat.restrictScalars f).map φ :=
  (rfl)

/-- The comparison `G Hᵖ(X; k) ⟶ Hᵖ(X; T, G k)`: the identification of the restriction of the
cohomology with the cohomology of the restricted complex, followed by the map induced by
`TopCat.restrictScalarsCochainMap`. -/
def restrictScalarsCohomologyMap (p : ℕ) :
    (ModuleCat.restrictScalars f).obj
        (X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p) ⟶
      X.singularCohomology T R ((ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{w} k))) p :=
  ((ModuleCat.restrictScalars f).mapHomologicalComplexCompHomologyFunctorIso _ p).inv.app _ ≫
    homologyMap (X.restrictScalarsCochainMap f c) p

/-- The cohomology comparison on the class of a cocycle `φ` is the class of the restricted cocycle
`f^* φ`. -/
@[reassoc]
lemma map_homologyπ_restrictScalarsCohomologyMap (p : ℕ) :
    (ModuleCat.restrictScalars f).map
        ((X.singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))).homologyπ p) ≫
      X.restrictScalarsCohomologyMap f c p =
    (((X.singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))).sc p).mapCyclesIso
        (ModuleCat.restrictScalars f)).inv ≫
      cyclesMap (X.restrictScalarsCochainMap f c) p ≫
        (X.singularCochainComplex T R ((ModuleCat.restrictScalars f).obj
          (𝟙_ (ModuleCat.{w} k)))).homologyπ p := by
  rw [restrictScalarsCohomologyMap,
    Functor.map_homologyπ_comp_mapHomologicalComplexCompHomologyFunctorIso_inv_app_assoc,
    homologyπ_naturality]

/-- The cocycle representing the comparison of the class of a cocycle `φ` is the restriction
`f^* φ` of the cochain underlying `φ`. -/
lemma iCycles_cyclesMap_restrictScalarsCochainMap (p : ℕ)
    (φ : (X.singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))).cycles p) :
    (X.singularCochainComplex T R ((ModuleCat.restrictScalars f).obj
        (𝟙_ (ModuleCat.{w} k)))).iCycles p
      (cyclesMap (X.restrictScalarsCochainMap f c) p
        ((((X.singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))).sc
          p).mapCyclesIso
          (ModuleCat.restrictScalars f)).inv φ)) =
      (X.restrictScalarsChainMap f c).f p ≫ (ModuleCat.restrictScalars f).map
        ((X.singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))).iCycles p
          φ) := by
  have h₁ := ConcreteCategory.congr_hom (cyclesMap_i (X.restrictScalarsCochainMap f c) p)
    ((((X.singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))).sc p).mapCyclesIso
      (ModuleCat.restrictScalars f)).inv φ)
  have h₂ := ConcreteCategory.congr_hom (ShortComplex.mapCyclesIso_inv_comp_iCycles
    ((X.singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))).sc p)
    (ModuleCat.restrictScalars f)) φ
  -- `G.map` of the inclusion of cocycles is that inclusion on elements.
  exact ((ConcreteCategory.comp_apply _ _ _).symm.trans
    (h₁.trans (ConcreteCategory.comp_apply _ _ _))).trans
      (congrArg _ ((ConcreteCategory.comp_apply _ _ _).symm.trans h₂))

/-! ### Compatibility with cap products -/

/-- **Cap products of chains under a change of coefficient ring**: capping the chain comparison
of a chain with a cochain `φ` over `k` is the chain comparison of the cap product, over `R`, of the
chain with the restriction `f^* φ` of `φ`. -/
lemma restrictScalarsChainMap_f_comp_map_capChain (p q n : ℕ) (h : p + q = n)
    (φ : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).X p ⟶ 𝟙_ (ModuleCat.{w} k)) :
    (X.restrictScalarsChainMap f c).f n ≫
      (ModuleCat.restrictScalars f).map
        (TauCeti.ChainComplex.capChain k (X.alexanderWhitneyDiagonal (λ_ _).inv)
          ((toSSet.obj X).chainComplexPairing (λ_ _).hom) p q n h φ) =
    TauCeti.ChainComplex.capChain R (X.alexanderWhitneyDiagonal (ρ_ T).inv)
        ((toSSet.obj X).chainComplexPairing
          (ρ_ ((ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{w} k)))).hom) p q n h
        ((X.restrictScalarsChainMap f c).f p ≫ (ModuleCat.restrictScalars f).map φ) ≫
      (X.restrictScalarsChainMap f (𝟙 _)).f q := by
  refine SSet.chainComplex_hom_ext (fun σ ↦ ?_)
  rw [ιChainComplex_restrictScalarsChainMap_f_assoc, ← Functor.map_comp,
    ιChainComplex_capChain_alexanderWhitneyDiagonal,
    reassoc_of% (ιChainComplex_capChain_alexanderWhitneyDiagonal (k := R) X (ρ_ T).inv
      (ρ_ ((ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{w} k)))).hom p q n h
      ((X.restrictScalarsChainMap f c).f p ≫ (ModuleCat.restrictScalars f).map φ) σ)]
  -- On both sides the coefficient of the front face acts on the coefficient of the simplex
  -- through a unitor of the unit, which cancels.
  rw [unitors_inv_equal, unitors_equal, ← rightUnitor_inv_naturality_assoc, Iso.inv_hom_id_assoc,
    ← rightUnitor_inv_naturality_assoc, Iso.inv_hom_id_assoc]
  simp

/-- The chain-level compatibility on cycles: capping the comparison of a cycle with a cocycle `φ`
is the comparison of the cap product with the restricted cocycle `w`. -/
private lemma cyclesMap_restrictScalarsChainMap_comp_map_capCycles (p q n : ℕ) (h : p + q = n)
    (φ : (X.singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))).cycles p)
    (w : (X.singularCochainComplex T R ((ModuleCat.restrictScalars f).obj
      (𝟙_ (ModuleCat.{w} k)))).cycles p)
    (hw : (X.singularCochainComplex T R ((ModuleCat.restrictScalars f).obj
          (𝟙_ (ModuleCat.{w} k)))).iCycles p w =
        (X.restrictScalarsChainMap f c).f p ≫ (ModuleCat.restrictScalars f).map
          ((X.singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))).iCycles p
            φ)) :
    cyclesMap (X.restrictScalarsChainMap f c) n ≫
      ((((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).sc n).mapCyclesIso
          (ModuleCat.restrictScalars f)).hom ≫
        (ModuleCat.restrictScalars f).map (TauCeti.ChainComplex.capCycles k
          (X.alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat.{w} k))).inv)
          ((toSSet.obj X).chainComplexPairing (λ_ (𝟙_ (ModuleCat.{w} k))).hom) p q n h φ) =
      TauCeti.ChainComplex.capCycles R (X.alexanderWhitneyDiagonal (ρ_ T).inv)
          ((toSSet.obj X).chainComplexPairing
            (ρ_ ((ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{w} k)))).hom) p q n h w ≫
        cyclesMap (X.restrictScalarsChainMap f (𝟙 _)) q ≫
          ((((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).sc q).mapCyclesIso
            (ModuleCat.restrictScalars f)).hom := by
  refine (cancel_mono ((ModuleCat.restrictScalars f).map
    (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).iCycles q))).1 ?_
  have hc (i : ℕ) : ((((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).sc i).mapCyclesIso
        (ModuleCat.restrictScalars f)).hom ≫ (ModuleCat.restrictScalars f).map
        (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).iCycles i) =
      (((ModuleCat.restrictScalars f).mapHomologicalComplex _).obj
        ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k)))).iCycles i :=
    ShortComplex.mapCyclesIso_hom_iCycles _ _
  simp only [Category.assoc, ← Functor.map_comp, TauCeti.ChainComplex.capCycles_i]
  rw [Functor.map_comp, reassoc_of% hc, hc]
  -- Both sides are now cap products of chains, compared by
  -- `TopCat.restrictScalarsChainMap_f_comp_map_capChain`.
  refine (cyclesMap_i_assoc _ n _).trans <| (congrArg (_ ≫ ·)
    (X.restrictScalarsChainMap_f_comp_map_capChain f c p q n h _)).trans <| Eq.symm ?_
  refine (congrArg (_ ≫ ·) (cyclesMap_i _ q)).trans <| (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) (TauCeti.ChainComplex.capCycles_i _ _ _ _ _ _ _)).trans <|
    (Category.assoc _ _ _).trans ?_
  rw [hw]

/-- **The cap product under a change of coefficient ring**, `f_*(x) ⌢ α = f_*(x ⌢ f^*α)`: for a
class `x ∈ Hₙ(X; T)` and `α ∈ Hᵖ(X; k)`, capping the comparison of `x` in `Hₙ(X; k)` with `α`,
over `k` along the unitors of `k`, is the comparison of the cap product of `x` with the restricted
class `f^*α ∈ Hᵖ(X; T, G k)`, over `R` along the right unitors of `T` and `G k`. -/
theorem restrictScalarsHomologyMap_comp_map_singularCap (p q n : ℕ) (h : p + q = n)
    (α : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p) :
    X.restrictScalarsHomologyMap f c n ≫ (ModuleCat.restrictScalars f).map
        (X.singularCap k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ (𝟙_ (ModuleCat.{w} k))).hom p q n h
          α) =
      X.singularCap R (ρ_ T).inv (ρ_ ((ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{w} k)))).hom
          p q n h (X.restrictScalarsCohomologyMap f c p α) ≫
        X.restrictScalarsHomologyMap f (𝟙 _) q := by
  obtain ⟨φ, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((X.singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))).homologyπ p)).1
      inferInstance α
  set w := cyclesMap (X.restrictScalarsCochainMap f c) p
    ((((X.singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))).sc p).mapCyclesIso
      (ModuleCat.restrictScalars f)).inv φ)
  have hT : X.restrictScalarsCohomologyMap f c p
      ((X.singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))).homologyπ p φ) =
      (X.singularCochainComplex T R ((ModuleCat.restrictScalars f).obj
          (𝟙_ (ModuleCat.{w} k)))).homologyπ p w :=
    ConcreteCategory.congr_hom (X.map_homologyπ_restrictScalarsCohomologyMap f c p) φ
  rw [hT]
  refine (cancel_epi (((toSSet.obj X).chainComplex T).homologyπ n)).1 ?_
  have hk := singularCap_homologyπ X k (λ_ (𝟙_ (ModuleCat.{w} k))).inv
    (λ_ (𝟙_ (ModuleCat.{w} k))).hom p q n h φ
  have hR := singularCap_homologyπ X R (ρ_ T).inv
    (ρ_ ((ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{w} k)))).hom p q n h w
  have hkey := X.cyclesMap_restrictScalarsChainMap_comp_map_capCycles f c p q n h φ w
    (X.iCycles_cyclesMap_restrictScalarsCochainMap f c p φ)
  -- The class maps land in `homology` of the chain complexes, while `singularCap` and the
  -- comparisons are stated on `singularHomologyFunctor`; the two agree only after unfolding, so
  -- `rw` cannot cross the composites and the squares are pasted as terms.
  exact (X.homologyπ_restrictScalarsHomologyMap_assoc f c n _).trans <|
    (congrArg (_ ≫ _ ≫ ·) (((ModuleCat.restrictScalars f).map_comp _ _).symm.trans <|
      (congrArg (ModuleCat.restrictScalars f).map hk).trans
        ((ModuleCat.restrictScalars f).map_comp _ _))).trans <|
    ((reassoc_of% hkey) _).trans <|
    (congrArg (_ ≫ ·) (X.homologyπ_restrictScalarsHomologyMap f (𝟙 _) q).symm).trans <|
    (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hR.symm).trans <| Category.assoc _ _ _

/-! ### The comparison for `ULift R` -/

variable {X} in
/-- The restriction of a cochain `φ` over `k` along `ULift R → k` takes the value `φ(σ)` on the
simplex `σ` with coefficient `⟨1⟩`. -/
private lemma restrictScalarsChainMap_uliftUnit_comp_map_apply {p : ℕ}
    (φ : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).X p ⟶ 𝟙_ (ModuleCat.{w} k))
    (σ : (toSSet.obj X) _⦋p⦌) :
    ((X.restrictScalarsChainMap f (ModuleCat.uliftUnitToRestrictScalars f)).f p ≫
        (ModuleCat.restrictScalars f).map φ)
        ((toSSet.obj X).ιChainComplex (R := ModuleCat.of R (ULift.{w} R)) σ ⟨1⟩) =
      φ ((toSSet.obj X).ιChainComplex (R := 𝟙_ (ModuleCat.{w} k)) σ 1) := by
  refine (ConcreteCategory.comp_apply _ _ _).symm.trans
    ((ConcreteCategory.congr_hom (X.ιChainComplex_restrictScalarsChainMap_f_assoc f
      (ModuleCat.uliftUnitToRestrictScalars f) σ ((ModuleCat.restrictScalars f).map φ)) ⟨1⟩).trans
        ?_)
  -- `G.map` is the identity on elements, and the unit map sends `⟨1⟩` to `f 1 = 1`.
  exact congrArg (fun x : k ↦ φ ((toSSet.obj X).ιChainComplex (R := 𝟙_ (ModuleCat.{w} k)) σ x))
    ((ModuleCat.uliftUnitToRestrictScalars_apply f ⟨1⟩).trans (map_one f))

/-- **Cochains over `k` are cochains over `R` on `ULift R`-chains**: restricting `k`-valued
cochains over `k` along `ULift R → k`, `x ↦ f x.down`, is bijective in every degree. Both kinds of
cochains are determined by their values on simplices. -/
theorem bijective_restrictScalarsCochainMap_f (p : ℕ) :
    Function.Bijective
      ((X.restrictScalarsCochainMap f (ModuleCat.uliftUnitToRestrictScalars f)).f p) := by
  have key : Function.Bijective fun φ : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).X p ⟶
      𝟙_ (ModuleCat.{w} k) ↦
        (X.restrictScalarsChainMap f (ModuleCat.uliftUnitToRestrictScalars f)).f p ≫
          (ModuleCat.restrictScalars f).map φ := by
    refine ⟨fun φ φ' hφ ↦ ?_, fun χ ↦ ?_⟩
    · apply (TauCeti.cochainValuesEquiv k (𝟙_ (ModuleCat.{w} k)) (toSSet.obj X) p).injective
      funext σ
      rw [TauCeti.cochainValuesEquiv_apply, TauCeti.cochainValuesEquiv_apply,
        ← restrictScalarsChainMap_uliftUnit_comp_map_apply f,
        ← restrictScalarsChainMap_uliftUnit_comp_map_apply f]
      simp only at hφ
      rw [hφ]
    · refine ⟨(TauCeti.cochainValuesEquiv k (𝟙_ (ModuleCat.{w} k)) (toSSet.obj X) p).symm
        fun σ ↦ χ ((toSSet.obj X).ιChainComplex (R := ModuleCat.of R (ULift.{w} R)) σ ⟨1⟩), ?_⟩
      refine SSet.chainComplex_hom_ext (fun σ ↦ ?_)
      rw [ιChainComplex_restrictScalarsChainMap_f_assoc, ← Functor.map_comp]
      refine ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
      have hm : m = m.down • (⟨1⟩ : ULift.{w} R) := ULift.ext (by simp)
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
      conv_rhs => rw [hm, map_smul, map_smul]
      rw [ModuleCat.uliftUnitToRestrictScalars_apply]
      -- `G.map` is the identity on elements and the `R`-action on the restriction of scalars is
      -- the `k`-action through `f`.
      exact TauCeti.cochainValuesEquiv_symm_apply k (𝟙_ (ModuleCat.{w} k)) (toSSet.obj X) p _ σ
        (f m.down)
  -- The cochain comparison precomposes with the chain comparison; `key` states this with the
  -- source read as the morphisms `C_p(X; k) ⟶ k` rather than as the cochain module.
  rw [show ⇑((X.restrictScalarsCochainMap f (ModuleCat.uliftUnitToRestrictScalars f)).f p) =
      fun φ ↦ (X.restrictScalarsChainMap f (ModuleCat.uliftUnitToRestrictScalars f)).f p ≫
        (ModuleCat.restrictScalars f).map φ from
    funext (X.restrictScalarsCochainMap_f_apply f _ p)]
  exact key

/-- The cochain comparison along `ULift R → k` is an isomorphism of cochain complexes. -/
instance : IsIso (X.restrictScalarsCochainMap f (ModuleCat.uliftUnitToRestrictScalars f)) :=
  have (p : ℕ) :
      IsIso ((X.restrictScalarsCochainMap f (ModuleCat.uliftUnitToRestrictScalars f)).f p) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (X.bijective_restrictScalarsCochainMap_f f p)
  HomologicalComplex.Hom.isIso_of_components _

/-- The cohomology comparison along `ULift R → k` is an isomorphism. -/
instance (p : ℕ) :
    IsIso (X.restrictScalarsCohomologyMap f (ModuleCat.uliftUnitToRestrictScalars f) p) :=
  IsIso.comp_isIso'
    (Iso.isIso_inv
      (((ModuleCat.restrictScalars f).mapHomologicalComplexCompHomologyFunctorIso _ p).app _))
    (homologyMapIso (asIso (X.restrictScalarsCochainMap f
      (ModuleCat.uliftUnitToRestrictScalars f))) p).isIso_hom

end TopCat
