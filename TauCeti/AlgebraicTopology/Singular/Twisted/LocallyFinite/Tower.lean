/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import TauCeti.Algebra.Category.ModuleCat.Tower.Milnor.Naturality
public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Functoriality
public import TauCeti.AlgebraicTopology.Singular.Twisted.Triple

/-!
# Locally finite chains as an inverse limit of relative chains

Let `S : ℕ → Set X` be a monotone sequence of subsets (`S n ⊆ S (n + 1)`) of a space `X` and let
`L` be a local coefficient system on `X`. The relative twisted chain complexes `C(X, X \ Sₙ; L)`,
with the quotient maps `C(X, X \ Sₙ₊₁; L) ⟶ C(X, X \ Sₙ; L)` of the triples
`(X, X \ Sₙ, X \ Sₙ₊₁)`, form a tower of chain complexes whose transition maps are surjective in
every degree (`TauCeti.LocalCoefficientSystem.relativeChainComplexTower`), and morphisms of local
coefficient systems act levelwise on this tower
(`TauCeti.LocalCoefficientSystem.relativeChainComplexTowerCoefficientMap`).

For a pair `(X, B)` with `X \ B` compact, a locally finite chain has only finitely many simplices
with nonzero coefficient meeting `X \ B`, and the class in `C(X, B; L)` of its part on those
simplices is linear in the chain and commutes with the boundaries
(`TopPair.locallyFiniteChainComplexToRelative`), compatibly with the quotient maps of triples
(`TauCeti.TopTriple.locallyFiniteChainComplexToRelative_comp_twistedChainComplexTotalToOuter`).
When every `Sₙ` is compact, these chain maps form a cone over the tower
(`TauCeti.LocalCoefficientSystem.locallyFiniteChainComplexCone`), inducing a chain map
`locallyFiniteChainComplexToLimComplex` to the limit complex. When `S` comes from a compact
exhaustion `K` of `X`, this cone is a limit
(`TauCeti.LocalCoefficientSystem.isLimitLocallyFiniteChainComplexCone`): a compatible family of
relative chains has well-defined coefficients on every simplex, since a simplex meets some `Kₙ`,
and the resulting family of coefficients is locally finite, since every point has a neighbourhood
contained in some `Kₙ`, on which only finitely many coefficients of a finite chain are nonzero.

Because the transitions are surjective, the Milnor sequence of a tower of complexes applies to this
limit, so Borel–Moore homology sits in the short exact sequence
`0 → lim¹ₙ H_{j+1}(X, X \ Kₙ; L) → H^{BM}_j(X; L) → limₙ H_j(X, X \ Kₙ; L) → 0`
(`TauCeti.LocalCoefficientSystem.limOneToBorelMooreHomology_injective`,
`TauCeti.LocalCoefficientSystem.exact_limOneToBorelMooreHomology_borelMooreHomologyToLim`,
`TauCeti.LocalCoefficientSystem.borelMooreHomologyToLim_surjective`), whose right-hand map is
induced by the relative classes (`TauCeti.LocalCoefficientSystem.limπ_borelMooreHomologyToLim`).

## Main declarations

* `TopPair.locallyFiniteChainComplexToRelative`: for a pair `(X, B)` with `X \ B` compact, the
  chain map from locally finite chains to `C(X, B; L)`, with naturality in coefficient morphisms
  (`TopPair.locallyFiniteChainComplexCoefficientMap_comp_locallyFiniteChainComplexToRelative`)
  and proper maps of pairs
  (`TopPair.locallyFiniteChainComplexMap_comp_locallyFiniteChainComplexToRelative`).
* `TauCeti.LocalCoefficientSystem.relativeChainComplexTower`: the tower of relative twisted chain
  complexes of a monotone sequence of subsets, with `relativeChainComplexTower_shift_surjective`,
  `relativeChainComplexTowerCoefficientMap`, `relativeChainComplexTowerCoefficientMap_id`, and
  `relativeChainComplexTowerCoefficientMap_comp`.
* `TauCeti.LocalCoefficientSystem.locallyFiniteChainComplexToLimComplex`: the chain map from
  locally finite chains to the limit complex of a tower of compact subsets, with coefficient
  naturality (`locallyFiniteChainComplexToLimComplex_naturality`).
* `TauCeti.LocalCoefficientSystem.isLimitLocallyFiniteChainComplexCone`: for a compact exhaustion,
  the locally finite chain complex is the limit of that tower, with
  `locallyFiniteChainComplexIsoLimComplex` the resulting isomorphism onto the limit complex.
* `TauCeti.LocalCoefficientSystem.borelMooreHomologyToLim` and
  `TauCeti.LocalCoefficientSystem.limOneToBorelMooreHomology`: the two maps of the Milnor sequence
  of Borel–Moore homology.

## References

* J. Milnor, *On axiomatic homology theory*, Pacific J. Math. 12 (1962), 337–341.
* G. E. Bredon, *Sheaf Theory*, 2nd ed., Graduate Texts in Mathematics 170, Chapter V.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite SimplexCategory Topology

open scoped Simplicial

universe u v w

namespace TopPair

open TauCeti TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R]

section ToRelative

variable (P : TopPair.{v}) (L : LocalCoefficientSystem.{u, v, max v w} R P.fst) {k : ℕ}
  (hP : IsCompact (Set.range P.map)ᶜ)

/-- The class in the relative chains of `P = (X, B)`, with `X \ B` compact, of the part of a
locally finite chain on the finitely many simplices meeting `X \ B`. -/
private def toRelativeFun (c : locallyFiniteChains L k) : (P.twistedChainComplex L).X k :=
  ((P.twistedChainComplexπ L).f k).hom <|
    ∑ σ ∈ ((mem_locallyFiniteChains.1 c.property).finite_setOf_inter_nonempty hP).toFinset,
      (ιTwistedChainComplex L k σ).hom ((c : ∀ τ : (TopCat.toSSet.obj P.fst) _⦋k⦌,
        L.obj (initialVertex τ)) σ)

private lemma toRelativeFun_eq (c : locallyFiniteChains L k) :
    toRelativeFun P L hP c = ((P.twistedChainComplexπ L).f k).hom
      (∑ σ ∈ ((mem_locallyFiniteChains.1 c.property).finite_setOf_inter_nonempty hP).toFinset,
        (ιTwistedChainComplex L k σ).hom ((c : ∀ τ : (TopCat.toSSet.obj P.fst) _⦋k⦌,
          L.obj (initialVertex τ)) σ)) :=
  (rfl)

private lemma twistedChainComplexCoeff_toRelativeFun (c : locallyFiniteChains L k)
    (σ : (TopCat.toSSet.obj P.fst) _⦋k⦌)
    (hσ : ¬Set.range (TopCat.simplexMap σ) ⊆ Set.range P.map) :
    (P.twistedChainComplexCoeff L σ hσ).hom (toRelativeFun P L hP c) =
      (c : ∀ τ : (TopCat.toSSet.obj P.fst) _⦋k⦌, L.obj (initialVertex τ)) σ := by
  rw [toRelativeFun_eq, twistedChainComplexCoeff_twistedChainComplexπ_f_apply]
  refine LocalCoefficientSystem.twistedChainComplexCoeff_sum_ιTwistedChainComplex_apply L _
    fun hS ↦ ?_
  by_contra hne
  exact hS ((Set.Finite.mem_toFinset _).2 ⟨hne, Set.inter_compl_nonempty_iff.2 hσ⟩)

/-- The linear map sending a locally finite chain to the class, in the relative chains of a pair
`P = (X, B)` with `X \ B` compact, of its part on the finitely many simplices meeting `X \ B`. -/
def locallyFiniteChainsToRelative :
    locallyFiniteChains L k →ₗ[R] (P.twistedChainComplex L).X k where
  toFun := toRelativeFun P L hP
  map_add' c c' := P.twistedChainComplex_ext_coeff L fun σ hσ ↦ by
    simp only [map_add, twistedChainComplexCoeff_toRelativeFun, Submodule.coe_add, Pi.add_apply]
  map_smul' a c := P.twistedChainComplex_ext_coeff L fun σ hσ ↦ by
    simp only [map_smul, twistedChainComplexCoeff_toRelativeFun, SetLike.val_smul, Pi.smul_apply,
      RingHom.id_apply]

private lemma locallyFiniteChainsToRelative_apply (c : locallyFiniteChains L k) :
    P.locallyFiniteChainsToRelative L hP c = toRelativeFun P L hP c :=
  (rfl)

/-- On a simplex meeting the complement of the subspace, the coefficient of the relative class of
a locally finite chain is the coefficient of the chain. -/
@[simp]
lemma twistedChainComplexCoeff_locallyFiniteChainsToRelative (c : locallyFiniteChains L k)
    (σ : (TopCat.toSSet.obj P.fst) _⦋k⦌)
    (hσ : ¬Set.range (TopCat.simplexMap σ) ⊆ Set.range P.map) :
    (P.twistedChainComplexCoeff L σ hσ).hom (P.locallyFiniteChainsToRelative L hP c) =
      (c : ∀ τ : (TopCat.toSSet.obj P.fst) _⦋k⦌, L.obj (initialVertex τ)) σ :=
  twistedChainComplexCoeff_toRelativeFun P L hP c σ hσ

/-- Taking relative classes commutes with the boundaries. -/
lemma locallyFiniteChainsToRelative_locallyFiniteBoundary (c : locallyFiniteChains L (k + 1)) :
    P.locallyFiniteChainsToRelative L hP (locallyFiniteBoundary L k c) =
      ((P.twistedChainComplex L).d (k + 1) k).hom (P.locallyFiniteChainsToRelative L hP c) := by
  refine P.twistedChainComplex_ext_coeff L fun ρ hρ ↦ ?_
  set S := ((mem_locallyFiniteChains.1 c.property).finite_setOf_inter_nonempty hP).toFinset
  have hd (a : L.twistedChainComplex.X (k + 1)) : ((P.twistedChainComplex L).d (k + 1) k).hom
      (((P.twistedChainComplexπ L).f (k + 1)).hom a) =
        ((P.twistedChainComplexπ L).f k).hom ((L.twistedChainComplex.d (k + 1) k).hom a) :=
    congrArg (fun g ↦ g.hom a) ((P.twistedChainComplexπ L).comm (k + 1) k)
  rw [twistedChainComplexCoeff_locallyFiniteChainsToRelative, coe_locallyFiniteBoundary,
    locallyFiniteBoundaryFun_apply, locallyFiniteChainsToRelative_apply, toRelativeFun_eq, hd,
    twistedChainComplexCoeff_twistedChainComplexπ_f_apply, map_sum, map_sum]
  refine finsum_eq_sum_of_support_subset _ fun σ hσ ↦ (Set.Finite.mem_toFinset _).2 ⟨?_, ?_⟩
  · exact fun h ↦ hσ (by simp [h])
  · -- A simplex inside the subspace has no face meeting its complement, so it does not
    -- contribute on `ρ`.
    by_contra hσA
    have hface (i : Fin (k + 2)) :
        (TopCat.toSSet.obj P.fst).map (SimplexCategory.δ i).op σ ≠ ρ := by
      rintro rfl
      obtain ⟨x, hx, hxA⟩ := Set.inter_compl_nonempty_iff.2 hρ
      exact hσA ⟨x, TopCat.range_simplexMap_map_subset _ σ hx, hxA⟩
    exact hσ (twistedChainComplexCoeff_d_ιTwistedChainComplex_apply_of_forall_ne L hface _)

/-- The chain map from locally finite chains to the relative twisted chains of a pair
`P = (X, B)` with `X \ B` compact, sending a locally finite chain to the class of its part on the
finitely many simplices meeting `X \ B`. -/
def locallyFiniteChainComplexToRelative :
    locallyFiniteChainComplex L ⟶ P.twistedChainComplex L where
  f k := eqToHom (locallyFiniteChainComplex_X L k) ≫
    ModuleCat.ofHom (P.locallyFiniteChainsToRelative L hP)
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    have h : ModuleCat.ofHom (locallyFiniteBoundary L j) ≫
        ModuleCat.ofHom (P.locallyFiniteChainsToRelative L hP) =
          ModuleCat.ofHom (P.locallyFiniteChainsToRelative L hP) ≫
            (P.twistedChainComplex L).d (j + 1) j :=
      ModuleCat.hom_ext <| LinearMap.ext <|
        P.locallyFiniteChainsToRelative_locallyFiniteBoundary L hP
    simp [locallyFiniteChainComplex_d, h]

/-- The components of the chain map to relative chains take relative classes. -/
lemma locallyFiniteChainComplexToRelative_f (k : ℕ) :
    (P.locallyFiniteChainComplexToRelative L hP).f k =
      eqToHom (locallyFiniteChainComplex_X L k) ≫
        ModuleCat.ofHom (P.locallyFiniteChainsToRelative L hP) :=
  (rfl)

/-- On a simplex meeting the complement of the subspace, the coefficient of the relative class of
a locally finite chain is the coefficient of the chain. -/
@[simp]
lemma twistedChainComplexCoeff_locallyFiniteChainComplexToRelative_f_apply
    (c : locallyFiniteChains L k) (σ : (TopCat.toSSet.obj P.fst) _⦋k⦌)
    (hσ : ¬Set.range (TopCat.simplexMap σ) ⊆ Set.range P.map) :
    (P.twistedChainComplexCoeff L σ hσ).hom
        (((P.locallyFiniteChainComplexToRelative L hP).f k).hom
          ((eqToHom (locallyFiniteChainComplex_X L k).symm).hom c)) =
      (c : ∀ τ : (TopCat.toSSet.obj P.fst) _⦋k⦌, L.obj (initialVertex τ)) σ := by
  have h : eqToHom (locallyFiniteChainComplex_X L k).symm ≫
      (P.locallyFiniteChainComplexToRelative L hP).f k =
        ModuleCat.ofHom (P.locallyFiniteChainsToRelative L hP) := by
    rw [locallyFiniteChainComplexToRelative_f, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← LinearMap.comp_apply ((P.locallyFiniteChainComplexToRelative L hP).f k).hom
    (eqToHom (locallyFiniteChainComplex_X L k).symm).hom, ← ModuleCat.hom_comp, h,
    ModuleCat.hom_ofHom, twistedChainComplexCoeff_locallyFiniteChainsToRelative]

/-- On finite chains, the relative class of the associated locally finite chain is the class of
the chain. -/
@[reassoc (attr := simp)]
lemma toLocallyFiniteChainComplex_comp_locallyFiniteChainComplexToRelative :
    toLocallyFiniteChainComplex L ≫ P.locallyFiniteChainComplexToRelative L hP =
      P.twistedChainComplexπ L := by
  ext k : 1
  refine ModuleCat.hom_ext <| LinearMap.ext fun y ↦ P.twistedChainComplex_ext_coeff L fun σ hσ ↦ ?_
  rw [HomologicalComplex.comp_f, toLocallyFiniteChainComplex_f, ModuleCat.hom_comp,
    ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
    twistedChainComplexCoeff_locallyFiniteChainComplexToRelative_f_apply,
    toLocallyFiniteChains_apply, twistedChainComplexCoeff_twistedChainComplexπ_f_apply]

end ToRelative

section ToRelativeNaturality

/-- Taking relative classes of locally finite chains commutes with morphisms of local coefficient
systems. -/
@[reassoc]
theorem locallyFiniteChainComplexCoefficientMap_comp_locallyFiniteChainComplexToRelative
    (P : TopPair.{v}) {L K : LocalCoefficientSystem.{u, v, max v w} R P.fst} (η : L ⟶ K)
    (hP : IsCompact (Set.range P.map)ᶜ) :
    locallyFiniteChainComplexCoefficientMap η ≫ P.locallyFiniteChainComplexToRelative K hP =
      P.locallyFiniteChainComplexToRelative L hP ≫ P.twistedChainComplexCoefficientMap η := by
  ext k : 1
  rw [← cancel_epi (eqToHom (locallyFiniteChainComplex_X L k).symm)]
  refine ModuleCat.hom_ext <| LinearMap.ext fun c ↦
    P.twistedChainComplex_ext_coeff K fun σ hσ ↦ ?_
  have hL : (P.twistedChainComplexCoefficientMap η).f k ≫ P.twistedChainComplexCoeff K σ hσ =
      P.twistedChainComplexCoeff L σ hσ ≫ η.app (initialVertex σ) := by
    apply (cancel_epi ((P.twistedChainComplexπ L).f k)).1
    have hπ := congrArg (fun φ ↦ φ.f k)
      (P.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap η)
    simp only [HomologicalComplex.comp_f] at hπ
    rw [← Category.assoc, hπ, Category.assoc, P.twistedChainComplexπ_f_twistedChainComplexCoeff,
      P.twistedChainComplexπ_f_twistedChainComplexCoeff_assoc]
    refine LocalCoefficientSystem.twistedChainComplex_hom_ext L fun τ ↦ ?_
    rw [ιTwistedChainComplex_twistedChainComplexCoefficientMap_f_assoc]
    by_cases hτ : τ = σ
    · subst hτ
      simp [ιTwistedChainComplex_twistedChainComplexCoeff]
    · simp [ιTwistedChainComplex_twistedChainComplexCoeff_of_ne, hτ]
  simp only [HomologicalComplex.comp_f, locallyFiniteChainComplexCoefficientMap_f,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  rw [P.twistedChainComplexCoeff_locallyFiniteChainComplexToRelative_f_apply K hP _ σ hσ,
    ModuleCat.hom_ofHom, coe_locallyFiniteChainsCoefficientMap_apply]
  have h1 := congrArg (fun f ↦ f.hom (((P.locallyFiniteChainComplexToRelative L hP).f k).hom
    ((eqToHom (locallyFiniteChainComplex_X L k).symm).hom c))) hL
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [h1, P.twistedChainComplexCoeff_locallyFiniteChainComplexToRelative_f_apply L hP c σ hσ]

/-- Pushing a locally finite chain forward along a proper map of pairs commutes with taking
relative classes modulo subspaces with compact complements. -/
@[reassoc]
theorem locallyFiniteChainComplexMap_comp_locallyFiniteChainComplexToRelative
    {P Q : TopPair.{v}} (g : P ⟶ Q)
    (hg : IsProperMap (Hom.fst g).hom) (L : LocalCoefficientSystem.{u, v, max v w} R Q.fst)
    (hP : IsCompact (Set.range P.map)ᶜ) (hQ : IsCompact (Set.range Q.map)ᶜ) :
    locallyFiniteChainComplexMap (Hom.fst g) hg L ≫ Q.locallyFiniteChainComplexToRelative L hQ =
      P.locallyFiniteChainComplexToRelative
          ((LocalCoefficientSystem.pullback (Hom.fst g).hom).obj L) hP ≫
        TopPair.twistedChainComplexMap g L := by
  -- Check equality degreewise and coefficientwise on each simplex `ρ` of `Q` not contained in
  -- `Set.range Q.map`: represent the relative class of `c` on `P` as the projection of its finite
  -- restriction to simplices meeting `(Set.range P.map)ᶜ`, push that finite sum forward along `g`,
  -- and verify that every simplex `σ` contributing to the `ρ`-coefficient lies in that finite set.
  ext k : 1
  rw [← cancel_epi (eqToHom (locallyFiniteChainComplex_X _ k).symm)]
  refine ModuleCat.hom_ext <| LinearMap.ext fun c ↦
    Q.twistedChainComplex_ext_coeff L fun ρ hρ ↦ ?_
  simp only [HomologicalComplex.comp_f, locallyFiniteChainComplexMap_f, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom]
  rw [Q.twistedChainComplexCoeff_locallyFiniteChainComplexToRelative_f_apply L hQ _ ρ hρ,
    coe_locallyFiniteChainsMap_apply]
  have hright : ((P.locallyFiniteChainComplexToRelative _ hP).f k).hom
      ((eqToHom (locallyFiniteChainComplex_X _ k).symm).hom c) =
      ((P.twistedChainComplexπ _).f k).hom
        (∑ σ ∈ ((mem_locallyFiniteChains.1 c.2).finite_setOf_inter_nonempty hP).toFinset,
          (ιTwistedChainComplex _ k σ).hom (c.1 σ)) := by
    refine P.twistedChainComplex_ext_coeff _ fun τ hτ ↦ ?_
    rw [P.twistedChainComplexCoeff_locallyFiniteChainComplexToRelative_f_apply _ hP c τ hτ,
      P.twistedChainComplexCoeff_twistedChainComplexπ_f_apply _ τ hτ,
      twistedChainComplexCoeff_sum_ιTwistedChainComplex_apply]
    intro hnot
    by_contra hc0
    exact hnot (((mem_locallyFiniteChains.1 c.2).finite_setOf_inter_nonempty hP).mem_toFinset.2
      ⟨hc0, Set.inter_compl_nonempty_iff.2 hτ⟩)
  rw [hright, TopPair.twistedChainComplexMap_f_twistedChainComplexπ_f_apply,
    Q.twistedChainComplexCoeff_twistedChainComplexπ_f_apply L ρ hρ, map_sum, map_sum]
  simp only [twistedChainComplexMap_f_ι_apply]
  refine finsum_eq_sum_of_support_subset _ fun σ hσ ↦ ?_
  rw [Function.mem_support] at hσ
  rw [Finset.mem_coe, Set.Finite.mem_toFinset]
  refine ⟨fun hc0 ↦ hσ ?_, ?_⟩
  · -- `((pullback (Hom.fst g).hom).obj L).obj (initialVertex σ)` is definitionally
    -- `L.obj (initialVertex ((TopCat.toSSet.map (Hom.fst g)).app (op ⦋k⦌) σ))`, since `pullback`
    -- composes with `FundamentalGroupoid.map` and `initialVertex` commutes with `toSSet.map`.
    have hc0' :
        (c.1 σ :
          L.obj (initialVertex ((TopCat.toSSet.map (Hom.fst g)).app (op ⦋k⦌) σ))) = 0 := hc0
    trans (L.twistedChainComplexCoeff ρ).hom
        ((L.ιTwistedChainComplex k _).hom
          (0 : L.obj (initialVertex ((TopCat.toSSet.map (Hom.fst g)).app (op ⦋k⦌) σ))))
    · exact congrArg (fun x ↦ (L.twistedChainComplexCoeff ρ).hom
        ((L.ιTwistedChainComplex k _).hom x)) hc0'
    · simp
  rw [Set.inter_compl_nonempty_iff]
  intro hsub
  have hEq : (TopCat.toSSet.map (Hom.fst g)).app _ σ = ρ := by
    by_contra hne
    exact hσ (twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne L hne _)
  apply hρ
  rw [← hEq, TopCat.simplexMap_app, ContinuousMap.coe_comp, Set.range_comp]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy⟩ := hsub hx
  exact ⟨Hom.snd g y, by
    have hw := congrArg (fun f : P.snd ⟶ Q.fst ↦ f y) (Hom.w g)
    simpa [hy] using hw⟩

end ToRelativeNaturality

end TopPair

namespace TauCeti.TopTriple

open LocalCoefficientSystem

variable {R : Type u} [Ring R] (T : TopTriple.{v})
  (L : LocalCoefficientSystem.{u, v, max v w} R T.fst)

/-- For a triple `(X, A, B)` with `X \ A` and `X \ B` compact, the relative classes of locally
finite chains in `C(X, B; L)` and `C(X, A; L)` are compatible with the quotient map. -/
@[reassoc (attr := simp)]
lemma locallyFiniteChainComplexToRelative_comp_twistedChainComplexTotalToOuter
    (hB : IsCompact (Set.range T.totalMap)ᶜ) (hA : IsCompact (Set.range T.outerMap)ᶜ) :
    (totalPair.obj T).locallyFiniteChainComplexToRelative L hB ≫
        T.twistedChainComplexTotalToOuter L =
      (outerPair.obj T).locallyFiniteChainComplexToRelative L hA := by
  ext k : 1
  rw [← cancel_epi (eqToHom (locallyFiniteChainComplex_X L k).symm)]
  refine ModuleCat.hom_ext <| LinearMap.ext fun c ↦
    (outerPair.obj T).twistedChainComplex_ext_coeff L fun σ hσ ↦ ?_
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [twistedChainComplexCoeff_twistedChainComplexTotalToOuter_f_apply,
    TopPair.twistedChainComplexCoeff_locallyFiniteChainComplexToRelative_f_apply,
    TopPair.twistedChainComplexCoeff_locallyFiniteChainComplexToRelative_f_apply]

end TauCeti.TopTriple

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R]

section Tower

/-
The ambient space of the pair `TopPair.ofSubset A` is only definitionally `X`, not reducibly, and
the terms of the tower below are only definitionally relative chain complexes. Goals mixing these
typings cannot be rewritten, so the limit argument goes through the coefficients
`towerCoeff` of the terms of the tower, whose characterizing lemmas are assembled as terms.
-/

variable {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, max v w} R X) (S : ℕ → Set X)
  (hS : ∀ n, S n ⊆ S (n + 1)) {k : ℕ}

/-- The tower of relative twisted chain complexes `C(X, X \ Sₙ; L)` of a monotone sequence of
subsets `S : ℕ → Set X` (`S n ⊆ S (n + 1)`), whose transitions are the quotient maps
`C(X, X \ Sₙ₊₁; L) ⟶ C(X, X \ Sₙ; L)`. -/
-- The body is exposed so that the terms of the tower are the relative chain complexes, which the
-- statements identifying the cone legs and the Milnor maps below need in order to typecheck.
@[expose]
def relativeChainComplexTower : ComplexTower.{max v w} R (ComplexShape.down ℕ) :=
  Functor.ofOpSequence (X := fun n ↦ (TopPair.ofSubset (S n)ᶜ).twistedChainComplex L)
    fun n ↦ TopTriple.twistedChainComplexTotalToOuter
      (TopTriple.ofSubset (Set.compl_subset_compl.2 (hS n))) L

/-- The terms of the tower of a monotone sequence of subsets are the relative twisted chain
complexes. -/
lemma relativeChainComplexTower_obj (n : ℕ) :
    (relativeChainComplexTower L S hS).obj (op n) =
      (TopPair.ofSubset (S n)ᶜ).twistedChainComplex L :=
  (rfl)

/-- The transitions of the tower of a monotone sequence of subsets are the quotient maps. -/
@[simp]
lemma relativeChainComplexTower_map_succ (n : ℕ) :
    (relativeChainComplexTower L S hS).map (homOfLE (Nat.le_succ n)).op =
      TopTriple.twistedChainComplexTotalToOuter
        (TopTriple.ofSubset (Set.compl_subset_compl.2 (hS n))) L :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- Every map of the tower of a monotone sequence of subsets is induced by the identity of the
ambient twisted chains. -/
@[reassoc, simp]
lemma twistedChainComplexπ_comp_relativeChainComplexTower_map {m n : ℕ} (f : op m ⟶ op n) :
    (TopPair.ofSubset (S m)ᶜ).twistedChainComplexπ L ≫ (relativeChainComplexTower L S hS).map f =
      (TopPair.ofSubset (S n)ᶜ).twistedChainComplexπ L := by
  have hnm : n ≤ m := leOfHom f.unop
  induction m, hnm using Nat.le_induction with
  | base =>
    obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
    exact (congrArg (_ ≫ ·) ((relativeChainComplexTower L S hS).map_id _)).trans
      (Category.comp_id _)
  | succ m hnm ih =>
    obtain rfl : f = (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op := Subsingleton.elim _ _
    refine (congrArg (_ ≫ ·) ((relativeChainComplexTower L S hS).map_comp _ _)).trans <|
      (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) ?_).trans (ih _)
    exact (congrArg (_ ≫ ·) (relativeChainComplexTower_map_succ L S hS m)).trans
      ((TopTriple.ofSubset _).twistedChainComplexπ_comp_totalToOuter L)

/-- The transitions of the tower of a monotone sequence of subsets are surjective in every
degree. -/
lemma relativeChainComplexTower_transition_surjective (i n : ℕ) :
    Function.Surjective (((relativeChainComplexTower L S hS).term i).transition n) := by
  rw [ModuleTower.transition_def, Functor.comp_map, HomologicalComplex.eval_map]
  intro y
  obtain ⟨a, rfl⟩ := (TopPair.ofSubset (S n)ᶜ).twistedChainComplexπ_f_surjective L y
  exact ⟨(((TopPair.ofSubset (S (n + 1))ᶜ).twistedChainComplexπ L).f i).hom a,
    congrArg (fun g ↦ (g.f i).hom a)
      (twistedChainComplexπ_comp_relativeChainComplexTower_map L S hS
        (homOfLE (Nat.le_succ n)).op)⟩

/-- The tower of a monotone sequence of subsets has surjective shift maps in every degree, so its
`lim¹` vanishes and the Milnor sequence applies to it. -/
lemma relativeChainComplexTower_shift_surjective (i : ℕ) :
    Function.Surjective ((relativeChainComplexTower L S hS).term i).shift :=
  ModuleTower.shift_surjective _ (relativeChainComplexTower_transition_surjective L S hS i)

/-- A morphism of local coefficient systems induces a morphism of relative chain complex towers. -/
def relativeChainComplexTowerCoefficientMap
    {L K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K) (S : ℕ → Set X)
    (hS : ∀ n, S n ⊆ S (n + 1)) :
    relativeChainComplexTower L S hS ⟶ relativeChainComplexTower K S hS where
  app n := (TopPair.ofSubset (S n.unop)ᶜ).twistedChainComplexCoefficientMap η
  naturality {m n} f := by
    apply (TopPair.ofSubset (S m.unop)ᶜ).twistedChainComplex_hom_ext L
    -- `(TopPair.ofSubset _).fst` is only definitionally `X`, so `rw`/`simp` fail at `implicit`
    -- transparency; explicit `trans` steps let elaboration align the ambient types.
    trans (TopPair.ofSubset (S n.unop)ᶜ).twistedChainComplexπ L ≫
        (TopPair.ofSubset (S n.unop)ᶜ).twistedChainComplexCoefficientMap η
    · exact twistedChainComplexπ_comp_relativeChainComplexTower_map_assoc L S hS f _
    trans twistedChainComplexCoefficientMap η ≫
        (TopPair.ofSubset (S n.unop)ᶜ).twistedChainComplexπ K
    · exact TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap
        (TopPair.ofSubset (S n.unop)ᶜ) η
    trans twistedChainComplexCoefficientMap η ≫
        (TopPair.ofSubset (S m.unop)ᶜ).twistedChainComplexπ K ≫
        (relativeChainComplexTower K S hS).map f
    · exact congrArg (_ ≫ ·)
        (twistedChainComplexπ_comp_relativeChainComplexTower_map K S hS f).symm
    · exact (TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc
        (TopPair.ofSubset (S m.unop)ᶜ) η _).symm

/-- On each level, `relativeChainComplexTowerCoefficientMap` is the relative coefficient map. -/
@[simp]
lemma relativeChainComplexTowerCoefficientMap_app
    {L K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K) (S : ℕ → Set X)
    (hS : ∀ n, S n ⊆ S (n + 1)) (n : ℕ) :
    (relativeChainComplexTowerCoefficientMap η S hS).app (op n) =
      (TopPair.ofSubset (S n)ᶜ).twistedChainComplexCoefficientMap η :=
  (rfl)

/-- The identity morphism of local coefficient systems induces the identity morphism of relative
chain complex towers. -/
@[simp]
lemma relativeChainComplexTowerCoefficientMap_id
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (S : ℕ → Set X)
    (hS : ∀ n, S n ⊆ S (n + 1)) :
    relativeChainComplexTowerCoefficientMap (𝟙 L) S hS =
      𝟙 (relativeChainComplexTower L S hS) := by
  apply NatTrans.ext
  funext ⟨n⟩
  exact TopPair.twistedChainComplexCoefficientMap_id (TopPair.ofSubset (S n)ᶜ) L

/-- Composition of morphisms of local coefficient systems induces the composite of the morphisms
of relative chain complex towers. -/
@[simp, reassoc]
lemma relativeChainComplexTowerCoefficientMap_comp
    {L K J : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K) (θ : K ⟶ J)
    (S : ℕ → Set X) (hS : ∀ n, S n ⊆ S (n + 1)) :
    relativeChainComplexTowerCoefficientMap (η ≫ θ) S hS =
      relativeChainComplexTowerCoefficientMap η S hS ≫
        relativeChainComplexTowerCoefficientMap θ S hS := by
  apply NatTrans.ext
  funext ⟨n⟩
  exact TopPair.twistedChainComplexCoefficientMap_comp (TopPair.ofSubset (S n)ᶜ) η θ

/-- The locally finite chain complex, with the chain maps to the relative twisted chains of the
pairs `(X, X \ Sₙ)`, as a cone over the tower of a monotone sequence of compact subsets. -/
-- The body is exposed so that the point and legs of the cone are visible to its consumers.
@[expose]
def locallyFiniteChainComplexCone (hSc : ∀ n, IsCompact (S n)) :
    Cone (relativeChainComplexTower L S hS) where
  pt := locallyFiniteChainComplex L
  π := NatTrans.ofOpSequence (fun n ↦ (TopPair.ofSubset (S n)ᶜ).locallyFiniteChainComplexToRelative
    L (hSc n).compl_range_ofSubset_compl_map) fun n ↦
    (Category.id_comp _).trans <|
      ((congrArg (_ ≫ ·) (relativeChainComplexTower_map_succ L S hS n)).trans
        (TopTriple.locallyFiniteChainComplexToRelative_comp_twistedChainComplexTotalToOuter
          (TopTriple.ofSubset (Set.compl_subset_compl.2 (hS n))) L
          (hSc (n + 1)).compl_range_ofSubset_compl_map
          (hSc n).compl_range_ofSubset_compl_map)).symm

/-- The point of the locally finite cone is the locally finite chain complex. -/
@[simp]
lemma locallyFiniteChainComplexCone_pt (hSc : ∀ n, IsCompact (S n)) :
    (locallyFiniteChainComplexCone L S hS hSc).pt = locallyFiniteChainComplex L :=
  (rfl)

/-- The legs of the locally finite cone take relative classes. -/
@[simp]
lemma locallyFiniteChainComplexCone_π_app (hSc : ∀ n, IsCompact (S n)) (n : ℕ) :
    (locallyFiniteChainComplexCone L S hS hSc).π.app (op n) =
      (TopPair.ofSubset (S n)ᶜ).locallyFiniteChainComplexToRelative L
        (hSc n).compl_range_ofSubset_compl_map :=
  (rfl)

/-- The relative classes of a locally finite chain for a monotone sequence of compact subsets are
compatible with the maps of the tower. -/
@[reassoc, simp]
lemma locallyFiniteChainComplexToRelative_comp_relativeChainComplexTower_map
    (hSc : ∀ n, IsCompact (S n)) {m n : ℕ} (f : op m ⟶ op n) :
    (TopPair.ofSubset (S m)ᶜ).locallyFiniteChainComplexToRelative L
        (hSc m).compl_range_ofSubset_compl_map ≫ (relativeChainComplexTower L S hS).map f =
      (TopPair.ofSubset (S n)ᶜ).locallyFiniteChainComplexToRelative L
        (hSc n).compl_range_ofSubset_compl_map :=
  (locallyFiniteChainComplexCone L S hS hSc).w f

/-- The chain map from locally finite chains to the limit complex of the relative tower of a
monotone sequence of compact subsets. -/
def locallyFiniteChainComplexToLimComplex (hSc : ∀ n, IsCompact (S n)) :
    locallyFiniteChainComplex L ⟶ (relativeChainComplexTower L S hS).limComplex :=
  (relativeChainComplexTower L S hS).isLimitLimComplexCone.lift
    (locallyFiniteChainComplexCone L S hS hSc)

/-- The `n`-th projection of `locallyFiniteChainComplexToLimComplex` takes relative classes modulo
`X \ Sₙ`. -/
@[reassoc (attr := simp)]
lemma locallyFiniteChainComplexToLimComplex_comp_limComplexπ
    (hSc : ∀ n, IsCompact (S n)) (n : ℕ) :
    locallyFiniteChainComplexToLimComplex L S hS hSc ≫
        (relativeChainComplexTower L S hS).limComplexπ n =
      (TopPair.ofSubset (S n)ᶜ).locallyFiniteChainComplexToRelative L
        (hSc n).compl_range_ofSubset_compl_map :=
  (relativeChainComplexTower L S hS).isLimitLimComplexCone.fac
    (locallyFiniteChainComplexCone L S hS hSc) (op n)

section CompactExhaustionLimit

variable (K : CompactExhaustion X)

/-- The coefficient on a simplex meeting `Kₙ` of a chain in the `n`-th term of the tower. -/
private def towerCoeff (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋k⦌)
    (hσ : (Set.range (TopCat.simplexMap σ) ∩ K n).Nonempty) :
    ((relativeChainComplexTower L K K.subset_succ).obj (op n)).X k ⟶ L.obj (initialVertex σ) :=
  (TopPair.ofSubset (K n)ᶜ).twistedChainComplexCoeff L σ
    (TopPair.not_range_simplexMap_subset_range_ofSubset_compl_map_iff.2 hσ)

/-- A chain in a term of the tower is determined by its coefficients. -/
private lemma towerCoeff_ext {n : ℕ}
    {y y' : ((relativeChainComplexTower L K K.subset_succ).obj (op n)).X k}
    (h : ∀ σ hσ, (towerCoeff L K n σ hσ).hom y = (towerCoeff L K n σ hσ).hom y') : y = y' :=
  (TopPair.ofSubset (K n)ᶜ).twistedChainComplex_ext_coeff L fun σ hσ ↦
    h σ (TopPair.not_range_simplexMap_subset_range_ofSubset_compl_map_iff.1 hσ)

/-- The coefficients of a chain in a term of the tower are those of an ambient twisted chain. -/
private lemma exists_towerCoeff_eq {n : ℕ}
    (y : ((relativeChainComplexTower L K K.subset_succ).obj (op n)).X k) :
    ∃ a : L.twistedChainComplex.X k,
      ∀ σ hσ, (towerCoeff L K n σ hσ).hom y = (twistedChainComplexCoeff L σ).hom a := by
  obtain ⟨a, rfl⟩ := (TopPair.ofSubset (K n)ᶜ).twistedChainComplexπ_f_surjective L y
  exact ⟨a, fun σ _ ↦
    (TopPair.ofSubset (K n)ᶜ).twistedChainComplexCoeff_twistedChainComplexπ_f_apply L σ _ a⟩

/-- The maps of the tower preserve the coefficients on simplices meeting the smaller compact
set. -/
private lemma towerCoeff_map {m n : ℕ} (f : op m ⟶ op n) (σ : (TopCat.toSSet.obj X) _⦋k⦌)
    (hn : (Set.range (TopCat.simplexMap σ) ∩ K n).Nonempty)
    (hm : (Set.range (TopCat.simplexMap σ) ∩ K m).Nonempty)
    (y : ((relativeChainComplexTower L K K.subset_succ).obj (op m)).X k) :
    (towerCoeff L K n σ hn).hom
        ((((relativeChainComplexTower L K K.subset_succ).map f).f k).hom y) =
      (towerCoeff L K m σ hm).hom y := by
  obtain ⟨a, rfl⟩ := (TopPair.ofSubset (K m)ᶜ).twistedChainComplexπ_f_surjective L y
  exact (congrArg _ (congrArg (fun g ↦ (g.f k).hom a)
    (twistedChainComplexπ_comp_relativeChainComplexTower_map L K K.subset_succ f))).trans
    (((TopPair.ofSubset (K n)ᶜ).twistedChainComplexCoeff_twistedChainComplexπ_f_apply L σ _
      a).trans ((TopPair.ofSubset (K m)ᶜ).twistedChainComplexCoeff_twistedChainComplexπ_f_apply L
        σ _ a).symm)

/-- The relative class of a locally finite chain in the `n`-th term of the tower. -/
private abbrev toTower (n : ℕ) :
    locallyFiniteChainComplex L ⟶ (relativeChainComplexTower L K K.subset_succ).obj (op n) :=
  (TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative L
    (K.isCompact n).compl_range_ofSubset_compl_map

private lemma towerCoeff_toTower (n : ℕ) (c : locallyFiniteChains L k)
    (σ : (TopCat.toSSet.obj X) _⦋k⦌) (hσ : (Set.range (TopCat.simplexMap σ) ∩ K n).Nonempty) :
    (towerCoeff L K n σ hσ).hom
        (((toTower L K n).f k).hom ((eqToHom (locallyFiniteChainComplex_X L k).symm).hom c)) =
      (c : ∀ τ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex τ)) σ :=
  (TopPair.ofSubset (K n)ᶜ).twistedChainComplexCoeff_locallyFiniteChainComplexToRelative_f_apply L
    (K.isCompact n).compl_range_ofSubset_compl_map c σ
    (TopPair.not_range_simplexMap_subset_range_ofSubset_compl_map_iff.2 hσ)

/-- The degree-`k` component of the map from locally finite chains to the limit of the tower,
precomposed with the identification of its source with the module of locally finite chains. -/
private abbrev toLim (k : ℕ) : ModuleCat.of R (locallyFiniteChains L k) ⟶
    (relativeChainComplexTower L K K.subset_succ).limComplex.X k :=
  eqToHom (locallyFiniteChainComplex_X L k).symm ≫
    ((relativeChainComplexTower L K K.subset_succ).isLimitLimComplexCone.lift
      (locallyFiniteChainComplexCone L K K.subset_succ K.isCompact)).f k

private lemma limπ_toLim_apply (n : ℕ) (c : locallyFiniteChains L k) :
    ((relativeChainComplexTower L K K.subset_succ).term k).limπ n ((toLim L K k).hom c) =
      ((toTower L K n).f k).hom ((eqToHom (locallyFiniteChainComplex_X L k).symm).hom c) := by
  have h := congrArg (fun φ : locallyFiniteChainComplex L ⟶
      (relativeChainComplexTower L K K.subset_succ).obj (op n) ↦
        (φ.f k).hom ((eqToHom (locallyFiniteChainComplex_X L k).symm).hom c))
    ((relativeChainComplexTower L K K.subset_succ).isLimitLimComplexCone.fac
      (locallyFiniteChainComplexCone L K K.subset_succ K.isCompact) (op n))
  rw [← ComplexTower.limComplexπ_f_hom]
  -- `h` is the goal up to definitional unfolding: the leg of `limComplexCone` at `n` is
  -- `limComplexπ n` (`ComplexTower.limComplexCone_π_app`), the leg of
  -- `locallyFiniteChainComplexCone` at `n` is `toTower n`, and the component of a composite of
  -- chain maps applied to an element is the composite application.
  exact h

/-- A point of the limit of the tower has the same coefficient on a simplex `σ` in every term
with `σ` meeting the corresponding compact set. -/
private lemma towerCoeff_limπ_eq_of_le
    (x : ((relativeChainComplexTower L K K.subset_succ).term k).lim)
    (σ : (TopCat.toSSet.obj X) _⦋k⦌) {m n : ℕ} (hnm : n ≤ m)
    (hn : (Set.range (TopCat.simplexMap σ) ∩ K n).Nonempty)
    (hm : (Set.range (TopCat.simplexMap σ) ∩ K m).Nonempty) :
    (towerCoeff L K n σ hn).hom
        (((relativeChainComplexTower L K K.subset_succ).term k).limπ n x) =
      (towerCoeff L K m σ hm).hom
        (((relativeChainComplexTower L K K.subset_succ).term k).limπ m x) := by
  have hx : ((relativeChainComplexTower L K K.subset_succ).term k).limπ n x =
      (((relativeChainComplexTower L K K.subset_succ).map (homOfLE hnm).op).f k).hom
        (((relativeChainComplexTower L K K.subset_succ).term k).limπ m x) := by
    rw [ModuleTower.limπ_apply, ModuleTower.limπ_apply,
      ← ModuleTower.transitionOfLE_coe_lim _ x hnm, ModuleTower.transitionOfLE_def,
      Functor.comp_map, HomologicalComplex.eval_map]
  rw [hx, towerCoeff_map L K _ σ hn hm]

/-- The map from locally finite chains to the limit of the tower is bijective in every degree. -/
private lemma bijective_toLim : Function.Bijective (toLim L K k).hom := by
  -- Every simplex meets the compact set of the first stage containing its initial vertex.
  let N (σ : (TopCat.toSSet.obj X) _⦋k⦌) : ℕ := K.find (TopCat.simplexMap σ (toTopInitialVertex _))
  have hN (σ : (TopCat.toSSet.obj X) _⦋k⦌) : (Set.range (TopCat.simplexMap σ) ∩ K (N σ)).Nonempty :=
    ⟨_, ⟨_, rfl⟩, K.mem_find _⟩
  -- The coefficient on `σ` of a point of the limit, read off in any term with `σ` meeting the
  -- corresponding compact set.
  have hc (x : ((relativeChainComplexTower L K K.subset_succ).term k).lim) (n : ℕ) (σ)
      (hσ : (Set.range (TopCat.simplexMap σ) ∩ K n).Nonempty) :
      (towerCoeff L K n σ hσ).hom
          (((relativeChainComplexTower L K K.subset_succ).term k).limπ n x) =
        (towerCoeff L K (N σ) σ (hN σ)).hom
          (((relativeChainComplexTower L K K.subset_succ).term k).limπ (N σ) x) :=
    (towerCoeff_limπ_eq_of_le L K x σ (le_max_left n (N σ)) hσ
      (hσ.mono (Set.inter_subset_inter_right _ (K.subset (le_max_left _ _))))).trans
    (towerCoeff_limπ_eq_of_le L K x σ (le_max_right n (N σ)) (hN σ) _).symm
  refine ⟨fun c c' h ↦ Subtype.ext <| funext fun σ ↦ ?_, fun x ↦ ?_⟩
  · have h' := congrArg (fun y ↦ (towerCoeff L K (N σ) σ (hN σ)).hom
      (((relativeChainComplexTower L K K.subset_succ).term k).limπ (N σ) y)) h
    dsimp only at h'
    rwa [limπ_toLim_apply, limπ_toLim_apply, towerCoeff_toTower, towerCoeff_toTower] at h'
  let c (σ : (TopCat.toSSet.obj X) _⦋k⦌) : L.obj (initialVertex σ) :=
    (towerCoeff L K (N σ) σ (hN σ)).hom
      (((relativeChainComplexTower L K K.subset_succ).term k).limπ (N σ) x)
  -- Near a point, the coefficients are those of a single finite ambient chain.
  have hlf : c ∈ locallyFiniteChains L k := by
    refine mem_locallyFiniteChains.2 <| isLocallyFiniteChain_iff.2 fun p ↦ ?_
    obtain ⟨n, hn⟩ := K.exists_mem_nhds p
    obtain ⟨a, ha⟩ := exists_towerCoeff_eq L K
      (((relativeChainComplexTower L K K.subset_succ).term k).limπ n x)
    refine ⟨K n, hn, (finite_support_twistedChainComplexCoeff L a).subset ?_⟩
    rintro σ ⟨hσ, hσK⟩
    rw [Set.mem_ofPred_eq, ← ha σ hσK, hc x n σ hσK]
    exact hσ
  refine ⟨⟨c, hlf⟩, ModuleTower.lim_ext _ fun n ↦ ?_⟩
  rw [limπ_toLim_apply]
  exact towerCoeff_ext L K fun σ hσ ↦ (towerCoeff_toTower L K n ⟨c, hlf⟩ σ hσ).trans
    (hc x n σ hσ).symm

/-- The map from locally finite chains to the limit complex of the tower of a compact exhaustion is
an isomorphism. -/
instance isIso_isLimitLimComplexCone_lift_locallyFiniteChainComplexCone :
    IsIso ((relativeChainComplexTower L K K.subset_succ).isLimitLimComplexCone.lift
      (locallyFiniteChainComplexCone L K K.subset_succ K.isCompact)) := by
  have (k : ℕ) : IsIso (((relativeChainComplexTower L K K.subset_succ).isLimitLimComplexCone.lift
      (locallyFiniteChainComplexCone L K K.subset_succ K.isCompact)).f k) :=
    (ConcreteCategory.isIso_iff_bijective _).2 <| (Function.Bijective.of_comp_iff _
      (ConcreteCategory.bijective_of_isIso
        (eqToHom (locallyFiniteChainComplex_X L k).symm))).1 (bijective_toLim L K)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **Locally finite chains form the inverse limit of relative chains.** For a compact exhaustion
`K` of `X`, the locally finite chain complex, with the maps sending a locally finite chain to the
class of its part on the simplices meeting `Kₙ`, is the limit of the tower of relative twisted
chain complexes `C(X, X \ Kₙ; L)`. -/
def isLimitLocallyFiniteChainComplexCone :
    IsLimit (locallyFiniteChainComplexCone L K K.subset_succ K.isCompact) :=
  IsLimit.ofPointIso (relativeChainComplexTower L K K.subset_succ).isLimitLimComplexCone

end CompactExhaustionLimit

end Tower

section TowerNaturality

variable {X : TopCat.{v}}

/-- Congruence of relative classes of locally finite chains along an equality of subsets. -/
lemma locallyFiniteChainComplexToRelative_congr
    (L : LocalCoefficientSystem.{u, v, max v w} R X) {S T : Set X} (h : S = T)
    (hS : IsCompact (Set.range (TopPair.ofSubset S).map)ᶜ)
    (hT : IsCompact (Set.range (TopPair.ofSubset T).map)ᶜ) :
    (TopPair.ofSubset S).locallyFiniteChainComplexToRelative L hS ≫
        eqToHom (congrArg (fun A : Set X ↦ (TopPair.ofSubset A).twistedChainComplex L) h) =
      (TopPair.ofSubset T).locallyFiniteChainComplexToRelative L hT := by
  subst h
  simp

/-- The map from locally finite chains to the limit complex of a tower of compact subsets is
natural in morphisms of local coefficient systems. -/
@[reassoc]
theorem locallyFiniteChainComplexToLimComplex_naturality
    {L K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K)
    (S : ℕ → Set X) (hS : ∀ n, S n ⊆ S (n + 1)) (hSc : ∀ n, IsCompact (S n)) :
    locallyFiniteChainComplexCoefficientMap η ≫
        locallyFiniteChainComplexToLimComplex K S hS hSc =
      locallyFiniteChainComplexToLimComplex L S hS hSc ≫
        ComplexTower.limComplexMap (relativeChainComplexTowerCoefficientMap η S hS) := by
  apply (relativeChainComplexTower K S hS).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  simp only [ComplexTower.limComplexCone_π_app, Category.assoc,
    ComplexTower.limComplexMap_comp_π,
    locallyFiniteChainComplexToLimComplex_comp_limComplexπ,
    locallyFiniteChainComplexToLimComplex_comp_limComplexπ_assoc]
  rw [relativeChainComplexTowerCoefficientMap_app]
  exact TopPair.locallyFiniteChainComplexCoefficientMap_comp_locallyFiniteChainComplexToRelative
    (TopPair.ofSubset (S n)ᶜ) η (hSc n).compl_range_ofSubset_compl_map

end TowerNaturality

section Milnor

variable {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, max v w} R X) (K : CompactExhaustion X)

/-- The isomorphism from the locally finite chain complex to the limit complex of the tower of a
compact exhaustion, whose components are the relative classes of locally finite chains
(`TauCeti.LocalCoefficientSystem.locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexπ`). -/
def locallyFiniteChainComplexIsoLimComplex :
    locallyFiniteChainComplex L ≅ (relativeChainComplexTower L K K.subset_succ).limComplex :=
  (isLimitLocallyFiniteChainComplexCone L K).conePointUniqueUpToIso
    (relativeChainComplexTower L K K.subset_succ).isLimitLimComplexCone

/-- The forward map of `locallyFiniteChainComplexIsoLimComplex` is
`locallyFiniteChainComplexToLimComplex`. -/
lemma locallyFiniteChainComplexIsoLimComplex_hom_eq :
    (locallyFiniteChainComplexIsoLimComplex L K).hom =
      locallyFiniteChainComplexToLimComplex L K K.subset_succ K.isCompact :=
  (rfl)

/-- The components of the isomorphism to the limit complex are the relative classes. -/
@[reassoc (attr := simp)]
lemma locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexπ (n : ℕ) :
    (locallyFiniteChainComplexIsoLimComplex L K).hom ≫
        (relativeChainComplexTower L K K.subset_succ).limComplexπ n =
      (TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative L
        (K.isCompact n).compl_range_ofSubset_compl_map :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (op n)

/-- The map from Borel–Moore homology to the limit of the relative twisted homology modules
`H_j(X, X \ Kₙ; L)` of a compact exhaustion, whose components are induced by the relative classes
of locally finite chains (`TauCeti.LocalCoefficientSystem.limπ_borelMooreHomologyToLim`). -/
def borelMooreHomologyToLim (j : ℕ) :
    borelMooreHomology L j →ₗ[R]
      ((relativeChainComplexTower L K K.subset_succ).homology j).lim :=
  (relativeChainComplexTower L K K.subset_succ).homologyToLim j ∘ₗ
    (HomologicalComplex.homologyMap (locallyFiniteChainComplexIsoLimComplex L K).hom j).hom

/-- The map from Borel–Moore homology to the limit of relative homology is the map of the tower
of complexes to the limit of its homology, after identifying locally finite chains with the limit
complex. -/
lemma borelMooreHomologyToLim_def (j : ℕ) :
    borelMooreHomologyToLim L K j =
      (relativeChainComplexTower L K K.subset_succ).homologyToLim j ∘ₗ
        (HomologicalComplex.homologyMap (locallyFiniteChainComplexIsoLimComplex L K).hom j).hom :=
  (rfl)

/-- The components of the map from Borel–Moore homology to the limit of relative homology are the
maps induced by the relative classes of locally finite chains. -/
lemma limπ_borelMooreHomologyToLim (j n : ℕ) (x : borelMooreHomology L j) :
    ((relativeChainComplexTower L K K.subset_succ).homology j).limπ n
        (borelMooreHomologyToLim L K j x) =
      (HomologicalComplex.homologyMap ((TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative
        L (K.isCompact n).compl_range_ofSubset_compl_map) j).hom x :=
  (ModuleTower.limπ_apply _ n _).trans <| (ComplexTower.coe_homologyToLim_apply _ j _ n).trans <|
    (congrArg (fun g : (locallyFiniteChainComplex L).homology j ⟶
        ((relativeChainComplexTower L K K.subset_succ).obj (op n)).homology j ↦ g.hom x)
      (HomologicalComplex.homologyMap_comp _ _ j).symm).trans
      (congrArg (fun φ : locallyFiniteChainComplex L ⟶
          (relativeChainComplexTower L K K.subset_succ).obj (op n) ↦
        (HomologicalComplex.homologyMap φ j).hom x)
        (locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexπ L K n))

/-- The map from `lim¹` of the relative twisted homology modules `H_{j+1}(X, X \ Kₙ; L)` of a
compact exhaustion to Borel–Moore homology in degree `j`: the connecting map of the Milnor
sequence. -/
def limOneToBorelMooreHomology (j : ℕ) :
    ((relativeChainComplexTower L K K.subset_succ).homology (j + 1)).limOne →ₗ[R]
      borelMooreHomology L j :=
  (HomologicalComplex.homologyMap (locallyFiniteChainComplexIsoLimComplex L K).inv j).hom ∘ₗ
    (relativeChainComplexTower L K K.subset_succ).limOneToHomology
      (relativeChainComplexTower_shift_surjective L K K.subset_succ)
      (ComplexShape.down_mk (j + 1) j rfl)

/-- The connecting map of the Milnor sequence of Borel–Moore homology is the connecting map of the
tower of complexes, after identifying the limit complex with locally finite chains. -/
lemma limOneToBorelMooreHomology_def (j : ℕ) :
    limOneToBorelMooreHomology L K j =
      (HomologicalComplex.homologyMap (locallyFiniteChainComplexIsoLimComplex L K).inv j).hom ∘ₗ
        (relativeChainComplexTower L K K.subset_succ).limOneToHomology
          (relativeChainComplexTower_shift_surjective L K K.subset_succ)
          (ComplexShape.down_mk (j + 1) j rfl) :=
  (rfl)

/-- The connecting map of the Milnor sequence of Borel–Moore homology is injective. -/
theorem limOneToBorelMooreHomology_injective (j : ℕ) :
    Function.Injective (limOneToBorelMooreHomology L K j) := by
  let e := (HomologicalComplex.homologyMapIso
    (locallyFiniteChainComplexIsoLimComplex L K) j).toLinearEquiv
  rw [limOneToBorelMooreHomology_def, LinearMap.coe_comp]
  exact e.symm.injective.comp (ComplexTower.limOneToHomology_injective _ _)

/-- **The Milnor sequence of Borel–Moore homology** is exact in the middle: the image of `lim¹`
is the kernel of the map to the limit of relative homology. -/
theorem exact_limOneToBorelMooreHomology_borelMooreHomologyToLim (j : ℕ) :
    Function.Exact (limOneToBorelMooreHomology L K j) (borelMooreHomologyToLim L K j) := by
  let e := (HomologicalComplex.homologyMapIso
    (locallyFiniteChainComplexIsoLimComplex L K) j).toLinearEquiv
  have hexact := ComplexTower.exact_limOneToHomology_homologyToLim
    (relativeChainComplexTower_shift_surjective L K K.subset_succ)
    (ComplexShape.down_mk (j + 1) j rfl)
  refine Function.Exact.of_ladder_linearEquiv_of_exact (e₁ := LinearEquiv.refl R _)
    (e₂ := e.symm) (e₃ := LinearEquiv.refl R _) ?_ ?_ hexact
  · rw [limOneToBorelMooreHomology_def]
    rfl
  · rw [borelMooreHomologyToLim_def]
    exact LinearMap.ext fun x ↦
      congrArg ((relativeChainComplexTower L K K.subset_succ).homologyToLim j)
        (e.apply_symm_apply x)

/-- The map from Borel–Moore homology to the limit of the relative twisted homology modules of a
compact exhaustion is surjective. -/
theorem borelMooreHomologyToLim_surjective (j : ℕ) :
    Function.Surjective (borelMooreHomologyToLim L K j) := by
  let e := (HomologicalComplex.homologyMapIso
    (locallyFiniteChainComplexIsoLimComplex L K) j).toLinearEquiv
  rw [borelMooreHomologyToLim_def, LinearMap.coe_comp]
  exact (ComplexTower.homologyToLim_surjective
    (relativeChainComplexTower_shift_surjective L K K.subset_succ) j).comp e.surjective

end Milnor

end TauCeti.LocalCoefficientSystem
