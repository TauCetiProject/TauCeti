/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import TauCeti.Algebra.Category.ModuleCat.Tower.Milnor.Naturality
public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Functoriality
public import TauCeti.AlgebraicTopology.Singular.Twisted.Triple

/-!
# Locally finite chains as an inverse limit of relative chains

Let `K₀ ⊆ K₁ ⊆ ⋯` be a compact exhaustion of a space `X` and let `L` be a local coefficient system
on `X`. The relative twisted chain complexes `C(X, X \ Kₙ; L)`, with the quotient maps
`C(X, X \ Kₙ₊₁; L) ⟶ C(X, X \ Kₙ; L)` of the triples `(X, X \ Kₙ, X \ Kₙ₊₁)`, form a tower of
chain complexes whose transition maps are surjective in every degree
(`TauCeti.LocalCoefficientSystem.relativeChainComplexTower`), obtained by specializing the general
complement tower `TauCeti.LocalCoefficientSystem.complChainComplexTower` of any monotone sequence
`C₀ ⊆ C₁ ⊆ ⋯` (together with its enlargement, coefficient, and pair-map functoriality).

For a pair `(X, B)` with `X \ B` compact, a locally finite chain has only finitely many simplices
with nonzero coefficient meeting `X \ B`, and the class in `C(X, B; L)` of its part on those
simplices is linear in the chain and commutes with the boundaries
(`TopPair.locallyFiniteChainComplexToRelative`), compatibly with the quotient maps of triples
(`TauCeti.TopTriple.locallyFiniteChainComplexToRelative_comp_twistedChainComplexTotalToOuter`).
For the pairs `(X, X \ Kₙ)` these chain maps form a cone over the tower, and this cone is a limit
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
  chain map from locally finite chains to `C(X, B; L)`.
* `TauCeti.LocalCoefficientSystem.complChainComplexTower`: the tower `C(X, X \ Cₙ; L)` of a
  monotone sequence `C`, with `locallyFiniteChainComplexToComplLim`, `complChainComplexTowerMap`,
  `complChainComplexTowerCoefficientMap`, and `complChainComplexTowerPairMap`.
* `TauCeti.LocalCoefficientSystem.relativeChainComplexTower`: the tower of relative twisted chain
  complexes of a compact exhaustion, with `relativeChainComplexTower_shift_surjective`.
* `TauCeti.LocalCoefficientSystem.isLimitLocallyFiniteChainComplexCone`: the locally finite chain
  complex is the limit of that tower, with `locallyFiniteChainComplexIsoLimComplex` the resulting
  isomorphism onto the limit complex.
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
    ∑ σ ∈ ((mem_locallyFiniteChains.1 c.2).finite_setOf_inter_nonempty hP).toFinset,
      (ιTwistedChainComplex L k σ).hom ((c : ∀ τ : (TopCat.toSSet.obj P.fst) _⦋k⦌,
        L.obj (initialVertex τ)) σ)

private lemma toRelativeFun_eq (c : locallyFiniteChains L k) :
    toRelativeFun P L hP c = ((P.twistedChainComplexπ L).f k).hom
      (∑ σ ∈ ((mem_locallyFiniteChains.1 c.2).finite_setOf_inter_nonempty hP).toFinset,
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
  set S := ((mem_locallyFiniteChains.1 c.2).finite_setOf_inter_nonempty hP).toFinset
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

/-- Taking relative classes of locally finite chains is natural in local coefficients. -/
@[reassoc] theorem locallyFiniteChainComplexToRelative_naturality
    {L₁ L₂ : LocalCoefficientSystem.{u, v, max v w} R P.fst} (η : L₁ ⟶ L₂) :
    P.locallyFiniteChainComplexToRelative L₁ hP ≫ P.twistedChainComplexCoefficientMap η =
      locallyFiniteChainComplexCoefficientMap η ≫ P.locallyFiniteChainComplexToRelative L₂ hP := by
  ext k : 1; rw [← cancel_epi (eqToHom (locallyFiniteChainComplex_X L₁ k).symm)]
  refine ModuleCat.hom_ext <| LinearMap.ext fun c ↦ P.twistedChainComplex_ext_coeff L₂ fun σ hσ ↦ ?_
  simp only [HomologicalComplex.comp_f, locallyFiniteChainComplexCoefficientMap_f, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearMap.comp_apply, P.twistedChainComplexCoeff_twistedChainComplexCoefficientMap_f_apply,
    P.twistedChainComplexCoeff_locallyFiniteChainComplexToRelative_f_apply,
    coe_locallyFiniteChainsCoefficientMap_apply]

/-- Pushing forward locally finite chains along a proper pair map commutes with relative classes. -/
@[reassoc] theorem locallyFiniteChainComplexMap_comp_locallyFiniteChainComplexToRelative
    {P Q : TopPair.{v}} (φ : P ⟶ Q) (hf : IsProperMap (Hom.fst φ).hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R Q.fst)
    (hP : IsCompact (Set.range P.map)ᶜ) (hQ : IsCompact (Set.range Q.map)ᶜ) :
    locallyFiniteChainComplexMap (Hom.fst φ) hf L ≫ Q.locallyFiniteChainComplexToRelative L hQ =
      P.locallyFiniteChainComplexToRelative
          ((LocalCoefficientSystem.pullback (Hom.fst φ).hom).obj L) hP ≫
        TopPair.twistedChainComplexMap φ L := by
  ext k : 1
  rw [← cancel_epi (eqToHom
    (locallyFiniteChainComplex_X ((LocalCoefficientSystem.pullback (Hom.fst φ).hom).obj L) k).symm)]
  refine ModuleCat.hom_ext <| LinearMap.ext fun c ↦ Q.twistedChainComplex_ext_coeff L fun ρ hρ ↦ ?_
  have hπ (a) := congrArg (fun g ↦ (g.f k).hom a)
    (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap φ L)
  simp only [HomologicalComplex.comp_f, locallyFiniteChainComplexMap_f,
    locallyFiniteChainComplexToRelative_f, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply] at hπ ⊢
  rw [Q.twistedChainComplexCoeff_locallyFiniteChainsToRelative, coe_locallyFiniteChainsMap_apply,
    locallyFiniteChainsToRelative_apply, toRelativeFun_eq, hπ,
    Q.twistedChainComplexCoeff_twistedChainComplexπ_f_apply, map_sum, map_sum]
  simp_rw [twistedChainComplexMap_f_ι_apply]
  refine finsum_eq_sum_of_support_subset _ fun σ hσ ↦ (Set.Finite.mem_toFinset _).2 ⟨?_, ?_⟩
  · exact fun h ↦ hσ (by dsimp only; erw [h, map_zero, map_zero])
  · obtain rfl : (TopCat.toSSet.map (Hom.fst φ)).app _ σ = ρ :=
      by_contra fun hne ↦ hσ (twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne L hne _)
    refine Set.inter_compl_nonempty_iff.2 fun hsub ↦ hρ fun _ ⟨t, ht⟩ ↦ ?_
    obtain ⟨u, hu⟩ := hsub ⟨t, rfl⟩
    exact ⟨Hom.snd φ u, (congrArg (fun g : P.snd ⟶ Q.fst ↦ g u) (Hom.w φ)).trans
      ((congrArg (Hom.fst φ) hu).trans ht)⟩

end ToRelative

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

section ComplTower

variable {X : TopCat.{v}}

section Basic
variable (L : LocalCoefficientSystem.{u, v, max v w} R X) (C : ℕ → Set X)
  (hC : ∀ n, C n ⊆ C (n + 1))

/-- The tower `C(X, X \ Cₙ; L)` of a monotone sequence `C : ℕ → Set X`. -/
@[expose] def complChainComplexTower : ComplexTower.{max v w} R (ComplexShape.down ℕ) :=
  Functor.ofOpSequence (X := fun n ↦ (TopPair.ofSubset (C n)ᶜ).twistedChainComplex L)
    fun n ↦ TopTriple.twistedChainComplexTotalToOuter
      (TopTriple.ofSubset (Set.compl_subset_compl.2 (hC n))) L
@[simp] lemma complChainComplexTower_map_succ (n : ℕ) :
    (complChainComplexTower L C hC).map (homOfLE (Nat.le_succ n)).op =
      TopTriple.twistedChainComplexTotalToOuter
        (TopTriple.ofSubset (Set.compl_subset_compl.2 (hC n))) L :=
  Functor.ofOpSequence_map_homOfLE_succ _ n
@[reassoc, simp] lemma twistedChainComplexπ_comp_complChainComplexTower_map {m n : ℕ}
    (f : op m ⟶ op n) :
    (TopPair.ofSubset (C m)ᶜ).twistedChainComplexπ L ≫ (complChainComplexTower L C hC).map f =
      (TopPair.ofSubset (C n)ᶜ).twistedChainComplexπ L := by
  induction m, leOfHom f.unop using Nat.le_induction with
  | base =>
    obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  | succ m hnm ih =>
    obtain rfl : f = (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op := Subsingleton.elim _ _
    erw [Functor.map_comp, ← Category.assoc, complChainComplexTower_map_succ,
      TopTriple.twistedChainComplexπ_comp_totalToOuter, ih]
/-- The transitions of `complChainComplexTower` are surjective in every degree. -/
lemma complChainComplexTower_transition_surjective (i n : ℕ) :
    Function.Surjective (((complChainComplexTower L C hC).term i).transition n) := by
  rw [ModuleTower.transition_def, Functor.comp_map, HomologicalComplex.eval_map]; intro y
  obtain ⟨a, rfl⟩ := (TopPair.ofSubset (C n)ᶜ).twistedChainComplexπ_f_surjective L y
  exact ⟨(((TopPair.ofSubset (C (n + 1))ᶜ).twistedChainComplexπ L).f i).hom a,
    congrArg (fun g ↦ (g.f i).hom a)
      (twistedChainComplexπ_comp_complChainComplexTower_map L C hC (homOfLE (Nat.le_succ n)).op)⟩
/-- `complChainComplexTower` has surjective shift maps in every degree. -/
lemma complChainComplexTower_shift_surjective (i : ℕ) :
    Function.Surjective ((complChainComplexTower L C hC).term i).shift :=
  ModuleTower.shift_surjective _ (complChainComplexTower_transition_surjective L C hC i)
/-- When each `C n` is compact, locally finite chains form a cone over `complChainComplexTower`. -/
@[expose] def locallyFiniteChainComplexComplCone (hK : ∀ n, IsCompact (C n)) :
    Cone (complChainComplexTower L C hC) where
  pt := locallyFiniteChainComplex L
  π := NatTrans.ofOpSequence
    (fun n ↦ (TopPair.ofSubset (C n)ᶜ).locallyFiniteChainComplexToRelative L
      (hK n).compl_range_ofSubset_compl_map)
    fun n ↦ by
      erw [Category.id_comp, complChainComplexTower_map_succ,
        TopTriple.locallyFiniteChainComplexToRelative_comp_twistedChainComplexTotalToOuter
          (hA := (hK n).compl_range_ofSubset_compl_map)]; rfl
/-- Canonical map from locally finite chains to `(complChainComplexTower L C hC).limComplex`. -/
def locallyFiniteChainComplexToComplLim (hK : ∀ n, IsCompact (C n)) :
    locallyFiniteChainComplex L ⟶ (complChainComplexTower L C hC).limComplex :=
  (complChainComplexTower L C hC).isLimitLimComplexCone.lift
    (locallyFiniteChainComplexComplCone L C hC hK)
@[reassoc (attr := simp)] lemma locallyFiniteChainComplexToComplLim_comp_π
    (hK : ∀ n, IsCompact (C n)) (n : ℕ) :
    locallyFiniteChainComplexToComplLim L C hC hK ≫
        (complChainComplexTower L C hC).limComplexπ n =
      (TopPair.ofSubset (C n)ᶜ).locallyFiniteChainComplexToRelative L
        (hK n).compl_range_ofSubset_compl_map :=
  (complChainComplexTower L C hC).isLimitLimComplexCone.fac _ (op n)
end Basic

section Helpers
variable {X₁ X₂ : TopCat.{v}} {L₁ : LocalCoefficientSystem.{u, v, max v w} R X₁}
  {L₂ : LocalCoefficientSystem.{u, v, max v w} R X₂}
  {C₁ : ℕ → Set X₁} {hC₁ : ∀ n, C₁ n ⊆ C₁ (n + 1)} {C₂ : ℕ → Set X₂} {hC₂ : ∀ n, C₂ n ⊆ C₂ (n + 1)}

private def mkComplTowerHom (app : ∀ n, (TopPair.ofSubset (C₁ n)ᶜ).twistedChainComplex L₁ ⟶
      (TopPair.ofSubset (C₂ n)ᶜ).twistedChainComplex L₂)
    (g : L₁.twistedChainComplex ⟶ L₂.twistedChainComplex)
    (h : ∀ n, (TopPair.ofSubset (C₁ n)ᶜ).twistedChainComplexπ L₁ ≫ app n =
      g ≫ (TopPair.ofSubset (C₂ n)ᶜ).twistedChainComplexπ L₂) :
    complChainComplexTower L₁ C₁ hC₁ ⟶ complChainComplexTower L₂ C₂ hC₂ where
  app n := app n.unop
  naturality {m n} f := (TopPair.ofSubset (C₁ m.unop)ᶜ).twistedChainComplex_hom_ext L₁ <| by
    erw [twistedChainComplexπ_comp_complChainComplexTower_map_assoc, h, ← Category.assoc, h,
      Category.assoc, twistedChainComplexπ_comp_complChainComplexTower_map]; rfl
private lemma complTower_hom_ext
    {α β : complChainComplexTower L₁ C₁ hC₁ ⟶ complChainComplexTower L₂ C₂ hC₂}
    (h : ∀ n, (TopPair.ofSubset (C₁ n)ᶜ).twistedChainComplexπ L₁ ≫ α.app (op n) =
      (TopPair.ofSubset (C₁ n)ᶜ).twistedChainComplexπ L₁ ≫ β.app (op n)) : α = β :=
  NatTrans.ext <| funext <| Opposite.rec fun n ↦
    (TopPair.ofSubset (C₁ n)ᶜ).twistedChainComplex_hom_ext L₁ (h n)
private lemma comp_toComplLim_eq {hK₁ : ∀ n, IsCompact (C₁ n)} {hK₂ : ∀ n, IsCompact (C₂ n)}
    (u : locallyFiniteChainComplex L₁ ⟶ locallyFiniteChainComplex L₂)
    (q : complChainComplexTower L₁ C₁ hC₁ ⟶ complChainComplexTower L₂ C₂ hC₂)
    (h : ∀ n, u ≫ (TopPair.ofSubset (C₂ n)ᶜ).locallyFiniteChainComplexToRelative L₂
        (hK₂ n).compl_range_ofSubset_compl_map =
      (TopPair.ofSubset (C₁ n)ᶜ).locallyFiniteChainComplexToRelative L₁
        (hK₁ n).compl_range_ofSubset_compl_map ≫ q.app (op n)) :
    u ≫ locallyFiniteChainComplexToComplLim L₂ C₂ hC₂ hK₂ =
      locallyFiniteChainComplexToComplLim L₁ C₁ hC₁ hK₁ ≫ ComplexTower.limComplexMap q :=
  (complChainComplexTower L₂ C₂ hC₂).limComplex_hom_ext fun n ↦ by
    erw [Category.assoc, locallyFiniteChainComplexToComplLim_comp_π, h, Category.assoc,
      ComplexTower.limComplexMap_comp_π, locallyFiniteChainComplexToComplLim_comp_π_assoc]; rfl
end Helpers

section TowerMap
variable (L : LocalCoefficientSystem.{u, v, max v w} R X) {C₁ C₂ : ℕ → Set X}
  (hC₁ : ∀ n, C₁ n ⊆ C₁ (n + 1)) (hC₂ : ∀ n, C₂ n ⊆ C₂ (n + 1))

/-- Enlarging `C₁ n ⊆ C₂ n` induces a quotient morphism of complement relative towers. -/
def complChainComplexTowerMap (h : ∀ n, C₁ n ⊆ C₂ n) :
    complChainComplexTower L C₂ hC₂ ⟶ complChainComplexTower L C₁ hC₁ :=
  mkComplTowerHom (fun n ↦
      (TopTriple.ofSubset (Set.compl_subset_compl.2 (h n))).twistedChainComplexTotalToOuter L)
    (𝟙 _) fun n ↦ by erw [TopTriple.twistedChainComplexπ_comp_totalToOuter, Category.id_comp]; rfl
@[simp] lemma complChainComplexTowerMap_app (h : ∀ n, C₁ n ⊆ C₂ n) (n : ℕ) :
    (complChainComplexTowerMap L hC₁ hC₂ h).app (op n) =
      (TopTriple.ofSubset (Set.compl_subset_compl.2 (h n))).twistedChainComplexTotalToOuter L :=
  (rfl)
@[reassoc] lemma twistedChainComplexπ_comp_complChainComplexTowerMap_app (h : ∀ n, C₁ n ⊆ C₂ n)
    (n : ℕ) :
    (TopPair.ofSubset (C₂ n)ᶜ).twistedChainComplexπ L ≫
        (complChainComplexTowerMap L hC₁ hC₂ h).app (op n) =
      (TopPair.ofSubset (C₁ n)ᶜ).twistedChainComplexπ L :=
  (TopTriple.ofSubset (Set.compl_subset_compl.2 (h n))).twistedChainComplexπ_comp_totalToOuter L
@[reassoc] lemma locallyFiniteChainComplexToRelative_comp_complChainComplexTowerMap_app
    (hK₁ : ∀ n, IsCompact (C₁ n)) (hK₂ : ∀ n, IsCompact (C₂ n)) (h : ∀ n, C₁ n ⊆ C₂ n) (n : ℕ) :
    (TopPair.ofSubset (C₂ n)ᶜ).locallyFiniteChainComplexToRelative L
        (hK₂ n).compl_range_ofSubset_compl_map ≫
        (complChainComplexTowerMap L hC₁ hC₂ h).app (op n) =
      (TopPair.ofSubset (C₁ n)ᶜ).locallyFiniteChainComplexToRelative L
        (hK₁ n).compl_range_ofSubset_compl_map :=
  TopTriple.locallyFiniteChainComplexToRelative_comp_twistedChainComplexTotalToOuter
    (TopTriple.ofSubset (Set.compl_subset_compl.2 (h n))) L
    (hK₂ n).compl_range_ofSubset_compl_map (hK₁ n).compl_range_ofSubset_compl_map
@[reassoc (attr := simp)] lemma locallyFiniteChainComplexToComplLim_comp_limComplexMap
    (hK₁ : ∀ n, IsCompact (C₁ n)) (hK₂ : ∀ n, IsCompact (C₂ n)) (h : ∀ n, C₁ n ⊆ C₂ n) :
    locallyFiniteChainComplexToComplLim L C₂ hC₂ hK₂ ≫
        ComplexTower.limComplexMap (complChainComplexTowerMap L hC₁ hC₂ h) =
      locallyFiniteChainComplexToComplLim L C₁ hC₁ hK₁ :=
  ((Category.id_comp _).symm.trans <| comp_toComplLim_eq (𝟙 _) _ fun n ↦ (Category.id_comp _).trans
    (locallyFiniteChainComplexToRelative_comp_complChainComplexTowerMap_app
      L hC₁ hC₂ hK₁ hK₂ h n).symm).symm
end TowerMap

@[simp] lemma complChainComplexTowerMap_refl (L : LocalCoefficientSystem.{u, v, max v w} R X)
    (C : ℕ → Set X) (hC : ∀ n, C n ⊆ C (n + 1)) :
    complChainComplexTowerMap L hC hC (fun n ↦ Set.Subset.refl (C n)) = 𝟙 _ :=
  complTower_hom_ext fun n ↦ by
    erw [twistedChainComplexπ_comp_complChainComplexTowerMap_app, Category.comp_id]
@[reassoc (attr := simp)] lemma complChainComplexTowerMap_comp
    (L : LocalCoefficientSystem.{u, v, max v w} R X) {C₁ C₂ C₃ : ℕ → Set X}
    (hC₁ : ∀ n, C₁ n ⊆ C₁ (n + 1)) (hC₂ : ∀ n, C₂ n ⊆ C₂ (n + 1)) (hC₃ : ∀ n, C₃ n ⊆ C₃ (n + 1))
    (h : ∀ n, C₁ n ⊆ C₂ n) (h' : ∀ n, C₂ n ⊆ C₃ n) :
    complChainComplexTowerMap L hC₂ hC₃ h' ≫ complChainComplexTowerMap L hC₁ hC₂ h =
      complChainComplexTowerMap L hC₁ hC₃ (fun n ↦ (h n).trans (h' n)) :=
  complTower_hom_ext fun n ↦ by
    erw [NatTrans.comp_app, twistedChainComplexπ_comp_complChainComplexTowerMap_app_assoc,
      twistedChainComplexπ_comp_complChainComplexTowerMap_app,
      twistedChainComplexπ_comp_complChainComplexTowerMap_app]

section CoeffMap
variable (C : ℕ → Set X) (hC : ∀ n, C n ⊆ C (n + 1))
  {L₁ L₂ : LocalCoefficientSystem.{u, v, max v w} R X} (η : L₁ ⟶ L₂)

/-- A morphism of local coefficient systems induces a morphism of complement relative towers. -/
def complChainComplexTowerCoefficientMap :
    complChainComplexTower L₁ C hC ⟶ complChainComplexTower L₂ C hC :=
  mkComplTowerHom (fun n ↦ (TopPair.ofSubset (C n)ᶜ).twistedChainComplexCoefficientMap η)
    (twistedChainComplexCoefficientMap η) fun n ↦
      (TopPair.ofSubset (C n)ᶜ).twistedChainComplexπ_comp_twistedChainComplexCoefficientMap η
@[simp] lemma complChainComplexTowerCoefficientMap_app (n : ℕ) :
    (complChainComplexTowerCoefficientMap C hC η).app (op n) =
      (TopPair.ofSubset (C n)ᶜ).twistedChainComplexCoefficientMap η := (rfl)
@[reassoc] lemma locallyFiniteChainComplexCoefficientMap_comp_toComplLim
    (hK : ∀ n, IsCompact (C n)) :
    locallyFiniteChainComplexCoefficientMap η ≫ locallyFiniteChainComplexToComplLim L₂ C hC hK =
      locallyFiniteChainComplexToComplLim L₁ C hC hK ≫
        ComplexTower.limComplexMap (complChainComplexTowerCoefficientMap C hC η) :=
  comp_toComplLim_eq _ _ fun n ↦
    ((TopPair.ofSubset (C n)ᶜ).locallyFiniteChainComplexToRelative_naturality _ η).symm
end CoeffMap

section PairMap
variable {Y : TopCat.{v}} (f : X ⟶ Y)
private lemma π_comp_eqToHom_pairMap {f : X ⟶ Y} {L : LocalCoefficientSystem.{u, v, max v w} R Y}
    {A : Set X} {B : Set Y} (φ : TopPair.ofSubset A ⟶ TopPair.ofSubset B)
    (hφ : TopPair.Hom.fst φ = f) :
    (TopPair.ofSubset A).twistedChainComplexπ ((pullback f.hom).obj L) ≫
        eqToHom (by rw [hφ]; rfl) ≫ TopPair.twistedChainComplexMap φ L =
      twistedChainComplexMap f L ≫ (TopPair.ofSubset B).twistedChainComplexπ L := by
  cases hφ; erw [eqToHom_refl, Category.id_comp]
  exact TopPair.twistedChainComplexπ_comp_twistedChainComplexMap φ L
section Fixed
variable (L : LocalCoefficientSystem.{u, v, max v w} R Y) {C_X : ℕ → Set X}
  (hC_X : ∀ n, C_X n ⊆ C_X (n + 1)) {C_Y : ℕ → Set Y} (hC_Y : ∀ n, C_Y n ⊆ C_Y (n + 1))
  (hf : ∀ n, Set.MapsTo f (C_X n)ᶜ (C_Y n)ᶜ)
/-- A continuous map `f : X ⟶ Y` carrying `(C_X n)ᶜ` into `(C_Y n)ᶜ` induces a tower morphism. -/
def complChainComplexTowerPairMap :
    complChainComplexTower ((pullback f.hom).obj L) C_X hC_X ⟶
      complChainComplexTower L C_Y hC_Y :=
  mkComplTowerHom (fun n ↦ eqToHom (by rw [TopPair.ofSubsetMap_fst]; rfl) ≫
      TopPair.twistedChainComplexMap (TopPair.ofSubsetMap f (hf n)) L)
    (twistedChainComplexMap f L) fun n ↦ π_comp_eqToHom_pairMap _ (TopPair.ofSubsetMap_fst f (hf n))
@[simp] lemma complChainComplexTowerPairMap_app (n : ℕ) :
    (complChainComplexTowerPairMap f L hC_X hC_Y hf).app (op n) =
      eqToHom (by rw [TopPair.ofSubsetMap_fst]; rfl) ≫
        TopPair.twistedChainComplexMap (TopPair.ofSubsetMap f (hf n)) L := (rfl)
@[reassoc] lemma twistedChainComplexπ_comp_complChainComplexTowerPairMap_app (n : ℕ) :
    (TopPair.ofSubset (C_X n)ᶜ).twistedChainComplexπ ((pullback f.hom).obj L) ≫
        (complChainComplexTowerPairMap f L hC_X hC_Y hf).app (op n) =
      twistedChainComplexMap f L ≫ (TopPair.ofSubset (C_Y n)ᶜ).twistedChainComplexπ L :=
  π_comp_eqToHom_pairMap _ (TopPair.ofSubsetMap_fst f (hf n))
end Fixed
/-- Enlarging both monotone sequences commutes with `complChainComplexTowerPairMap`. -/
@[reassoc] lemma complChainComplexTowerMap_comp_complChainComplexTowerPairMap
    (L : LocalCoefficientSystem.{u, v, max v w} R Y) {C_X C_X' : ℕ → Set X}
    (hC_X : ∀ n, C_X n ⊆ C_X (n + 1)) (hC_X' : ∀ n, C_X' n ⊆ C_X' (n + 1)) {C_Y C_Y' : ℕ → Set Y}
    (hC_Y : ∀ n, C_Y n ⊆ C_Y (n + 1)) (hC_Y' : ∀ n, C_Y' n ⊆ C_Y' (n + 1))
    (hf : ∀ n, Set.MapsTo f (C_X n)ᶜ (C_Y n)ᶜ) (hf' : ∀ n, Set.MapsTo f (C_X' n)ᶜ (C_Y' n)ᶜ)
    (hX : ∀ n, C_X n ⊆ C_X' n) (hY : ∀ n, C_Y n ⊆ C_Y' n) :
    complChainComplexTowerMap ((pullback f.hom).obj L) hC_X hC_X' hX ≫
        complChainComplexTowerPairMap f L hC_X hC_Y hf =
      complChainComplexTowerPairMap f L hC_X' hC_Y' hf' ≫
        complChainComplexTowerMap L hC_Y hC_Y' hY :=
  complTower_hom_ext fun n ↦ (CommSq.vert_comp
      ⟨(twistedChainComplexπ_comp_complChainComplexTowerMap_app _ hC_X hC_X' hX n).trans
        (Category.id_comp _).symm⟩
      ⟨twistedChainComplexπ_comp_complChainComplexTowerPairMap_app f L hC_X hC_Y hf n⟩).w.trans <|
    (congrArg (· ≫ _) ((Category.id_comp _).trans (Category.comp_id _).symm)).trans
      (CommSq.vert_comp
        ⟨twistedChainComplexπ_comp_complChainComplexTowerPairMap_app f L hC_X' hC_Y' hf' n⟩
        ⟨(twistedChainComplexπ_comp_complChainComplexTowerMap_app L hC_Y hC_Y' hY n).trans
          (Category.id_comp _).symm⟩).w.symm
/-- `complChainComplexTowerPairMap` is natural in the local coefficient system. -/
@[reassoc] lemma complChainComplexTowerPairMap_naturality
    {L₁ L₂ : LocalCoefficientSystem.{u, v, max v w} R Y} (η : L₁ ⟶ L₂) {C_X : ℕ → Set X}
    (hC_X : ∀ n, C_X n ⊆ C_X (n + 1)) {C_Y : ℕ → Set Y} (hC_Y : ∀ n, C_Y n ⊆ C_Y (n + 1))
    (hf : ∀ n, Set.MapsTo f (C_X n)ᶜ (C_Y n)ᶜ) :
    complChainComplexTowerPairMap f L₁ hC_X hC_Y hf ≫
        complChainComplexTowerCoefficientMap C_Y hC_Y η =
      complChainComplexTowerCoefficientMap C_X hC_X ((pullback f.hom).map η) ≫
        complChainComplexTowerPairMap f L₂ hC_X hC_Y hf :=
  complTower_hom_ext fun n ↦ (CommSq.vert_comp
      ⟨twistedChainComplexπ_comp_complChainComplexTowerPairMap_app f L₁ hC_X hC_Y hf n⟩
      ⟨(TopPair.ofSubset _).twistedChainComplexπ_comp_twistedChainComplexCoefficientMap η⟩).w.trans
    <| (congrArg (· ≫ _) (twistedChainComplexMap_naturality f η)).trans (CommSq.vert_comp
      ⟨(TopPair.ofSubset _).twistedChainComplexπ_comp_twistedChainComplexCoefficientMap _⟩
      ⟨twistedChainComplexπ_comp_complChainComplexTowerPairMap_app f L₂ hC_X hC_Y hf n⟩).w.symm
/-- Proper pushforward commutes with `locallyFiniteChainComplexToComplLim`. -/
@[reassoc] lemma locallyFiniteChainComplexMap_comp_toComplLim (hf_proper : IsProperMap f.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R Y) {C_X : ℕ → Set X}
    (hC_X : ∀ n, C_X n ⊆ C_X (n + 1)) (hK_X : ∀ n, IsCompact (C_X n)) {C_Y : ℕ → Set Y}
    (hC_Y : ∀ n, C_Y n ⊆ C_Y (n + 1)) (hK_Y : ∀ n, IsCompact (C_Y n))
    (hf : ∀ n, Set.MapsTo f (C_X n)ᶜ (C_Y n)ᶜ) :
    locallyFiniteChainComplexMap f hf_proper L ≫
        locallyFiniteChainComplexToComplLim L C_Y hC_Y hK_Y =
      locallyFiniteChainComplexToComplLim ((pullback f.hom).obj L) C_X hC_X hK_X ≫
        ComplexTower.limComplexMap (complChainComplexTowerPairMap f L hC_X hC_Y hf) :=
  comp_toComplLim_eq _ _ fun n ↦
    have aux {g : X ⟶ Y} (φ : TopPair.ofSubset (C_X n)ᶜ ⟶ TopPair.ofSubset (C_Y n)ᶜ)
        (hφ : TopPair.Hom.fst φ = g) (hg : IsProperMap g.hom) :
        locallyFiniteChainComplexMap g hg L ≫
            (TopPair.ofSubset _).locallyFiniteChainComplexToRelative L _ =
          (TopPair.ofSubset _).locallyFiniteChainComplexToRelative ((pullback g.hom).obj L) _ ≫
            eqToHom (by rw [hφ]; rfl) ≫ TopPair.twistedChainComplexMap φ L := by
      cases hφ; erw [eqToHom_refl, Category.id_comp]
      exact TopPair.locallyFiniteChainComplexMap_comp_locallyFiniteChainComplexToRelative φ hg L _ _
    aux (TopPair.ofSubsetMap f (hf n)) (TopPair.ofSubsetMap_fst f (hf n)) hf_proper
end PairMap

/-- Composition law for `complChainComplexTowerPairMap`. -/
@[reassoc] lemma complChainComplexTowerPairMap_comp {Y Z : TopCat.{v}} (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z)
    (L : LocalCoefficientSystem.{u, v, max v w} R Z) {C_X : ℕ → Set X}
    (hC_X : ∀ n, C_X n ⊆ C_X (n + 1)) {C_Y : ℕ → Set Y} (hC_Y : ∀ n, C_Y n ⊆ C_Y (n + 1))
    {C_Z : ℕ → Set Z} (hC_Z : ∀ n, C_Z n ⊆ C_Z (n + 1))
    (hf₁ : ∀ n, Set.MapsTo f₁ (C_X n)ᶜ (C_Y n)ᶜ) (hf₂ : ∀ n, Set.MapsTo f₂ (C_Y n)ᶜ (C_Z n)ᶜ)
    (hf₁₂ : ∀ n, Set.MapsTo (f₁ ≫ f₂) (C_X n)ᶜ (C_Z n)ᶜ) :
    complChainComplexTowerPairMap (f₁ ≫ f₂) L hC_X hC_Z hf₁₂ =
      complChainComplexTowerCoefficientMap C_X hC_X ((pullbackCompIso f₁.hom f₂.hom).hom.app L) ≫
        complChainComplexTowerPairMap f₁ ((pullback f₂.hom).obj L) hC_X hC_Y hf₁ ≫
          complChainComplexTowerPairMap f₂ L hC_Y hC_Z hf₂ :=
  complTower_hom_ext fun n ↦
    (twistedChainComplexπ_comp_complChainComplexTowerPairMap_app _ L hC_X hC_Z hf₁₂ n).trans <|
    (congrArg (· ≫ _) (twistedChainComplexMap_comp f₁ f₂ L)).trans <| (CommSq.vert_comp
      ⟨(TopPair.ofSubset _).twistedChainComplexπ_comp_twistedChainComplexCoefficientMap _⟩
      ⟨(CommSq.vert_comp
        ⟨twistedChainComplexπ_comp_complChainComplexTowerPairMap_app f₁ _ hC_X hC_Y hf₁ n⟩
        ⟨twistedChainComplexπ_comp_complChainComplexTowerPairMap_app f₂ L hC_Y hC_Z hf₂ n⟩
      ).w⟩).w.symm

/-- Naturality square for `complChainComplexTowerPairMap`. -/
@[reassoc] lemma complChainComplexTowerPairMap_naturality_square {A B C' D : TopCat.{v}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C') (d : C' ⟶ D)
    (L : LocalCoefficientSystem.{u, v, max v w} R D) (h : a ≫ b = c ≫ d) {C_A : ℕ → Set A}
    (hC_A : ∀ n, C_A n ⊆ C_A (n + 1)) {C_B : ℕ → Set B} (hC_B : ∀ n, C_B n ⊆ C_B (n + 1))
    {C_C : ℕ → Set C'} (hC_C : ∀ n, C_C n ⊆ C_C (n + 1)) {C_D : ℕ → Set D}
    (hC_D : ∀ n, C_D n ⊆ C_D (n + 1)) (ha : ∀ n, Set.MapsTo a (C_A n)ᶜ (C_B n)ᶜ)
    (hb : ∀ n, Set.MapsTo b (C_B n)ᶜ (C_D n)ᶜ) (hc : ∀ n, Set.MapsTo c (C_A n)ᶜ (C_C n)ᶜ)
    (hd : ∀ n, Set.MapsTo d (C_C n)ᶜ (C_D n)ᶜ) :
    complChainComplexTowerPairMap a ((pullback b.hom).obj L) hC_A hC_B ha ≫
        complChainComplexTowerPairMap b L hC_B hC_D hb =
      complChainComplexTowerCoefficientMap C_A hC_A
          (((pullbackCompIso a.hom b.hom).app L).symm ≪≫
            eqToIso (congrArg (fun k : A ⟶ D ↦ (pullback k.hom).obj L) h) ≪≫
            (pullbackCompIso c.hom d.hom).app L).hom ≫
        complChainComplexTowerPairMap c ((pullback d.hom).obj L) hC_A hC_C hc ≫
          complChainComplexTowerPairMap d L hC_C hC_D hd :=
  complTower_hom_ext fun n ↦ (CommSq.vert_comp
      ⟨twistedChainComplexπ_comp_complChainComplexTowerPairMap_app a _ hC_A hC_B ha n⟩
      ⟨twistedChainComplexπ_comp_complChainComplexTowerPairMap_app b L hC_B hC_D hb n⟩).w.trans <|
    (congrArg (· ≫ _) (twistedChainComplexMap_naturality_square a b c d L h)).trans <|
    (CommSq.vert_comp
      ⟨(TopPair.ofSubset _).twistedChainComplexπ_comp_twistedChainComplexCoefficientMap _⟩
      ⟨(CommSq.vert_comp
        ⟨twistedChainComplexπ_comp_complChainComplexTowerPairMap_app c _ hC_A hC_C hc n⟩
        ⟨twistedChainComplexπ_comp_complChainComplexTowerPairMap_app d L hC_C hC_D hd n⟩
      ).w⟩).w.symm

end ComplTower

section Tower

/-
The ambient space of the pair `TopPair.ofSubset A` is only definitionally `X`, not reducibly, and
the terms of the tower below are only definitionally relative chain complexes. Goals mixing these
typings cannot be rewritten, so the limit argument goes through the coefficients
`towerCoeff` of the terms of the tower, whose characterizing lemmas are assembled as terms.
-/

variable {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, max v w} R X) (K : CompactExhaustion X)
  {k : ℕ}

/-- The tower of relative twisted chain complexes `C(X, X \ Kₙ; L)` of a compact exhaustion `K` of
`X`, whose transitions are the quotient maps `C(X, X \ Kₙ₊₁; L) ⟶ C(X, X \ Kₙ; L)`. -/
-- The body is exposed so that the terms of the tower are the relative chain complexes, which the
-- statements identifying the cone legs and the Milnor maps below need in order to typecheck.
@[expose]
def relativeChainComplexTower : ComplexTower.{max v w} R (ComplexShape.down ℕ) :=
  complChainComplexTower L K K.subset_succ

/-- The terms of the tower of a compact exhaustion are the relative twisted chain complexes. -/
lemma relativeChainComplexTower_obj (n : ℕ) :
    (relativeChainComplexTower L K).obj (op n) =
      (TopPair.ofSubset (K n)ᶜ).twistedChainComplex L :=
  (rfl)

/-- The transitions of the tower of a compact exhaustion are the quotient maps. -/
@[simp]
lemma relativeChainComplexTower_map_succ (n : ℕ) :
    (relativeChainComplexTower L K).map (homOfLE (Nat.le_succ n)).op =
      TopTriple.twistedChainComplexTotalToOuter
        (TopTriple.ofSubset (Set.compl_subset_compl.2 (K.subset_succ n))) L :=
  complChainComplexTower_map_succ L K K.subset_succ n

/-- Every map of the tower of a compact exhaustion is induced by the identity of the ambient
twisted chains. -/
@[reassoc, simp]
lemma twistedChainComplexπ_comp_relativeChainComplexTower_map {m n : ℕ} (f : op m ⟶ op n) :
    (TopPair.ofSubset (K m)ᶜ).twistedChainComplexπ L ≫ (relativeChainComplexTower L K).map f =
      (TopPair.ofSubset (K n)ᶜ).twistedChainComplexπ L :=
  twistedChainComplexπ_comp_complChainComplexTower_map L K K.subset_succ f

/-- The transitions of the tower of a compact exhaustion are surjective in every degree. -/
lemma relativeChainComplexTower_transition_surjective (i n : ℕ) :
    Function.Surjective (((relativeChainComplexTower L K).term i).transition n) :=
  complChainComplexTower_transition_surjective L K K.subset_succ i n

/-- The tower of a compact exhaustion has surjective shift maps in every degree, so its `lim¹`
vanishes and the Milnor sequence applies to it. -/
lemma relativeChainComplexTower_shift_surjective (i : ℕ) :
    Function.Surjective ((relativeChainComplexTower L K).term i).shift :=
  complChainComplexTower_shift_surjective L K K.subset_succ i

/-- The coefficient on a simplex meeting `Kₙ` of a chain in the `n`-th term of the tower. -/
private def towerCoeff (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋k⦌)
    (hσ : (Set.range (TopCat.simplexMap σ) ∩ K n).Nonempty) :
    ((relativeChainComplexTower L K).obj (op n)).X k ⟶ L.obj (initialVertex σ) :=
  (TopPair.ofSubset (K n)ᶜ).twistedChainComplexCoeff L σ
    (TopPair.not_range_simplexMap_subset_range_ofSubset_compl_map_iff.2 hσ)

/-- A chain in a term of the tower is determined by its coefficients. -/
private lemma towerCoeff_ext {n : ℕ} {y y' : ((relativeChainComplexTower L K).obj (op n)).X k}
    (h : ∀ σ hσ, (towerCoeff L K n σ hσ).hom y = (towerCoeff L K n σ hσ).hom y') : y = y' :=
  (TopPair.ofSubset (K n)ᶜ).twistedChainComplex_ext_coeff L fun σ hσ ↦
    h σ (TopPair.not_range_simplexMap_subset_range_ofSubset_compl_map_iff.1 hσ)

/-- The coefficients of a chain in a term of the tower are those of an ambient twisted chain. -/
private lemma exists_towerCoeff_eq {n : ℕ} (y : ((relativeChainComplexTower L K).obj (op n)).X k) :
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
    (y : ((relativeChainComplexTower L K).obj (op m)).X k) :
    (towerCoeff L K n σ hn).hom ((((relativeChainComplexTower L K).map f).f k).hom y) =
      (towerCoeff L K m σ hm).hom y := by
  obtain ⟨a, rfl⟩ := (TopPair.ofSubset (K m)ᶜ).twistedChainComplexπ_f_surjective L y
  exact (congrArg _ (congrArg (fun g ↦ (g.f k).hom a)
    (twistedChainComplexπ_comp_relativeChainComplexTower_map L K f))).trans
    (((TopPair.ofSubset (K n)ᶜ).twistedChainComplexCoeff_twistedChainComplexπ_f_apply L σ _
      a).trans ((TopPair.ofSubset (K m)ᶜ).twistedChainComplexCoeff_twistedChainComplexπ_f_apply L
        σ _ a).symm)

/-- The relative class of a locally finite chain in the `n`-th term of the tower. -/
private abbrev toTower (n : ℕ) :
    locallyFiniteChainComplex L ⟶ (relativeChainComplexTower L K).obj (op n) :=
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

/-- The locally finite chain complex, with the chain maps to the relative twisted chains of the
pairs `(X, X \ Kₙ)`, as a cone over the tower of a compact exhaustion. -/
-- The body is exposed so that the point and legs of the cone are visible to its consumers.
@[expose]
def locallyFiniteChainComplexCone : Cone (relativeChainComplexTower L K) :=
  locallyFiniteChainComplexComplCone L K K.subset_succ K.isCompact

/-- The point of the cone of a compact exhaustion is the locally finite chain complex. -/
@[simp]
lemma locallyFiniteChainComplexCone_pt :
    (locallyFiniteChainComplexCone L K).pt = locallyFiniteChainComplex L :=
  (rfl)

/-- The legs of the cone of a compact exhaustion take relative classes. -/
@[simp]
lemma locallyFiniteChainComplexCone_π_app (n : ℕ) :
    (locallyFiniteChainComplexCone L K).π.app (op n) =
      (TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative L
        (K.isCompact n).compl_range_ofSubset_compl_map :=
  (rfl)

/-- The relative classes of a locally finite chain for the sets of a compact exhaustion are
compatible with the maps of the tower. -/
@[reassoc, simp]
lemma locallyFiniteChainComplexToRelative_comp_relativeChainComplexTower_map {m n : ℕ}
    (f : op m ⟶ op n) :
    (TopPair.ofSubset (K m)ᶜ).locallyFiniteChainComplexToRelative L
        (K.isCompact m).compl_range_ofSubset_compl_map ≫ (relativeChainComplexTower L K).map f =
      (TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative L
        (K.isCompact n).compl_range_ofSubset_compl_map :=
  (locallyFiniteChainComplexCone L K).w f

/-- The degree-`k` component of the map from locally finite chains to the limit of the tower,
precomposed with the identification of its source with the module of locally finite chains. -/
private abbrev toLim (k : ℕ) : ModuleCat.of R (locallyFiniteChains L k) ⟶
    (relativeChainComplexTower L K).limComplex.X k :=
  eqToHom (locallyFiniteChainComplex_X L k).symm ≫
    ((relativeChainComplexTower L K).isLimitLimComplexCone.lift
      (locallyFiniteChainComplexCone L K)).f k

private lemma limπ_toLim_apply (n : ℕ) (c : locallyFiniteChains L k) :
    ((relativeChainComplexTower L K).term k).limπ n ((toLim L K k).hom c) =
      ((toTower L K n).f k).hom ((eqToHom (locallyFiniteChainComplex_X L k).symm).hom c) := by
  have h := congrArg (fun φ : locallyFiniteChainComplex L ⟶
      (relativeChainComplexTower L K).obj (op n) ↦
        (φ.f k).hom ((eqToHom (locallyFiniteChainComplex_X L k).symm).hom c))
    ((relativeChainComplexTower L K).isLimitLimComplexCone.fac
      (locallyFiniteChainComplexCone L K) (op n))
  rw [← ComplexTower.limComplexπ_f_hom]
  -- `h` is the goal up to definitional unfolding: the leg of `limComplexCone` at `n` is
  -- `limComplexπ n` (`ComplexTower.limComplexCone_π_app`), the leg of
  -- `locallyFiniteChainComplexCone` at `n` is `toTower n`, and the component of a composite of
  -- chain maps applied to an element is the composite application.
  exact h

/-- A point of the limit of the tower has the same coefficient on a simplex `σ` in every term
with `σ` meeting the corresponding compact set. -/
private lemma towerCoeff_limπ_eq_of_le (x : ((relativeChainComplexTower L K).term k).lim)
    (σ : (TopCat.toSSet.obj X) _⦋k⦌) {m n : ℕ} (hnm : n ≤ m)
    (hn : (Set.range (TopCat.simplexMap σ) ∩ K n).Nonempty)
    (hm : (Set.range (TopCat.simplexMap σ) ∩ K m).Nonempty) :
    (towerCoeff L K n σ hn).hom (((relativeChainComplexTower L K).term k).limπ n x) =
      (towerCoeff L K m σ hm).hom (((relativeChainComplexTower L K).term k).limπ m x) := by
  have hx : ((relativeChainComplexTower L K).term k).limπ n x =
      (((relativeChainComplexTower L K).map (homOfLE hnm).op).f k).hom
        (((relativeChainComplexTower L K).term k).limπ m x) := by
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
  have hc (x : ((relativeChainComplexTower L K).term k).lim) (n : ℕ) (σ)
      (hσ : (Set.range (TopCat.simplexMap σ) ∩ K n).Nonempty) :
      (towerCoeff L K n σ hσ).hom (((relativeChainComplexTower L K).term k).limπ n x) =
        (towerCoeff L K (N σ) σ (hN σ)).hom
          (((relativeChainComplexTower L K).term k).limπ (N σ) x) :=
    (towerCoeff_limπ_eq_of_le L K x σ (le_max_left n (N σ)) hσ
      (hσ.mono (Set.inter_subset_inter_right _ (K.subset (le_max_left _ _))))).trans
    (towerCoeff_limπ_eq_of_le L K x σ (le_max_right n (N σ)) (hN σ) _).symm
  refine ⟨fun c c' h ↦ Subtype.ext <| funext fun σ ↦ ?_, fun x ↦ ?_⟩
  · have h' := congrArg (fun y ↦ (towerCoeff L K (N σ) σ (hN σ)).hom
      (((relativeChainComplexTower L K).term k).limπ (N σ) y)) h
    dsimp only at h'
    rwa [limπ_toLim_apply, limπ_toLim_apply, towerCoeff_toTower, towerCoeff_toTower] at h'
  let c (σ : (TopCat.toSSet.obj X) _⦋k⦌) : L.obj (initialVertex σ) :=
    (towerCoeff L K (N σ) σ (hN σ)).hom (((relativeChainComplexTower L K).term k).limπ (N σ) x)
  -- Near a point, the coefficients are those of a single finite ambient chain.
  have hlf : c ∈ locallyFiniteChains L k := by
    refine mem_locallyFiniteChains.2 <| isLocallyFiniteChain_iff.2 fun p ↦ ?_
    obtain ⟨n, hn⟩ := K.exists_mem_nhds p
    obtain ⟨a, ha⟩ := exists_towerCoeff_eq L K (((relativeChainComplexTower L K).term k).limπ n x)
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
    IsIso ((relativeChainComplexTower L K).isLimitLimComplexCone.lift
      (locallyFiniteChainComplexCone L K)) := by
  have (k : ℕ) : IsIso (((relativeChainComplexTower L K).isLimitLimComplexCone.lift
      (locallyFiniteChainComplexCone L K)).f k) :=
    (ConcreteCategory.isIso_iff_bijective _).2 <| (Function.Bijective.of_comp_iff _
      (ConcreteCategory.bijective_of_isIso
        (eqToHom (locallyFiniteChainComplex_X L k).symm))).1 (bijective_toLim L K)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **Locally finite chains form the inverse limit of relative chains.** For a compact exhaustion
`K` of `X`, the locally finite chain complex, with the maps sending a locally finite chain to the
class of its part on the simplices meeting `Kₙ`, is the limit of the tower of relative twisted
chain complexes `C(X, X \ Kₙ; L)`. -/
def isLimitLocallyFiniteChainComplexCone : IsLimit (locallyFiniteChainComplexCone L K) :=
  IsLimit.ofPointIso (relativeChainComplexTower L K).isLimitLimComplexCone

end Tower

section Milnor

variable {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, max v w} R X) (K : CompactExhaustion X)

/-- The isomorphism from the locally finite chain complex to the limit complex of the tower of a
compact exhaustion, whose components are the relative classes of locally finite chains
(`TauCeti.LocalCoefficientSystem.locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexπ`). -/
def locallyFiniteChainComplexIsoLimComplex :
    locallyFiniteChainComplex L ≅ (relativeChainComplexTower L K).limComplex :=
  (isLimitLocallyFiniteChainComplexCone L K).conePointUniqueUpToIso
    (relativeChainComplexTower L K).isLimitLimComplexCone

/-- The components of the isomorphism to the limit complex are the relative classes. -/
@[reassoc (attr := simp)]
lemma locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexπ (n : ℕ) :
    (locallyFiniteChainComplexIsoLimComplex L K).hom ≫
        (relativeChainComplexTower L K).limComplexπ n =
      (TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative L
        (K.isCompact n).compl_range_ofSubset_compl_map :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (op n)

lemma locallyFiniteChainComplexIsoLimComplex_hom_eq_toComplLim :
    (locallyFiniteChainComplexIsoLimComplex L K).hom =
      locallyFiniteChainComplexToComplLim L K K.subset_succ K.isCompact :=
  (relativeChainComplexTower L K).limComplex_hom_ext fun n ↦
    (locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexπ L K n).trans
      (locallyFiniteChainComplexToComplLim_comp_π L K K.subset_succ K.isCompact n).symm
@[reassoc (attr := simp)] lemma locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexMap_compl
    {C : ℕ → Set X} (hC : ∀ n, C n ⊆ C (n + 1)) (hK : ∀ n, IsCompact (C n)) (h : ∀ n, C n ⊆ K n) :
    (locallyFiniteChainComplexIsoLimComplex L K).hom ≫
        ComplexTower.limComplexMap (complChainComplexTowerMap L hC K.subset_succ h) =
      locallyFiniteChainComplexToComplLim L C hC hK := by
  rw [locallyFiniteChainComplexIsoLimComplex_hom_eq_toComplLim]
  exact locallyFiniteChainComplexToComplLim_comp_limComplexMap L hC K.subset_succ hK K.isCompact h
/-- Proper pushforward commutes with `locallyFiniteChainComplexIsoLimComplex`. -/
@[reassoc] lemma locallyFiniteChainComplexMap_comp_isoLimComplex_hom {Y : TopCat.{v}} (f : X ⟶ Y)
    (hf_proper : IsProperMap f.hom) (L : LocalCoefficientSystem.{u, v, max v w} R Y)
    (K_X : CompactExhaustion X) (K_Y : CompactExhaustion Y)
    (hf : ∀ n, Set.MapsTo f (K_X n)ᶜ (K_Y n)ᶜ) :
    locallyFiniteChainComplexMap f hf_proper L ≫
        (locallyFiniteChainComplexIsoLimComplex L K_Y).hom =
      (locallyFiniteChainComplexIsoLimComplex ((pullback f.hom).obj L) K_X).hom ≫
        ComplexTower.limComplexMap
          (complChainComplexTowerPairMap f L K_X.subset_succ K_Y.subset_succ hf) := by
  simp only [locallyFiniteChainComplexIsoLimComplex_hom_eq_toComplLim]
  exact locallyFiniteChainComplexMap_comp_toComplLim f hf_proper L _ _ _ _ hf
/-- Morphism of relative chain towers induced by a morphism of local coefficient systems. -/
abbrev relativeChainComplexTowerCoefficientMap
    {L₁ L₂ : LocalCoefficientSystem.{u, v, max v w} R X} (η : L₁ ⟶ L₂) :
    relativeChainComplexTower L₁ K ⟶ relativeChainComplexTower L₂ K :=
  complChainComplexTowerCoefficientMap K K.subset_succ η
/-- `locallyFiniteChainComplexIsoLimComplex` is natural in the local coefficient system. -/
@[reassoc] theorem locallyFiniteChainComplexCoefficientMap_comp_isoLimComplex_hom
    {L₁ L₂ : LocalCoefficientSystem.{u, v, max v w} R X} (η : L₁ ⟶ L₂) :
    locallyFiniteChainComplexCoefficientMap η ≫ (locallyFiniteChainComplexIsoLimComplex L₂ K).hom =
      (locallyFiniteChainComplexIsoLimComplex L₁ K).hom ≫
        ComplexTower.limComplexMap (relativeChainComplexTowerCoefficientMap K η) := by
  simp only [locallyFiniteChainComplexIsoLimComplex_hom_eq_toComplLim]
  exact locallyFiniteChainComplexCoefficientMap_comp_toComplLim K K.subset_succ η K.isCompact

/-- The map from Borel–Moore homology to the limit of the relative twisted homology modules
`H_j(X, X \ Kₙ; L)` of a compact exhaustion, whose components are induced by the relative classes
of locally finite chains (`TauCeti.LocalCoefficientSystem.limπ_borelMooreHomologyToLim`). -/
def borelMooreHomologyToLim (j : ℕ) :
    borelMooreHomology L j →ₗ[R] ((relativeChainComplexTower L K).homology j).lim :=
  (relativeChainComplexTower L K).homologyToLim j ∘ₗ
    (HomologicalComplex.homologyMap (locallyFiniteChainComplexIsoLimComplex L K).hom j).hom

/-- The map from Borel–Moore homology to the limit of relative homology is the map of the tower
of complexes to the limit of its homology, after identifying locally finite chains with the limit
complex. -/
lemma borelMooreHomologyToLim_def (j : ℕ) :
    borelMooreHomologyToLim L K j = (relativeChainComplexTower L K).homologyToLim j ∘ₗ
      (HomologicalComplex.homologyMap (locallyFiniteChainComplexIsoLimComplex L K).hom j).hom :=
  (rfl)

/-- The components of the map from Borel–Moore homology to the limit of relative homology are the
maps induced by the relative classes of locally finite chains. -/
lemma limπ_borelMooreHomologyToLim (j n : ℕ) (x : borelMooreHomology L j) :
    ((relativeChainComplexTower L K).homology j).limπ n (borelMooreHomologyToLim L K j x) =
      (HomologicalComplex.homologyMap ((TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative
        L (K.isCompact n).compl_range_ofSubset_compl_map) j).hom x :=
  (ModuleTower.limπ_apply _ n _).trans <| (ComplexTower.coe_homologyToLim_apply _ j _ n).trans <|
    (congrArg (fun g : (locallyFiniteChainComplex L).homology j ⟶
        ((relativeChainComplexTower L K).obj (op n)).homology j ↦ g.hom x)
      (HomologicalComplex.homologyMap_comp _ _ j).symm).trans
      (congrArg (fun φ : locallyFiniteChainComplex L ⟶ (relativeChainComplexTower L K).obj (op n) ↦
        (HomologicalComplex.homologyMap φ j).hom x)
        (locallyFiniteChainComplexIsoLimComplex_hom_comp_limComplexπ L K n))

/-- The map from `lim¹` of the relative twisted homology modules `H_{j+1}(X, X \ Kₙ; L)` of a
compact exhaustion to Borel–Moore homology in degree `j`: the connecting map of the Milnor
sequence. -/
def limOneToBorelMooreHomology (j : ℕ) :
    ((relativeChainComplexTower L K).homology (j + 1)).limOne →ₗ[R] borelMooreHomology L j :=
  (HomologicalComplex.homologyMap (locallyFiniteChainComplexIsoLimComplex L K).inv j).hom ∘ₗ
    (relativeChainComplexTower L K).limOneToHomology
      (relativeChainComplexTower_shift_surjective L K) (ComplexShape.down_mk (j + 1) j rfl)

/-- The connecting map of the Milnor sequence of Borel–Moore homology is the connecting map of the
tower of complexes, after identifying the limit complex with locally finite chains. -/
lemma limOneToBorelMooreHomology_def (j : ℕ) :
    limOneToBorelMooreHomology L K j =
      (HomologicalComplex.homologyMap (locallyFiniteChainComplexIsoLimComplex L K).inv j).hom ∘ₗ
        (relativeChainComplexTower L K).limOneToHomology
          (relativeChainComplexTower_shift_surjective L K) (ComplexShape.down_mk (j + 1) j rfl) :=
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
    (relativeChainComplexTower_shift_surjective L K) (ComplexShape.down_mk (j + 1) j rfl)
  refine Function.Exact.of_ladder_linearEquiv_of_exact (e₁ := LinearEquiv.refl R _)
    (e₂ := e.symm) (e₃ := LinearEquiv.refl R _) ?_ ?_ hexact
  · rw [limOneToBorelMooreHomology_def]
    rfl
  · rw [borelMooreHomologyToLim_def]
    exact LinearMap.ext fun x ↦
      congrArg ((relativeChainComplexTower L K).homologyToLim j) (e.apply_symm_apply x)

/-- The map from Borel–Moore homology to the limit of the relative twisted homology modules of a
compact exhaustion is surjective. -/
theorem borelMooreHomologyToLim_surjective (j : ℕ) :
    Function.Surjective (borelMooreHomologyToLim L K j) := by
  let e := (HomologicalComplex.homologyMapIso
    (locallyFiniteChainComplexIsoLimComplex L K) j).toLinearEquiv
  rw [borelMooreHomologyToLim_def, LinearMap.coe_comp]
  exact (ComplexTower.homologyToLim_surjective (relativeChainComplexTower_shift_surjective L K)
    j).comp e.surjective

end Milnor

end TauCeti.LocalCoefficientSystem
