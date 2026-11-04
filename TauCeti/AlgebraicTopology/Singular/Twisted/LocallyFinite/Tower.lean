/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import TauCeti.Algebra.Category.ModuleCat.Tower.Milnor.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.Triple

/-!
# Locally finite chains as an inverse limit of relative chains

Let `K₀ ⊆ K₁ ⊆ ⋯` be a compact exhaustion of a space `X` and let `L` be a local coefficient system
on `X`. The relative twisted chain complexes `C(X, X \ Kₙ; L)`, with the quotient maps
`C(X, X \ Kₙ₊₁; L) ⟶ C(X, X \ Kₙ; L)` of the triples `(X, X \ Kₙ, X \ Kₙ₊₁)`, form a tower of
chain complexes whose transition maps are surjective in every degree
(`TauCeti.LocalCoefficientSystem.relativeChainComplexTower`).

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
  Functor.ofOpSequence (X := fun n ↦ (TopPair.ofSubset (K n)ᶜ).twistedChainComplex L)
    fun n ↦ TopTriple.twistedChainComplexTotalToOuter
      (TopTriple.ofSubset (Set.compl_subset_compl.2 (K.subset_succ n))) L

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
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- Every map of the tower of a compact exhaustion is induced by the identity of the ambient
twisted chains. -/
@[reassoc, simp]
lemma twistedChainComplexπ_comp_relativeChainComplexTower_map {m n : ℕ} (f : op m ⟶ op n) :
    (TopPair.ofSubset (K m)ᶜ).twistedChainComplexπ L ≫ (relativeChainComplexTower L K).map f =
      (TopPair.ofSubset (K n)ᶜ).twistedChainComplexπ L := by
  have hnm : n ≤ m := leOfHom f.unop
  induction m, hnm using Nat.le_induction with
  | base =>
    obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
    exact (congrArg (_ ≫ ·) ((relativeChainComplexTower L K).map_id _)).trans (Category.comp_id _)
  | succ m hnm ih =>
    obtain rfl : f = (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op := Subsingleton.elim _ _
    refine (congrArg (_ ≫ ·) ((relativeChainComplexTower L K).map_comp _ _)).trans <|
      (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) ?_).trans (ih _)
    exact (congrArg (_ ≫ ·) (relativeChainComplexTower_map_succ L K m)).trans
      ((TopTriple.ofSubset _).twistedChainComplexπ_comp_totalToOuter L)

/-- The transitions of the tower of a compact exhaustion are surjective in every degree. -/
lemma relativeChainComplexTower_transition_surjective (i n : ℕ) :
    Function.Surjective (((relativeChainComplexTower L K).term i).transition n) := by
  rw [ModuleTower.transition_def, Functor.comp_map, HomologicalComplex.eval_map]
  intro y
  obtain ⟨a, rfl⟩ := (TopPair.ofSubset (K n)ᶜ).twistedChainComplexπ_f_surjective L y
  exact ⟨(((TopPair.ofSubset (K (n + 1))ᶜ).twistedChainComplexπ L).f i).hom a,
    congrArg (fun g ↦ (g.f i).hom a)
      (twistedChainComplexπ_comp_relativeChainComplexTower_map L K (homOfLE (Nat.le_succ n)).op)⟩

/-- The tower of a compact exhaustion has surjective shift maps in every degree, so its `lim¹`
vanishes and the Milnor sequence applies to it. -/
lemma relativeChainComplexTower_shift_surjective (i : ℕ) :
    Function.Surjective ((relativeChainComplexTower L K).term i).shift :=
  ModuleTower.shift_surjective _ (relativeChainComplexTower_transition_surjective L K i)

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
def locallyFiniteChainComplexCone : Cone (relativeChainComplexTower L K) where
  pt := locallyFiniteChainComplex L
  π := NatTrans.ofOpSequence (fun n ↦ (TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative
    L (K.isCompact n).compl_range_ofSubset_compl_map) fun n ↦
    (Category.id_comp _).trans <|
      ((congrArg (_ ≫ ·) (relativeChainComplexTower_map_succ L K n)).trans
        (TopTriple.locallyFiniteChainComplexToRelative_comp_twistedChainComplexTotalToOuter
          (TopTriple.ofSubset (Set.compl_subset_compl.2 (K.subset_succ n))) L
          (K.isCompact (n + 1)).compl_range_ofSubset_compl_map
          (K.isCompact n).compl_range_ofSubset_compl_map)).symm

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
