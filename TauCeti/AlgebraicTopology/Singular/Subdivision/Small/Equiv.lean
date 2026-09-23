/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Homotopy

/-!
# Chains subordinate to a cover are a deformation retract of all singular chains

For an open cover `U` of a space `X`, the singular chains subordinate to `U` — those supported on
simplices whose image lies in a single member of `U` — include into all singular chains by a chain
homotopy equivalence.  This is the small-chain theorem, the analytic heart of excision: it lets
every singular chain be replaced, without changing its homology class, by one assembled from
simplices small enough to be seen inside a single member of the cover.

The construction is Hatcher's.  Barycentric subdivision `S` is chain homotopic to the identity
through the prism operator `P`, so the `m`-fold subdivision `Sᵐ` is chain homotopic to the identity
through `∑_{k < m} Sᵏ ≫ P`.  A singular simplex `σ` becomes subordinate to `U` after enough
subdivisions; taking for each `σ` a number `singularSubdivisionDepth` of subdivisions that works
simultaneously for `σ` and all of its iterated faces produces a chain-homotopy operator `D` whose
associated map `ρ = 1 - ∂D - D∂` is a chain map landing in the chains subordinate to `U`.  Since
`D` vanishes on subordinate simplices, `ρ` restricts to the identity there, so the inclusion is a
deformation retract in the chain-level sense: it has a strict retraction which is a homotopy
inverse.

The number of subdivisions depends on the simplex, so `ρ` and the resulting retraction are not
natural in the space.  The inclusion itself is natural, hence so is the induced isomorphism
`smallSingularHomologyIso` on homology.

## Main definitions and results

* `TauCeti.smallSingularChains`: the subgroup of singular chains factoring through the chains
  subordinate to `U`.
* `TauCeti.singularSubdivisionDepth`: a number of barycentric subdivisions making a singular
  simplex and all of its iterated faces subordinate to `U`, monotone under passing to a face.
* `TauCeti.singularSmallApprox`: the chain endomorphism `ρ`, with
  `TauCeti.singularSmallApproxHomotopy` the chain homotopy to the identity and
  `TauCeti.mem_smallSingularChains_ιChainComplex_comp_singularSmallApprox` the statement that it
  lands in the chains subordinate to `U`.
* `TauCeti.smallSingularRetraction`: the resulting retraction of singular chains onto the chains
  subordinate to `U`.
* `TauCeti.smallSingularChainHomotopyEquiv`: the small-chain inclusion is a chain homotopy
  equivalence, and `TauCeti.smallSingularHomologyIso` the induced isomorphism on homology.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Proposition 2.21.
-/

public section

noncomputable section

open CategoryTheory Limits Convexity Simplicial AlgebraicTopology

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C)
  {X : TopCat.{w}} {ι : Type*} (U : ι → Set X)

-- The chain inclusion is the coproduct map induced by an injective map of simplices.
local instance (n : ℕ) :
    Mono ((SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f n) :=
  inferInstanceAs (Mono ((sigmaConst.obj R).map
    ((X.smallSingularSubcomplex U).ι.app (Opposite.op ⦋n⦌))))

/-- The subgroup of the singular `n`-chains of `X` with coefficients in `R` consisting of the
chains that factor through the chains subordinate to the family `U`. -/
def smallSingularChains (n : ℕ) :
    AddSubgroup (R ⟶ ((TopCat.toSSet.obj X).chainComplex R).X n) :=
  (Preadditive.rightComp R
    ((SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f n)).range

variable {R U}

lemma mem_smallSingularChains_iff {n : ℕ}
    (f : R ⟶ ((TopCat.toSSet.obj X).chainComplex R).X n) :
    f ∈ smallSingularChains R U n ↔
      ∃ g : R ⟶ ((X.smallSingularSubcomplex U : SSet).chainComplex R).X n,
        g ≫ (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f n = f :=
  AddMonoidHom.mem_range

/-- The summand of a simplex subordinate to `U` is a chain subordinate to `U`. -/
lemma ιChainComplex_mem_smallSingularChains {n : ℕ}
    (σ : (X.smallSingularSubcomplex U : SSet) _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ.1 ∈ smallSingularChains R U n :=
  (mem_smallSingularChains_iff _).2
    ⟨(X.smallSingularSubcomplex U : SSet).ιChainComplex σ, by simp⟩

/-- The prism operator of barycentric subdivision preserves chains subordinate to `U`. -/
lemma smallSingularChains.comp_singularPrismX {n : ℕ}
    {f : R ⟶ ((TopCat.toSSet.obj X).chainComplex R).X n}
    (hf : f ∈ smallSingularChains R U n) :
    f ≫ singularPrismX R X n ∈ smallSingularChains R U (n + 1) := by
  obtain ⟨g, rfl⟩ := (mem_smallSingularChains_iff _).1 hf
  exact (mem_smallSingularChains_iff _).2
    ⟨g ≫ smallSingularPrismX R U n, by simp⟩

/-- Barycentric subdivision preserves chains subordinate to `U`. -/
lemma smallSingularChains.comp_singularSubdivisionX {n : ℕ}
    {f : R ⟶ ((TopCat.toSSet.obj X).chainComplex R).X n}
    (hf : f ∈ smallSingularChains R U n) :
    f ≫ singularSubdivisionX R X n ∈ smallSingularChains R U n := by
  obtain ⟨g, rfl⟩ := (mem_smallSingularChains_iff _).1 hf
  exact (mem_smallSingularChains_iff _).2
    ⟨g ≫ smallSingularSubdivisionX R U n, by simp⟩

/-- Once a chain has become subordinate to `U` after `m` subdivisions, it stays subordinate
after any larger number of subdivisions. -/
lemma smallSingularChains.comp_singularSubdivisionChainMap_pow_of_le {n m m' : ℕ} (hm : m ≤ m')
    {f : R ⟶ ((TopCat.toSSet.obj X).chainComplex R).X n}
    (hf : f ≫ (End.of (singularSubdivisionChainMap R X) ^ m).f n ∈ smallSingularChains R U n) :
    f ≫ (End.of (singularSubdivisionChainMap R X) ^ m').f n ∈ smallSingularChains R U n := by
  induction m', hm using Nat.le_induction with
  | base => exact hf
  | succ m' _ ih =>
    rw [HomologicalComplex.pow_f_succ, singularSubdivisionChainMap_f, ← Category.assoc]
    exact smallSingularChains.comp_singularSubdivisionX ih

variable (R U)

/-- The least number of barycentric subdivisions after which a singular simplex becomes a chain
subordinate to the family `U`. -/
def singularSubdivisionOrder {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) : ℕ :=
  sInf {m | (TopCat.toSSet.obj X).ιChainComplex σ ≫
    (End.of (singularSubdivisionChainMap R X) ^ m).f n ∈ smallSingularChains R U n}

/-- The subdivision order is at most any number of subdivisions that makes the simplex
subordinate to `U`. -/
lemma singularSubdivisionOrder_le {n m : ℕ} {σ : TopCat.toSSet.obj X _⦋n⦌}
    (hσ : (TopCat.toSSet.obj X).ιChainComplex σ ≫
      (End.of (singularSubdivisionChainMap R X) ^ m).f n ∈ smallSingularChains R U n) :
    singularSubdivisionOrder R U σ ≤ m :=
  Nat.sInf_le hσ

/-- After `singularSubdivisionOrder` subdivisions, or any larger number, a singular simplex is a
chain subordinate to the open cover `U`. -/
theorem mem_smallSingularChains_ιChainComplex_comp_pow (hU : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = Set.univ) {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) {m : ℕ}
    (hm : singularSubdivisionOrder R U σ ≤ m) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫
      (End.of (singularSubdivisionChainMap R X) ^ m).f n ∈ smallSingularChains R U n := by
  obtain ⟨n₀, hn₀⟩ := exists_iterate_singularSubdivision_factor_small R U hU hcov σ
  exact smallSingularChains.comp_singularSubdivisionChainMap_pow_of_le hm
    (Nat.sInf_mem (s := {m | (TopCat.toSSet.obj X).ιChainComplex σ ≫
        (End.of (singularSubdivisionChainMap R X) ^ m).f n ∈ smallSingularChains R U n})
      ⟨n₀, (mem_smallSingularChains_iff _).2 (hn₀ n₀ le_rfl)⟩)

/-- A simplex already subordinate to `U` needs no subdivision. -/
@[simp]
lemma singularSubdivisionOrder_eq_zero {n : ℕ} {σ : TopCat.toSSet.obj X _⦋n⦌}
    (hσ : σ ∈ (X.smallSingularSubcomplex U).obj (Opposite.op ⦋n⦌)) :
    singularSubdivisionOrder R U σ = 0 :=
  Nat.le_zero.1 (Nat.sInf_le (by
    simpa using ιChainComplex_mem_smallSingularChains (R := R) ⟨σ, hσ⟩))

/-- The subdivision depth of a singular simplex: a number of barycentric subdivisions after which
the simplex and all of its iterated faces are subordinate to the family `U`.  Unlike the order, it
is monotone under passing to a face, which is what makes the operator
`TauCeti.singularSmallApproxHom` below land in the chains subordinate to `U`. -/
def singularSubdivisionDepth (n : ℕ) (σ : TopCat.toSSet.obj X _⦋n⦌) : ℕ :=
  match n, σ with
  | 0, σ => singularSubdivisionOrder R U σ
  | n + 1, σ => max (singularSubdivisionOrder R U σ)
      (Finset.univ.sup fun j : Fin (n + 2) ↦
        singularSubdivisionDepth n ((TopCat.toSSet.obj X).δ j σ))

lemma singularSubdivisionOrder_le_singularSubdivisionDepth (n : ℕ)
    (σ : TopCat.toSSet.obj X _⦋n⦌) :
    singularSubdivisionOrder R U σ ≤ singularSubdivisionDepth R U n σ := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

lemma singularSubdivisionDepth_δ_le (n : ℕ) (σ : TopCat.toSSet.obj X _⦋n + 1⦌)
    (j : Fin (n + 2)) :
    singularSubdivisionDepth R U n ((TopCat.toSSet.obj X).δ j σ) ≤
      singularSubdivisionDepth R U (n + 1) σ := by
  rw [singularSubdivisionDepth]
  exact le_max_of_le_right (Finset.le_sup (f := fun j : Fin (n + 2) ↦
    singularSubdivisionDepth R U n ((TopCat.toSSet.obj X).δ j σ)) (Finset.mem_univ j))

@[simp]
lemma singularSubdivisionDepth_eq_zero : ∀ (n : ℕ) (σ : TopCat.toSSet.obj X _⦋n⦌),
    σ ∈ (X.smallSingularSubcomplex U).obj (Opposite.op ⦋n⦌) →
      singularSubdivisionDepth R U n σ = 0 := by
  intro n
  induction n with
  | zero => exact fun σ hσ ↦ singularSubdivisionOrder_eq_zero R U hσ
  | succ n ih =>
    intro σ hσ
    rw [singularSubdivisionDepth, singularSubdivisionOrder_eq_zero R U hσ,
      Nat.max_eq_right (Nat.zero_le _)]
    exact Nat.le_zero.1 (Finset.sup_le fun j _ ↦
      (ih _ ((X.smallSingularSubcomplex U).map (SimplexCategory.δ j).op hσ)).le)

/-! ### The small-chain approximation -/

/-- The chain-homotopy operator of the small-chain approximation.  On the summand of a singular
simplex `σ` it is the iterated prism operator of the chain homotopy from the identity to the
`singularSubdivisionDepth`-fold barycentric subdivision. -/
def singularSmallApproxHom (i j : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex R).X i ⟶ ((TopCat.toSSet.obj X).chainComplex R).X j :=
  Cofan.IsColimit.desc ((TopCat.toSSet.obj X).isColimitChainComplexXCofan R i) fun σ ↦
    (TopCat.toSSet.obj X).ιChainComplex σ ≫
      ((singularSubdivisionHomotopy R X).idPow (singularSubdivisionDepth R U i σ)).hom i j

@[reassoc (attr := simp)]
lemma ιChainComplex_singularSmallApproxHom {i j : ℕ} (σ : TopCat.toSSet.obj X _⦋i⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ singularSmallApproxHom R U i j =
      (TopCat.toSSet.obj X).ιChainComplex σ ≫
        ((singularSubdivisionHomotopy R X).idPow (singularSubdivisionDepth R U i σ)).hom i j :=
  Cofan.IsColimit.fac _ _ σ

lemma singularSmallApproxHom_eq_zero (i j : ℕ) (hij : ¬ (ComplexShape.down ℕ).Rel j i) :
    singularSmallApproxHom R U i j = 0 := by
  ext σ
  rw [ιChainComplex_singularSmallApproxHom,
    ((singularSubdivisionHomotopy R X).idPow (singularSubdivisionDepth R U i σ)).zero i j hij]

/-- The small-chain approximation of the singular chain complex: a chain endomorphism homotopic
to the identity all of whose values are chains subordinate to `U`.  It is Hatcher's operator
`ρ = 1 - ∂D - D∂`, where `D` is `TauCeti.singularSmallApproxHom`. -/
def singularSmallApprox :
    (TopCat.toSSet.obj X).chainComplex R ⟶ (TopCat.toSSet.obj X).chainComplex R :=
  𝟙 _ - Homotopy.nullHomotopicMap (singularSmallApproxHom R U)

lemma singularSmallApprox_f (n : ℕ) :
    (singularSmallApprox R U).f n = 𝟙 _ -
      (dNext n (singularSmallApproxHom R U) + prevD n (singularSmallApproxHom R U)) := by
  rw [singularSmallApprox, HomologicalComplex.sub_f_apply, HomologicalComplex.id_f,
    (Homotopy.nullHomotopy _ (singularSmallApproxHom_eq_zero R U)).comm n]
  simp [Homotopy.nullHomotopy]

/-- The small-chain approximation is chain homotopic to the identity. -/
def singularSmallApproxHomotopy : Homotopy (𝟙 _) (singularSmallApprox R U) where
  hom := singularSmallApproxHom R U
  zero := singularSmallApproxHom_eq_zero R U
  comm n := by
    rw [singularSmallApprox_f]
    abel

/-- The approximation operator kills the chains that are already subordinate to `U`. -/
lemma ι_comp_singularSmallApproxHom (i j : ℕ) :
    (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f i ≫
      singularSmallApproxHom R U i j = 0 := by
  ext τ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  simp

/-- The approximation restricts to the identity on the chains subordinate to `U`. -/
@[reassoc (attr := simp)]
lemma ι_comp_singularSmallApprox :
    SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R ≫ singularSmallApprox R U =
      SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R := by
  ext n : 1
  have hd : (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f n ≫
      dNext n (singularSmallApproxHom R U) = 0 := by
    rw [dNext, AddMonoidHom.mk'_apply, ← Category.assoc, HomologicalComplex.Hom.comm,
      Category.assoc, ι_comp_singularSmallApproxHom, comp_zero]
  have hp : (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f n ≫
      prevD n (singularSmallApproxHom R U) = 0 := by
    rw [prevD, AddMonoidHom.mk'_apply, ← Category.assoc, ι_comp_singularSmallApproxHom, zero_comp]
  rw [HomologicalComplex.comp_f, singularSmallApprox_f, Preadditive.comp_sub, Category.comp_id,
    Preadditive.comp_add, hd, hp, add_zero, sub_zero]

variable (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ)

include hU hcov

/-- Enlarging the number of subdivisions in the iterated prism operator changes it by a chain
subordinate to `U`, provided the simplex is already subordinate after the smaller number. -/
lemma mem_smallSingularChains_ιChainComplex_comp_idPow_hom_sub {n : ℕ}
    (σ : TopCat.toSSet.obj X _⦋n⦌) {m m' : ℕ} (hm' : singularSubdivisionOrder R U σ ≤ m')
    (hmm : m' ≤ m) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫
        (((singularSubdivisionHomotopy R X).idPow m).hom n (n + 1) -
          ((singularSubdivisionHomotopy R X).idPow m').hom n (n + 1)) ∈
      smallSingularChains R U (n + 1) := by
  have hsum : ((singularSubdivisionHomotopy R X).idPow m).hom n (n + 1) -
      ((singularSubdivisionHomotopy R X).idPow m').hom n (n + 1) =
      ∑ k ∈ Finset.Ico m' m,
        (End.of (singularSubdivisionChainMap R X) ^ k).f n ≫ singularPrismX R X n := by
    rw [Finset.sum_Ico_eq_sub _ hmm]
    simp
  rw [hsum, Preadditive.comp_sum]
  refine AddSubgroup.sum_mem _ fun k hk ↦ ?_
  rw [← Category.assoc]
  exact smallSingularChains.comp_singularPrismX
    (mem_smallSingularChains_ιChainComplex_comp_pow R U hU hcov σ
      (hm'.trans (Finset.mem_Ico.1 hk).1))

/-- **The small-chain approximation lands in the chains subordinate to the cover.** -/
theorem mem_smallSingularChains_ιChainComplex_comp_singularSmallApprox {n : ℕ}
    (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ (singularSmallApprox R U).f n ∈
      smallSingularChains R U n := by
  set m := singularSubdivisionDepth R U n σ
  -- The two prism operators agree on the summand of `σ` in the `prevD` direction.
  have hprev : (TopCat.toSSet.obj X).ιChainComplex σ ≫
      (prevD n ((singularSubdivisionHomotopy R X).idPow m).hom -
        prevD n (singularSmallApproxHom R U)) = 0 := by
    rw [Preadditive.comp_sub, Homotopy.prevD_chainComplex, Homotopy.prevD_chainComplex,
      ← Category.assoc, ← Category.assoc, ιChainComplex_singularSmallApproxHom, sub_self]
  -- In the `dNext` direction they differ by a chain subordinate to `U`, because the depth of a
  -- face of `σ` is at most the depth of `σ`.
  have hdnext : (TopCat.toSSet.obj X).ιChainComplex σ ≫
      (dNext n ((singularSubdivisionHomotopy R X).idPow m).hom -
        dNext n (singularSmallApproxHom R U)) ∈ smallSingularChains R U n := by
    cases n with
    | zero => simp
    | succ k =>
      rw [Preadditive.comp_sub, Homotopy.dNext_succ_chainComplex,
        Homotopy.dNext_succ_chainComplex, ← Category.assoc, ← Category.assoc,
        SSet.ιChainComplex_d, Preadditive.sum_comp, Preadditive.sum_comp,
        ← Finset.sum_sub_distrib]
      refine AddSubgroup.sum_mem _ fun j _ ↦ ?_
      rw [Preadditive.zsmul_comp, Preadditive.zsmul_comp, ← smul_sub, ← Preadditive.comp_sub,
        Preadditive.comp_sub, ιChainComplex_singularSmallApproxHom, ← Preadditive.comp_sub]
      exact AddSubgroup.zsmul_mem _
        (mem_smallSingularChains_ιChainComplex_comp_idPow_hom_sub R U hU hcov _
          (singularSubdivisionOrder_le_singularSubdivisionDepth R U k _)
          (singularSubdivisionDepth_δ_le R U k σ j)) _
  have hf : (TopCat.toSSet.obj X).ιChainComplex σ ≫ (singularSmallApprox R U).f n =
      (TopCat.toSSet.obj X).ιChainComplex σ ≫
          (End.of (singularSubdivisionChainMap R X) ^ m).f n +
        (TopCat.toSSet.obj X).ιChainComplex σ ≫
          (dNext n ((singularSubdivisionHomotopy R X).idPow m).hom -
            dNext n (singularSmallApproxHom R U)) := by
    have hsplit : (singularSmallApprox R U).f n =
        (End.of (singularSubdivisionChainMap R X) ^ m).f n +
          (dNext n ((singularSubdivisionHomotopy R X).idPow m).hom -
            dNext n (singularSmallApproxHom R U)) +
          (prevD n ((singularSubdivisionHomotopy R X).idPow m).hom -
            prevD n (singularSmallApproxHom R U)) := by
      rw [singularSmallApprox_f, ← HomologicalComplex.id_f,
        ((singularSubdivisionHomotopy R X).idPow m).comm n]
      abel
    rw [hsplit, Preadditive.comp_add, Preadditive.comp_add, hprev, add_zero]
  rw [hf]
  exact AddSubgroup.add_mem _ (mem_smallSingularChains_ιChainComplex_comp_pow R U hU hcov σ
    (singularSubdivisionOrder_le_singularSubdivisionDepth R U n σ)) hdnext

/-! ### The retraction onto the chains subordinate to the cover -/

private theorem exists_comp_eq_ιChainComplex_comp_singularSmallApprox {n : ℕ}
    (σ : TopCat.toSSet.obj X _⦋n⦌) :
    ∃ g : R ⟶ ((X.smallSingularSubcomplex U : SSet).chainComplex R).X n,
      g ≫ (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f n =
        (TopCat.toSSet.obj X).ιChainComplex σ ≫ (singularSmallApprox R U).f n :=
  (mem_smallSingularChains_iff _).1
    (mem_smallSingularChains_ιChainComplex_comp_singularSmallApprox R U hU hcov σ)

/-- The degreewise factorisation of the small-chain approximation through the chains subordinate
to `U`, obtained by choosing a factorisation on each summand. -/
private def smallSingularRetractionX (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex R).X n ⟶
      ((X.smallSingularSubcomplex U : SSet).chainComplex R).X n :=
  Cofan.IsColimit.desc ((TopCat.toSSet.obj X).isColimitChainComplexXCofan R n) fun σ ↦
    (exists_comp_eq_ιChainComplex_comp_singularSmallApprox R U hU hcov σ).choose

@[reassoc]
private lemma ιChainComplex_smallSingularRetractionX {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ smallSingularRetractionX R U hU hcov n =
      (exists_comp_eq_ιChainComplex_comp_singularSmallApprox R U hU hcov σ).choose :=
  Cofan.IsColimit.fac _ _ σ

@[reassoc (attr := simp)]
private lemma smallSingularRetractionX_comp_ι (n : ℕ) :
    smallSingularRetractionX R U hU hcov n ≫
        (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f n =
      (singularSmallApprox R U).f n := by
  ext σ
  rw [← Category.assoc, ιChainComplex_smallSingularRetractionX]
  exact (exists_comp_eq_ιChainComplex_comp_singularSmallApprox R U hU hcov σ).choose_spec

/-- **The retraction of singular chains onto the chains subordinate to an open cover.** -/
def smallSingularRetraction :
    (TopCat.toSSet.obj X).chainComplex R ⟶
      (X.smallSingularSubcomplex U : SSet).chainComplex R where
  f := smallSingularRetractionX R U hU hcov
  comm' i j hij := by
    apply (cancel_mono ((SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f j)).1
    rw [Category.assoc, ← HomologicalComplex.Hom.comm, ← Category.assoc,
      smallSingularRetractionX_comp_ι, Category.assoc, smallSingularRetractionX_comp_ι,
      HomologicalComplex.Hom.comm]

@[simp]
private lemma smallSingularRetraction_f (n : ℕ) :
    (smallSingularRetraction R U hU hcov).f n = smallSingularRetractionX R U hU hcov n := (rfl)

@[reassoc (attr := simp)]
lemma smallSingularRetraction_comp_ι :
    smallSingularRetraction R U hU hcov ≫
        SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R = singularSmallApprox R U := by
  ext n : 1
  exact smallSingularRetractionX_comp_ι R U hU hcov n

/-! ### The inclusion is a chain homotopy equivalence -/

@[reassoc (attr := simp)]
lemma ι_comp_smallSingularRetraction :
    SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R ≫
      smallSingularRetraction R U hU hcov = 𝟙 _ := by
  have : Mono (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R) :=
    HomologicalComplex.mono_of_mono_f _ inferInstance
  apply (cancel_mono (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R)).1
  rw [Category.assoc, smallSingularRetraction_comp_ι, ι_comp_singularSmallApprox,
    Category.id_comp]

/-- **Chains subordinate to an open cover are a deformation retract of all singular chains.**
The inclusion of the chains subordinate to an open cover `U` into the singular chain complex is a
chain homotopy equivalence, whose homotopy inverse `TauCeti.smallSingularRetraction` is even a
strict retraction. -/
def smallSingularChainHomotopyEquiv :
    HomotopyEquiv ((X.smallSingularSubcomplex U : SSet).chainComplex R)
      ((TopCat.toSSet.obj X).chainComplex R) where
  hom := SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R
  inv := smallSingularRetraction R U hU hcov
  homotopyHomInvId := Homotopy.ofEq (ι_comp_smallSingularRetraction R U hU hcov)
  homotopyInvHomId := (Homotopy.ofEq (smallSingularRetraction_comp_ι R U hU hcov)).trans
    (singularSmallApproxHomotopy R U).symm

/-- The isomorphism on homology induced by the inclusion of the chains subordinate to an open
cover.  Since the inclusion is natural in the covered space, so is this isomorphism, whereas the
homotopy inverse underlying it is not. -/
def smallSingularHomologyIso [CategoryWithHomology C] (n : ℕ) :
    ((X.smallSingularSubcomplex U : SSet).chainComplex R).homology n ≅
      ((TopCat.toSSet.obj X).chainComplex R).homology n :=
  (smallSingularChainHomotopyEquiv R U hU hcov).toHomologyIso n

@[simp]
lemma smallSingularHomologyIso_hom [CategoryWithHomology C] (n : ℕ) :
    (smallSingularHomologyIso R U hU hcov n).hom = HomologicalComplex.homologyMap
      (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R) n := (rfl)

/-- The small-chain homology isomorphism is natural under maps carrying members of one cover
into members of another. -/
lemma smallSingularHomologyIso_naturality [CategoryWithHomology C]
    {κ : Type*} {Y : TopCat.{w}} (V : κ → Set Y) (f : X ⟶ Y) (r : ι → κ)
    (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) (hV : ∀ j, IsOpen (V j))
    (hcovV : ⋃ j, V j = Set.univ) (n : ℕ) :
    (smallSingularHomologyIso R U hU hcov n).hom ≫
        HomologicalComplex.homologyMap
          (SSet.chainComplexMap (TopCat.toSSet.map f) R) n =
      HomologicalComplex.homologyMap
          (SSet.chainComplexMap (X.smallSingularSubcomplexMap U V f r hf) R) n ≫
        (smallSingularHomologyIso R V hV hcovV n).hom := by
  rw [smallSingularHomologyIso_hom, smallSingularHomologyIso_hom,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    ← Functor.map_comp, ← Functor.map_comp, TopCat.smallSingularSubcomplexMap_ι]

/-- The inclusion of the chains subordinate to an open cover induces an isomorphism on homology
in every degree. -/
theorem isIso_homologyMap_smallSingularChainι [CategoryWithHomology C] (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R) n) := by
  rw [← smallSingularHomologyIso_hom R U hU hcov n]
  infer_instance

/-- The inclusion of the chains subordinate to an open cover is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smallSingularSubcomplex_ι [CategoryWithHomology C] :
    QuasiIso (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_homologyMap_smallSingularChainι R U hU hcov n

end TauCeti
