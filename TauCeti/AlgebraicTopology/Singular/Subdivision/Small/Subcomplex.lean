/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Equiv
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Subcomplex
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Coproduct

/-!
# The small-chain theorem for affinely stable subcomplexes of singular chains

Let `S` be an affinely stable subcomplex of the singular simplicial set of a space `X`
(`SSet.Subcomplex.IsAffineStable`), for instance the smooth singular simplices of a manifold
(`TauCeti.smoothSingularSubcomplex`), and let `U` be an open cover of `X`. The simplices of `S`
whose image lies in a single member of `U` form the subcomplex
`S ⊓ X.smallSingularSubcomplex U`. The inclusion of its chains into the chains of `S` is a chain
homotopy equivalence whose homotopy inverse is a strict retraction
(`TauCeti.subcomplexSmallChainHomotopyEquiv`). For the smooth singular simplices of a manifold this
is the small-chain theorem for smooth chains: every smooth singular chain is homologous, through
smooth chains, to a chain of smooth simplices each lying in a member of the cover. It is the input
to Mayer–Vietoris for smooth singular chains.

The construction restricts Hatcher's operator from the singular small-chain theorem
(`TauCeti.smallSingularChainHomotopyEquiv`) to `S`. On the summand of a simplex `σ` of `S`, the
chain-homotopy operator `D` (`TauCeti.subcomplexSmallApproxHom`) iterates the prism operator of the
restricted subdivision homotopy (`TauCeti.subcomplexSubdivisionHomotopy`); the number of iterations
is the subdivision depth `TauCeti.singularSubdivisionDepth` of `σ` as a singular simplex. Restricted
subdivision and prism are compatible with the inclusion into singular chains, so `D` and the
approximation `ρ = 1 - ∂D - D∂` (`TauCeti.subcomplexSmallApprox`) restrict the corresponding
singular operators. By the singular theorem, `ρ σ` is a singular chain subordinate to `U`. A
chain of `S` whose image is subordinate to `U` is a chain of `S ⊓ X.smallSingularSubcomplex U`
(`SSet.Subcomplex.exists_comp_chainComplexMap_homOfLE_eq_of_comp_eq`). Hence `ρ` factors through
the small chains of `S`, and the factorisation is the retraction.

## Main definitions and results

* `TauCeti.subcomplexSmallApprox`: the chain endomorphism `ρ` of the chains of `S`, chain homotopic
  to the identity (`TauCeti.subcomplexSmallApproxHomotopy`) and restricting the singular one
  (`TauCeti.subcomplexSmallApprox_ι`).
* `TauCeti.subcomplexSmallRetraction`: the retraction of the chains of `S` onto the chains of
  `S ⊓ X.smallSingularSubcomplex U`.
* `TauCeti.subcomplexSmallChainHomotopyEquiv`: the inclusion of these chains is a chain homotopy
  equivalence; `TauCeti.subcomplexSmallHomologyIso` is the induced isomorphism on homology and
  `TauCeti.quasiIso_chainComplexMap_homOfLE_inf_smallSingularSubcomplex` the quasi-isomorphism
  statement.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Proposition 2.21.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, proof of Theorem 18.7.
-/

public section

noncomputable section

open CategoryTheory Limits Simplicial AlgebraicTopology Opposite

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C)
  {X : TopCat.{w}} (S : (TopCat.toSSet.obj X).Subcomplex) {ι : Type*} (U : ι → Set X)

-- The chain inclusion is the coproduct map induced by an injective map of simplices.
local instance (n : ℕ) : Mono ((SSet.chainComplexMap
    (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) R).f n) :=
  inferInstanceAs (Mono ((sigmaConst.obj R).map
    ((SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)).app
      (op ⦋n⦌))))

variable [S.IsAffineStable]

/-! ### The small-chain approximation on `S` -/

/-- The chain-homotopy operator of the small-chain approximation of the chains of `S`. On the
summand of a simplex `σ` it is the iterated prism operator of the chain homotopy from the identity
to the `singularSubdivisionDepth`-fold restricted barycentric subdivision. -/
def subcomplexSmallApproxHom (i j : ℕ) :
    ((S : SSet).chainComplex R).X i ⟶ ((S : SSet).chainComplex R).X j :=
  Cofan.IsColimit.desc ((S : SSet).isColimitChainComplexXCofan R i) fun σ ↦
    (S : SSet).ιChainComplex σ ≫
      ((subcomplexSubdivisionHomotopy R S).idPow (singularSubdivisionDepth R U i σ.1)).hom i j

@[reassoc (attr := simp)]
lemma ιChainComplex_subcomplexSmallApproxHom {i j : ℕ} (σ : (S : SSet) _⦋i⦌) :
    (S : SSet).ιChainComplex σ ≫ subcomplexSmallApproxHom R S U i j =
      (S : SSet).ιChainComplex σ ≫
        ((subcomplexSubdivisionHomotopy R S).idPow (singularSubdivisionDepth R U i σ.1)).hom i j :=
  Cofan.IsColimit.fac _ _ σ

/-- The operator vanishes outside the bidegrees `(i, i + 1)` of a chain homotopy. -/
lemma subcomplexSmallApproxHom_eq_zero (i j : ℕ) (hij : ¬ (ComplexShape.down ℕ).Rel j i) :
    subcomplexSmallApproxHom R S U i j = 0 := by
  ext σ
  rw [ιChainComplex_subcomplexSmallApproxHom,
    ((subcomplexSubdivisionHomotopy R S).idPow (singularSubdivisionDepth R U i σ.1)).zero i j hij,
    comp_zero]

/-- The operator on the chains of `S` restricts the operator of the singular small-chain
approximation. -/
@[reassoc]
lemma subcomplexSmallApproxHom_ι (i j : ℕ) :
    subcomplexSmallApproxHom R S U i j ≫ (SSet.chainComplexMap S.ι R).f j =
      (SSet.chainComplexMap S.ι R).f i ≫ singularSmallApproxHom R U i j := by
  ext σ
  rw [ιChainComplex_subcomplexSmallApproxHom_assoc,
    Homotopy.idPow_hom_comp_eq_comp_idPow_hom _ (singularSubdivisionHomotopy R X)
      (subcomplexSubdivisionChainMap_ι R S) (subcomplexSubdivisionHomotopy_hom_ι R S),
    SSet.ι_chainComplexMap_f_assoc, SSet.ι_chainComplexMap_f_assoc,
    ιChainComplex_singularSmallApproxHom]
  rfl

/-- The small-chain approximation of the chains of `S`: Hatcher's operator `ρ = 1 - ∂D - D∂`,
where `D` is `TauCeti.subcomplexSmallApproxHom`. -/
def subcomplexSmallApprox : (S : SSet).chainComplex R ⟶ (S : SSet).chainComplex R :=
  𝟙 _ - Homotopy.nullHomotopicMap (subcomplexSmallApproxHom R S U)

/-- The small-chain approximation of the chains of `S` in degree `n`. -/
lemma subcomplexSmallApprox_f (n : ℕ) :
    (subcomplexSmallApprox R S U).f n = 𝟙 _ -
      (dNext n (subcomplexSmallApproxHom R S U) + prevD n (subcomplexSmallApproxHom R S U)) := by
  rw [subcomplexSmallApprox, HomologicalComplex.sub_f_apply, HomologicalComplex.id_f,
    (Homotopy.nullHomotopy _ (subcomplexSmallApproxHom_eq_zero R S U)).comm n]
  simp [Homotopy.nullHomotopy]

/-- The small-chain approximation of the chains of `S` is chain homotopic to the identity. -/
def subcomplexSmallApproxHomotopy : Homotopy (𝟙 _) (subcomplexSmallApprox R S U) where
  hom := subcomplexSmallApproxHom R S U
  zero := subcomplexSmallApproxHom_eq_zero R S U
  comm n := by
    rw [subcomplexSmallApprox_f]
    abel

/-- The small-chain approximation of the chains of `S` restricts the singular small-chain
approximation. -/
@[reassoc (attr := simp)]
lemma subcomplexSmallApprox_ι :
    subcomplexSmallApprox R S U ≫ SSet.chainComplexMap S.ι R =
      SSet.chainComplexMap S.ι R ≫ singularSmallApprox R U := by
  have h : (fun i j ↦ subcomplexSmallApproxHom R S U i j ≫ (SSet.chainComplexMap S.ι R).f j) =
      fun i j ↦ (SSet.chainComplexMap S.ι R).f i ≫ singularSmallApproxHom R U i j := by
    funext i j
    exact subcomplexSmallApproxHom_ι R S U i j
  ext n : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, subcomplexSmallApprox_f,
    singularSmallApprox_f, Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
    Category.comp_id, Preadditive.add_comp, Preadditive.comp_add, ← dNext_comp_right,
    ← prevD_comp_right, h, dNext_comp_left, prevD_comp_left]

/-- The approximation operator kills the chains of `S` that are already subordinate to `U`. -/
lemma homOfLE_comp_subcomplexSmallApproxHom (i j : ℕ) :
    (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) R).f i ≫
      subcomplexSmallApproxHom R S U i j = 0 := by
  ext τ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, ιChainComplex_subcomplexSmallApproxHom]
  simp [singularSubdivisionDepth_eq_zero R U i _ τ.2.2]

/-- The approximation restricts to the identity on the chains of `S` subordinate to `U`. -/
@[reassoc (attr := simp)]
lemma homOfLE_comp_subcomplexSmallApprox :
    SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) R ≫
      subcomplexSmallApprox R S U =
    SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) R := by
  ext n : 1
  have hd : (SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) R).f n ≫
        dNext n (subcomplexSmallApproxHom R S U) = 0 := by
    rw [dNext, AddMonoidHom.mk'_apply, ← Category.assoc, HomologicalComplex.Hom.comm,
      Category.assoc, homOfLE_comp_subcomplexSmallApproxHom, comp_zero]
  have hp : (SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) R).f n ≫
        prevD n (subcomplexSmallApproxHom R S U) = 0 := by
    rw [prevD, AddMonoidHom.mk'_apply, ← Category.assoc, homOfLE_comp_subcomplexSmallApproxHom,
      zero_comp]
  rw [HomologicalComplex.comp_f, subcomplexSmallApprox_f, Preadditive.comp_sub, Category.comp_id,
    Preadditive.comp_add, hd, hp, add_zero, sub_zero]

variable (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ)

include hU hcov

/-- **The small-chain approximation of `S` lands in the chains of `S` subordinate to the
cover.** -/
theorem exists_comp_eq_ιChainComplex_comp_subcomplexSmallApprox {n : ℕ}
    (σ : (S : SSet) _⦋n⦌) :
    ∃ g : R ⟶ ((S ⊓ X.smallSingularSubcomplex U).toSSet.chainComplex R).X n,
      g ≫ (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) R).f n =
          (S : SSet).ιChainComplex σ ≫ (subcomplexSmallApprox R S U).f n := by
  obtain ⟨g₀, hg₀⟩ := (mem_smallSingularChains_iff _).1
    (mem_smallSingularChains_ιChainComplex_comp_singularSmallApprox R U hU hcov σ.1)
  refine SSet.Subcomplex.exists_comp_chainComplexMap_homOfLE_eq_of_comp_eq R S _ (h := g₀) ?_
  rw [hg₀, Category.assoc, ← HomologicalComplex.comp_f, subcomplexSmallApprox_ι,
    HomologicalComplex.comp_f, SSet.ι_chainComplexMap_f_assoc]
  rfl

/-! ### The retraction onto the chains of `S` subordinate to the cover -/

/-- The degreewise factorisation of the small-chain approximation of `S` through the chains of
`S` subordinate to `U`, obtained by choosing a factorisation on each summand. -/
private def subcomplexSmallRetractionX (n : ℕ) :
    ((S : SSet).chainComplex R).X n ⟶
      ((S ⊓ X.smallSingularSubcomplex U).toSSet.chainComplex R).X n :=
  Cofan.IsColimit.desc ((S : SSet).isColimitChainComplexXCofan R n) fun σ ↦
    (exists_comp_eq_ιChainComplex_comp_subcomplexSmallApprox R S U hU hcov σ).choose

private lemma ιChainComplex_subcomplexSmallRetractionX {n : ℕ} (σ : (S : SSet) _⦋n⦌) :
    (S : SSet).ιChainComplex σ ≫ subcomplexSmallRetractionX R S U hU hcov n =
      (exists_comp_eq_ιChainComplex_comp_subcomplexSmallApprox R S U hU hcov σ).choose :=
  Cofan.IsColimit.fac _ _ σ

@[reassoc (attr := simp)]
private lemma subcomplexSmallRetractionX_comp_homOfLE (n : ℕ) :
    subcomplexSmallRetractionX R S U hU hcov n ≫ (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) R).f n =
      (subcomplexSmallApprox R S U).f n := by
  ext σ
  rw [← Category.assoc, ιChainComplex_subcomplexSmallRetractionX]
  exact (exists_comp_eq_ιChainComplex_comp_subcomplexSmallApprox R S U hU hcov σ).choose_spec

/-- **The retraction of the chains of `S` onto the chains of `S` subordinate to an open
cover.** -/
def subcomplexSmallRetraction :
    (S : SSet).chainComplex R ⟶ (S ⊓ X.smallSingularSubcomplex U).toSSet.chainComplex R where
  f := subcomplexSmallRetractionX R S U hU hcov
  comm' i j _ := by
    apply (cancel_mono ((SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) R).f j)).1
    rw [Category.assoc, ← HomologicalComplex.Hom.comm, ← Category.assoc,
      subcomplexSmallRetractionX_comp_homOfLE, Category.assoc,
      subcomplexSmallRetractionX_comp_homOfLE, HomologicalComplex.Hom.comm]

@[reassoc (attr := simp)]
lemma subcomplexSmallRetraction_comp_homOfLE :
    subcomplexSmallRetraction R S U hU hcov ≫ SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) R =
      subcomplexSmallApprox R S U := by
  ext n : 1
  exact subcomplexSmallRetractionX_comp_homOfLE R S U hU hcov n

@[reassoc (attr := simp)]
lemma homOfLE_comp_subcomplexSmallRetraction :
    SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) R ≫
      subcomplexSmallRetraction R S U hU hcov = 𝟙 _ := by
  apply (cancel_mono (SSet.chainComplexMap
    (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) R)).1
  rw [Category.assoc, subcomplexSmallRetraction_comp_homOfLE R S U hU hcov,
    homOfLE_comp_subcomplexSmallApprox, Category.id_comp]

/-! ### The inclusion is a chain homotopy equivalence -/

/-- **The small-chain theorem for an affinely stable subcomplex.** For an open cover `U` of `X`,
the inclusion of the chains of the simplices of `S` lying in a member of `U` into the chains of
`S` is a chain homotopy equivalence, whose homotopy inverse `TauCeti.subcomplexSmallRetraction` is
a strict retraction. -/
def subcomplexSmallChainHomotopyEquiv :
    HomotopyEquiv ((S ⊓ X.smallSingularSubcomplex U).toSSet.chainComplex R)
      ((S : SSet).chainComplex R) where
  hom := SSet.chainComplexMap
    (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) R
  inv := subcomplexSmallRetraction R S U hU hcov
  homotopyHomInvId := Homotopy.ofEq (homOfLE_comp_subcomplexSmallRetraction R S U hU hcov)
  homotopyInvHomId := (Homotopy.ofEq (subcomplexSmallRetraction_comp_homOfLE R S U hU hcov)).trans
    (subcomplexSmallApproxHomotopy R S U).symm

/-- The forward map of the small-chain homotopy equivalence of `S` is the inclusion of the chains
of `S` subordinate to the cover. -/
@[simp]
lemma subcomplexSmallChainHomotopyEquiv_hom :
    (subcomplexSmallChainHomotopyEquiv R S U hU hcov).hom = SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) R := (rfl)

/-- The isomorphism on homology induced by the inclusion of the chains of `S` subordinate to an
open cover. -/
def subcomplexSmallHomologyIso [CategoryWithHomology C] (n : ℕ) :
    ((S ⊓ X.smallSingularSubcomplex U).toSSet.chainComplex R).homology n ≅
      ((S : SSet).chainComplex R).homology n :=
  (subcomplexSmallChainHomotopyEquiv R S U hU hcov).toHomologyIso n

@[simp]
lemma subcomplexSmallHomologyIso_hom [CategoryWithHomology C] (n : ℕ) :
    (subcomplexSmallHomologyIso R S U hU hcov n).hom = HomologicalComplex.homologyMap
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) R) n :=
  (rfl)

/-- The inclusion of the chains of `S` subordinate to an open cover is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_homOfLE_inf_smallSingularSubcomplex [CategoryWithHomology C] :
    QuasiIso (SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) R) := by
  rw [← subcomplexSmallChainHomotopyEquiv_hom R S U hU hcov]
  infer_instance

end TauCeti
