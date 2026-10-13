/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Covering
public import TauCeti.AlgebraicTopology.Singular.Transfer.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.Basic

/-!
# Singular chains of a covering space as twisted chains of its base

Let `p : E ⟶ B` be a covering map and `R` a ring. A singular simplex `τ` of `E` is determined by
the simplex `p ∘ τ` of `B` together with the sheet over the initial vertex of `p ∘ τ` through
which `τ` passes, since a singular simplex of `B` lifts uniquely once the lift of one point is
prescribed. Hence the free module on the singular `n`-simplices of `E` is the direct sum, over the
singular `n`-simplices `σ` of `B`, of the free module on the sheets over the initial vertex of
`σ`, which is the fibre of the permutation local system `hp.permutationLocalSystem R` there. This
identification commutes with the boundary maps: passing to a face moves the initial vertex inside
`σ`, which moves the sheet by monodromy along a path inside `σ`, and the lift of that path is the
corresponding path inside `τ`. So the singular chain complex of `E` is isomorphic to the chain
complex of `B` twisted by the permutation local system
(`IsCoveringMap.singularChainComplexPermutationIso`), and the same holds for homology
(`IsCoveringMap.singularHomologyPermutationIso`).

Under this isomorphism the two maps between the chains of `E` and of `B` are induced by maps of
coefficient systems between the permutation local system and the constant system with fibre `R`:

* `p_* : C(E; R) ⟶ C(B; R)` is induced by the augmentation, which adds up the coefficients of all
  sheets (`IsCoveringMap.singularChainComplexPermutationIso_hom_comp_augmentation`);
* when the fibres are finite, the transfer `C(B; R) ⟶ C(E; R)` is induced by the map sending `r`
  to the sum of all sheets with coefficient `r`
  (`IsCoveringMap.transfer_comp_singularChainComplexPermutationIso_inv`).

These descriptions do not need the covering to be regular, so they describe the transfer of an
arbitrary finite covering through its permutation local system.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H, for homology with local coefficients and the local system of a covering space, and
  Section 3.G, for the transfer.
-/

public section

noncomputable section

open CategoryTheory Limits Simplicial TauCeti.TopCat TauCeti.LocalCoefficientSystem

universe u

namespace TauCeti.LocalCoefficientSystem

variable {E B : TopCat.{u}} {p : E ⟶ B} {n : SimplexCategoryᵒᵖ}

/-- The point of the fibre of `p` over the initial vertex of `p ∘ τ` through which a singular
simplex `τ` of `E` passes. For a covering map `p`, this is the sheet that determines the lift `τ`
of `p ∘ τ`. -/
abbrev initialSheet (τ : (TopCat.toSSet.obj E).obj n) :
    p ⁻¹' {(initialVertex ((TopCat.toSSet.map p).app n τ)).as} :=
  ⟨simplexMap τ (SimplexCategory.toTopInitialVertex n.unop), rfl⟩

end TauCeti.LocalCoefficientSystem

namespace IsCoveringMap

variable {E B : TopCat.{u}} {p : E ⟶ B} (hp : IsCoveringMap p) (R : Type u) [Ring R]
  {n : SimplexCategoryᵒᵖ}

/-- Monodromy along a path inside the image `p ∘ τ` of a singular simplex `τ` of `E` moves the
point of `τ` at the start of the path to the point of `τ` at its end. -/
theorem monodromy_pathTransport (τ : (TopCat.toSSet.obj E).obj n)
    (z w : SimplexCategory.toTop.{u}.obj n.unop) :
    hp.monodromy (pathTransport ((TopCat.toSSet.map p).app n τ) z w) ⟨simplexMap τ z, rfl⟩ =
      ⟨simplexMap τ w, rfl⟩ := by
  rw [← map_pathTransport]
  exact hp.monodromy_map _

/-- The lift of a singular simplex `σ` of `B` through the sheet `e` over its initial vertex. -/
private def liftSimplex (σ : (TopCat.toSSet.obj B).obj n)
    (e : p ⁻¹' {(initialVertex σ).as}) : (TopCat.toSSet.map p).app n ⁻¹' {σ} :=
  ((hp.bijOn_simplexMap_apply σ (SimplexCategory.toTopInitialVertex n.unop)).equiv _).symm e

private lemma liftSimplex_initialSheet (τ : (TopCat.toSSet.obj E).obj n) :
    (liftSimplex hp ((TopCat.toSSet.map p).app n τ) (initialSheet τ)).1 = τ :=
  -- Evaluating the lift `τ` at the initial vertex gives, by definition, its initial sheet.
  congrArg Subtype.val ((Equiv.symm_apply_eq _).2 rfl :
    liftSimplex hp ((TopCat.toSSet.map p).app n τ) (initialSheet τ) = ⟨τ, rfl⟩)

private lemma simplexMap_liftSimplex (σ : (TopCat.toSSet.obj B).obj n)
    (e : p ⁻¹' {(initialVertex σ).as}) :
    simplexMap (liftSimplex hp σ e).1
        (SimplexCategory.toTopInitialVertex n.unop) = e :=
  congrArg Subtype.val (Equiv.apply_symm_apply
    ((hp.bijOn_simplexMap_apply σ (SimplexCategory.toTopInitialVertex n.unop)).equiv _) e)

/-- The coefficients at the initial sheet of `τ` in the twisted summand of `p ∘ τ` are the
coefficients at the sheet `e` in the twisted summand of `σ`, whenever `p ∘ τ = σ` and `τ` passes
through `e`. -/
private lemma single_initialSheet_ιTwistedChainComplex {k : ℕ} {τ : (TopCat.toSSet.obj E) _⦋k⦌}
    {σ : (TopCat.toSSet.obj B) _⦋k⦌} (h : (TopCat.toSSet.map p).app _ τ = σ)
    {e : p ⁻¹' {(initialVertex σ).as}}
    (he : simplexMap τ (SimplexCategory.toTopInitialVertex _) = e) :
    hp.permutationLocalSystemSingle R _ (initialSheet τ) ≫
        ιTwistedChainComplex (hp.permutationLocalSystem R) k ((TopCat.toSSet.map p).app _ τ) =
      hp.permutationLocalSystemSingle R _ e ≫
        ιTwistedChainComplex (hp.permutationLocalSystem R) k σ := by
  subst h
  obtain rfl : initialSheet τ = e := Subtype.ext he
  rfl

/-- Reindexing a simplex `τ` of `E` along `α` moves its initial sheet by the monodromy along the
vertex transport of `p ∘ τ`. -/
private lemma single_initialSheet_map_vertexTransport {k l : ℕ} (α : ⦋l⦌ ⟶ ⦋k⦌)
    (τ : (TopCat.toSSet.obj E) _⦋k⦌) :
    hp.permutationLocalSystemSingle R _ (initialSheet τ) ≫
        (hp.permutationLocalSystem R).map (vertexTransport α.op ((TopCat.toSSet.map p).app _ τ)) ≫
          ιTwistedChainComplex (hp.permutationLocalSystem R) l
            ((TopCat.toSSet.obj B).map α.op ((TopCat.toSSet.map p).app _ τ)) =
      hp.permutationLocalSystemSingle R _ (initialSheet ((TopCat.toSSet.obj E).map α.op τ)) ≫
        ιTwistedChainComplex (hp.permutationLocalSystem R) l
          ((TopCat.toSSet.map p).app _ ((TopCat.toSSet.obj E).map α.op τ)) := by
  rw [hp.permutationLocalSystemSingle_map_assoc,
    vertexTransport_eq_mk _ _ (PathConnectedSpace.somePath _ _), ← pathTransport_eq_mk]
  exact (single_initialSheet_ιTwistedChainComplex hp R
    (NatTrans.naturality_apply (TopCat.toSSet.map p) α.op τ)
    (congrArg Subtype.val (hp.monodromy_pathTransport τ _ _)).symm).symm

/-- The component in degree `k` of the comparison: the summand of a simplex `τ` of `E` goes to the
coefficients at the initial sheet of `τ` in the twisted summand of `p ∘ τ`. -/
private def singularChainComplexPermutationHomX (k : ℕ) :
    ((TopCat.toSSet.obj E).chainComplex (ModuleCat.of R R)).X k ⟶
      (twistedChainComplex (hp.permutationLocalSystem R)).X k :=
  Cofan.IsColimit.desc ((TopCat.toSSet.obj E).isColimitChainComplexXCofan _ k) fun τ ↦
    hp.permutationLocalSystemSingle R _ (initialSheet τ) ≫
      ιTwistedChainComplex (hp.permutationLocalSystem R) k ((TopCat.toSSet.map p).app _ τ)

/-- The summand of a simplex `σ` of `B` in the inverse comparison: the coefficients at a sheet `e`
go to the summand of the lift of `σ` through `e`. -/
private def liftSum {k : ℕ} (σ : (TopCat.toSSet.obj B) _⦋k⦌) :
    (hp.permutationLocalSystem R).obj (initialVertex σ) ⟶
      ((TopCat.toSSet.obj E).chainComplex (ModuleCat.of R R)).X k :=
  ModuleCat.ofHom <| Finsupp.linearCombination R fun e ↦
    ((TopCat.toSSet.obj E).ιChainComplex (R := ModuleCat.of R R) (liftSimplex hp σ e).1).hom 1

private lemma single_liftSum {k : ℕ} (σ : (TopCat.toSSet.obj B) _⦋k⦌)
    (e : p ⁻¹' {(initialVertex σ).as}) :
    hp.permutationLocalSystemSingle R _ e ≫ liftSum hp R σ =
      (TopCat.toSSet.obj E).ιChainComplex (liftSimplex hp σ e).1 := by
  ext : 1
  -- Both sides are linear maps out of `R`, the left one `r ↦ linearCombination (single e r)`.
  exact LinearMap.ext_ring <|
    (congrArg (liftSum hp R σ).hom (hp.permutationLocalSystemSingle_hom_apply R _ e 1)).trans
      ((Finsupp.linearCombination_single R 1 e).trans (one_smul R _))

/-- The inverse component in degree `k` of the comparison. -/
private def singularChainComplexPermutationInvX (k : ℕ) :
    (twistedChainComplex (hp.permutationLocalSystem R)).X k ⟶
      ((TopCat.toSSet.obj E).chainComplex (ModuleCat.of R R)).X k :=
  Cofan.IsColimit.desc (isColimitTwistedChainComplexXCofan (hp.permutationLocalSystem R) k)
    (liftSum hp R)

@[reassoc]
private lemma ιChainComplex_singularChainComplexPermutationHomX {k : ℕ}
    (τ : (TopCat.toSSet.obj E) _⦋k⦌) :
    (TopCat.toSSet.obj E).ιChainComplex τ ≫ singularChainComplexPermutationHomX hp R k =
      hp.permutationLocalSystemSingle R _ (initialSheet τ) ≫
        ιTwistedChainComplex (hp.permutationLocalSystem R) k ((TopCat.toSSet.map p).app _ τ) :=
  Cofan.IsColimit.fac ((TopCat.toSSet.obj E).isColimitChainComplexXCofan _ k) _ τ

@[reassoc]
private lemma single_ιTwistedChainComplex_singularChainComplexPermutationInvX {k : ℕ}
    (σ : (TopCat.toSSet.obj B) _⦋k⦌) (e : p ⁻¹' {(initialVertex σ).as}) :
    hp.permutationLocalSystemSingle R _ e ≫
        ιTwistedChainComplex (hp.permutationLocalSystem R) k σ ≫
          singularChainComplexPermutationInvX hp R k =
      (TopCat.toSSet.obj E).ιChainComplex (liftSimplex hp σ e).1 := by
  have h : ιTwistedChainComplex (hp.permutationLocalSystem R) k σ ≫
      singularChainComplexPermutationInvX hp R k = liftSum hp R σ :=
    Cofan.IsColimit.fac (isColimitTwistedChainComplexXCofan (hp.permutationLocalSystem R) k) _ σ
  rw [h, single_liftSum]

/-- The degreewise isomorphism underlying the comparison. -/
private def singularChainComplexPermutationIsoX (k : ℕ) :
    ((TopCat.toSSet.obj E).chainComplex (ModuleCat.of R R)).X k ≅
      (twistedChainComplex (hp.permutationLocalSystem R)).X k where
  hom := singularChainComplexPermutationHomX hp R k
  inv := singularChainComplexPermutationInvX hp R k
  hom_inv_id := SSet.chainComplex_hom_ext fun τ ↦ by
    rw [ιChainComplex_singularChainComplexPermutationHomX_assoc,
      single_ιTwistedChainComplex_singularChainComplexPermutationInvX, liftSimplex_initialSheet]
    exact (Category.comp_id _).symm
  inv_hom_id := twistedChainComplex_hom_ext _ fun σ ↦ hp.permutationLocalSystem_hom_ext R fun e ↦ by
    rw [single_ιTwistedChainComplex_singularChainComplexPermutationInvX_assoc,
      ιChainComplex_singularChainComplexPermutationHomX, Category.comp_id]
    exact single_initialSheet_ιTwistedChainComplex hp R (liftSimplex hp σ e).2
      (simplexMap_liftSimplex hp σ e)

/-- **Singular chains of a covering space as twisted chains of the base**: the singular chain
complex of `E` with coefficients in `R` is isomorphic to the singular chain complex of `B` twisted
by the permutation local system of `p`. In degree `k`, a singular simplex `τ` of `E` corresponds to
the simplex `p ∘ τ` of `B` together with the sheet over its initial vertex through which `τ`
passes. -/
def singularChainComplexPermutationIso :
    (TopCat.toSSet.obj E).chainComplex (ModuleCat.of R R) ≅
      twistedChainComplex (hp.permutationLocalSystem R) :=
  HomologicalComplex.Hom.isoOfComponents (singularChainComplexPermutationIsoX hp R) <| by
    rintro _ k rfl
    refine SSet.chainComplex_hom_ext fun τ ↦ ?_
    -- Taking the faces of `τ` moves its initial sheet by monodromy inside `p ∘ τ`.
    dsimp only [singularChainComplexPermutationIsoX]
    rw [SSet.ιChainComplex_d_assoc, ιChainComplex_singularChainComplexPermutationHomX_assoc,
      ιTwistedChainComplex_d, Preadditive.sum_comp, Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
      ιChainComplex_singularChainComplexPermutationHomX]
    exact congrArg _ (single_initialSheet_map_vertexTransport hp R (SimplexCategory.δ i) τ)

/-- The comparison of singular chains of a covering space with twisted chains of the base sends
the summand of a simplex `τ` to the coefficients at the initial sheet of `τ` in the twisted summand
of `p ∘ τ`. -/
@[reassoc (attr := simp)]
lemma ιChainComplex_singularChainComplexPermutationIso_hom_f {k : ℕ}
    (τ : (TopCat.toSSet.obj E) _⦋k⦌) :
    (TopCat.toSSet.obj E).ιChainComplex τ ≫ (hp.singularChainComplexPermutationIso R).hom.f k =
      hp.permutationLocalSystemSingle R _ (initialSheet τ) ≫
        ιTwistedChainComplex (hp.permutationLocalSystem R) k ((TopCat.toSSet.map p).app _ τ) :=
  ιChainComplex_singularChainComplexPermutationHomX hp R τ

/-- The inverse comparison of singular chains of a covering space with twisted chains of the base
sends the coefficients at the initial sheet of `τ` in the twisted summand of `p ∘ τ` to the summand
of `τ`. -/
@[reassoc (attr := simp)]
lemma single_ιTwistedChainComplex_singularChainComplexPermutationIso_inv_f {k : ℕ}
    (τ : (TopCat.toSSet.obj E) _⦋k⦌) :
    hp.permutationLocalSystemSingle R _ (initialSheet τ) ≫
        ιTwistedChainComplex (hp.permutationLocalSystem R) k ((TopCat.toSSet.map p).app _ τ) ≫
          (hp.singularChainComplexPermutationIso R).inv.f k =
      (TopCat.toSSet.obj E).ιChainComplex τ := by
  rw [← ιChainComplex_singularChainComplexPermutationIso_hom_f_assoc,
    ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f, Category.comp_id]

/-- **Projection as a coefficient map**: under the comparison of singular chains of `E` with
chains of `B` twisted by the permutation local system, `p_* : C(E; R) ⟶ C(B; R)` is induced by the
augmentation of the permutation local system. -/
theorem singularChainComplexPermutationIso_hom_comp_augmentation :
    (hp.singularChainComplexPermutationIso R).hom ≫
        twistedChainComplexCoefficientMap (hp.permutationLocalSystemAugmentation R) ≫
          (twistedChainComplexConstantIso B (ModuleCat.of R R)).hom =
      SSet.chainComplexMap (TopCat.toSSet.map p) (ModuleCat.of R R) := by
  refine HomologicalComplex.hom_ext _ _ fun k ↦ SSet.chainComplex_hom_ext fun τ ↦ ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    ιChainComplex_singularChainComplexPermutationIso_hom_f_assoc,
    ιTwistedChainComplex_twistedChainComplexCoefficientMap_f_assoc,
    hp.permutationLocalSystemSingle_augmentation_app_assoc]
  exact (Category.id_comp _).trans <|
    (ιTwistedChainComplex_twistedChainComplexConstantIso_hom_f B _ k _).trans
      (SSet.ι_chainComplexMap_f _ _ (TopCat.toSSet.map p) (ModuleCat.of R R) τ).symm

/-- **The transfer as a coefficient map**: under the comparison of singular chains of `E` with
chains of `B` twisted by the permutation local system, the transfer `C(B; R) ⟶ C(E; R)` of a
covering with finite fibres is induced by the transfer of the permutation local system, which sends
`r` to the sum of all sheets with coefficient `r`. -/
theorem transfer_comp_singularChainComplexPermutationIso_inv (hfin : ∀ b, Finite ↥(p ⁻¹' {b})) :
    (twistedChainComplexConstantIso B (ModuleCat.of R R)).inv ≫
        twistedChainComplexCoefficientMap (hp.permutationLocalSystemTransfer R hfin) ≫
          (hp.singularChainComplexPermutationIso R).inv =
      hp.singularTransfer hfin (ModuleCat.of R R) := by
  classical
  refine HomologicalComplex.hom_ext _ _ fun k ↦ SSet.chainComplex_hom_ext fun σ ↦ ?_
  let := Fintype.ofFinite (p ⁻¹' {(initialVertex σ).as})
  have hconst : (TopCat.toSSet.obj B).ιChainComplex σ ≫
      (twistedChainComplexConstantIso B (ModuleCat.of R R)).inv.f k =
        ιTwistedChainComplex ((constantFunctor B).obj (ModuleCat.of R R)) k σ :=
    ι_twistedChainComplexConstantIso_inv_f B _ k σ
  have key : ιTwistedChainComplex ((constantFunctor B).obj (ModuleCat.of R R)) k σ ≫
      (twistedChainComplexCoefficientMap (hp.permutationLocalSystemTransfer R hfin)).f k ≫
        (hp.singularChainComplexPermutationIso R).inv.f k =
      ∑ τ ∈ (hp.finite_preimage_singleton_toSSet_map_app hfin σ).toFinset,
        (TopCat.toSSet.obj E).ιChainComplex τ := by
    rw [ιTwistedChainComplex_twistedChainComplexCoefficientMap_f_assoc,
      hp.permutationLocalSystemTransfer_app R hfin]
    refine (Preadditive.sum_comp _ _ _).trans ?_
    -- The sheets over the initial vertex of `σ` correspond to the lifts of `σ`.
    refine Finset.sum_bij (fun e _ ↦ (liftSimplex hp σ e).1) (fun e _ ↦ ?_)
      (fun e₁ _ e₂ _ h ↦ ?_) (fun τ hτ ↦ ?_)
      fun e _ ↦ single_ιTwistedChainComplex_singularChainComplexPermutationInvX hp R σ e
    · exact (Set.Finite.mem_toFinset _).2 (liftSimplex hp σ e).2
    · exact (Equiv.injective _) (Subtype.ext h)
    · refine ⟨_, Finset.mem_univ _, congrArg Subtype.val
        (((hp.bijOn_simplexMap_apply σ _).equiv _).symm_apply_apply ⟨τ, ?_⟩)⟩
      exact (Set.Finite.mem_toFinset _).1 hτ
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ιChainComplex_singularTransfer_f]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hconst).trans key)

/-- **Singular homology of a covering space as twisted homology of the base**: the singular
homology of `E` with coefficients in `R` is isomorphic to the singular homology of `B` with
coefficients in the permutation local system of `p`. -/
def singularHomologyPermutationIso (k : ℕ) :
    (TopCat.toSSet.obj E).homology (ModuleCat.of R R) k ≅
      twistedHomology (hp.permutationLocalSystem R) k :=
  (HomologicalComplex.homologyFunctor _ _ k).mapIso (hp.singularChainComplexPermutationIso R)

/-- The comparison of singular homology of a covering space with twisted homology of the base is
induced by the comparison of chain complexes. -/
lemma singularHomologyPermutationIso_hom (k : ℕ) :
    (hp.singularHomologyPermutationIso R k).hom =
      HomologicalComplex.homologyMap (hp.singularChainComplexPermutationIso R).hom k :=
  (rfl)

/-- The inverse comparison of singular homology of a covering space with twisted homology of the
base is induced by the inverse comparison of chain complexes. -/
lemma singularHomologyPermutationIso_inv (k : ℕ) :
    (hp.singularHomologyPermutationIso R k).inv =
      HomologicalComplex.homologyMap (hp.singularChainComplexPermutationIso R).inv k :=
  (rfl)

/-- **Projection as a coefficient map**, on homology: under the comparison of singular homology
of `E` with homology of `B` twisted by the permutation local system, `p_*` is induced by the
augmentation of the permutation local system. -/
theorem singularHomologyPermutationIso_hom_comp_augmentation (k : ℕ) :
    (hp.singularHomologyPermutationIso R k).hom ≫
        twistedHomologyCoefficientMap (hp.permutationLocalSystemAugmentation R) k ≫
          (twistedHomologyConstantIso B (ModuleCat.of R R) k).hom =
      SSet.homologyMap (TopCat.toSSet.map p) (ModuleCat.of R R) k := by
  have h := congrArg (HomologicalComplex.homologyMap · k)
    (hp.singularChainComplexPermutationIso_hom_comp_augmentation R)
  simp only [HomologicalComplex.homologyMap_comp] at h
  rw [singularHomologyPermutationIso_hom, twistedHomologyConstantIso_hom]
  exact h

/-- **The transfer as a coefficient map**, on homology: under the comparison of singular homology
of `E` with homology of `B` twisted by the permutation local system, the transfer of a covering
with finite fibres is induced by the transfer of the permutation local system. -/
theorem transfer_comp_singularHomologyPermutationIso_inv (hfin : ∀ b, Finite ↥(p ⁻¹' {b}))
    (k : ℕ) :
    (twistedHomologyConstantIso B (ModuleCat.of R R) k).inv ≫
        twistedHomologyCoefficientMap (hp.permutationLocalSystemTransfer R hfin) k ≫
          (hp.singularHomologyPermutationIso R k).inv =
      HomologicalComplex.homologyMap (hp.singularTransfer hfin (ModuleCat.of R R)) k := by
  have h := congrArg (HomologicalComplex.homologyMap · k)
    (hp.transfer_comp_singularChainComplexPermutationIso_inv R hfin)
  simp only [HomologicalComplex.homologyMap_comp] at h
  rw [singularHomologyPermutationIso_inv, twistedHomologyConstantIso_inv]
  exact h

end IsCoveringMap
