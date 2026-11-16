/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Action
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation

/-!
# Conjugation on component groups of closed subgroups

Over an algebraically closed field `k`, conjugating a closed subgroup `N = V(I)` of a finite-type
affine group `G = Spec H` by a rational point `g ∈ G(k)` induces a group isomorphism
`π₀(N) ≃* π₀(g N g⁻¹)` (`TauCeti.FiniteTypeCommHopfAlgCat.componentGroupConjugationEquiv`).

This file builds that isomorphism from the Hopf-algebra conjugation equivalence
`HopfIdeal.quotientConjugationEquiv`, computes its action on rational-point classes
`[x] ↦ [g x g⁻¹]`, proves functoriality in `g` (`1`, products, inverses), compatibility with the
ambient component-group inclusion and nested subgroup inclusions, and shows that self-conjugation
by a point of `N(k)` acts by inner conjugation in `π₀(N)` (hence trivially for `g ∈ N°(k)`).

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupConjugationEquiv`: conjugation isomorphism
  `π₀(V(I)) ≃* π₀(V(J))` when `J = I.conjugate g`.
* `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupConjugationEquiv_subgroupComponentMap`: action on
  rational-point classes `[x] ↦ [g x g⁻¹]`.
* `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupConjugationEquiv_mul` and
  `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupConjugationEquiv_self_eq_conj`: functoriality in
  `g` and inner action on self-conjugation.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37 and §5.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §6.1.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (H : FiniteTypeCommHopfAlgCat.{u, u} k)

/-- Conjugation by a rational point `g ∈ G(k)` induces a group isomorphism between the component
groups of a closed subgroup `V(I)` and its conjugate `V(J)` (`J = I.conjugate g`). -/
noncomputable def componentGroupConjugationEquiv (I J : HopfIdeal k H)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (hJ : J = I.conjugate g) :
    ConnectedComponents (PrimeSpectrum (quotient H I)) ≃*
      ConnectedComponents (PrimeSpectrum (quotient H J)) where
  toFun := mapComponentGroup
    (ofHom (I.quotientConjugationEquiv J g hJ).toBialgHom : quotient H J ⟶ quotient H I)
  invFun := mapComponentGroup
    (ofHom (I.quotientConjugationEquiv J g hJ).symm.toBialgHom : quotient H I ⟶ quotient H J)
  left_inv C := by
    have hcomp :
        (ofHom (I.quotientConjugationEquiv J g hJ).symm.toBialgHom :
            quotient H I ⟶ quotient H J) ≫
          ofHom (I.quotientConjugationEquiv J g hJ).toBialgHom =
        𝟙 (quotient H I) := by
      ext q
      exact (I.quotientConjugationEquiv J g hJ).apply_symm_apply q
    have h : (mapComponentGroup (ofHom (I.quotientConjugationEquiv J g hJ).symm.toBialgHom :
          quotient H I ⟶ quotient H J)).comp
        (mapComponentGroup (ofHom (I.quotientConjugationEquiv J g hJ).toBialgHom :
          quotient H J ⟶ quotient H I)) = MonoidHom.id _ := by
      rw [← mapComponentGroup_comp, hcomp, mapComponentGroup_id]
    exact DFunLike.congr_fun h C
  right_inv C := by
    have hcomp :
        (ofHom (I.quotientConjugationEquiv J g hJ).toBialgHom :
            quotient H J ⟶ quotient H I) ≫
          ofHom (I.quotientConjugationEquiv J g hJ).symm.toBialgHom =
        𝟙 (quotient H J) := by
      ext q
      exact (I.quotientConjugationEquiv J g hJ).symm_apply_apply q
    have h : (mapComponentGroup (ofHom (I.quotientConjugationEquiv J g hJ).toBialgHom :
          quotient H J ⟶ quotient H I)).comp
        (mapComponentGroup (ofHom (I.quotientConjugationEquiv J g hJ).symm.toBialgHom :
          quotient H I ⟶ quotient H J)) = MonoidHom.id _ := by
      rw [← mapComponentGroup_comp, hcomp, mapComponentGroup_id]
    exact DFunLike.congr_fun h C
  map_mul' := (mapComponentGroup (ofHom (I.quotientConjugationEquiv J g hJ).toBialgHom :
    quotient H J ⟶ quotient H I)).map_mul

omit [IsAlgClosed k] in
/-- Conjugating a rational point of `V(I)` by `g` lands in `V(J)` when `J = I.conjugate g`. -/
theorem conj_mem_quotientPointsSubgroup_of_eq_conjugate (I J : HopfIdeal k H)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (hJ : J = I.conjugate g)
    {x : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)}
    (hx : x ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    g * x * g⁻¹ ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of k k) := by
  subst hJ
  have hconj :
      BialgHom.mapDomain (A := k) (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom x =
        g * x * g⁻¹ := by
    simpa only [Algebra.ofId_self, AlgHom.mapValue_id, MonoidHom.id_apply] using
      HopfAlgebra.mapDomain_pointConjugationBialgEquiv (R := k) (H := H) (A := k) g x
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hx ⊢
  intro h hh
  have hpt : (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom h =
      HopfAlgebra.pointConjugationAlgHom g h :=
    AlgHom.congr_fun (HopfAlgebra.pointConjugationBialgEquiv_toAlgHom g) h
  rw [← hconj, BialgHom.mapDomain_apply_apply, hpt]
  exact hx _ (HopfIdeal.mem_conjugate.mp hh)

/-- On rational-point classes, `componentGroupConjugationEquiv` acts by conjugation
`[x] ↦ [g x g⁻¹]`. -/
@[simp]
theorem componentGroupConjugationEquiv_subgroupComponentMap (I J : HopfIdeal k H)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (hJ : J = I.conjugate g)
    (x : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    componentGroupConjugationEquiv H I J g hJ (subgroupComponentMap H I x) =
      subgroupComponentMap H J
        ⟨g * x.1 * g⁻¹,
          conj_mem_quotientPointsSubgroup_of_eq_conjugate H I J g hJ x.2⟩ := by
  obtain ⟨q, rfl⟩ := (quotientPointsSubgroupMulEquiv H I (CommAlgCat.of k k)).surjective x
  rw [subgroupComponentMap_quotientPointsSubgroupMulEquiv]
  -- Expose `mapComponentGroup` in the definition of `componentGroupConjugationEquiv`.
  change mapComponentGroup
      (ofHom (I.quotientConjugationEquiv J g hJ).toBialgHom : quotient H J ⟶ quotient H I)
      (rationalComponentMap (quotient H I) q) = _
  rw [mapComponentGroup_rationalComponentMap]
  let q' : HopfAlgebra.points (R := k) (H := quotient H J) (CommAlgCat.of k k) :=
    BialgHom.mapDomain (A := k) (I.quotientConjugationEquiv J g hJ).toBialgHom q
  have hval : CommHopfAlgCat.quotientPointsHom H.obj J (CommAlgCat.of k k) q' =
      g * (quotientPointsSubgroupMulEquiv H I (CommAlgCat.of k k) q).1 * g⁻¹ := by
    rw [quotientPointsSubgroupMulEquiv_apply_val]
    have hconj :
        BialgHom.mapDomain (A := k) (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom
          (CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) q) =
        g * CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) q * g⁻¹ := by
      simpa only [Algebra.ofId_self, AlgHom.mapValue_id, MonoidHom.id_apply] using
        HopfAlgebra.mapDomain_pointConjugationBialgEquiv (R := k) (H := H) (A := k) g
          (CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) q)
    rw [← hconj]
    apply WithConv.ofConv_injective
    ext h
    have hpt : (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom h =
        HopfAlgebra.pointConjugationAlgHom g h :=
      AlgHom.congr_fun (HopfAlgebra.pointConjugationBialgEquiv_toAlgHom g) h
    rw [CommHopfAlgCat.quotientPointsHom_apply_apply, Ideal.Quotient.mkₐ_eq_mk]
    dsimp only [q']
    rw [BialgHom.mapDomain_apply_apply, BialgHom.mapDomain_apply_apply,
      BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_toBialgHom,
      HopfIdeal.quotientConjugationEquiv_mk, CommHopfAlgCat.quotientPointsHom_apply_apply,
      Ideal.Quotient.mkₐ_eq_mk, hpt]
  have hsub :
      (⟨g * (quotientPointsSubgroupMulEquiv H I (CommAlgCat.of k k) q).1 * g⁻¹,
        conj_mem_quotientPointsSubgroup_of_eq_conjugate H I J g hJ
          (quotientPointsSubgroupMulEquiv H I (CommAlgCat.of k k) q).2⟩ :
        CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of k k)) =
      ⟨CommHopfAlgCat.quotientPointsHom H.obj J (CommAlgCat.of k k) q',
        CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H.obj J _ q'⟩ :=
    Subtype.ext hval.symm
  rw [hsub, subgroupComponentMap_quotientPointsHom]
  rfl

/-- Conjugation by the identity point induces the identity automorphism on `π₀(V(I))`. -/
@[simp]
theorem componentGroupConjugationEquiv_one (I : HopfIdeal k H) :
    componentGroupConjugationEquiv H I I 1 (HopfIdeal.conjugate_one I).symm =
      MulEquiv.refl _ := by
  ext C
  obtain ⟨x, rfl⟩ := subgroupComponentMap_surjective H I C
  rw [componentGroupConjugationEquiv_subgroupComponentMap]
  simp

/-- Successive conjugations compose covariantly on component groups. -/
theorem componentGroupConjugationEquiv_mul (I J K : HopfIdeal k H)
    (g h : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (hJ : J = I.conjugate h) (hK : K = J.conjugate g) :
    componentGroupConjugationEquiv H I K (g * h) (by rw [hK, hJ, HopfIdeal.conjugate_mul]) =
      (componentGroupConjugationEquiv H I J h hJ).trans
        (componentGroupConjugationEquiv H J K g hK) := by
  ext C
  obtain ⟨x, rfl⟩ := subgroupComponentMap_surjective H I C
  rw [MulEquiv.trans_apply, componentGroupConjugationEquiv_subgroupComponentMap,
    componentGroupConjugationEquiv_subgroupComponentMap,
    componentGroupConjugationEquiv_subgroupComponentMap]
  congr 1
  apply Subtype.ext
  simp [mul_assoc]

/-- The inverse of `componentGroupConjugationEquiv` is conjugation by `g⁻¹`. -/
@[simp]
theorem componentGroupConjugationEquiv_symm (I J : HopfIdeal k H)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (hJ : J = I.conjugate g) :
    (componentGroupConjugationEquiv H I J g hJ).symm =
      componentGroupConjugationEquiv H J I g⁻¹
        (by rw [hJ, HopfIdeal.conjugate_inv_conjugate]) := by
  apply MulEquiv.symm_bijective.injective
  ext C
  obtain ⟨x, rfl⟩ := subgroupComponentMap_surjective H I C
  apply (componentGroupConjugationEquiv H J I g⁻¹
    (by rw [hJ, HopfIdeal.conjugate_inv_conjugate])).injective
  rw [MulEquiv.symm_symm, MulEquiv.apply_symm_apply,
    componentGroupConjugationEquiv_subgroupComponentMap,
    componentGroupConjugationEquiv_subgroupComponentMap]
  congr 1
  apply Subtype.ext
  simp [mul_assoc]

/-- Conjugation on a closed subgroup's component group commutes with inclusion into `π₀(G)` via
inner conjugation by the ambient component `[g] ∈ π₀(G)`. -/
theorem mapComponentGroup_mkQuotient_componentGroupConjugationEquiv (I J : HopfIdeal k H)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (hJ : J = I.conjugate g)
    (C : ConnectedComponents (PrimeSpectrum (quotient H I))) :
    mapComponentGroup (mkQuotient H J) (componentGroupConjugationEquiv H I J g hJ C) =
      MulAut.conj (rationalComponentMap H g) (mapComponentGroup (mkQuotient H I) C) := by
  obtain ⟨x, rfl⟩ := subgroupComponentMap_surjective H I C
  rw [componentGroupConjugationEquiv_subgroupComponentMap,
    mapComponentGroup_mkQuotient_subgroupComponentMap,
    mapComponentGroup_mkQuotient_subgroupComponentMap,
    MulAut.conj_apply, map_mul, map_mul, map_inv]

/-- Self-conjugation by a rational point `g ∈ V(I)(k)` acts on `π₀(V(I))` by inner conjugation
by `[g] ∈ π₀(V(I))`. -/
theorem componentGroupConjugationEquiv_self_eq_conj (I : HopfIdeal k H)
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    componentGroupConjugationEquiv H I I g.1
        (HopfIdeal.conjugate_eq_self_of_mem_quotientPointsSubgroup I g.2).symm =
      MulAut.conj (subgroupComponentMap H I g) := by
  ext C
  obtain ⟨x, rfl⟩ := subgroupComponentMap_surjective H I C
  rw [componentGroupConjugationEquiv_subgroupComponentMap, MulAut.conj_apply,
    ← map_inv, ← map_mul, ← map_mul]
  rfl

/-- Self-conjugation by a rational point in the identity component `V(I)°(k)` acts trivially on
`π₀(V(I))`. -/
theorem componentGroupConjugationEquiv_self_eq_refl_of_mem_identityComponent (I : HopfIdeal k H)
    {g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)}
    (hg : g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent
      (CommAlgCat.of k k)) :
    componentGroupConjugationEquiv H I I g
        (HopfIdeal.conjugate_eq_self_of_mem_quotientPointsSubgroup I
          (CommHopfAlgCat.quotientPointsSubgroup_le_of_le H.obj
            (HopfIdeal.le_identityComponent I) _ hg)).symm =
      MulEquiv.refl _ := by
  let gI : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) :=
    ⟨g, CommHopfAlgCat.quotientPointsSubgroup_le_of_le H.obj
      (HopfIdeal.le_identityComponent I) _ hg⟩
  have h1 : subgroupComponentMap H I gI = 1 :=
    (subgroupComponentMap_eq_one_iff H I gI).mpr hg
  rw [componentGroupConjugationEquiv_self_eq_conj H I gI, h1, map_one]
  rfl

/-- Conjugation is natural with respect to nested closed-subgroup inclusions `V(I₂) ⊆ V(I₁)`. -/
theorem mapComponentGroup_quotientMapOfLe_componentGroupConjugationEquiv
    {I₁ I₂ J₁ J₂ : HopfIdeal k H} (hI : I₁ ≤ I₂)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (hJ₁ : J₁ = I₁.conjugate g) (hJ₂ : J₂ = I₂.conjugate g)
    (C : ConnectedComponents (PrimeSpectrum (quotient H I₂))) :
    mapComponentGroup (quotientMapOfLe H (by rw [hJ₁, hJ₂]; exact HopfIdeal.conjugate_mono g hI))
        (componentGroupConjugationEquiv H I₂ J₂ g hJ₂ C) =
      componentGroupConjugationEquiv H I₁ J₁ g hJ₁
        (mapComponentGroup (quotientMapOfLe H hI) C) := by
  obtain ⟨x, rfl⟩ := subgroupComponentMap_surjective H I₂ C
  rw [componentGroupConjugationEquiv_subgroupComponentMap,
    mapComponentGroup_quotientMapOfLe_subgroupComponentMap,
    mapComponentGroup_quotientMapOfLe_subgroupComponentMap,
    componentGroupConjugationEquiv_subgroupComponentMap]

end TauCeti.FiniteTypeCommHopfAlgCat
