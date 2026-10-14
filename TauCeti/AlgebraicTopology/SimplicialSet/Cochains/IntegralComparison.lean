/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Cochains.Basic

/-!
# Integral comparison for simplicial cochains

Cochains `Hom_k(C_*(K; k), M)` and `Hom_ℤ(C_*(K; ℤ), M)` are isomorphic as complexes of
abelian groups: both are functions on simplices with the alternating-face differential.
The comparison preserves simplex values and is natural in simplicial maps. It applies to
noncommutative rings, without flatness or projectivity. We use `TauCeti.cochainValuesEquiv`
to identify the two complexes rather than choosing chain representatives.

Simplicial sets and modules are small, so the regular integral coefficient object can be
used without lifting. The scalar ring of the two cochain complexes is `ℤ`.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.1.
-/

public section

noncomputable section

open CategoryTheory Limits SSet
open scoped Simplicial

namespace TauCeti

variable (k : Type) [Ring k] (M : ModuleCat.{0} k) (K : SSet.{0})

/-- Simplicial cochains over `k` with values in `M` agree with integral cochains with values
in the underlying abelian group of `M`. The comparison preserves simplex values. -/
def simplicialCochainComplexIntegralIso :
    (K.chainComplex (ModuleCat.of k k)).linearYonedaObj ℤ M ≅
      (K.chainComplex (ModuleCat.of ℤ ℤ)).linearYonedaObj ℤ (ModuleCat.of ℤ M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ((cochainValuesEquiv k M K n).trans
      (cochainValuesEquiv ℤ (ModuleCat.of ℤ M) K n).symm).toModuleIso) fun i j hij ↦ by
    have h : i + 1 = j := hij
    subst j
    have comm (φ : (K.chainComplex (ModuleCat.of k k)).X i ⟶ M) :
        (K.chainComplex (ModuleCat.of ℤ ℤ)).d (i + 1) i ≫
            (cochainValuesEquiv ℤ (ModuleCat.of ℤ M) K i).symm
              (cochainValuesEquiv k M K i φ) =
          (cochainValuesEquiv ℤ (ModuleCat.of ℤ M) K (i + 1)).symm
            (cochainValuesEquiv k M K (i + 1)
              ((K.chainComplex (ModuleCat.of k k)).d (i + 1) i ≫ φ)) := by
      apply (cochainValuesEquiv ℤ (ModuleCat.of ℤ M) K (i + 1)).injective
      funext σ
      simp only [cochainValuesEquiv_d, LinearEquiv.apply_symm_apply]
    ext φ
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply,
      TauCeti.ChainComplex.linearYonedaObj_d_apply,
      TauCeti.ChainComplex.linearYonedaObj_d_apply]
    exact comm φ

/-- The degreewise integral comparison extends the simplex values integrally. -/
lemma simplicialCochainComplexIntegralIso_hom_f_apply (n : ℕ)
    (φ : ((K.chainComplex (ModuleCat.of k k)).linearYonedaObj ℤ M).X n) :
    (simplicialCochainComplexIntegralIso k M K).hom.f n φ =
      (cochainValuesEquiv ℤ (ModuleCat.of ℤ M) K n).symm (cochainValuesEquiv k M K n φ) :=
  (rfl)

/-- The inverse degreewise comparison extends the same simplex values over `k`. -/
lemma simplicialCochainComplexIntegralIso_inv_f_apply (n : ℕ)
    (φ : ((K.chainComplex (ModuleCat.of ℤ ℤ)).linearYonedaObj ℤ (ModuleCat.of ℤ M)).X n) :
    (simplicialCochainComplexIntegralIso k M K).inv.f n φ =
      (cochainValuesEquiv k M K n).symm (cochainValuesEquiv ℤ (ModuleCat.of ℤ M) K n φ) :=
  (rfl)

/-- The integral comparison sends a cochain to the integral cochain with the same simplex
values. -/
lemma cochainValuesEquiv_simplicialCochainComplexIntegralIso_hom (n : ℕ)
    (φ : ((K.chainComplex (ModuleCat.of k k)).linearYonedaObj ℤ M).X n) (σ : K _⦋n⦌) :
    cochainValuesEquiv ℤ (ModuleCat.of ℤ M) K n
        ((simplicialCochainComplexIntegralIso k M K).hom.f n φ) σ =
      cochainValuesEquiv k M K n φ σ := by
  rw [simplicialCochainComplexIntegralIso_hom_f_apply, LinearEquiv.apply_symm_apply]

/-- The inverse integral comparison also preserves simplex values. -/
lemma cochainValuesEquiv_simplicialCochainComplexIntegralIso_inv (n : ℕ)
    (φ : ((K.chainComplex (ModuleCat.of ℤ ℤ)).linearYonedaObj ℤ (ModuleCat.of ℤ M)).X n)
    (σ : K _⦋n⦌) :
    cochainValuesEquiv k M K n ((simplicialCochainComplexIntegralIso k M K).inv.f n φ) σ =
      cochainValuesEquiv ℤ (ModuleCat.of ℤ M) K n φ σ := by
  rw [simplicialCochainComplexIntegralIso_inv_f_apply, LinearEquiv.apply_symm_apply]

/-- The integral comparison evaluates a simplex chain by integral scalar multiplication of
its original value on the unit simplex chain. -/
-- Simplify before descending into the Yoneda component, whose cochain carrier is opaque.
@[simp↓]
lemma simplicialCochainComplexIntegralIso_hom_f_apply_ιChainComplex (n : ℕ)
    (φ : ((K.chainComplex (ModuleCat.of k k)).linearYonedaObj ℤ M).X n)
    (σ : K _⦋n⦌) (a : ℤ) :
    ConcreteCategory.hom (X := (K.chainComplex (ModuleCat.of ℤ ℤ)).X n)
        (Y := ModuleCat.of ℤ M) ((simplicialCochainComplexIntegralIso k M K).hom.f n φ)
        (K.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ a) =
      a • ConcreteCategory.hom (X := (K.chainComplex (ModuleCat.of k k)).X n) (Y := M) φ
        (K.ιChainComplex (R := ModuleCat.of k k) σ 1) := by
  rw [simplicialCochainComplexIntegralIso_hom_f_apply, cochainValuesEquiv_symm_apply]
  exact congrArg (a • ·) (cochainValuesEquiv_apply k M K n φ σ)

/-- The inverse comparison evaluates a simplex chain by scalar multiplication over `k` of
its integral value on the unit simplex chain. -/
-- Simplify before descending into the Yoneda component, whose cochain carrier is opaque.
@[simp↓]
lemma simplicialCochainComplexIntegralIso_inv_f_apply_ιChainComplex (n : ℕ)
    (φ : ((K.chainComplex (ModuleCat.of ℤ ℤ)).linearYonedaObj ℤ (ModuleCat.of ℤ M)).X n)
    (σ : K _⦋n⦌) (a : k) :
    ConcreteCategory.hom (X := (K.chainComplex (ModuleCat.of k k)).X n) (Y := M)
        ((simplicialCochainComplexIntegralIso k M K).inv.f n φ)
        (K.ιChainComplex (R := ModuleCat.of k k) σ a) =
      a • ConcreteCategory.hom (X := (K.chainComplex (ModuleCat.of ℤ ℤ)).X n)
        (Y := ModuleCat.of ℤ M) φ (K.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ 1) := by
  rw [simplicialCochainComplexIntegralIso_inv_f_apply, cochainValuesEquiv_symm_apply]
  exact congrArg (a • ·) (cochainValuesEquiv_apply ℤ (ModuleCat.of ℤ M) K n φ σ)

/-- The integral cochain comparison is natural in maps of simplicial sets. -/
@[reassoc]
lemma simplicialCochainComplexIntegralIso_hom_naturality {L : SSet.{0}} (f : K ⟶ L) :
    cochainComplexMap (R := ModuleCat.of k k) (k := ℤ) (M := M) f ≫
        (simplicialCochainComplexIntegralIso k M K).hom =
      (simplicialCochainComplexIntegralIso k M L).hom ≫
        cochainComplexMap (R := ModuleCat.of ℤ ℤ) (k := ℤ) (M := ModuleCat.of ℤ M) f := by
  -- Prove the square on raw cochains, then use the component computation rules.
  have comm (n : ℕ) (φ : (L.chainComplex (ModuleCat.of k k)).X n ⟶ M) :
      (cochainValuesEquiv ℤ (ModuleCat.of ℤ M) K n).symm
          (cochainValuesEquiv k M K n ((chainComplexMap f (ModuleCat.of k k)).f n ≫ φ)) =
        (chainComplexMap f (ModuleCat.of ℤ ℤ)).f n ≫
          (cochainValuesEquiv ℤ (ModuleCat.of ℤ M) L n).symm
            (cochainValuesEquiv k M L n φ) := by
    apply (cochainValuesEquiv ℤ (ModuleCat.of ℤ M) K n).injective
    funext σ
    simp only [LinearEquiv.apply_symm_apply, cochainValuesEquiv_chainComplexMap]
  ext n φ
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  change ((cochainComplexMap f).f n ≫
      (simplicialCochainComplexIntegralIso k M K).hom.f n) φ =
    ((simplicialCochainComplexIntegralIso k M L).hom.f n ≫
      (cochainComplexMap f).f n) φ
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply,
    simplicialCochainComplexIntegralIso_hom_f_apply,
    SSet.cochainComplexMap_f_apply, SSet.cochainComplexMap_f_apply,
    simplicialCochainComplexIntegralIso_hom_f_apply]
  exact comm n φ

end TauCeti
