/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Cochains.Basic
import TauCeti.Algebra.Homology.Kronecker

/-!
# Integral comparison for simplicial cochains

Cochains `Hom_k(C_*(K; k), M)` and `Hom_ℤ(C_*(K; ℤ), M)` are isomorphic as complexes of
abelian groups: both are functions on simplices with the alternating-face differential.
The comparison preserves simplex values and is natural in simplicial maps. It applies to
noncommutative rings, without flatness or projectivity. We use `TauCeti.cochainValuesEquiv`
to identify the two complexes rather than choosing chain representatives.

Simplicial sets and modules are small, so the regular integral coefficient object can be
used without lifting. The scalar ring of the two cochain complexes is `ℤ`. Transporting simplex
values from `M` to `ModuleCat.of ℤ M` commutes with the coboundary
(`TauCeti.cochainValuesEquiv_symm_cochainValuesEquiv_d_comp`). For a `k`-module `V` which is an
injective abelian group, every morphism `H_p(K; ℤ) ⟶ V` is the evaluation on integral cycles of a
cocycle over `k` (`TauCeti.exists_cocycle_iCycles_comp_eq`).

## References

* A. Hatcher, *Algebraic Topology*, Section 3.1.
-/

public section

noncomputable section

open CategoryTheory Limits SSet
open scoped Simplicial

namespace TauCeti

variable (k : Type) [Ring k] (M : ModuleCat.{0} k) (K : SSet.{0})

/-- Transporting simplex values from cochains over `k` to integral cochains commutes with the
coboundary: the integral cochain with the values of `φ ∘ d` is `d` followed by the integral cochain
with the values of `φ`. -/
lemma cochainValuesEquiv_symm_cochainValuesEquiv_d_comp (i j : ℕ)
    (φ : (K.chainComplex (ModuleCat.of k k)).X j ⟶ M) :
    (cochainValuesEquiv ℤ (ModuleCat.of ℤ M) K i).symm
        (cochainValuesEquiv k M K i ((K.chainComplex (ModuleCat.of k k)).d i j ≫ φ)) =
      (K.chainComplex (ModuleCat.of ℤ ℤ)).d i j ≫
        (cochainValuesEquiv ℤ (ModuleCat.of ℤ M) K j).symm (cochainValuesEquiv k M K j φ) := by
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · obtain rfl : i = j + 1 := hij.symm
    apply (cochainValuesEquiv ℤ (ModuleCat.of ℤ M) K (j + 1)).injective
    funext σ
    simp only [cochainValuesEquiv_d, LinearEquiv.apply_symm_apply]
  · rw [(K.chainComplex _).shape i j hij, (K.chainComplex _).shape i j hij, zero_comp, zero_comp,
      map_zero, map_zero]

/-- Simplicial cochains over `k` with values in `M` agree with integral cochains with values
in the underlying abelian group of `M`. The comparison preserves simplex values. -/
def simplicialCochainComplexIntegralIso :
    (K.chainComplex (ModuleCat.of k k)).linearYonedaObj ℤ M ≅
      (K.chainComplex (ModuleCat.of ℤ ℤ)).linearYonedaObj ℤ (ModuleCat.of ℤ M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ((cochainValuesEquiv k M K n).trans
      (cochainValuesEquiv ℤ (ModuleCat.of ℤ M) K n).symm).toModuleIso) fun i j _ ↦ by
    ext φ
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply,
      TauCeti.ChainComplex.linearYonedaObj_d_apply,
      TauCeti.ChainComplex.linearYonedaObj_d_apply]
    exact (cochainValuesEquiv_symm_cochainValuesEquiv_d_comp k M K j i φ).symm

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
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply,
    simplicialCochainComplexIntegralIso_hom_f_apply,
    SSet.cochainComplexMap_f_apply, SSet.cochainComplexMap_f_apply,
    simplicialCochainComplexIntegralIso_hom_f_apply]
  exact comm n φ

section Values

variable (V : Type) [AddCommGroup V] [Module k V]

/-- For a `k`-module `V` which is an injective abelian group, every morphism
`f : H_p(K; ℤ) ⟶ V` is the evaluation on integral cycles of a cocycle `b` over `k`: the integral
cochain with the simplex values of `b` restricts on the cycles to `f`. This is the surjectivity of
the Kronecker map for the injective coefficient object `V`
(`TauCeti.ChainComplex.kronecker_bijective`), transported along simplex values from integral
cochains to cochains over `k`. -/
lemma exists_cocycle_iCycles_comp_eq [Injective (ModuleCat.of ℤ V)] (p : ℕ)
    (f : (K.chainComplex (ModuleCat.of ℤ ℤ)).homology p ⟶ ModuleCat.of ℤ V) :
    ∃ b : (K.chainComplex (ModuleCat.of k k)).X p ⟶ ModuleCat.of k V,
      (K.chainComplex (ModuleCat.of k k)).d ((ComplexShape.up ℕ).next p) p ≫ b = 0 ∧
      (K.chainComplex (ModuleCat.of ℤ ℤ)).iCycles p ≫
          (cochainValuesEquiv ℤ (ModuleCat.of ℤ V) K p).symm
            (cochainValuesEquiv k (ModuleCat.of k V) K p b) =
        (K.chainComplex (ModuleCat.of ℤ ℤ)).homologyπ p ≫ f := by
  -- `f` is the evaluation of the class of an integral cocycle `a`.
  obtain ⟨x, hx⟩ := (ChainComplex.kronecker_bijective (k := ℤ)
    (X := K.chainComplex (ModuleCat.of ℤ ℤ)) (Y := ModuleCat.of ℤ V) p).2 f
  obtain ⟨ψ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p x
  -- Name the underlying cochain with its morphism type, so that composites with it can be
  -- rewritten.
  obtain ⟨a, ha⟩ : ∃ a : (K.chainComplex (ModuleCat.of ℤ ℤ)).X p ⟶ ModuleCat.of ℤ V,
      ((K.chainComplex (ModuleCat.of ℤ ℤ)).linearYonedaObj ℤ (ModuleCat.of ℤ V)).iCycles p ψ =
        a := ⟨_, rfl⟩
  have hca : (K.chainComplex (ModuleCat.of ℤ ℤ)).iCycles p ≫ a =
      (K.chainComplex (ModuleCat.of ℤ ℤ)).homologyπ p ≫ f := by
    rw [← hx, ChainComplex.kronecker_homologyπ, ha]
  have hda : (K.chainComplex (ModuleCat.of ℤ ℤ)).d (p + 1) p ≫ a = 0 := by
    rw [← ha]
    exact ChainComplex.d_comp_linearYonedaObj_iCycles p (p + 1) ψ
  -- The cochain `b` over `k` with the same values on simplices is a cocycle.
  refine ⟨(cochainValuesEquiv k (ModuleCat.of k V) K p).symm
    (cochainValuesEquiv ℤ (ModuleCat.of ℤ V) K p a), ?_, ?_⟩
  · rw [CochainComplex.next ℕ p]
    have h := cochainValuesEquiv_symm_cochainValuesEquiv_d_comp k (ModuleCat.of k V) K (p + 1) p
      ((cochainValuesEquiv k (ModuleCat.of k V) K p).symm
        (cochainValuesEquiv ℤ (ModuleCat.of ℤ V) K p a))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply, hda,
      LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff] at h
    exact h
  · rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply, hca]

end Values

end TauCeti
