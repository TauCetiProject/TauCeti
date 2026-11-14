/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finite products of ideal sheaves

The support of a finite product of ideal sheaves is the union of their supports.
When the supports of finitely many ideal sheaves are pairwise disjoint, their
product equals their intersection.
This identifies the sum of section divisors with their set-theoretic union, and of disjoint
section divisors with their scheme-theoretic union.

On a separated morphism `f : X ⟶ S` locally of finite type, if the closed subschemes of ideal
sheaves are finite over `S`, then so is the closed subscheme of their product, without assuming `f`
proper (`isFinite_mul_subschemeι_comp`, `isFinite_prod_subschemeι_comp`).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The support of a finite product of ideal sheaves is the supremum of their supports. -/
@[simp]
theorem support_finset_prod {X : Scheme} {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData) :
    (∏ i ∈ s, I i).support = s.sup fun i ↦ (I i).support := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.prod_insert ha, ih]

/-- The support of a product of ideal sheaves indexed by a finite type, as a set, is the union of
their supports. -/
theorem coe_support_prod {X : Scheme} {ι : Type*} [Fintype ι] (I : ι → X.IdealSheafData) :
    ((∏ i, I i).support : Set X) = ⋃ i, (I i).support := by
  simp

/-- Ideal sheaves with disjoint supports generate the unit ideal sheaf together. -/
theorem sup_eq_top_of_disjoint_support
    {X : Scheme} {I J : X.IdealSheafData} (h : Disjoint I.support J.support) :
    I ⊔ J = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_sup]
  exact h.eq_bot

/-- A finite product of ideal sheaves with pairwise disjoint supports equals their intersection. -/
theorem prod_eq_iInf_of_pairwise_disjoint_support
    {X : Scheme} {ι : Type*} [Fintype ι] (I : ι → X.IdealSheafData)
    (h : Pairwise fun i j ↦ Disjoint (I i).support (I j).support) :
    ∏ i, I i = ⨅ i, I i := by
  classical
  ext U : 2
  have hcop : Pairwise fun i j ↦ IsCoprime ((I i).ideal U) ((I j).ideal U) := by
    intro i j hij
    have hs := Scheme.IdealSheafData.sup_eq_top_of_disjoint_support (h hij)
    have he := congrArg (fun J : X.IdealSheafData ↦ J.ideal U) hs
    exact Ideal.isCoprime_iff_sup_eq.mpr he
  let e : X.IdealSheafData →* Ideal Γ(X, U) :=
    { toFun := fun J ↦ J.ideal U
      map_one' := by simp [Scheme.IdealSheafData.one_eq_top]
      map_mul' := fun _ _ ↦ rfl }
  have he (J : X.IdealSheafData) : e J = J.ideal U := rfl
  refine (map_prod e I Finset.univ).trans ?_
  simpa [he, Scheme.IdealSheafData.ideal_iInf] using
    (Ideal.prod_eq_iInf_of_pairwise_isCoprime
      (s := Finset.univ) (J := fun i ↦ (I i).ideal U)
      (fun i _ j _ hij ↦ hcop hij))

universe u

/-- **The closed subscheme of a product of two finite ideal sheaves is finite.** Let `f : X ⟶ S` be
separated and locally of finite type, without assuming `f` proper. If `V(I)` and `V(J)` are finite
over `S`, then `V(I * J)` is finite over `S`. -/
theorem isFinite_mul_subschemeι_comp {X S : Scheme.{u}} (I J : X.IdealSheafData) {f : X ⟶ S}
    [LocallyOfFiniteType f] [IsSeparated f]
    [IsFinite (I.subschemeι ≫ f)] [IsFinite (J.subschemeι ≫ f)] :
    IsFinite ((I * J).subschemeι ≫ f) := by
  -- The coproduct `V(I) ⨿ V(J)` surjects onto `V(I * J)` over `S`, transferring universal
  -- closedness and finiteness of fibres.
  have hIle : I * J ≤ I := mul_le_of_le_one_right bot_le le_top
  have hJle : I * J ≤ J := mul_le_of_le_one_left bot_le le_top
  let q : I.subscheme ⨿ J.subscheme ⟶ (I * J).subscheme :=
    coprod.desc (inclusion hIle) (inclusion hJle)
  have hqcomp : q ≫ ((I * J).subschemeι ≫ f) =
      coprod.desc (I.subschemeι ≫ f) (J.subschemeι ≫ f) := by
    apply coprod.hom_ext <;> simp [q, inclusion_subschemeι_assoc]
  have : Surjective q := ⟨fun z ↦ by
    have hz : (I * J).subschemeι z ∈ Set.range I.subschemeι ∪ Set.range J.subschemeι := by
      rw [range_subschemeι, range_subschemeι, ← TopologicalSpace.Closeds.coe_sup, ← support_mul,
        ← range_subschemeι]
      exact ⟨z, rfl⟩
    have hw : ∃ w, (q ≫ (I * J).subschemeι) w = (I * J).subschemeι z := by
      rcases hz with ⟨y, hy⟩ | ⟨y, hy⟩
      · refine ⟨(coprod.inl : I.subscheme ⟶ I.subscheme ⨿ J.subscheme) y, ?_⟩
        rw [← Scheme.Hom.comp_apply]; simpa [q] using hy
      · refine ⟨(coprod.inr : J.subscheme ⟶ I.subscheme ⨿ J.subscheme) y, ?_⟩
        rw [← Scheme.Hom.comp_apply]; simpa [q] using hy
    obtain ⟨w, hw⟩ := hw
    rw [Scheme.Hom.comp_apply] at hw
    exact ⟨w, (I * J).subschemeι.isEmbedding.injective hw⟩⟩
  have : IsFinite (q ≫ ((I * J).subschemeι ≫ f)) := hqcomp ▸ inferInstance
  have : UniversallyClosed ((I * J).subschemeι ≫ f) :=
    .of_comp_surjective q ((I * J).subschemeι ≫ f)
  have : IsProper ((I * J).subschemeι ≫ f) := ⟨⟩
  have : LocallyQuasiFinite ((I * J).subschemeι ≫ f) :=
    .of_finite_preimage_singleton _ fun s ↦
      (((q ≫ ((I * J).subschemeι ≫ f)).finite_preimage_singleton s).image q).subset fun z hz ↦ by
        obtain ⟨w, rfl⟩ := q.surjective z
        exact ⟨w, hz, rfl⟩
  exact .of_isProper_of_locallyQuasiFinite _

end AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti

open AlgebraicGeometry.Scheme.IdealSheafData

universe u

/-- **The closed subscheme of a finite product of finite ideal sheaves is finite.** Let `f : X ⟶ S`
be separated and locally of finite type; properness of `f` is not assumed. If `V(I i)` is finite
over `S` for each `i ∈ s`, then `V(∏ i ∈ s, I i)` is finite over `S`. -/
theorem isFinite_prod_subschemeι_comp {X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] [IsSeparated f] {ι : Type*} (s : Finset ι)
    {I : ι → X.IdealSheafData} (hfin : ∀ i ∈ s, IsFinite ((I i).subschemeι ≫ f)) :
    IsFinite ((∏ i ∈ s, I i).subschemeι ≫ f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, one_eq_top]
    infer_instance
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have := hfin a (Finset.mem_insert_self a s)
    have := ih fun i hi ↦ hfin i (Finset.mem_insert_of_mem hi)
    exact (I a).isFinite_mul_subschemeι_comp (∏ i ∈ s, I i)

end TauCeti
