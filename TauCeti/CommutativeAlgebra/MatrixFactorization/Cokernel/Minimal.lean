/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Minimal
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.PeriodicResolution
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Resolution
public import TauCeti.Algebra.Homology.Periodic.Minimal
import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
import TauCeti.Algebra.Category.ModuleCat.Projective.LocalRing
import TauCeti.RingTheory.LocalRing.Quotient
import TauCeti.RingTheory.LocalRing.Module

/-!
# Minimality of cokernel resolutions of matrix factorizations

Whenever `(w)` lies in the Jacobson radical of a commutative ring `S`, reducing a finite-projective
matrix factorization `X` modulo `w` preserves and reflects minimality
(`TauCeti.MatrixFactorization.quotientPeriodicComplex_obj_isMinimal_iff`), as does forming
Eisenbud's periodic resolution (`quotientCokernelProjectiveResolution_complex_isMinimal_iff`).

When `(S, 𝔪)` is a local ring with local quotient `R = S ⧸ (w)` and `w ∈ nonZeroDivisors S`, the
odd differential `d₁` maps into `𝔪 • X₀` if and only if the reduced cokernel has no nonzero
projective `R`-retract (`range_d₁_le_maximalIdeal_smul_iff_forall_projective_retract_isZero`), and
Eisenbud's factorization `ofInjective f` of a minimal length-one presentation
`0 → P --f--> Q --g--> M → 0` is minimal if and only if `M` has no nonzero projective `R`-retract
(`isMinimal_ofInjective_iff`).

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Sections 5–6.
-/

public section
noncomputable section

universe u

open CategoryTheory Limits IsLocalRing
open scoped ChangeOfRings

namespace TauCeti.MatrixFactorization

variable {S : Type u} [CommRing S] {w : S}

section LocalReduction

/-- Whenever `(w)` lies in the Jacobson radical of `S`, the reduced two-periodic complex of `X`
is minimal if and only if `X` is minimal. -/
theorem quotientPeriodicComplex_obj_isMinimal_iff
    (hw_jac : Ideal.span {w} ≤ Ring.jacobson S) (X : MatrixFactorization S w) :
    (quotientPeriodicComplex.obj X).IsMinimal ↔ X.IsMinimal := by
  let q := Ideal.Quotient.mk (Ideal.span {w})
  have hjac : (Ring.jacobson S).map q = Ring.jacobson (S ⧸ Ideal.span {w}) := by
    rw [Ring.jacobson_quotient_of_le hw_jac]
    ext x
    rw [Ideal.mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective, Submodule.mem_map]
    -- `Ideal` and `Submodule` share the same membership predicate, and `q.toSemilinearMap` acts
    -- by `q`.
    rfl
  have hrange {P Q : ModuleCat.{u} S} (g : P ⟶ Q) :
      LinearMap.range ((ModuleCat.extendScalars q).map g).hom ≤
          Ring.jacobson (S ⧸ Ideal.span {w}) • ⊤ ↔
        LinearMap.range g.hom ≤ Ring.jacobson S • ⊤ :=
    hjac ▸ ModuleCat.ExtendScalars.range_map_quotient_le_map_smul_iff hw_jac g
  rw [HomologicalComplex.isMinimal_iff_forall_rel, isMinimal_iff]
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hd₀, hd₁⟩ i j hij ↦ ?_⟩
  · have h01 := h 0 1 (zero_add 1)
    rw [quotientPeriodicComplex_obj_d_zero_one] at h01
    simpa only [FGModuleCat.forget₂_map] using (hrange ((forget₂ _ _).map X.obj.d₀)).1 h01
  · have h10 := h 1 0 (by decide)
    rw [quotientPeriodicComplex_obj_d_one_zero] at h10
    simpa only [FGModuleCat.forget₂_map] using (hrange ((forget₂ _ _).map X.obj.d₁)).1 h10
  · rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) i with rfl | rfl
    · obtain rfl : j = 1 := hij.symm.trans (zero_add 1)
      rw [quotientPeriodicComplex_obj_d_zero_one]
      exact (hrange ((forget₂ _ _).map X.obj.d₀)).2
        (by simpa only [FGModuleCat.forget₂_map] using hd₀)
    · obtain rfl : j = 0 := hij.symm.trans (by decide)
      rw [quotientPeriodicComplex_obj_d_one_zero]
      exact (hrange ((forget₂ _ _).map X.obj.d₁)).2
        (by simpa only [FGModuleCat.forget₂_map] using hd₁)

/-- For a non-zero-divisor `w` lying in the Jacobson radical of `S`, the periodic projective
resolution of the reduced cokernel of `X` is minimal if and only if `X` is minimal. -/
theorem quotientCokernelProjectiveResolution_complex_isMinimal_iff
    (hw : w ∈ nonZeroDivisors S) (hw_jac : Ideal.span {w} ≤ Ring.jacobson S)
    (X : MatrixFactorization S w) :
    (quotientCokernelProjectiveResolution hw X).complex.IsMinimal ↔ X.IsMinimal := by
  rw [quotientCokernelProjectiveResolution_complex, PeriodicComplex.resolutionComplex_isMinimal_iff,
    quotientPeriodicComplex_obj_isMinimal_iff hw_jac]

end LocalReduction

section ProjectiveRetract

variable [IsLocalRing S] [IsLocalRing (S ⧸ Ideal.span {w})]

private theorem not_nonempty_retract_self_of_range_d₁_le (hw : w ∈ nonZeroDivisors S)
    {X : MatrixFactorization S w} (hd₁ : LinearMap.range X.obj.d₁.hom.hom ≤ maximalIdeal S • ⊤)
    (retR : Retract (ModuleCat.of (S ⧸ Ideal.span {w}) (S ⧸ Ideal.span {w}))
      (cokernelFunctor.obj
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj) :
    False := by
  let q := Ideal.Quotient.mk (Ideal.span {w})
  obtain ⟨y, hy⟩ := quotientCokernelπ_surjective X (retR.i.hom 1)
  have hπy : retR.r.hom (quotientCokernelπ X y) = 1 :=
    hy ▸ ConcreteCategory.congr_hom retR.retract 1
  have : Module.Projective S X.obj.X₁ := X.property.2
  let φ : X.obj.X₁ →ₗ[S] S ⧸ Ideal.span {w} :=
    (quotientCokernelπ X ≫ (ModuleCat.restrictScalars q).map retR.r).hom
  obtain ⟨β, hβ⟩ := Module.projective_lifting_property (Ideal.span {w}).mkQ φ
    (Submodule.mkQ_surjective _)
  have hβ_eq (z : X.obj.X₁) : q (β z) = φ z := congr($hβ z)
  have hβy : β y ∉ maximalIdeal S := fun hm ↦ by
    have : IsLocalHom q := .of_surjective _ Ideal.Quotient.mk_surjective
    have h1 : (1 : S ⧸ Ideal.span {w}) ∈ maximalIdeal (S ⧸ Ideal.span {w}) := by
      have hφy : φ y = 1 := hπy
      rw [← hφy, ← hβ_eq y]; exact map_nonunit q (β y) hm
    exact (maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hd₀_div (x : X.obj.X₀) : ∃ c : S, β (X.obj.d₀.hom.hom x) = w * c := by
    refine Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 ?_)
    have h0 : (quotientCokernelπ X).hom (X.obj.d₀.hom.hom x) = 0 :=
      (exact_d₀_quotientCokernelπ X _).2 ⟨x, rfl⟩
    exact (hβ_eq _).trans ((congrArg ((ModuleCat.restrictScalars q).map retR.r).hom h0).trans
      (map_zero _))
  obtain ⟨m, hm, hwm_eq⟩ : ∃ m ∈ maximalIdeal S,
      β (X.obj.d₀.hom.hom (X.obj.d₁.hom.hom y)) = w * m :=
    Submodule.smul_induction_on (hd₁ ⟨y, rfl⟩)
      (fun a ha x₀ _ ↦ by
        obtain ⟨c, hc⟩ := hd₀_div x₀
        exact ⟨a * c, Ideal.mul_mem_right c _ ha, by
          rw [map_smul, map_smul, smul_eq_mul, hc]; ring⟩)
      (fun _ _ ⟨m₁, hm₁, h₁⟩ ⟨m₂, hm₂, h₂⟩ ↦
        ⟨m₁ + m₂, add_mem hm₁ hm₂, by rw [map_add, map_add, h₁, h₂, mul_add]⟩)
  have hwy : w * β y = w * m := by
    rw [← smul_eq_mul, ← β.map_smul, ← d₁_comp_d₀_apply, hwm_eq]
  exact hβy ((Module.Flat.isSMulRegular_of_nonZeroDivisors hw hwy) ▸ hm)

private theorem isZero_projective_retract_of_range_d₁_le (hw : w ∈ nonZeroDivisors S)
    {X : MatrixFactorization S w} (hd₁ : LinearMap.range X.obj.d₁.hom.hom ≤ maximalIdeal S • ⊤)
    (P : ModuleCat.{u} (S ⧸ Ideal.span {w})) [Projective P]
    (ret : Retract P (cokernelFunctor.obj
      ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj) : IsZero P := by
  cases subsingleton_or_nontrivial P
  · exact ModuleCat.isZero_of_subsingleton P
  · obtain ⟨retR⟩ := ret.nonempty_retract_ring_of_projective
    exact False.elim (not_nonempty_retract_self_of_range_d₁_le hw hd₁ retR)

omit [IsLocalRing S] [IsLocalRing (S ⧸ Ideal.span {w})] in
private theorem cokernelDesc_comp_adj_symm_quotientCokernelπ
    {X : MatrixFactorization S w} {R_mod : ModuleCat.{u} (S ⧸ Ideal.span {w})}
    (g : X.obj.X₀.obj ⟶ (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj
      R_mod)
    (y : X.obj.X₁) :
    ((cokernelDesc (Ideal.Quotient.mk_singleton_self w)
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).hom ≫
      ((ModuleCat.extendRestrictScalarsAdj.{u} (Ideal.Quotient.mk (Ideal.span {w}))).homEquiv
        X.obj.X₀.obj R_mod).symm g) (quotientCokernelπ X y) = g (X.obj.d₁.hom y) := by
  let q := Ideal.Quotient.mk (Ideal.span {w})
  let X' := (baseChangeFunctor q).obj X
  let g' : (ModuleCat.extendScalars q).obj X.obj.X₀.obj ⟶ R_mod :=
    ((ModuleCat.extendRestrictScalarsAdj.{u} q).homEquiv X.obj.X₀.obj R_mod).symm g
  rw [quotientCokernelπ_apply]
  have hdesc : (cokernelDesc (Ideal.Quotient.mk_singleton_self w) X').hom
      (cokernelπ X' ((1 : S ⧸ Ideal.span {w}) ⊗ₜ[S, q] y)) =
      (1 : S ⧸ Ideal.span {w}) ⊗ₜ[S, q] X.obj.d₁.hom y :=
    (ConcreteCategory.congr_hom
      (cokernelπ_cokernelDesc_hom (Ideal.Quotient.mk_singleton_self w) X')
      ((1 : S ⧸ Ideal.span {w}) ⊗ₜ[S, q] y)).trans (by
        simp only [X', baseChangeFunctor_obj_d₁, FGModuleCat.forget₂_map]
        exact ModuleCat.ExtendScalars.map_tmul q X.obj.d₁.hom 1 y)
  refine (congrArg g'.hom hdesc).trans ?_
  refine (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply (M := X.obj.X₀.obj) g'
    (X.obj.d₁.hom y)).symm.trans ?_
  simp [g']

omit [IsLocalRing (S ⧸ Ideal.span {w})] in
private theorem nonempty_retract_self_of_not_range_d₁_le
    {X : MatrixFactorization S w} (hnot : ¬ LinearMap.range X.obj.d₁.hom.hom ≤ maximalIdeal S • ⊤) :
    Nonempty (Retract (ModuleCat.of (S ⧸ Ideal.span {w}) (S ⧸ Ideal.span {w}))
      (cokernelFunctor.obj
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj) := by
  let q := Ideal.Quotient.mk (Ideal.span {w})
  let X' := (baseChangeFunctor q).obj X
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := Set.not_subset.1 hnot
  have : Module.Projective S X.obj.X₀ := X.property.1
  obtain ⟨α, hαy⟩ := Module.isUnimodular_iff.mp
    (Module.isUnimodular_iff_notMem_jacobson_smul_top.mpr
      ((ringJacobson_eq_maximalIdeal (R := S)).symm ▸ hy))
  let R_mod := ModuleCat.of (S ⧸ Ideal.span {w}) (S ⧸ Ideal.span {w})
  let g : X.obj.X₀.obj ⟶ (ModuleCat.restrictScalars q).obj R_mod :=
    ModuleCat.ofHom ((Ideal.Quotient.mkₐ S (Ideal.span {w})).toLinearMap ∘ₗ α) ≫
      (ModuleCat.restrictScalarsAlgebraMapIso (R := S) (S := S ⧸ Ideal.span {w})
        (S ⧸ Ideal.span {w})).inv
  let r_hom : (cokernelFunctor.obj X').obj ⟶ R_mod :=
    (cokernelDesc (Ideal.Quotient.mk_singleton_self w) X').hom ≫
      ((ModuleCat.extendRestrictScalarsAdj.{u} q).homEquiv X.obj.X₀.obj R_mod).symm g
  let m₀ : (cokernelFunctor.obj X').obj := quotientCokernelπ X y
  have hr_apply : r_hom m₀ = 1 :=
    (cokernelDesc_comp_adj_symm_quotientCokernelπ g y).trans (by
      simp only [g, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        AlgHom.toLinearMap_apply, hαy, map_one]
      exact ModuleCat.restrictScalarsAlgebraMapIso_inv_apply (R := S) (S ⧸ Ideal.span {w}) 1)
  exact ⟨{ i := ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ m₀), r := r_hom,
           retract := ModuleCat.hom_ext <| LinearMap.ext fun r ↦ by simp [hr_apply] }⟩

/-- **Eisenbud's projective-summand criterion.** For a non-zero-divisor `w` in a local ring `S`
with local quotient `R = S ⧸ (w)`, `range d₁ ≤ 𝔪_S • X₀` holds if and only if the reduced cokernel
of `X` has no nonzero projective `R`-retract. -/
theorem range_d₁_le_maximalIdeal_smul_iff_forall_projective_retract_isZero
    (hw : w ∈ nonZeroDivisors S) (X : MatrixFactorization S w) :
    LinearMap.range X.obj.d₁.hom.hom ≤ maximalIdeal S • ⊤ ↔
      ∀ P : ModuleCat.{u} (S ⧸ Ideal.span {w}), Projective P →
        Nonempty (Retract P
          (cokernelFunctor.obj
            ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj) →
        IsZero P := by
  refine ⟨fun hd₁ P _ ⟨ret⟩ ↦ isZero_projective_retract_of_range_d₁_le hw hd₁ P ret, fun h ↦ ?_⟩
  by_contra hnot
  exact not_subsingleton (S ⧸ Ideal.span {w}) <| ModuleCat.subsingleton_of_isZero <|
    h (ModuleCat.of _ (S ⧸ Ideal.span {w})) inferInstance
      (nonempty_retract_self_of_not_range_d₁_le hnot)

/-- **Minimality of Eisenbud's matrix factorization.** For a minimal length-one `S`-projective
resolution `0 → P --f--> Q --g--> M → 0` of an `S ⧸ (w)`-module `M`, `ofInjective f` is minimal if
and only if `M` has no nonzero projective `S ⧸ (w)`-retract. -/
theorem isMinimal_ofInjective_iff (hw : w ∈ nonZeroDivisors S)
    {P Q : FGModuleCat.{u} S} [Module.Projective S P] [Module.Projective S Q]
    {M : ModuleCat.{u} (S ⧸ Ideal.span {w})} {f : P ⟶ Q}
    {g : Q.obj ⟶ (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M}
    (hf : Function.Injective f.hom.hom) (hfg : Function.Exact f.hom.hom g.hom)
    (hg : Function.Surjective g) (hf_min : LinearMap.range f.hom.hom ≤ maximalIdeal S • ⊤) :
    (ofInjective f hf (hfg.smul_mem_range (Ideal.Quotient.mk_singleton_self w))).IsMinimal ↔
      ∀ R_proj : ModuleCat.{u} (S ⧸ Ideal.span {w}), Projective R_proj →
        Nonempty (Retract R_proj M) → IsZero R_proj := by
  have hf₀ : LinearMap.range (ofInjective f hf
      (hfg.smul_mem_range (Ideal.Quotient.mk_singleton_self w))).obj.d₀.hom.hom ≤
      maximalIdeal S • ⊤ := by
    rw [ofInjective_obj_d₀]
    exact hf_min
  rw [isMinimal_iff_range_le_maximalIdeal_smul,
    range_d₁_le_maximalIdeal_smul_iff_forall_projective_retract_isZero hw, and_iff_right hf₀]
  let e := quotientCokernelIsoOfExact hf hfg hg
  exact forall₂_congr fun _ _ ↦ imp_congr_left
    ⟨fun ⟨ret⟩ ↦ ⟨ret.trans e.retract⟩, fun ⟨ret⟩ ↦ ⟨ret.trans e.symm.retract⟩⟩

end ProjectiveRetract
end TauCeti.MatrixFactorization
