/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Quotients of submodules

If `F` is the sum of disjoint submodules `p` and `p'`, then the quotient of `F` by `p'`
is linearly equivalent to `p`. The equivalence `Submodule.quotientEquivOfEqSup` specializes
Mathlib's second isomorphism theorem `LinearMap.quotientInfEquivSupQuotient`, allowing the
ambient submodule `F` to be identified by an equality. This applies, for example, when a
successive filtration step splits into the preceding step and a homogeneous component.

Pulling back the span of a quotient class and then mapping it along a linear map gives the
image of the quotient kernel plus the span of the image of a representative. This identifies
the underlying submodule when lifting a cyclic submodule of a subquotient, for example an
eigenline, into the ambient module.

A linear map `φ : P → M` induces an isomorphism from the quotient of `P` by the preimage of a
submodule `F` onto the subquotient `(F ⊔ range φ) ⧸ F`;
`Submodule.quotientComapEquivSupQuotient` generalizes the second isomorphism theorem, which is
the case `φ = p.subtype`.

Two surjective linear maps with the same kernel identify their codomains, by the first
isomorphism theorem; `LinearMap.equivOfSurjectiveOfKerEq` packages this equivalence.

For linear maps `f : M₁ → M₂` and `g : M₂ → M₃` with `g ∘ f = 0`, the homology of
`M₁ → M₂ → M₃` can be described either as `ker g` modulo the image of `f`, or as the image of
`ker g` in the cokernel of `f`; `LinearMap.mapMkQKerEquiv` identifies the two.

If an ideal `I` annihilates `S`, every linear map `M → S` kills `I • M`, so maps out of
`M ⧸ I • M` into `S` are the same as maps out of `M`; `TauCeti.linearMapQuotientSMulTopEquiv`
packages this as an additive equivalence. For `I = Ring.jacobson R` it applies to every semisimple
`S`, by `IsSemisimpleModule.jacobson_le_annihilator`.

The images of a set `S` span `M ⧸ p` exactly when `p ⊔ span S = ⊤`
(`Submodule.span_image_mkQ_eq_top_iff`). When the quotient is finitely generated, finitely many
vectors of `S` already suffice (`Submodule.exists_finset_subset_sup_span_eq_top`). For the range
of a linear map `f`, this says that finitely many vectors `vᵢ` of `S` make
`(x, c) ↦ f x + ∑ cᵢ vᵢ` onto (`LinearMap.exists_surjective_coprod_fintypeLinearCombination`),
the form in which transversality arguments enlarge an operator with finite cokernel by finitely
many parameter directions.

If an `R`-submodule `P` of an `S`-module `M` equals the scalar restriction `Q.restrictScalars R`
of an `S`-submodule `Q`, composing `Submodule.quotEquivOfEq` with
`Submodule.Quotient.restrictScalarsEquiv` gives a canonical `R`-linear equivalence
`Submodule.quotEquivOfEqRestrictScalars : (M ⧸ P) ≃ₗ[R] M ⧸ Q`.
-/

public section

namespace Submodule

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- If `F = p ⊔ p'` and `p` and `p'` are disjoint, the quotient of `F` by `p'` is `p`. -/
noncomputable def quotientEquivOfEqSup (F p p' : Submodule R M) (hF : F = p ⊔ p')
    (h : Disjoint p p') : (F ⧸ p'.comap F.subtype) ≃ₗ[R] p := by
  subst F
  have hp : p.comap p.subtype ⊓ p'.comap p.subtype = ⊥ := by
    simpa only [comap_subtype_self, top_inf_eq] using disjoint_iff_comap_eq_bot.mp h
  exact (LinearMap.quotientInfEquivSupQuotient p p').symm.trans (quotEquivOfEqBot _ hp)

/-- The inverse equivalence sends an element of `p` to its quotient class in `F`. -/
@[simp]
theorem quotientEquivOfEqSup_symm_apply (F p p' : Submodule R M) (hF : F = p ⊔ p')
    (h : Disjoint p p') (x : p) :
    (quotientEquivOfEqSup F p p' hF h).symm x =
      Quotient.mk ⟨x, by rw [hF]; exact mem_sup_left x.property⟩ := by
  subst F
  rw [quotientEquivOfEqSup, LinearEquiv.trans_symm]
  simp only [LinearEquiv.trans_apply, quotEquivOfEqBot_symm_apply]
  exact LinearMap.quotientInfEquivSupQuotient_apply_mk p p' x

/-- The equivalence sends the class of any representative lying in `p` to that representative. -/
@[simp]
theorem quotientEquivOfEqSup_apply_mk (F p p' : Submodule R M) (hF : F = p ⊔ p')
    (h : Disjoint p p') (y : F) (hy : (y : M) ∈ p) :
    quotientEquivOfEqSup F p p' hF h (Quotient.mk y) = ⟨y, hy⟩ := by
  apply (quotientEquivOfEqSup F p p' hF h).symm.injective
  rw [LinearEquiv.symm_apply_apply, quotientEquivOfEqSup_symm_apply]

/-- A quotient representative has zero image exactly when it lies in the right summand. -/
theorem quotientEquivOfEqSup_apply_mk_eq_zero_iff (F p p' : Submodule R M)
    (hF : F = p ⊔ p') (h : Disjoint p p') (y : F) :
    quotientEquivOfEqSup F p p' hF h (Quotient.mk y) = 0 ↔ (y : M) ∈ p' := by
  simp

/-- The equivalence sends the class of any representative in the right summand to zero. -/
theorem quotientEquivOfEqSup_apply_mk_of_mem_right (F p p' : Submodule R M)
    (hF : F = p ⊔ p') (h : Disjoint p p') (y : F) (hy : (y : M) ∈ p') :
    quotientEquivOfEqSup F p p' hF h (Quotient.mk y) = 0 := by
  simp [hy]

/-- Mapping the inverse image of the span of a quotient class gives the image of the
quotient kernel plus the span of the image of a representative. -/
theorem map_comap_mkQ_span_singleton (S : Submodule R M) (f : M →ₗ[R] N) (v : M) :
    ((R ∙ S.mkQ v).comap S.mkQ).map f = S.map f ⊔ R ∙ f v := by
  have hspan : (R ∙ v).map S.mkQ = R ∙ S.mkQ v := by
    simp [Submodule.map_span]
  rw [← hspan, Submodule.comap_map_mkQ, Submodule.map_sup]
  simp [Submodule.map_span]

/-- The map `φ` induces a linear isomorphism from the quotient of `P` by the preimage of `F`
under `φ` onto the subquotient `(F ⊔ range φ) ⧸ F`. For `φ = p.subtype` this is the second
isomorphism theorem `LinearMap.quotientInfEquivSupQuotient`. -/
noncomputable def quotientComapEquivSupQuotient {P : Type*} [AddCommGroup P] [Module R P]
    (F : Submodule R M) (φ : P →ₗ[R] M) :
    (P ⧸ F.comap φ) ≃ₗ[R]
      (F ⊔ LinearMap.range φ : Submodule R M) ⧸
        F.submoduleOf (F ⊔ LinearMap.range φ : Submodule R M) :=
  let ψ : P →ₗ[R] (F ⊔ LinearMap.range φ : Submodule R M) ⧸
      F.submoduleOf (F ⊔ LinearMap.range φ : Submodule R M) :=
    (F.submoduleOf (F ⊔ LinearMap.range φ : Submodule R M)).mkQ ∘ₗ
      φ.codRestrict _ fun c ↦ Submodule.mem_sup_right ⟨c, rfl⟩
  Submodule.quotEquivOfEq _ _ (by
    ext c
    simp only [LinearMap.mem_ker, ψ, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    simp only [Submodule.submoduleOf, Submodule.mem_comap, LinearMap.codRestrict_apply,
      Submodule.coe_subtype]) ≪≫ₗ
  ψ.quotKerEquivOfSurjective (by
    apply LinearMap.range_eq_top.mp
    simp only [ψ, LinearMap.range_comp, Submodule.map_mkQ_eq_top, LinearMap.range_codRestrict]
    exact (Submodule.submoduleOf_sup_of_le le_sup_left le_sup_right).symm.trans
      (Submodule.submoduleOf_eq_top.mpr le_rfl))

@[simp]
theorem quotientComapEquivSupQuotient_apply_mk {P : Type*} [AddCommGroup P] [Module R P]
    (F : Submodule R M) (φ : P →ₗ[R] M) (c : P) :
    quotientComapEquivSupQuotient F φ (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (p := F.submoduleOf (F ⊔ LinearMap.range φ : Submodule R M))
        ⟨φ c, Submodule.mem_sup_right ⟨c, rfl⟩⟩ := by
  simp [quotientComapEquivSupQuotient]
  rfl

/-- The images of a set `S` span the quotient `M ⧸ p` exactly when `p` and the span of `S`
together span `M`. -/
theorem span_image_mkQ_eq_top_iff {p : Submodule R M} {S : Set M} :
    span R (p.mkQ '' S) = ⊤ ↔ p ⊔ span R S = ⊤ := by
  rw [← map_span, map_mkQ_eq_top]

/-- **Finitely many vectors complete a submodule with finitely generated quotient.** If `M ⧸ p`
is finitely generated and `p ⊔ span R S = ⊤`, then some finite subset `t ⊆ S` already gives
`p ⊔ span R t = ⊤`. -/
theorem exists_finset_subset_sup_span_eq_top {p : Submodule R M} [Module.Finite R (M ⧸ p)]
    {S : Set M} (h : p ⊔ span R S = ⊤) : ∃ t : Finset M, ↑t ⊆ S ∧ p ⊔ span R t = ⊤ := by
  classical
  rw [← span_image_mkQ_eq_top_iff] at h
  obtain ⟨b, hbS, hbspan⟩ := (fg_span_iff_fg_span_finset_subset _).1 (h ▸ Module.Finite.fg_top)
  obtain ⟨t, htS, rfl⟩ := Finset.subset_set_image_iff.1 hbS
  refine ⟨t, htS, ?_⟩
  rw [← span_image_mkQ_eq_top_iff, ← Finset.coe_image, ← hbspan, h]

section RestrictScalars

variable {S : Type*} [Ring S] [SMul R S] [Module S M] [IsScalarTower R S M]

/-- If an `R`-submodule `P` equals the scalar restriction of an `S`-submodule `Q`, the quotients
`M ⧸ P` and `M ⧸ Q` are canonically `R`-linearly equivalent. -/
def quotEquivOfEqRestrictScalars (P : Submodule R M) (Q : Submodule S M)
    (h : P = Q.restrictScalars R) : (M ⧸ P) ≃ₗ[R] M ⧸ Q :=
  (quotEquivOfEq P (Q.restrictScalars R) h).trans (Quotient.restrictScalarsEquiv R Q)

/-- `Submodule.quotEquivOfEqRestrictScalars` sends a quotient class to the class of the same
representative. -/
@[simp]
theorem quotEquivOfEqRestrictScalars_mk (P : Submodule R M) (Q : Submodule S M)
    (h : P = Q.restrictScalars R) (x : M) :
    P.quotEquivOfEqRestrictScalars Q h (Quotient.mk x) = Quotient.mk x := by
  simp [quotEquivOfEqRestrictScalars]

/-- The inverse of `Submodule.quotEquivOfEqRestrictScalars` sends a quotient class to the class of
the same representative. -/
@[simp]
theorem quotEquivOfEqRestrictScalars_symm_mk (P : Submodule R M) (Q : Submodule S M)
    (h : P = Q.restrictScalars R) (x : M) :
    (P.quotEquivOfEqRestrictScalars Q h).symm (Quotient.mk x) = Quotient.mk x := by
  rw [LinearEquiv.symm_apply_eq, quotEquivOfEqRestrictScalars_mk]

end RestrictScalars

end Submodule

namespace LinearMap

variable {R M N N' : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup N']
  [Module R M] [Module R N] [Module R N'] (g : M →ₗ[R] N) (h : M →ₗ[R] N')
  (hg : Function.Surjective g) (hh : Function.Surjective h) (hk : ker g = ker h)

/-- Two surjective linear maps with the same kernel identify their codomains, by the first
isomorphism theorem. -/
noncomputable def equivOfSurjectiveOfKerEq : N ≃ₗ[R] N' :=
  (g.quotKerEquivOfSurjective hg).symm.trans
    ((Submodule.quotEquivOfEq _ _ hk).trans (h.quotKerEquivOfSurjective hh))

/-- The equivalence sends the image of an element under the first map to its image under
the second map. -/
@[simp]
theorem equivOfSurjectiveOfKerEq_apply (x : M) :
    g.equivOfSurjectiveOfKerEq h hg hh hk (g x) = h x := by
  simp [equivOfSurjectiveOfKerEq]

/-- The inverse equivalence sends the image of an element under the second map to its image
under the first map. -/
@[simp]
theorem equivOfSurjectiveOfKerEq_symm_apply (x : M) :
    (g.equivOfSurjectiveOfKerEq h hg hh hk).symm (h x) = g x :=
  (LinearEquiv.symm_apply_eq _).mpr (equivOfSurjectiveOfKerEq_apply g h hg hh hk x).symm

section MapMkQKer

variable {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup M₃] [Module R M₃]

/-- For linear maps `f : M₁ → M₂` and `g : M₂ → M₃` with `g ∘ f = 0`, the image of `ker g` in the
cokernel of `f` is the quotient of `ker g` by the image of `f`, that is by the range of the
corestriction of `f` to `ker g`. Both describe the homology of `M₁ → M₂ → M₃`. -/
noncomputable def mapMkQKerEquiv (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hfg : ∀ x, f x ∈ ker g) :
    (ker g ⧸ range (f.codRestrict (ker g) hfg)) ≃ₗ[R] (ker g).map (range f).mkQ :=
  Submodule.quotEquivOfEq _ _ (by
      rw [range_codRestrict, ker_comp, Submodule.ker_mkQ]) ≪≫ₗ
    ((range f).mkQ ∘ₗ (ker g).subtype).quotKerEquivRange ≪≫ₗ
      LinearEquiv.ofEq _ _ (by rw [range_comp, Submodule.range_subtype])

/-- `mapMkQKerEquiv` sends the class of `x ∈ ker g` to the class of `x` modulo the image of `f`. -/
@[simp]
theorem coe_mapMkQKerEquiv_mk (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (hfg : ∀ x, f x ∈ ker g)
    (x : ker g) :
    (f.mapMkQKerEquiv g hfg (Submodule.Quotient.mk x) : M₂ ⧸ range f) =
      Submodule.Quotient.mk (x : M₂) := by
  simp [mapMkQKerEquiv]

end MapMkQKer

/-- **Finitely many vectors make a map with finitely generated cokernel onto.** If the cokernel
`N ⧸ range f` of `f : P → N` is finitely generated and `range f` and the span of `S` together
span `N`, then finitely many vectors `v₁, …, vₙ` of `S` make `(x, c) ↦ f x + ∑ cᵢ vᵢ` onto. -/
theorem exists_surjective_coprod_fintypeLinearCombination {P : Type*} [AddCommMonoid P]
    [Module R P] {f : P →ₗ[R] N}
    [Module.Finite R (N ⧸ range f)] {S : Set N} (hS : range f ⊔ Submodule.span R S = ⊤) :
    ∃ (n : ℕ) (v : Fin n → N), (∀ i, v i ∈ S) ∧
      Function.Surjective (f.coprod (Fintype.linearCombination R v)) := by
  classical
  obtain ⟨t, htS, htop⟩ := Submodule.exists_finset_subset_sup_span_eq_top hS
  refine ⟨t.card, fun i ↦ t.equivFin.symm i, fun i ↦ htS (t.equivFin.symm i).property, ?_⟩
  rw [← range_eq_top, range_coprod, Fintype.range_linearCombination, ← htop]
  congr
  exact (EquivLike.range_comp (Subtype.val : t → N) t.equivFin.symm).trans Subtype.range_coe

end LinearMap

namespace TauCeti

variable {R : Type*} [Ring R]

/-- **Maps into a module annihilated by `I` factor through `M ⧸ I • M`.** If the ideal `I`
annihilates `S`, then composition with `M → M ⧸ I • M` identifies maps out of `M ⧸ I • M` with maps
out of `M`; the identification is additive. For `I = Ring.jacobson R` this applies to every
semisimple `S` by `IsSemisimpleModule.jacobson_le_annihilator`. -/
def linearMapQuotientSMulTopEquiv {I : Ideal R} (M : Type*) [AddCommGroup M] [Module R M]
    {S : Type*} [AddCommGroup S] [Module R S] (hI : I ≤ Module.annihilator R S) :
    (M ⧸ I • (⊤ : Submodule R M) →ₗ[R] S) ≃+ (M →ₗ[R] S) where
  toFun g := g ∘ₗ (I • (⊤ : Submodule R M)).mkQ
  invFun f := (I • (⊤ : Submodule R M)).liftQ f <|
    Submodule.smul_le.mpr fun r hr x _ ↦ by
      rw [LinearMap.mem_ker, map_smul]
      exact Module.mem_annihilator.mp (hI hr) _
  left_inv g := Submodule.linearMap_qext _ (Submodule.liftQ_mkQ _ _ _)
  right_inv f := Submodule.liftQ_mkQ _ _ _
  map_add' g h := LinearMap.add_comp _ h g

@[simp]
theorem linearMapQuotientSMulTopEquiv_apply {I : Ideal R} (M : Type*) [AddCommGroup M]
    [Module R M] {S : Type*} [AddCommGroup S] [Module R S] (hI : I ≤ Module.annihilator R S)
    (g : M ⧸ I • (⊤ : Submodule R M) →ₗ[R] S) (x : M) :
    linearMapQuotientSMulTopEquiv M hI g x = g (Submodule.Quotient.mk x) :=
  (rfl)

@[simp]
theorem linearMapQuotientSMulTopEquiv_symm_apply_mk {I : Ideal R} (M : Type*) [AddCommGroup M]
    [Module R M] {S : Type*} [AddCommGroup S] [Module R S] (hI : I ≤ Module.annihilator R S)
    (f : M →ₗ[R] S) (x : M) :
    (linearMapQuotientSMulTopEquiv M hI).symm f (Submodule.Quotient.mk x) = f x :=
  (rfl)

end TauCeti
