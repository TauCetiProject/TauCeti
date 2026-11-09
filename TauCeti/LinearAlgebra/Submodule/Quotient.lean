/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Maps
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

Two surjective linear maps with the same kernel identify their codomains, by the first
isomorphism theorem; `LinearMap.equivOfSurjectiveOfKerEq` packages this equivalence.

If an ideal `I` annihilates `S`, every linear map `M → S` kills `I • M`, so maps out of
`M ⧸ I • M` into `S` are the same as maps out of `M`; `TauCeti.linearMapQuotientSMulTopEquiv`
packages this as an additive equivalence. For `I = Ring.jacobson R` it applies to every semisimple
`S`, by `IsSemisimpleModule.jacobson_le_annihilator`.
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
