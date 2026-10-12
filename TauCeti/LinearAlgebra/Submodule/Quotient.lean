/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
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
