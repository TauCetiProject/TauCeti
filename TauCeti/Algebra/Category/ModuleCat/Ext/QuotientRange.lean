/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.Torsion.Basic
public import TauCeti.Algebra.Category.ModuleCat.Ext.Basic
public import TauCeti.Algebra.Homology.Ext.Presentation
public import TauCeti.LinearAlgebra.Determinant.Basic
public import TauCeti.LinearAlgebra.FreeModule.CardQuotient

/-!
# `Ext¹` of the cokernel of a linear map into a projective module

Let `f : P →ₗ[R] Q` be an injective linear map of modules over a commutative ring `R`, with `Q`
projective. Then `0 → P → Q → Q ⧸ range f → 0` is a projective presentation of the cokernel, so
`Ext¹(Q ⧸ range f, R)` is the cokernel of the restriction map `Hom(Q, R) → Hom(P, R)`, that is,

`Ext¹(Q ⧸ range f, R) ≃ Dual P ⧸ range f.dualMap`

(`LinearMap.extOneQuotientRangeEquiv`). This is `TauCeti.homCokernelEquivExt` for the
presentation `LinearMap.quotientRangeShortComplex f`, with morphisms of modules read as linear
maps.

For an endomorphism `f` of a finite free module over a principal ideal domain with
`det f ≠ 0`, the transpose `f.dualMap` has the same determinant (`LinearMap.det_dualMap`), so
`Ext¹(P ⧸ range f, R)` has the cardinality of `R ⧸ (det f)`, the same as the cokernel
`P ⧸ range f` itself (`LinearMap.card_ext_one_quotient_range_eq_card_quotient_span_det`,
`LinearMap.card_quotient_range_eq_card_quotient_span_det`). It is a torsion module, killed by
`det f`, which by Cramer's rule kills the cokernel `P ⧸ range f` and hence every
`Extⁿ(P ⧸ range f, M)` (`LinearMap.det_smul_ext_quotient_range_eq_zero`,
`LinearMap.isTorsion_ext_quotient_range`). Over `ℤ` the order of the finite group
`Ext¹(P ⧸ range f, ℤ)` is `|det f|`. Through the universal coefficient theorem, this computes the
torsion of a cohomology group from a presentation of the torsion of the homology one degree below.

## Main results

* `LinearMap.shortExact_quotientRangeShortComplex`: `0 → P → Q → Q ⧸ range f → 0` is short exact
  for injective `f`.
* `LinearMap.extOneQuotientRangeEquiv`: `Ext¹(Q ⧸ range f, R) ≃ₗ[R] Dual P ⧸ range f.dualMap` for
  injective `f` and projective `Q`.
* `LinearMap.card_ext_one_quotient_range_eq_card_quotient_span_det`: for an endomorphism `f` of a
  finite free module over a principal ideal domain with `det f ≠ 0`, `Ext¹(P ⧸ range f, R)` has
  the same `Nat.card` as `R ⧸ (det f)`.
* `LinearMap.det_smul_ext_quotient_range_eq_zero`: for an endomorphism `f` of a finite free
  module, `det f` kills `Extⁿ(P ⧸ range f, M)`.
* `LinearMap.isTorsion_ext_quotient_range`: when `det f` is a non-zero-divisor,
  `Extⁿ(P ⧸ range f, M)` is a torsion module.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 3.3 (`Ext` from a projective
  presentation).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian Module

universe w

namespace LinearMap

variable {R : Type w} [CommRing R] {P Q : Type w} [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q]

/-- The short complex `P ⟶ Q ⟶ Q ⧸ range f` of modules given by a linear map `f` and the quotient
map onto its cokernel. -/
abbrev quotientRangeShortComplex (f : P →ₗ[R] Q) : ShortComplex (ModuleCat.{w} R) :=
  ModuleCat.shortComplexOfCompEqZero f (range f).mkQ
    f.exact_map_mkQ_range.linearMap_comp_eq_zero

/-- For injective `f`, the short complex `0 → P → Q → Q ⧸ range f → 0` is short exact. -/
theorem shortExact_quotientRangeShortComplex {f : P →ₗ[R] Q} (hf : Function.Injective f) :
    f.quotientRangeShortComplex.ShortExact :=
  ModuleCat.shortComplex_shortExact _ f.exact_map_mkQ_range hf (Submodule.mkQ_surjective _)

variable [Module.Projective R Q]

/-- **`Ext¹` of a cokernel.** For an injective linear map `f : P →ₗ[R] Q` into a projective module,
`Ext¹(Q ⧸ range f, R)` is the cokernel of the restriction map `f.dualMap : Dual Q → Dual P`. The
class of a linear form `g : P →ₗ[R] R` is the extension class of the presentation
`0 → P → Q → Q ⧸ range f → 0` pushed forward along `g`
(`LinearMap.extOneQuotientRangeEquiv_symm_mk`). -/
def extOneQuotientRangeEquiv {f : P →ₗ[R] Q} (hf : Function.Injective f) :
    Ext.{w} (ModuleCat.of R (Q ⧸ range f)) (ModuleCat.of R R) 1 ≃ₗ[R]
      Dual R P ⧸ range f.dualMap :=
  (TauCeti.homCokernelEquivExt R (shortExact_quotientRangeShortComplex hf)
      (ModuleCat.of R R)).symm.trans
    (Submodule.Quotient.equiv _ _ ModuleCat.homLinearEquiv (by
      ext g
      constructor
      · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
        exact ⟨h.hom, rfl⟩
      · rintro ⟨h, rfl⟩
        exact ⟨_, ⟨ModuleCat.ofHom h, rfl⟩, rfl⟩))

/-- The inverse of `LinearMap.extOneQuotientRangeEquiv` sends the class of a linear form
`g : P →ₗ[R] R` to the extension class of the presentation `0 → P → Q → Q ⧸ range f → 0`
pushed forward along `g`. -/
@[simp]
theorem extOneQuotientRangeEquiv_symm_mk {f : P →ₗ[R] Q} (hf : Function.Injective f)
    (g : Dual R P) :
    (extOneQuotientRangeEquiv hf).symm (Submodule.Quotient.mk g) =
      (shortExact_quotientRangeShortComplex hf).extClass.comp
        (Ext.mk₀ (ModuleCat.ofHom (X := P) (Y := R) g)) (add_zero 1) := by
  simp only [extOneQuotientRangeEquiv, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm]
  exact TauCeti.homCokernelEquivExt_mk R (shortExact_quotientRangeShortComplex hf) _
    (ModuleCat.ofHom (X := P) (Y := R) g)

/-- `LinearMap.extOneQuotientRangeEquiv` sends the extension class of the presentation
`0 → P → Q → Q ⧸ range f → 0` pushed forward along a linear form `g : P →ₗ[R] R` to the class
of `g`. -/
@[simp]
theorem extOneQuotientRangeEquiv_extClass_comp {f : P →ₗ[R] Q} (hf : Function.Injective f)
    (g : Dual R P) :
    extOneQuotientRangeEquiv hf ((shortExact_quotientRangeShortComplex hf).extClass.comp
        (Ext.mk₀ (ModuleCat.ofHom (X := P) (Y := R) g)) (add_zero 1)) =
      Submodule.Quotient.mk g := by
  rw [← extOneQuotientRangeEquiv_symm_mk hf, LinearEquiv.apply_symm_apply]

end LinearMap

namespace LinearMap

variable {R : Type w} [CommRing R] [IsDomain R] {P : Type w}
  [AddCommGroup P] [Module R P] [Module.Free R P] [Module.Finite R P] {f : P →ₗ[R] P}

/-- **The order of `Ext¹` of a cokernel.** For an endomorphism `f` of a finite free module over a
principal ideal domain with `det f ≠ 0`, `Ext¹(P ⧸ range f, R)` has the same `Nat.card` as
`R ⧸ (det f)`. Over `ℤ` this is `|det f|`. -/
theorem card_ext_one_quotient_range_eq_card_quotient_span_det [IsPrincipalIdealRing R]
    (hf : f.det ≠ 0) :
    Nat.card (Ext.{w} (ModuleCat.of R (P ⧸ range f)) (ModuleCat.of R R) 1) =
      Nat.card (R ⧸ Ideal.span {f.det}) := by
  rw [Nat.card_congr (extOneQuotientRangeEquiv
      (injective_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hf))).toEquiv,
    card_quotient_range_eq_card_quotient_span_det (by rwa [det_dualMap]), det_dualMap]

omit [IsDomain R] in
/-- For an endomorphism `f` of a finite free module, `det f` kills `Extⁿ(P ⧸ range f, M)` for every
module `M`: by Cramer's rule (`LinearMap.det_smul_mem_range`) it annihilates `P ⧸ range f`. -/
theorem det_smul_ext_quotient_range_eq_zero {M : ModuleCat.{w} R} {n : ℕ}
    (x : Ext.{w} (ModuleCat.of R (P ⧸ range f)) M n) : f.det • x = 0 :=
  Ext.smul_eq_zero_of_mem_annihilator_left (Module.mem_annihilator.2 fun y ↦ by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact det_smul_mem_range f y) x

omit [IsDomain R] in
/-- For an endomorphism `f` of a finite free module whose determinant is a non-zero-divisor,
`Extⁿ(P ⧸ range f, M)` is a torsion module for every module `M`: it is killed by `det f`
(`LinearMap.det_smul_ext_quotient_range_eq_zero`). -/
theorem isTorsion_ext_quotient_range (hf : f.det ∈ nonZeroDivisors R) {M : ModuleCat.{w} R}
    {n : ℕ} : Module.IsTorsion R (Ext.{w} (ModuleCat.of R (P ⧸ range f)) M n) :=
  fun x ↦ ⟨⟨f.det, hf⟩, det_smul_ext_quotient_range_eq_zero x⟩

end LinearMap

end
