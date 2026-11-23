/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Transpose
public import TauCeti.LinearAlgebra.Dual.ContragredientDual
public import TauCeti.Algebra.Module.Presentation.Quadratic

import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.LocalRing.Module
import TauCeti.Algebra.Module.AuslanderReiten.BaseChange
import TauCeti.Algebra.Module.AuslanderReiten.FinitePresentation
import TauCeti.LinearAlgebra.Matrix.ToLin
import TauCeti.RingTheory.FittingIdeal.BaseChange
import TauCeti.RingTheory.FittingIdeal.Matrix
import TauCeti.RingTheory.FittingIdeal.Semilinear

/-!
# Transposed presentations and their Fitting ideals

Let `R` and `S` be commutative rings connected by a ring isomorphism `σ : S ≃+* R` (such as the
contragredient involution `# : R^# ≃+* R` on a commutative group ring or character group ring), and
let `P₁ →f P₀ → M → 0` be a presentation of an `R`-module `M`. Applying the contragredient dual
`P^* = ContragredientDual σ P` reverses `f` into an `S`-linear map `f^* : P₀^* →ₗ[S] P₁^*`. Its
cokernel

  `PresentationTranspose σ f =`
  `ContragredientDual σ P₁ ⧸ LinearMap.range (ContragredientDual.map σ f)`

is the **transpose** attached to the presentation, using the standard quotient API (`Submodule.mkQ`,
`Submodule.liftQ`, `Submodule.quot_hom_ext`) and identified `σ`-semilinearly with
`TauCeti.AuslanderReitenTranspose f` via `PresentationTranspose.toARTransposeLinearEquiv`. Note
that Dasgupta and Kakde write the presentation with indices swapped (`P₀ → P₁ → M`).

The transpose belongs to the presentation map `f`, not to the isomorphism class of `M` alone:
`id : R →ₗ[R] R` and `fst : R × R →ₗ[R] R` both present the zero module, yet the transpose of `id`
vanishes (`PresentationTranspose.subsingleton_id`) while the transpose of `fst` is isomorphic to
`S` (`PresentationTranspose.fstEquiv`).

When `f` comes from a quadratic presentation `P` of `M` with relation matrix `P.rel`, the transpose
carries a canonical quadratic presentation over `S` with relation matrix `P.relᵀ.map σ.symm` up to
canonical index identification (`PresentationTranspose.quadraticPresentation`), of determinant
`σ⁻¹(det P.rel)` (`PresentationTranspose.det_quadraticPresentation_rel`), and therefore its zeroth
Fitting ideal over `S` is `σ⁻¹(Fitt₀(M))` (`PresentationTranspose.fittingIdeal_eq`, Dasgupta–Kakde
Lemma 6.1). More generally, if `P₁ →f P₀ → M → 0` is an exact presentation by finitely generated
projective `R`-modules of constant ranks `t` and `t + s` (without assuming `P₁` or `P₀` free),
localizing at maximal ideals of `R` reduces to the free case
(`PresentationTranspose.fittingIdeal_eq_of_free`) and shows `Fitt₀_S(M^tr) = σ⁻¹(Fitt_s(M))`
(`PresentationTranspose.fittingIdeal_eq_excess`, Dasgupta–Kakde equation (171)).

## Main definitions

* `TauCeti.PresentationTranspose σ f`: the cokernel `coker(f^* : P₀^* → P₁^*)` as the `S`-module
  quotient `ContragredientDual σ P₁ ⧸ LinearMap.range (ContragredientDual.map σ f)`.
* `TauCeti.PresentationTranspose.toARTransposeLinearEquiv`: the `σ`-semilinear identification
  with `TauCeti.AuslanderReitenTranspose f`, constructed via
  `AuslanderReitenTranspose.quotientEquiv`.
* `TauCeti.PresentationTranspose.congr`: functoriality of the transpose under an isomorphism of
  presenting arrows.
* `TauCeti.PresentationTranspose.fstEquiv` and `TauCeti.PresentationTranspose.mulLeftEquiv`:
  explicit identifications `PresentationTranspose σ (LinearMap.fst R R R) ≃ₗ[S] S` and
  `PresentationTranspose σ (LinearMap.mulLeft R a) ≃ₗ[S] S ⧸ Ideal.span {σ.symm a}`, characterized
  on representatives by `fstEquiv_mk`, `fstEquiv_symm_apply`, `mulLeftEquiv_mk`, and
  `mulLeftEquiv_symm_mk`.
* `TauCeti.PresentationTranspose.quadraticPresentation`: the quadratic presentation over `S`
  attached to a quadratic presentation `P` over `R`, characterized by `quadraticPresentation_size`,
  `quadraticPresentation_rel`, and `quadraticPresentation_gen_apply`.

## Main results

* `TauCeti.PresentationTranspose.det_quadraticPresentation_rel` and
  `TauCeti.PresentationTranspose.fittingIdeal_eq`: for a quadratic presentation `P` of a finite
  `R`-module `M`, the transposed relation determinant is `σ⁻¹(det P.rel)` and
  `Fitt₀_S(PresentationTranspose σ (Matrix.toLin' P.rel)) = σ⁻¹(Fitt₀_R(M))`.
* `TauCeti.PresentationTranspose.fittingIdeal_toLin'_eq_minorsIdeal` and
  `TauCeti.PresentationTranspose.fittingIdeal_eq_of_free`: the free excess-generators formula
  identifying `Fitt₀_S(M^tr)` with the `t × t` minors of the transposed matrix and with
  `σ⁻¹(Fitt_s(M))`.
* `TauCeti.PresentationTranspose.fittingIdeal_eq_excess`: for an exact sequence
  `P₁ →f P₀ →π M → 0` with `P₁`, `P₀` finitely generated projective of constant stalk ranks `t`
  and `t + s`, `Fitt₀_S(PresentationTranspose σ f) = σ⁻¹(Fitt_s(M))`.

## References

* S. Dasgupta, M. Kakde, *On the Brumer–Stark conjecture*, Ann. of Math. (2) 197 (2023), §6.1,
  equation (81) and Lemma 6.1, p. 40; Appendix A.4, proof of Lemma A.8, p. 86; Appendix B.2,
  proof of Lemma B.4, equation (171), p. 93.
* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969), Section 2.1.
-/

public section

noncomputable section

open scoped Matrix TensorProduct

namespace TauCeti

section Basic

variable {R S P₀ P₁ Q₀ Q₁ : Type*} [CommRing R] [CommRing S]
  [AddCommMonoid P₀] [Module R P₀] [AddCommMonoid P₁] [Module R P₁]
  [AddCommMonoid Q₀] [Module R Q₀] [AddCommMonoid Q₁] [Module R Q₁]

/-- The **transpose** `coker(f^* : P₀^* → P₁^*)` of a presentation arrow `f : P₁ →ₗ[R] P₀`, viewed
as an `S`-module quotient along a ring isomorphism `σ : S ≃+* R` through `ContragredientDual`.
It depends on the presentation arrow `f` rather than on `coker f` alone. -/
abbrev PresentationTranspose (σ : S ≃+* R) (f : P₁ →ₗ[R] P₀) : Type _ :=
  ContragredientDual σ P₁ ⧸ LinearMap.range (ContragredientDual.map σ f)

namespace PresentationTranspose

private def arOppositeEquiv (σ : S ≃+* R) (f : P₁ →ₗ[R] P₀) :
    let ρ : Rᵐᵒᵖ ≃+* S := (RingEquiv.toOpposite R).symm.trans σ.symm
    haveI := RingHomInvPair.of_ringEquiv ρ
    haveI := RingHomInvPair.of_ringEquiv_symm ρ
    PresentationTranspose σ f ≃ₛₗ[(ρ.symm : S →+* Rᵐᵒᵖ)] AuslanderReitenTranspose f :=
  let ρ : Rᵐᵒᵖ ≃+* S := (RingEquiv.toOpposite R).symm.trans σ.symm
  haveI := RingHomInvPair.of_ringEquiv ρ
  haveI := RingHomInvPair.of_ringEquiv_symm ρ
  let e : Module.Dual R P₁ ≃ₛₗ[(ρ : Rᵐᵒᵖ →+* S)] ContragredientDual σ P₁ :=
    { toFun := ContragredientDual.ofDual
      invFun := ContragredientDual.toDual
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r φ ↦ by
        ext x
        simp [ρ, LinearMap.smul_apply, mul_comm]
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have he : (LinearMap.range (f.lcomp Rᵐᵒᵖ R)).map e.toLinearMap =
      LinearMap.range (ContragredientDual.map σ f) := by
    ext φ
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨ψ, rfl⟩, rfl⟩
      refine ⟨ContragredientDual.ofDual ψ, ContragredientDual.toDual_injective ?_⟩
      ext y
      simp [e, LinearMap.lcomp_apply']
    · rintro ⟨ψ, rfl⟩
      refine ⟨f.lcomp Rᵐᵒᵖ R ψ.toDual, ⟨ψ.toDual, rfl⟩, ContragredientDual.toDual_injective ?_⟩
      ext y
      simp [e, LinearMap.lcomp_apply']
  (AuslanderReitenTranspose.quotientEquiv f
    (LinearMap.range (ContragredientDual.map σ f)) e he).symm

/-- `PresentationTranspose σ f` is `σ`-semilinearly equivalent to `AuslanderReitenTranspose f`,
constructed from `AuslanderReitenTranspose.quotientEquiv`. -/
def toARTransposeLinearEquiv (σ : S ≃+* R) (f : P₁ →ₗ[R] P₀) :
    haveI := RingHomInvPair.of_ringEquiv σ
    haveI := RingHomInvPair.of_ringEquiv_symm σ
    PresentationTranspose σ f ≃ₛₗ[(σ : S →+* R)] AuslanderReitenTranspose f :=
  let ρ : Rᵐᵒᵖ ≃+* S := (RingEquiv.toOpposite R).symm.trans σ.symm
  have := RingHomInvPair.of_ringEquiv ρ
  have := RingHomInvPair.of_ringEquiv_symm ρ
  haveI := RingHomInvPair.of_ringEquiv σ
  haveI := RingHomInvPair.of_ringEquiv_symm σ
  let q := arOppositeEquiv σ f
  { q.toAddEquiv with
    map_smul' := fun s x ↦ by
      have hs := q.map_smul' s x
      have hop : (ρ.symm : S →+* Rᵐᵒᵖ) s = MulOpposite.op (algebraMap R R (σ s)) := rfl
      change q.toAddEquiv.toFun (s • x) = (ρ.symm : S →+* Rᵐᵒᵖ) s • q.toAddEquiv.toFun x at hs
      rw [hop, AuslanderReitenTranspose.op_algebraMap_smul] at hs
      exact hs }

@[simp]
theorem toARTransposeLinearEquiv_mk {σ : S ≃+* R} {f : P₁ →ₗ[R] P₀}
    (φ : ContragredientDual σ P₁) :
    toARTransposeLinearEquiv σ f (Submodule.Quotient.mk φ) =
      AuslanderReitenTranspose.mk f φ.toDual := by
  change arOppositeEquiv σ f (Submodule.Quotient.mk φ) =
    AuslanderReitenTranspose.mk f φ.toDual
  dsimp only [arOppositeEquiv]
  rw [AuslanderReitenTranspose.quotientEquiv_symm_mk]
  rfl

@[simp]
theorem toARTransposeLinearEquiv_symm_mk {σ : S ≃+* R} {f : P₁ →ₗ[R] P₀}
    (φ : Module.Dual R P₁) :
    haveI := RingHomInvPair.of_ringEquiv σ
    haveI := RingHomInvPair.of_ringEquiv_symm σ
    (toARTransposeLinearEquiv σ f).symm (AuslanderReitenTranspose.mk f φ) =
      Submodule.Quotient.mk (ContragredientDual.ofDual φ) := by
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  apply (toARTransposeLinearEquiv σ f).injective
  simp

/-- An isomorphism of presentation arrows `(e₁, e₀)` with `e₀ ∘ f = g ∘ e₁` induces an `S`-linear
equivalence between their transposes. -/
def congr (σ : S ≃+* R) {f : P₁ →ₗ[R] P₀} {g : Q₁ →ₗ[R] Q₀}
    (e₁ : P₁ ≃ₗ[R] Q₁) (e₀ : P₀ ≃ₗ[R] Q₀)
    (hfg : e₀.toLinearMap ∘ₗ f = g ∘ₗ e₁.toLinearMap) :
    PresentationTranspose σ f ≃ₗ[S] PresentationTranspose σ g :=
  Submodule.Quotient.equiv _ _ (ContragredientDual.congr σ e₁.symm) <| by
    have hcomp :
        (ContragredientDual.congr σ e₁.symm).toLinearMap ∘ₗ ContragredientDual.map σ f =
          ContragredientDual.map σ g ∘ₗ (ContragredientDual.congr σ e₀.symm).toLinearMap := by
      ext ψ q
      have h : f (e₁.symm q) = e₀.symm (g q) :=
        e₀.injective (by simpa using LinearMap.congr_fun hfg (e₁.symm q))
      simp [h]
    rw [← LinearMap.range_comp, hcomp, LinearEquiv.range_comp]

@[simp]
theorem congr_mk (σ : S ≃+* R) {f : P₁ →ₗ[R] P₀} {g : Q₁ →ₗ[R] Q₀}
    (e₁ : P₁ ≃ₗ[R] Q₁) (e₀ : P₀ ≃ₗ[R] Q₀)
    (hfg : e₀.toLinearMap ∘ₗ f = g ∘ₗ e₁.toLinearMap) (φ : ContragredientDual σ P₁) :
    congr σ e₁ e₀ hfg (Submodule.Quotient.mk φ) =
      Submodule.Quotient.mk (ContragredientDual.congr σ e₁.symm φ) := by
  simp [congr, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]

@[simp]
theorem congr_symm_mk (σ : S ≃+* R) {f : P₁ →ₗ[R] P₀} {g : Q₁ →ₗ[R] Q₀}
    (e₁ : P₁ ≃ₗ[R] Q₁) (e₀ : P₀ ≃ₗ[R] Q₀)
    (hfg : e₀.toLinearMap ∘ₗ f = g ∘ₗ e₁.toLinearMap) (ψ : ContragredientDual σ Q₁) :
    (congr σ e₁ e₀ hfg).symm (Submodule.Quotient.mk ψ) =
      Submodule.Quotient.mk (ContragredientDual.congr σ e₁ ψ) := by
  apply (congr σ e₁ e₀ hfg).injective
  simp only [LinearEquiv.apply_symm_apply, congr_mk]
  congr 1
  ext x
  simp

/-- The transpose of the identity presentation `id : P₁ →ₗ[R] P₁` vanishes. -/
instance subsingleton_id (σ : S ≃+* R) :
    Subsingleton (PresentationTranspose σ (LinearMap.id : P₁ →ₗ[R] P₁)) :=
  haveI := RingHomInvPair.of_ringEquiv σ
  haveI := RingHomInvPair.of_ringEquiv_symm σ
  (toARTransposeLinearEquiv σ (LinearMap.id : P₁ →ₗ[R] P₁)).toEquiv.subsingleton_congr.2
    (AuslanderReitenTranspose.subsingleton_of_comp_eq_id _ (LinearMap.id_comp LinearMap.id))

/-- The presentation `fst : R × R →ₗ[R] R`, `(a, b) ↦ a`, of the zero module has transpose
isomorphic to `S` via `[φ] ↦ σ⁻¹(φ (0, 1))`. This exhibits the dependence of the transpose on the
chosen presentation. -/
def fstEquiv (σ : S ≃+* R) : PresentationTranspose σ (LinearMap.fst R R R) ≃ₗ[S] S :=
  haveI : Subsingleton (AuslanderReitenTranspose (LinearMap.id : R →ₗ[R] R)) :=
    AuslanderReitenTranspose.subsingleton_of_comp_eq_id _ (LinearMap.id_comp _)
  haveI : Unique (AuslanderReitenTranspose (LinearMap.id : R →ₗ[R] R)) :=
    uniqueOfSubsingleton 0
  haveI := RingHomInvPair.of_ringEquiv σ
  haveI := RingHomInvPair.of_ringEquiv_symm σ
  ((toARTransposeLinearEquiv σ (LinearMap.fst R R R)).trans
    ((AuslanderReitenTranspose.compFstEquiv (LinearMap.id : R →ₗ[R] R) R).restrictScalars R)).trans
    (LinearEquiv.uniqueProd.trans
      ((LinearMap.ringLmapEquivSelf R R R).trans σ.toSemilinearEquiv.symm))

/-- `fstEquiv` sends the class of `φ` to `σ⁻¹(φ (0, 1))`. -/
@[simp]
theorem fstEquiv_mk (σ : S ≃+* R) (φ : ContragredientDual σ (R × R)) :
    fstEquiv σ (Submodule.Quotient.mk φ) = σ.symm (φ (0, 1)) := by
  have : Subsingleton (AuslanderReitenTranspose (LinearMap.id : R →ₗ[R] R)) :=
    AuslanderReitenTranspose.subsingleton_of_comp_eq_id _ (LinearMap.id_comp _)
  let _ : Unique (AuslanderReitenTranspose (LinearMap.id : R →ₗ[R] R)) :=
    uniqueOfSubsingleton 0
  have hmk : AuslanderReitenTranspose.mk (LinearMap.fst R R R) φ.toDual =
      AuslanderReitenTranspose.mk ((LinearMap.id : R →ₗ[R] R) ∘ₗ LinearMap.fst R R R)
        φ.toDual := rfl
  simp only [fstEquiv, LinearEquiv.trans_apply, toARTransposeLinearEquiv_mk,
    LinearEquiv.restrictScalars_apply, hmk, LinearEquiv.uniqueProd_apply,
    LinearMap.ringLmapEquivSelf_apply]
  rw [AuslanderReitenTranspose.compFstEquiv_mk]
  rfl

/-- The inverse of `fstEquiv` sends `s : S` to `s • [snd]`. -/
@[simp]
theorem fstEquiv_symm_apply (σ : S ≃+* R) (s : S) :
    (fstEquiv σ).symm s =
      s • (Submodule.Quotient.mk (ContragredientDual.ofDual (LinearMap.snd R R R)) :
        PresentationTranspose σ (LinearMap.fst R R R)) := by
  apply (fstEquiv σ).injective
  simp

/-- The transpose of multiplication by `a : R` (`R →(a) R`) is `S`-linearly isomorphic to
`S ⧸ Ideal.span {σ.symm a}` via `[φ] ↦ [σ⁻¹(φ 1)]`. -/
def mulLeftEquiv (σ : S ≃+* R) (a : R) :
    PresentationTranspose σ (LinearMap.mulLeft R a) ≃ₗ[S] S ⧸ Ideal.span {σ.symm a} :=
  haveI := RingHomInvPair.of_ringEquiv σ
  haveI := RingHomInvPair.of_ringEquiv_symm σ
  let eval₁ : ContragredientDual σ R ≃ₗ[S] S :=
    ((ContragredientDual.toDualLinearEquiv σ R).trans (LinearMap.ringLmapEquivSelf R R R)).trans
      σ.toSemilinearEquiv.symm
  have he : (LinearMap.range (ContragredientDual.map σ (LinearMap.mulLeft R a))).map
      eval₁.toLinearMap = Ideal.span {σ.symm a} := by
    have hdual : (LinearMap.range (ContragredientDual.map σ (LinearMap.mulLeft R a))).map
        (ContragredientDual.toDualLinearEquiv σ R).toLinearMap =
        LinearMap.range (LinearMap.mulLeft R a).dualMap := by
      have hcomp :
          (ContragredientDual.toDualLinearEquiv σ R).toLinearMap.comp
              (ContragredientDual.map σ (LinearMap.mulLeft R a)) =
            (LinearMap.mulLeft R a).dualMap.comp
              (ContragredientDual.toDualLinearEquiv σ R).toLinearMap := by
        ext ψ
        simp [LinearMap.dualMap_apply']
      rw [← LinearMap.range_comp, hcomp, LinearEquiv.range_comp]
    have hspan : (LinearMap.range (LinearMap.mulLeft R a).dualMap).map
        ((LinearMap.ringLmapEquivSelf R R R).trans σ.toSemilinearEquiv.symm).toLinearMap =
        Ideal.span {σ.symm a} := by
      rw [LinearMap.range_dualMap_dual_eq_span_singleton, Submodule.map_span]
      simp [Ideal.submodule_span_eq]
    rw [← hspan, ← hdual, ← Submodule.map_comp]
    rfl
  Submodule.Quotient.equiv _ (Ideal.span {σ.symm a}) eval₁ he

/-- `mulLeftEquiv` sends the class of `φ` to the quotient class of `σ⁻¹(φ 1)` modulo
`Ideal.span {σ.symm a}`. -/
@[simp]
theorem mulLeftEquiv_mk (σ : S ≃+* R) (a : R) (φ : ContragredientDual σ R) :
    mulLeftEquiv σ a (Submodule.Quotient.mk φ) =
      Ideal.Quotient.mk (Ideal.span {σ.symm a}) (σ.symm (φ 1)) := by
  change mulLeftEquiv σ a (Submodule.Quotient.mk φ) =
    Submodule.Quotient.mk (σ.symm (φ 1))
  simp only [mulLeftEquiv, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
    LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearMap.ringLmapEquivSelf_apply,
    ContragredientDual.toDualLinearEquiv_apply, ContragredientDual.toDual_apply]
  rfl

/-- The inverse of `mulLeftEquiv` sends `[s]` to `s • [id]`. -/
@[simp]
theorem mulLeftEquiv_symm_mk (σ : S ≃+* R) (a : R) (s : S) :
    (mulLeftEquiv σ a).symm (Ideal.Quotient.mk (Ideal.span {σ.symm a}) s) =
      s • (Submodule.Quotient.mk (ContragredientDual.ofDual LinearMap.id) :
        PresentationTranspose σ (LinearMap.mulLeft R a)) := by
  apply (mulLeftEquiv σ a).injective
  rw [LinearEquiv.apply_symm_apply, map_smul, mulLeftEquiv_mk]
  simp [← Ideal.Quotient.algebraMap_eq, Algebra.smul_def]

instance finitePresentation {σ : S ≃+* R} {f : P₁ →ₗ[R] P₀}
    [Module.Finite R P₀] [Module.Projective R P₀] [Module.Finite R P₁] [Module.Projective R P₁] :
    Module.FinitePresentation S (PresentationTranspose σ f) := by
  have : Module.FinitePresentation S (ContragredientDual σ P₁) :=
    Module.finitePresentation_of_projective _ _
  refine Module.finitePresentation_of_surjective _ (Submodule.mkQ_surjective _) ?_
  rw [Submodule.ker_mkQ]
  exact Submodule.fg_range _

end PresentationTranspose

end Basic

section FittingIdeal

variable {R S M P₀ P₁ : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
  [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁]

namespace PresentationTranspose

/-- **Quadratic presentation of the transpose.** If `P` is a quadratic presentation of `M` over
`R` with square relation matrix `P.rel`, then `PresentationTranspose σ (Matrix.toLin' P.rel)` is
quadratically presented over `S` of the same size `P.size` with relation matrix
`P.relᵀ.map σ.symm` up to `quadraticPresentation_size`. -/
def quadraticPresentation (σ : S ≃+* R) (P : QuadraticPresentation R M) :
    QuadraticPresentation S (PresentationTranspose σ (Matrix.toLin' P.rel)) :=
  QuadraticPresentation.ofExact P.size_pos
    ((Pi.basisFun R (Fin P.size)).contragredientDual σ)
    ((Pi.basisFun R (Fin P.size)).contragredientDual σ)
    (LinearMap.exact_iff.2 (Submodule.ker_mkQ _))
    (Submodule.mkQ_surjective _)

/-- The quadratic presentation of the transpose has the same size as `P`. -/
@[simp]
theorem quadraticPresentation_size (σ : S ≃+* R) (P : QuadraticPresentation R M) :
    (quadraticPresentation σ P).size = P.size :=
  (rfl)

/-- The relation matrix of `quadraticPresentation σ P` is `P.relᵀ.map σ.symm`, reindexed along
`quadraticPresentation_size σ P`. -/
@[simp]
theorem quadraticPresentation_rel (σ : S ≃+* R) (P : QuadraticPresentation R M) :
    (quadraticPresentation σ P).rel =
      Matrix.reindex (finCongr (quadraticPresentation_size σ P)).symm
        (finCongr (quadraticPresentation_size σ P)).symm (P.relᵀ.map σ.symm) := by
  ext i j
  simp [quadraticPresentation]
  rfl

/-- The relation matrix of `quadraticPresentation σ P` has determinant `σ⁻¹(det P.rel)`. -/
theorem det_quadraticPresentation_rel (σ : S ≃+* R) (P : QuadraticPresentation R M) :
    (quadraticPresentation σ P).rel.det = σ.symm P.rel.det := by
  rw [quadraticPresentation_rel, Matrix.det_reindex_self, ← P.rel.det_transpose]
  exact ((σ.symm : R →+* S).map_det P.relᵀ).symm

/-- The generator map of `quadraticPresentation σ P` sends `v` to the linear combination of the
classes of the coordinate projections in `PresentationTranspose σ (Matrix.toLin' P.rel)`. -/
theorem quadraticPresentation_gen_apply (σ : S ≃+* R) (P : QuadraticPresentation R M)
    (v : Fin (quadraticPresentation σ P).size → S) :
    (quadraticPresentation σ P).gen v =
      ∑ i : Fin P.size, v ((finCongr (quadraticPresentation_size σ P)).symm i) •
        (Submodule.Quotient.mk (ContragredientDual.ofDual (LinearMap.proj i)) :
          PresentationTranspose σ (Matrix.toLin' P.rel)) := by
  have h (w : Fin P.size → S) :
      (LinearMap.range (ContragredientDual.map σ (Matrix.toLin' P.rel))).mkQ
        (((Pi.basisFun R (Fin P.size)).contragredientDual σ).equivFun.symm w) =
        ∑ i : Fin P.size, w i •
          (Submodule.Quotient.mk (ContragredientDual.ofDual (LinearMap.proj i)) :
            PresentationTranspose σ (Matrix.toLin' P.rel)) := by
    rw [Module.Basis.equivFun_symm_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, Module.Basis.contragredientDual_apply]
    rfl
  exact h v

/-- **Fitting ideal of a transposed quadratic presentation** (Dasgupta–Kakde, Lemma 6.1): for a
quadratic presentation `P` of a finite `R`-module `M`,
`Fitt₀_S(PresentationTranspose σ (Matrix.toLin' P.rel)) = σ⁻¹(Fitt₀_R(M))`. -/
theorem fittingIdeal_eq (σ : S ≃+* R) (P : QuadraticPresentation R M) [Module.Finite R M] :
    TauCeti.fittingIdeal S (PresentationTranspose σ (Matrix.toLin' P.rel)) 0 =
      Ideal.map σ.symm (TauCeti.fittingIdeal R M 0) := by
  rw [(quadraticPresentation σ P).fittingIdeal_eq, P.fittingIdeal_eq,
    det_quadraticPresentation_rel, Ideal.map_span, Set.image_singleton]

/-- For an `m × t` matrix `A` over `R`, the zeroth Fitting ideal over `S` of the transpose of
`Matrix.toLin' A : (Fin t → R) →ₗ[R] (Fin m → R)` is the ideal of `t × t` minors of the transposed
matrix `Aᵀ.map σ.symm`. -/
theorem fittingIdeal_toLin'_eq_minorsIdeal (σ : S ≃+* R) {m t : ℕ} (A : Matrix (Fin m) (Fin t) R) :
    TauCeti.fittingIdeal S (PresentationTranspose σ (Matrix.toLin' A)) 0 =
      (LinearMap.range (Aᵀ.map σ.symm).mulVecLin).minorsIdeal t := by
  nontriviality S
  let d₀ := (Pi.basisFun R (Fin m)).contragredientDual σ
  let d₁ := (Pi.basisFun R (Fin t)).contragredientDual σ
  let q : (Fin t → S) →ₗ[S] PresentationTranspose σ (Matrix.toLin' A) :=
    (LinearMap.range (ContragredientDual.map σ (Matrix.toLin' A))).mkQ ∘ₗ
      d₁.equivFun.symm.toLinearMap
  have hq : Function.Surjective q := (Submodule.mkQ_surjective _).comp d₁.equivFun.symm.surjective
  have hex₀ : Function.Exact (ContragredientDual.map σ (Matrix.toLin' A))
      (LinearMap.range (ContragredientDual.map σ (Matrix.toLin' A))).mkQ :=
    LinearMap.exact_iff.2 (Submodule.ker_mkQ _)
  have hex₁ : Function.Exact (Aᵀ.map σ.symm).mulVecLin q := by
    dsimp only [q]
    rw [← Matrix.toLin'_apply', ← ContragredientDual.toMatrix_map_toLin' σ A,
      ← d₀.equivFun.precomp_exact_iff_exact,
      LinearMap.toLin'_toMatrix_comp_equivFun, LinearEquiv.conj_exact_iff_exact]
    exact hex₀
  rw [TauCeti.fittingIdeal_eq_minorsIdeal_ker hq 0, Module.finrank_fin_fun, Nat.sub_zero,
    hex₁.linearMap_ker_eq]

/-- For an `m × t` matrix `A` over `R`, the zeroth Fitting ideal over `S` of the transpose of
`Matrix.toLin' A` is the image along `σ⁻¹` of the ideal of `t × t` minors of `A`. -/
theorem fittingIdeal_toLin'_eq_map_minorsIdeal (σ : S ≃+* R) {m t : ℕ}
    (A : Matrix (Fin m) (Fin t) R) :
    TauCeti.fittingIdeal S (PresentationTranspose σ (Matrix.toLin' A)) 0 =
      Ideal.map σ.symm ((LinearMap.range A.mulVecLin).minorsIdeal t) := by
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  let Φ (k : ℕ) : (Fin k → R) ≃ₛₗ[(σ.symm : R →+* S)] (Fin k → S) :=
    { toFun x i := σ.symm (x i)
      invFun y i := σ (y i)
      map_add' x y := funext fun i ↦ map_add σ.symm _ _
      map_smul' a x := funext fun i ↦ map_mul σ.symm _ _
      left_inv x := funext fun i ↦ σ.apply_symm_apply _
      right_inv y := funext fun i ↦ σ.symm_apply_apply _ }
  have hcomp :
      (Φ t : (Fin t → R) →ₛₗ[(σ.symm : R →+* S)] (Fin t → S)) ∘ₛₗ Aᵀ.mulVecLin =
        (Aᵀ.map σ.symm).mulVecLin ∘ₛₗ (Φ m : (Fin m → R) →ₛₗ[(σ.symm : R →+* S)] (Fin m → S)) := by
    ext x i
    dsimp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply, Φ]
    simpa [Function.comp_def] using (σ.symm : R →+* S).map_mulVec Aᵀ x i
  have hrange :
      (LinearMap.range Aᵀ.mulVecLin).map (Φ t : (Fin t → R) →ₛₗ[(σ.symm : R →+* S)] (Fin t → S)) =
        LinearMap.range (Aᵀ.map σ.symm).mulVecLin := by
    rw [← Submodule.map_top Aᵀ.mulVecLin, ← Submodule.map_comp, hcomp, Submodule.map_comp,
      Submodule.map_top, LinearMap.range_eq_top.2 (Φ m).surjective, Submodule.map_top]
  rw [fittingIdeal_toLin'_eq_minorsIdeal, ← hrange,
    Submodule.minorsIdeal_map_semilinearEquiv, Matrix.minorsIdeal_range_transpose_mulVecLin]
  rfl

/-- **Free form of the excess-generators Fitting-ideal identity**: if `P₁ →f P₀ →π M → 0` is an
exact sequence of `R`-modules with `P₁` and `P₀` finite free of ranks `t` and `t + s`, then
`Fitt₀_S(PresentationTranspose σ f) = σ⁻¹(Fitt_s(M))`. -/
theorem fittingIdeal_eq_of_free (σ : S ≃+* R) {t s : ℕ}
    [Module.Finite R P₀] [Module.Free R P₀] [Module.Finite R P₁] [Module.Free R P₁]
    (f : P₁ →ₗ[R] P₀) (π : P₀ →ₗ[R] M) (hπ : Function.Surjective π)
    (hf : LinearMap.range f = LinearMap.ker π)
    (h₁ : Module.finrank R P₁ = t) (h₀ : Module.finrank R P₀ = t + s) [Module.Finite R M] :
    TauCeti.fittingIdeal S (PresentationTranspose σ f) 0 =
      Ideal.map σ.symm (TauCeti.fittingIdeal R M s) := by
  nontriviality S
  have : Nontrivial R := σ.symm.toEquiv.nontrivial
  let b₁ : Module.Basis (Fin t) R P₁ := Module.finBasisOfFinrankEq R P₁ h₁
  let b₀ : Module.Basis (Fin (t + s)) R P₀ := Module.finBasisOfFinrankEq R P₀ h₀
  let A : Matrix (Fin (t + s)) (Fin t) R := LinearMap.toMatrix b₁ b₀ f
  have hcomm : b₀.equivFun.toLinearMap ∘ₗ f = Matrix.toLin' A ∘ₗ b₁.equivFun.toLinearMap :=
    (LinearMap.toLin'_toMatrix_comp_equivFun b₁ b₀ f).symm
  let π' : (Fin (t + s) → R) →ₗ[R] M := π ∘ₗ b₀.equivFun.symm.toLinearMap
  have hπ' : Function.Surjective π' := hπ.comp b₀.equivFun.symm.surjective
  have hex : Function.Exact A.mulVecLin π' := by
    dsimp only [π']
    rw [← Matrix.toLin'_apply', ← b₁.equivFun.precomp_exact_iff_exact,
      LinearMap.toLin'_toMatrix_comp_equivFun, LinearEquiv.conj_exact_iff_exact]
    exact LinearMap.exact_iff.2 hf.symm
  rw [TauCeti.fittingIdeal_congr (congr σ b₁.equivFun b₀.equivFun hcomm) 0,
    fittingIdeal_toLin'_eq_map_minorsIdeal, TauCeti.fittingIdeal_eq_minorsIdeal_ker hπ' s,
    Module.finrank_fin_fun, Nat.add_sub_cancel, hex.linearMap_ker_eq]

/-- **Higher Fitting ideals and transposes with excess generators** (Dasgupta–Kakde, equation (171),
proof of Lemma B.4): if `P₁ →f P₀ →π M → 0` is an exact sequence of `R`-modules in which `P₁` and
`P₀` are finitely generated projective of constant stalk ranks `t` and `t + s` (without assuming
freeness), then `Fitt₀_S(PresentationTranspose σ f) = σ⁻¹(Fitt_s(M))`. -/
theorem fittingIdeal_eq_excess (σ : S ≃+* R) {t s : ℕ}
    [Module.Finite R P₀] [Module.Projective R P₀] [Module.Finite R P₁] [Module.Projective R P₁]
    (f : P₁ →ₗ[R] P₀) (π : P₀ →ₗ[R] M) (hπ : Function.Surjective π)
    (hf : LinearMap.range f = LinearMap.ker π)
    (h₁ : ∀ 𝔭 : PrimeSpectrum R, Module.rankAtStalk P₁ 𝔭 = t)
    (h₀ : ∀ 𝔭 : PrimeSpectrum R, Module.rankAtStalk P₀ 𝔭 = t + s)
    [Module.Finite R M] :
    TauCeti.fittingIdeal S (PresentationTranspose σ f) 0 =
      Ideal.map σ.symm (TauCeti.fittingIdeal R M s) := by
  have : Module.Finite R (AuslanderReitenTranspose f) :=
    Module.Finite.of_surjective ((AuslanderReitenTranspose.mk f).restrictScalars R)
      (AuslanderReitenTranspose.mk_surjective f)
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  rw [TauCeti.fittingIdeal_eq_map_of_semilinearEquiv (toARTransposeLinearEquiv σ f).symm 0]
  refine congrArg (Ideal.map (σ.symm : R →+* S)) ?_
  -- Check equality of ideals of `R` after localizing at every maximal ideal `𝔪`, where the
  -- finitely generated projective modules `P₁` and `P₀` become free of ranks `t` and `t + s`.
  refine Ideal.eq_of_localization_maximal fun 𝔪 h𝔪 ↦ ?_
  have : 𝔪.IsPrime := h𝔪.isPrime
  let T := Localization.AtPrime 𝔪
  have : Module.Free T (T ⊗[R] P₁) := Module.free_of_flat_of_isLocalRing
  have : Module.Free T (T ⊗[R] P₀) := Module.free_of_flat_of_isLocalRing
  have hrank₁ : Module.finrank T (T ⊗[R] P₁) = t :=
    TauCeti.Module.finrank_tensorProduct_eq_of_rankAtStalk_eq
      (funext fun 𝔭 ↦ (h₁ 𝔭).trans (by simp))
  have hrank₀ : Module.finrank T (T ⊗[R] P₀) = t + s :=
    TauCeti.Module.finrank_tensorProduct_eq_of_rankAtStalk_eq
      (funext fun 𝔭 ↦ (h₀ 𝔭).trans (by simp))
  have hexact0 : Function.Exact (f.baseChange T) (π.baseChange T) :=
    lTensor_exact T (LinearMap.exact_iff.2 hf.symm) hπ
  have hexact : LinearMap.range (f.baseChange T) = LinearMap.ker (π.baseChange T) :=
    (LinearMap.exact_iff.1 hexact0).symm
  have hsurj : Function.Surjective (π.baseChange T) := LinearMap.lTensor_surjective T hπ
  let eT : T ⊗[R] AuslanderReitenTranspose f ≃ₗ[T]
      PresentationTranspose (RingEquiv.refl T) (f.baseChange T) :=
    (AuslanderReitenTranspose.baseChangeEquiv T f).trans
      (toARTransposeLinearEquiv (RingEquiv.refl T) (f.baseChange T)).symm
  have hfree := fittingIdeal_eq_of_free (RingEquiv.refl T) (f.baseChange T) (π.baseChange T)
    hsurj hexact hrank₁ hrank₀
  rw [RingEquiv.symm_refl] at hfree
  change _ = Ideal.map (RingHom.id T) _ at hfree
  rw [Ideal.map_id] at hfree
  rw [← TauCeti.fittingIdeal_baseChange (AuslanderReitenTranspose f) T 0,
    ← TauCeti.fittingIdeal_baseChange M T s, TauCeti.fittingIdeal_congr eT 0, hfree]

end PresentationTranspose

end FittingIdeal

section Examples

-- The transpose of `id : R →ₗ[R] R` vanishes.
example {R S : Type*} [CommRing R] [CommRing S] (σ : S ≃+* R) :
    Subsingleton (PresentationTranspose σ (LinearMap.id : R →ₗ[R] R)) :=
  inferInstance

-- The presentation `R × R →ₗ[R] R, (a, b) ↦ a` of the zero module has transpose `≃ₗ[S] S`,
-- which is nontrivial whenever `S` is nontrivial.
example {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S] (σ : S ≃+* R) :
    Nontrivial (PresentationTranspose σ (LinearMap.fst R R R)) :=
  (PresentationTranspose.fstEquiv σ).toEquiv.nontrivial

-- The transpose of `R →(a) R` is `S`-linearly isomorphic to `S ⧸ Ideal.span {σ.symm a}`.
example {R S : Type*} [CommRing R] [CommRing S] (σ : S ≃+* R) (a : R) :
    Nonempty (PresentationTranspose σ (LinearMap.mulLeft R a) ≃ₗ[S] S ⧸ Ideal.span {σ.symm a}) :=
  ⟨PresentationTranspose.mulLeftEquiv σ a⟩

end Examples

end TauCeti
