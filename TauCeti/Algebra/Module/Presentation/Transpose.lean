/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Transpose
public import TauCeti.LinearAlgebra.Dual.Contragredient
public import TauCeti.Algebra.Module.Presentation.Quadratic

import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.LocalRing.Module
import TauCeti.Algebra.Module.AuslanderReiten.BaseChange
import TauCeti.Algebra.Module.AuslanderReiten.FinitePresentation
import TauCeti.RingTheory.FittingIdeal.BaseChange
import TauCeti.RingTheory.FittingIdeal.Matrix

/-!
# Transposed presentations and their Fitting ideals

Let `R` and `S` be commutative rings connected by a ring isomorphism `σ : S ≃+* R` (such as the
contragredient involution `# : R^# ≃+* R` on a group ring or character group ring), and let
`P₁ →f P₀ → M → 0` be a presentation of an `R`-module `M`. Applying the contragredient dual
`P^* = ContragredientDual σ P` reverses `f` into an `S`-linear map `f^* : P₀^* →ₗ[S] P₁^*`. Its
cokernel

  `PresentationTranspose σ f = coker(f^* : P₀^* → P₁^*)`

is the **transpose** attached to the presentation. Its underlying additive group is
`TauCeti.AuslanderReitenTranspose f`, with `S` acting through `s ↦ op (σ s)`. Note that Dasgupta
and Kakde write the presentation with indices swapped (`P₀ → P₁ → M`).

The transpose belongs to the presentation map `f`, not to the isomorphism class of `M` alone:
`id : R →ₗ[R] R` and `fst : R × R →ₗ[R] R` both present the zero module, yet the transpose of `id`
vanishes (`PresentationTranspose.subsingleton_id`) while the transpose of `fst` is isomorphic to
`S` (`PresentationTranspose.fstEquiv`).

When `f` comes from a quadratic presentation `P` of `M` with relation matrix `P.rel`, the transpose
carries a canonical quadratic presentation over `S` with relation matrix `P.relᵀ.map σ.symm`
(`PresentationTranspose.quadraticPresentation`), and therefore its zeroth Fitting ideal over `S`
is `σ⁻¹(Fitt₀(M))` (`PresentationTranspose.fittingIdeal_eq`, Dasgupta–Kakde Lemma 6.1). More
generally, if `P₁ →f P₀ → M → 0` is an exact presentation by finitely generated projective
`R`-modules of constant ranks `t` and `t + s` (without assuming `P₁` or `P₀` free), localizing at
maximal ideals of `R` reduces to the free case (`PresentationTranspose.fittingIdeal_eq_of_free`)
and shows `Fitt₀_S(M^tr) = σ⁻¹(Fitt_s(M))` (`PresentationTranspose.fittingIdeal_eq_excess`,
Dasgupta–Kakde equation (171)).

## Main definitions

* `TauCeti.PresentationTranspose σ f`: the cokernel `coker(f^* : P₀^* → P₁^*)` as an `S`-module
  along `σ : S ≃+* R`, with carrier `TauCeti.AuslanderReitenTranspose f`.
* `TauCeti.PresentationTranspose.toARTranspose` and
  `TauCeti.PresentationTranspose.toARTransposeLinearEquiv`: the additive and `σ`-semilinear
  identifications with `TauCeti.AuslanderReitenTranspose f`.
* `TauCeti.PresentationTranspose.mk` and `TauCeti.PresentationTranspose.lift`: the `S`-linear
  quotient map `ContragredientDual σ P₁ →ₗ[S] PresentationTranspose σ f` and its universal
  property.
* `TauCeti.PresentationTranspose.congr`: functoriality of the transpose under an isomorphism of
  presenting arrows.
* `TauCeti.PresentationTranspose.fstEquiv` and `TauCeti.PresentationTranspose.mulLeftEquiv`:
  explicit identifications `PresentationTranspose σ (LinearMap.fst R R R) ≃ₗ[S] S` and
  `PresentationTranspose σ (LinearMap.mulLeft R a) ≃ₗ[S] S ⧸ Ideal.span {σ.symm a}`.
* `TauCeti.PresentationTranspose.quadraticPresentation`: the quadratic presentation over `S` with
  matrix `P.relᵀ.map σ.symm` attached to a quadratic presentation `P` over `R`.

## Main results

* `TauCeti.PresentationTranspose.fittingIdeal_eq`: for a quadratic presentation `P` of a finite
  `R`-module `M`, `Fitt₀_S(PresentationTranspose σ (Matrix.toLin' P.rel)) = σ⁻¹(Fitt₀_R(M))`.
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
as an `S`-module along a ring isomorphism `σ : S ≃+* R` through `ContragredientDual`. Its carrier
is `AuslanderReitenTranspose f`, and it depends on the presentation arrow `f` rather than on
`coker f` alone. -/
def PresentationTranspose (_σ : S ≃+* R) (f : P₁ →ₗ[R] P₀) : Type _ :=
  AuslanderReitenTranspose f

instance (σ : S ≃+* R) (f : P₁ →ₗ[R] P₀) : AddCommGroup (PresentationTranspose σ f) :=
  inferInstanceAs (AddCommGroup (AuslanderReitenTranspose f))

namespace PresentationTranspose

/-- The underlying additive group of `PresentationTranspose σ f` is `AuslanderReitenTranspose f`. -/
def toARTranspose {σ : S ≃+* R} {f : P₁ →ₗ[R] P₀} :
    PresentationTranspose σ f ≃+ AuslanderReitenTranspose f := by
  -- Both sides share the same underlying `AddCommGroup` structure.
  with_unfolding_all
    exact AddEquiv.refl (AuslanderReitenTranspose f)

instance (σ : S ≃+* R) (f : P₁ →ₗ[R] P₀) : SMul S (PresentationTranspose σ f) where
  smul s x := toARTranspose.symm (σ s • toARTranspose x)

private theorem smul_def {σ : S ≃+* R} {f : P₁ →ₗ[R] P₀} (s : S) (x : PresentationTranspose σ f) :
    s • x = toARTranspose.symm (σ s • toARTranspose x) :=
  (rfl)

instance (σ : S ≃+* R) (f : P₁ →ₗ[R] P₀) : Module S (PresentationTranspose σ f) where
  one_smul x := by rw [smul_def, map_one, one_smul, AddEquiv.symm_apply_apply]
  mul_smul s t x := by
    rw [smul_def, smul_def, smul_def, map_mul, mul_smul, AddEquiv.apply_symm_apply]
  smul_zero s := by rw [smul_def, map_zero, smul_zero, map_zero]
  smul_add s x y := by rw [smul_def, smul_def, smul_def, map_add, smul_add, map_add]
  add_smul s t x := by rw [smul_def, smul_def, smul_def, map_add, add_smul, map_add]
  zero_smul x := by rw [smul_def, map_zero, zero_smul, map_zero]

/-- `toARTranspose` intertwines the `S`-action on `PresentationTranspose σ f` with the `R`-action
on `AuslanderReitenTranspose f` along `σ`. -/
@[simp]
theorem toARTranspose_smul {σ : S ≃+* R} {f : P₁ →ₗ[R] P₀}
    (s : S) (x : PresentationTranspose σ f) :
    toARTranspose (s • x) = σ s • toARTranspose x := by
  rw [smul_def, AddEquiv.apply_symm_apply]

@[simp]
theorem toARTranspose_symm_smul {σ : S ≃+* R} {f : P₁ →ₗ[R] P₀}
    (r : R) (y : AuslanderReitenTranspose f) :
    (toARTranspose (σ := σ) (f := f)).symm (r • y) =
      σ.symm r • (toARTranspose (σ := σ) (f := f)).symm y := by
  apply toARTranspose.injective
  rw [toARTranspose_smul, σ.apply_symm_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- `toARTranspose` as a `σ`-semilinear equivalence onto `AuslanderReitenTranspose f`. -/
def toARTransposeLinearEquiv (σ : S ≃+* R) (f : P₁ →ₗ[R] P₀) :
    haveI := RingHomInvPair.of_ringEquiv σ
    haveI := RingHomInvPair.of_ringEquiv_symm σ
    PresentationTranspose σ f ≃ₛₗ[(σ : S →+* R)] AuslanderReitenTranspose f :=
  haveI := RingHomInvPair.of_ringEquiv σ
  haveI := RingHomInvPair.of_ringEquiv_symm σ
  { toARTranspose with
    map_smul' := toARTranspose_smul }

@[simp]
theorem toARTransposeLinearEquiv_apply {σ : S ≃+* R} {f : P₁ →ₗ[R] P₀}
    (x : PresentationTranspose σ f) :
    toARTransposeLinearEquiv σ f x = toARTranspose x :=
  (rfl)

@[simp]
theorem toARTransposeLinearEquiv_symm_apply {σ : S ≃+* R} {f : P₁ →ₗ[R] P₀}
    (y : AuslanderReitenTranspose f) :
    (toARTransposeLinearEquiv σ f).symm y = toARTranspose.symm y :=
  (rfl)

/-- For `σ = RingEquiv.refl R`, `PresentationTranspose (RingEquiv.refl R) f` is `R`-linearly
equivalent to `AuslanderReitenTranspose f`. -/
def toARTransposeLinearEquivRefl (f : P₁ →ₗ[R] P₀) :
    PresentationTranspose (RingEquiv.refl R) f ≃ₗ[R] AuslanderReitenTranspose f where
  toFun := toARTranspose
  invFun := toARTranspose.symm
  map_add' := map_add toARTranspose
  map_smul' r x := by
    rw [toARTranspose_smul, RingEquiv.refl_apply, RingHom.id_apply]
  left_inv := toARTranspose.left_inv
  right_inv := toARTranspose.right_inv

/-- The `S`-linear quotient map `P₁^* →ₗ[S] PresentationTranspose σ f` from the contragredient dual
of `P₁` onto the transpose. -/
def mk (σ : S ≃+* R) (f : P₁ →ₗ[R] P₀) :
    ContragredientDual σ P₁ →ₗ[S] PresentationTranspose σ f where
  toFun φ := toARTranspose.symm (AuslanderReitenTranspose.mk f φ.toDual)
  map_add' φ ψ := by
    rw [ContragredientDual.toDual_add, map_add, map_add]
  map_smul' s φ := by
    apply toARTranspose.injective
    rw [toARTranspose_smul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      ContragredientDual.toDual_smul, ← AuslanderReitenTranspose.mkLinear_apply, map_smul,
      AuslanderReitenTranspose.mkLinear_apply, RingHom.id_apply]

@[simp]
theorem toARTranspose_mk {σ : S ≃+* R} {f : P₁ →ₗ[R] P₀} (φ : ContragredientDual σ P₁) :
    toARTranspose (mk σ f φ) = AuslanderReitenTranspose.mk f φ.toDual :=
  toARTranspose.apply_symm_apply _

/-- Every element of `PresentationTranspose σ f` is represented by an element of
`ContragredientDual σ P₁`. -/
theorem mk_surjective (σ : S ≃+* R) (f : P₁ →ₗ[R] P₀) : Function.Surjective (mk σ f) := fun x ↦ by
  obtain ⟨φ, hφ⟩ := AuslanderReitenTranspose.mk_surjective f (toARTranspose x)
  exact ⟨ContragredientDual.ofDual φ, toARTranspose.injective (by rw [toARTranspose_mk]; exact hφ)⟩

/-- A functional `φ ∈ P₁^*` represents `0` in `PresentationTranspose σ f` if and only if it lies in
the image of `f^* : P₀^* →ₗ[S] P₁^*` (that is, factors through `f`). -/
@[simp]
theorem mk_eq_zero_iff {σ : S ≃+* R} {f : P₁ →ₗ[R] P₀} (φ : ContragredientDual σ P₁) :
    mk σ f φ = 0 ↔ φ ∈ LinearMap.range (ContragredientDual.map σ f) := by
  rw [← toARTranspose.map_eq_zero_iff, toARTranspose_mk, AuslanderReitenTranspose.mk_eq_zero_iff]
  constructor
  · rintro ⟨ψ, hψ⟩
    refine ⟨ContragredientDual.ofDual ψ, ContragredientDual.toDual_injective ?_⟩
    simpa only [ContragredientDual.toDual_map, ContragredientDual.toDual_ofDual,
      LinearMap.lcomp_apply'] using hψ
  · rintro ⟨ψ, rfl⟩
    exact ⟨ψ.toDual, by rw [ContragredientDual.toDual_map, LinearMap.lcomp_apply']⟩

/-- The kernel of `mk σ f` is the range of `ContragredientDual.map σ f`. -/
@[simp]
theorem ker_mk (σ : S ≃+* R) (f : P₁ →ₗ[R] P₀) :
    LinearMap.ker (mk σ f) = LinearMap.range (ContragredientDual.map σ f) := by
  ext φ
  exact mk_eq_zero_iff φ

/-- The defining sequence `P₀^* →(f^*) P₁^* →(mk) PresentationTranspose σ f` is exact. -/
theorem exact (σ : S ≃+* R) (f : P₁ →ₗ[R] P₀) :
    Function.Exact (ContragredientDual.map σ f) (mk σ f) :=
  LinearMap.exact_iff.2 (ker_mk σ f)

@[simp]
theorem mk_map {σ : S ≃+* R} {f : P₁ →ₗ[R] P₀} (ψ : ContragredientDual σ P₀) :
    mk σ f (ContragredientDual.map σ f ψ) = 0 :=
  (exact σ f).apply_apply_eq_zero ψ

@[simp]
theorem mk_eq_mk_iff {σ : S ≃+* R} {f : P₁ →ₗ[R] P₀} (φ ψ : ContragredientDual σ P₁) :
    mk σ f φ = mk σ f ψ ↔ φ - ψ ∈ LinearMap.range (ContragredientDual.map σ f) := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff]

/-- Induction principle for `PresentationTranspose σ f` reducing to classes `mk σ f φ`. -/
@[elab_as_elim]
theorem induction_on {σ : S ≃+* R} {f : P₁ →ₗ[R] P₀}
    {motive : PresentationTranspose σ f → Prop} (x : PresentationTranspose σ f)
    (h : ∀ φ : ContragredientDual σ P₁, motive (mk σ f φ)) : motive x := by
  obtain ⟨φ, rfl⟩ := mk_surjective σ f x
  exact h φ

section Lift

variable {N : Type*} [AddCommGroup N] [Module S N]

/-- **Universal property of `PresentationTranspose`.** An `S`-linear map
`g : ContragredientDual σ P₁ →ₗ[S] N` that vanishes on `ContragredientDual.map σ f ψ` for all
`ψ ∈ P₀^*` descends to a unique `S`-linear map out of `PresentationTranspose σ f`. -/
def lift (σ : S ≃+* R) (f : P₁ →ₗ[R] P₀) (g : ContragredientDual σ P₁ →ₗ[S] N)
    (hg : ∀ ψ : ContragredientDual σ P₀, g (ContragredientDual.map σ f ψ) = 0) :
    PresentationTranspose σ f →ₗ[S] N := by
  letI : Module Rᵐᵒᵖ N :=
    Module.compHom N (σ.symm.toRingHom.comp (RingEquiv.toOpposite R).symm.toRingHom)
  let g' : Module.Dual R P₁ →ₗ[Rᵐᵒᵖ] N :=
    { toFun φ := g (ContragredientDual.ofDual φ)
      map_add' φ ψ := by rw [ContragredientDual.ofDual_add, map_add]
      map_smul' r φ := by
        have hr : r • φ = r.unop • φ := LinearMap.ext fun x ↦ mul_comm (φ x) r.unop
        -- Unfold the pulled-back `Rᵐᵒᵖ`-action on `N` to `σ⁻¹(r.unop) • ·`.
        change g (ContragredientDual.ofDual (r • φ)) =
          σ.symm r.unop • g (ContragredientDual.ofDual φ)
        rw [hr, ContragredientDual.ofDual_smul', map_smul] }
  have hg' (ψ : Module.Dual R P₀) : g' (f.lcomp Rᵐᵒᵖ R ψ) = 0 := by
    simpa only [g', LinearMap.coe_mk, AddHom.coe_mk, LinearMap.lcomp_apply',
      ← ContragredientDual.map_ofDual] using hg (ContragredientDual.ofDual ψ)
  let L := AuslanderReitenTranspose.lift f g' hg'
  exact
    { toFun x := L (toARTranspose x)
      map_add' x y := by rw [map_add, map_add]
      map_smul' s x := by
        have hL := L.map_smul (MulOpposite.op (σ s)) (toARTranspose x)
        -- Under `op r ↦ σ⁻¹ r`, `op (σ s)` acts on `N` as `σ⁻¹ (σ s) • ·`.
        change L (MulOpposite.op (σ s) • toARTranspose x) =
          σ.symm (σ s) • L (toARTranspose x) at hL
        rw [toARTranspose_smul, ← AuslanderReitenTranspose.op_algebraMap_smul (k := R) f (σ s),
          Algebra.algebraMap_self_apply, hL, σ.symm_apply_apply, RingHom.id_apply] }

@[simp]
theorem lift_mk (σ : S ≃+* R) (f : P₁ →ₗ[R] P₀) (g : ContragredientDual σ P₁ →ₗ[S] N)
    (hg : ∀ ψ : ContragredientDual σ P₀, g (ContragredientDual.map σ f ψ) = 0)
    (φ : ContragredientDual σ P₁) :
    lift σ f g hg (mk σ f φ) = g φ := by
  simp only [lift, LinearMap.coe_mk, AddHom.coe_mk, toARTranspose_mk,
    AuslanderReitenTranspose.lift_mk, ContragredientDual.ofDual_toDual]

@[simp]
theorem lift_comp_mk (σ : S ≃+* R) (f : P₁ →ₗ[R] P₀) (g : ContragredientDual σ P₁ →ₗ[S] N)
    (hg : ∀ ψ : ContragredientDual σ P₀, g (ContragredientDual.map σ f ψ) = 0) :
    (lift σ f g hg).comp (mk σ f) = g :=
  LinearMap.ext (lift_mk σ f g hg)

/-- `S`-linear maps out of `PresentationTranspose σ f` are determined by their values on
`mk σ f φ`. -/
@[ext]
theorem hom_ext {σ : S ≃+* R} {f : P₁ →ₗ[R] P₀}
    {h₁ h₂ : PresentationTranspose σ f →ₗ[S] N}
    (h : ∀ φ : ContragredientDual σ P₁, h₁ (mk σ f φ) = h₂ (mk σ f φ)) : h₁ = h₂ :=
  LinearMap.ext fun x ↦ induction_on x h

end Lift

/-- An isomorphism of presentation arrows `(e₁, e₀)` with `e₀ ∘ f = g ∘ e₁` induces an `S`-linear
equivalence between their transposes. -/
def congr (σ : S ≃+* R) {f : P₁ →ₗ[R] P₀} {g : Q₁ →ₗ[R] Q₀}
    (e₁ : P₁ ≃ₗ[R] Q₁) (e₀ : P₀ ≃ₗ[R] Q₀)
    (hfg : e₀.toLinearMap ∘ₗ f = g ∘ₗ e₁.toLinearMap) :
    PresentationTranspose σ f ≃ₗ[S] PresentationTranspose σ g := by
  have hgf : e₀.symm.toLinearMap ∘ₗ g = f ∘ₗ e₁.symm.toLinearMap := by
    ext y
    apply e₀.injective
    have hy := LinearMap.congr_fun hfg (e₁.symm y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at hy ⊢
    exact hy.symm
  refine LinearEquiv.ofLinearMap
    (lift σ f ((mk σ g).comp (ContragredientDual.congr σ e₁.symm).toLinearMap) fun ψ ↦ ?_)
    (lift σ g ((mk σ f).comp (ContragredientDual.congr σ e₁).toLinearMap) fun ψ ↦ ?_)
    (hom_ext fun φ ↦ ?_) (hom_ext fun φ ↦ ?_)
  · have hcomm : ContragredientDual.congr σ e₁.symm (ContragredientDual.map σ f ψ) =
        ContragredientDual.map σ g (ContragredientDual.congr σ e₀.symm ψ) := by
      ext y
      have hy := LinearMap.congr_fun hgf y
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hy
      simp [ ← hy]
    simp [hcomm]
  · have hcomm : ContragredientDual.congr σ e₁ (ContragredientDual.map σ g ψ) =
        ContragredientDual.map σ f (ContragredientDual.congr σ e₀ ψ) := by
      ext x
      have hx := LinearMap.congr_fun hfg x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hx
      simp [hx]
    simp [hcomm]
  · simp only [LinearMap.comp_apply, LinearMap.id_apply, lift_mk, LinearEquiv.coe_coe]
    congr 1
    ext y
    simp
  · simp only [LinearMap.comp_apply, LinearMap.id_apply, lift_mk, LinearEquiv.coe_coe]
    congr 1
    ext x
    simp

@[simp]
theorem congr_mk (σ : S ≃+* R) {f : P₁ →ₗ[R] P₀} {g : Q₁ →ₗ[R] Q₀}
    (e₁ : P₁ ≃ₗ[R] Q₁) (e₀ : P₀ ≃ₗ[R] Q₀)
    (hfg : e₀.toLinearMap ∘ₗ f = g ∘ₗ e₁.toLinearMap) (φ : ContragredientDual σ P₁) :
    congr σ e₁ e₀ hfg (mk σ f φ) = mk σ g (ContragredientDual.congr σ e₁.symm φ) := by
  simp [congr]

/-- A split monomorphism has vanishing transpose. -/
theorem subsingleton_of_comp_eq_id (σ : S ≃+* R) {f : P₁ →ₗ[R] P₀} {r : P₀ →ₗ[R] P₁}
    (hr : r ∘ₗ f = LinearMap.id) : Subsingleton (PresentationTranspose σ f) :=
  (toARTranspose (σ := σ) (f := f)).toEquiv.subsingleton_congr.2
    (AuslanderReitenTranspose.subsingleton_of_comp_eq_id f hr)

/-- For finitely generated projective `P₁`, the transpose vanishes iff `f` splits. -/
theorem subsingleton_iff_exists_comp_eq_id (σ : S ≃+* R) (f : P₁ →ₗ[R] P₀)
    [Module.Finite R P₁] [Module.Projective R P₁] :
    Subsingleton (PresentationTranspose σ f) ↔ ∃ r : P₀ →ₗ[R] P₁, r ∘ₗ f = LinearMap.id :=
  (toARTranspose (σ := σ) (f := f)).toEquiv.subsingleton_congr.trans
    (AuslanderReitenTranspose.subsingleton_iff_exists_comp_eq_id f)

/-- The transpose of the identity presentation `id : P₁ →ₗ[R] P₁` vanishes. -/
instance subsingleton_id (σ : S ≃+* R) :
    Subsingleton (PresentationTranspose σ (LinearMap.id : P₁ →ₗ[R] P₁)) :=
  subsingleton_of_comp_eq_id σ (r := LinearMap.id) (LinearMap.id_comp LinearMap.id)

/-- The presentation `fst : R × R →ₗ[R] R`, `(a, b) ↦ a`, of the zero module has transpose
isomorphic to `S` via `[φ] ↦ σ⁻¹(φ (0, 1))`. This exhibits the dependence of the transpose on the
chosen presentation. -/
def fstEquiv (σ : S ≃+* R) : PresentationTranspose σ (LinearMap.fst R R R) ≃ₗ[S] S := by
  let eval₀₁ : ContragredientDual σ (R × R) →ₗ[S] S :=
    { toFun φ := σ.symm (φ (0, 1))
      map_add' φ ψ := by simp
      map_smul' s φ := by
        rw [ContragredientDual.smul_apply_eq_mul, map_mul, σ.symm_apply_apply,
          RingHom.id_apply, smul_eq_mul] }
  let sndDual : ContragredientDual σ (R × R) := ContragredientDual.ofDual (LinearMap.snd R R R)
  have hsnd (p : R × R) : sndDual p = p.2 := rfl
  refine LinearEquiv.ofLinearMap
    (lift σ (LinearMap.fst R R R) eval₀₁ fun ψ ↦ by simp [eval₀₁])
    (LinearMap.toSpanSingleton S _ (mk σ (LinearMap.fst R R R) sndDual))
    (LinearMap.ext fun s ↦ by simp [eval₀₁, hsnd])
    (hom_ext fun φ ↦ ?_)
  simp only [LinearMap.comp_apply, LinearMap.id_apply, lift_mk, LinearMap.toSpanSingleton_apply,
    ← map_smul, eval₀₁, LinearMap.coe_mk, AddHom.coe_mk]
  rw [mk_eq_mk_iff]
  refine ⟨ContragredientDual.ofDual (-φ (1, 0) • LinearMap.id),
    ContragredientDual.ext fun ⟨a, b⟩ ↦ ?_⟩
  have hab : (a, b) = a • ((1 : R), (0 : R)) + b • ((0 : R), (1 : R)) := by
    ext <;> simp
  have hφab : φ (a, b) = a * φ (1, 0) + b * φ (0, 1) := by
    conv_lhs => rw [hab, map_add, ContragredientDual.map_smul_of_tower,
      ContragredientDual.map_smul_of_tower]
  rw [ContragredientDual.map_apply, ContragredientDual.ofDual_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.fst_apply, smul_eq_mul, ContragredientDual.sub_apply,
    ContragredientDual.smul_apply_eq_mul, σ.apply_symm_apply, hsnd, hφab]
  -- Normalize `φ.toDual (1, 0)` and projections of `(a, b)` before `ring`.
  change -φ (1, 0) * a = φ (0, 1) * b - (a * φ (1, 0) + b * φ (0, 1))
  ring

/-- The transpose of multiplication by `a : R` (`R →(a) R`) is `S`-linearly isomorphic to
`S ⧸ Ideal.span {σ.symm a}` via `[φ] ↦ [σ⁻¹(φ 1)]`. -/
def mulLeftEquiv (σ : S ≃+* R) (a : R) :
    PresentationTranspose σ (LinearMap.mulLeft R a) ≃ₗ[S] S ⧸ Ideal.span {σ.symm a} := by
  let I : Ideal S := Ideal.span {σ.symm a}
  let eval₁ : ContragredientDual σ R →ₗ[S] S :=
    { toFun φ := σ.symm (φ 1)
      map_add' φ ψ := by simp
      map_smul' s φ := by
        rw [ContragredientDual.smul_apply_eq_mul, map_mul, σ.symm_apply_apply,
          RingHom.id_apply, smul_eq_mul] }
  let idDual : ContragredientDual σ R := ContragredientDual.ofDual LinearMap.id
  have hidDual (x : R) : idDual x = x := rfl
  have hkill (ψ : ContragredientDual σ R) :
      I.mkQ (eval₁ (ContragredientDual.map σ (LinearMap.mulLeft R a) ψ)) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
    have hψ : ψ a = a * ψ 1 := by
      simpa only [smul_eq_mul, mul_one] using ψ.map_smul_of_tower a 1
    refine ⟨σ.symm (ψ 1), ?_⟩
    simp only [eval₁, LinearMap.coe_mk, AddHom.coe_mk, ContragredientDual.map_apply,
      LinearMap.mulLeft_apply, mul_one, hψ, map_mul]
  let inv₀ : S →ₗ[S] PresentationTranspose σ (LinearMap.mulLeft R a) :=
    LinearMap.toSpanSingleton S _ (mk σ (LinearMap.mulLeft R a) idDual)
  have hinv₀ : I ≤ LinearMap.ker inv₀ := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    simp only [inv₀, LinearMap.toSpanSingleton_apply, ← map_smul, mk_eq_zero_iff]
    refine ⟨idDual, ContragredientDual.ext fun x ↦ ?_⟩
    simp [hidDual]
  refine LinearEquiv.ofLinearMap
    (lift σ (LinearMap.mulLeft R a) (I.mkQ.comp eval₁) hkill)
    (I.liftQ inv₀ hinv₀)
    (LinearMap.ext fun q ↦ Submodule.Quotient.induction_on I q fun s ↦ by
      have hinv_s : inv₀ s = mk σ (LinearMap.mulLeft R a) (s • idDual) := by
        simp only [inv₀, LinearMap.toSpanSingleton_apply, map_smul]
      rw [LinearMap.comp_apply, LinearMap.id_apply, Submodule.liftQ_apply, hinv_s, lift_mk,
        LinearMap.comp_apply, eval₁.map_smul, Submodule.mkQ_apply]
      simp [eval₁, hidDual])
    (hom_ext fun φ ↦ ?_)
  simp only [LinearMap.comp_apply, LinearMap.id_apply, lift_mk, Submodule.mkQ_apply,
    Submodule.liftQ_apply, inv₀, LinearMap.toSpanSingleton_apply, ← map_smul, eval₁,
    LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  ext x
  have hx : φ x = x * φ 1 := by
    simpa only [smul_eq_mul, mul_one] using φ.map_smul_of_tower x 1
  simp [hx, hidDual, mul_comm]

instance finite {σ : S ≃+* R} {f : P₁ →ₗ[R] P₀} [Module.Finite R P₁] [Module.Projective R P₁] :
    Module.Finite S (PresentationTranspose σ f) :=
  Module.Finite.of_surjective (mk σ f) (mk_surjective σ f)

instance finitePresentation {σ : S ≃+* R} {f : P₁ →ₗ[R] P₀}
    [Module.Finite R P₀] [Module.Projective R P₀] [Module.Finite R P₁] [Module.Projective R P₁] :
    Module.FinitePresentation S (PresentationTranspose σ f) := by
  have : Module.FinitePresentation S (ContragredientDual σ P₁) :=
    Module.finitePresentation_of_projective _ _
  refine Module.finitePresentation_of_surjective (mk σ f) (mk_surjective σ f) ?_
  rw [ker_mk]
  exact Submodule.fg_range _

private theorem fittingIdeal_eq_map_arTranspose (σ : S ≃+* R)
    [Module.Finite R P₁] [Module.Projective R P₁] (f : P₁ →ₗ[R] P₀)
    [Module.Finite R (AuslanderReitenTranspose f)] (k : ℕ) :
    TauCeti.fittingIdeal S (PresentationTranspose σ f) k =
      Ideal.map σ.symm (TauCeti.fittingIdeal R (AuslanderReitenTranspose f) k) := by
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  exact (toARTransposeLinearEquiv σ f).symm.fittingIdeal_eq_map k

end PresentationTranspose

end Basic

section FittingIdeal

variable {R S M P₀ P₁ : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
  [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁]

namespace PresentationTranspose

/-- **Quadratic presentation of the transpose.** If `P` is a quadratic presentation of `M` over
`R` with square relation matrix `P.rel`, then `PresentationTranspose σ (Matrix.toLin' P.rel)` is
quadratically presented over `S` of the same size `P.size` with relation matrix
`P.relᵀ.map σ.symm`. -/
@[expose]
def quadraticPresentation (σ : S ≃+* R) (P : QuadraticPresentation R M) :
    QuadraticPresentation S (PresentationTranspose σ (Matrix.toLin' P.rel)) :=
  QuadraticPresentation.ofExact P.size_pos
    ((Pi.basisFun R (Fin P.size)).contragredientDual σ)
    ((Pi.basisFun R (Fin P.size)).contragredientDual σ)
    (exact σ (Matrix.toLin' P.rel))
    (mk_surjective σ (Matrix.toLin' P.rel))

@[simp]
theorem quadraticPresentation_size (σ : S ≃+* R) (P : QuadraticPresentation R M) :
    (quadraticPresentation σ P).size = P.size :=
  (rfl)

@[simp]
theorem quadraticPresentation_rel (σ : S ≃+* R) (P : QuadraticPresentation R M) :
    (quadraticPresentation σ P).rel = P.relᵀ.map σ.symm :=
  ContragredientDual.toMatrix_map_toLin' σ P.rel

/-- **Fitting ideal of a transposed quadratic presentation** (Dasgupta–Kakde, Lemma 6.1): for a
quadratic presentation `P` of a finite `R`-module `M`,
`Fitt₀_S(PresentationTranspose σ (Matrix.toLin' P.rel)) = σ⁻¹(Fitt₀_R(M))`. -/
theorem fittingIdeal_eq (σ : S ≃+* R) (P : QuadraticPresentation R M) [Module.Finite R M] :
    TauCeti.fittingIdeal S (PresentationTranspose σ (Matrix.toLin' P.rel)) 0 =
      Ideal.map σ.symm (TauCeti.fittingIdeal R M 0) := by
  let Mrel : Matrix (Fin P.size) (Fin P.size) S := (quadraticPresentation σ P).rel
  have hMrel : Mrel = P.relᵀ.map σ.symm := quadraticPresentation_rel σ P
  have hdet : Mrel.det = σ.symm P.rel.det := by
    rw [hMrel, ← P.rel.det_transpose]
    simp [Matrix.det_apply', map_sum σ.symm, map_prod σ.symm]
  rw [(quadraticPresentation σ P).fittingIdeal_eq, P.fittingIdeal_eq]
  -- Align the index type `(quadraticPresentation σ P).size` with `P.size`.
  change Ideal.span {Mrel.det} = Ideal.map σ.symm (Ideal.span {P.rel.det})
  rw [hdet, Ideal.map_span, Set.image_singleton]

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
    mk σ (Matrix.toLin' A) ∘ₗ d₁.equivFun.symm.toLinearMap
  have hq : Function.Surjective q := (mk_surjective σ _).comp d₁.equivFun.symm.surjective
  have hrel : Matrix.toLin' (Aᵀ.map σ.symm) =
      d₁.equivFun.toLinearMap ∘ₗ ContragredientDual.map σ (Matrix.toLin' A) ∘ₗ
        d₀.equivFun.symm.toLinearMap := by
    rw [← ContragredientDual.toMatrix_map_toLin' σ A]
    refine LinearMap.ext fun v ↦ funext fun i ↦ ?_
    have hv := LinearMap.toMatrix_mulVec_repr d₀ d₁ (ContragredientDual.map σ (Matrix.toLin' A))
      (d₀.equivFun.symm v)
    simpa only [Matrix.toLin'_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using congrFun hv i
  have hker : LinearMap.ker q = LinearMap.range (Aᵀ.map σ.symm).mulVecLin := by
    rw [← Matrix.toLin'_apply', hrel, LinearMap.range_comp,
      LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
      LinearMap.ker_comp, ker_mk, Submodule.map_equiv_eq_comap_symm]
  rw [TauCeti.fittingIdeal_eq_minorsIdeal_ker hq 0, Module.finrank_fin_fun, Nat.sub_zero, hker]

/-- For an `m × t` matrix `A` over `R`, the zeroth Fitting ideal over `S` of the transpose of
`Matrix.toLin' A` is the image along `σ⁻¹` of the ideal of `t × t` minors of `A`. -/
theorem fittingIdeal_toLin'_eq_map_minorsIdeal (σ : S ≃+* R) {m t : ℕ}
    (A : Matrix (Fin m) (Fin t) R) :
    TauCeti.fittingIdeal S (PresentationTranspose σ (Matrix.toLin' A)) 0 =
      Ideal.map σ.symm ((LinearMap.range A.mulVecLin).minorsIdeal t) := by
  rw [fittingIdeal_toLin'_eq_minorsIdeal, ← Matrix.minorsIdeal_range_transpose_mulVecLin A]
  have := RingHomInvPair.of_ringEquiv σ.symm
  have := RingHomInvPair.of_ringEquiv_symm σ.symm
  let piEquiv (n : ℕ) : (Fin n → R) ≃ₛₗ[(σ.symm : R →+* S)] (Fin n → S) :=
    { toFun v i := σ.symm (v i)
      invFun v i := σ (v i)
      map_add' _ _ := funext fun _ ↦ map_add σ.symm _ _
      map_smul' _ _ := funext fun _ ↦ map_mul σ.symm _ _
      left_inv _ := funext fun _ ↦ σ.apply_symm_apply _
      right_inv _ := funext fun _ ↦ σ.symm_apply_apply _ }
  let Pσ := piEquiv t
  let Qσ := piEquiv m
  have hmap : (LinearMap.range Aᵀ.mulVecLin).map (Pσ : (Fin t → R) →ₛₗ[(σ.symm : R →+* S)] _) =
      LinearMap.range (Aᵀ.map σ.symm).mulVecLin := by
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      refine ⟨Qσ w, funext fun i ↦ ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
      simp only [LinearEquiv.coe_coe, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        Matrix.map_apply]
      -- Evaluate `Pσ` and `Qσ` componentwise via `σ.symm`.
      change ∑ j, σ.symm (A j i) * σ.symm (w j) = σ.symm (∑ j, A j i * w j)
      simp [map_sum, map_mul]
    · rintro ⟨w, rfl⟩
      refine ⟨Aᵀ.mulVecLin (Qσ.symm w), ⟨Qσ.symm w, rfl⟩, funext fun i ↦ ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
      simp only [LinearEquiv.coe_coe, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        Matrix.map_apply]
      -- Evaluate `Pσ` via `σ.symm` and `Qσ.symm` via `σ`.
      change σ.symm (∑ j, A j i * σ (w j)) = ∑ j, σ.symm (A j i) * w j
      simp [map_sum, map_mul]
  rw [← hmap, Submodule.minorsIdeal_map_semilinearEquiv]
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
    LinearMap.ext fun x ↦ funext fun i ↦ by
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.toLin'_apply,
        ← Module.Basis.equivFun_apply, A] using
        congrFun (LinearMap.toMatrix_mulVec_repr b₁ b₀ f x).symm i
  let π' : (Fin (t + s) → R) →ₗ[R] M := π ∘ₗ b₀.equivFun.symm.toLinearMap
  have hπ' : Function.Surjective π' := hπ.comp b₀.equivFun.symm.surjective
  have hrel : Matrix.toLin' A =
      b₀.equivFun.toLinearMap ∘ₗ f ∘ₗ b₁.equivFun.symm.toLinearMap :=
    LinearMap.ext fun v ↦ funext fun i ↦ by
      have hv := LinearMap.toMatrix_mulVec_repr b₁ b₀ f (b₁.equivFun.symm v)
      simpa only [Matrix.toLin'_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, A] using congrFun hv i
  have hker : LinearMap.ker π' = LinearMap.range A.mulVecLin := by
    rw [← Matrix.toLin'_apply', hrel, LinearMap.range_comp,
      LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
      LinearMap.ker_comp, ← hf, Submodule.map_equiv_eq_comap_symm]
  rw [TauCeti.fittingIdeal_congr (congr σ b₁.equivFun b₀.equivFun hcomm) 0,
    fittingIdeal_toLin'_eq_map_minorsIdeal, TauCeti.fittingIdeal_eq_minorsIdeal_ker hπ' s,
    Module.finrank_fin_fun, Nat.add_sub_cancel, hker]

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
    Module.Finite.of_surjective (AuslanderReitenTranspose.mkLinear f)
      (AuslanderReitenTranspose.mkLinear_surjective f)
  rw [fittingIdeal_eq_map_arTranspose σ f 0]
  congr 1
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
      (toARTransposeLinearEquivRefl (f.baseChange T)).symm
  have hfree := fittingIdeal_eq_of_free (RingEquiv.refl T) (f.baseChange T) (π.baseChange T)
    hsurj hexact hrank₁ hrank₀
  have hmap_refl (J : Ideal T) : Ideal.map (RingEquiv.refl T).symm J = J := by
    ext x
    rw [RingEquiv.symm_refl, Ideal.mem_map_iff_of_surjective _ (RingEquiv.refl T).surjective]
    simp
  rw [hmap_refl] at hfree
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
