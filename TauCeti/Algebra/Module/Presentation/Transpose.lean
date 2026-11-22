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

  `PresentationTranspose σ f = coker(f^* : P₀^* → P₁^*)`

is the **transpose** attached to the presentation. Its underlying additive group is
`TauCeti.AuslanderReitenTranspose f`, with `S` acting through `s ↦ op (σ s)`. Note that Dasgupta
and Kakde write the presentation with indices swapped (`P₀ → P₁ → M`).

The transpose belongs to the presentation map `f`, not to the isomorphism class of `M` alone:
`id : R →ₗ[R] R` and `fst : R × R →ₗ[R] R` both present the zero module, yet the transpose of `id`
vanishes (`PresentationTranspose.subsingleton_id`) while the transpose of `fst` is isomorphic to
`S` (`PresentationTranspose.fstEquiv`).

When `f` comes from a quadratic presentation `P` of `M` with relation matrix `P.rel`, the transpose
carries a canonical quadratic presentation over `S` with relation matrix `P.relᵀ.map σ.symm` up to
canonical index identification (`PresentationTranspose.quadraticPresentation`), of determinant
`σ⁻¹(det P.rel)` (`PresentationTranspose.det_quadraticPresentation_rel`), and therefore its zeroth
Fitting ideal over `S` is `σ⁻¹(Fitt₀(M))` (`PresentationTranspose.fittingIdeal_eq`, Dasgupta–Kakde
Lemma 6.1). More
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

instance (σ : S ≃+* R) (f : P₁ →ₗ[R] P₀) : Module S (PresentationTranspose σ f) :=
  letI := Module.compHom (AuslanderReitenTranspose f) (σ : S →+* R)
  inferInstanceAs (Module S (AuslanderReitenTranspose f))

/-- `toARTranspose` intertwines the `S`-action on `PresentationTranspose σ f` with the `R`-action
on `AuslanderReitenTranspose f` along `σ`. -/
@[simp]
theorem toARTranspose_smul {σ : S ≃+* R} {f : P₁ →ₗ[R] P₀}
    (s : S) (x : PresentationTranspose σ f) :
    toARTranspose (s • x) = σ s • toARTranspose x := by
  with_unfolding_all
    rfl

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
      ContragredientDual.toDual_smul, RingHom.id_apply]
    exact ((AuslanderReitenTranspose.mk f).restrictScalars R).map_smul (σ s) φ.toDual

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
    PresentationTranspose σ f →ₗ[S] N :=
  (mk σ f).liftOfSurjective (mk_surjective σ f) ⟨g, by
    rw [ker_mk]
    rintro _ ⟨ψ, rfl⟩
    exact hg ψ⟩

@[simp]
theorem lift_mk (σ : S ≃+* R) (f : P₁ →ₗ[R] P₀) (g : ContragredientDual σ P₁ →ₗ[S] N)
    (hg : ∀ ψ : ContragredientDual σ P₀, g (ContragredientDual.map σ f ψ) = 0)
    (φ : ContragredientDual σ P₁) :
    lift σ f g hg (mk σ f φ) = g φ :=
  LinearMap.equivOfSurjective_apply (mk_surjective σ f) _

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
equivalence between their transposes, obtained by transporting
`AuslanderReitenTranspose.linearEquiv` along `toARTranspose`. -/
def congr (σ : S ≃+* R) {f : P₁ →ₗ[R] P₀} {g : Q₁ →ₗ[R] Q₀}
    (e₁ : P₁ ≃ₗ[R] Q₁) (e₀ : P₀ ≃ₗ[R] Q₀)
    (hfg : e₀.toLinearMap ∘ₗ f = g ∘ₗ e₁.toLinearMap) :
    PresentationTranspose σ f ≃ₗ[S] PresentationTranspose σ g :=
  haveI := RingHomInvPair.of_ringEquiv σ
  haveI := RingHomInvPair.of_ringEquiv_symm σ
  ((toARTransposeLinearEquiv σ f).trans
    ((AuslanderReitenTranspose.linearEquiv e₀ e₁ hfg).restrictScalars R)).trans
    (toARTransposeLinearEquiv σ g).symm

@[simp]
theorem congr_mk (σ : S ≃+* R) {f : P₁ →ₗ[R] P₀} {g : Q₁ →ₗ[R] Q₀}
    (e₁ : P₁ ≃ₗ[R] Q₁) (e₀ : P₀ ≃ₗ[R] Q₀)
    (hfg : e₀.toLinearMap ∘ₗ f = g ∘ₗ e₁.toLinearMap) (φ : ContragredientDual σ P₁) :
    congr σ e₁ e₀ hfg (mk σ f φ) = mk σ g (ContragredientDual.congr σ e₁.symm φ) := by
  apply toARTranspose.injective
  simp only [congr, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    toARTransposeLinearEquiv_apply, toARTransposeLinearEquiv_symm_apply, toARTranspose_mk,
    AddEquiv.apply_symm_apply, AuslanderReitenTranspose.linearEquiv_mk]
  congr 1
  ext x
  simp [LinearMap.lcomp_apply]

@[simp]
theorem congr_symm_mk (σ : S ≃+* R) {f : P₁ →ₗ[R] P₀} {g : Q₁ →ₗ[R] Q₀}
    (e₁ : P₁ ≃ₗ[R] Q₁) (e₀ : P₀ ≃ₗ[R] Q₀)
    (hfg : e₀.toLinearMap ∘ₗ f = g ∘ₗ e₁.toLinearMap) (ψ : ContragredientDual σ Q₁) :
    (congr σ e₁ e₀ hfg).symm (mk σ g ψ) = mk σ f (ContragredientDual.congr σ e₁ ψ) := by
  apply (congr σ e₁ e₀ hfg).injective
  simp only [LinearEquiv.apply_symm_apply, congr_mk]
  congr 1
  ext x
  simp

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
    fstEquiv σ (mk σ (LinearMap.fst R R R) φ) = σ.symm (φ (0, 1)) := by
  have : Subsingleton (AuslanderReitenTranspose (LinearMap.id : R →ₗ[R] R)) :=
    AuslanderReitenTranspose.subsingleton_of_comp_eq_id _ (LinearMap.id_comp _)
  let _ : Unique (AuslanderReitenTranspose (LinearMap.id : R →ₗ[R] R)) :=
    uniqueOfSubsingleton 0
  have hmk : AuslanderReitenTranspose.mk (LinearMap.fst R R R) φ.toDual =
      AuslanderReitenTranspose.mk ((LinearMap.id : R →ₗ[R] R) ∘ₗ LinearMap.fst R R R)
        φ.toDual := rfl
  simp only [fstEquiv, LinearEquiv.trans_apply, toARTransposeLinearEquiv_apply,
    toARTranspose_mk, LinearEquiv.restrictScalars_apply, hmk, LinearEquiv.uniqueProd_apply,
    LinearMap.ringLmapEquivSelf_apply]
  rw [AuslanderReitenTranspose.compFstEquiv_mk]
  rfl

/-- The inverse of `fstEquiv` sends `s : S` to `s • [snd]`. -/
@[simp]
theorem fstEquiv_symm_apply (σ : S ≃+* R) (s : S) :
    (fstEquiv σ).symm s =
      s • mk σ (LinearMap.fst R R R) (ContragredientDual.ofDual (LinearMap.snd R R R)) := by
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
  have he : (LinearMap.ker (mk σ (LinearMap.mulLeft R a))).map eval₁.toLinearMap =
      Ideal.span {σ.symm a} := by
    have hdual : (LinearMap.ker (mk σ (LinearMap.mulLeft R a))).map
        (ContragredientDual.toDualLinearEquiv σ R).toLinearMap =
        LinearMap.range (LinearMap.mulLeft R a).dualMap := by
      rw [ker_mk, ← LinearMap.range_comp]
      ext φ
      simp only [LinearMap.mem_range, LinearMap.comp_apply, LinearEquiv.coe_coe,
        ContragredientDual.toDualLinearEquiv_apply]
      constructor
      · rintro ⟨ψ, hψ⟩
        refine ⟨ψ.toDual, ?_⟩
        simpa [ContragredientDual.toDual_map, LinearMap.dualMap_apply'] using hψ
      · rintro ⟨ψ, hψ⟩
        refine ⟨ContragredientDual.ofDual ψ, ?_⟩
        simpa [ContragredientDual.toDual_map, LinearMap.dualMap_apply'] using hψ
    have hspan : (LinearMap.range (LinearMap.mulLeft R a).dualMap).map
        ((LinearMap.ringLmapEquivSelf R R R).trans σ.toSemilinearEquiv.symm).toLinearMap =
        Ideal.span {σ.symm a} := by
      rw [LinearMap.range_dualMap_dual_eq_span_singleton, Submodule.map_span]
      simp [Ideal.submodule_span_eq]
    rw [← hspan, ← hdual, ← Submodule.map_comp]
    rfl
  ((mk σ (LinearMap.mulLeft R a)).quotKerEquivOfSurjective (mk_surjective σ _)).symm.trans
    (Submodule.Quotient.equiv _ (Ideal.span {σ.symm a}) eval₁ he)

/-- `mulLeftEquiv` sends the class of `φ` to the quotient class of `σ⁻¹(φ 1)` modulo
`Ideal.span {σ.symm a}`. -/
@[simp]
theorem mulLeftEquiv_mk (σ : S ≃+* R) (a : R) (φ : ContragredientDual σ R) :
    mulLeftEquiv σ a (mk σ (LinearMap.mulLeft R a) φ) =
      Ideal.Quotient.mk (Ideal.span {σ.symm a}) (σ.symm (φ 1)) := by
  change (mulLeftEquiv σ a (mk σ (LinearMap.mulLeft R a) φ)) =
    Submodule.Quotient.mk (σ.symm (φ 1))
  simp only [mulLeftEquiv, LinearEquiv.trans_apply, LinearMap.quotKerEquivOfSurjective_symm_apply,
    Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, LinearEquiv.coe_coe,
    LinearMap.ringLmapEquivSelf_apply, ContragredientDual.toDualLinearEquiv_apply,
    ContragredientDual.toDual_apply]
  rfl

/-- The inverse of `mulLeftEquiv` sends `[s]` to `s • [id]`. -/
@[simp]
theorem mulLeftEquiv_symm_mk (σ : S ≃+* R) (a : R) (s : S) :
    (mulLeftEquiv σ a).symm (Ideal.Quotient.mk (Ideal.span {σ.symm a}) s) =
      s • mk σ (LinearMap.mulLeft R a) (ContragredientDual.ofDual LinearMap.id) := by
  apply (mulLeftEquiv σ a).injective
  rw [LinearEquiv.apply_symm_apply, map_smul, mulLeftEquiv_mk]
  simp [← Ideal.Quotient.algebraMap_eq, Algebra.smul_def]

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
    (exact σ (Matrix.toLin' P.rel))
    (mk_surjective σ (Matrix.toLin' P.rel))

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
        mk σ (Matrix.toLin' P.rel) (ContragredientDual.ofDual (LinearMap.proj i)) := by
  have h (w : Fin P.size → S) :
      mk σ (Matrix.toLin' P.rel)
        (((Pi.basisFun R (Fin P.size)).contragredientDual σ).equivFun.symm w) =
        ∑ i : Fin P.size, w i •
          mk σ (Matrix.toLin' P.rel) (ContragredientDual.ofDual (LinearMap.proj i)) := by
    rw [Module.Basis.equivFun_symm_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, Module.Basis.contragredientDual_apply]
    congr 2
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
    mk σ (Matrix.toLin' A) ∘ₗ d₁.equivFun.symm.toLinearMap
  have hq : Function.Surjective q := (mk_surjective σ _).comp d₁.equivFun.symm.surjective
  have hrel : Matrix.toLin' (Aᵀ.map σ.symm) =
      d₁.equivFun.toLinearMap ∘ₗ ContragredientDual.map σ (Matrix.toLin' A) ∘ₗ
        d₀.equivFun.symm.toLinearMap := by
    have hcomm := LinearMap.toLin'_toMatrix_comp_equivFun d₀ d₁
      (ContragredientDual.map σ (Matrix.toLin' A))
    rw [ContragredientDual.toMatrix_map_toLin'] at hcomm
    simpa only [LinearMap.comp_assoc, LinearEquiv.comp_symm, LinearMap.comp_id] using
      congrArg (· ∘ₗ d₀.equivFun.symm.toLinearMap) hcomm
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
      exact ((σ.symm : R →+* S).map_mulVec Aᵀ w i).symm
    · rintro ⟨w, rfl⟩
      refine ⟨Aᵀ.mulVecLin (Qσ.symm w), ⟨Qσ.symm w, rfl⟩, funext fun i ↦ ?_⟩
      have h : Pσ (Aᵀ.mulVecLin (Qσ.symm w)) i =
          ((Aᵀ.map σ.symm).mulVecLin (Qσ (Qσ.symm w))) i :=
        (σ.symm : R →+* S).map_mulVec Aᵀ (Qσ.symm w) i
      simpa only [LinearEquiv.coe_coe, Qσ.apply_symm_apply] using h
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
    (LinearMap.toLin'_toMatrix_comp_equivFun b₁ b₀ f).symm
  have hrel : Matrix.toLin' A =
      b₀.equivFun.toLinearMap ∘ₗ f ∘ₗ b₁.equivFun.symm.toLinearMap := by
    simpa only [LinearMap.comp_assoc, LinearEquiv.comp_symm, LinearMap.comp_id] using
      congrArg (· ∘ₗ b₁.equivFun.symm.toLinearMap) hcomm.symm
  let π' : (Fin (t + s) → R) →ₗ[R] M := π ∘ₗ b₀.equivFun.symm.toLinearMap
  have hπ' : Function.Surjective π' := hπ.comp b₀.equivFun.symm.surjective
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
