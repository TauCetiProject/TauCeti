/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Smooth.FixedPoints
public import TauCeti.RingTheory.WeilRestriction.Semilinear
public import TauCeti.RingTheory.WeilRestriction.Smooth
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Tame fixed-point schemes of Weil restrictions

Let `B` be a finite projective `A`-algebra and `C` a finitely presented `B`-algebra equipped with
an action `ρB` of a monoid `Γ` on `B` by `A`-algebra automorphisms and a semilinear action `ρC` on
`C` by ring automorphisms. By `WeilRestriction.inducedAction`, `Γ` acts on `WeilRestriction A B C`
by `A`-algebra automorphisms; the closed fixed-point subscheme `(Res_{B/A} Spec C)^Γ` is
represented by `WeilRestriction A B C ⧸ Algebra.fixedPointIdeal (inducedAction ρB ρC h)`.

On `T`-points, `A`-algebra homomorphisms out of this quotient correspond bijectively to
`Γ`-equivariant `B`-algebra homomorphisms `C →ₐ[B] B ⊗[A] T` (`fixedPointQuotientHomEquiv`). When
`ρC` is trivial, semilinearity forces `inducedAction ρB ρC h = 1` automatically without assuming
`ρB = 1` (`inducedAction_eq_one_of_eq_one`, `fixedPointIdeal_inducedAction_eq_bot`), so the
fixed-point quotient is canonically isomorphic to `WeilRestriction A B C`
(`fixedSchemeTrivialAlgEquiv`).

When `Γ` is a group whose order `Nat.card Γ` is invertible in `A` and `C` is formally smooth
(respectively smooth) over `B`, Edixhoven's tame fixed-point theorem combined with smoothness of
Weil restrictions shows that the fixed-point quotient is formally smooth (respectively smooth) over
`A`, with no local or henselian hypothesis on `A` (`formallySmooth_fixedPoints`,
`smooth_fixedPoints`).

For the affine line `C = Polynomial B` carrying the coefficient action `polynomialCoeffAction ρB`,
if `Γ` is a group with `IsUnit (Nat.card Γ : A)`, `algebraMap A B` is injective, and every
`Γ`-fixed element of `B` lies in `Set.range (algebraMap A B)`, the Reynolds-averaging retraction
`TauCeti.Algebra.linearRetractOfIsUnitCard` identifies `(B ⊗[A] T)^Γ` with `T`, so the fixed-point
scheme of `Res_{B/A} B[X]` is canonically `Polynomial A` (`fixedSchemePolynomialAlgEquiv`).

## Main definitions

* `TauCeti.Algebra.WeilRestriction.fixedPointQuotientHomEquiv`: `A`-algebra maps out of
  `WeilRestriction A B C ⧸ Algebra.fixedPointIdeal (inducedAction ρB ρC h)` into `T` correspond
  bijectively to `Γ`-equivariant `B`-algebra maps `C →ₐ[B] B ⊗[A] T`.
* `TauCeti.Algebra.WeilRestriction.fixedSchemeTrivialAlgEquiv`: when `ρC = 1`, the fixed-point
  quotient is canonically isomorphic to `WeilRestriction A B C`.
* `TauCeti.Algebra.WeilRestriction.polynomialCoeffAction` and
  `TauCeti.Algebra.WeilRestriction.fixedSchemePolynomialAlgEquiv`: the coefficient action of `Γ` on
  `Polynomial B` and the descent isomorphism identifying the fixed-point quotient of
  `WeilRestriction A B (Polynomial B)` with `Polynomial A`.

## Main results

* `TauCeti.Algebra.WeilRestriction.inducedAction_eq_one_of_eq_one` and
  `TauCeti.Algebra.WeilRestriction.fixedPointIdeal_inducedAction_eq_bot`: a trivial action on `C`
  induces the trivial action on `WeilRestriction A B C` and cuts out the zero ideal.
* `TauCeti.Algebra.WeilRestriction.formallySmooth_fixedPoints` and
  `TauCeti.Algebra.WeilRestriction.smooth_fixedPoints`: Edixhoven's tame fixed-point theorem for
  Weil restrictions of formally smooth and smooth algebras.
* `TauCeti.Algebra.WeilRestriction.homEquiv_fixedSchemePolynomialAlgEquiv_comp_mkₐ`: on universal
  points, `fixedSchemePolynomialAlgEquiv` classifies evaluation at `1 ⊗ₜ X`.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), §2.4 (p. 292),
  Prop. 3.1 (p. 293), and Prop. 3.4 (pp. 294–295).
-/

public noncomputable section

open Algebra TensorProduct Polynomial

namespace TauCeti.Algebra.WeilRestriction

section General

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  [Module.Finite A B] [Module.Projective A B] [FinitePresentation B C]

section Monoid

variable {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
  (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))

/-- **Universal property of the fixed-point scheme of a Weil restriction.** `A`-algebra maps from
`WeilRestriction A B C ⧸ fixedPointIdeal (inducedAction ρB ρC h)` to `T` correspond bijectively to
`Γ`-equivariant `B`-algebra homomorphisms `C →ₐ[B] B ⊗[A] T`. -/
def fixedPointQuotientHomEquiv (T : Type*) [CommRing T] [Algebra A T] :
    ((WeilRestriction A B C ⧸ fixedPointIdeal (inducedAction ρB ρC h)) →ₐ[A] T) ≃
      {y : C →ₐ[B] B ⊗[A] T //
        ∀ γ c, y (ρC γ c) = Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y c)} :=
  (fixedPointQuotientAlgHomEquiv (inducedAction ρB ρC h) T).trans
    { toFun g := ⟨homEquiv A B C T g.1, fun γ ↦ (comp_inducedAction_eq_iff ρB ρC h γ g.1).1 (g.2 γ)⟩
      invFun y := ⟨(homEquiv A B C T).symm y.1, fun γ ↦ by
        rw [comp_inducedAction_eq_iff, Equiv.apply_symm_apply]
        exact y.2 γ⟩
      left_inv g := Subtype.ext ((homEquiv A B C T).symm_apply_apply g.1)
      right_inv y := Subtype.ext ((homEquiv A B C T).apply_symm_apply y.1) }

/-- The `Γ`-equivariant `B`-algebra map attached to `f` is `homEquiv` applied to `f ∘ mkₐ`. -/
@[simp]
theorem fixedPointQuotientHomEquiv_apply {T : Type*} [CommRing T] [Algebra A T]
    (f : (WeilRestriction A B C ⧸ fixedPointIdeal (inducedAction ρB ρC h)) →ₐ[A] T) :
    (fixedPointQuotientHomEquiv ρB ρC h T f).1 =
      homEquiv A B C T
        (f.comp (Ideal.Quotient.mkₐ A (fixedPointIdeal (inducedAction ρB ρC h)))) := by
  simp [fixedPointQuotientHomEquiv]

/-- Precomposing `(fixedPointQuotientHomEquiv ρB ρC h T).symm y` with `mkₐ` classifies `y`. -/
theorem homEquiv_fixedPointQuotientHomEquiv_symm_comp_mkₐ {T : Type*} [CommRing T] [Algebra A T]
    (y : {y : C →ₐ[B] B ⊗[A] T //
      ∀ γ c, y (ρC γ c) = Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y c)}) :
    homEquiv A B C T (((fixedPointQuotientHomEquiv ρB ρC h T).symm y).comp
      (Ideal.Quotient.mkₐ A (fixedPointIdeal (inducedAction ρB ρC h)))) = y.1 := by
  have h1 := fixedPointQuotientHomEquiv_apply ρB ρC h
    ((fixedPointQuotientHomEquiv ρB ρC h T).symm y)
  rw [(fixedPointQuotientHomEquiv ρB ρC h T).apply_symm_apply] at h1
  exact h1.symm

/-- If `Γ` acts trivially on `C`, the induced action on `WeilRestriction A B C` is trivial, even
without assuming `ρB = 1`. -/
theorem inducedAction_eq_one_of_eq_one (hC : ρC = 1) :
    inducedAction ρB ρC h = 1 := by
  ext γ x
  let W := WeilRestriction A B C
  let u : C →ₐ[B] B ⊗[A] W := homEquiv A B C W (AlgHom.id A W)
  have hb (b : B) : (ρB γ b) ⊗ₜ[A] (1 : W) = b ⊗ₜ[A] (1 : W) := by
    have hu := congrArg u (h γ b)
    rw [hC, MonoidHom.one_apply, RingAut.one_apply, AlgHom.commutes, AlgHom.commutes,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply] at hu
    exact hu.symm
  have hr : Algebra.TensorProduct.rTensor W (ρB γ : B →ₐ[A] B) = AlgHom.id A (B ⊗[A] W) := by
    apply Algebra.TensorProduct.ext'
    intro b w
    calc
      Algebra.TensorProduct.rTensor W (ρB γ : B →ₐ[A] B) (b ⊗ₜ[A] w)
          = ((ρB γ b) ⊗ₜ[A] (1 : W)) * ((1 : B) ⊗ₜ[A] w) := by
            simp [Algebra.TensorProduct.rTensor]
      _ = (b ⊗ₜ[A] (1 : W)) * ((1 : B) ⊗ₜ[A] w) := by rw [hb]
      _ = b ⊗ₜ[A] w := by simp
  have hcomp : (AlgHom.id A W).comp (inducedAction ρB ρC h γ : W →ₐ[A] W) = AlgHom.id A W := by
    rw [comp_inducedAction_eq_iff]
    intro c
    rw [hC, MonoidHom.one_apply, RingAut.one_apply, hr, AlgHom.id_apply]
  simpa [W] using DFunLike.congr_fun hcomp x

/-- If `Γ` acts trivially on `C`, the displacement ideal on `WeilRestriction A B C` is zero. -/
theorem fixedPointIdeal_inducedAction_eq_bot (hC : ρC = 1) :
    fixedPointIdeal (inducedAction ρB ρC h) = ⊥ := by
  rw [fixedPointIdeal_eq_bot_iff]
  exact inducedAction_eq_one_of_eq_one ρB ρC h hC

/-- When `Γ` acts trivially on `C`, the fixed-point quotient of `WeilRestriction A B C` is
canonically isomorphic to `WeilRestriction A B C`. -/
def fixedSchemeTrivialAlgEquiv (hC : ρC = 1) :
    (WeilRestriction A B C ⧸ fixedPointIdeal (inducedAction ρB ρC h)) ≃ₐ[A]
      WeilRestriction A B C :=
  (Ideal.quotientEquivAlgOfEq A (fixedPointIdeal_inducedAction_eq_bot ρB ρC h hC)).trans
    (AlgEquiv.quotientBot A (WeilRestriction A B C))

/-- `fixedSchemeTrivialAlgEquiv` sends the quotient class of `x` to `x`. -/
@[simp]
theorem fixedSchemeTrivialAlgEquiv_mk (hC : ρC = 1) (x : WeilRestriction A B C) :
    fixedSchemeTrivialAlgEquiv ρB ρC h hC
      (Ideal.Quotient.mk (fixedPointIdeal (inducedAction ρB ρC h)) x) = x := by
  rw [fixedSchemeTrivialAlgEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  rfl

end Monoid

section Smooth

variable {Γ : Type*} [Group Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
  (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))

/-- **Edixhoven's tame fixed-point formal smoothness theorem for Weil restrictions.** If `Γ` is a
group with `IsUnit (Nat.card Γ : A)` acting semilinearly on a formally smooth finitely presented
`B`-algebra `C` along a finite projective `A`-algebra `B`, then the fixed-point quotient of
`WeilRestriction A B C` is formally smooth over `A`. -/
theorem formallySmooth_fixedPoints [FormallySmooth B C] (hΓ : IsUnit (Nat.card Γ : A)) :
    FormallySmooth A (WeilRestriction A B C ⧸ fixedPointIdeal (inducedAction ρB ρC h)) :=
  formallySmooth_quotient_fixedPointIdeal (inducedAction ρB ρC h) hΓ

/-- **Edixhoven's tame fixed-point theorem for Weil restrictions.** If `Γ` is a group with
`IsUnit (Nat.card Γ : A)` acting semilinearly on a smooth `B`-algebra `C` along a finite projective
`A`-algebra `B`, then the fixed-point quotient of `WeilRestriction A B C` is smooth over `A`
(Edixhoven, Props. 3.1 and 3.4, pp. 293–295). -/
theorem smooth_fixedPoints [Smooth B C] (hΓ : IsUnit (Nat.card Γ : A)) :
    Smooth A (WeilRestriction A B C ⧸ fixedPointIdeal (inducedAction ρB ρC h)) :=
  smooth_quotient_fixedPointIdeal (inducedAction ρB ρC h) hΓ

end Smooth

end General

section PolynomialCoeffAction

/-- An action `ρB` of a monoid `Γ` on a semiring `B` by `A`-algebra automorphisms induces a
coefficient-wise action on `Polynomial B` by ring automorphisms fixing the indeterminate `X`. -/
def polynomialCoeffAction {A B Γ : Type*} [CommSemiring A] [Semiring B] [Algebra A B] [Monoid Γ]
    (ρB : Γ →* (B ≃ₐ[A] B)) : Γ →* RingAut (Polynomial B) where
  toFun γ := Polynomial.mapEquiv (ρB γ).toRingEquiv
  map_one' := RingEquiv.ext fun p ↦ by
    simp only [Polynomial.mapEquiv_apply, map_one]
    exact (congrArg (Polynomial.map · p) (RingHom.ext fun _ ↦ rfl)).trans Polynomial.map_id
  map_mul' γ δ := RingEquiv.ext fun p ↦ by
    simp only [RingAut.mul_apply, Polynomial.mapEquiv_apply, Polynomial.map_map, map_mul]
    exact congrArg (Polynomial.map · p) (RingHom.ext fun _ ↦ rfl)

/-- `polynomialCoeffAction ρB γ` acts on scalar polynomials `C b` via `ρB γ`. -/
@[simp]
theorem polynomialCoeffAction_C {A B Γ : Type*} [CommSemiring A] [Semiring B] [Algebra A B]
    [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (γ : Γ) (b : B) :
    polynomialCoeffAction ρB γ (Polynomial.C b) = Polynomial.C (ρB γ b) :=
  Polynomial.map_C _

/-- `polynomialCoeffAction ρB γ` fixes the indeterminate `X`. -/
@[simp]
theorem polynomialCoeffAction_X {A B Γ : Type*} [CommSemiring A] [Semiring B] [Algebra A B]
    [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (γ : Γ) :
    polynomialCoeffAction ρB γ Polynomial.X = Polynomial.X :=
  Polynomial.map_X _

/-- `polynomialCoeffAction ρB` is semilinear over `ρB` along `algebraMap B (Polynomial B)`. -/
theorem polynomialCoeffAction_algebraMap {A B Γ : Type*} [CommSemiring A] [CommSemiring B]
    [Algebra A B] [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (γ : Γ) (b : B) :
    polynomialCoeffAction ρB γ (algebraMap B (Polynomial B) b) =
      algebraMap B (Polynomial B) (ρB γ b) :=
  polynomialCoeffAction_C ρB γ b

end PolynomialCoeffAction

section AffineLine

variable {A B Γ : Type*} [CommRing A] [CommRing B] [Algebra A B]

private theorem aeval_one_tmul_X_polynomialCoeffAction [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B))
    (γ : Γ) (p : Polynomial B) :
    (Polynomial.aeval (1 ⊗ₜ[A] (Polynomial.X : Polynomial A) : B ⊗[A] Polynomial A))
      (polynomialCoeffAction ρB γ p) =
    Algebra.TensorProduct.rTensor (Polynomial A) (ρB γ : B →ₐ[A] B)
      (Polynomial.aeval (1 ⊗ₜ[A] (Polynomial.X : Polynomial A)) p) := by
  have hhom :
      (Polynomial.aeval
          (1 ⊗ₜ[A] (Polynomial.X : Polynomial A) : B ⊗[A] Polynomial A)).toRingHom.comp
        (polynomialCoeffAction ρB γ).toRingHom =
      (Algebra.TensorProduct.rTensor (Polynomial A) (ρB γ : B →ₐ[A] B)).toRingHom.comp
        (Polynomial.aeval (1 ⊗ₜ[A] (Polynomial.X : Polynomial A))).toRingHom :=
    Polynomial.ringHom_ext
      (fun b ↦ by simp [Polynomial.aeval_C, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.rTensor])
      (by simp [Algebra.TensorProduct.rTensor])
  exact DFunLike.congr_fun hhom p

private def fixedSchemePolynomialToAlgHom [Module.Finite A B] [Module.Projective A B] [Monoid Γ]
    (ρB : Γ →* (B ≃ₐ[A] B)) :
    (WeilRestriction A B (Polynomial B) ⧸
      fixedPointIdeal (inducedAction ρB (polynomialCoeffAction ρB)
        (polynomialCoeffAction_algebraMap ρB))) →ₐ[A] Polynomial A :=
  (fixedPointQuotientHomEquiv ρB (polynomialCoeffAction ρB)
    (polynomialCoeffAction_algebraMap ρB) (Polynomial A)).symm
      ⟨Polynomial.aeval (1 ⊗ₜ Polynomial.X), aeval_one_tmul_X_polynomialCoeffAction ρB⟩

private theorem lid_rTensor_linearRetractOfIsUnitCard_one_tmul [Group Γ] (ρB : Γ →* (B ≃ₐ[A] B))
    (hΓ : IsUnit (Nat.card Γ : A)) (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B))
    (p : Polynomial A) :
    Algebra.TensorProduct.lid A (Polynomial A)
      (LinearMap.rTensor (Polynomial A) (linearRetractOfIsUnitCard ρB hΓ hinj hfix)
        ((1 : B) ⊗ₜ[A] p)) = p := by
  rw [LinearMap.rTensor_tmul, Algebra.TensorProduct.lid_tmul, ← map_one (algebraMap A B),
    linearRetractOfIsUnitCard_algebraMap, one_smul]

/-- **Tame Galois descent of the affine line.** Let `B` be a finite projective `A`-algebra with
an action `ρB` of a group `Γ` with `IsUnit (Nat.card Γ : A)` such that `algebraMap A B` is
injective and `B^Γ ⊆ Set.range (algebraMap A B)`. Then the fixed-point quotient of
`WeilRestriction A B (Polynomial B)` under the coefficient action is canonically isomorphic to
`Polynomial A`. -/
def fixedSchemePolynomialAlgEquiv [Module.Finite A B] [Module.Projective A B]
    [Group Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (hΓ : IsUnit (Nat.card Γ : A))
    (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B)) :
    (WeilRestriction A B (Polynomial B) ⧸
      fixedPointIdeal (inducedAction ρB (polynomialCoeffAction ρB)
        (polynomialCoeffAction_algebraMap ρB))) ≃ₐ[A] Polynomial A := by
  let hcompat := polynomialCoeffAction_algebraMap ρB
  let I := fixedPointIdeal (inducedAction ρB (polynomialCoeffAction ρB) hcompat)
  let Q := WeilRestriction A B (Polynomial B) ⧸ I
  let e := fixedPointQuotientHomEquiv ρB (polynomialCoeffAction ρB) hcompat
  let ψ : Q →ₐ[A] Polynomial A := fixedSchemePolynomialToAlgHom ρB
  let π := linearRetractOfIsUnitCard ρB hΓ hinj hfix
  let uQ := e Q (AlgHom.id A Q)
  let q₀ : Q := Algebra.TensorProduct.lid A Q (LinearMap.rTensor Q π (uQ.1 Polynomial.X))
  have hzQ : Algebra.TensorProduct.includeRight q₀ = uQ.1 Polynomial.X :=
    includeRight_lid_rTensor_linearRetractOfIsUnitCard_of_fixed ρB hΓ hinj hfix Q
      (uQ.1 Polynomial.X) fun γ ↦ by
        have hX := uQ.2 γ Polynomial.X
        rw [polynomialCoeffAction_X] at hX
        exact hX.symm
  refine AlgEquiv.ofAlgHom ψ (Polynomial.aeval q₀) ?_ ?_
  · apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, AlgHom.id_apply, Polynomial.aeval_X]
    -- Transport `1 ⊗ₜ q₀ = uQ.1 X` along `B ⊗ ψ`, then apply the retraction `lid ∘ (π ⊗ id)`.
    have hnat : Algebra.TensorProduct.lTensor (S := B) B ψ (uQ.1 Polynomial.X) =
        1 ⊗ₜ[A] Polynomial.X := by
      have hcomp : homEquiv A B (Polynomial B) (Polynomial A)
          (ψ.comp (Ideal.Quotient.mkₐ A I)) = Polynomial.aeval (1 ⊗ₜ Polynomial.X) :=
        homEquiv_fixedPointQuotientHomEquiv_symm_comp_mkₐ ρB (polynomialCoeffAction ρB) hcompat _
      rw [homEquiv_comp (T := Q) (T' := Polynomial A)] at hcomp
      simpa only [uQ, e, I, Q, fixedPointQuotientHomEquiv_apply, AlgHom.id_comp,
        AlgHom.comp_apply, Polynomial.aeval_X] using DFunLike.congr_fun hcomp Polynomial.X
    have heq : (1 : B) ⊗ₜ[A] ψ q₀ = (1 : B) ⊗ₜ[A] Polynomial.X := by
      rw [← hnat, ← hzQ]
      simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lTensor]
    simpa only [π, lid_rTensor_linearRetractOfIsUnitCard_one_tmul ρB hΓ hinj hfix] using congrArg
      (fun w ↦ Algebra.TensorProduct.lid A (Polynomial A) (LinearMap.rTensor (Polynomial A) π w))
      heq
  · refine (e Q).injective <| Subtype.ext <| Polynomial.algHom_ext ?_
    simp only [e, ψ, fixedSchemePolynomialToAlgHom, fixedPointQuotientHomEquiv_apply,
      AlgHom.id_comp]
    rw [AlgHom.comp_assoc, homEquiv_comp (T := Polynomial A) (T' := Q),
      homEquiv_fixedPointQuotientHomEquiv_symm_comp_mkₐ]
    simpa only [AlgHom.comp_apply, Polynomial.aeval_X, Algebra.TensorProduct.lTensor,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.includeRight_apply, uQ,
      e, I, Q, fixedPointQuotientHomEquiv_apply, AlgHom.id_comp] using hzQ

/-- Precomposing `fixedSchemePolynomialAlgEquiv` with the quotient map classifies evaluation of
`Polynomial B` at `1 ⊗ₜ X ∈ B ⊗[A] Polynomial A`. -/
theorem homEquiv_fixedSchemePolynomialAlgEquiv_comp_mkₐ [Module.Finite A B] [Module.Projective A B]
    [Group Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (hΓ : IsUnit (Nat.card Γ : A))
    (hinj : Function.Injective (algebraMap A B))
    (hfix : ∀ b : B, (∀ γ : Γ, ρB γ b = b) → b ∈ Set.range (algebraMap A B)) :
    homEquiv A B (Polynomial B) (Polynomial A)
      ((fixedSchemePolynomialAlgEquiv ρB hΓ hinj hfix).toAlgHom.comp
        (Ideal.Quotient.mkₐ A
          (fixedPointIdeal (inducedAction ρB (polynomialCoeffAction ρB)
            (polynomialCoeffAction_algebraMap ρB))))) =
      Polynomial.aeval (1 ⊗ₜ[A] Polynomial.X) :=
  homEquiv_fixedPointQuotientHomEquiv_symm_comp_mkₐ ρB (polynomialCoeffAction ρB)
    (polynomialCoeffAction_algebraMap ρB) _

end AffineLine

end TauCeti.Algebra.WeilRestriction
