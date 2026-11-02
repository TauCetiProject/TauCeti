/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Derivative
public import Mathlib.RingTheory.Kaehler.Basic

import TauCeti.RingTheory.Dagger.Noetherian

/-!
# Universally finite differentials of overconvergent algebras

Mathlib's Kähler differentials `Ω[A⁄K]` are the wrong module of differentials for a
Monsky–Washnitzer algebra `W = K⟨X₁, …, Xₙ⟩†`: they see the transcendental relations between
overconvergent series, and they are in general not finitely generated over `W`. Grosse-Klönne's
module of differentials `Ω¹_A` of a dagger algebra `A` is instead universal among derivations into
*finite* modules. This file defines it for every commutative `K`-algebra `A`, as the quotient
`Omega K A` of `Ω[A⁄K]` by the intersection of all submodules with finite quotient, with the
derivation `Omega.d`. When `A` is noetherian every derivation into a finite `A`-module factors
uniquely through `Omega.d`.

For `W` itself the module is free on `dX₁, …, dXₙ`, with `dg = ∑ᵢ (∂g/∂Xᵢ) dXᵢ`. The input is
that a derivation of `W` into a finite module is determined by its values on the variables. If
`D` kills the variables, then it kills the polynomials, and every class of `W ⧸ m ^ (k + 1)`, for
a maximal ideal `m`, has a polynomial representative, so `D` maps `W` into `m ^ k M` for every
`k`. Since the powers of the maximal ideals separate the finite module `M`, `D = 0`. The
polynomial representatives come from Weierstrass division in one variable at a time: modulo an
ideal of finite codimension each variable satisfies its minimal polynomial over `K`, a polynomial
with constant coefficients and hence distinguished at the unit radius. These inputs are
`TauCeti.Dagger.washnitzerAlgebra.surjective_mkₐ_comp_ofMvPolynomial` and
`TauCeti.Dagger.washnitzerAlgebra.derivation_ext`.

## Main definitions

* `TauCeti.Dagger.Omega K A`: the universally finite module of differentials of `A` over `K`.
* `TauCeti.Dagger.Omega.d`: its universal derivation, and `TauCeti.Dagger.Omega.ofKaehler`, the
  canonical surjection from Mathlib's Kähler differentials.
* `TauCeti.Dagger.Omega.lift`: the linear map induced by a derivation into a noetherian module.
* `TauCeti.Dagger.Omega.washnitzerBasis`: the basis `dX₁, …, dXₙ` of `Ω¹_W`, which is therefore a
  finite free `W`-module.

## Main results

* `TauCeti.Dagger.Omega.existsUnique_lift`: the universal property of `Omega.d`.
* `TauCeti.Dagger.Omega.washnitzerBasis_repr_d`: the coordinates of `dg` are the partial
  derivatives of `g`.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §4.1.
* E. Grosse-Klönne, *Finiteness of de Rham cohomology in rigid analysis*, Duke Math. J. 113
  (2002), §1.2.
* K. Kedlaya, *Finiteness of rigid cohomology with coefficients*, Duke Math. J. 134 (2006),
  §3.1.
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries

section Omega

variable (K A : Type*) [CommRing K] [CommRing A] [Algebra K A]

/-- The intersection of all submodules of `Ω[A⁄K]` with finite quotient: the kernel of the
canonical surjection `Ω[A⁄K] → Ω¹_{A/K}`. -/
noncomputable def Omega.finiteKer : Submodule A Ω[A⁄K] :=
  ⨅ (N : Submodule A Ω[A⁄K]) (_ : Module.Finite A (Ω[A⁄K] ⧸ N)), N

/-- The **universally finite module of differentials** `Ω¹_{A/K}`: the quotient of the Kähler
differentials `Ω[A⁄K]` by the intersection of all submodules with finite quotient. For a dagger
algebra this is Grosse-Klönne's module of differentials. -/
def Omega : Type _ :=
  Ω[A⁄K] ⧸ Omega.finiteKer K A

namespace Omega

noncomputable instance : AddCommGroup (Omega K A) :=
  inferInstanceAs (AddCommGroup (Ω[A⁄K] ⧸ finiteKer K A))

noncomputable instance : Module A (Omega K A) := inferInstanceAs (Module A (Ω[A⁄K] ⧸ finiteKer K A))

noncomputable instance : Module K (Omega K A) := inferInstanceAs (Module K (Ω[A⁄K] ⧸ finiteKer K A))

instance : IsScalarTower K A (Omega K A) :=
  inferInstanceAs (IsScalarTower K A (Ω[A⁄K] ⧸ finiteKer K A))

/-- The canonical surjection from the Kähler differentials. -/
noncomputable def ofKaehler : Ω[A⁄K] →ₗ[A] Omega K A :=
  (finiteKer K A).mkQ

/-- Every element of `Ω¹_{A/K}` comes from a Kähler differential. -/
theorem ofKaehler_surjective : Function.Surjective (ofKaehler K A) :=
  (finiteKer K A).mkQ_surjective

variable {K A} in
/-- A Kähler differential vanishes in `Omega K A` iff it lies in every submodule of `Ω[A⁄K]` with
finite quotient. -/
theorem ofKaehler_eq_zero_iff {x : Ω[A⁄K]} :
    ofKaehler K A x = 0 ↔ ∀ N : Submodule A Ω[A⁄K], Module.Finite A (Ω[A⁄K] ⧸ N) → x ∈ N :=
  (Submodule.Quotient.mk_eq_zero (finiteKer K A)).trans (by simp [finiteKer, Submodule.mem_iInf])

/-- The **universal derivation** `d : A → Ω¹_{A/K}`. -/
noncomputable def d : Derivation K A (Omega K A) :=
  (ofKaehler K A).compDer (KaehlerDifferential.D K A)

/-- The canonical surjection is compatible with the universal derivations. -/
@[simp]
theorem ofKaehler_D (a : A) : ofKaehler K A (KaehlerDifferential.D K A a) = d K A a :=
  (rfl)

/-- The differentials `d a` span `Ω¹_{A/K}`. -/
theorem span_range_d : Submodule.span A (Set.range (d K A)) = ⊤ := by
  have h : Set.range (d K A) = ofKaehler K A '' Set.range (KaehlerDifferential.D K A) := by
    rw [← Set.range_comp]
    rfl
  rw [h, Submodule.span_image, KaehlerDifferential.span_range_derivation, Submodule.map_top,
    LinearMap.range_eq_top.mpr (ofKaehler_surjective K A)]

variable {K A}

/-- Two linear maps out of `Ω¹_{A/K}` agreeing on every `d a` are equal. -/
@[ext]
theorem hom_ext {M : Type*} [AddCommGroup M] [Module A M] {u v : Omega K A →ₗ[A] M}
    (h : ∀ a, u (d K A a) = v (d K A a)) : u = v :=
  LinearMap.ext_on_range (span_range_d K A) h

variable {M : Type*} [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
  [IsNoetherian A M]

/-- The kernel of the linear map induced on Kähler differentials by a derivation into a
noetherian module has finite quotient, so it contains the intersection defining `Omega`. -/
private theorem finiteKer_le_ker (D : Derivation K A M) :
    finiteKer K A ≤ LinearMap.ker D.liftKaehlerDifferential :=
  iInf₂_le (LinearMap.ker D.liftKaehlerDifferential)
    (Module.Finite.equiv D.liftKaehlerDifferential.quotKerEquivRange.symm)

/-- The linear map `Ω¹_{A/K} → M` induced by a derivation into a noetherian module, for instance
a finite module over a noetherian ring. -/
noncomputable def lift (D : Derivation K A M) : Omega K A →ₗ[A] M :=
  (finiteKer K A).liftQ D.liftKaehlerDifferential (finiteKer_le_ker D)

/-- On Kähler differentials, `lift D` is the linear map induced by `D`. -/
@[simp]
theorem lift_ofKaehler (D : Derivation K A M) (x : Ω[A⁄K]) :
    lift D (ofKaehler K A x) = D.liftKaehlerDifferential x :=
  (rfl)

/-- `lift D` sends `d a` to `D a`. -/
@[simp]
theorem lift_d (D : Derivation K A M) (a : A) : lift D (d K A a) = D a :=
  D.liftKaehlerDifferential_comp_D a

/-- **The universal property of `Ω¹_{A/K}`.** Every derivation into a noetherian module, for
instance a finite module over a noetherian ring, factors uniquely through `d`. -/
theorem existsUnique_lift (D : Derivation K A M) :
    ∃! u : Omega K A →ₗ[A] M, ∀ a, u (d K A a) = D a :=
  ⟨lift D, lift_d D, fun _ hu ↦ hom_ext fun a ↦ (hu a).trans (lift_d D a).symm⟩

end Omega

end Omega

namespace Omega

open washnitzerAlgebra

variable (σ K : Type*) [Finite σ] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "W" => washnitzerAlgebra σ K

/-- The partial derivatives, assembled into a derivation into the free module `σ → W`. -/
private noncomputable def pderivPi : Derivation K W (σ → W) where
  toLinearMap := LinearMap.pi fun i ↦ (pderiv σ K i).toLinearMap
  map_one_eq_zero' := funext fun i ↦ (pderiv σ K i).map_one_eq_zero
  leibniz' a b := funext fun i ↦ (pderiv σ K i).leibniz a b

omit [Finite σ] [CompleteSpace K] in
private theorem pderivPi_apply (g : W) (i : σ) : pderivPi σ K g i = pderiv σ K i g :=
  (rfl)

omit [CompleteSpace K] in
private theorem pderivPi_X (i : σ) : pderivPi σ K (X σ K i) = Pi.basisFun W σ i := by
  classical
  funext j
  obtain rfl | h := eq_or_ne j i
  · simp [pderivPi_apply]
  · simp [pderivPi_apply, washnitzerAlgebra.pderiv_X_of_ne h.symm, h]

/-- The coordinate map `Ω¹_W → σ → W`, `dg ↦ (∂g/∂Xᵢ)ᵢ`, is bijective. -/
private theorem bijective_lift_pderivPi : Function.Bijective (lift (pderivPi σ K)) := by
  classical
  have := Fintype.ofFinite σ
  refine ⟨(injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := ofKaehler_surjective K W z
    rw [lift_ofKaehler] at hz
    refine ofKaehler_eq_zero_iff.mpr fun N _ ↦ ?_
    -- On the finite quotient by `N`, the universal derivation is `∑ᵢ (∂/∂Xᵢ) • dXᵢ`.
    let DN := N.mkQ.compDer (KaehlerDifferential.D K W)
    let v := Fintype.linearCombination W fun i ↦ DN (X σ K i)
    have hD : v.compDer (pderivPi σ K) = DN := derivation_ext fun i ↦ by
      simp [v, pderivPi_X, Fintype.linearCombination_apply_single]
    have hmk : N.mkQ = v ∘ₗ (pderivPi σ K).liftKaehlerDifferential :=
      Derivation.liftKaehlerDifferential_unique _ _ <| Derivation.ext fun a ↦
        (DFunLike.congr_fun hD a).symm.trans
          (congrArg v ((pderivPi σ K).liftKaehlerDifferential_comp_D a)).symm
    rw [← Submodule.Quotient.mk_eq_zero, ← N.mkQ_apply, hmk, LinearMap.comp_apply, hz, map_zero]
  · rw [← LinearMap.range_eq_top, eq_top_iff, ← (Pi.basisFun W σ).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨d K W (X σ K i), by rw [lift_d, pderivPi_X]⟩

/-- **The module of differentials of the Monsky–Washnitzer algebra is free** on the differentials
`dX₁, …, dXₙ` of the variables. -/
noncomputable def washnitzerBasis : Module.Basis σ W (Omega K W) :=
  .ofEquivFun (.ofBijective _ (bijective_lift_pderivPi σ K))

instance : Module.Free W (Omega K W) := .of_basis (washnitzerBasis σ K)

instance : Module.Finite W (Omega K W) := .of_basis (washnitzerBasis σ K)

variable {σ K}

/-- The coordinates of `dg` in the basis `dX₁, …, dXₙ` are the partial derivatives of `g`. -/
@[simp]
theorem washnitzerBasis_repr_d (g : W) (i : σ) :
    (washnitzerBasis σ K).repr (d K W g) i = pderiv σ K i g := by
  simp [washnitzerBasis, pderivPi_apply]

/-- The basis vectors are the differentials of the variables. -/
@[simp]
theorem washnitzerBasis_apply (i : σ) : washnitzerBasis σ K i = d K W (X σ K i) := by
  classical
  refine (washnitzerBasis σ K).repr.injective (Finsupp.ext fun j ↦ ?_)
  rw [Module.Basis.repr_self, washnitzerBasis_repr_d]
  obtain rfl | h := eq_or_ne j i
  · simp
  · simp [h, washnitzerAlgebra.pderiv_X_of_ne h.symm]

/-- **The differential of an overconvergent series**: `dg = ∑ᵢ (∂g/∂Xᵢ) dXᵢ`. -/
theorem d_eq_sum [Fintype σ] (g : W) :
    d K W g = ∑ i, pderiv σ K i g • d K W (X σ K i) := by
  conv_lhs => rw [← (washnitzerBasis σ K).sum_repr (d K W g)]
  simp

end Omega

end TauCeti.Dagger
