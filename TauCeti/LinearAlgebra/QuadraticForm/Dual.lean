/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import TauCeti.LinearAlgebra.Dual.Lemmas
public import TauCeti.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# The hyperbolic form on a module and its dual

The polar form of `QuadraticForm.dualProd K M` pairs the two coordinate summands by evaluation.
It is nondegenerate whenever the linear functionals on `M` separate points, with no assumption
on the characteristic of `K` or the dimension of `M`.

More generally, a pairing `ψ : A →ₗ[K] Module.Dual K C` defines the quadratic form
`(a, c) ↦ ψ a c` on `A × C`, the pullback of the hyperbolic form along `ψ × id`. Over a linearly
ordered field, with `A` and `C` finite dimensional, both of its indices of inertia are the rank of
`ψ` (`TauCeti.sigPos_dualProd_comp_prodMap`, `TauCeti.sigNeg_dualProd_comp_prodMap`). The form
vanishes on `ker ψ × C`, which bounds the positive index above by the rank of `ψ`, and its radical
lies in `ker ψ × ker ψ.flip`, which bounds the sum of the two indices below by the sum of the ranks
of `ψ` and of the transposed pairing `ψ.flip : C →ₗ[K] Module.Dual K A`. These two ranks agree
(`LinearMap.finrank_range_flip`), and the automorphism `(a, c) ↦ (a, -c)` negates the form, so the
two indices agree. For `ψ = id` this is the hyperbolic form on `Module.Dual K C × C`, whose indices
are both `dim C` (`TauCeti.sigPos_dualProd`, `TauCeti.sigNeg_dualProd`).

The intersection form of `S¹ × Y`, for a closed three-manifold `Y`, has this shape: in the
decomposition `H²(S¹ × Y) ≅ H²(Y) × H¹(Y)` its quadratic form is `(b, c) ↦ 2 ψ_z(b, c)`, where
`ψ_z(b, c) = ⟨pr₁^* θ ⌣ pr₂^* (b ⌣ c), z⟩` (`TopCat.sphereProdCupPairing`) for a homology class `z`
of `S¹ × Y` and `θ ∈ H¹(S¹)` dual to the standard generator
(`TopCat.sigPos_singularCupPairing_sphere`).
-/

public section

namespace TauCeti

open Module QuadraticMap QuadraticForm

variable {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

/-! ## The polar form of the hyperbolic form -/

/-- **The polar form of the hyperbolic quadratic form** `Q (f, m) = f m` pairs each coordinate
summand with the other and neither with itself. -/
@[simp]
theorem polar_dualProd (p q : Module.Dual K M × M) :
    polar (QuadraticForm.dualProd K M) p q = p.1 q.2 + q.1 p.2 := by
  simp only [polar, QuadraticForm.dualProd_apply, Prod.fst_add, Prod.snd_add,
    LinearMap.add_apply, map_add]
  ring

/-- The hyperbolic form is nondegenerate whenever the functionals on `M` separate points. -/
theorem nondegenerate_dualProd (hM : Function.Injective (Module.Dual.eval K M)) :
    (QuadraticForm.dualProd K M).Nondegenerate := by
  have hpolar : (QuadraticForm.dualProd K M).polarBilin = LinearMap.dualProd K M := by
    apply LinearMap.ext₂
    intro p q
    simp only [polarBilin_apply_apply, polar_dualProd, LinearMap.dualProd_apply_apply, add_comm]
  apply QuadraticMap.nondegenerate_of_ker_polarBilin_eq_bot
  rw [hpolar]
  exact LinearMap.separatingLeft_iff_ker_eq_bot.mp
    ((LinearMap.separatingLeft_dualProd K M).mpr hM)

/-! ## The indices of inertia of a pairing -/

section Signature

variable {K A C : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup A]
  [Module K A] [AddCommGroup C] [Module K C]

omit [IsStrictOrderedRing K] in
/-- The automorphism `(a, c) ↦ (a, -c)` negates the quadratic form of a pairing, so its two indices
of inertia agree. -/
theorem sigNeg_dualProd_comp_prodMap_eq_sigPos (ψ : A →ₗ[K] Module.Dual K C) :
    sigNeg ((QuadraticForm.dualProd K C).comp (ψ.prodMap LinearMap.id)) =
      sigPos ((QuadraticForm.dualProd K C).comp (ψ.prodMap LinearMap.id)) :=
  QuadraticForm.sigNeg_eq_sigPos_of_comp_eq_neg _
    ((LinearEquiv.refl K A).prodCongr (LinearEquiv.neg K)) fun x ↦ by simp

variable [FiniteDimensional K A] [FiniteDimensional K C]

/-- **The positive index of inertia of a pairing is its rank**: the quadratic form
`(a, c) ↦ ψ a c` of a pairing `ψ : A →ₗ[K] Module.Dual K C` of finite-dimensional spaces has
positive index of inertia the rank of `ψ`. -/
theorem sigPos_dualProd_comp_prodMap (ψ : A →ₗ[K] Module.Dual K C) :
    sigPos ((QuadraticForm.dualProd K C).comp (ψ.prodMap LinearMap.id)) =
      finrank K (LinearMap.range ψ) := by
  set Q := (QuadraticForm.dualProd K C).comp (ψ.prodMap LinearMap.id)
  have hA := LinearMap.finrank_range_add_finrank_ker ψ
  have hC := LinearMap.finrank_range_add_finrank_ker ψ.flip
  have hψ : finrank K (LinearMap.range ψ.flip) = finrank K (LinearMap.range ψ) :=
    LinearMap.finrank_range_flip ψ
  have hAC : finrank K (A × C) = finrank K A + finrank K C := Module.finrank_prod
  -- `Q` vanishes on `ker ψ × C`
  have h₁ := QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := Q)
    (V := (LinearMap.ker ψ).prod ⊤) fun x hx ↦ by
      simp [Q, LinearMap.mem_ker.mp (Submodule.mem_prod.mp hx).1]
  -- the radical of `Q` lies in `ker ψ × ker ψ.flip`
  have hrad : Q.radical ≤ (LinearMap.ker ψ).prod (LinearMap.ker ψ.flip) := by
    intro x hx
    have hpolar : ∀ y, QuadraticMap.polar Q x y = 0 := fun y ↦ by
      simpa using LinearMap.congr_fun
        (LinearMap.mem_ker.mp (QuadraticMap.radical_le_ker_polarBilin hx)) y
    refine Submodule.mem_prod.mpr ⟨LinearMap.mem_ker.mpr ?_, LinearMap.mem_ker.mpr ?_⟩
    · ext c
      simpa [Q, QuadraticMap.polar] using hpolar (0, c)
    · ext a
      simpa [Q, QuadraticMap.polar] using hpolar (a, 0)
  have h₃ := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  have h₄ := Submodule.finrank_mono hrad
  rw [show sigNeg Q = sigPos Q from sigNeg_dualProd_comp_prodMap_eq_sigPos ψ] at h₃
  rw [(Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod, finrank_top] at h₁
  rw [(Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod] at h₄
  omega

/-- **The negative index of inertia of a pairing is its rank**: the quadratic form
`(a, c) ↦ ψ a c` of a pairing `ψ : A →ₗ[K] Module.Dual K C` of finite-dimensional spaces has
negative index of inertia the rank of `ψ`. -/
theorem sigNeg_dualProd_comp_prodMap (ψ : A →ₗ[K] Module.Dual K C) :
    sigNeg ((QuadraticForm.dualProd K C).comp (ψ.prodMap LinearMap.id)) =
      finrank K (LinearMap.range ψ) := by
  rw [sigNeg_dualProd_comp_prodMap_eq_sigPos, sigPos_dualProd_comp_prodMap]

omit [FiniteDimensional K A] in
/-- The hyperbolic form `(f, c) ↦ f c` on `Module.Dual K C × C` has positive index of inertia
`dim C`. -/
theorem sigPos_dualProd : sigPos (QuadraticForm.dualProd K C) = finrank K C := by
  have h := sigPos_dualProd_comp_prodMap (LinearMap.id : Module.Dual K C →ₗ[K] Module.Dual K C)
  rw [LinearMap.prodMap_id, LinearMap.range_id, finrank_top, Subspace.dual_finrank_eq] at h
  exact h

omit [FiniteDimensional K A] in
/-- The hyperbolic form `(f, c) ↦ f c` on `Module.Dual K C × C` has negative index of inertia
`dim C`. -/
theorem sigNeg_dualProd : sigNeg (QuadraticForm.dualProd K C) = finrank K C := by
  have h := sigNeg_dualProd_comp_prodMap (LinearMap.id : Module.Dual K C →ₗ[K] Module.Dual K C)
  rw [LinearMap.prodMap_id, LinearMap.range_id, finrank_top, Subspace.dual_finrank_eq] at h
  exact h

end Signature

end TauCeti
