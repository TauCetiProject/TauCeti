/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import TauCeti.AlgebraicGeometry.Modules.Differentials.LocallyFreeQuotient.Spec
public import TauCeti.Examples.AlgebraicGeometry.Modules.LocallyFreeQuotientCusp

/-!
# The cusp in characteristic `2` has a locally free quotient of its differentials

Let `k` be a field of characteristic `2` and `A = k[x, y]/(y² − x³)` the coordinate ring of the
cusp. The partial derivative `∂/∂y` descends to a `k`-derivation of `A`: it kills `x` and sends
`y² − x³` to `2y = 0`. It is constructed as the `ε`-component of the ring map `A → A[ε]`,
`x ↦ x`, `y ↦ y + ε`, which exists because `(y + ε)² = y² + 2yε = x³`. The induced map
`Ω[A⁄k] → A` sends `dx ↦ 0` and `dy ↦ 1`, so it is surjective, and `Spec A` satisfies
`HasLocallyFreeQuotientOfDifferentials k _ 1` although `Ω[A⁄k]` has the torsion section `dx`.

This is the Check of NashBlowups §0.7 for the cusp over `𝔽_2`: the model "`Ω_{X/k}` is itself
locally free of rank `d`" is excluded.
-/

public section

open AlgebraicGeometry Polynomial KaehlerDifferential TauCeti.AlgebraicGeometry

namespace TauCeti.CuspDifferentialsExample

universe u

noncomputable section

variable {k : Type u} [Field k]

/-- The ring map `A → A[ε]` from the cusp ring to its dual numbers, `x ↦ x`, `y ↦ y + ε`, which
exists in characteristic `2`: `(y + ε)² = y² + 2yε = x³`. -/
def cuspDualMap (h2 : (2 : k) = 0) : CuspRing k →+* TrivSqZeroExt (CuspRing k) (CuspRing k) :=
  AdjoinRoot.lift ((TrivSqZeroExt.inlHom (CuspRing k) (CuspRing k)).comp (AdjoinRoot.of _))
    (TrivSqZeroExt.inl (cuspY k) + TrivSqZeroExt.inr 1) (by
      have h2' : (2 : CuspRing k) = 0 := by
        rw [← map_ofNat (algebraMap k (CuspRing k)) 2, h2, map_zero]
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, RingHom.comp_apply, map_pow, ← cuspX_def,
        TrivSqZeroExt.inlHom_apply, sq]
      ext
      · simp only [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add,
          TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_zero, add_zero]
        linear_combination cuspY_sq k
      · simp only [TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add,
          TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
          TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_zero, smul_eq_mul,
          MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, add_zero]
        linear_combination cuspY k * h2')

/-- The ring map `A → A[ε]` sends `a ∈ k[x]` to `a`. -/
theorem cuspDualMap_of (h2 : (2 : k) = 0) (a : Polynomial k) :
    cuspDualMap h2 (AdjoinRoot.of _ a) = TrivSqZeroExt.inl (AdjoinRoot.of _ a) :=
  AdjoinRoot.lift_of _

/-- The ring map `A → A[ε]` sends `y` to `y + ε`. -/
theorem cuspDualMap_cuspY (h2 : (2 : k) = 0) :
    cuspDualMap h2 (cuspY k) = TrivSqZeroExt.inl (cuspY k) + TrivSqZeroExt.inr 1 := by
  simp only [cuspDualMap, cuspY_def]
  exact AdjoinRoot.lift_root _

/-- The ring map `A → A[ε]` lifts the identity: its first component is the identity. -/
theorem fst_cuspDualMap (h2 : (2 : k) = 0) (a : CuspRing k) : (cuspDualMap h2 a).fst = a := by
  have : (TrivSqZeroExt.fstHom (CuspRing k) (CuspRing k) (CuspRing k)).toRingHom.comp
      (cuspDualMap h2) = RingHom.id _ := by
    refine AdjoinRoot.ringHom_ext (RingHom.ext fun a ↦ ?_) ?_
    · simp [cuspDualMap_of]
    · rw [← cuspY_def]
      simp [cuspDualMap_cuspY]
  exact congrArg (· a) this

/-- In characteristic `2`, the partial derivative `∂/∂y` of the cusp ring, as a `k`-derivation:
the `ε`-component of the ring map `A → A[ε]`, `x ↦ x`, `y ↦ y + ε`. -/
def cuspDerivationY (h2 : (2 : k) = 0) : Derivation k (CuspRing k) (CuspRing k) :=
  Derivation.mk'
    { toFun a := (cuspDualMap h2 a).snd
      map_add' a b := by simp
      map_smul' c a := by
        have hc : algebraMap k (CuspRing k) c = AdjoinRoot.of _ (Polynomial.C c) := by
          rw [IsScalarTower.algebraMap_apply k (Polynomial k) (CuspRing k),
            AdjoinRoot.algebraMap_eq, Polynomial.algebraMap_eq]
        rw [Algebra.smul_def, map_mul, hc, cuspDualMap_of, RingHom.id_apply, Algebra.smul_def, hc,
          TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, smul_zero,
          add_zero, smul_eq_mul] }
    (fun a b ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, TrivSqZeroExt.snd_mul,
        fst_cuspDualMap, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring)

/-- `∂/∂y` sends `a` to the `ε`-component of its image in `A[ε]`. -/
theorem cuspDerivationY_apply (h2 : (2 : k) = 0) (a : CuspRing k) :
    cuspDerivationY h2 a = (cuspDualMap h2 a).snd :=
  (rfl)

/-- `∂y/∂y = 1`. -/
theorem cuspDerivationY_cuspY (h2 : (2 : k) = 0) : cuspDerivationY h2 (cuspY k) = 1 := by
  simp [cuspDerivationY_apply, cuspDualMap_cuspY]

/-- `∂x/∂y = 0`. -/
theorem cuspDerivationY_cuspX (h2 : (2 : k) = 0) : cuspDerivationY h2 (cuspX k) = 0 := by
  simp [cuspDerivationY_apply, cuspX_def, cuspDualMap_of]

/-- In characteristic `2`, the quotient `Ω[A⁄k] → A^1` of the differentials of the cusp ring
induced by `∂/∂y`: `dx ↦ 0`, `dy ↦ 1`. -/
def cuspQuotient (h2 : (2 : k) = 0) :
    Ω[CuspRing k⁄k] →ₗ[CuspRing k] (Fin 1 → CuspRing k) :=
  LinearMap.pi fun _ ↦ (cuspDerivationY h2).liftKaehlerDifferential

/-- The quotient induced by `∂/∂y` sends `dx` to `0`. -/
theorem cuspQuotient_D_cuspX (h2 : (2 : k) = 0) :
    cuspQuotient h2 (D k (CuspRing k) (cuspX k)) = 0 := by
  funext j
  simp [cuspQuotient, cuspDerivationY_cuspX]

/-- The quotient induced by `∂/∂y` sends `dy` to `1`. -/
theorem cuspQuotient_D_cuspY (h2 : (2 : k) = 0) :
    cuspQuotient h2 (D k (CuspRing k) (cuspY k)) = 1 := by
  funext j
  simp [cuspQuotient, cuspDerivationY_cuspY]

/-- The quotient induced by `∂/∂y` is surjective. -/
theorem cuspQuotient_surjective (h2 : (2 : k) = 0) : Function.Surjective (cuspQuotient h2) :=
  fun v ↦ ⟨v 0 • D k (CuspRing k) (cuspY k), funext fun j ↦ by
    rw [map_smul, cuspQuotient_D_cuspY, Subsingleton.elim j 0]
    simp⟩

/-- **The cusp over a field of characteristic `2` has a locally free quotient of rank `1` of its
differentials**: `dx ↦ 0`, `dy ↦ 1` (NashBlowups §0.7, Check). -/
theorem hasLocallyFreeQuotientOfDifferentials_cusp (h2 : (2 : k) = 0) :
    HasLocallyFreeQuotientOfDifferentials k (Spec (.of (CuspRing k))) 1 :=
  hasLocallyFreeQuotientOfDifferentials_Spec_of_surjective k (.of (CuspRing k)) _
    (cuspQuotient_surjective h2)

-- **Check.** The quotient exists although the differentials of the cusp in characteristic `2`
-- have the torsion relation `x² dx = 0`.
example (h2 : (2 : k) = 0) : cuspX k ^ 2 • D k (CuspRing k) (cuspX k) = 0 :=
  cuspX_sq_smul_D_cuspX_eq_zero h2

end

end TauCeti.CuspDifferentialsExample
