/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.LocallyFreeQuotient.Spec
public import TauCeti.Examples.AlgebraicGeometry.Modules.LocallyFreeQuotient.Cusp.Basic
public import TauCeti.RingTheory.Derivation.TrivSqZeroExt
import TauCeti.Algebra.CharP.Two

/-!
# The cusp in characteristic `2` has a locally free quotient of its differentials

Let `k` be a field of characteristic `2` and `A = k[x, y]/(y² − x³)` the coordinate ring of the
cusp. The partial derivative `∂/∂y` descends to a `k`-derivation of `A`: it kills `x` and sends
`y² − x³` to `2y = 0`. It is constructed as the `ε`-component of the `k`-algebra map
`A → A[ε]`, `x ↦ x`, `y ↦ y + ε`, which exists because `(y + ε)² = y² + 2yε = x³` and lies over
the identity of `A`. The induced map `Ω[A⁄k] → A` sends `dx ↦ 0` and `dy ↦ 1`, so it is
surjective, and `Spec A` satisfies `HasLocallyFreeQuotientOfDifferentials k _ 1`.

This rank-`1` quotient exists even though `Ω[A⁄k]` has the torsion relation `x² dx = 0`
(`cuspX_sq_smul_D_cuspX_eq_zero`, in `LocallyFreeQuotient.Cusp.Basic`), so a locally free quotient
of the differentials need not come from the differentials themselves being locally free.
-/

public section

open AlgebraicGeometry Polynomial KaehlerDifferential TauCeti.AlgebraicGeometry

namespace TauCeti.CuspDifferentialsExample

universe u

noncomputable section

variable {k : Type u} [Field k]

/-- The `k`-algebra map `A → A[ε]` from the cusp ring to its dual numbers, `x ↦ x`,
`y ↦ y + ε`, which exists in characteristic `2`: `(y + ε)² = y² + 2yε = x³`. -/
def cuspDualMap (h2 : (2 : k) = 0) : CuspRing k →ₐ[k] TrivSqZeroExt (CuspRing k) (CuspRing k) :=
  AdjoinRoot.liftAlgHom _
    ((TrivSqZeroExt.inlAlgHom k (CuspRing k) (CuspRing k)).comp (AdjoinRoot.ofAlgHom k _))
    (TrivSqZeroExt.inl (cuspY k) + TrivSqZeroExt.inr 1) (by
      simp only [cuspPolynomial, eval₂_sub, eval₂_X_pow, eval₂_C]
      ext
      · simp [← cuspX_def, sq]
        linear_combination cuspY_sq k
      · simp [← cuspX_def, sq, MulOpposite.smul_eq_mul_unop]
        linear_combination cuspY k * (two_eq_zero_of_algebra h2 : (2 : CuspRing k) = 0))

/-- The ring map `A → A[ε]` sends `a ∈ k[x]` to `a`. -/
@[simp]
theorem cuspDualMap_of (h2 : (2 : k) = 0) (a : Polynomial k) :
    cuspDualMap h2 (AdjoinRoot.of _ a) = TrivSqZeroExt.inl (AdjoinRoot.of _ a) :=
  AdjoinRoot.liftAlgHom_of _ _ _ _ _

/-- The ring map `A → A[ε]` sends `x` to `x`. -/
@[simp]
theorem cuspDualMap_cuspX (h2 : (2 : k) = 0) :
    cuspDualMap h2 (cuspX k) = TrivSqZeroExt.inl (cuspX k) := by
  rw [cuspX_def, cuspDualMap_of]

/-- The ring map `A → A[ε]` sends `y` to `y + ε`. -/
@[simp]
theorem cuspDualMap_cuspY (h2 : (2 : k) = 0) :
    cuspDualMap h2 (cuspY k) = TrivSqZeroExt.inl (cuspY k) + TrivSqZeroExt.inr 1 := by
  simp [cuspDualMap, cuspY_def]

/-- In characteristic `2`, the partial derivative `∂/∂y` of the cusp ring, as a `k`-derivation:
the `ε`-component of the `k`-algebra map `A → A[ε]`, `x ↦ x`, `y ↦ y + ε`, which lies over the
identity of `A`. -/
def cuspDerivationY (h2 : (2 : k) = 0) : Derivation k (CuspRing k) (CuspRing k) :=
  (derivationToTrivSqZeroExtEquivLift k (CuspRing k) (CuspRing k)).symm ⟨cuspDualMap h2, by
    ext
    · simp
    · simp [← cuspY_def]⟩

/-- `∂/∂y` sends `a` to the `ε`-component of its image in `A[ε]`. -/
theorem cuspDerivationY_apply (h2 : (2 : k) = 0) (a : CuspRing k) :
    cuspDerivationY h2 a = (cuspDualMap h2 a).snd :=
  derivationToTrivSqZeroExtEquivLift_symm_apply _ a

/-- `∂y/∂y = 1`. -/
@[simp]
theorem cuspDerivationY_cuspY (h2 : (2 : k) = 0) : cuspDerivationY h2 (cuspY k) = 1 := by
  simp [cuspDerivationY_apply]

/-- `∂x/∂y = 0`. -/
@[simp]
theorem cuspDerivationY_cuspX (h2 : (2 : k) = 0) : cuspDerivationY h2 (cuspX k) = 0 := by
  simp [cuspDerivationY_apply]

/-- In characteristic `2`, the quotient `Ω[A⁄k] → A^1` of the differentials of the cusp ring
induced by `∂/∂y`: `dx ↦ 0`, `dy ↦ 1`. -/
def cuspQuotient (h2 : (2 : k) = 0) :
    Ω[CuspRing k⁄k] →ₗ[CuspRing k] (Fin 1 → CuspRing k) :=
  LinearMap.pi fun _ ↦ (cuspDerivationY h2).liftKaehlerDifferential

/-- The quotient induced by `∂/∂y` sends `dx` to `0`. -/
@[simp]
theorem cuspQuotient_D_cuspX (h2 : (2 : k) = 0) :
    cuspQuotient h2 (D k (CuspRing k) (cuspX k)) = 0 := by
  funext j
  simp [cuspQuotient]

/-- The quotient induced by `∂/∂y` sends `dy` to `1`. -/
@[simp]
theorem cuspQuotient_D_cuspY (h2 : (2 : k) = 0) :
    cuspQuotient h2 (D k (CuspRing k) (cuspY k)) = 1 := by
  funext j
  simp [cuspQuotient]

/-- The quotient induced by `∂/∂y` is surjective. -/
theorem cuspQuotient_surjective (h2 : (2 : k) = 0) : Function.Surjective (cuspQuotient h2) :=
  fun v ↦ ⟨v 0 • D k (CuspRing k) (cuspY k), funext fun j ↦ by
    rw [map_smul, cuspQuotient_D_cuspY, Subsingleton.elim j 0]
    simp⟩

/-- **The cusp over a field of characteristic `2` has a locally free quotient of rank `1` of its
differentials**: `dx ↦ 0`, `dy ↦ 1`. -/
theorem hasLocallyFreeQuotientOfDifferentials_cusp (h2 : (2 : k) = 0) :
    HasLocallyFreeQuotientOfDifferentials k (Spec (.of (CuspRing k))) 1 :=
  hasLocallyFreeQuotientOfDifferentials_Spec_of_surjective k (.of (CuspRing k)) _
    (cuspQuotient_surjective h2)

-- The differentials still have the torsion relation `x² dx = 0`.
example (h2 : (2 : k) = 0) : cuspX k ^ 2 • D k (CuspRing k) (cuspX k) = 0 :=
  cuspX_sq_smul_D_cuspX_eq_zero h2

end

end TauCeti.CuspDifferentialsExample
