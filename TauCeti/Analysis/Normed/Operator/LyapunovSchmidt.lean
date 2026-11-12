/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
public import TauCeti.LinearAlgebra.Projection.RangeKer
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import TauCeti.Analysis.Normed.Operator.Banach

/-!
# The Lyapunov–Schmidt projection of a family of operators

Let `L : X →L[𝕜] Y` and `P : Y →L[𝕜] Z` be continuous linear maps between normed spaces whose
composite `A = P L` is invertible. The **Lyapunov–Schmidt projection**

`Π = id - L A⁻¹ P` (`ContinuousLinearMap.lyapunovSchmidtProj`)

is the projection of `Y` onto the kernel `W` of `P` along the range of `L`
(`ContinuousLinearMap.coe_lyapunovSchmidtProj`). It depends on `P` only through `W`
(`ContinuousLinearMap.lyapunovSchmidtProj_eq_of_ker_eq`), and it reduces the linear equation
`L f + S = 0` to an equation in `W`: the vector `f = -A⁻¹ P S` is the unique one with
`L f + S ∈ W` (`ContinuousLinearMap.apply_add_mem_ker_iff`), for it `L f + S = Π S`, and
`Π S = 0` exactly when `S` lies in the range of `L`
(`ContinuousLinearMap.lyapunovSchmidtProj_apply_eq_zero_iff`). The algebra is
`LinearMap.id_sub_comp_comp_eq_projection`. For Banach `X` and `Z`, `P L` is invertible exactly
when `L` is injective, `P` is surjective, and the kernel of `P` is complementary to the range of `L`
(`ContinuousLinearMap.isInvertible_comp_iff`).

In a perturbative construction the operator depends on a parameter `σ`, while `W` and `P` are
chosen once near a base parameter, so that `A(σ) = P(σ) L(σ)` is invertible there. Then `A(σ)`
stays invertible for nearby `σ` when `X` is complete
(`ContinuousAt.eventually_isInvertible_clm_comp`), the projections `Π_σ` inherit the regularity
of the family (`ContDiffAt.lyapunovSchmidtProj`), and their derivative along a direction `v` is

`∂ᵥ Π = -Π (∂ᵥ L) A⁻¹ P - L A⁻¹ (∂ᵥ P) Π`

(`DifferentiableAt.fderiv_lyapunovSchmidtProj`). For a fixed `P` the second term vanishes. For a
family of equations `L(σ) f + S(σ) = 0` this controls the reduced section `σ ↦ Π_σ S(σ)` with values
in the fixed space `W`, whose zeros are the parameters at which the equation is solvable.

## Main definitions

* `ContinuousLinearMap.lyapunovSchmidtProj`: the operator `id - L (P L)⁻¹ P`.

## Main results

* `ContinuousLinearMap.isInvertible_comp_iff`: `P L` is invertible exactly when `L` is injective,
  `P` is surjective and `range L` is complementary to `ker P`.
* `ContinuousLinearMap.coe_lyapunovSchmidtProj`: for invertible `P L`, it is the projection onto
  `ker P` along `range L`.
* `ContinuousLinearMap.lyapunovSchmidtProj_eq_of_ker_eq`: it depends on `P` only through `ker P`.
* `ContDiffAt.lyapunovSchmidtProj`: the projections of a `C^n` family are `C^n`.
* `DifferentiableAt.fderiv_lyapunovSchmidtProj`: their derivative.

## References

* S.-N. Chow and J. K. Hale, *Methods of Bifurcation Theory*, Springer, 1982, §2.4.
* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace ContinuousLinearMap

variable {𝕜 X Y Z : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- The **Lyapunov–Schmidt projection** `id - L (P L)⁻¹ P` of `L : X →L[𝕜] Y` relative to
`P : Y →L[𝕜] Z`. When `P L` is invertible, it is the projection of `Y` onto `ker P` along
`range L` (`ContinuousLinearMap.coe_lyapunovSchmidtProj`). -/
def lyapunovSchmidtProj (L : X →L[𝕜] Y) (P : Y →L[𝕜] Z) : Y →L[𝕜] Y :=
  ContinuousLinearMap.id 𝕜 Y - L ∘L (P ∘L L).inverse ∘L P

variable {L : X →L[𝕜] Y} {P : Y →L[𝕜] Z}

/-- The Lyapunov–Schmidt projection sends `y` to `y - L (P L)⁻¹ P y`. -/
theorem lyapunovSchmidtProj_apply (y : Y) :
    L.lyapunovSchmidtProj P y = y - L ((P ∘L L).inverse (P y)) := by
  simp [lyapunovSchmidtProj]

/-- For Banach spaces `X` and `Z`, the operator `P L` is invertible exactly when `L` is injective,
`P` is surjective, and the range of `L` is complementary to the kernel of `P`. -/
theorem isInvertible_comp_iff [CompleteSpace X] [CompleteSpace Z] :
    (P ∘L L).IsInvertible ↔
      Function.Injective L ∧ Function.Surjective P ∧ IsCompl L.range P.ker := by
  rw [isInvertible_iff_bijective]
  exact LinearMap.bijective_comp_iff

section Invertible

variable (h : (P ∘L L).IsInvertible)
include h

/-- An invertible `P L` is a linear equivalence `A` with `P ∘ L = A` and `(P L)⁻¹ = A⁻¹`. -/
private theorem comp_eq_and_inverse_eq :
    ∃ A : X ≃ₗ[𝕜] Z, (P : Y →ₗ[𝕜] Z) ∘ₗ (L : X →ₗ[𝕜] Y) = A ∧
      ((P ∘L L).inverse : Z →ₗ[𝕜] X) = A.symm := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A.toLinearEquiv, ?_, ?_⟩
  · rw [← toLinearMap_comp, ← hA]
    ext x
    simp
  · rw [← hA, inverse_equiv]
    ext z
    simp

/-- If `P L` is invertible, the range of `L` and the kernel of `P` are complementary. -/
theorem isCompl_range_ker_of_isInvertible_comp : IsCompl L.range P.ker := by
  obtain ⟨A, hA, -⟩ := comp_eq_and_inverse_eq h
  exact LinearMap.isCompl_range_ker_of_comp_eq A hA

/-- If `P L` is invertible, the Lyapunov–Schmidt projection `id - L (P L)⁻¹ P` is the projection
onto the kernel of `P` along the range of `L`. -/
theorem coe_lyapunovSchmidtProj :
    (L.lyapunovSchmidtProj P : Y →ₗ[𝕜] Y) =
      P.ker.projection L.range (isCompl_range_ker_of_isInvertible_comp h).symm := by
  obtain ⟨A, hA, hinv⟩ := comp_eq_and_inverse_eq h
  rw [← LinearMap.id_sub_comp_comp_eq_projection A hA, ← hinv]
  ext y
  simp [lyapunovSchmidtProj_apply]

/-- If `P L` is invertible, the Lyapunov–Schmidt projection is the projection onto the kernel of
`P` along the range of `L`, pointwise. -/
theorem lyapunovSchmidtProj_apply_eq_projection (y : Y) :
    L.lyapunovSchmidtProj P y =
      P.ker.projection L.range (isCompl_range_ker_of_isInvertible_comp h).symm y :=
  congr($(coe_lyapunovSchmidtProj h) y)

/-- If `P L` is invertible, the Lyapunov–Schmidt projection is idempotent. -/
theorem isIdempotentElem_lyapunovSchmidtProj : IsIdempotentElem (L.lyapunovSchmidtProj P) := by
  have hp := Submodule.isIdempotentElem_projection (isCompl_range_ker_of_isInvertible_comp h).symm
  ext y
  rw [mul_def, comp_apply, lyapunovSchmidtProj_apply_eq_projection h,
    lyapunovSchmidtProj_apply_eq_projection h]
  exact congr($hp y)

/-- If `P L` is invertible, the Lyapunov–Schmidt projection takes values in the kernel of `P`. -/
@[simp]
theorem apply_lyapunovSchmidtProj (y : Y) : P (L.lyapunovSchmidtProj P y) = 0 := by
  rw [lyapunovSchmidtProj_apply_eq_projection h]
  exact LinearMap.mem_ker.1 (Submodule.projection_apply_mem _ y)

/-- If `P L` is invertible, the Lyapunov–Schmidt projection vanishes on the range of `L`. -/
@[simp]
theorem lyapunovSchmidtProj_apply_apply (x : X) : L.lyapunovSchmidtProj P (L x) = 0 := by
  rw [lyapunovSchmidtProj_apply_eq_projection h]
  exact Submodule.projection_apply_of_mem_right _ (LinearMap.mem_range_self _ x)

/-- If `P L` is invertible, the Lyapunov–Schmidt projection of `y` vanishes exactly when `y` lies
in the range of `L`. -/
theorem lyapunovSchmidtProj_apply_eq_zero_iff {y : Y} :
    L.lyapunovSchmidtProj P y = 0 ↔ y ∈ L.range := by
  rw [lyapunovSchmidtProj_apply_eq_projection h, Submodule.projection_apply_eq_zero_iff]

/-- If `P L` is invertible, then `x = -(P L)⁻¹ P y` is the unique vector with `L x + y ∈ ker P`.
For it, `L x + y` is the Lyapunov–Schmidt projection of `y`. -/
theorem apply_add_mem_ker_iff {x : X} {y : Y} :
    L x + y ∈ P.ker ↔ x = -(P ∘L L).inverse (P y) := by
  obtain ⟨A, hA, hinv⟩ := comp_eq_and_inverse_eq h
  rw [show (P ∘L L).inverse (P y) = A.symm (P y) from congr($hinv (P y))]
  exact LinearMap.add_mem_ker_iff_eq_neg_symm A hA

/-- The Lyapunov–Schmidt projection depends on `P` only through its kernel: if `P L` and `P' L`
are invertible and `ker P = ker P'`, the two projections agree. -/
theorem lyapunovSchmidtProj_eq_of_ker_eq {Z' : Type*} [NormedAddCommGroup Z'] [NormedSpace 𝕜 Z']
    {P' : Y →L[𝕜] Z'} (h' : (P' ∘L L).IsInvertible)
    (hker : P.ker = P'.ker) :
    L.lyapunovSchmidtProj P = L.lyapunovSchmidtProj P' := by
  obtain ⟨A, hA, hinv⟩ := comp_eq_and_inverse_eq h
  obtain ⟨A', hA', hinv'⟩ := comp_eq_and_inverse_eq h'
  have := LinearMap.comp_comp_eq_of_ker_eq A A' hA hA' hker
  rw [← hinv, ← hinv'] at this
  exact ContinuousLinearMap.ext fun y => by
    simpa [lyapunovSchmidtProj_apply] using congr(y - $this y)

end Invertible

end ContinuousLinearMap

section Family

open ContinuousLinearMap

variable {𝕜 E X Y Z : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace X]
  {L : E → X →L[𝕜] Y} {P : E → Y →L[𝕜] Z} {σ : E} {n : WithTop ℕ∞}

omit [NormedSpace 𝕜 E] in
/-- If `P(σ) L(σ)` is invertible and both families are continuous at `σ`, then `P(σ') L(σ')` is
invertible for all `σ'` near `σ`. -/
theorem ContinuousAt.eventually_isInvertible_clm_comp (hL : ContinuousAt L σ)
    (hP : ContinuousAt P σ) (h : (P σ ∘L L σ).IsInvertible) :
    ∀ᶠ σ' in 𝓝 σ, (P σ' ∘L L σ').IsInvertible :=
  (hP.clm_comp hL).eventually h.eventually_nhds

/-- The Lyapunov–Schmidt projections of `C^n` families `L` and `P` form a `C^n` family at every
parameter where `P L` is invertible. -/
theorem ContDiffAt.lyapunovSchmidtProj (hL : ContDiffAt 𝕜 n L σ) (hP : ContDiffAt 𝕜 n P σ)
    (h : (P σ ∘L L σ).IsInvertible) :
    ContDiffAt 𝕜 n (fun σ => (L σ).lyapunovSchmidtProj (P σ)) σ :=
  contDiffAt_const.sub (hL.clm_comp (((hP.clm_comp hL).clm_inverse h).clm_comp hP))

/-- The Lyapunov–Schmidt projections of differentiable families `L` and `P` form a
differentiable family at every parameter where `P L` is invertible. -/
theorem DifferentiableAt.lyapunovSchmidtProj (hL : DifferentiableAt 𝕜 L σ)
    (hP : DifferentiableAt 𝕜 P σ) (h : (P σ ∘L L σ).IsInvertible) :
    DifferentiableAt 𝕜 (fun σ => (L σ).lyapunovSchmidtProj (P σ)) σ :=
  (differentiableAt_const _).sub
    (hL.clm_comp (((hP.clm_comp hL).clm_inverse_of_completeSpace h).clm_comp hP))

/-- The derivative of the Lyapunov–Schmidt projections `Π = id - L A⁻¹ P`, `A = P L`, of
differentiable families along a direction `v`, at a parameter where `A` is invertible:
`∂ᵥ Π = -Π (∂ᵥ L) A⁻¹ P - L A⁻¹ (∂ᵥ P) Π`. -/
theorem DifferentiableAt.fderiv_lyapunovSchmidtProj (hL : DifferentiableAt 𝕜 L σ)
    (hP : DifferentiableAt 𝕜 P σ) (h : (P σ ∘L L σ).IsInvertible) (v : E) :
    fderiv 𝕜 (fun σ => (L σ).lyapunovSchmidtProj (P σ)) σ v =
      -((L σ).lyapunovSchmidtProj (P σ) ∘L fderiv 𝕜 L σ v ∘L (P σ ∘L L σ).inverse ∘L P σ) -
        L σ ∘L (P σ ∘L L σ).inverse ∘L fderiv 𝕜 P σ v ∘L (L σ).lyapunovSchmidtProj (P σ) := by
  have hA : DifferentiableAt 𝕜 (fun σ => P σ ∘L L σ) σ := hP.clm_comp hL
  have hinv := hA.clm_inverse_of_completeSpace h
  have hderiv : fderiv 𝕜 (fun σ => (L σ).lyapunovSchmidtProj (P σ)) σ v =
      -(fderiv 𝕜 L σ v ∘L (P σ ∘L L σ).inverse ∘L P σ +
        L σ ∘L (fderiv 𝕜 (fun σ => (P σ ∘L L σ).inverse) σ v ∘L P σ +
          (P σ ∘L L σ).inverse ∘L fderiv 𝕜 P σ v)) := by
    simp only [ContinuousLinearMap.lyapunovSchmidtProj]
    rw [fderiv_const_sub, fderiv_clm_comp hL (hinv.clm_comp hP), fderiv_clm_comp hinv hP]
    simp [add_comm]
  rw [hderiv, hA.fderiv_clm_inverse h, fderiv_clm_comp hP hL]
  ext y
  simp only [lyapunovSchmidtProj_apply, neg_apply, add_apply, sub_apply, coe_comp,
    Function.comp_apply, map_sub, map_add, map_neg, compL_apply, flip_apply]
  abel

end Family
