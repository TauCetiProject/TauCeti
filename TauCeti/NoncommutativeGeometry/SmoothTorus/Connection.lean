/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NoncommutativeGeometry.SmoothTorus.Derivation
public import TauCeti.RingTheory.Connection.Right.CurvatureTrace

/-!
# Curvature of connections on projective modules over the smooth noncommutative torus

A connection on a finite projective right module over `𝒜_θ` is a pair of covariant derivatives
`∇₁, ∇₂` along the basic derivations `δ₁, δ₂`, and its curvature is the module endomorphism
`[∇₁, ∇₂]`. For the module cut out of the free module `𝒜_θⁿ` by an idempotent matrix `e`, the
normalized curvature trace `(2πi)⁻¹ τ(Tr [∇₁, ∇₂])` does not depend on the connection, and it is
the value `(φ#Tr)(e, e, e)` of the matrix extension of the fundamental cyclic two-cocycle
`φ (a₀, a₁, a₂) = (2πi)⁻¹ τ (a₀ (δ₁a₁ δ₂a₂ - δ₂a₁ δ₁a₂))`. This is Connes' description of the
pairing of `φ` with the class of `e` as the first Chern number of the module, computed from the
curvature of any connection, for instance the Grassmann connection `e ∘ δⱼ`.

## Main results

* `TauCeti.SmoothNoncommutativeTorus.matrixCochainExtension_fundamentalCocycle_eq_rangeEndTrace`:
  `(φ#Tr)(e, e, e) = (2πi)⁻¹ τ(Tr [∇₁, ∇₂])` for every idempotent matrix `e` over `𝒜_θ` and all
  connections along `δ₁` and `δ₂` on the range of `e`.

## References

* A. Connes, *C\*-algèbres et géométrie différentielle*, C. R. Acad. Sci. Paris Sér. A-B 290
  (1980), A599–A604.
* A. Connes, *Noncommutative Geometry*, Academic Press, 1994, Chapter III, §3, and Chapter IV,
  §6.
-/

public section

namespace TauCeti.SmoothNoncommutativeTorus

open RightConnection Complex Real

variable {θ : ℝ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The curvature-trace formula on the smooth noncommutative torus.** For an idempotent matrix
`e` over `𝒜_θ` and connections `∇₁, ∇₂` along the basic derivations `δ₁, δ₂` on the range of
`e` acting on `𝒜_θ^ι`, the matrix extension of the fundamental cocycle at `(e, e, e)` is the
normalized curvature trace `(2πi)⁻¹ τ(Tr [∇₁, ∇₂])`. -/
theorem matrixCochainExtension_fundamentalCocycle_eq_rangeEndTrace
    {e : Matrix ι ι (SmoothNoncommutativeTorus θ)} (he : IsIdempotentElem e)
    (c₁ : RightConnection (E := LinearMap.range
      (Matrix.mulVecBilin (SmoothNoncommutativeTorus θ) (SmoothNoncommutativeTorus θ)ᵐᵒᵖ e))
      (derivation₁ θ))
    (c₂ : RightConnection (E := LinearMap.range
      (Matrix.mulVecBilin (SmoothNoncommutativeTorus θ) (SmoothNoncommutativeTorus θ)ᵐᵒᵖ e))
      (derivation₂ θ)) :
    matrixCochainExtension ι 2
        ((fundamentalCocycle θ : cyclicCochains ℂ (SmoothNoncommutativeTorus θ) ℂ 2) :
          MultilinearMap (RingHom.id ℂ) (fun _ : Fin 3 ↦ SmoothNoncommutativeTorus θ) ℂ)
        ![e, e, e] =
      (2 * π * I)⁻¹ * rangeEndTrace (trace θ)
        (Matrix.mulVecBilin (SmoothNoncommutativeTorus θ) (SmoothNoncommutativeTorus θ)ᵐᵒᵖ e)
        (curvature c₁ c₂ commute_derivation₁_derivation₂) := by
  rw [coe_fundamentalCocycle, map_smul, smul_apply, smul_eq_mul,
    rangeEndTrace_curvature_eq_matrixCochainExtension trace_mul_comm trace_derivation₁
      trace_derivation₂ commute_derivation₁_derivation₂ he c₁ c₂]

end TauCeti.SmoothNoncommutativeTorus
