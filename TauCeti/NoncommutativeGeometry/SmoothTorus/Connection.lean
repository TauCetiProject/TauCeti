/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NoncommutativeGeometry.Connection.Grassmann
public import TauCeti.NoncommutativeGeometry.SmoothTorus.Derivation

/-!
# Connections on projective modules over the smooth noncommutative torus

A connection on a finitely generated projective right module `E` over the smooth noncommutative
torus `𝒜_θ` is a pair `(∇₁, ∇₂)` of connections along its two basic derivations `δ₁` and `δ₂`.
Its curvature `F = ∇₁ ∇₂ - ∇₂ ∇₁` is an endomorphism of `E`. For the module `E = e 𝒜_θⁱ` of an
idempotent matrix `e`, the normalized trace `(2πi)⁻¹ τ (Tr F)` of the curvature is the value
`(φ#Tr)(e, e, e)` of the fundamental cyclic cocycle

`φ (a₀, a₁, a₂) = (2πi)⁻¹ τ (a₀ (δ₁(a₁) δ₂(a₂) - δ₂(a₁) δ₁(a₂)))`

extended to matrices, whatever the connection. This is the noncommutative Chern–Weil formula: the
first Chern number of `E` computed from any connection is the pairing of `[e]` with `φ`.

## Main results

* `TauCeti.SmoothNoncommutativeTorus.inv_two_pi_I_mul_trace_endToMatrix_curvature`: the
  normalized curvature-trace formula `(2πi)⁻¹ τ (Tr F) = (φ#Tr)(e, e, e)`.

## References

* A. Connes, *C\*-algèbres et géométrie différentielle*, C. R. Acad. Sci. Paris Sér. A-B 290
  (1980), A599–A604.
* A. Connes, *Noncommutative Geometry*, Academic Press, 1994, Chapter III, §2.β and §3.
-/

public section

open Complex Real LinearMap

namespace TauCeti.SmoothNoncommutativeTorus

variable {θ : ℝ} {ι : Type*} [Fintype ι] {e : Matrix ι ι (SmoothNoncommutativeTorus θ)}

/-- **The curvature-trace formula on the smooth noncommutative torus.** For every connection
`(∇₁, ∇₂)` along the basic derivations on the projective module `e 𝒜_θⁱ` of an idempotent matrix
`e`, the curvature `F` satisfies `(2πi)⁻¹ τ (Tr F) = (φ#Tr)(e, e, e)`, where `φ` is the fundamental
cyclic cocycle of `𝒜_θ`. -/
theorem inv_two_pi_I_mul_trace_endToMatrix_curvature (he : IsIdempotentElem e)
    (D₁ : RightConnection (E := range
      (Matrix.mulVecBilin (SmoothNoncommutativeTorus θ) (SmoothNoncommutativeTorus θ)ᵐᵒᵖ e))
      (derivation₁ θ))
    (D₂ : RightConnection (E := range
      (Matrix.mulVecBilin (SmoothNoncommutativeTorus θ) (SmoothNoncommutativeTorus θ)ᵐᵒᵖ e))
      (derivation₂ θ)) :
    (2 * π * I)⁻¹ * trace θ
        (he.endToMatrix (RightConnection.curvature D₁ D₂ commute_derivation₁_derivation₂)).trace =
      matrixCochainExtension ι 2
        ((fundamentalCocycle θ : cyclicCochains ℂ (SmoothNoncommutativeTorus θ) ℂ 2) :
          MultilinearMap (RingHom.id ℂ) (fun _ : Fin 3 ↦ SmoothNoncommutativeTorus θ) ℂ)
        ![e, e, e] := by
  have hφ : ((fundamentalCocycle θ : cyclicCochains ℂ (SmoothNoncommutativeTorus θ) ℂ 2) :
      MultilinearMap (RingHom.id ℂ) (fun _ : Fin 3 ↦ SmoothNoncommutativeTorus θ) ℂ) =
        (2 * π * I)⁻¹ • traceDerivationPairCochain (trace θ) (derivation₁ θ) (derivation₂ θ) := by
    ext a
    simp
  rw [he.map_trace_endToMatrix_curvature trace_mul_comm trace_derivation₁ trace_derivation₂, hφ,
    map_smul, smul_apply, smul_eq_mul]

end TauCeti.SmoothNoncommutativeTorus
