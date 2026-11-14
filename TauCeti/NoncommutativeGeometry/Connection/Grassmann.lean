/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Idempotent
public import TauCeti.LinearAlgebra.Matrix.Trace.Basic
public import TauCeti.RingTheory.Connection.Right.Grassmann
public import TauCeti.RingTheory.CyclicCohomology.Derivation

/-!
# The Grassmann connection and the curvature-trace formula

Let `e : Matrix ι ι A` be an idempotent matrix over an algebra `A`, and `E = e Aⁱ` the finitely
generated projective right `A`-module of column vectors fixed by `e`. For a derivation `δ` of `A`,
the **Grassmann connection** along `δ` is

`∇ ξ = e δ(ξ)`,

where `δ` acts on the coordinates of `ξ`: the projection by `e` of the coordinate connection
`TauCeti.RightConnection.coordinate δ ι`. For commuting derivations `δ₁` and `δ₂`, the curvature of
the pair of Grassmann connections is left multiplication by the matrix
`e (δ₁(e) δ₂(e) - δ₂(e) δ₁(e)) e`.

An `A`-linear endomorphism `t` of `E` is left multiplication by its matrix
`IsIdempotentElem.endToMatrix t`, and a trace `τ` on `A` gives `t` the trace `τ (Tr t)` of that
matrix. The **curvature-trace formula** says that for a trace `τ` invariant under commuting
derivations `δ₁` and `δ₂`, every pair of connections `(∇₁, ∇₂)` on `E` along `δ₁` and `δ₂` has
curvature `F` with

`τ (Tr F) = (φ#Tr)(e, e, e)`, where `φ(a₀, a₁, a₂) = τ(a₀ (δ₁(a₁) δ₂(a₂) - δ₂(a₁) δ₁(a₂)))`

is the cyclic `2`-cocycle `TauCeti.traceDerivationPairCochain` of `τ`, `δ₁` and `δ₂`. For the
Grassmann connections this is a direct computation. Any other connection differs from them by
`A`-linear endomorphisms `α` and `β`, which change the curvature by the commutators
`[∇₁, β] - [∇₂, α] + [α, β]`. Each of these has vanishing trace: the last because `τ ∘ Tr` is a
trace, and the others because `τ` is invariant under the derivations. So the trace of the
curvature does not depend on the connection.

On the smooth noncommutative torus, with its canonical trace and basic derivations, `(2πi)⁻¹ φ` is
the fundamental cyclic cocycle, so `(2πi)⁻¹ τ (Tr F)` is the pairing of the projective module
`e Aⁱ` with it.

## Main definitions

* `IsIdempotentElem.grassmannConnection`: the Grassmann connection `ξ ↦ e δ(ξ)` on `e Aⁱ`, as a
  `TauCeti.RightConnection`.

## Main results

* `IsIdempotentElem.endToMatrix_curvature_grassmannConnection`: the curvature of the Grassmann
  connections has matrix `e (δ₁(e) δ₂(e) - δ₂(e) δ₁(e)) e`.
* `IsIdempotentElem.endToMatrix_derivativeEnd_grassmannConnection`: the commutator of the
  Grassmann connection with an endomorphism of matrix `t` has matrix `e δ(t) e`.
* `IsIdempotentElem.map_trace_endToMatrix_curvature`: the curvature-trace formula
  `τ (Tr F) = (φ#Tr)(e, e, e)`, for every pair of connections.

## References

* A. Connes, *C\*-algèbres et géométrie différentielle*, C. R. Acad. Sci. Paris Sér. A-B 290
  (1980), A599–A604.
* A. Connes, *Noncommutative Geometry*, Academic Press, 1994, Chapter III, §2.β and §3.
-/

public section

open LinearMap Matrix TauCeti

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A] {ι : Type*} [Fintype ι]
  {e : Matrix ι ι A}

namespace IsIdempotentElem

/-- The **Grassmann connection** `ξ ↦ e δ(ξ)` along a derivation `δ` on the right module `e Aⁱ`
of column vectors fixed by an idempotent matrix `e`; the derivation acts on the coordinates.
It is the projection by `e` of the coordinate connection. -/
def grassmannConnection (he : IsIdempotentElem e) (δ : derivationLieAlgebra k A) :
    RightConnection (E := range (Matrix.mulVecBilin A Aᵐᵒᵖ e)) δ :=
  (RightConnection.coordinate δ ι).project _ he.mulVecBilin

@[simp]
theorem coe_grassmannConnection_apply (he : IsIdempotentElem e) (δ : derivationLieAlgebra k A)
    (ξ : range (Matrix.mulVecBilin A Aᵐᵒᵖ e)) :
    (he.grassmannConnection δ ξ : ι → A) = e *ᵥ ((δ : Module.End k A) ∘ ξ) := by
  rw [grassmannConnection, RightConnection.coe_project_apply, Matrix.mulVecBilin_apply]
  congr 1
  ext i
  exact RightConnection.coordinate_apply δ _ i

/-- The curvature of the Grassmann connections along commuting derivations `δ₁` and `δ₂` is left
multiplication by `e (δ₁(e) δ₂(e) - δ₂(e) δ₁(e))`. -/
theorem coe_curvature_grassmannConnection_apply (he : IsIdempotentElem e)
    {δ₁ δ₂ : derivationLieAlgebra k A} (h : Commute (δ₁ : Module.End k A) δ₂)
    (ξ : range (Matrix.mulVecBilin A Aᵐᵒᵖ e)) :
    (RightConnection.curvature (he.grassmannConnection δ₁) (he.grassmannConnection δ₂) h ξ :
      ι → A) =
      (e * (e.map (δ₁ : Module.End k A) * e.map (δ₂ : Module.End k A) -
        e.map (δ₂ : Module.End k A) * e.map (δ₁ : Module.End k A))) *ᵥ (ξ : ι → A) := by
  have hcomm : (δ₁ : Module.End k A) ∘ (δ₂ : Module.End k A) ∘ (ξ : ι → A) =
      (δ₂ : Module.End k A) ∘ (δ₁ : Module.End k A) ∘ (ξ : ι → A) :=
    funext fun i ↦ LinearMap.congr_fun h.eq _
  -- `e δ_i(e) δ_j(ξ) = e δ_i(e) δ_j(e) ξ`, since `e δ_i(e) e = 0`.
  have key (δ δ' : derivationLieAlgebra k A) :
      e *ᵥ ((δ : Module.End k A) ∘ (e *ᵥ ((δ' : Module.End k A) ∘ (ξ : ι → A)))) =
        (e * e.map (δ : Module.End k A) * e.map (δ' : Module.End k A)) *ᵥ (ξ : ι → A) +
          e *ᵥ ((δ : Module.End k A) ∘ (δ' : Module.End k A) ∘ (ξ : ι → A)) := by
    have h₁ : (e * e.map (δ : Module.End k A)) *ᵥ ((δ' : Module.End k A) ∘ (ξ : ι → A)) =
        (e * e.map (δ : Module.End k A) * e.map (δ' : Module.End k A)) *ᵥ (ξ : ι → A) := by
      rw [derivationLieAlgebra.comp_eq_map_mulVec_add_of_mulVec_eq δ'
          (he.mem_range_mulVecBilin_iff.1 ξ.2), mulVec_add, mulVec_mulVec, mulVec_mulVec,
        he.mul_map_mul_eq_zero δ, zero_mulVec, add_zero]
    rw [derivationLieAlgebra.comp_mulVec, mulVec_add, mulVec_mulVec, mulVec_mulVec, he.eq, h₁]
  simp only [RightConnection.curvature_apply, Submodule.coe_sub,
    coe_grassmannConnection_apply, key, hcomm, Matrix.mul_sub, sub_mulVec, ← Matrix.mul_assoc]
  abel

/-- The curvature of the Grassmann connections along commuting derivations `δ₁` and `δ₂` has
matrix `e (δ₁(e) δ₂(e) - δ₂(e) δ₁(e)) e`. -/
theorem endToMatrix_curvature_grassmannConnection (he : IsIdempotentElem e)
    {δ₁ δ₂ : derivationLieAlgebra k A} (h : Commute (δ₁ : Module.End k A) δ₂) :
    he.endToMatrix
        (RightConnection.curvature (he.grassmannConnection δ₁) (he.grassmannConnection δ₂) h) =
      e * (e.map (δ₁ : Module.End k A) * e.map (δ₂ : Module.End k A) -
        e.map (δ₂ : Module.End k A) * e.map (δ₁ : Module.End k A)) * e := by
  ext i j
  rw [endToMatrix_apply, coe_curvature_grassmannConnection_apply, ← col_apply (_ * e),
    col_mul_eq_mulVec_col]

/-- The commutator `[∇, t]` of the Grassmann connection along `δ` with an endomorphism `t` of
`e Aⁱ` is left multiplication by `e δ(t)`, where `δ(t)` is the entrywise derivative of the matrix
of `t`. -/
theorem coe_derivativeEnd_grassmannConnection_apply (he : IsIdempotentElem e)
    (δ : derivationLieAlgebra k A)
    (t : Module.End Aᵐᵒᵖ (range (Matrix.mulVecBilin A Aᵐᵒᵖ e)))
    (ξ : range (Matrix.mulVecBilin A Aᵐᵒᵖ e)) :
    (RightConnection.derivativeEnd (he.grassmannConnection δ) t ξ : ι → A) =
      (e * (he.endToMatrix t).map (δ : Module.End k A)) *ᵥ (ξ : ι → A) := by
  simp only [RightConnection.derivativeEnd_apply, Submodule.coe_sub, coe_grassmannConnection_apply,
    he.apply_eq_endToMatrix_mulVec t, derivationLieAlgebra.comp_mulVec, mulVec_add, mulVec_mulVec,
    mul_endToMatrix, endToMatrix_mul]
  abel

/-- The commutator `[∇, t]` of the Grassmann connection along `δ` with an endomorphism `t` of
`e Aⁱ` has matrix `e δ(t) e`, where `δ(t)` is the entrywise derivative of the matrix of `t`. -/
theorem endToMatrix_derivativeEnd_grassmannConnection (he : IsIdempotentElem e)
    (δ : derivationLieAlgebra k A) (t : Module.End Aᵐᵒᵖ (range (Matrix.mulVecBilin A Aᵐᵒᵖ e))) :
    he.endToMatrix (RightConnection.derivativeEnd (he.grassmannConnection δ) t) =
      e * (he.endToMatrix t).map (δ : Module.End k A) * e := by
  ext i j
  rw [endToMatrix_apply, coe_derivativeEnd_grassmannConnection_apply, ← col_apply (_ * e),
    col_mul_eq_mulVec_col]

/-! ### The curvature-trace formula -/

section Trace

variable {M : Type*} [AddCommGroup M] [Module k M] {τ : A →ₗ[k] M}

/-- **The curvature-trace formula.** Let `τ` be a trace on `A` invariant under commuting
derivations `δ₁` and `δ₂`. For every pair of connections `∇₁` and `∇₂` along `δ₁` and `δ₂` on the
right module `e Aⁱ` of an idempotent matrix `e`, the trace `τ (Tr F)` of the matrix of their
curvature `F` is `(φ#Tr)(e, e, e)`, where `φ(a₀, a₁, a₂) = τ(a₀ (δ₁(a₁) δ₂(a₂) - δ₂(a₁) δ₁(a₂)))`.
In particular it does not depend on the connections. -/
theorem map_trace_endToMatrix_curvature (he : IsIdempotentElem e)
    (hτ : ∀ x y, τ (x * y) = τ (y * x)) {δ₁ δ₂ : derivationLieAlgebra k A}
    (hδ₁ : ∀ x, τ ((δ₁ : Module.End k A) x) = 0) (hδ₂ : ∀ x, τ ((δ₂ : Module.End k A) x) = 0)
    (h : Commute (δ₁ : Module.End k A) δ₂)
    (D₁ : RightConnection (E := range (Matrix.mulVecBilin A Aᵐᵒᵖ e)) δ₁)
    (D₂ : RightConnection (E := range (Matrix.mulVecBilin A Aᵐᵒᵖ e)) δ₂) :
    τ (he.endToMatrix (RightConnection.curvature D₁ D₂ h)).trace =
      matrixCochainExtension ι 2 (traceDerivationPairCochain τ δ₁ δ₂) ![e, e, e] := by
  -- Write `∇ⱼ` as the Grassmann connection plus an `A`-linear endomorphism.
  rw [← RightConnection.addEnd_difference D₁ (he.grassmannConnection δ₁),
    ← RightConnection.addEnd_difference D₂ (he.grassmannConnection δ₂),
    RightConnection.curvature_addEnd]
  set α := RightConnection.difference D₁ (he.grassmannConnection δ₁)
  set β := RightConnection.difference D₂ (he.grassmannConnection δ₂)
  set F := RightConnection.curvature (he.grassmannConnection δ₁) (he.grassmannConnection δ₂) h
  -- The change of curvature has trace zero.
  rw [map_add, map_sub he.endToMatrix (F + _), map_add he.endToMatrix F, Ring.lie_def,
    map_sub, map_mul, map_mul]
  simp only [trace_add, trace_sub, map_add, map_sub, F,
    endToMatrix_curvature_grassmannConnection, endToMatrix_derivativeEnd_grassmannConnection,
    he.map_trace_mul_map_mul_eq_zero hτ hδ₁ (he.mul_endToMatrix β) (he.endToMatrix_mul β),
    he.map_trace_mul_map_mul_eq_zero hτ hδ₂ (he.mul_endToMatrix α) (he.endToMatrix_mul α),
    map_trace_mul_comm τ hτ (he.endToMatrix α), sub_self, add_zero, sub_zero]
  -- The Grassmann curvature `e X e` has the trace of `e X`.
  rw [map_trace_mul_comm τ hτ _ e, ← Matrix.mul_assoc, he.eq,
    matrixCochainExtension_traceDerivationPairCochain]
  simp

end Trace

end IsIdempotentElem
