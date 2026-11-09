/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Idempotent
public import TauCeti.LinearAlgebra.Matrix.Trace.Basic
public import TauCeti.NoncommutativeGeometry.Connection.Basic
public import TauCeti.RingTheory.CyclicCohomology.Derivation

/-!
# The Grassmann connection and the curvature-trace formula

Let `e : Matrix ι ι A` be an idempotent matrix over an algebra `A`, and `E = e Aⁱ` the finitely
generated projective right `A`-module of column vectors fixed by `e`. For a derivation `δ` of `A`,
the **Grassmann connection** along `δ` is

`∇ ξ = e δ(ξ)`,

where `δ` acts on the coordinates of `ξ`. For commuting derivations `δ₁` and `δ₂`, the curvature of
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
`A`-linear endomorphisms, which change the curvature by the commutators
`⁅∇₁, β⁆ - ⁅∇₂, α⁆ + ⁅α, β⁆`. Each of these has vanishing trace: the last because `τ ∘ Tr` is a
trace, and the others because `τ` is invariant under the derivations. So the trace of the
curvature does not depend on the connection.

On the smooth noncommutative torus, with its canonical trace and basic derivations, `(2πi)⁻¹ φ` is
the fundamental cyclic cocycle, so `(2πi)⁻¹ τ (Tr F)` is the pairing of the projective module
`e Aⁱ` with it.

## Main definitions

* `IsIdempotentElem.grassmannConnection`: the Grassmann connection `ξ ↦ e δ(ξ)` on `e Aⁱ`.

## Main results

* `IsIdempotentElem.endToMatrix_curvature_grassmannConnection`: the curvature of the Grassmann
  connections has matrix `e (δ₁(e) δ₂(e) - δ₂(e) δ₁(e)) e`.
* `IsIdempotentElem.endToMatrix_lie_grassmannConnection`: the commutator of the Grassmann
  connection with an endomorphism of matrix `t` has matrix `e δ(t) e`.
* `IsIdempotentElem.map_trace_endToMatrix_curvature`: the curvature-trace formula
  `τ (Tr F) = (φ#Tr)(e, e, e)`, for every pair of connections.

## References

* A. Connes, *C\*-algèbres et géométrie différentielle*, C. R. Acad. Sci. Paris Sér. A-B 290
  (1980), A599–A604.
* A. Connes, *Noncommutative Geometry*, Academic Press, 1994, Chapter III, §2.β and §3.
-/

public section

open LinearMap Matrix TauCeti

open scoped RightActions

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A] {ι : Type*} [Fintype ι]
  {e : Matrix ι ι A}

namespace IsIdempotentElem

/-- The **Grassmann connection** `ξ ↦ e δ(ξ)` along a derivation `δ` on the right module `e Aⁱ`
of column vectors fixed by an idempotent matrix `e`; the derivation acts on the coordinates. -/
def grassmannConnection (he : IsIdempotentElem e) (δ : derivationLieAlgebra k A) :
    DerivationConnection δ (range (Matrix.mulVecBilin A Aᵐᵒᵖ e)) where
  toAddMonoidHom :=
    { toFun ξ := ⟨e *ᵥ ((δ : Module.End k A) ∘ ξ), mem_range_self _ _⟩
      map_zero' := Subtype.ext <| by ext; simp [mulVec, dotProduct]
      map_add' ξ η := Subtype.ext <| by
        ext; simp [mulVec, dotProduct, mul_add, Finset.sum_add_distrib] }
  leibniz' ξ a := Subtype.ext <| by
    have hξ : e *ᵥ (ξ : ι → A) = ξ := he.mem_range_mulVecBilin_iff.1 ξ.2
    have hδ : (δ : Module.End k A) ∘ ((ξ : ι → A) <• a) =
        ((δ : Module.End k A) ∘ (ξ : ι → A)) <• a + (ξ : ι → A) <• (δ : Module.End k A) a :=
      funext fun i ↦ by simp
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Submodule.coe_add, Submodule.coe_smul, hδ,
      mulVec_add, mulVec_smul, hξ]

@[simp]
theorem coe_grassmannConnection_apply (he : IsIdempotentElem e) (δ : derivationLieAlgebra k A)
    (ξ : range (Matrix.mulVecBilin A Aᵐᵒᵖ e)) :
    (he.grassmannConnection δ ξ : ι → A) = e *ᵥ ((δ : Module.End k A) ∘ ξ) :=
  (rfl)

/-- The coordinate derivative of a column vector `ξ` fixed by an idempotent `e` splits as
`δ(ξ) = δ(e) ξ + e δ(ξ)`. -/
private theorem comp_eq_map_mulVec_add (he : IsIdempotentElem e) (δ : derivationLieAlgebra k A)
    (ξ : range (Matrix.mulVecBilin A Aᵐᵒᵖ e)) :
    (δ : Module.End k A) ∘ (ξ : ι → A) =
      e.map (δ : Module.End k A) *ᵥ ξ + e *ᵥ ((δ : Module.End k A) ∘ ξ) := by
  conv_lhs => rw [← he.mem_range_mulVecBilin_iff.1 ξ.2]
  exact derivationLieAlgebra.comp_mulVec δ e ξ

/-- `e δ(e) e = 0` for an idempotent matrix `e` and the entrywise derivation `δ`. -/
private theorem mul_map_mul_self_eq_zero (he : IsIdempotentElem e)
    (δ : derivationLieAlgebra k A) : e * e.map (δ : Module.End k A) * e = 0 := by
  simpa using derivationLieAlgebra.mul_apply_mul_eq_zero (derivationLieAlgebra.mapMatrix δ) he

/-- The curvature of the Grassmann connections along commuting derivations `δ₁` and `δ₂` is left
multiplication by `e (δ₁(e) δ₂(e) - δ₂(e) δ₁(e))`. -/
theorem coe_curvature_grassmannConnection_apply (he : IsIdempotentElem e)
    {δ₁ δ₂ : derivationLieAlgebra k A} (h : Commute (δ₁ : Module.End k A) δ₂)
    (ξ : range (Matrix.mulVecBilin A Aᵐᵒᵖ e)) :
    ((he.grassmannConnection δ₁).curvature (he.grassmannConnection δ₂) h ξ : ι → A) =
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
      rw [comp_eq_map_mulVec_add he δ' ξ, mulVec_add, mulVec_mulVec, mulVec_mulVec,
        mul_map_mul_self_eq_zero he δ, zero_mulVec, add_zero]
    rw [derivationLieAlgebra.comp_mulVec, mulVec_add, mulVec_mulVec, mulVec_mulVec, he.eq, h₁]
  simp only [DerivationConnection.curvature_apply, Submodule.coe_sub,
    coe_grassmannConnection_apply, key, hcomm, Matrix.mul_sub, sub_mulVec, ← Matrix.mul_assoc]
  abel

/-- The curvature of the Grassmann connections along commuting derivations `δ₁` and `δ₂` has
matrix `e (δ₁(e) δ₂(e) - δ₂(e) δ₁(e)) e`. -/
theorem endToMatrix_curvature_grassmannConnection (he : IsIdempotentElem e)
    {δ₁ δ₂ : derivationLieAlgebra k A} (h : Commute (δ₁ : Module.End k A) δ₂) :
    he.endToMatrix ((he.grassmannConnection δ₁).curvature (he.grassmannConnection δ₂) h) =
      e * (e.map (δ₁ : Module.End k A) * e.map (δ₂ : Module.End k A) -
        e.map (δ₂ : Module.End k A) * e.map (δ₁ : Module.End k A)) * e := by
  ext i j
  rw [endToMatrix_apply, coe_curvature_grassmannConnection_apply, ← col_apply (_ * e),
    col_mul_eq_mulVec_col]

/-- The commutator `⁅∇, t⁆` of the Grassmann connection along `δ` with an endomorphism `t` of
`e Aⁱ` is left multiplication by `e δ(t)`, where `δ(t)` is the entrywise derivative of the matrix
of `t`. -/
theorem coe_lie_grassmannConnection_apply (he : IsIdempotentElem e) (δ : derivationLieAlgebra k A)
    (t : Module.End Aᵐᵒᵖ (range (Matrix.mulVecBilin A Aᵐᵒᵖ e)))
    (ξ : range (Matrix.mulVecBilin A Aᵐᵒᵖ e)) :
    (⁅he.grassmannConnection δ, t⁆ ξ : ι → A) =
      (e * (he.endToMatrix t).map (δ : Module.End k A)) *ᵥ (ξ : ι → A) := by
  simp only [DerivationConnection.lie_apply, Submodule.coe_sub, coe_grassmannConnection_apply,
    he.apply_eq_endToMatrix_mulVec t, derivationLieAlgebra.comp_mulVec, mulVec_add, mulVec_mulVec,
    mul_endToMatrix, endToMatrix_mul]
  abel

/-- The commutator `⁅∇, t⁆` of the Grassmann connection along `δ` with an endomorphism `t` of
`e Aⁱ` has matrix `e δ(t) e`, where `δ(t)` is the entrywise derivative of the matrix of `t`. -/
theorem endToMatrix_lie_grassmannConnection (he : IsIdempotentElem e)
    (δ : derivationLieAlgebra k A) (t : Module.End Aᵐᵒᵖ (range (Matrix.mulVecBilin A Aᵐᵒᵖ e))) :
    he.endToMatrix ⁅he.grassmannConnection δ, t⁆ =
      e * (he.endToMatrix t).map (δ : Module.End k A) * e := by
  ext i j
  rw [endToMatrix_apply, coe_lie_grassmannConnection_apply, ← col_apply (_ * e),
    col_mul_eq_mulVec_col]

/-! ### The curvature-trace formula -/

section Trace

variable {M : Type*} [AddCommGroup M] [Module k M] {τ : A →ₗ[k] M}

/-- For a trace `τ` invariant under `δ`, the matrix `e δ(t) e` of the commutator of the Grassmann
connection with an endomorphism `t` of `e Aⁱ` has trace zero. -/
private theorem map_trace_mul_map_endToMatrix_mul_eq_zero (he : IsIdempotentElem e)
    (hτ : ∀ x y, τ (x * y) = τ (y * x)) {δ : derivationLieAlgebra k A}
    (hδ : ∀ x, τ ((δ : Module.End k A) x) = 0)
    (t : Module.End Aᵐᵒᵖ (range (Matrix.mulVecBilin A Aᵐᵒᵖ e))) :
    τ (e * (he.endToMatrix t).map (δ : Module.End k A) * e).trace = 0 := by
  set T := he.endToMatrix t
  -- Differentiating `T = T e` gives `δ(T) e = δ(T) - T δ(e)`.
  have hL : T.map (δ : Module.End k A) =
      T.map (δ : Module.End k A) * e + T * e.map (δ : Module.End k A) := by
    simpa [T, endToMatrix_mul] using
      derivationLieAlgebra.leibniz (derivationLieAlgebra.mapMatrix δ) T e
  have h₀ : τ (T.map (δ : Module.End k A)).trace = 0 := by
    simp [Matrix.trace, hδ]
  have h₁ : τ (T * e.map (δ : Module.End k A)).trace = 0 := by
    calc τ (T * e.map (δ : Module.End k A)).trace
        _ = τ (e * T * e.map (δ : Module.End k A)).trace := by rw [mul_endToMatrix]
        _ = τ (T * e.map (δ : Module.End k A) * e).trace := by
          rw [Matrix.mul_assoc, map_trace_mul_comm τ hτ e]
        _ = τ (T * e * e.map (δ : Module.End k A) * e).trace := by rw [endToMatrix_mul]
        _ = 0 := by
          rw [Matrix.mul_assoc T, Matrix.mul_assoc T, mul_map_mul_self_eq_zero he δ,
            Matrix.mul_zero, trace_zero, map_zero]
  rw [Matrix.mul_assoc, map_trace_mul_comm τ hτ e, Matrix.mul_assoc, he.eq,
    eq_sub_of_add_eq hL.symm, trace_sub, map_sub, h₀, h₁, sub_zero]

/-- **The curvature-trace formula.** Let `τ` be a trace on `A` invariant under commuting
derivations `δ₁` and `δ₂`. For every pair of connections `∇₁` and `∇₂` along `δ₁` and `δ₂` on the
right module `e Aⁱ` of an idempotent matrix `e`, the trace `τ (Tr F)` of the matrix of their
curvature `F` is `(φ#Tr)(e, e, e)`, where `φ(a₀, a₁, a₂) = τ(a₀ (δ₁(a₁) δ₂(a₂) - δ₂(a₁) δ₁(a₂)))`.
In particular it does not depend on the connections. -/
theorem map_trace_endToMatrix_curvature (he : IsIdempotentElem e)
    (hτ : ∀ x y, τ (x * y) = τ (y * x)) {δ₁ δ₂ : derivationLieAlgebra k A}
    (hδ₁ : ∀ x, τ ((δ₁ : Module.End k A) x) = 0) (hδ₂ : ∀ x, τ ((δ₂ : Module.End k A) x) = 0)
    (h : Commute (δ₁ : Module.End k A) δ₂)
    (D₁ : DerivationConnection δ₁ (range (Matrix.mulVecBilin A Aᵐᵒᵖ e)))
    (D₂ : DerivationConnection δ₂ (range (Matrix.mulVecBilin A Aᵐᵒᵖ e))) :
    τ (he.endToMatrix (D₁.curvature D₂ h)).trace =
      matrixCochainExtension ι 2 (traceDerivationPairCochain τ δ₁ δ₂) ![e, e, e] := by
  -- Write `∇ⱼ` as the Grassmann connection plus an `A`-linear endomorphism.
  have : Nonempty (DerivationConnection δ₁ (range (Matrix.mulVecBilin A Aᵐᵒᵖ e))) :=
    ⟨he.grassmannConnection δ₁⟩
  have : Nonempty (DerivationConnection δ₂ (range (Matrix.mulVecBilin A Aᵐᵒᵖ e))) :=
    ⟨he.grassmannConnection δ₂⟩
  rw [← vsub_vadd D₁ (he.grassmannConnection δ₁), ← vsub_vadd D₂ (he.grassmannConnection δ₂),
    DerivationConnection.curvature_vadd, Ring.lie_def,
    sub_eq_add_neg _ (⁅he.grassmannConnection δ₂, D₁ -ᵥ he.grassmannConnection δ₁⁆)]
  -- The change of curvature has trace zero.
  simp only [map_add, map_neg, map_sub, map_mul, trace_add, trace_neg, trace_sub,
    endToMatrix_curvature_grassmannConnection, endToMatrix_lie_grassmannConnection,
    map_trace_mul_map_endToMatrix_mul_eq_zero he hτ hδ₁ (D₂ -ᵥ he.grassmannConnection δ₂),
    map_trace_mul_map_endToMatrix_mul_eq_zero he hτ hδ₂ (D₁ -ᵥ he.grassmannConnection δ₁),
    map_trace_mul_comm τ hτ (he.endToMatrix (D₁ -ᵥ he.grassmannConnection δ₁)), sub_self,
    neg_zero, add_zero]
  -- The Grassmann curvature `e X e` has the trace of `e X`.
  rw [map_trace_mul_comm τ hτ _ e, ← Matrix.mul_assoc, he.eq,
    matrixCochainExtension_traceDerivationPairCochain]
  simp

end Trace

end IsIdempotentElem
