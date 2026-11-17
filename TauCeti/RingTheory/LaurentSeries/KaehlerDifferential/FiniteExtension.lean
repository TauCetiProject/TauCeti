/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Level.KaehlerDifferential

/-!
# Differential traces and residues on scalar-extended Laurent one-forms

Write `F = K⸨X⸩` and `Ω = ContinuousKaehlerDifferential K`. For any commutative `F`-algebra `L`,
the trace on the scalar extension `L ⊗[F] Ω` sends `x ⊗ ω` to `Tr_{L/F}(x) ω`, and its residue is
the `X⁻¹`-coefficient of this trace. For an isomorphism `e : L ≃ₐ[F] Level K d`, with `d` nonzero
in `K`, this tensor product identifies with the continuous one-forms of the ramified level via
`AlgEquiv.laurentDifferentialTensorEquiv`, sending `x ⊗ ω` to `e(x)` times the pullback of `ω`.

For formally étale `F`-algebras, the intrinsic continuous one-forms `Ω¹_cont(L/K)` identify with
`L ⊗[F] Ω` via `Extension.ContinuousKaehlerDifferential.tensorEquiv`; the intrinsic trace, residue,
and chart-independence results live in `KaehlerDifferential/Trace.lean` and
`KaehlerDifferential/Level.lean` and are constructed from the base-change maps here.

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS 1 (1968), for the
  compatibility of residues with the trace of differentials.
-/

public section

open TensorProduct
open scoped LaurentSeries

namespace TauCeti.ContinuousKaehlerDifferential

variable {K : Type*} [Field K] (L : Type*) [CommRing L] [Algebra K⸨X⸩ L]

/-- The differential trace on scalar-extended continuous forms: apply the algebra trace
on the first tensor factor, so that `x ⊗ ω` maps to `Tr(x) ω`. As with `Algebra.trace`,
this is zero for infinite-dimensional extensions. -/
noncomputable def traceBaseChange :
    L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K →ₗ[K⸨X⸩] ContinuousKaehlerDifferential K :=
  (TensorProduct.lid K⸨X⸩ _).toLinearMap ∘ₗ (Algebra.trace K⸨X⸩ L).rTensor _

@[simp]
theorem traceBaseChange_tmul (x : L) (ω : ContinuousKaehlerDifferential K) :
    traceBaseChange L (x ⊗ₜ ω) = Algebra.trace K⸨X⸩ L x • ω := by
  simp [traceBaseChange]

/-- Tracing a pulled-back form multiplies it by the degree of the extension. -/
theorem traceBaseChange_one_tmul (ω : ContinuousKaehlerDifferential K) :
    traceBaseChange L (1 ⊗ₜ ω) = Module.finrank K⸨X⸩ L • ω := by
  rw [traceBaseChange_tmul, ← map_one (algebraMap K⸨X⸩ L), Algebra.trace_algebraMap,
    smul_assoc, one_smul]

/-- The residue on scalar-extended continuous forms, computed as the residue of
their differential trace. For every separable level chart this is exactly the
coefficient residue in its level parameter. -/
noncomputable def residueBaseChange :
    L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K →+ K where
  toFun η := (equivLaurentSeries K (traceBaseChange L η)).coeff (-1)
  map_zero' := by simp
  map_add' η θ := by simp

/-- The residue is the coefficient of `t⁻¹` in the differential trace. -/
theorem residueBaseChange_apply (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    residueBaseChange L η = (equivLaurentSeries K (traceBaseChange L η)).coeff (-1) :=
  (rfl)

/-- On a pure tensor `x ⊗ f dt`, the residue is the coefficient of `t⁻¹` in
`Tr(x) f`, equivalently in `Tr(x f)`. -/
@[simp]
theorem residueBaseChange_tmul (x : L) (ω : ContinuousKaehlerDifferential K) :
    residueBaseChange L (x ⊗ₜ ω) =
      (Algebra.trace K⸨X⸩ L x * equivLaurentSeries K ω).coeff (-1) := by
  simp [residueBaseChange_apply]

/-- The residue of a form pulled back from the base is multiplied by the degree. -/
theorem residueBaseChange_one_tmul (ω : ContinuousKaehlerDifferential K) :
    residueBaseChange L (1 ⊗ₜ ω) =
      Module.finrank K⸨X⸩ L • (equivLaurentSeries K ω).coeff (-1) := by
  rw [residueBaseChange_apply, traceBaseChange_one_tmul]
  simp only [map_nsmul, HahnSeries.coeff_nsmul, Pi.smul_apply]

end TauCeti.ContinuousKaehlerDifferential

namespace AlgEquiv

open TauCeti TauCeti.ContinuousKaehlerDifferential
open TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential

variable {K : Type*} [Field K] {L : Type*} [CommRing L] [Algebra K⸨X⸩ L]
  {d : ℕ+} [NeZero ((d : ℕ) : K)]

/-- A level chart identifies scalar-extended forms with the continuous forms of that
level. This is an equivalence over the base Laurent field; scalar multiplication by
`x : L` corresponds to multiplication by `e x` on the target. -/
noncomputable def laurentDifferentialTensorEquiv (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d) :
    L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K ≃ₗ[K⸨X⸩]
      TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential K d :=
  (TensorProduct.congr e.toLinearEquiv (.refl K⸨X⸩ _)).trans
    ((TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.tensorEquiv K d).restrictScalars
      K⸨X⸩)

@[simp]
theorem laurentDifferentialTensorEquiv_tmul (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d)
    (x : L) (ω : ContinuousKaehlerDifferential K) :
    e.laurentDifferentialTensorEquiv (x ⊗ₜ ω) =
      e x • TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.map K d ω := by
  simp [laurentDifferentialTensorEquiv]

/-- The inverse chart comparison sends a scalar multiple of a pulled-back form to
its corresponding pure tensor. -/
@[simp]
theorem laurentDifferentialTensorEquiv_symm_smul_map
    (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d)
    (x : TauCeti.LaurentSeries.Level K d) (ω : ContinuousKaehlerDifferential K) :
    e.laurentDifferentialTensorEquiv.symm
        (x • TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.map K d ω) =
      e.symm x ⊗ₜ ω := by
  apply e.laurentDifferentialTensorEquiv.symm_apply_eq.mpr
  simp

/-- The chart comparison respects the extension's scalar action through the chart. -/
theorem laurentDifferentialTensorEquiv_smul
    (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d)
    (x : L) (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    e.laurentDifferentialTensorEquiv (x • η) = e x • e.laurentDifferentialTensorEquiv η := by
  induction η using TensorProduct.inductionOn with
  | tmul y ω => simp [smul_tmul', smul_eq_mul, mul_smul]
  | add η θ hη hθ => simp [smul_add, hη, hθ]

end AlgEquiv
