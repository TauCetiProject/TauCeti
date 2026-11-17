/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Level.KaehlerDifferential

/-!
# Differential traces and residues in finite Laurent extensions

Write `F = K⸨X⸩` and `Ω = ContinuousKaehlerDifferential K`. The trace on the scalar
extension `L ⊗[F] Ω` sends `x ⊗ ω` to `Tr_{L/F}(x) ω`. For an isomorphism
`e : L ≃ₐ[F] Level K d`, with `d` nonzero in `K`, this tensor product identifies with
the continuous one-forms of the ramified level. The comparison sends `x ⊗ ω` to
`e(x)` times the pullback of `ω`, and intertwines the two differential traces.

Consequently the coefficient residue computed in the level parameter is independent
of the chosen isomorphism: it equals the residue of the trace. This supplies a
chart-independent residue on `L ⊗[F] Ω`, not just on coefficients of forms expressed
in `dt`. When `K` is algebraically closed of characteristic zero, every finite
extension has such a chart by `Level.algEquivOfFinrankEq` from
`LaurentSeries.Puiseux.FiniteExtension`.

The constructions reuse the scalar-extension comparison and trace-residue identity
for explicit levels from `LaurentSeries.Level.KaehlerDifferential`. No topology or
derivation on an arbitrary extension is chosen here.

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS 1 (1968), for the
  compatibility of residues with the trace of differentials.
-/

public section

open TensorProduct
open scoped LaurentSeries

namespace TauCeti.ContinuousKaehlerDifferential

variable {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K⸨X⸩ L]

/-- The differential trace on scalar-extended continuous forms: apply the field trace
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

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K⸨X⸩ L]
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

/-- Differential trace commutes with every level chart. In particular the trace
transported from the explicit level is the trace on the first tensor factor. -/
@[simp]
theorem trace_laurentDifferentialTensorEquiv
    (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d)
    (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.trace K d
        (e.laurentDifferentialTensorEquiv η) = traceBaseChange L η := by
  induction η using TensorProduct.inductionOn with
  | tmul x ω =>
    simp only [laurentDifferentialTensorEquiv_tmul,
      TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.trace_smul_map,
      traceBaseChange_tmul]
    rw [Algebra.trace_eq_of_algEquiv e]
  | add η θ hη hθ => simp [hη, hθ]

/-- **Trace-residue compatibility in any level chart.** The residue of the trace
of a scalar-extended form is the coefficient residue in the level parameter. -/
theorem residueBaseChange_eq_coeff (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d)
    (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    residueBaseChange L η =
      (TauCeti.LaurentSeries.Level.ringEquivLaurentSeries K d
        (TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.equivLevel K d
          (e.laurentDifferentialTensorEquiv η))).coeff (-1) := by
  rw [residueBaseChange_apply, ← trace_laurentDifferentialTensorEquiv e]
  exact coeff_neg_one_equivLaurentSeries_trace _

/-- **Independence of the level chart.** Two isomorphisms with ramified levels give
the same coefficient residue on scalar-extended forms. The levels need not be
identified in advance. -/
theorem coeff_laurentDifferentialTensorEquiv_eq {n : ℕ+} [NeZero ((n : ℕ) : K)]
    (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d)
    (e' : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K n)
    (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    (TauCeti.LaurentSeries.Level.ringEquivLaurentSeries K d
      (TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.equivLevel K d
        (e.laurentDifferentialTensorEquiv η))).coeff (-1) =
    (TauCeti.LaurentSeries.Level.ringEquivLaurentSeries K n
      (TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.equivLevel K n
        (e'.laurentDifferentialTensorEquiv η))).coeff (-1) := by
  rw [← residueBaseChange_eq_coeff e, ← residueBaseChange_eq_coeff e']

end AlgEquiv
