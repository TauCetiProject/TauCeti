/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.WeightOne.RiemannForm
public import TauCeti.Geometry.Symplectic.Complex.Module.Hermitian
import TauCeti.LinearAlgebra.BilinearForm.BaseChange

/-!
# The Hermitian form of a Riemann form

Let `V` be an integral module (for a complex torus `V_ℝ / Λ`, the period lattice `Λ`), `J` an
almost complex structure on its realification `V_ℝ = ℝ ⊗[ℤ] V`, and `E` an integral bilinear form
on `V` with real extension `E_ℝ`. The **Hermitian form** of `E` is

`H (v, w) = E_ℝ (J v) w + i E_ℝ v w`,

the form `TauCeti.AlmostComplexStructure.hermitianOfIm` with imaginary part `E_ℝ`. It is complex
linear in the first variable for the complex structure `J.complexModule` in which `i` acts by `J`.
When `E` is a Riemann form (`TauCeti.AlmostComplexStructure.IsRiemannForm`), `H` is conjugate
symmetric and positive definite, `H (v, v) = E_ℝ (J v) v > 0` for `v ≠ 0`. This is the
translation between Riemann forms and positive definite Hermitian forms whose imaginary part is
integral on the lattice (Birkenhake–Lange, *Complex Abelian Varieties*, Lemma 2.1.7 and §4.1;
Stanford VIGRE notes, *Complex theory of abelian varieties*, Definitions 1.13–1.14).

The convention `H (v, w) = E_ℝ (J v) w + i E_ℝ v w`, linear in the first variable, follows
Birkenhake–Lange. On `ℤ + iℤ ⊂ ℂ` with `H (v, w) = v * conj w` it gives `E (i, 1) = 1`.

## Main declarations

* `TauCeti.AlmostComplexStructure.RiemannForm.hermitian`: the form `H` of `(J, E)`.
* `TauCeti.AlmostComplexStructure.RiemannForm.im_hermitian`: `Im H = E_ℝ`.
* `TauCeti.AlmostComplexStructure.RiemannForm.hermitian_smul_left`: `H` is complex linear in the
  first variable for `J.complexModule`.
* `TauCeti.AlmostComplexStructure.IsRiemannForm.hermitian_conj_symm`: for a Riemann form, `H` is
  conjugate symmetric.
* `TauCeti.AlmostComplexStructure.IsRiemannForm.hermitian_self_pos`: for a Riemann form,
  `0 < H (v, v)` for `v ≠ 0`.
-/

public section

namespace TauCeti.AlmostComplexStructure

open scoped TensorProduct ComplexOrder ComplexConjugate

variable {V : Type*} [AddCommGroup V]

namespace RiemannForm

variable (J : AlmostComplexStructure (Hodge.Realification V)) (E : LinearMap.BilinForm ℤ V)

/-- The **Hermitian form** `H (v, w) = E_ℝ (J v) w + i E_ℝ v w` of an integral bilinear form `E`
on `V` and an almost complex structure `J` on the realification of `V`, as a real bilinear map: the
form `TauCeti.AlmostComplexStructure.hermitianOfIm` with imaginary part `E_ℝ`. It is complex linear
in the first variable for `J.complexModule` (`hermitian_smul_left`); when `E` is a Riemann form it
is conjugate symmetric (`IsRiemannForm.hermitian_conj_symm`) and positive definite
(`IsRiemannForm.hermitian_self_pos`). -/
noncomputable def hermitian : Hodge.Realification V →ₗ[ℝ] Hodge.Realification V →ₗ[ℝ] ℂ :=
  J.hermitianOfIm (E.baseChange ℝ)

/-- The Hermitian form of `E` is the Hermitian form with imaginary part `E_ℝ`. -/
theorem hermitian_def : hermitian J E = J.hermitianOfIm (E.baseChange ℝ) := (rfl)

/-- The defining formula `H (v, w) = E_ℝ (J v) w + i E_ℝ v w`. -/
@[simp]
theorem hermitian_apply (v w : Hodge.Realification V) :
    hermitian J E v w = (E.baseChange ℝ (J v) w : ℂ) + Complex.I * E.baseChange ℝ v w := by
  rw [hermitian_def, hermitianOfIm_apply]

/-- **The imaginary part of the Hermitian form is the Riemann form**: `Im H = E_ℝ`. -/
theorem im_hermitian (v w : Hodge.Realification V) :
    (hermitian J E v w).im = E.baseChange ℝ v w := by
  simp

/-- The Hermitian form is complex linear in the first variable for the complex structure
`J.complexModule`, in which `i` acts by `J`. -/
theorem hermitian_smul_left (z : ℂ) (v w : Hodge.Realification V) :
    letI := J.complexModule
    hermitian J E (z • v) w = z * hermitian J E v w :=
  J.hermitianOfIm_smul_left _ z v w

end RiemannForm

namespace IsRiemannForm

variable {J : AlmostComplexStructure (Hodge.Realification V)} {E : LinearMap.BilinForm ℤ V}

/-- The real extension of a Riemann form satisfies `E_ℝ (J v) w = E_ℝ (J w) v`: the real part of
the Hermitian form is symmetric. -/
theorem baseChange_apply_left_comm (h : J.IsRiemannForm E) (v w : Hodge.Realification V) :
    E.baseChange ℝ (J v) w = E.baseChange ℝ (J w) v :=
  J.bilinForm_apply_left_comm h.isAlt.baseChange h.invariant v w

/-- **The Hermitian form of a Riemann form is conjugate symmetric**: `conj (H (w, v)) = H (v, w)`.
-/
theorem hermitian_conj_symm (h : J.IsRiemannForm E) (v w : Hodge.Realification V) :
    conj (RiemannForm.hermitian J E w v) = RiemannForm.hermitian J E v w :=
  hermitianOfIm_conj_symm h.isAlt.baseChange h.invariant v w

/-- **The Hermitian form of a Riemann form is positive definite**:
`H (v, v) = E_ℝ (J v) v > 0` for every nonzero real vector `v`. -/
theorem hermitian_self_pos (h : J.IsRiemannForm E) {v : Hodge.Realification V} (hv : v ≠ 0) :
    0 < RiemannForm.hermitian J E v v :=
  hermitianOfIm_self_pos h.isAlt.baseChange (h.positive v hv)

end IsRiemannForm

end TauCeti.AlmostComplexStructure
