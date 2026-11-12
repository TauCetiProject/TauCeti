/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

/-!
# The Clifford action of the Kähler form

Let `J` be an orthogonal complex structure on a finite-dimensional real inner product space `V`,
with Kähler two-vector `ω` (`TauCeti.AlmostComplexStructure.kahlerForm`). For the quadratic form
`Q v = -‖v‖²`, write `c = CliffordAlgebra.ι Q` and `c₂ = CliffordAlgebra.bivectorExterior Q` for
Clifford multiplication by vectors and by two-forms.

The commutator of the Clifford image of any two-vector `F` with a generator is the Clifford image
of the contraction `v ⌟ F` (`TauCeti.twoVectorContraction`): `⁅c₂(F), c(v)⁆ = 2 c(v ⌟ F)`. For the
Kähler two-vector `v ⌟ ω = J v`, so the commutator of `c₂(ω)` with a generator is the Clifford image
of `J`: `⁅c₂(ω), c(v)⁆ = 2 c(J v)`. On a Clifford module this is how the eigenspaces of `c₂(ω)` see
`J`.
For instance, on Taubes's canonical line, the `-2i`-eigenline of `c₂(ω)` in the positive
half-spinors of a four-dimensional spin module, `v ↦ c(v) u` turns `J` into multiplication by `i`
(`TauCeti.SeibergWitten.ι_apply_apply_of_cliffordProjection_apply_eq_self`).

In dimension four, with a unitary frame `(e₀, e₁, e₂, e₃)`, `J e₀ = e₁` and `J e₂ = e₃`, the
Kähler two-vector is `ω = e₀ ∧ e₁ + e₂ ∧ e₃`, and `c₂` sends it to `c(e₀) c(e₁) + c(e₂) c(e₃)`.

## Main results

* `CliffordAlgebra.bivectorExterior_lie_ι`: `⁅c₂(F), c(v)⁆ = 2 c(v ⌟ F)`.
* `TauCeti.AlmostComplexStructure.bivectorExterior_kahlerForm`:
  `c₂(ω) = c(e₀) c(e₁) + c(e₂) c(e₃)` in a unitary frame.
* `TauCeti.AlmostComplexStructure.bivectorExterior_kahlerForm_lie_ι`:
  `⁅c₂(ω), c(v)⁆ = 2 c(J v)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.4.
-/

public section

namespace CliffordAlgebra

open TauCeti exteriorPower
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Q : QuadraticForm ℝ V}

/-- **The Clifford image of a two-vector generates its contraction**: for `Q v = -‖v‖²`,
`⁅c₂(F), c(v)⁆ = 2 c(v ⌟ F)`, where `v ⌟ F` is `TauCeti.twoVectorContraction F v`. -/
theorem bivectorExterior_lie_ι (hQ : ∀ v, Q v = -‖v‖ ^ 2) (F : ⋀[ℝ]^2 V) (v : V) :
    ⁅bivectorExterior Q F, ι Q v⁆ = ι Q ((2 : ℝ) • twoVectorContraction F v) := by
  have hpolar (x y : V) : QuadraticMap.polar Q x y = -2 * ⟪x, y⟫ := by
    simp only [QuadraticMap.polar, hQ, norm_add_sq_real]
    ring
  -- Both sides are linear in `F`; compare them on `a ∧ b`, using
  -- `v ⌟ (a ∧ b) = ⟪v, a⟫ b - ⟪v, b⟫ a`.
  have key : (LinearMap.mulRight ℝ (ι Q v) - LinearMap.mulLeft ℝ (ι Q v)) ∘ₗ bivectorExterior Q =
      ((2 : ℝ) • ι Q) ∘ₗ (LinearMap.applyₗ (R := ℝ) v ∘ₗ
        { toFun := twoVectorContraction, map_add' := twoVectorContraction_add,
          map_smul' := twoVectorContraction_smul }) := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun w ↦ ?_)
    have hw : w = ![w 0, w 1] := (FinVec.etaExpand_eq w).symm
    have hc : twoVectorContraction (ιMulti ℝ 2 w) v = ⟪v, w 0⟫ • w 1 - ⟪v, w 1⟫ • w 0 := by
      refine ext_inner_right ℝ fun x ↦ ?_
      rw [inner_twoVectorContraction_apply, inner_ιMulti_ιMulti]
      simp [Matrix.det_fin_two, inner_sub_left, real_inner_smul_left, real_inner_comm v]
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.sub_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, LinearMap.smul_apply,
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.applyₗ_apply_apply]
    rw [hc]
    conv_lhs => rw [hw]
    rw [bivectorExterior_apply_ιMulti, ← Ring.lie_def, bivector_lie_ι, hpolar, hpolar]
    simp only [map_sub, map_smul, smul_sub, smul_smul]
    rw [real_inner_comm (w 1) v, real_inner_comm (w 0) v]
    module
  simpa [Ring.lie_def] using LinearMap.congr_fun key F

end CliffordAlgebra

namespace TauCeti.AlmostComplexStructure

open CliffordAlgebra exteriorPower
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Q : QuadraticForm ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2) {J : AlmostComplexStructure V}

section Frame

variable {e : OrthonormalBasis (Fin 4) ℝ V} (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)

include hQ h₀ h₂ in
/-- **The Clifford image of the Kähler form** in a unitary frame:
`c₂(ω) = c(e₀) c(e₁) + c(e₂) c(e₃)`. -/
theorem bivectorExterior_kahlerForm :
    bivectorExterior Q J.kahlerForm = ι Q (e 0) * ι Q (e 1) + ι Q (e 2) * ι Q (e 3) := by
  have hortho {i j : Fin 4} (hij : i ≠ j) : Q.IsOrtho (e i) (e j) :=
    (QuadraticMap.isOrtho_iff_inner_eq_zero hQ).2 (e.orthonormal.2 hij)
  rw [kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂, map_add, bivectorExterior_apply_ιMulti,
    bivectorExterior_apply_ιMulti, bivector_eq_ι_mul_ι_of_isOrtho Q (hortho (by decide)),
    bivector_eq_ι_mul_ι_of_isOrtho Q (hortho (by decide))]

end Frame

include hQ in
/-- **The Kähler form generates `J` in the Clifford algebra**: for an orthogonal `J`,
`⁅c₂(ω), c(v)⁆ = 2 c(J v)`. -/
theorem bivectorExterior_kahlerForm_lie_ι (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) (v : V) :
    ⁅bivectorExterior Q J.kahlerForm, ι Q v⁆ = ι Q ((2 : ℝ) • J v) := by
  rw [bivectorExterior_lie_ι hQ, twoVectorContraction_kahlerForm hJ]

end TauCeti.AlmostComplexStructure
