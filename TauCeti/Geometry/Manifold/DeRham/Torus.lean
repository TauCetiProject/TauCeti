/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
public import TauCeti.Geometry.Manifold.DifferentialForm.Torus

/-!
# The de Rham classes of the coordinate time forms of a torus

For a finite family of positive periods `p i`, the coordinate time forms `dt_i` of the torus
`Tⁿ = ∀ i, AddCircle (p i)` (`TauCeti.torusTimeForm p i`) are closed. A constant-coefficient
combination `∑ j, c j • dt_j` integrates to `c i * p i` around the `i`-th coordinate circle, while
an exact form integrates to zero around every closed curve. Hence `∑ j, c j • dt_j` is exact only
when every coefficient vanishes, so the de Rham classes `[dt_i]` are linearly independent in
`H¹_dR(Tⁿ)`. In particular each `dt_i` is a closed one-form that is not exact, and a torus of
positive dimension has nontrivial first de Rham cohomology.

These closed non-exact forms are the angle forms of the torus. Their graphs in the cotangent bundle
of the torus are the standard examples of Lagrangian sections that are not exact.

## Main declarations

* `TauCeti.torusTimeClosedForm p i`: the coordinate time form `dt_i` as a closed form.
* `TauCeti.sum_smul_torusTimeForm_mem_exactForms_iff`: `∑ j, c j • dt_j` is exact if and only if
  `c = 0`.
* `TauCeti.torusTimeForm_notMem_exactForms`: `dt_i` is not exact.
* `TauCeti.linearIndependent_deRhamCohomology_mk_torusTimeClosedForm`: the classes `[dt_i]` are
  linearly independent in `H¹_dR(Tⁿ)`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 11 (closed and exact covector fields on the torus) and
  Chapter 17 (de Rham cohomology).
-/

public section

noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)]

/-- The coordinate time form `dt_i` of the torus `∀ i, AddCircle (p i)`, as a closed form. -/
def torusTimeClosedForm (i : ι) :
    closedForms (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) 1 :=
  ⟨torusTimeForm p i, (mem_closedForms _ _).2 ((SmoothForm.isClosed_def _).1
    (isClosed_torusTimeForm p i))⟩

/-- The underlying form of `torusTimeClosedForm p i` is the coordinate time form `dt_i`. -/
@[simp]
theorem coe_torusTimeClosedForm (i : ι) :
    (torusTimeClosedForm p i : SmoothForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (∀ i, AddCircle (p i)) ℝ 1) = torusTimeForm p i :=
  (rfl)

/-- **The coordinate time forms are independent modulo exact forms.** A constant-coefficient
combination `∑ j, c j • dt_j` of the coordinate time forms of a torus is exact if and only if all
its coefficients vanish: its integral around the `i`-th coordinate circle is `c i * p i`. -/
theorem sum_smul_torusTimeForm_mem_exactForms_iff (c : ι → ℝ) :
    ∑ j, c j • torusTimeForm p j ∈
        exactForms (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) 1 ↔
      c = 0 := by
  classical
  refine ⟨fun h ↦ funext fun i ↦ ?_, fun h ↦ by simp [h]⟩
  -- Integrate around the `i`-th coordinate circle through `0`, a closed curve.
  have hγ : ContMDiff 𝓘(ℝ, ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) 1
      (fun t : ℝ ↦ update (0 : ∀ i, AddCircle (p i)) i (t : AddCircle (p i))) :=
    (contMDiff_update _ i).comp (AddCircle.contMDiff_coe (p i) 1)
  have h0 := pathIntegral_eq_zero_of_mem_exactForms h hγ (a := 0) (b := p i)
    (by simp [AddCircle.coe_period])
  rw [pathIntegral_sum_smul_torusTimeForm_update, sub_zero] at h0
  exact (mul_eq_zero.1 h0).resolve_right (Fact.out : 0 < p i).ne'

/-- **The coordinate time forms are not exact.** The coordinate time form `dt_i` of a torus is a
closed one-form that is not exact, since its integral around the `i`-th coordinate circle is the
period `p i ≠ 0`. -/
theorem torusTimeForm_notMem_exactForms (i : ι) :
    torusTimeForm p i ∉
      exactForms (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) 1 := by
  classical
  have h := (sum_smul_torusTimeForm_mem_exactForms_iff p (Pi.single i 1)).not.2
    (Pi.single_ne_zero_iff.2 one_ne_zero)
  simpa [Pi.single_apply] using h

/-- **The de Rham classes of the coordinate time forms are linearly independent** in the first de
Rham cohomology of the torus. -/
theorem linearIndependent_deRhamCohomology_mk_torusTimeClosedForm :
    LinearIndependent ℝ fun i ↦
      deRhamCohomology.mk (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (M := ∀ i, AddCircle (p i)) 1
        (torusTimeClosedForm p i) := by
  refine Fintype.linearIndependent_iff.2 fun c hc ↦ ?_
  simp_rw [← map_smul, ← map_sum, deRhamCohomology.mk_eq_zero_iff] at hc
  have h : c = 0 := (sum_smul_torusTimeForm_mem_exactForms_iff p c).1 (by simpa using hc)
  simp [h]

/-- A torus of positive dimension has nontrivial first de Rham cohomology. -/
instance nontrivial_deRhamCohomology_torus_one [Nonempty ι] :
    Nontrivial (deRhamCohomology (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (∀ i, AddCircle (p i)) 1) :=
  (linearIndependent_deRhamCohomology_mk_torusTimeClosedForm p).nontrivial

end TauCeti
