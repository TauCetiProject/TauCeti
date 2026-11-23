/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
public import TauCeti.Analysis.Normed.Operator.LinearPMap.Cayley
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Intertwining
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# The Cayley transform of a self-adjoint partial linear map

For a symmetric partial linear map `A` on a complex inner product space with `-i` as a resolvent
point, the identity `‖-i y - A y‖ = ‖i y - A y‖` makes the Cayley transform `LinearPMap.cayley A`
an isometry. Since every nonreal scalar is a resolvent point of a self-adjoint partial linear map
on a complex Hilbert space, its Cayley transform is also surjective, hence unitary, and in
particular star-normal. This turns the spectral theory of an unbounded self-adjoint operator into
that of a bounded unitary operator: every resolvent of `A` is a continuous function of its
Cayley transform. In particular, a bounded operator intertwining two
self-adjoint partial linear maps intertwines every continuous function of their Cayley transforms.

The Cayley transform itself and its algebraic properties are in
`TauCeti.Analysis.Normed.Operator.LinearPMap.Cayley`.

## Main results

* `LinearPMap.IsFormalAdjoint.norm_cayley_apply`: `U` is isometric for symmetric `A`.
* `IsSelfAdjoint.cayley_mem_unitary`, `IsSelfAdjoint.isStarNormal_cayley`: the Cayley transform
  of a self-adjoint partial linear map is unitary and star-normal.
* `IsSelfAdjoint.resolvent_eq_cfc_cayley`: the resolvent `R(z)` is the continuous function
  `(1 - U) ((z - i) - (z + i) U)⁻¹` of the Cayley transform `U`.
* `IsSelfAdjoint.ofReal_re_inverseCayley_eq_and_mem_spectrum`: away from `1`, the inverse Cayley
  image `i (1 + w) / (1 - w)` of a point `w` of the spectrum of `U` is real and lies in the
  spectrum of `A`.
* `LinearPMap.Intertwines.comp_cfc_cayley_eq`: an intertwiner `X A ⊆ B X` of self-adjoint partial
  linear maps satisfies `X f(U_A) = f(U_B) X` for every symbol `f` continuous on both spectra.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Section VIII.3 (the Cayley transform).
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Section 13.1.
-/

public section

noncomputable section

open Complex

namespace LinearPMap

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {A : E →ₗ.[ℂ] E}

/-- **The Cayley transform of a symmetric operator is isometric** whenever `-i` is a resolvent
point: `‖-i y - A y‖² = ‖y‖² + ‖A y‖² = ‖i y - A y‖²` for `y ∈ dom A`. -/
theorem IsFormalAdjoint.norm_cayley_apply (hA : A.IsFormalAdjoint A) (h : -I ∈ A.resolventSet)
    (x : E) : ‖A.cayley x‖ = ‖x‖ := by
  obtain ⟨y, rfl⟩ : ∃ y : A.domain, -I • (y : E) - A y = x :=
    ⟨⟨A.resolvent (-I) x, resolvent_mem_domain h x⟩, smul_sub_apply_resolvent h x⟩
  rw [cayley_neg_I_smul_sub_apply h, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    hA.norm_smul_sub_sq I, hA.norm_smul_sub_sq (-I)]
  simp

variable [CompleteSpace E]

/-- The Cayley transform of a self-adjoint partial linear map preserves norms. -/
theorem _root_.IsSelfAdjoint.norm_cayley_apply (hA : IsSelfAdjoint A) (x : E) :
    ‖A.cayley x‖ = ‖x‖ :=
  hA.isFormalAdjoint.norm_cayley_apply (hA.mem_resolventSet_of_im_ne_zero (z := -I) (by simp)) x

/-- The Cayley transform of a self-adjoint partial linear map is surjective. -/
theorem _root_.IsSelfAdjoint.cayley_surjective (hA : IsSelfAdjoint A) :
    Function.Surjective A.cayley :=
  LinearPMap.cayley_surjective (hA.mem_resolventSet_of_im_ne_zero (z := I) (by simp))
    (hA.mem_resolventSet_of_im_ne_zero (z := -I) (by simp))

/-- **The Cayley transform of a self-adjoint partial linear map is unitary.** -/
theorem _root_.IsSelfAdjoint.cayley_mem_unitary (hA : IsSelfAdjoint A) :
    A.cayley ∈ unitary (E →L[ℂ] E) :=
  (Unitary.linearIsometryEquiv.symm <| LinearIsometryEquiv.ofSurjective
    ⟨A.cayley.toLinearMap, hA.norm_cayley_apply⟩ hA.cayley_surjective).property

/-- The Cayley transform of a self-adjoint partial linear map is star-normal. -/
theorem _root_.IsSelfAdjoint.isStarNormal_cayley (hA : IsSelfAdjoint A) :
    IsStarNormal A.cayley :=
  isStarNormal_of_mem_unitary hA.cayley_mem_unitary

/-- **The resolvent as a function of the Cayley transform.** At every resolvent point `z`, the
resolvent of a self-adjoint partial linear map is `R(z) = (1 - U) ((z - i) - (z + i) U)⁻¹`, the
continuous functional calculus of the Cayley transform `U` at
`w ↦ (1 - w) / ((z - i) - (z + i) w)`. -/
theorem _root_.IsSelfAdjoint.resolvent_eq_cfc_cayley (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z ∈ A.resolventSet) :
    A.resolvent z = cfc (fun w => (1 - w) / (z - I - (z + I) * w)) A.cayley := by
  have := hA.isStarNormal_cayley
  have hm := hA.neg_I_mem_resolventSet
  have hd : ∀ w ∈ _root_.spectrum ℂ A.cayley, z - I - (z + I) * w ≠ 0 := fun _ hw =>
    sub_I_sub_add_I_mul_ne_zero_of_mem_spectrum_cayley hm hz hw
  rw [cfc_map_div _ _ A.cayley hd,
    Ring.eq_mul_inverse_iff_mul_eq _ _ _ ((isUnit_cfc_iff _ A.cayley).mpr hd),
    cfc_sub (fun _ => z - I) (fun w => (z + I) * w) A.cayley, cfc_const (z - I) A.cayley,
    cfc_const_mul (z + I) (fun w => w) A.cayley, cfc_sub (fun _ => 1) (fun w => w) A.cayley,
    cfc_const_one ℂ A.cayley, cfc_id' ℂ A.cayley, Algebra.algebraMap_eq_smul_one]
  -- With `U = 1 + 2i R(-i)`, this is the resolvent identity `R(z) - R(-i) = (-i - z) R(z) R(-i)`.
  have h := resolvent_sub_resolvent hz hm
  rw [← ContinuousLinearMap.mul_def] at h
  have hU : A.cayley = 1 + (2 * I) • A.resolvent (-I) := by
    ext x
    simp [cayley_apply]
  simp only [hU, mul_sub, mul_add, mul_smul_comm, mul_one]
  linear_combination (norm := module) (-2 * I) • h

/-- Away from `1`, a point `w` of the spectrum of the Cayley transform of a self-adjoint partial
linear map `A` has a real inverse Cayley image `i (1 + w) / (1 - w)`, which lies in the spectrum of
`A`. -/
theorem _root_.IsSelfAdjoint.ofReal_re_inverseCayley_eq_and_mem_spectrum (hA : IsSelfAdjoint A)
    {w : ℂ} (hw : w ∈ _root_.spectrum ℂ A.cayley) (h1 : w ≠ 1) :
    (((I * (1 + w) / (1 - w)).re : ℝ) : ℂ) = I * (1 + w) / (1 - w) ∧
      I * (1 + w) / (1 - w) ∈ A.spectrum := by
  have hmem := (mem_spectrum_cayley_iff hA.neg_I_mem_resolventSet h1).mp hw
  exact ⟨Complex.ext (by simp) (by simpa using (hA.spectrum_subset_im_eq_zero hmem).symm), hmem⟩

section Intertwining

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] {B : F →ₗ.[ℂ] F} {X : E →L[ℂ] F}

/-- **Continuous-calculus intertwining.** An intertwiner of self-adjoint partial linear maps
intertwines the continuous functional calculi of their Cayley transforms: `X f(U_A) = f(U_B) X`
for every symbol `f` continuous on both spectra. -/
theorem Intertwines.comp_cfc_cayley_eq (h : A.Intertwines B X) (hA : IsSelfAdjoint A)
    (hB : IsSelfAdjoint B) (f : ℂ → ℂ)
    (hfA : ContinuousOn f (_root_.spectrum ℂ A.cayley) := by cfc_cont_tac)
    (hfB : ContinuousOn f (_root_.spectrum ℂ B.cayley) := by cfc_cont_tac) :
    X ∘L cfc f A.cayley = cfc f B.cayley ∘L X := by
  have hU := h.comp_cayley_eq (hA.mem_resolventSet_of_im_ne_zero (by simp))
    (hB.mem_resolventSet_of_im_ne_zero (by simp))
  have := hA.isStarNormal_cayley
  have := hB.isStarNormal_cayley
  exact X.comp_cfc_eq_cfc_comp hU
    (X.comp_star_eq_star_comp_of_mul_star_self_of_star_mul_self
      (Unitary.mul_star_self_of_mem hA.cayley_mem_unitary)
      (Unitary.star_mul_self_of_mem hB.cayley_mem_unitary) hU) f

end Intertwining

end InnerProductSpace

end LinearPMap

end
