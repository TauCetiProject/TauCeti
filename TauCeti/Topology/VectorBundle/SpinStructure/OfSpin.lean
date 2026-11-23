/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SpinStructure.Spinor

/-!
# The `Spinᶜ` structure of a Spin structure

A Spin structure `s` of rank `n ≥ 1` on a real vector bundle `E` with fibre inner products, with
principal `Spin(n)`-bundle `P`, induces a `Spinᶜ` structure `s.toSpinC`
(`TauCeti.SpinStructure.toSpinC`): its principal bundle is the extension of structure group
`P ×_{Spin(n)} Spinᶜ(n)` along `s ↦ [s, 1]` (`CliffordAlgebra.spinCGroup.ofSpin`), and the frame of
`[p, 1]` is the frame of `p` (`TauCeti.SpinStructure.toFrame_inlSpinC`).

The determinant character `[s, z] ↦ z²` is trivial on `Spin(n)`, so the class `[[p, 1], 1]` in
the determinant line of `s.toSpinC` does not depend on the point `p` of `P` over `x`
(`TauCeti.SpinStructure.determinantLineSection_eq`). It is therefore a nowhere vanishing section of
the determinant line (`TauCeti.SpinStructure.determinantLineSection_ne_zero`), and it is continuous
(`TauCeti.SpinStructure.continuous_determinantLineSection`). Scaling it identifies every fibre
with `ℂ` (`TauCeti.SpinStructure.determinantLineEquiv`).

## Main definitions

* `TauCeti.SpinStructure.toSpinC`: the `Spinᶜ` structure induced by a Spin structure.
* `TauCeti.SpinStructure.determinantLineSection`: the section `x ↦ [[p, 1], 1]` of its determinant
  line.
* `TauCeti.SpinStructure.determinantLineEquiv`: the identification `ℂ ≃ L_x`,
  `c ↦ c • determinantLineSection x`.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

open Bundle MulOpposite CliffordAlgebra

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {F : Type*} {E : X → Type}
  [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F E]
  [VectorBundle ℝ F E] {n : ℕ} [NeZero n]

/-- The proof that the standard form on `ℝⁿ`, `n ≥ 1`, is nonzero, on which `Spinᶜ(n)` depends. -/
local notation "hQn" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)

namespace SpinStructure

/-- The inclusion `Spin(n) → Spinᶜ(n)` lifts the vector action `Spin(n) → SO(n)` along the
rotation homomorphism `Spinᶜ(n) → SO(n)`. -/
private theorem comp_ofSpin :
    ((QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)).subtype.comp
        (spinCGroup.toSpecialOrthogonal (realCliffordForm n 0) hQn)).comp
        (spinCGroup.ofSpin (realCliffordForm n 0) hQn) =
      (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)).subtype.comp
        (spinToSpecialOrthogonal (realCliffordForm n 0)) := by
  ext g : 1
  simp [spinCGroup.toSpecialOrthogonal_ofSpin]

variable (s : SpinStructure F E n)

/-- **The `Spinᶜ` structure of a Spin structure**: the extension of its principal `Spin(n)`-bundle
`P` along the inclusion `Spin(n) → Spinᶜ(n)`, `s ↦ [s, 1]`. Its principal bundle is
`P ×_{Spin(n)} Spinᶜ(n)`, and the frame of `[p, 1]` is the frame of `p`
(`TauCeti.SpinStructure.toFrame_inlSpinC`). -/
noncomputable def toSpinC : SpinCStructure F E n :=
  s.extendSpinC (spinCGroup.ofSpin _ hQn) (spinCGroup.continuous_ofSpin _ hQn) comp_ofSpin

/-- The point `[p, 1]` of the principal bundle of `s.toSpinC` over the point `p` of `s`. -/
noncomputable def inlSpinC {x : X} (p : s.P x) : s.toSpinC.P x :=
  PrincipalBundle.Extend.inl (spinCGroup.ofSpin _ hQn) (spinCGroup.continuous_ofSpin _ hQn) p

/-- The map `p ↦ [p, 1]` from the total space of `P` to that of the principal bundle of
`s.toSpinC` is continuous. -/
theorem continuous_inlSpinC :
    Continuous fun p : TotalSpace (realCliffordSpinGroupZero n) s.P ↦
      TotalSpace.mk' (spinCGroup (realCliffordForm n 0) hQn) p.proj (s.inlSpinC p.snd) :=
  PrincipalBundle.Extend.continuous_inl s.P _ (spinCGroup.continuous_ofSpin _ hQn)

/-- **Compatibility with frames**: the frame of `[p, 1]` in the induced `Spinᶜ` structure is the
frame of `p`. -/
@[simp]
theorem toFrame_inlSpinC (x : X) (p : s.P x) :
    s.toSpinC.toFrame ⟨x, s.inlSpinC p⟩ = s.toFrame ⟨x, p⟩ :=
  OrthonormalFrameLift.toFrame_extendSpinC_inl s (spinCGroup.ofSpin _ hQn)
    (spinCGroup.continuous_ofSpin _ hQn) comp_ofSpin x p

/-- `[p • g, 1] = [p, 1] • [g, 1]` for `g ∈ Spin(n)`. -/
@[simp]
theorem inlSpinC_smul {x : X} (p : s.P x) (g : realCliffordSpinGroupZero n) :
    s.inlSpinC (op g • p) = op (spinCGroup.ofSpin _ hQn g) • s.inlSpinC p :=
  PrincipalBundle.Extend.inl_smul _ (spinCGroup.continuous_ofSpin _ hQn) p g

/-- The principal `Spinᶜ(n)`-division of `[p, 1]` and `[q, 1]` is the image of the principal
`Spin(n)`-division of `p` and `q`. -/
@[simp]
theorem division_inlSpinC {x : X} (p q : s.P x) :
    PrincipalBundle.division (spinCGroup (realCliffordForm n 0) hQn) (s.inlSpinC p)
        (s.inlSpinC q) =
      spinCGroup.ofSpin _ hQn (PrincipalBundle.division (realCliffordSpinGroupZero n) p q) :=
  PrincipalBundle.Extend.division_inl _ (spinCGroup.continuous_ofSpin _ hQn) p q

/-- The class `[[p, 1], 1]` in the determinant line of `s.toSpinC`. -/
noncomputable def determinantLineSection (x : X) : s.toSpinC.determinantLine x :=
  AssociatedBundle.mk _ (s.inlSpinC (Classical.arbitrary (s.P x)))
    (SpinCStructure.DeterminantModel.toComplex.symm 1)

/-- **The section of the determinant line does not depend on the point of `P`**: for every point
`p` of `P` over `x`, it is `[[p, 1], 1]`, since `Spin(n)` acts trivially on the determinant
model. -/
theorem determinantLineSection_eq {x : X} (p : s.P x) :
    s.determinantLineSection x =
      AssociatedBundle.mk _ (s.inlSpinC p) (SpinCStructure.DeterminantModel.toComplex.symm 1) := by
  rw [determinantLineSection,
    ← PrincipalBundle.smul_division (G := realCliffordSpinGroupZero n) p
      (Classical.arbitrary (s.P x)),
    inlSpinC_smul, AssociatedBundle.mk_smul]
  congr 1
  apply SpinCStructure.DeterminantModel.toComplex.injective
  rw [SpinCStructure.DeterminantModel.toComplex_smul, spinCGroup.det_ofSpin, Circle.coe_one,
    one_mul]

/-- The section of the determinant line vanishes nowhere. -/
theorem determinantLineSection_ne_zero (x : X) : s.determinantLineSection x ≠ 0 := by
  rw [determinantLineSection, ← AssociatedBundle.mk_zero (s.inlSpinC _), Ne,
    (AssociatedBundle.mk_bijective _).injective.eq_iff]
  exact SpinCStructure.DeterminantModel.toComplex.symm.map_ne_zero_iff.mpr one_ne_zero

/-- The identification of the fibre of the determinant line of `s.toSpinC` at `x` with `ℂ` given
by the canonical section: `c ↦ c • s.determinantLineSection x`
(`TauCeti.SpinStructure.determinantLineEquiv_apply`). -/
noncomputable def determinantLineEquiv (x : X) : ℂ ≃ₗ[ℂ] s.toSpinC.determinantLine x :=
  LinearEquiv.trans
    (LinearIsometryEquiv.toLinearEquiv (SpinCStructure.DeterminantModel.toComplex (n := n)).symm)
    (ContinuousLinearEquiv.toLinearEquiv
      (AssociatedBundle.mkContinuousLinearEquiv ℂ _ (s.inlSpinC (Classical.arbitrary (s.P x)))))

@[simp]
theorem determinantLineEquiv_apply (x : X) (c : ℂ) :
    s.determinantLineEquiv x c = c • s.determinantLineSection x := by
  rw [determinantLineSection, ← AssociatedBundle.mk_smul_scalar, ← map_smul, smul_eq_mul, mul_one]
  simp only [determinantLineEquiv, LinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.coe_toLinearEquiv,
    AssociatedBundle.mkContinuousLinearEquiv_apply]

/-- **The section of the determinant line is continuous.** -/
theorem continuous_determinantLineSection :
    Continuous fun x ↦ TotalSpace.mk' (SpinCStructure.DeterminantModel n) x
      (s.determinantLineSection x) := by
  -- Pulled back to the total space of `P`, the section is `p ↦ [[p, 1], 1]`.
  refine (FiberBundle.isQuotientMap_proj (F := realCliffordSpinGroupZero n)
    (E := s.P)).continuous_iff.2 ?_
  exact (s.continuous_inlSpinC.totalSpaceMk_associatedBundleMk continuous_const).congr
    fun ⟨x, p⟩ ↦ by rw [Function.comp_apply, determinantLineSection_eq s p]

end SpinStructure

end TauCeti
