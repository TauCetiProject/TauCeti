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
`[p, 1]` is the frame of `p` (`TauCeti.SpinStructure.toFrame_toSpinC_inl`).

The determinant character `[s, z] ↦ z²` is trivial on `Spin(n)`, so the determinant line of
`s.toSpinC` is trivial: the class `[[p, 1], 1]` does not depend on the point `p` of `P` over `x`
(`TauCeti.SpinStructure.determinantLineSection_eq`), so it is a nowhere vanishing section of the
determinant line (`TauCeti.SpinStructure.determinantLineSection_ne_zero`), and it is continuous
(`TauCeti.SpinStructure.continuous_determinantLineSection`). It identifies every fibre with `ℂ`
(`TauCeti.SpinStructure.determinantLineEquiv`). Hence a `Spinᶜ` structure coming from a Spin
structure has a trivial determinant line.

## Main definitions

* `TauCeti.SpinStructure.toSpinC`: the `Spinᶜ` structure induced by a Spin structure.
* `TauCeti.SpinStructure.determinantLineSection`: the section `x ↦ [[p, 1], 1]` of its determinant
  line.
* `TauCeti.SpinStructure.determinantLineEquiv`: the identification `ℂ ≃ L_x`, `c ↦ c [[p, 1], 1]`.

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

/-- The inclusion `Spin(n) → Spinᶜ(n)`, `s ↦ [s, 1]`, is continuous: it is the quotient map
`Spin(n) × U(1) → Spinᶜ(n)` after `s ↦ (s, 1)`. -/
private theorem continuous_ofSpin :
    Continuous (spinCGroup.ofSpin (realCliffordForm n 0) hQn) := by
  have h := (spinCGroup.isQuotientCoveringMap_mk (realCliffordForm n 0) hQn).continuous.comp
    (continuous_id.prodMk (continuous_const (y := (1 : Circle))))
  exact h.congr fun g ↦ (spinCGroup.ofSpin_apply _ hQn g).symm

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
(`TauCeti.SpinStructure.toFrame_toSpinC_inl`). -/
noncomputable def toSpinC : SpinCStructure F E n :=
  s.extendSpinC (spinCGroup.ofSpin _ hQn) continuous_ofSpin comp_ofSpin

/-- The point `[p, 1]` of the principal bundle of `s.toSpinC` over the point `p` of `s`. -/
noncomputable def inlSpinC {x : X} (p : s.P x) : s.toSpinC.P x :=
  PrincipalBundle.Extend.inl (spinCGroup.ofSpin _ hQn) continuous_ofSpin p

/-- **Compatibility with frames**: the frame of `[p, 1]` in the induced `Spinᶜ` structure is the
frame of `p`. -/
@[simp]
theorem toFrame_toSpinC_inl (x : X) (p : s.P x) :
    s.toSpinC.toFrame ⟨x, s.inlSpinC p⟩ = s.toFrame ⟨x, p⟩ :=
  OrthonormalFrameLift.toFrame_extendSpinC_inl s (spinCGroup.ofSpin _ hQn) continuous_ofSpin
    comp_ofSpin x p

/-- `[p • g, 1] = [p, 1] • [g, 1]` for `g ∈ Spin(n)`. -/
theorem inlSpinC_smul {x : X} (p : s.P x) (g : realCliffordSpinGroupZero n) :
    s.inlSpinC (op g • p) = op (spinCGroup.ofSpin _ hQn g) • s.inlSpinC p :=
  PrincipalBundle.Extend.inl_smul (spinCGroup.ofSpin _ hQn) continuous_ofSpin p g

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

/-- **The determinant line of `s.toSpinC` is trivial on every fibre**: `c ↦ c [[p, 1], 1]` is a
linear isomorphism `ℂ ≃ L_x`. -/
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

/-- **The section of the determinant line is continuous.** Near each point it is
`x ↦ [[p x, 1], 1]` for a continuous local section `p` of `P`. -/
theorem continuous_determinantLineSection :
    Continuous fun x ↦ TotalSpace.mk' (SpinCStructure.DeterminantModel n) x
      (s.determinantLineSection x) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  set e := trivializationAt (realCliffordSpinGroupZero n) s.P x₀
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  -- The local section `x ↦ e⁻¹ (x, 1)` of `P` is continuous on the base set of `e`.
  have hp : ContinuousOn (fun x ↦ TotalSpace.mk' (realCliffordSpinGroupZero n) x (e.symm x 1))
      e.baseSet :=
    e.continuousOn_symm.comp
      (continuous_id.prodMk
        (continuous_const (y := (1 : realCliffordSpinGroupZero n)))).continuousOn
      fun _ hx ↦ ⟨hx, Set.mem_univ _⟩
  have hq := (hp.totalSpaceMk_extendMk (f := id) (ρ := spinCGroup.ofSpin _ hQn) continuous_ofSpin
    (continuousOn_const (c := 1))).totalSpaceMk_associatedBundleMk
      (v := fun _ ↦ (SpinCStructure.DeterminantModel.toComplex (n := n)).symm (1 : ℂ))
      continuousOn_const
  refine ((hq x₀ hx₀).continuousAt (e.open_baseSet.mem_nhds hx₀)).congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hx₀] with x _
  rw [determinantLineSection_eq s (e.symm x 1), inlSpinC, PrincipalBundle.Extend.inl_def]
  rfl

end SpinStructure

end TauCeti
