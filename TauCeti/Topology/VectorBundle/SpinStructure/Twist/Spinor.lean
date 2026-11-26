/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SpinStructure.Spinor
public import TauCeti.Topology.VectorBundle.SpinStructure.Twist.Basic
public import TauCeti.Topology.VectorBundle.TensorProduct.Basic

/-!
# The determinant line and the half-spinors of a twisted `Spinᶜ` structure

Let `s` be a `Spinᶜ` structure with principal `Spinᶜ(n)`-bundle `P`, and let `Q` be a principal
`U(1)`-bundle over the same base, with Hermitian line `E = Q ×_{U(1)} ℂ`
(`TauCeti.AssociatedBundle Circle Q ℂ`, on which `U(1)` acts on `ℂ` by multiplication). The twist
`s.twist Q` (`TauCeti.SpinCStructure.twist`) has principal bundle `(P ×_X Q) ×_μ Spinᶜ(n)`, where
`μ ([g, z], w) = [g, z w]` multiplies by the central circle. This file identifies the bundles
associated to the twist with those of `s` tensored with powers of `E`:

`L(s.twist Q) ≃ L(s) ⊗ (E ⊗ E)`,  `W^ε(s.twist Q) ≃ W^ε(s) ⊗ E`

(`TauCeti.SpinCStructure.determinantLineTwistEquiv`,
`TauCeti.SpinCStructure.halfSpinorBundleTwistEquiv`), as fibrewise continuous linear equivalences
whose forward maps are continuous on total spaces. So twisting by a line `E` multiplies the
determinant line by `E²` and each half-spinor bundle by `E`.

In frames, the comparisons read

`[[(p, q), h], w] ↦ [p, h w] ⊗ ([q, 1] ⊗ [q, 1])`,  `[[(p, q), h], ψ] ↦ [p, h ψ] ⊗ [q, 1]`

(`TauCeti.SpinCStructure.determinantLineTwistEquiv_mk`,
`TauCeti.SpinCStructure.halfSpinorBundleTwistEquiv_mk`). They are well defined because the central
circle acts with weight two on the determinant model and with weight one on the half-spinors
(`TauCeti.SpinCStructure.DeterminantModel.ofCircle_smul`,
`Orientation.HalfSpinModel.ofCircle_smul`): for `(p, q) = (p₀ g, q₀ u)` the point
`[[(p, q), h], w]` is `[[(p₀, q₀), 1], g [1, u] h w]`, and `[1, u]` acts on the determinant model by
`u²`, the factor relating `[q₀ u, 1] ⊗ [q₀ u, 1] = u² ([q₀, 1] ⊗ [q₀, 1])`, and on the half-spinors
by `u`, the factor relating `[q₀ u, 1] = u [q₀, 1]`.

The tensor product fibres carry the `ℂ`-module topology (`TauCeti.ModuleTopology`), for which
they form the tensor product vector bundles of `TauCeti.Topology.VectorBundle.TensorProduct.Basic`.

## Main definitions

* `TauCeti.SpinCStructure.determinantLineTwistEquiv`: `L(s.twist Q)_x ≃ L(s)_x ⊗ (E_x ⊗ E_x)`.
* `TauCeti.SpinCStructure.halfSpinorBundleTwistEquiv`: `W^ε(s.twist Q)_x ≃ W^ε(s)_x ⊗ E_x`, in
  rank four.

## Main results

* `TauCeti.SpinCStructure.twist_associatedBundleMk_op_smul`: in any bundle associated to the
  twist, `[[(p₀ g, q₀ u), h], w] = [[(p₀, q₀), 1], (g [1, u] h) w]`.
* `TauCeti.SpinCStructure.continuous_twist_associatedBundle_iff`: a map out of a bundle associated
  to the twist with fibre `M` is continuous when it is continuous on
  `((P ×_X Q) × Spinᶜ(n)) × M`.
* `TauCeti.SpinCStructure.continuous_twist_associatedBundleMk_fst_smul`,
  `TauCeti.SpinCStructure.continuous_twist_associatedBundleMk_snd_one`: on
  `((P ×_X Q) × Spinᶜ(n)) × M`, the classes `[p, h w]` and `[q, 1]` form continuous families.
* `TauCeti.SpinCStructure.determinantLineTwistEquiv_mk`,
  `TauCeti.SpinCStructure.halfSpinorBundleTwistEquiv_mk`: the formulas in frames, and
  `TauCeti.SpinCStructure.determinantLineTwistEquiv_symm_tmul`,
  `TauCeti.SpinCStructure.halfSpinorBundleTwistEquiv_symm_tmul` for their inverses.
* `TauCeti.SpinCStructure.continuous_determinantLineTwistEquiv`,
  `TauCeti.SpinCStructure.continuous_halfSpinorBundleTwistEquiv`: the forward comparisons are
  continuous on total spaces.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
* C. Okonek and A. Teleman, *Seiberg–Witten invariants for manifolds with `b₊ = 1`, and the
  universal wall crossing formula*, Internat. J. Math. 7 (1996), 811–832, pp. 3–4 of
  arXiv:alg-geom/9603003 (the spinor bundles and the determinant line of a `Spinᶜ` structure).
-/

public section

noncomputable section

open Bundle MulOpposite CliffordAlgebra TauCeti.PrincipalBundle
open scoped TensorProduct TauCeti.ModuleTopology

namespace TauCeti

namespace SpinCStructure

variable {X : Type*} [TopologicalSpace X] {F : Type*} {V : X → Type}
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V]
  [VectorBundle ℝ F V]
  (Q : X → Type) [TopologicalSpace (TotalSpace Circle Q)] [∀ x, TopologicalSpace (Q x)]
  [FiberBundle Circle Q] [∀ x, MulAction Circleᵐᵒᵖ (Q x)] [PrincipalBundle Circle Q]

section Rank

variable {n : ℕ} [NeZero n]

/-- The proof that the standard form on `ℝⁿ`, `n ≥ 1`, is nonzero, on which `Spinᶜ(n)` depends. -/
local notation "hQ" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)
local notation "SpinC" => spinCGroup (realCliffordForm n 0) hQ
/-- Multiplication by the central circle, along which the twist extends the fibre product. -/
local notation "μ" => spinCGroup.mulCircle (realCliffordForm n 0) hQ
local notation "hμ" => spinCGroup.continuous_mulCircle (realCliffordForm n 0) hQ

/-! ### Bundles associated to the twist -/

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V] [VectorBundle ℝ F V] in
/-- **Changing frames in a bundle associated to the twist**: for `(p, q) = (p₀ g, q₀ u)`,
`[[(p, q), h], w] = [[(p₀, q₀), 1], (g [1, u] h) w]`. -/
theorem twist_associatedBundleMk_op_smul {M : Type*} [TopologicalSpace M] [MulAction SpinC M]
    [ContinuousSMul SpinC M] (s : SpinCStructure F V n) {x : X} (p₀ : s.P x) (q₀ : Q x)
    (g : SpinC) (u : Circle) (h : SpinC) (w : M) :
    AssociatedBundle.mk (P := Extend (FiberProd s.P Q) μ hμ) SpinC
        (Extend.mk μ hμ (FiberProd.mk (op g • p₀) (op u • q₀)) h) w =
      AssociatedBundle.mk SpinC (Extend.inl μ hμ (FiberProd.mk p₀ q₀)) ((μ (g, u) * h) • w) := by
  rw [← FiberProd.op_smul_mk, Extend.mk_smul, ← Extend.smul_inl, AssociatedBundle.mk_smul]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V] [VectorBundle ℝ F V] in
/-- **Continuity out of a bundle associated to the twist**: its total space is an open quotient of
`((P ×_X Q) × Spinᶜ(n)) × M` by `(((p, q), h), w) ↦ [[(p, q), h], w]`, so a map out of it is
continuous exactly when its composite with this quotient map is. -/
theorem continuous_twist_associatedBundle_iff {M : Type*} [TopologicalSpace M]
    [MulAction SpinC M] [ContinuousSMul SpinC M] (s : SpinCStructure F V n) {Y : Type*}
    [TopologicalSpace Y]
    {f : TotalSpace M (AssociatedBundle SpinC (Extend (FiberProd s.P Q) μ hμ) M) → Y} :
    Continuous f ↔
      Continuous fun y : (TotalSpace (SpinC × Circle) (FiberProd s.P Q) × SpinC) × M ↦
        f ⟨y.1.1.proj, AssociatedBundle.mk SpinC (Extend.mk μ hμ y.1.1.snd y.1.2) y.2⟩ :=
  ((AssociatedBundle.isOpenQuotientMap_totalSpaceMk_mk SpinC
    (Extend (FiberProd s.P Q) μ hμ) M).comp
      ((Extend.isOpenQuotientMap_totalSpaceMk_mk (FiberProd s.P Q) μ hμ).prodMap
        IsOpenQuotientMap.id)).continuous_comp_iff.symm

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, TopologicalSpace (Q x)] [FiberBundle Circle Q] [∀ x, MulAction Circleᵐᵒᵖ (Q x)]
  [PrincipalBundle Circle Q] in
/-- On `((P ×_X Q) × Spinᶜ(n)) × M`, the classes `[p, h w]` in the bundle associated to `P` with
fibre `M` form a continuous family. -/
theorem continuous_twist_associatedBundleMk_fst_smul {M : Type*} [TopologicalSpace M]
    [MulAction SpinC M] [ContinuousSMul SpinC M] (s : SpinCStructure F V n) :
    Continuous fun y : (TotalSpace (SpinC × Circle) (FiberProd s.P Q) × SpinC) × M ↦
      TotalSpace.mk' M (E := AssociatedBundle SpinC s.P M) y.1.1.proj
        (AssociatedBundle.mk SpinC y.1.1.snd.fst (y.1.2 • y.2)) :=
  (FiberProd.continuous_totalSpaceMk_fst.comp (continuous_fst.comp continuous_fst))
    |>.totalSpaceMk_associatedBundleMk ((continuous_snd.comp continuous_fst).smul continuous_snd)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V] [VectorBundle ℝ F V] in
/-- On `((P ×_X Q) × Spinᶜ(n)) × M`, the classes `[q, 1]` in the Hermitian line
`E = Q ×_{U(1)} ℂ` form a continuous family. -/
theorem continuous_twist_associatedBundleMk_snd_one {M : Type*} [TopologicalSpace M]
    (s : SpinCStructure F V n) :
    Continuous fun y : (TotalSpace (SpinC × Circle) (FiberProd s.P Q) × SpinC) × M ↦
      TotalSpace.mk' ℂ (E := AssociatedBundle Circle Q ℂ) y.1.1.proj
        (AssociatedBundle.mk Circle y.1.1.snd.snd (1 : ℂ)) :=
  (FiberProd.continuous_totalSpaceMk_snd.comp (continuous_fst.comp continuous_fst))
    |>.totalSpaceMk_associatedBundleMk continuous_const

/-! ### The determinant line -/

section DeterminantLine

/-- The comparison of determinant lines read in the frames `[(p₀, q₀), 1]`, `p₀` and `q₀`:
`[[(p₀, q₀), 1], w] ↦ [p₀, w] ⊗ ([q₀, 1] ⊗ [q₀, 1])`. -/
private def determinantLineTwistLinearEquiv (s : SpinCStructure F V n) {x : X} (p₀ : s.P x)
    (q₀ : Q x) :
    (s.twist Q).determinantLine x ≃ₗ[ℂ]
      s.determinantLine x ⊗[ℂ]
        (AssociatedBundle Circle Q ℂ x ⊗[ℂ] AssociatedBundle Circle Q ℂ x) :=
  (AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC (F := DeterminantModel n)
      (P := Extend (FiberProd s.P Q) μ hμ)
      (Extend.inl μ hμ (FiberProd.mk p₀ q₀))).symm.toLinearEquiv ≪≫ₗ
    (TensorProduct.rid ℂ (DeterminantModel n)).symm ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl ℂ _) (TensorProduct.lid ℂ ℂ).symm ≪≫ₗ
    TensorProduct.congr (AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC p₀).toLinearEquiv
      (TensorProduct.congr (AssociatedBundle.mkContinuousLinearEquiv ℂ Circle q₀).toLinearEquiv
        (AssociatedBundle.mkContinuousLinearEquiv ℂ Circle q₀).toLinearEquiv)

/-- The comparison of determinant lines in its reference frames, as a composite, stated on the
fibre `Extend (P ×_X Q)` of the twist. -/
private theorem determinantLineTwistLinearEquiv_apply (s : SpinCStructure F V n) {x : X}
    (p₀ : s.P x) (q₀ : Q x)
    (z : AssociatedBundle SpinC (Extend (FiberProd s.P Q) μ hμ) (DeterminantModel n) x) :
    determinantLineTwistLinearEquiv Q s p₀ q₀ z =
      TensorProduct.congr (AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC p₀).toLinearEquiv
        (TensorProduct.congr (AssociatedBundle.mkContinuousLinearEquiv ℂ Circle q₀).toLinearEquiv
          (AssociatedBundle.mkContinuousLinearEquiv ℂ Circle q₀).toLinearEquiv)
        (TensorProduct.congr (LinearEquiv.refl ℂ _) (TensorProduct.lid ℂ ℂ).symm
          ((TensorProduct.rid ℂ (DeterminantModel n)).symm
            ((AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC
              (Extend.inl μ hμ (FiberProd.mk p₀ q₀))).symm z))) :=
  (rfl)

/-- The comparison of determinant lines in every frame, whatever its reference frames:
`[[(p, q), h], w] ↦ [p, h w] ⊗ ([q, 1] ⊗ [q, 1])`. -/
private theorem determinantLineTwistLinearEquiv_mk (s : SpinCStructure F V n) {x : X}
    (p₀ p : s.P x) (q₀ q : Q x) (h : SpinC) (w : DeterminantModel n) :
    determinantLineTwistLinearEquiv Q s p₀ q₀
        (AssociatedBundle.mk (P := Extend (FiberProd s.P Q) μ hμ) SpinC
          (Extend.mk μ hμ (FiberProd.mk p q) h) w) =
      AssociatedBundle.mk SpinC p (h • w) ⊗ₜ[ℂ]
        (AssociatedBundle.mk Circle q (1 : ℂ) ⊗ₜ[ℂ] AssociatedBundle.mk Circle q (1 : ℂ)) := by
  -- Write `(p, q) = (p₀, q₀) • (g, u)`; then `[[(p, q), h], w] = [[(p₀, q₀), 1], g [1, u] h w]`.
  obtain ⟨g, rfl⟩ : ∃ g, op g • p₀ = p := ⟨_, smul_division (G := SpinC) p₀ p⟩
  obtain ⟨u, rfl⟩ : ∃ u, op u • q₀ = q := ⟨_, smul_division (G := Circle) q₀ q⟩
  rw [twist_associatedBundleMk_op_smul (M := DeterminantModel n) Q s,
    determinantLineTwistLinearEquiv_apply,
    AssociatedBundle.mkContinuousLinearEquiv_symm_apply_mk, division_self, one_smul]
  -- `[1, u]` acts on the determinant model by `u²`, and `[q₀ u, 1] = [q₀, u] = u [q₀, 1]`.
  simp [AssociatedBundle.mk_smul, Circle.smul_def, mul_smul, DeterminantModel.ofCircle_smul,
    smul_comm g, AssociatedBundle.mk_eq_smul_mk_one q₀ (u : ℂ), TensorProduct.tmul_smul,
    ← TensorProduct.smul_tmul', sq]

/-- **The determinant line of a twisted `Spinᶜ` structure**: twisting `s` by a principal
`U(1)`-bundle `Q` with Hermitian line `E = Q ×_{U(1)} ℂ` tensors its determinant line with `E²`,

`L(s.twist Q)_x ≃ L(s)_x ⊗ (E_x ⊗ E_x)`,  `[[(p, q), h], w] ↦ [p, h w] ⊗ ([q, 1] ⊗ [q, 1])`

(`TauCeti.SpinCStructure.determinantLineTwistEquiv_mk`). Its forward map is continuous on total
spaces (`TauCeti.SpinCStructure.continuous_determinantLineTwistEquiv`). -/
def determinantLineTwistEquiv (s : SpinCStructure F V n) (x : X) :
    (s.twist Q).determinantLine x ≃L[ℂ]
      s.determinantLine x ⊗[ℂ]
        (AssociatedBundle Circle Q ℂ x ⊗[ℂ] AssociatedBundle Circle Q ℂ x) :=
  (determinantLineTwistLinearEquiv Q s ((FiberBundle.homeomorphAt SpinC s.P x).symm 1)
    ((FiberBundle.homeomorphAt Circle Q x).symm 1)).toContinuousLinearEquivOfIsModuleTopology

/-- **The comparison of determinant lines in a frame**:
`[[(p, q), h], w] ↦ [p, h w] ⊗ ([q, 1] ⊗ [q, 1])`. -/
@[simp]
theorem determinantLineTwistEquiv_mk (s : SpinCStructure F V n) {x : X} (p : s.P x) (q : Q x)
    (h : SpinC) (w : DeterminantModel n) :
    s.determinantLineTwistEquiv Q x
        (AssociatedBundle.mk (P := Extend (FiberProd s.P Q) μ hμ) SpinC
          (Extend.mk μ hμ (FiberProd.mk p q) h) w) =
      AssociatedBundle.mk SpinC p (h • w) ⊗ₜ[ℂ]
        (AssociatedBundle.mk Circle q (1 : ℂ) ⊗ₜ[ℂ] AssociatedBundle.mk Circle q (1 : ℂ)) :=
  (congrFun (LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology _) _).trans
    (determinantLineTwistLinearEquiv_mk Q s _ p _ q h w)

/-- **The comparison of determinant lines at `[(p, q), 1]`**:
`[[(p, q), 1], w] ↦ [p, w] ⊗ ([q, 1] ⊗ [q, 1])`. -/
@[simp]
theorem determinantLineTwistEquiv_inl (s : SpinCStructure F V n) {x : X} (p : s.P x) (q : Q x)
    (w : DeterminantModel n) :
    s.determinantLineTwistEquiv Q x
        (AssociatedBundle.mk (P := Extend (FiberProd s.P Q) μ hμ) SpinC
          (Extend.inl μ hμ (FiberProd.mk p q)) w) =
      AssociatedBundle.mk SpinC p w ⊗ₜ[ℂ]
        (AssociatedBundle.mk Circle q (1 : ℂ) ⊗ₜ[ℂ] AssociatedBundle.mk Circle q (1 : ℂ)) := by
  rw [Extend.inl_def, determinantLineTwistEquiv_mk, one_smul]

/-- **The inverse comparison of determinant lines on pure tensors**:
`[p, w] ⊗ ([q, a] ⊗ [q, c]) ↦ [[(p, q), 1], a c w]`. -/
@[simp]
theorem determinantLineTwistEquiv_symm_tmul (s : SpinCStructure F V n) {x : X} (p : s.P x)
    (q : Q x) (w : DeterminantModel n) (a c : ℂ) :
    (s.determinantLineTwistEquiv Q x).symm
        (AssociatedBundle.mk SpinC p w ⊗ₜ[ℂ]
          (AssociatedBundle.mk Circle q a ⊗ₜ[ℂ] AssociatedBundle.mk Circle q c)) =
      AssociatedBundle.mk (P := Extend (FiberProd s.P Q) μ hμ) SpinC
        (Extend.inl μ hμ (FiberProd.mk p q)) ((a * c) • w) := by
  refine (ContinuousLinearEquiv.symm_apply_eq _).2
    ((?_ : _ = _).trans (determinantLineTwistEquiv_inl Q s p q _).symm)
  -- `[q, a] = a [q, 1]` and `[q, c] = c [q, 1]`.
  rw [AssociatedBundle.mk_eq_smul_mk_one q a, AssociatedBundle.mk_eq_smul_mk_one q c]
  simp only [AssociatedBundle.mk_smul_scalar, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul',
    smul_smul, mul_comm c a]

/-- **The comparison of determinant lines is continuous** on total spaces. -/
theorem continuous_determinantLineTwistEquiv (s : SpinCStructure F V n) :
    Continuous fun v : TotalSpace (DeterminantModel n) (s.twist Q).determinantLine ↦
      TotalSpace.mk' (ProjectiveTensor ℂ (DeterminantModel n) (ProjectiveTensor ℂ ℂ ℂ))
        (E := fun x ↦ s.determinantLine x ⊗[ℂ]
          (AssociatedBundle Circle Q ℂ x ⊗[ℂ] AssociatedBundle Circle Q ℂ x))
        v.proj (s.determinantLineTwistEquiv Q v.proj v.snd) := by
  -- On `((P ×_X Q) × Spinᶜ(n)) × Λ`, `Λ = DeterminantModel n`, the comparison is
  -- `(((p, q), h), w) ↦ [p, h w] ⊗ ([q, 1] ⊗ [q, 1])`.
  refine (continuous_twist_associatedBundle_iff Q s).2 ?_
  have hc : Continuous fun y : (TotalSpace (SpinC × Circle) (FiberProd s.P Q) × SpinC) ×
      DeterminantModel n ↦
      TotalSpace.mk' (ProjectiveTensor ℂ (DeterminantModel n) (ProjectiveTensor ℂ ℂ ℂ))
        (E := fun x ↦ s.determinantLine x ⊗[ℂ]
          (AssociatedBundle Circle Q ℂ x ⊗[ℂ] AssociatedBundle Circle Q ℂ x)) y.1.1.proj
        (AssociatedBundle.mk SpinC y.1.1.snd.fst (y.1.2 • y.2) ⊗ₜ[ℂ]
          (AssociatedBundle.mk Circle y.1.1.snd.snd (1 : ℂ) ⊗ₜ[ℂ]
            AssociatedBundle.mk Circle y.1.1.snd.snd (1 : ℂ))) :=
    (continuous_twist_associatedBundleMk_fst_smul Q s).tmul_section
      ((continuous_twist_associatedBundleMk_snd_one Q s).tmul_section
        (continuous_twist_associatedBundleMk_snd_one Q s))
  exact hc.congr fun _ ↦ congrArg (TotalSpace.mk _) (determinantLineTwistEquiv_mk ..).symm

end DeterminantLine

end Rank

/-! ### The half-spinor bundles -/

section HalfSpinor

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fact (Module.finrank ℝ U = 4)] {qf : QuadraticForm ℝ U}
  (o : Orientation ℝ U (Fin 4)) (hqf : ∀ v, qf v = -‖v‖ ^ 2)
  (b : OrthonormalBasis (Fin 4) ℝ U)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra qf →ₐ[ℝ] Module.End ℂ W)
  (hρ : ∀ v, LinearMap.adjoint (ρ (ι qf v)) = -ρ (ι qf v)) (ε : ℂ)

/-- The proof that the standard form on `ℝ⁴` is nonzero, on which `Spinᶜ(4)` depends. -/
local notation "hpos" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm 4 0)
local notation "SpinC₄" => spinCGroup (realCliffordForm 4 0) hpos
/-- Multiplication by the central circle of `Spinᶜ(4)`. -/
local notation "μ₄" => spinCGroup.mulCircle (realCliffordForm 4 0) hpos
local notation "hμ₄" => spinCGroup.continuous_mulCircle (realCliffordForm 4 0) hpos

/-- The comparison of half-spinor bundles read in the frames `[(p₀, q₀), 1]`, `p₀` and `q₀`:
`[[(p₀, q₀), 1], ψ] ↦ [p₀, ψ] ⊗ [q₀, 1]`. -/
private def halfSpinorBundleTwistLinearEquiv (s : SpinCStructure F V 4) {x : X} (p₀ : s.P x)
    (q₀ : Q x) :
    (s.twist Q).halfSpinorBundle o hqf b ρ hρ ε x ≃ₗ[ℂ]
      s.halfSpinorBundle o hqf b ρ hρ ε x ⊗[ℂ] AssociatedBundle Circle Q ℂ x :=
  (AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC₄ (F := o.HalfSpinModel hqf b ρ hρ ε)
      (P := Extend (FiberProd s.P Q) μ₄ hμ₄)
      (Extend.inl μ₄ hμ₄ (FiberProd.mk p₀ q₀))).symm.toLinearEquiv ≪≫ₗ
    (TensorProduct.rid ℂ (o.HalfSpinModel hqf b ρ hρ ε)).symm ≪≫ₗ
    TensorProduct.congr (AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC₄ p₀).toLinearEquiv
      (AssociatedBundle.mkContinuousLinearEquiv ℂ Circle q₀).toLinearEquiv

/-- The comparison of half-spinor bundles in its reference frames, as a composite, stated on the
fibre `Extend (P ×_X Q)` of the twist. -/
private theorem halfSpinorBundleTwistLinearEquiv_apply (s : SpinCStructure F V 4) {x : X}
    (p₀ : s.P x) (q₀ : Q x)
    (z : AssociatedBundle SpinC₄ (Extend (FiberProd s.P Q) μ₄ hμ₄)
      (o.HalfSpinModel hqf b ρ hρ ε) x) :
    halfSpinorBundleTwistLinearEquiv Q o hqf b ρ hρ ε s p₀ q₀ z =
      TensorProduct.congr (AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC₄ p₀).toLinearEquiv
        (AssociatedBundle.mkContinuousLinearEquiv ℂ Circle q₀).toLinearEquiv
        ((TensorProduct.rid ℂ (o.HalfSpinModel hqf b ρ hρ ε)).symm
          ((AssociatedBundle.mkContinuousLinearEquiv ℂ SpinC₄
            (Extend.inl μ₄ hμ₄ (FiberProd.mk p₀ q₀))).symm z)) :=
  (rfl)

/-- The comparison of half-spinor bundles in every frame, whatever its reference frames:
`[[(p, q), h], ψ] ↦ [p, h ψ] ⊗ [q, 1]`. -/
private theorem halfSpinorBundleTwistLinearEquiv_mk (s : SpinCStructure F V 4) {x : X}
    (p₀ p : s.P x) (q₀ q : Q x) (h : SpinC₄) (ψ : o.HalfSpinModel hqf b ρ hρ ε) :
    halfSpinorBundleTwistLinearEquiv Q o hqf b ρ hρ ε s p₀ q₀
        (AssociatedBundle.mk (P := Extend (FiberProd s.P Q) μ₄ hμ₄) SpinC₄
          (Extend.mk μ₄ hμ₄ (FiberProd.mk p q) h) ψ) =
      AssociatedBundle.mk SpinC₄ p (h • ψ) ⊗ₜ[ℂ] AssociatedBundle.mk Circle q (1 : ℂ) := by
  -- Write `(p, q) = (p₀, q₀) • (g, u)`; then `[[(p, q), h], ψ] = [[(p₀, q₀), 1], g [1, u] h ψ]`.
  obtain ⟨g, rfl⟩ : ∃ g, op g • p₀ = p := ⟨_, smul_division (G := SpinC₄) p₀ p⟩
  obtain ⟨u, rfl⟩ : ∃ u, op u • q₀ = q := ⟨_, smul_division (G := Circle) q₀ q⟩
  rw [twist_associatedBundleMk_op_smul, halfSpinorBundleTwistLinearEquiv_apply,
    AssociatedBundle.mkContinuousLinearEquiv_symm_apply_mk, division_self, one_smul]
  -- `[1, u]` acts on the half-spinors by `u`, and `[q₀ u, 1] = u [q₀, 1]`.
  simp [AssociatedBundle.mk_smul, Circle.smul_def, mul_smul,
    Orientation.HalfSpinModel.ofCircle_smul, smul_comm g, ← TensorProduct.tmul_smul]

/-- **The half-spinor bundles of a twisted `Spinᶜ` structure**: twisting a `Spinᶜ` structure `s`
of rank four by a principal `U(1)`-bundle `Q` with Hermitian line `E = Q ×_{U(1)} ℂ` tensors each
half-spinor bundle with `E`,

`W^ε(s.twist Q)_x ≃ W^ε(s)_x ⊗ E_x`,  `[[(p, q), h], ψ] ↦ [p, h ψ] ⊗ [q, 1]`

(`TauCeti.SpinCStructure.halfSpinorBundleTwistEquiv_mk`). Its forward map is continuous on total
spaces (`TauCeti.SpinCStructure.continuous_halfSpinorBundleTwistEquiv`). -/
def halfSpinorBundleTwistEquiv (s : SpinCStructure F V 4) (x : X) :
    (s.twist Q).halfSpinorBundle o hqf b ρ hρ ε x ≃L[ℂ]
      s.halfSpinorBundle o hqf b ρ hρ ε x ⊗[ℂ] AssociatedBundle Circle Q ℂ x :=
  (halfSpinorBundleTwistLinearEquiv Q o hqf b ρ hρ ε s
    ((FiberBundle.homeomorphAt SpinC₄ s.P x).symm 1)
    ((FiberBundle.homeomorphAt Circle Q x).symm 1)).toContinuousLinearEquivOfIsModuleTopology

/-- **The comparison of half-spinor bundles in a frame**:
`[[(p, q), h], ψ] ↦ [p, h ψ] ⊗ [q, 1]`. -/
@[simp]
theorem halfSpinorBundleTwistEquiv_mk (s : SpinCStructure F V 4) {x : X} (p : s.P x) (q : Q x)
    (h : SpinC₄) (ψ : o.HalfSpinModel hqf b ρ hρ ε) :
    s.halfSpinorBundleTwistEquiv Q o hqf b ρ hρ ε x
        (AssociatedBundle.mk (P := Extend (FiberProd s.P Q) μ₄ hμ₄) SpinC₄
          (Extend.mk μ₄ hμ₄ (FiberProd.mk p q) h) ψ) =
      AssociatedBundle.mk SpinC₄ p (h • ψ) ⊗ₜ[ℂ] AssociatedBundle.mk Circle q (1 : ℂ) :=
  (congrFun (LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology _) _).trans
    (halfSpinorBundleTwistLinearEquiv_mk Q o hqf b ρ hρ ε s _ p _ q h ψ)

/-- **The comparison of half-spinor bundles at `[(p, q), 1]`**:
`[[(p, q), 1], ψ] ↦ [p, ψ] ⊗ [q, 1]`. -/
@[simp]
theorem halfSpinorBundleTwistEquiv_inl (s : SpinCStructure F V 4) {x : X} (p : s.P x) (q : Q x)
    (ψ : o.HalfSpinModel hqf b ρ hρ ε) :
    s.halfSpinorBundleTwistEquiv Q o hqf b ρ hρ ε x
        (AssociatedBundle.mk (P := Extend (FiberProd s.P Q) μ₄ hμ₄) SpinC₄
          (Extend.inl μ₄ hμ₄ (FiberProd.mk p q)) ψ) =
      AssociatedBundle.mk SpinC₄ p ψ ⊗ₜ[ℂ] AssociatedBundle.mk Circle q (1 : ℂ) := by
  rw [Extend.inl_def, halfSpinorBundleTwistEquiv_mk, one_smul]

/-- **The inverse comparison of half-spinor bundles on pure tensors**:
`[p, ψ] ⊗ [q, a] ↦ [[(p, q), 1], a ψ]`. -/
@[simp]
theorem halfSpinorBundleTwistEquiv_symm_tmul (s : SpinCStructure F V 4) {x : X} (p : s.P x)
    (q : Q x) (ψ : o.HalfSpinModel hqf b ρ hρ ε) (a : ℂ) :
    (s.halfSpinorBundleTwistEquiv Q o hqf b ρ hρ ε x).symm
        (AssociatedBundle.mk SpinC₄ p ψ ⊗ₜ[ℂ] AssociatedBundle.mk Circle q a) =
      AssociatedBundle.mk (P := Extend (FiberProd s.P Q) μ₄ hμ₄) SpinC₄
        (Extend.inl μ₄ hμ₄ (FiberProd.mk p q)) (a • ψ) := by
  refine (ContinuousLinearEquiv.symm_apply_eq _).2
    ((?_ : _ = _).trans (halfSpinorBundleTwistEquiv_inl Q o hqf b ρ hρ ε s p q _).symm)
  -- `[q, a] = a [q, 1]`.
  rw [AssociatedBundle.mk_smul_scalar, TensorProduct.smul_tmul,
    ← AssociatedBundle.mk_eq_smul_mk_one]

/-- **The comparison of half-spinor bundles is continuous** on total spaces. -/
theorem continuous_halfSpinorBundleTwistEquiv (s : SpinCStructure F V 4) :
    Continuous fun v : TotalSpace (o.HalfSpinModel hqf b ρ hρ ε)
        ((s.twist Q).halfSpinorBundle o hqf b ρ hρ ε) ↦
      TotalSpace.mk' (ProjectiveTensor ℂ (o.HalfSpinModel hqf b ρ hρ ε) ℂ)
        (E := fun x ↦ s.halfSpinorBundle o hqf b ρ hρ ε x ⊗[ℂ] AssociatedBundle Circle Q ℂ x)
        v.proj (s.halfSpinorBundleTwistEquiv Q o hqf b ρ hρ ε v.proj v.snd) := by
  -- On `((P ×_X Q) × Spinᶜ(4)) × S^ε`, the comparison is `(((p, q), h), ψ) ↦ [p, h ψ] ⊗ [q, 1]`.
  refine (continuous_twist_associatedBundle_iff Q s).2 ?_
  have hc : Continuous fun y : (TotalSpace (SpinC₄ × Circle) (FiberProd s.P Q) × SpinC₄) ×
      o.HalfSpinModel hqf b ρ hρ ε ↦
      TotalSpace.mk' (ProjectiveTensor ℂ (o.HalfSpinModel hqf b ρ hρ ε) ℂ)
        (E := fun x ↦ s.halfSpinorBundle o hqf b ρ hρ ε x ⊗[ℂ] AssociatedBundle Circle Q ℂ x)
        y.1.1.proj
        (AssociatedBundle.mk SpinC₄ y.1.1.snd.fst (y.1.2 • y.2) ⊗ₜ[ℂ]
          AssociatedBundle.mk Circle y.1.1.snd.snd (1 : ℂ)) :=
    (continuous_twist_associatedBundleMk_fst_smul Q s).tmul_section
      (continuous_twist_associatedBundleMk_snd_one Q s)
  exact hc.congr fun _ ↦ congrArg (TotalSpace.mk _) (halfSpinorBundleTwistEquiv_mk ..).symm

end HalfSpinor

end SpinCStructure

end TauCeti
