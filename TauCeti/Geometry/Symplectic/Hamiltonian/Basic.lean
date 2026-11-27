/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Duality
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.FDeriv.Basic
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Geometry.Symplectic.CompatibleMetric

/-!
# Hamiltonian vector fields on symplectic vector spaces

For a constant symplectic form on a finite-dimensional real normed space, the Hamiltonian
vector field of `H` is obtained by inverting contraction with the symplectic form.
Our sign convention is `ω (X_H x) v = dH(x) v`. For `ω = dq ∧ dp`, this gives the
Hamilton equations `q' = ∂H/∂p`, `p' = -∂H/∂q`.

The characteristic contraction equation determines the field uniquely, and the field vanishes
off the topological support of `H`
(`TauCeti.SymplecticForm.hamiltonianVectorField_eq_zero_of_notMem_tsupport`). Since `dH(X_H) = 0`, a
differentiable Hamiltonian is constant along every integral curve of `X_H`
(`TauCeti.SymplecticForm.apply_eq_of_hasDerivWithinAt_hamiltonianVectorField`), and so is every
differentiable function Poisson-commuting with it
(`TauCeti.SymplecticForm.apply_eq_of_hasDerivWithinAt_of_poissonBracket_eq_zero`). The
linearization of `X_H` is infinitesimally symplectic when `H` is twice continuously
differentiable; this is the identity used to show that Hamiltonian flows preserve the symplectic
form. Contracting the linearization with `ω` gives the Hessian, so `dX_H(x)` has the kernel of
the Hessian (`TauCeti.SymplecticForm.fderiv_hamiltonianVectorField_apply_eq_zero_iff`).
A Lipschitz bound `‖X_G(z) - X_G(y₀)‖ ≤ L ‖z - y₀‖` on a ball gives the second-order Taylor bound
`|G(y) - G(y₀) - dG(y₀)(y - y₀)| ≤ ‖ω‖ L ‖y - y₀‖²` there
(`TauCeti.SymplecticForm.abs_sub_sub_fderiv_le_of_norm_hamiltonianVectorField_sub_le`).
A compactly supported `C²` Hamiltonian has a globally Lipschitz Hamiltonian vector field
(`TauCeti.SymplecticForm.exists_lipschitzWith_hamiltonianVectorField`), so its flow is defined
for all times. For a compactly supported `C³` Hamiltonian the first two derivatives of the
Hamiltonian vector field are bounded
(`TauCeti.SymplecticForm.exists_forall_norm_fderiv_hamiltonianVectorField_le`).

For an almost complex structure `J` preserving `ω`, the field `J X_H` is the gradient of `H` for
the bilinear form `g = ω(·, J ·)`
(`TauCeti.SymplecticForm.Invariant.associatedBilinForm_hamiltonianVectorField`). When `g` is the
inner product of `V`, this says `J X_H = ∇H`
(`TauCeti.SymplecticForm.apply_hamiltonianVectorField_eq_gradient`). For the opposite bilinear
form `ω(·, -J ·)`, the gradient of `H` is `-J X_H`, with no invariance needed
(`TauCeti.SymplecticForm.associatedBilinForm_neg_apply_neg_hamiltonianVectorField`). The
Hamiltonian vector field of `(c / 2) ‖y‖²` is the linear field `-c J`
(`TauCeti.SymplecticForm.hamiltonianVectorField_div_two_mul_norm_sq`), whose derivative has norm
at most `c ≥ 0`
(`TauCeti.SymplecticForm.norm_fderiv_hamiltonianVectorField_div_two_mul_norm_sq_le`).

Along a family of Hamiltonians whose derivatives vary continuously, for instance a jointly `C¹`
family evaluated along a continuous map, the Hamiltonian vector fields vary continuously.

The Poisson bracket `{F, G} = ω(X_F, X_G)` of two Hamiltonians is the symplectic pairing of their
Hamiltonian vector fields. With the contraction convention it is `dF(X_G) = -dG(X_F)`; it is
antisymmetric, vanishes when either argument is constant, and is linear in each argument on
Hamiltonians differentiable at the point.

See McDuff--Salamon, *Introduction to Symplectic Topology*, the discussion of Hamiltonian
vector fields and their flows. The construction uses `SymplecticForm` contraction duality.
-/

public section

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The Hamiltonian vector field, with convention `ι_X ω = dH`.
The derivative is totalized as usual: at a nondifferentiability point this field is zero. -/
noncomputable def hamiltonianVectorField (ω : SymplecticForm V) (H : V → ℝ) (x : V) : V :=
  ω.toBilinForm.toContinuousBilinearMap.inverse (fderiv ℝ H x)

/-- The Hamiltonian vector field is inverse contraction applied to the derivative. -/
theorem hamiltonianVectorField_def (ω : SymplecticForm V) (H : V → ℝ) (x : V) :
    ω.hamiltonianVectorField H x =
      ω.toBilinForm.toContinuousBilinearMap.inverse (fderiv ℝ H x) :=
  (rfl)

/-- The Hamiltonian vector field at `x` depends only on the germ of the Hamiltonian at `x`. -/
theorem hamiltonianVectorField_congr_of_eventuallyEq (ω : SymplecticForm V) {H H' : V → ℝ}
    {x : V} (h : H =ᶠ[nhds x] H') :
    ω.hamiltonianVectorField H x = ω.hamiltonianVectorField H' x := by
  rw [hamiltonianVectorField_def, hamiltonianVectorField_def, h.fderiv_eq]

/-- Contraction of the Hamiltonian field is the derivative of the Hamiltonian. -/
@[simp]
theorem apply_hamiltonianVectorField (ω : SymplecticForm V) (H : V → ℝ) (x v : V) :
    ω (ω.hamiltonianVectorField H x) v = fderiv ℝ H x v := by
  exact congrArg (fun L : V →L[ℝ] ℝ ↦ L v)
    (ω.isInvertible_toContinuousBilinearMap.self_apply_inverse (fderiv ℝ H x))

/-- The contraction equation uniquely characterizes the Hamiltonian vector field. -/
theorem eq_hamiltonianVectorField_iff (ω : SymplecticForm V) (H : V → ℝ) (x u : V) :
    u = ω.hamiltonianVectorField H x ↔ ∀ v, ω u v = fderiv ℝ H x v := by
  constructor
  · rintro rfl v
    exact ω.apply_hamiltonianVectorField H x v
  · intro h
    apply ω.isInvertible_toContinuousBilinearMap.injective
    ext v
    exact (h v).trans (ω.apply_hamiltonianVectorField H x v).symm

/-- The Hamiltonian vector field vanishes at `x` exactly when the derivative `fderiv ℝ H x` does.
Where `H` is differentiable these are the critical points of `H`; since `fderiv` is `0` where `H`
is not differentiable, the field also vanishes at every such point. -/
@[simp]
theorem hamiltonianVectorField_eq_zero_iff (ω : SymplecticForm V) (H : V → ℝ) (x : V) :
    ω.hamiltonianVectorField H x = 0 ↔ fderiv ℝ H x = 0 := by
  rw [eq_comm, eq_hamiltonianVectorField_iff]
  simp [ContinuousLinearMap.ext_iff, eq_comm]

/-- The Hamiltonian vector field vanishes off the topological support of the Hamiltonian. -/
theorem hamiltonianVectorField_eq_zero_of_notMem_tsupport (ω : SymplecticForm V) {H : V → ℝ}
    {x : V} (hx : x ∉ tsupport H) : ω.hamiltonianVectorField H x = 0 :=
  (ω.hamiltonianVectorField_eq_zero_iff H x).2 (fderiv_of_notMem_tsupport ℝ hx)

/-- The Hamiltonian vector field `X_{K z}` of a family `K` of Hamiltonians vanishes at every point
`(z, x)` off the topological support of the family. -/
theorem hamiltonianVectorField_eq_zero_of_notMem_tsupport_uncurry (ω : SymplecticForm V)
    {X : Type*} [TopologicalSpace X] {K : X → V → ℝ} {z : X} {x : V}
    (h : (z, x) ∉ tsupport (Function.uncurry K)) : ω.hamiltonianVectorField (K z) x = 0 :=
  ω.hamiltonianVectorField_eq_zero_of_notMem_tsupport fun hx ↦ h
    (tsupport_comp_subset_preimage (Function.uncurry K) (continuous_const.prodMk continuous_id) hx)

/-- The Hamiltonian vector field is homogeneous: `X_{c H} = c X_H`. -/
@[simp]
theorem hamiltonianVectorField_const_mul (ω : SymplecticForm V) (c : ℝ) (H : V → ℝ) (x : V) :
    ω.hamiltonianVectorField (fun y ↦ c * H y) x = c • ω.hamiltonianVectorField H x := by
  have h : (fun y ↦ c * H y) = c • H := by
    ext
    simp
  rw [hamiltonianVectorField, hamiltonianVectorField, h, fderiv_const_smul_field, Pi.smul_apply,
    map_smul]

/-- The Hamiltonian vector field is homogeneous, as an identity of vector fields:
`X_{c H} = c X_H`. -/
theorem hamiltonianVectorField_const_mul' (ω : SymplecticForm V) (c : ℝ) (H : V → ℝ) :
    ω.hamiltonianVectorField (fun y ↦ c * H y) = c • ω.hamiltonianVectorField H :=
  funext fun x ↦ ω.hamiltonianVectorField_const_mul c H x

/-- The Hamiltonian has zero derivative in its own Hamiltonian direction. -/
@[simp]
theorem fderiv_apply_hamiltonianVectorField (ω : SymplecticForm V) (H : V → ℝ) (x : V) :
    fderiv ℝ H x (ω.hamiltonianVectorField H x) = 0 := by
  rw [← ω.apply_hamiltonianVectorField H x, ω.self_eq_zero]

/-- For a `J`-invariant symplectic form, `J X_H(x)` is the gradient of `H` at `x` for the
bilinear form `g = ω(·, J ·)`: `g(J X_H(x), w) = dH(x) w`. -/
theorem Invariant.associatedBilinForm_hamiltonianVectorField {ω : SymplecticForm V}
    {J : AlmostComplexStructure V} (hJ : ω.Invariant J) (H : V → ℝ) (x w : V) :
    ω.associatedBilinForm J (J (ω.hamiltonianVectorField H x)) w = fderiv ℝ H x w := by
  rw [associatedBilinForm_apply, (ω.invariant_iff J).mp hJ, apply_hamiltonianVectorField]

/-- A `C^(n+1)` Hamiltonian has a `C^n` Hamiltonian vector field. -/
theorem contDiff_hamiltonianVectorField (ω : SymplecticForm V) {H : V → ℝ}
    {n : WithTop ℕ∞} (hH : ContDiff ℝ (n + 1) H) :
    ContDiff ℝ n (ω.hamiltonianVectorField H) :=
  ω.toBilinForm.toContinuousBilinearMap.inverse.contDiff.comp
    (hH.fderiv_right le_rfl)

/-- A Hamiltonian with compact support has a Hamiltonian vector field with compact support. -/
theorem hasCompactSupport_hamiltonianVectorField (ω : SymplecticForm V) {H : V → ℝ}
    (hc : HasCompactSupport H) : HasCompactSupport (ω.hamiltonianVectorField H) := by
  have h : ω.hamiltonianVectorField H =
      ω.toBilinForm.toContinuousBilinearMap.inverse ∘ fderiv ℝ H :=
    funext (ω.hamiltonianVectorField_def H)
  exact h ▸ (hc.fderiv ℝ).comp_left (map_zero _)

/-- A `C²` Hamiltonian with compact support has a globally Lipschitz Hamiltonian vector field, so
its flow `TauCeti.SymplecticForm.hamiltonianFlow` is defined for all times. -/
theorem exists_lipschitzWith_hamiltonianVectorField (ω : SymplecticForm V) {H : V → ℝ}
    (hH : ContDiff ℝ 2 H) (hc : HasCompactSupport H) :
    ∃ K, LipschitzWith K (ω.hamiltonianVectorField H) := by
  exact (ω.contDiff_hamiltonianVectorField (n := 1)
    (by simpa only [one_add_one_eq_two] using hH)).lipschitzWith_of_hasCompactSupport
    (ω.hasCompactSupport_hamiltonianVectorField hc) one_ne_zero

/-- A `C³` Hamiltonian with compact support has a Hamiltonian vector field whose first and second
derivatives are bounded on all of `V`. -/
theorem exists_forall_norm_fderiv_hamiltonianVectorField_le (ω : SymplecticForm V) {H : V → ℝ}
    (hH : ContDiff ℝ 3 H) (hc : HasCompactSupport H) :
    ∃ a c, ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a ∧
      ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c := by
  have hXc := ω.hasCompactSupport_hamiltonianVectorField hc
  have hdX := (ω.contDiff_hamiltonianVectorField (n := 2) hH).fderiv_right (m := 1) (by norm_num)
  obtain ⟨a, ha⟩ := hdX.continuous.bounded_above_of_compact_support (hXc.fderiv ℝ)
  obtain ⟨c, hc⟩ := (hdX.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    ((hXc.fderiv ℝ).fderiv ℝ)
  exact ⟨a, c, fun x ↦ ⟨ha x, hc x⟩⟩

/-- Contracting the linearization of the Hamiltonian vector field gives the Hessian. -/
theorem apply_fderiv_hamiltonianVectorField (ω : SymplecticForm V) {H : V → ℝ}
    {x : V} (hH : DifferentiableAt ℝ (fderiv ℝ H) x) (u v : V) :
    ω (fderiv ℝ (ω.hamiltonianVectorField H) x u) v =
      fderiv ℝ (fderiv ℝ H) x u v := by
  have h := ω.toBilinForm.toContinuousBilinearMap.inverse.hasFDerivAt.comp x hH.hasFDerivAt
  have hX : HasFDerivAt (ω.hamiltonianVectorField H)
      (ω.toBilinForm.toContinuousBilinearMap.inverse.comp (fderiv ℝ (fderiv ℝ H) x)) x := h
  rw [hX.fderiv]
  exact congrArg (fun L : V →L[ℝ] ℝ ↦ L v)
    (ω.isInvertible_toContinuousBilinearMap.self_apply_inverse
      (fderiv ℝ (fderiv ℝ H) x u))

/-- The linearization of the Hamiltonian vector field has the kernel of the Hessian: where `dH`
is differentiable, `dX_H(x) u = 0` exactly when `d²H(x)(u, ·) = 0`, because
`ω(dX_H(x) u, v) = d²H(x)(u, v)` and `ω` is nondegenerate. -/
theorem fderiv_hamiltonianVectorField_apply_eq_zero_iff (ω : SymplecticForm V) {H : V → ℝ}
    {x : V} (hH : DifferentiableAt ℝ (fderiv ℝ H) x) (u : V) :
    fderiv ℝ (ω.hamiltonianVectorField H) x u = 0 ↔ ∀ v, fderiv ℝ (fderiv ℝ H) x u v = 0 := by
  simp_rw [← ω.apply_fderiv_hamiltonianVectorField hH u]
  exact ⟨fun h v ↦ by rw [h]; exact LinearMap.map_zero₂ _ v, ω.separatingLeft _⟩

/-- The linearization of a `C²` Hamiltonian vector field is infinitesimally symplectic. -/
theorem apply_fderiv_hamiltonianVectorField_add (ω : SymplecticForm V) {H : V → ℝ}
    {x : V} (hH : ContDiffAt ℝ 2 H x) (u v : V) :
    ω (fderiv ℝ (ω.hamiltonianVectorField H) x u) v +
      ω u (fderiv ℝ (ω.hamiltonianVectorField H) x v) = 0 := by
  have hd := (hH.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [← ω.neg_eq (fderiv ℝ (ω.hamiltonianVectorField H) x v) u,
    ω.apply_fderiv_hamiltonianVectorField hd, ω.apply_fderiv_hamiltonianVectorField hd]
  rw [hH.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField]) u v]
  exact add_neg_cancel _

/-- For a `J`-invariant symplectic form and a `C²` Hamiltonian, `J dX_H(x)` is symmetric for the
bilinear form `g = ω(·, J ·)`: `g(J dX_H(x) u, v) = g(u, J dX_H(x) v)`. It is the Hessian of `H`
at `x`, since `J X_H` is the gradient of `H` for `g`. -/
theorem Invariant.associatedBilinForm_apply_fderiv_hamiltonianVectorField_comm
    {ω : SymplecticForm V} {J : AlmostComplexStructure V} (hJ : ω.Invariant J) {H : V → ℝ}
    {x : V} (hH : ContDiffAt ℝ 2 H x) (u v : V) :
    ω.associatedBilinForm J (J (fderiv ℝ (ω.hamiltonianVectorField H) x u)) v =
      ω.associatedBilinForm J u (J (fderiv ℝ (ω.hamiltonianVectorField H) x v)) := by
  have h := ω.apply_fderiv_hamiltonianVectorField_add hH u v
  have hneg : ω u (-fderiv ℝ (ω.hamiltonianVectorField H) x v) =
      -ω u (fderiv ℝ (ω.hamiltonianVectorField H) x v) := map_neg (ω.toBilinForm u) _
  rw [associatedBilinForm_apply, associatedBilinForm_apply, (ω.invariant_iff J).mp hJ,
    J.apply_apply, hneg]
  linarith

/-- A constant Hamiltonian has zero Hamiltonian vector field. -/
@[simp]
theorem hamiltonianVectorField_const (ω : SymplecticForm V) (c : ℝ) :
    ω.hamiltonianVectorField (fun _ ↦ c) = 0 := by
  funext x
  rw [Pi.zero_apply, eq_comm, eq_hamiltonianVectorField_iff]
  simp

/-- The Hamiltonian vector field of the linear function `ω(a, ·)` is the constant `a`. -/
@[simp]
theorem hamiltonianVectorField_apply_left (ω : SymplecticForm V) (a x : V) :
    ω.hamiltonianVectorField (fun y ↦ ω a y) x = a := by
  -- The function `ω(a, ·)` is the continuous linear map `ω.toBilinForm.toContinuousBilinearMap a`.
  have h : HasFDerivAt (fun y ↦ ω a y) (ω.toBilinForm.toContinuousBilinearMap a) x :=
    (ω.toBilinForm.toContinuousBilinearMap a).hasFDerivAt
  rw [eq_comm, eq_hamiltonianVectorField_iff, h.fderiv]
  intro v
  exact (LinearMap.toContinuousBilinearMap_apply _ a v).symm

/-- Adding a constant to a Hamiltonian does not change its Hamiltonian vector field. No
differentiability is needed: `H` and `H + c` are differentiable at the same points. -/
@[simp]
theorem hamiltonianVectorField_add_const (ω : SymplecticForm V) (H : V → ℝ) (c : ℝ) :
    ω.hamiltonianVectorField (fun x ↦ H x + c) = ω.hamiltonianVectorField H := by
  funext x
  rw [hamiltonianVectorField_def, hamiltonianVectorField_def, fderiv_add_const]

/-- Translating a Hamiltonian translates its Hamiltonian vector field:
`X_{H(· + c)}(x) = X_H(x + c)`. No differentiability is needed. -/
@[simp]
theorem hamiltonianVectorField_comp_add_right (ω : SymplecticForm V) (H : V → ℝ) (c : V) :
    ω.hamiltonianVectorField (fun x ↦ H (x + c)) = fun x ↦ ω.hamiltonianVectorField H (x + c) := by
  funext x
  rw [hamiltonianVectorField_def, hamiltonianVectorField_def, fderiv_comp_add_right]

/-- The Hamiltonian vector field is linear in Hamiltonians differentiable at the point:
`X_{aF + bG} = a X_F + b X_G`. -/
theorem hamiltonianVectorField_const_mul_add_const_mul (ω : SymplecticForm V) {F G : V → ℝ}
    {x : V} (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (a b : ℝ) :
    ω.hamiltonianVectorField (fun y ↦ a * F y + b * G y) x =
      a • ω.hamiltonianVectorField F x + b • ω.hamiltonianVectorField G x := by
  rw [eq_comm, eq_hamiltonianVectorField_iff]
  intro v
  rw [fderiv_fun_add (hF.const_mul a) (hG.const_mul b), fderiv_const_mul hF, fderiv_const_mul hG]
  simp [map_add, map_smul]

/-- For `C²` Hamiltonians the derivative of the Hamiltonian vector field is linear in the
Hamiltonian: `d X_{aF + bG} = a dX_F + b dX_G`. -/
theorem fderiv_hamiltonianVectorField_const_mul_add_const_mul (ω : SymplecticForm V)
    {F G : V → ℝ} (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (a b : ℝ) (x : V) :
    fderiv ℝ (ω.hamiltonianVectorField fun y ↦ a * F y + b * G y) x =
      a • fderiv ℝ (ω.hamiltonianVectorField F) x +
        b • fderiv ℝ (ω.hamiltonianVectorField G) x := by
  have hXF := (ω.contDiff_hamiltonianVectorField (n := 1) hF).differentiable one_ne_zero
  have hXG := (ω.contDiff_hamiltonianVectorField (n := 1) hG).differentiable one_ne_zero
  have hX : ω.hamiltonianVectorField (fun y ↦ a * F y + b * G y) =
      a • ω.hamiltonianVectorField F + b • ω.hamiltonianVectorField G :=
    funext fun y ↦ ω.hamiltonianVectorField_const_mul_add_const_mul
      ((hF.differentiable two_ne_zero) y) ((hG.differentiable two_ne_zero) y) _ _
  rw [hX, fderiv_add ((hXF x).const_smul _) ((hXG x).const_smul _), fderiv_const_smul (hXF x),
    fderiv_const_smul (hXG x)]

/-- For `C²` Hamiltonians the derivative of the Hamiltonian vector field of `aF + bG` is bounded
by `|a| ‖dX_F‖ + |b| ‖dX_G‖`. -/
theorem norm_fderiv_hamiltonianVectorField_const_mul_add_const_mul_le (ω : SymplecticForm V)
    {F G : V → ℝ} (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (a b : ℝ) (x : V) :
    ‖fderiv ℝ (ω.hamiltonianVectorField fun y ↦ a * F y + b * G y) x‖ ≤
      |a| * ‖fderiv ℝ (ω.hamiltonianVectorField F) x‖ +
        |b| * ‖fderiv ℝ (ω.hamiltonianVectorField G) x‖ := by
  rw [ω.fderiv_hamiltonianVectorField_const_mul_add_const_mul hF hG, ← Real.norm_eq_abs,
    ← Real.norm_eq_abs, ← norm_smul, ← norm_smul]
  exact norm_add_le _ _

/-- The Hamiltonian vector field is additive on finite sums of Hamiltonians differentiable at
the point: `X_{∑ Fᵢ} = ∑ X_{Fᵢ}`. -/
theorem hamiltonianVectorField_fun_sum (ω : SymplecticForm V) {ι : Type*} {s : Finset ι}
    {F : ι → V → ℝ} {x : V} (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) x) :
    ω.hamiltonianVectorField (fun y ↦ ∑ i ∈ s, F i y) x =
      ∑ i ∈ s, ω.hamiltonianVectorField (F i) x := by
  rw [eq_comm, eq_hamiltonianVectorField_iff]
  intro v
  rw [fderiv_fun_sum hF]
  simp [map_sum]

/-- The Hamiltonian vector field of `-H` is `-X_H`. -/
@[simp]
theorem hamiltonianVectorField_neg (ω : SymplecticForm V) (H : V → ℝ) (x : V) :
    ω.hamiltonianVectorField (-H) x = -ω.hamiltonianVectorField H x := by
  rw [eq_comm, eq_hamiltonianVectorField_iff]
  intro v
  simp [fderiv_neg]

/-- The Hamiltonian vector field of a sum of Hamiltonians differentiable at the point:
`X_{F + G} = X_F + X_G`. -/
theorem hamiltonianVectorField_add (ω : SymplecticForm V) {F G : V → ℝ} {x : V}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    ω.hamiltonianVectorField (F + G) x =
      ω.hamiltonianVectorField F x + ω.hamiltonianVectorField G x := by
  rw [eq_comm, eq_hamiltonianVectorField_iff]
  intro v
  rw [fderiv_add hF hG]
  simp [map_add]

/-- The Hamiltonian vector field of a difference of Hamiltonians differentiable at the point:
`X_{F - G} = X_F - X_G`. -/
theorem hamiltonianVectorField_sub (ω : SymplecticForm V) {F G : V → ℝ} {x : V}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    ω.hamiltonianVectorField (F - G) x =
      ω.hamiltonianVectorField F x - ω.hamiltonianVectorField G x := by
  rw [eq_comm, eq_hamiltonianVectorField_iff]
  intro v
  rw [fderiv_sub hF hG]
  simp [map_sub]

open Metric in
/-- **Second-order Taylor bound for a Hamiltonian.** If the Hamiltonian vector field of a
differentiable function `G` satisfies `‖X_G(z) - X_G(y₀)‖ ≤ L ‖z - y₀‖` on the closed ball of
radius `r` about `y₀`, then `|G(y) - G(y₀) - dG(y₀)(y - y₀)| ≤ ‖ω‖ L ‖y - y₀‖²` for
`‖y - y₀‖ ≤ r`, where `‖ω‖` is the operator norm of the form. -/
theorem abs_sub_sub_fderiv_le_of_norm_hamiltonianVectorField_sub_le (ω : SymplecticForm V)
    {G : V → ℝ} (hG : Differentiable ℝ G) {y₀ y : V} {L r : ℝ} (hL : 0 ≤ L)
    (hX : ∀ z ∈ closedBall y₀ r,
      ‖ω.hamiltonianVectorField G z - ω.hamiltonianVectorField G y₀‖ ≤ L * ‖z - y₀‖)
    (hy : ‖y - y₀‖ ≤ r) :
    |G y - G y₀ - fderiv ℝ G y₀ (y - y₀)| ≤
      ‖ω.toBilinForm.toContinuousBilinearMap‖ * L * ‖y - y₀‖ ^ 2 := by
  set B := ‖ω.toBilinForm.toContinuousBilinearMap‖
  -- On the ball of radius `‖y - y₀‖`, `dG(z) - dG(y₀) = ω(X_G(z) - X_G(y₀), ·)` is small.
  have hball (z : V) (hz : z ∈ closedBall y₀ ‖y - y₀‖) :
      ‖fderiv ℝ G z - fderiv ℝ G y₀‖ ≤ B * L * ‖y - y₀‖ := by
    have hz' : ‖z - y₀‖ ≤ ‖y - y₀‖ := by simpa [dist_eq_norm] using hz
    have hXz := (hX z (mem_closedBall.2 (by rw [dist_eq_norm]; exact hz'.trans hy))).trans
      (mul_le_mul_of_nonneg_left hz' hL)
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
    rw [sub_apply, ← ω.apply_hamiltonianVectorField, ← ω.apply_hamiltonianVectorField,
      Real.norm_eq_abs]
    have h := ω.abs_apply_le_opNorm_mul_norm_mul_norm
      (ω.hamiltonianVectorField G z - ω.hamiltonianVectorField G y₀) v
    simp only [map_sub, LinearMap.sub_apply] at h
    calc _ ≤ B * ‖ω.hamiltonianVectorField G z - ω.hamiltonianVectorField G y₀‖ * ‖v‖ := h
      _ ≤ B * (L * ‖y - y₀‖) * ‖v‖ := by gcongr
      _ = _ := by ring
  have hyb : y ∈ closedBall y₀ ‖y - y₀‖ := by simp [dist_eq_norm]
  have hmv := (convex_closedBall y₀ ‖y - y₀‖).norm_image_sub_le_of_norm_fderiv_le'
    (fun z _ ↦ hG z) hball (mem_closedBall_self (norm_nonneg _)) hyb
  rw [Real.norm_eq_abs] at hmv
  exact hmv.trans_eq (by ring)

section Continuity

variable {X : Type*} [TopologicalSpace X] {K : X → V → ℝ} {u : X → V} {s : Set X}

/-- Along a family of Hamiltonians `K z` and points `u z` whose derivatives `dK_z(u z)` vary
continuously on a set, the Hamiltonian vector fields `X_{K z}(u z)` vary continuously on it. -/
theorem continuousOn_hamiltonianVectorField_comp (ω : SymplecticForm V)
    (h : ContinuousOn (fun z ↦ fderiv ℝ (K z) (u z)) s) :
    ContinuousOn (fun z ↦ ω.hamiltonianVectorField (K z) (u z)) s :=
  ω.toBilinForm.toContinuousBilinearMap.inverse.continuous.comp_continuousOn h

/-- Along a family of Hamiltonians `K z` and points `u z` whose derivatives `dK_z(u z)` vary
continuously, the Hamiltonian vector fields `X_{K z}(u z)` vary continuously. -/
theorem continuous_hamiltonianVectorField_comp (ω : SymplecticForm V)
    (h : Continuous fun z ↦ fderiv ℝ (K z) (u z)) :
    Continuous fun z ↦ ω.hamiltonianVectorField (K z) (u z) :=
  ω.toBilinForm.toContinuousBilinearMap.inverse.continuous.comp h

end Continuity

/-- For a family of Hamiltonians `K z` that is jointly `C¹` over a set `U` of the parameter space,
the Hamiltonian vector field `X_{K z}(x)` is continuous jointly in the parameter `z ∈ U` and the
point `x`. -/
theorem continuousOn_uncurry_hamiltonianVectorField {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] (ω : SymplecticForm V) {K : W → V → ℝ} {U : Set W}
    (hK : ContDiffOn ℝ 1 (Function.uncurry K) (U ×ˢ Set.univ)) :
    ContinuousOn (Function.uncurry fun z ↦ ω.hamiltonianVectorField (K z)) (U ×ˢ Set.univ) := by
  refine ω.toBilinForm.toContinuousBilinearMap.inverse.continuous.comp_continuousOn ?_
  exact (hK.fderiv_right (n := 0) isOpen_univ).continuousOn

/-- For a family of Hamiltonians `K z` that is jointly `C¹` over a set `U` of the parameter space,
the Hamiltonian vector fields `X_{K z}` evaluated along a map continuous on `U` vary continuously
on `U`. -/
theorem continuousOn_hamiltonianVectorField_comp_of_contDiffOn {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] (ω : SymplecticForm V) {K : W → V → ℝ} {u : W → V} {U : Set W}
    (hu : ContinuousOn u U) (hK : ContDiffOn ℝ 1 (Function.uncurry K) (U ×ˢ Set.univ)) :
    ContinuousOn (fun z ↦ ω.hamiltonianVectorField (K z) (u z)) U :=
  (ω.continuousOn_uncurry_hamiltonianVectorField hK).comp (continuousOn_id.prodMk hu)
    fun _ hz ↦ ⟨hz, Set.mem_univ _⟩

/-- For a jointly `C¹` family of Hamiltonians `K z`, the Hamiltonian vector field `X_{K z}(x)` is
continuous jointly in the parameter `z` and the point `x`. -/
theorem continuous_uncurry_hamiltonianVectorField {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] (ω : SymplecticForm V) {K : W → V → ℝ}
    (hK : ContDiff ℝ 1 (Function.uncurry K)) :
    Continuous (Function.uncurry fun z ↦ ω.hamiltonianVectorField (K z)) := by
  have h := ω.continuousOn_uncurry_hamiltonianVectorField (U := Set.univ) hK.contDiffOn
  rw [Set.univ_prod_univ] at h
  exact continuousOn_univ.1 h

section PoissonBracket

/-- The Poisson bracket `{F, G}(x) = ω(X_F x, X_G x)` of two Hamiltonians. -/
noncomputable def poissonBracket (ω : SymplecticForm V) (F G : V → ℝ) (x : V) : ℝ :=
  ω (ω.hamiltonianVectorField F x) (ω.hamiltonianVectorField G x)

theorem poissonBracket_def (ω : SymplecticForm V) (F G : V → ℝ) (x : V) :
    ω.poissonBracket F G x =
      ω (ω.hamiltonianVectorField F x) (ω.hamiltonianVectorField G x) :=
  (rfl)

/-- The Poisson bracket `{F, G}` is the derivative of `F` along the Hamiltonian field of `G`. -/
theorem poissonBracket_eq_fderiv (ω : SymplecticForm V) (F G : V → ℝ) (x : V) :
    ω.poissonBracket F G x = fderiv ℝ F x (ω.hamiltonianVectorField G x) := by
  rw [poissonBracket_def, apply_hamiltonianVectorField]

/-- The Poisson bracket `{F, G}` is minus the derivative of `G` along the Hamiltonian field of
`F`. -/
theorem poissonBracket_eq_neg_fderiv (ω : SymplecticForm V) (F G : V → ℝ) (x : V) :
    ω.poissonBracket F G x = -fderiv ℝ G x (ω.hamiltonianVectorField F x) := by
  rw [poissonBracket_def, ← ω.neg_eq, apply_hamiltonianVectorField]

/-- The Poisson bracket is antisymmetric. -/
theorem neg_poissonBracket (ω : SymplecticForm V) (F G : V → ℝ) (x : V) :
    -ω.poissonBracket G F x = ω.poissonBracket F G x := by
  rw [poissonBracket_def, poissonBracket_def, ω.neg_eq]

@[simp]
theorem poissonBracket_self (ω : SymplecticForm V) (F : V → ℝ) (x : V) :
    ω.poissonBracket F F x = 0 := by
  rw [poissonBracket_def, self_eq_zero]

@[simp]
theorem poissonBracket_const_left (ω : SymplecticForm V) (c : ℝ) (G : V → ℝ) (x : V) :
    ω.poissonBracket (fun _ ↦ c) G x = 0 := by
  simp [poissonBracket_def]

@[simp]
theorem poissonBracket_const_right (ω : SymplecticForm V) (F : V → ℝ) (c : ℝ) (x : V) :
    ω.poissonBracket F (fun _ ↦ c) x = 0 := by
  simp [poissonBracket_def]

/-- Adding a constant to the first Hamiltonian does not change the Poisson bracket. -/
@[simp]
theorem poissonBracket_add_const_left (ω : SymplecticForm V) (F : V → ℝ) (c : ℝ) (G : V → ℝ)
    (x : V) : ω.poissonBracket (fun y ↦ F y + c) G x = ω.poissonBracket F G x := by
  simp [poissonBracket_def]

/-- Adding a constant to the second Hamiltonian does not change the Poisson bracket. -/
@[simp]
theorem poissonBracket_add_const_right (ω : SymplecticForm V) (F G : V → ℝ) (c : ℝ) (x : V) :
    ω.poissonBracket F (fun y ↦ G y + c) x = ω.poissonBracket F G x := by
  simp [poissonBracket_def]

/-- The Poisson bracket is homogeneous in its first argument: `{c F, G} = c {F, G}`. -/
@[simp]
theorem poissonBracket_const_mul_left (ω : SymplecticForm V) (c : ℝ) (F G : V → ℝ) (x : V) :
    ω.poissonBracket (fun y ↦ c * F y) G x = c * ω.poissonBracket F G x := by
  simp [poissonBracket_def, map_smul]

/-- The Poisson bracket is homogeneous in its second argument: `{F, c G} = c {F, G}`. -/
@[simp]
theorem poissonBracket_const_mul_right (ω : SymplecticForm V) (F : V → ℝ) (c : ℝ) (G : V → ℝ)
    (x : V) : ω.poissonBracket F (fun y ↦ c * G y) x = c * ω.poissonBracket F G x := by
  simp [poissonBracket_def, map_smul]

/-- Negating the first argument negates the Poisson bracket. -/
@[simp]
theorem poissonBracket_neg_left (ω : SymplecticForm V) (F G : V → ℝ) (x : V) :
    ω.poissonBracket (-F) G x = -ω.poissonBracket F G x := by
  simp [poissonBracket_def]

/-- Negating the second argument negates the Poisson bracket. -/
@[simp]
theorem poissonBracket_neg_right (ω : SymplecticForm V) (F G : V → ℝ) (x : V) :
    ω.poissonBracket F (-G) x = -ω.poissonBracket F G x := by
  simp [poissonBracket_def]

/-- The Poisson bracket is subtractive in its first argument on Hamiltonians differentiable at
the point. -/
theorem poissonBracket_sub_left (ω : SymplecticForm V) {F F' : V → ℝ} (G : V → ℝ) {x : V}
    (hF : DifferentiableAt ℝ F x) (hF' : DifferentiableAt ℝ F' x) :
    ω.poissonBracket (F - F') G x = ω.poissonBracket F G x - ω.poissonBracket F' G x := by
  simp only [poissonBracket_eq_fderiv, fderiv_sub hF hF', sub_apply]

/-- The Poisson bracket is subtractive in its second argument on Hamiltonians differentiable at
the point. -/
theorem poissonBracket_sub_right (ω : SymplecticForm V) (F : V → ℝ) {G G' : V → ℝ} {x : V}
    (hG : DifferentiableAt ℝ G x) (hG' : DifferentiableAt ℝ G' x) :
    ω.poissonBracket F (G - G') x = ω.poissonBracket F G x - ω.poissonBracket F G' x := by
  simp only [poissonBracket_eq_fderiv, ω.hamiltonianVectorField_sub hG hG', map_sub]

/-- The Poisson bracket is additive in its first argument on finite sums of Hamiltonians
differentiable at the point: `{∑ Fᵢ, G} = ∑ {Fᵢ, G}`. -/
theorem poissonBracket_fun_sum_left (ω : SymplecticForm V) {ι : Type*} {s : Finset ι}
    {F : ι → V → ℝ} (G : V → ℝ) {x : V} (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) x) :
    ω.poissonBracket (fun y ↦ ∑ i ∈ s, F i y) G x = ∑ i ∈ s, ω.poissonBracket (F i) G x := by
  simp only [poissonBracket_eq_fderiv, fderiv_fun_sum hF, sum_apply]

/-- The Poisson bracket is additive in its second argument on finite sums of Hamiltonians
differentiable at the point: `{F, ∑ Gᵢ} = ∑ {F, Gᵢ}`. -/
theorem poissonBracket_fun_sum_right (ω : SymplecticForm V) {ι : Type*} {s : Finset ι}
    (F : V → ℝ) {G : ι → V → ℝ} {x : V} (hG : ∀ i ∈ s, DifferentiableAt ℝ (G i) x) :
    ω.poissonBracket F (fun y ↦ ∑ i ∈ s, G i y) x = ∑ i ∈ s, ω.poissonBracket F (G i) x := by
  simp only [poissonBracket_eq_fderiv, ω.hamiltonianVectorField_fun_sum hG, map_sum]

/-- The Poisson bracket of two combinations `a F + b G` and `c F + d G` is `a d - b c` times
`{F, G}`, with no differentiability hypothesis: where a combination is not differentiable its
Hamiltonian field is zero, and then `{F, G}` or the bracket of the combinations vanishes too. -/
theorem poissonBracket_comb (ω : SymplecticForm V) (F G : V → ℝ) (a b c d : ℝ) (x : V) :
    ω.poissonBracket (fun y ↦ a * F y + b * G y) (fun y ↦ c * F y + d * G y) x =
      (a * d - b * c) * ω.poissonBracket F G x := by
  by_cases hdet : a * d - b * c = 0
  · rw [hdet, zero_mul]
    by_cases hab : a = 0 ∧ b = 0
    · obtain ⟨rfl, rfl⟩ := hab
      simp
    · have hs : 0 < a ^ 2 + b ^ 2 := by
        by_contra h
        exact hab ⟨by nlinarith [sq_nonneg a, sq_nonneg b], by nlinarith [sq_nonneg a, sq_nonneg b]⟩
      have hB : (fun y ↦ c * F y + d * G y) =
          fun y ↦ ((c * a + d * b) / (a ^ 2 + b ^ 2)) * (a * F y + b * G y) := by
        funext y
        field_simp
        linear_combination (G y * a - F y * b) * hdet
      rw [hB, poissonBracket_const_mul_right, poissonBracket_self, mul_zero]
  · by_cases hFG : DifferentiableAt ℝ F x ∧ DifferentiableAt ℝ G x
    · simp only [poissonBracket_def, ω.hamiltonianVectorField_const_mul_add_const_mul hFG.1 hFG.2]
      exact ω.apply_smul_add_smul _ _ _ _ _ _
    · have hzero : ∀ H : V → ℝ, ¬ DifferentiableAt ℝ H x → ω.hamiltonianVectorField H x = 0 :=
        fun H hH ↦ by
          rw [hamiltonianVectorField_eq_zero_iff, fderiv_zero_of_not_differentiableAt hH]
      have hRHS : ω.poissonBracket F G x = 0 := by
        rw [poissonBracket_def]
        by_cases hF : DifferentiableAt ℝ F x
        · simp [hzero G fun hG ↦ hFG ⟨hF, hG⟩]
        · simp [hzero F hF]
      rw [hRHS, mul_zero, poissonBracket_def]
      by_cases hA : DifferentiableAt ℝ (fun y ↦ a * F y + b * G y) x
      · have hB : ¬ DifferentiableAt ℝ (fun y ↦ c * F y + d * G y) x :=
          fun hB ↦ hFG (differentiableAt_and_of_differentiableAt_comb hdet hA hB)
        simp [hzero _ hB]
      · simp [hzero _ hA]

/-- **Conservation of first integrals.** A function `F` which Poisson-commutes with `G` along an
integral curve of the Hamiltonian vector field of `G` on a preconnected set of times is constant
along it, provided `F` is differentiable at every point of the curve. -/
theorem apply_eq_of_hasDerivWithinAt_of_poissonBracket_eq_zero (ω : SymplecticForm V)
    {F G : V → ℝ} {γ : ℝ → V} {s : Set ℝ} (hs : IsPreconnected s)
    (hγ : ∀ t ∈ s, HasDerivWithinAt γ (ω.hamiltonianVectorField G (γ t)) s t)
    (hF : ∀ t ∈ s, DifferentiableAt ℝ F (γ t)) (hFG : ∀ t ∈ s, ω.poissonBracket F G (γ t) = 0)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    F (γ t) = F (γ t₀) := by
  have hd (t : ℝ) (ht : t ∈ s) : HasDerivWithinAt (F ∘ γ) 0 s t := by
    have h := (hF t ht).hasFDerivAt.comp_hasDerivWithinAt t (hγ t ht)
    rwa [← poissonBracket_eq_fderiv, hFG t ht] at h
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := F ∘ γ) (f' := fun _ ↦ 0)
    (C := 0) (fun x hx ↦ hd x hx) (fun _ _ ↦ by simp)
    (isPreconnected_iff_ordConnected.1 hs).convex ht₀ ht
  simpa [sub_eq_zero] using h

/-- **Conservation of energy.** A Hamiltonian is constant along every integral curve of its
Hamiltonian vector field on a preconnected set of times, provided it is differentiable at
every point of the curve; the curve need only have its derivative within the set of times. -/
theorem apply_eq_of_hasDerivWithinAt_hamiltonianVectorField (ω : SymplecticForm V) {H : V → ℝ}
    {γ : ℝ → V} {s : Set ℝ} (hs' : IsPreconnected s)
    (hγ : ∀ t ∈ s, HasDerivWithinAt γ (ω.hamiltonianVectorField H (γ t)) s t)
    (hH : ∀ t ∈ s, DifferentiableAt ℝ H (γ t)) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    H (γ t) = H (γ t₀) :=
  ω.apply_eq_of_hasDerivWithinAt_of_poissonBracket_eq_zero hs' hγ hH
    (fun _ _ ↦ ω.poissonBracket_self H _) ht₀ ht

end PoissonBracket

section Gradient

open scoped Gradient RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **`J X_H` is the gradient of `H`.** If the inner product of `E` is the metric `ω(·, J ·)`, then
`J X_H(x) = ∇H(x)`. -/
theorem apply_hamiltonianVectorField_eq_gradient {ω : SymplecticForm E}
    {J : AlmostComplexStructure E} (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (H : E → ℝ) (x : E) :
    J (ω.hamiltonianVectorField H x) = ∇ H x :=
  ext_inner_right ℝ fun w ↦ by
    rw [inner_gradient_left, ← hg, ← associatedBilinForm_apply]
    exact (ω.invariant_of_apply_apply_eq_inner hg).associatedBilinForm_hamiltonianVectorField H x w

/-- **The gradient of a Hamiltonian.** For the bilinear form `g(v, w) = ω(v, -J w)`, the
Hamiltonian vector field `X_H` of `ι_{X_H} ω = dH` gives the gradient `-J X_H` of `H`:
`g(v, -J X_H(x)) = dH_x(v)`. -/
theorem associatedBilinForm_neg_apply_neg_hamiltonianVectorField (ω : SymplecticForm V)
    (J : AlmostComplexStructure V) (H : V → ℝ) (x v : V) :
    ω.associatedBilinForm (-J) v (-J (ω.hamiltonianVectorField H x)) = fderiv ℝ H x v := by
  simp only [associatedBilinForm_apply, AlmostComplexStructure.neg_apply, map_neg, neg_neg,
    AlmostComplexStructure.apply_apply]
  rw [ω.neg_eq, apply_hamiltonianVectorField]

/-- If the inner product of `E` is the metric `ω(·, J ·)`, the Hamiltonian `Q(y) = (c / 2) ‖y‖²`
has the linear Hamiltonian vector field `X_Q(y) = -c J y`. -/
theorem hamiltonianVectorField_div_two_mul_norm_sq {ω : SymplecticForm E}
    {J : AlmostComplexStructure E} (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (c : ℝ) :
    ω.hamiltonianVectorField (fun y ↦ c / 2 * ‖y‖ ^ 2) =
      ⇑(-c • J.toLinearMap.toContinuousLinearMap) := by
  funext y
  rw [eq_comm, eq_hamiltonianVectorField_iff]
  intro v
  have hd : HasFDerivAt (fun y : E ↦ c / 2 * ‖y‖ ^ 2) ((c / 2) • (2 • innerSL ℝ y)) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul (c / 2)
  have hJ : ω (J y) v = -⟪y, v⟫ := by rw [real_inner_comm, ← hg v y, ω.neg_eq]
  rw [hd.fderiv]
  simp [hJ]
  ring

/-- If the inner product of `E` is the metric `ω(·, J ·)`, the derivative `-c J` of the Hamiltonian
vector field of `Q(y) = (c / 2) ‖y‖²` has norm at most `c ≥ 0`, since `J` is an isometry. -/
theorem norm_fderiv_hamiltonianVectorField_div_two_mul_norm_sq_le {ω : SymplecticForm E}
    {J : AlmostComplexStructure E} (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {c : ℝ} (hc : 0 ≤ c) (y : E) :
    ‖fderiv ℝ (ω.hamiltonianVectorField fun y ↦ c / 2 * ‖y‖ ^ 2) y‖ ≤ c := by
  rw [hamiltonianVectorField_div_two_mul_norm_sq hg c, ContinuousLinearMap.fderiv, norm_smul,
    norm_neg, Real.norm_eq_abs, abs_of_nonneg hc]
  refine mul_le_of_le_one_right hc (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ ?_)
  rw [one_mul, LinearMap.coe_toContinuousLinearMap']
  exact (ω.norm_apply_eq_norm_of_apply_apply_self_eq_inner (fun v ↦ hg v v) v).le

end Gradient

end TauCeti.SymplecticForm
