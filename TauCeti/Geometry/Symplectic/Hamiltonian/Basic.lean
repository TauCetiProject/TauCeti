/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Duality
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Hamiltonian vector fields on symplectic vector spaces

For a constant symplectic form on a finite-dimensional real normed space, the Hamiltonian
vector field of `H` is obtained by inverting contraction with the symplectic form.
Our sign convention is `ω (X_H x) v = dH(x) v`. For `ω = dq ∧ dp`, this gives the
Hamilton equations `q' = ∂H/∂p`, `p' = -∂H/∂q`.

The characteristic contraction equation determines the field uniquely. Since `dH(X_H) = 0`, a
differentiable Hamiltonian is constant along every integral curve of `X_H`
(`TauCeti.SymplecticForm.apply_eq_of_hasDerivWithinAt_hamiltonianVectorField`). The linearization of
`X_H` is infinitesimally symplectic when `H` is twice continuously differentiable; this is the
identity used to show that Hamiltonian flows preserve the symplectic form.

For an almost complex structure `J` preserving `ω`, the field `J X_H` is the gradient of `H` for
the bilinear form `g = ω(·, J ·)`
(`TauCeti.SymplecticForm.Invariant.associatedBilinForm_hamiltonianVectorField`).

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

/-- The Hamiltonian vector field is homogeneous: `X_{c H} = c X_H`. -/
@[simp]
theorem hamiltonianVectorField_const_mul (ω : SymplecticForm V) (c : ℝ) (H : V → ℝ) (x : V) :
    ω.hamiltonianVectorField (fun y ↦ c * H y) x = c • ω.hamiltonianVectorField H x := by
  have h : (fun y ↦ c * H y) = c • H := by
    ext
    simp
  rw [hamiltonianVectorField, hamiltonianVectorField, h, fderiv_const_smul_field, Pi.smul_apply,
    map_smul]

/-- The Hamiltonian has zero derivative in its own Hamiltonian direction. -/
@[simp]
theorem fderiv_apply_hamiltonianVectorField (ω : SymplecticForm V) (H : V → ℝ) (x : V) :
    fderiv ℝ H x (ω.hamiltonianVectorField H x) = 0 := by
  rw [← ω.apply_hamiltonianVectorField H x, ω.self_eq_zero]

/-- **Conservation of energy.** A Hamiltonian is constant along every integral curve of its
Hamiltonian vector field on a preconnected set of times, provided it is differentiable at
every point of the curve; the curve need only have its derivative within the set of times. -/
theorem apply_eq_of_hasDerivWithinAt_hamiltonianVectorField (ω : SymplecticForm V) {H : V → ℝ}
    {γ : ℝ → V} {s : Set ℝ} (hs' : IsPreconnected s)
    (hγ : ∀ t ∈ s, HasDerivWithinAt γ (ω.hamiltonianVectorField H (γ t)) s t)
    (hH : ∀ t ∈ s, DifferentiableAt ℝ H (γ t)) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    H (γ t) = H (γ t₀) := by
  have hd (t : ℝ) (ht : t ∈ s) : HasDerivWithinAt (H ∘ γ) 0 s t := by
    simpa using (hH t ht).hasFDerivAt.comp_hasDerivWithinAt t (hγ t ht)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := H ∘ γ) (f' := fun _ ↦ 0)
    (C := 0) (fun x hx ↦ hd x hx) (fun _ _ ↦ by simp)
    (isPreconnected_iff_ordConnected.1 hs').convex ht₀ ht
  simpa [sub_eq_zero] using h

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

end PoissonBracket

end TauCeti.SymplecticForm
