/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Hamiltonian
public import TauCeti.Geometry.Manifold.Morse.Hessian
import TauCeti.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Zeros of contact Hamiltonian vector fields and their linearization

Let `α` be a contact form on a finite-dimensional manifold `M`, with Reeb vector field `R_α` and
contact distribution `ξ = ker α`, and let `X_f` be the contact Hamiltonian vector field of a
function `f`, defined by `α(X_f) = f` and `ι_(X_f) dα = (R_α f) α - df`
(`TauCeti.SmoothForm.contactHamiltonianVectorField`).

The field `X_f` vanishes at `p` exactly when `f` vanishes at `p` and `df_p` vanishes on the contact
hyperplane `ξ_p` (`contactHamiltonianVectorField_eq_zero_iff`). In particular `X_f` vanishes
wherever `f` vanishes to second order, that is wherever `f` and `df` both vanish.

At such a point `p`, read `X_f` in the preferred chart at `p` and let `L` be the derivative of its
coordinate expression at the chart image of `p`, the linearization of `X_f` at `p`. Differentiate
the two defining equations at `p` along `w`. Every term carrying a derivative of a test vector
field is multiplied by `X_f(p) = 0` or by `(R_α f)(p) = 0` and drops out. Differentiating
`α(X_f) = f` gives `α_p(L w) = df_p(w) = 0`
(`apply_fderiv_mpullbackWithin_contactHamiltonianVectorField`), so `L` takes values in `ξ_p`.
Differentiating `dα(X_f, Y) = (R_α f) α(Y) - df(Y)` gives, in terms of the critical Hessian
`Hess f (p)` of `f` at `p` (`TauCeti.criticalHessian`),

`dα_p(L w, u) = Hess f (p) (w, R_α(p)) α_p(u) - Hess f (p) (w, u)`

(`mextDeriv_fderiv_mpullbackWithin_contactHamiltonianVectorField_left`). On the contact hyperplane
this reads `dα_p(L w, u) = -Hess f (p) (w, u)` for `u ∈ ξ_p`. Since `dα_p` is nondegenerate on
`ξ_p`, these properties determine `L`: `L w = k` exactly when `k ∈ ξ_p` and
`dα_p(k, u) = -Hess f (p) (w, u)` for every `u ∈ ξ_p`
(`fderiv_mpullbackWithin_contactHamiltonianVectorField_eq_iff`). So if the Hessian of `f` at `p`
is `-dα_p(K ·, ·)` on `T_p M × ξ_p` for a linear map `K` into `ξ_p`, then the linearization of
`X_f` at `p` is `K`. In particular `L w = 0` exactly when `Hess f (p) (w, ·)` vanishes on `ξ_p`
(`fderiv_mpullbackWithin_contactHamiltonianVectorField_eq_zero_iff`).

This is the pointwise computation behind the correction step of the isotropic neighbourhood
theorem. There, a quadratic Hamiltonian `H(s) = -½ dα(K s, s)` in the normal directions of an
isotropic submanifold `N`, extended so that `H` and `dH` vanish on `N`, is used to realize a
prescribed normal map: its contact Hamiltonian vector field vanishes on `N`, and the results here
identify its linearization at the points of `N` from the Hessian of `H`.

## Main results

All declarations are in the namespace `TauCeti.SmoothForm.IsContactForm`.

* `contactHamiltonianVectorField_eq_zero_iff`: `X_f(p) = 0` exactly when `f(p) = 0` and `df_p`
  vanishes on `ξ_p`.
* `apply_fderiv_mpullbackWithin_contactHamiltonianVectorField`: at a second-order zero of `f`,
  the linearization of `X_f` takes values in `ξ_p`.
* `mextDeriv_fderiv_mpullbackWithin_contactHamiltonianVectorField_left`: the formula for
  `dα_p(L w, u)` through the critical Hessian of `f`.
* `fderiv_mpullbackWithin_contactHamiltonianVectorField_eq_iff`: the linearization is the unique
  map into `ξ_p` with `dα_p(L w, ·) = -Hess f (p) (w, ·)` on `ξ_p`.
* `fderiv_mpullbackWithin_contactHamiltonianVectorField_eq_zero_iff`: the kernel of the
  linearization.

## References

* Hansjörg Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced
  Mathematics 109 (2008), Sections 2.3 (contact Hamiltonians) and 2.5 (isotropic submanifolds
  and their neighbourhoods).
* Andreas Kriegl and Peter W. Michor, *The Convenient Setting of Global Analysis*, Mathematical
  Surveys and Monographs 53, American Mathematical Society (1997), Section 43.
-/

public section

open Filter Function Set
open scoped Manifold Topology ContDiff

namespace TauCeti.SmoothForm.IsContactForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {α : SmoothForm I M ℝ 1} {f : M → ℝ} {p : M}

/-! ### Zeros -/

/-- **Zeros of a contact Hamiltonian vector field.** For a contact form `α`, the contact
Hamiltonian vector field of `f` vanishes at `p` exactly when `f` vanishes at `p` and `df_p`
vanishes on the contact hyperplane `ξ_p = ker α_p`. -/
theorem contactHamiltonianVectorField_eq_zero_iff (hα : α.IsContactForm) :
    α.contactHamiltonianVectorField f p = 0 ↔
      f p = 0 ∧ ∀ v ∈ α.kerDistribution p, mvfderiv I f p v = 0 := by
  constructor
  · intro h
    have h1 := hα.apply_contactHamiltonianVectorField f p
    rw [h, (α.1 p).map_coord_zero (m := ![0]) 0 rfl] at h1
    refine ⟨h1.symm, fun v hv ↦ ?_⟩
    have h2 := hα.mextDeriv_contactHamiltonianVectorField_left f p v
    rw [h, (mextDeriv α.1 p).map_coord_zero (m := ![0, v]) 0 rfl, mem_kerDistribution.1 hv,
      mul_zero, zero_sub] at h2
    linarith
  · rintro ⟨h0, hξ⟩
    -- The covector `(f + R_α f) α - df` vanishes at `p`: on `v`, its value is the value of `df`
    -- on `v - α(v) R_α ∈ ξ_p`, up to sign.
    have hcov : (f p + mvfderiv I f p (α.reebVectorField p)) • degreeOneEquiv α p -
        mvfderiv I f p = 0 := by
      ext v
      have hv := hξ _ (hα.sub_smul_reebVectorField_mem_kerDistribution v)
      rw [map_sub, map_smul, smul_eq_mul] at hv
      simp only [_root_.sub_apply, _root_.smul_apply, degreeOneEquiv_apply_apply_vec, h0,
        smul_eq_mul, _root_.zero_apply]
      linear_combination -hv
    rw [contactHamiltonianVectorField_def, hcov, map_zero]

/-- Two vectors of the contact hyperplane `ξ_p` with the same `dα_p`-pairing against `ξ_p` are
equal, since `dα_p` is nondegenerate on `ξ_p`. -/
private theorem eq_of_mem_kerDistribution_of_forall_mextDeriv_eq (hα : α.IsContactForm)
    {a b : TangentSpace I p} (ha : α.1 p ![a] = 0) (hb : α.1 p ![b] = 0)
    (hab : ∀ u ∈ α.kerDistribution p, mextDeriv α.1 p ![a, u] = mextDeriv α.1 p ![b, u]) :
    a = b := by
  -- The contact flat maps of `a` and `b` agree on the component of `v` in `ξ_p` and on the Reeb
  -- vector, which `dα_p` kills.
  refine (hα.isInvertible_contactFlat p).injective (ContinuousLinearMap.ext fun v ↦ ?_)
  have h := hab _ (hα.sub_smul_reebVectorField_mem_kerDistribution v)
  have hRa := hα.mextDeriv_reebVectorField_right p a
  have hRb := hα.mextDeriv_reebVectorField_right p b
  simp only [mextDeriv_eq_bilinFormAt] at h hRa hRb
  simp only [map_sub, map_smul, hRa, hRb, smul_zero, sub_zero] at h
  simpa only [contactFlat_apply, ha, hb, zero_mul, add_zero, mextDeriv_eq_bilinFormAt] using h

/-! ### The linearization at a second-order zero -/

variable [I.Boundaryless]

omit [FiniteDimensional ℝ E] in
/-- The derivative at `p` of `y ↦ φ_y(W_0 y, …, W_(k-1) y)`, when the field `W i₀` vanishes at
`p`: only the derivative of the coordinate expression of `W i₀` in the preferred chart at `p`
contributes. -/
private theorem mvfderiv_apply_vectorField_of_eq_zero {k : ℕ} (φ : SmoothForm I M ℝ k)
    (W : Fin k → (y : M) → TangentSpace I y)
    (hW : ∀ i, MDifferentiableAt I I.tangent (fun y ↦ (W i y : TangentBundle I M)) p)
    {i₀ : Fin k} (h₀ : W i₀ p = 0) (w : TangentSpace I p) :
    mvfderiv I (fun y ↦ φ.1 y (W · y)) p w = φ.1 p (update (W · p) i₀
      (fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm (W i₀) (range I))
        (extChartAt I p p) w)) := by
  let V : Fin k → E → E := fun i ↦
    VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm (W i) (range I)
  have hV : ∀ i, DifferentiableAt ℝ (V i) (extChartAt I p p) := fun i ↦
    (hW i).differentiableAt_mpullbackWithin_extChartAt_symm
  have hVp : ∀ i, V i (extChartAt I p p) = W i p := fun i ↦
    VectorField.mpullbackWithin_extChartAt_symm_self _ _
  have hφ : DifferentiableAt ℝ (RoughForm.inChartAt φ.1 p) (extChartAt I p p) :=
    RoughForm.differentiableAt_inChartAt φ.1 ((φ.contMDiff p).mdifferentiableAt (by simp))
  -- Read the function in the chart at `p`, where the derivative of the vanishing slot is the only
  -- surviving term.
  have h := fderivWithin_inChartAt_apply_mpullbackWithin (s := univ) (x := p) φ.1 W
    hφ.differentiableWithinAt (fun i ↦ (hV i).differentiableWithinAt)
  rw [mvfderivWithin_univ, preimage_univ, univ_inter,
    fderivWithin_of_mem_nhds (by rw [I.range_eq_univ]; exact univ_mem)] at h
  have key := fderiv_continuousAlternatingMap_apply_apply_of_eq_zero (g := V) hφ hV
    ((hVp i₀).trans h₀) w
  rw [h, RoughForm.inChartAt_extChartAt_self, funext hVp] at key
  exact key

/-- **The linearization of a contact Hamiltonian vector field takes values in the contact
hyperplane.** Let `α` be a contact form on a boundaryless finite-dimensional manifold and `f` a
`C²` function with `f(p) = 0` and `df_p = 0`. Let `L` be the derivative at the chart image of `p`
of the coordinate expression of `X_f` in the preferred chart at `p`. Then `α_p(L w) = 0`. -/
theorem apply_fderiv_mpullbackWithin_contactHamiltonianVectorField (hα : α.IsContactForm)
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (hf0 : f p = 0) (hcrit : mvfderiv I f p = 0)
    (w : TangentSpace I p) :
    α.1 p ![fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm
      (α.contactHamiltonianVectorField f) (range I)) (extChartAt I p p) w] = 0 := by
  -- Differentiate `α(X_f) = f` at `p`, where `X_f` vanishes and `df_p = 0`.
  have h := mvfderiv_apply_vectorField_of_eq_zero (i₀ := 0) α
    ![α.contactHamiltonianVectorField f]
    (fun i ↦ by fin_cases i; exact hα.mdifferentiable_contactHamiltonianVectorField hf p)
    (hα.contactHamiltonianVectorField_eq_zero_iff.2 ⟨hf0, fun v _ ↦ by rw [hcrit]; rfl⟩) w
  have hfun : (fun y ↦ α.1 y (![α.contactHamiltonianVectorField f] · y)) = f := by
    funext y
    convert hα.apply_contactHamiltonianVectorField f y using 2
    funext i
    fin_cases i
    rfl
  have hupd : update (![α.contactHamiltonianVectorField f] · p) 0
      (fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm
        (α.contactHamiltonianVectorField f) (range I)) (extChartAt I p p) w) =
      ![fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm
        (α.contactHamiltonianVectorField f) (range I)) (extChartAt I p p) w] := by
    funext i
    fin_cases i
    exact update_self _ _ _
  rw [hfun, hcrit, Matrix.cons_val_zero, hupd] at h
  exact h.symm

/-- **The linearization of a contact Hamiltonian vector field at a second-order zero.** Let `α` be
a contact form on a boundaryless finite-dimensional manifold and `f` a `C²` function with
`f(p) = 0` and `df_p = 0`. Let `L` be the derivative at the chart image of `p` of the coordinate
expression of `X_f` in the preferred chart at `p`. Then, in terms of the critical Hessian of `f`,

`dα_p(L w, u) = Hess f (p) (w, R_α(p)) α_p(u) - Hess f (p) (w, u)`. -/
theorem mextDeriv_fderiv_mpullbackWithin_contactHamiltonianVectorField_left
    (hα : α.IsContactForm)
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (hf0 : f p = 0) (hcrit : mvfderiv I f p = 0)
    (w u : TangentSpace I p) :
    mextDeriv α.1 p ![fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm
        (α.contactHamiltonianVectorField f) (range I)) (extChartAt I p p) w, u] =
      criticalHessian I f p w (α.reebVectorField p) * α.1 p ![u] -
        criticalHessian I f p w u := by
  -- Extend `u` to a vector field `Y` and differentiate `dα(X_f, Y)` at `p`, where `X_f` vanishes.
  let Y : (y : M) → TangentSpace I y := FiberBundle.extend E u
  have hY : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) p :=
    FiberBundle.mdifferentiableAt_extend I E u
  have hYp : Y p = u := FiberBundle.extend_apply_self E u
  have h := mvfderiv_apply_vectorField_of_eq_zero (i₀ := 0) (mextDerivₗ I 1 α)
    ![α.contactHamiltonianVectorField f, Y]
    (fun i ↦ by fin_cases i; exacts [hα.mdifferentiable_contactHamiltonianVectorField hf p, hY])
    (hα.contactHamiltonianVectorField_eq_zero_iff.2 ⟨hf0, fun v _ ↦ by rw [hcrit]; rfl⟩) w
  have hupd : update (![α.contactHamiltonianVectorField f, Y] · p) 0
      (fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm
        (α.contactHamiltonianVectorField f) (range I)) (extChartAt I p p) w) =
      ![fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm
        (α.contactHamiltonianVectorField f) (range I)) (extChartAt I p p) w, u] := by
    funext i
    fin_cases i
    · exact update_self _ _ _
    · exact (update_of_ne (by decide) _ _).trans hYp
  rw [mextDerivₗ_apply, Matrix.cons_val_zero, hupd] at h
  refine h.symm.trans ?_
  -- By the contraction equation, `dα(X_f, Y) = (R_α f) α(Y) - df(Y)`.
  have hfun : (fun y ↦ mextDeriv α.1 y (![α.contactHamiltonianVectorField f, Y] · y)) =
      fun y ↦ mvfderiv I f y (α.reebVectorField y) * α.1 y ![Y y] - mvfderiv I f y (Y y) := by
    funext y
    rw [← hα.mextDeriv_contactHamiltonianVectorField_left f y (Y y)]
    congr 1
    funext i
    fin_cases i <;> rfl
  -- Differentiate the right side at `p`, where `R_α f` vanishes.
  have hR : MDifferentiableAt I I.tangent
      (fun y ↦ (α.reebVectorField y : TangentBundle I M)) p :=
    (hα.contMDiff_reebVectorField p).mdifferentiableAt (by simp)
  have hRf := hα.mdifferentiable_mvfderiv_reebVectorField hf p
  have hαY : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ α.1 y ![Y y]) p :=
    α.mdifferentiableAt_apply_vectorField (V := fun i y ↦ ![Y y] i) fun i ↦ by
      fin_cases i
      exact hY
  have hRfαY : MDifferentiableAt I 𝓘(ℝ)
      (fun y ↦ mvfderiv I f y (α.reebVectorField y) * α.1 y ![Y y]) p := hRf.mul hαY
  have hdfY := mdifferentiableAt_mvfderiv_apply (hf p) le_rfl hY
  have hHY := criticalHessian_apply_eq_mvfderiv (hf p) hcrit hY w
  rw [hYp] at hHY
  rw [hfun, mvfderiv_fun_sub hRfαY hdfY, mvfderiv_fun_mul hRf hαY,
    criticalHessian_apply_eq_mvfderiv (hf p) hcrit hR w, hHY, hcrit, _root_.zero_apply,
    zero_smul, zero_add]
  have hlin : ∀ (c : ℝ) (A B : TangentSpace I p →L[ℝ] ℝ),
      (c • A - B) w = A w * c - B w := fun c A B ↦ by simp [mul_comm]
  exact (hlin _ _ _).trans (by rw [hYp])

/-- **The linearization of a contact Hamiltonian vector field on the contact hyperplane.** At a
point `p` where the `C²` function `f` and its differential vanish, the linearization `L` of `X_f`
at `p` satisfies `dα_p(L w, u) = -Hess f (p) (w, u)` for every `u ∈ ξ_p`. -/
theorem mextDeriv_fderiv_mpullbackWithin_contactHamiltonianVectorField_left_of_mem
    (hα : α.IsContactForm)
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (hf0 : f p = 0) (hcrit : mvfderiv I f p = 0)
    (w : TangentSpace I p) {u : TangentSpace I p} (hu : u ∈ α.kerDistribution p) :
    mextDeriv α.1 p ![fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm
        (α.contactHamiltonianVectorField f) (range I)) (extChartAt I p p) w, u] =
      -criticalHessian I f p w u := by
  rw [hα.mextDeriv_fderiv_mpullbackWithin_contactHamiltonianVectorField_left hf hf0 hcrit,
    mem_kerDistribution.1 hu, mul_zero, zero_sub]

/-- **Characterization of the linearization of a contact Hamiltonian vector field.** At a point `p`
where the `C²` function `f` and its differential vanish, the linearization `L` of `X_f` at `p`
sends `w` to `k` exactly when `k` lies in the contact hyperplane `ξ_p` and
`dα_p(k, u) = -Hess f (p) (w, u)` for every `u ∈ ξ_p`. The two conditions determine `k`, since
`dα_p` is nondegenerate on `ξ_p`. -/
theorem fderiv_mpullbackWithin_contactHamiltonianVectorField_eq_iff (hα : α.IsContactForm)
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (hf0 : f p = 0) (hcrit : mvfderiv I f p = 0)
    (w k : TangentSpace I p) :
    fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm
        (α.contactHamiltonianVectorField f) (range I)) (extChartAt I p p) w = k ↔
      k ∈ α.kerDistribution p ∧
        ∀ u ∈ α.kerDistribution p, mextDeriv α.1 p ![k, u] = -criticalHessian I f p w u := by
  have hL := hα.apply_fderiv_mpullbackWithin_contactHamiltonianVectorField hf hf0 hcrit w
  have hLu := fun u (hu : u ∈ α.kerDistribution p) ↦
    hα.mextDeriv_fderiv_mpullbackWithin_contactHamiltonianVectorField_left_of_mem hf hf0 hcrit w hu
  refine ⟨?_, fun ⟨hk, hku⟩ ↦
    hα.eq_of_mem_kerDistribution_of_forall_mextDeriv_eq hL (mem_kerDistribution.1 hk)
      fun u hu ↦ (hLu u hu).trans (hku u hu).symm⟩
  rintro rfl
  exact ⟨mem_kerDistribution.2 hL, hLu⟩

/-- **The kernel of the linearization of a contact Hamiltonian vector field.** At a point `p` where
the `C²` function `f` and its differential vanish, the linearization `L` of `X_f` at `p` kills `w`
exactly when `Hess f (p) (w, ·)` vanishes on the contact hyperplane `ξ_p`. -/
theorem fderiv_mpullbackWithin_contactHamiltonianVectorField_eq_zero_iff (hα : α.IsContactForm)
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (hf0 : f p = 0) (hcrit : mvfderiv I f p = 0)
    (w : TangentSpace I p) :
    fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm
        (α.contactHamiltonianVectorField f) (range I)) (extChartAt I p p) w = 0 ↔
      ∀ u ∈ α.kerDistribution p, criticalHessian I f p w u = 0 := by
  refine (hα.fderiv_mpullbackWithin_contactHamiltonianVectorField_eq_iff hf hf0 hcrit w 0).trans ?_
  refine ⟨fun ⟨_, h⟩ u hu ↦ ?_, fun h ↦ ⟨zero_mem _, fun u hu ↦ ?_⟩⟩
  · have := h u hu
    rwa [(mextDeriv α.1 p).map_coord_zero (m := ![0, u]) 0 rfl, zero_eq_neg] at this
  · rw [(mextDeriv α.1 p).map_coord_zero (m := ![0, u]) 0 rfl, h u hu, neg_zero]

end TauCeti.SmoothForm.IsContactForm
