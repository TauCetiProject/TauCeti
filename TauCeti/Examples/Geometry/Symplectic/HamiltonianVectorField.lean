/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.CanonicalTransformation
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Translation
public import TauCeti.Geometry.Symplectic.Hamiltonian.Oscillator.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Plane
public import TauCeti.Geometry.Symplectic.Prod.Basic
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Symplectic.Floer.Examples.LinearPerturbation
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Examples: Hamiltonian vector fields on the plane

Explicit computations on the standard symplectic plane `(ℝ², dq ∧ dp)`, the constant two-form
`(stdSymplecticForm (V := ℝ)).constSmooth` with `dq ∧ dp (v, w) = v₁ w₂ - v₂ w₁`, test the
Hamiltonian formalism of `TauCeti.SmoothTwoForm.IsHamiltonianVectorField` (`ι_X σ = df`) and show
that the hypotheses of its general statements cannot be dropped.

* **Nondegeneracy is needed for uniqueness and zeros.** For the zero two-form every vector field
  is a Hamiltonian vector field of a constant function
  (`isHamiltonianVectorField_zero_const`). So `∂_q`, which vanishes nowhere although the
  differential of a constant function does, and the zero field are two different Hamiltonian
  vector fields of the same function (`exists_isHamiltonianVectorField_zero_ne`,
  `exists_isHamiltonianVectorField_zero_ne_zero`): the nondegeneracy hypotheses of
  `TauCeti.SmoothTwoForm.IsHamiltonianVectorField.unique` and
  `TauCeti.SmoothTwoForm.IsHamiltonianVectorField.apply_eq_zero_iff` cannot be dropped.
* **The Leibniz rule.** The coordinates have the Hamiltonian vector fields `X_q = -∂_p` and
  `X_p = ∂_q` (`isHamiltonianVectorField_fst`, `isHamiltonianVectorField_snd`), and the Leibniz
  rule `X_{qp} = q X_p + p X_q` gives `X_{qp} = q ∂_q - p ∂_p`
  (`isHamiltonianVectorField_fst_mul_snd`). Their Poisson bracket is `{q, p} = 1`
  (`poissonBracket_fst_snd`), which is `dq(X_p)`.
* **Conservation of energy needs a preconnected set of times.** For `H(q, p) = p`, with
  `X_H = ∂_q`, the curve equal to `(t, 0)` for `t ∈ (0, 1)` and to `(t, 5)` for `t ∈ (2, 3)` is an
  integral curve of `X_H` on `(0, 1) ∪ (2, 3)` along which `H` takes the values `0` and `5`
  (`exists_isMIntegralCurveOn_snd_ne`), unlike on an interval
  (`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.apply_eq_of_isMIntegralCurveOn`).
* **Transport needs invertible differentials.** The inclusion `φ(q₁, p₁) = (q₁, p₁, 0, 0)` of the
  plane into `(ℝ⁴, dq₁ ∧ dp₁ + dq₂ ∧ dp₂)` is a symplectic map
  (`isSymplecticMap_inl`) whose differential is not invertible
  (`not_isInvertible_mfderiv_inl`). For `h = q₂` the function
  `h ∘ φ = 0` has Hamiltonian vector field `0`, while `X_h = -∂_{p₂} ≠ 0`
  (`mfderiv_inl_hamiltonianVectorField_ne`): the invertibility hypothesis of
  `TauCeti.SmoothTwoForm.IsSymplecticMap.mfderiv_hamiltonianVectorField_comp` cannot be dropped.
* **The variational equation.** For the oscillator `H = (q² + p²) / 2`, with
  `X_H = p ∂_q - q ∂_p`, the flow `φ_t(q, p) = (q cos t + p sin t, -q sin t + p cos t)` is linear,
  so its differential is its own matrix `R(t)`, and `R' = A R` for
  `A = [[0, 1], [-1, 0]] = DX_H` (`TauCeti.hasDerivAt_oscillatorEvolution_comp`,
  `fderiv_hamiltonianVectorField_oscillator`). Reading the equation with the transpose `Aᵀ` gives
  the opposite rotation `R(-t)` (`hasDerivAt_oscillatorEvolution_neg_comp`).
* **A flow that is not Hamiltonian need not be symplectic.** The field `X = q ∂_q` has the flow
  `φ_t(q, p) = (eᵗ q, p)` (`hasDerivAt_dilationFst`), which pulls `dq ∧ dp` back to
  `eᵗ dq ∧ dp` (`eval₂_mfderiv_dilationFst`), so it is not a symplectic map for `t ≠ 0`
  (`not_isSymplecticMap_dilationFst`); indeed `X` is the Hamiltonian vector field of no function
  (`not_isHamiltonianVectorField_dilationField`). The time-dependent Hamiltonian `H_t = t q` has
  `X_{H_t} = -t ∂_p` (`isHamiltonianVectorField_const_mul_fst`) and the flow
  `Φ_{s,t}(q, p) = (q, p - (t² - s²) / 2)` (`translationFlow_self`, `hasDerivAt_translationFlow`), a
  translation, hence symplectic (`isSymplecticMap_translationFlow`).

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.1.
* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Chapter 3.
-/

public section

noncomputable section

open ContinuousLinearMap Set
open scoped Manifold

namespace TauCeti.Examples.HamiltonianVectorField

/-! ### Nondegeneracy is needed for uniqueness and zeros -/

/-- For the zero two-form on the plane, every vector field is a Hamiltonian vector field of every
constant function. -/
theorem isHamiltonianVectorField_zero_const (c : ℝ)
    (X : (x : ℝ × ℝ) → TangentSpace 𝓘(ℝ, ℝ × ℝ) x) :
    (0 : SmoothTwoForm 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ)).IsHamiltonianVectorField (fun _ ↦ c) X :=
  SmoothTwoForm.isHamiltonianVectorField_iff.2 fun x v ↦ by
    simp [SmoothBundleForm.eval₂_apply, mvfderiv_const]

/-- **Uniqueness needs nondegeneracy.** For the zero two-form, `∂_q` and `0` are two different
Hamiltonian vector fields of the same constant function. -/
theorem exists_isHamiltonianVectorField_zero_ne :
    ∃ X Y : (x : ℝ × ℝ) → TangentSpace 𝓘(ℝ, ℝ × ℝ) x,
      (0 : SmoothTwoForm 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ)).IsHamiltonianVectorField (fun _ ↦ 0) X ∧
      (0 : SmoothTwoForm 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ)).IsHamiltonianVectorField (fun _ ↦ 0) Y ∧
      X ≠ Y :=
  ⟨fun _ ↦ ((1 : ℝ), (0 : ℝ)), fun _ ↦ ((0 : ℝ), (0 : ℝ)), isHamiltonianVectorField_zero_const 0 _,
    isHamiltonianVectorField_zero_const 0 _, fun h ↦ by
      have h0 := congrArg Prod.fst (congrFun h 0)
      simp at h0⟩

/-- **Zeros need nondegeneracy.** For the zero two-form, the field `∂_q` is a Hamiltonian vector
field of a constant function, whose differential vanishes everywhere, but `∂_q` vanishes
nowhere. -/
theorem exists_isHamiltonianVectorField_zero_ne_zero :
    ∃ (f : ℝ × ℝ → ℝ) (X : (x : ℝ × ℝ) → TangentSpace 𝓘(ℝ, ℝ × ℝ) x),
      (0 : SmoothTwoForm 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ)).IsHamiltonianVectorField f X ∧
      ∀ x, mvfderiv 𝓘(ℝ, ℝ × ℝ) f x = 0 ∧ X x ≠ 0 :=
  ⟨fun _ ↦ 0, fun _ ↦ ((1 : ℝ), (0 : ℝ)), isHamiltonianVectorField_zero_const 0 _,
    fun _ ↦ ⟨mvfderiv_const 0, fun h ↦ by
      have h1 := congrArg Prod.fst h
      -- The zero tangent vector is the zero of the model space `ℝ²`.
      exact one_ne_zero h1⟩⟩

/-! ### The Leibniz rule -/

/-- The position coordinate `q` has the Hamiltonian vector field `X_q = -∂_p`. -/
theorem isHamiltonianVectorField_fst :
    (stdSymplecticForm (V := ℝ)).constSmooth.IsHamiltonianVectorField (fun x ↦ x.1)
      (fun _ ↦ ((0 : ℝ), (-1 : ℝ))) :=
  (SymplecticForm.isNondegenerate_constSmooth _).isHamiltonianVectorField_iff_eq.2 <|
    funext fun x ↦ by
      rw [SymplecticForm.hamiltonianVectorField_constSmooth]
      exact (stdSymplecticForm_hamiltonianVectorField_fst x).symm

/-- The momentum coordinate `p` has the Hamiltonian vector field `X_p = ∂_q`. -/
theorem isHamiltonianVectorField_snd :
    (stdSymplecticForm (V := ℝ)).constSmooth.IsHamiltonianVectorField (fun x ↦ x.2)
      (fun _ ↦ ((1 : ℝ), (0 : ℝ))) :=
  (SymplecticForm.isNondegenerate_constSmooth _).isHamiltonianVectorField_iff_eq.2 <|
    funext fun x ↦ by
      rw [SymplecticForm.hamiltonianVectorField_constSmooth]
      exact (stdSymplecticForm_hamiltonianVectorField_snd x).symm

/-- **The Leibniz rule on the plane.** The product `qp` has the Hamiltonian vector field
`X_{qp} = q X_p + p X_q = q ∂_q - p ∂_p`. -/
theorem isHamiltonianVectorField_fst_mul_snd :
    (stdSymplecticForm (V := ℝ)).constSmooth.IsHamiltonianVectorField (fun x ↦ x.1 * x.2)
      (fun x ↦ (x.1, -x.2)) := by
  have hX : (fun x : ℝ × ℝ ↦ ((x.1, -x.2) : ℝ × ℝ)) =
      (fun x : ℝ × ℝ ↦ x.1) • (fun _ ↦ ((1 : ℝ), (0 : ℝ))) +
        (fun x : ℝ × ℝ ↦ x.2) • (fun _ ↦ ((0 : ℝ), (-1 : ℝ))) := by
    funext x
    ext <;> simp
  rw [hX]
  exact isHamiltonianVectorField_fst.mul isHamiltonianVectorField_snd
    differentiable_fst.mdifferentiable differentiable_snd.mdifferentiable

/-- **The canonical relation.** The Poisson bracket of the coordinates is `{q, p} = 1`. -/
theorem poissonBracket_fst_snd :
    (stdSymplecticForm (V := ℝ)).constSmooth.poissonBracket (fun x ↦ x.1) (fun x ↦ x.2) =
      fun _ ↦ 1 := by
  funext x
  rw [SymplecticForm.poissonBracket_constSmooth]
  simpa using stdSymplecticForm_poissonBracket_inner_fst_inner_snd (1 : ℝ) (1 : ℝ) x

/-! ### Conservation of energy needs a preconnected set of times -/

/-- **Conservation of energy needs a preconnected set of times.** For `H(q, p) = p`, whose
Hamiltonian vector field is `∂_q`, the curve equal to `(t, 0)` for `t < 3 / 2` and to `(t, 5)`
otherwise is an integral curve of `∂_q` on `(0, 1) ∪ (2, 3)`, and `H` takes the value `0` at the
time `1 / 2` and the value `5` at the time `5 / 2`. -/
theorem exists_isMIntegralCurveOn_snd_ne :
    ∃ γ : ℝ → ℝ × ℝ, IsMIntegralCurveOn (I := 𝓘(ℝ, ℝ × ℝ)) γ (fun _ ↦ ((1 : ℝ), (0 : ℝ)))
      (Ioo 0 1 ∪ Ioo 2 3) ∧ (γ (1 / 2)).2 = 0 ∧ (γ (5 / 2)).2 = 5 := by
  refine ⟨fun t ↦ if t < 3 / 2 then (t, 0) else (t, 5),
    isMIntegralCurveOn_iff_isIntegralCurveOn.2 fun t ht ↦ ?_, by norm_num, by norm_num⟩
  -- Near each time of the two intervals the curve is a horizontal line.
  have hloc : ∀ c : ℝ, (∀ᶠ u in nhds t,
      (if u < 3 / 2 then ((u, 0) : ℝ × ℝ) else (u, 5)) = (u, c)) →
      HasDerivWithinAt (fun u ↦ if u < 3 / 2 then ((u, 0) : ℝ × ℝ) else (u, 5))
        ((1 : ℝ), (0 : ℝ)) (Ioo 0 1 ∪ Ioo 2 3) t := fun c hc ↦
    (((hasDerivAt_id t).prodMk (hasDerivAt_const t c)).congr_of_eventuallyEq hc).hasDerivWithinAt
  rcases ht with ht | ht
  · exact hloc 0 (Filter.eventually_of_mem (Iio_mem_nhds (by linarith [ht.2] : t < 3 / 2))
      fun u hu ↦ by simp [mem_Iio.1 hu])
  · exact hloc 5 (Filter.eventually_of_mem (Ioi_mem_nhds (by linarith [ht.1] : 3 / 2 < t))
      fun u hu ↦ by simp [not_lt.2 (le_of_lt (mem_Ioi.1 hu))])

/-! ### Transport needs invertible differentials -/

/-- The symplectic form `dq₁ ∧ dp₁ + dq₂ ∧ dp₂` of `ℝ⁴`, written `(ℝ × ℝ) × (ℝ × ℝ)` with
coordinates `((q₁, p₁), (q₂, p₂))`. -/
abbrev prodStdSymplecticForm : SmoothTwoForm 𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ)) ((ℝ × ℝ) × (ℝ × ℝ)) :=
  ((stdSymplecticForm (V := ℝ)).prod (stdSymplecticForm (V := ℝ))).constSmooth

/-- The inclusion `inl : (q₁, p₁) ↦ ((q₁, p₁), (0, 0))` of the plane into `ℝ⁴` is a symplectic
map. -/
theorem isSymplecticMap_inl :
    (stdSymplecticForm (V := ℝ)).constSmooth.IsSymplecticMap prodStdSymplecticForm
      (inl ℝ (ℝ × ℝ) (ℝ × ℝ)) := by
  have key : ∀ a b : ℝ × ℝ,
      (stdSymplecticForm (V := ℝ)).prod (stdSymplecticForm (V := ℝ)) (inl ℝ (ℝ × ℝ) (ℝ × ℝ) a)
        (inl ℝ (ℝ × ℝ) (ℝ × ℝ) b) = stdSymplecticForm a b := fun a b ↦ by
    simp
  exact SmoothTwoForm.isSymplecticMap_iff.2 fun x v w ↦
    (SymplecticForm.eval₂_constSmooth_mfderiv_continuousLinearMap _ (inl ℝ (ℝ × ℝ) (ℝ × ℝ)) x v
      w).trans
      ((key v w).trans (SymplecticForm.constSmooth_apply _ x v w).symm)

/-- The Hamiltonian vector field of `h = q₂` on `ℝ⁴` is `-∂_{p₂}`. -/
theorem hamiltonianVectorField_prodStdSymplecticForm_fst_comp_snd :
    prodStdSymplecticForm.hamiltonianVectorField (fun y ↦ y.2.1) =
      fun _ ↦ (((0 : ℝ), (0 : ℝ)), ((0 : ℝ), -1)) := by
  refine ((SymplecticForm.isNondegenerate_constSmooth _).isHamiltonianVectorField_iff_eq.1
    (SmoothTwoForm.isHamiltonianVectorField_iff.2 fun x v ↦ ?_)).symm
  have hd : fderiv ℝ (fun y : (ℝ × ℝ) × (ℝ × ℝ) ↦ y.2.1) x =
      (fst ℝ ℝ ℝ).comp (snd ℝ (ℝ × ℝ) (ℝ × ℝ)) :=
    ((fst ℝ ℝ ℝ).comp (snd ℝ (ℝ × ℝ) (ℝ × ℝ))).fderiv
  refine (SymplecticForm.constSmooth_apply _ x _ v).trans ?_
  -- Both sides are the coordinate `q₂` of `v`.
  rw [mvfderiv_eq_fderiv_apply, hd]
  obtain ⟨⟨q₁, p₁⟩, q₂, p₂⟩ := v
  simp

/-- **Transport needs invertible differentials.** For `h = q₂` on `ℝ⁴`, the differential of the
inclusion `φ = inl` of the plane does not carry the Hamiltonian vector field of `h ∘ φ = 0` to that
of `h`, which is `-∂_{p₂} ≠ 0`. -/
theorem mfderiv_inl_hamiltonianVectorField_ne (x : ℝ × ℝ) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ)) (inl ℝ (ℝ × ℝ) (ℝ × ℝ)) x
        ((stdSymplecticForm (V := ℝ)).constSmooth.hamiltonianVectorField
          ((fun y : (ℝ × ℝ) × (ℝ × ℝ) ↦ y.2.1) ∘ inl ℝ (ℝ × ℝ) (ℝ × ℝ)) x) ≠
      prodStdSymplecticForm.hamiltonianVectorField (fun y ↦ y.2.1) (inl ℝ (ℝ × ℝ) (ℝ × ℝ) x) := by
  have hcomp : (fun y : (ℝ × ℝ) × (ℝ × ℝ) ↦ y.2.1) ∘ inl ℝ (ℝ × ℝ) (ℝ × ℝ) =
      fun _ ↦ (0 : ℝ) := by
    funext _
    simp
  rw [hcomp, SmoothTwoForm.hamiltonianVectorField_const,
    hamiltonianVectorField_prodStdSymplecticForm_fst_comp_snd]
  intro h
  have h2 := congrArg (fun z : (ℝ × ℝ) × (ℝ × ℝ) ↦ z.2.2) h
  -- The zero tangent vector is the zero of the model space `ℝ⁴`.
  have h0 : (0 : TangentSpace 𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ)) (inl ℝ (ℝ × ℝ) (ℝ × ℝ) x)).2.2 = 0 := rfl
  rw [Pi.zero_apply, map_zero, h0] at h2
  norm_num at h2

/-- The differential of the inclusion `inl` of the plane into `ℝ⁴` is not invertible. -/
theorem not_isInvertible_mfderiv_inl (x : ℝ × ℝ) :
    ¬ (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ)) (inl ℝ (ℝ × ℝ) (ℝ × ℝ)) x).IsInvertible := by
  rintro ⟨e, he⟩
  -- The vector `∂_{q₂}` is not in the range of the differential `v ↦ (v, 0)`.
  obtain ⟨v, hv⟩ := e.surjective (((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ)))
  have hv' := congrArg (fun z : (ℝ × ℝ) × (ℝ × ℝ) ↦ z.2.1) hv
  rw [← ContinuousLinearEquiv.coe_coe, he, (inl ℝ (ℝ × ℝ) (ℝ × ℝ)).mfderiv_eq] at hv'
  -- The second component of `inl v = (v, 0)` is `0`, so `hv'` reads `0 = 1`.
  rw [inl_apply] at hv'
  exact zero_ne_one hv'

/-! ### The variational equation of the oscillator -/

/-- The Hamiltonian vector field `X_H(q, p) = (p, -q)` of the oscillator `H = (q² + p²) / 2` has
the constant derivative `A = [[0, 1], [-1, 0]]`. -/
theorem fderiv_hamiltonianVectorField_oscillator (x : ℝ × ℝ) :
    fderiv ℝ ((stdSymplecticForm (V := ℝ)).hamiltonianVectorField
      (fun y ↦ (y.1 ^ 2 + y.2 ^ 2) / 2)) x = (snd ℝ ℝ ℝ).prod (-fst ℝ ℝ ℝ) := by
  rw [show (stdSymplecticForm (V := ℝ)).hamiltonianVectorField (fun y ↦ (y.1 ^ 2 + y.2 ^ 2) / 2) =
      (snd ℝ ℝ ℝ).prod (-fst ℝ ℝ ℝ) from
    funext fun y ↦ (stdSymplecticForm_hamiltonianVectorField_oscillator y).trans (by simp)]
  exact ((snd ℝ ℝ ℝ).prod (-fst ℝ ℝ ℝ)).fderiv

/-- **The transposed equation rotates the other way.** `t ↦ R(-t)`, the oscillator flow run
backwards, solves the transposed equation `R' = Aᵀ R`. -/
theorem hasDerivAt_oscillatorEvolution_neg_comp (t : ℝ) :
    HasDerivAt (fun s ↦ oscillatorEvolution (-s))
      (((-snd ℝ ℝ ℝ).prod (fst ℝ ℝ ℝ)).comp (oscillatorEvolution (-t))) t := by
  have h := (hasDerivAt_oscillatorEvolution_comp (-t)).scomp t (hasDerivAt_neg t)
  refine h.congr_deriv (ContinuousLinearMap.ext fun x ↦ Prod.ext ?_ ?_) <;>
    simp [oscillatorEvolution_apply]

/-! ### A flow that is not Hamiltonian need not be symplectic -/

/-- The field `X = q ∂_q` on the plane. -/
abbrev dilationField (x : ℝ × ℝ) : TangentSpace 𝓘(ℝ, ℝ × ℝ) x :=
  (x.1, 0)

/-- The flow `φ_t(q, p) = (eᵗ q, p)` of the field `q ∂_q`. -/
abbrev dilationFst (t : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
  (Real.exp t • fst ℝ ℝ ℝ).prod (snd ℝ ℝ ℝ)

/-- `φ_t(q, p) = (eᵗ q, p)` is the flow of `X = q ∂_q`. -/
theorem hasDerivAt_dilationFst (t : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun s ↦ dilationFst s x) ((dilationFst t x).1, 0) t := by
  simpa using ((Real.hasDerivAt_exp t).mul_const x.1).prodMk (hasDerivAt_const t x.2)

/-- The flow of `q ∂_q` pulls `dq ∧ dp` back to `eᵗ dq ∧ dp`. -/
theorem eval₂_mfderiv_dilationFst (t : ℝ) (x : ℝ × ℝ) (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ) x) :
    (stdSymplecticForm (V := ℝ)).constSmooth.eval₂ (dilationFst t x)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (dilationFst t) x v)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (dilationFst t) x w) =
      Real.exp t * (stdSymplecticForm (V := ℝ)).constSmooth.eval₂ x v w := by
  have key : ∀ a b : ℝ × ℝ, stdSymplecticForm (dilationFst t a) (dilationFst t b) =
      Real.exp t * stdSymplecticForm a b := fun a b ↦ by
    simp [stdSymplecticForm_apply, mul_sub, mul_left_comm, mul_assoc]
  exact (SymplecticForm.eval₂_constSmooth_mfderiv_continuousLinearMap _ (dilationFst t) x v w).trans
    ((key v w).trans (congrArg (Real.exp t * ·) (SymplecticForm.constSmooth_apply _ x v w)).symm)

/-- The time-`t` flow of `q ∂_q` is not a symplectic map for `t ≠ 0`. -/
theorem not_isSymplecticMap_dilationFst {t : ℝ} (ht : t ≠ 0) :
    ¬ (stdSymplecticForm (V := ℝ)).constSmooth.IsSymplecticMap
      (stdSymplecticForm (V := ℝ)).constSmooth (dilationFst t) := by
  intro h
  have h1 := (eval₂_mfderiv_dilationFst t 0 ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))).symm.trans
    (SmoothTwoForm.isSymplecticMap_iff.1 h 0 _ _)
  rw [eval₂_constSmooth_stdSymplecticForm 0 ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))] at h1
  exact ht (Real.exp_eq_one_iff t |>.1 (by simpa using h1))

/-- Off the axis `q = 0`, a Hamiltonian of `q ∂_q` is differentiable with differential `q dp`. -/
private theorem differentiableAt_of_isHamiltonianVectorField_dilationField {f : ℝ × ℝ → ℝ}
    (hf : (stdSymplecticForm (V := ℝ)).constSmooth.IsHamiltonianVectorField f dilationField)
    {x : ℝ × ℝ} (hx : x.1 ≠ 0) :
    DifferentiableAt ℝ f x ∧ ∀ v : ℝ × ℝ, fderiv ℝ f x v = x.1 * v.2 := by
  have key : ∀ v : ℝ × ℝ, fderiv ℝ f x v = x.1 * v.2 := fun v ↦ by
    have := ((eval₂_constSmooth_stdSymplecticForm x _ v).symm.trans
      (SmoothTwoForm.isHamiltonianVectorField_iff.1 hf x v)).trans (mvfderiv_eq_fderiv_apply f x v)
    simpa using this.symm
  refine ⟨?_, key⟩
  -- Where `f` is not differentiable its differential is `0`, which is not `q dp` for `q ≠ 0`.
  by_contra hd
  have := key ((0 : ℝ), (1 : ℝ))
  rw [fderiv_zero_of_not_differentiableAt hd] at this
  simp only [zero_apply, mul_one] at this
  exact hx this.symm

/-- The field `q ∂_q` is the Hamiltonian vector field of no function `f : ℝ² → ℝ`, differentiable
or not, on `(ℝ², dq ∧ dp)`. -/
theorem not_isHamiltonianVectorField_dilationField (f : ℝ × ℝ → ℝ) :
    ¬ (stdSymplecticForm (V := ℝ)).constSmooth.IsHamiltonianVectorField f dilationField := by
  intro hf
  -- Off the axis `q = 0` a Hamiltonian is constant in `q` and grows like `q p` in `p`; comparing
  -- its values at the corners of `[1, 2] × [0, 1]` gives `2 = 1`.
  have hF := fun x hx ↦ differentiableAt_of_isHamiltonianVectorField_dilationField hf (x := x) hx
  -- Along `q ↦ (q, p)` for `q ∈ [1, 2]`, the derivative of `f` vanishes.
  have hq : ∀ p : ℝ, f (2, p) = f (1, p) := fun p ↦ by
    have h := sub_eq_mul_of_fderiv_apply_eq ((0 : ℝ), p) ((1 : ℝ), (0 : ℝ)) (c := 0)
      (by norm_num : (1 : ℝ) < 2) fun s hs ↦ by
        have h := hF (((0 : ℝ), p) + s • ((1 : ℝ), (0 : ℝ)))
          (by simpa using (by linarith [hs.1] : (0 : ℝ) < s).ne')
        exact ⟨h.1, by rw [h.2]; simp⟩
    simpa [sub_eq_zero] using h
  -- Along `p ↦ (q, p)` for `p ∈ [0, 1]` and `q ≥ 1`, the derivative of `f` is `q`.
  have hp : ∀ q : ℝ, 1 ≤ q → f (q, 1) - f (q, 0) = q := fun q hq ↦ by
    have h := sub_eq_mul_of_fderiv_apply_eq (q, (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) (c := q)
      (by norm_num : (0 : ℝ) < 1) fun s _ ↦ by
        have h := hF ((q, (0 : ℝ)) + s • ((0 : ℝ), (1 : ℝ)))
          (by simpa using (by linarith : (0 : ℝ) < q).ne')
        exact ⟨h.1, by rw [h.2]; simp⟩
    simpa using h
  have h2 := hp 2 (by norm_num)
  rw [hq 1, hq 0, hp 1 le_rfl] at h2
  norm_num at h2

/-- The time-dependent Hamiltonian `H_t(q, p) = t q` has the Hamiltonian vector field
`X_{H_t} = -t ∂_p`. -/
theorem isHamiltonianVectorField_const_mul_fst (t : ℝ) :
    (stdSymplecticForm (V := ℝ)).constSmooth.IsHamiltonianVectorField (fun x ↦ t * x.1)
      (fun _ ↦ ((0 : ℝ), -t)) := by
  have hX : (fun _ : ℝ × ℝ ↦ ((0 : ℝ), -t)) = t • fun _ ↦ ((0 : ℝ), (-1 : ℝ)) := by
    funext x
    ext <;> simp
  rw [hX]
  exact isHamiltonianVectorField_fst.const_smul t

/-- The flow `Φ_{s,t}(q, p) = (q, p - (t² - s²) / 2)` of the time-dependent Hamiltonian
`H_t = t q`, from time `s` to time `t`: a translation. -/
abbrev translationFlow (s t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  x + ((0 : ℝ), -(t ^ 2 - s ^ 2) / 2)

/-- The flow of `H_t = t q` from time `s` to time `s` is the identity. -/
theorem translationFlow_self (s : ℝ) (x : ℝ × ℝ) : translationFlow s s x = x := by
  simp

/-- The flow of `H_t = t q` moves along `X_{H_t} = -t ∂_p`. -/
theorem hasDerivAt_translationFlow (s t : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun u ↦ translationFlow s u x) ((0 : ℝ), -t) t := by
  have h : HasDerivAt (fun u : ℝ ↦ -(u ^ 2 - s ^ 2) / 2) (-t) t :=
    ((((hasDerivAt_pow 2 t).sub_const (s ^ 2)).neg).div_const 2).congr_deriv (by ring)
  exact ((hasDerivAt_const t (0 : ℝ)).prodMk h).const_add x

/-- **The flow of `H_t = t q` is symplectic**: it is a translation, hence a symplectic map at all
times. -/
theorem isSymplecticMap_translationFlow (s t : ℝ) :
    (stdSymplecticForm (V := ℝ)).constSmooth.IsSymplecticMap
      (stdSymplecticForm (V := ℝ)).constSmooth (translationFlow s t) := by
  have h : translationFlow s t =
      fun x ↦ Multiplicative.ofAdd (((0 : ℝ), -(t ^ 2 - s ^ 2) / 2) : ℝ × ℝ) • x := by
    funext x
    rw [← toAdd_vadd, toAdd_ofAdd, vadd_eq_add, add_comm]
  rw [h]
  exact (SmoothTwoForm.isSymplecticMap_iff_mpullback_eq _).2
    (SymplecticForm.mpullback_smul_multiplicative_constSmooth _ _)

end TauCeti.Examples.HamiltonianVectorField
