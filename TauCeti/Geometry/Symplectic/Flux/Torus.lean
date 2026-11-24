/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Torus
public import TauCeti.Geometry.Manifold.DeRham.Torus
public import TauCeti.Geometry.Symplectic.Flux
public import TauCeti.Geometry.Symplectic.Flux.Endpoint
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Topology.Covering.AddCircle
import TauCeti.Geometry.Manifold.Instances.AddCircle.Lift

/-!
# The flux of the translations of a torus, and the flux group of the two-torus

For a finite family of positive periods `p i`, let `Tⁿ = ∀ i, AddCircle (p i)` be the torus with
coordinate time forms `dt_i` (`TauCeti.torusTimeForm p i`), and let `φ_t (x) = x + [t v]` be the
translation diffeotopy along a real vector `v` (`TauCeti.torusTranslationDiffeotopy p v`). Its
velocity is the constant field `v` and each `φ_t` has derivative the identity. So for a two-form
`σ` with constant coefficients `β` in the product charts, each `φ_t` preserves `σ`, and the flux
form `∫₀¹ φ_t^* (ι_v σ) dt` is the constant one-form `ι_v β = β (v, ·)`
(`TauCeti.fluxForm_torusTranslationDiffeotopy_apply`).

On the two-torus with the area form `A dt_0 ∧ dt_1` this gives

`Flux(φ) = A (v 0 [dt_1] - v 1 [dt_0])` in `H¹_dR(T²)`

(`TauCeti.flux_torusTranslationDiffeotopy_smul_torusVolumeForm`). With unit periods,
coordinates `(x, y)` and `v = a ∂_x + b ∂_y`, this is `A (a [dy] - b [dx])`: the translation in the
`x`-direction has flux `A [dy]` and that in the `y`-direction has flux `-A [dx]`. The diffeotopy is
a loop exactly when `v` lies in the period lattice
(`TauCeti.final_torusTranslationDiffeotopy_eq_refl_iff`), and for `A ≠ 0` its flux vanishes only
when `v = 0`, since `[dt_0]` and `[dt_1]` are linearly independent. Integrated around the two
coordinate circles, the flux form has periods `-A v 1 p 0` and `A v 0 p 1`
(`TauCeti.pathIntegral_fluxForm_torusTranslationDiffeotopy_smul_torusVolumeForm_update`); for unit
periods and integer `v` these are integer multiples of `A`. So the fluxes of the translation loops
of the unit torus are exactly the classes `A (m [dx] + n [dy])` with `m, n ∈ ℤ`. For arbitrary
periods, every class `A (m p_1 [dt_0] + n p_0 [dt_1])` with `m, n ∈ ℤ` is the flux of a translation
loop all of whose maps preserve the area form
(`TauCeti.exists_final_eq_refl_and_flux_smul_torusVolumeForm_eq`). These classes are the total area
`A p_0 p_1` times the integer combinations of the classes `[dt_i / p_i]`, which integrate to `1`
around the `i`-th coordinate circle and to `0` around the other.

Conversely, every loop of `Tⁿ` has the flux of a translation loop. Let `φ_t` be a diffeotopy with
`φ_1 = id`. Its displacement `(t, x) ↦ φ_t x - x` is a smooth map `[0, 1] × Tⁿ → Tⁿ` vanishing at
time zero, so it lifts to a smooth `D : [0, 1] × Tⁿ → ℝⁿ` with `D (0, x) = 0`. At time one the lift
takes values in the period lattice, a discrete set, so on the connected torus it is a constant
lattice vector `v`. The straight-line homotopy

`G ((x, t), s) = x + [(1 - s) D (t, x) + s t v]`

joins the motion of `φ_t` to that of the translation loop along `v` and fixes both time ends, since
`D (0, x) = 0` and `D (1, x) = v`. Its intermediate maps need be neither diffeomorphisms nor
`σ`-preserving, and the flux form is invariant under such homotopies
(`TauCeti.Diffeotopy.fluxForm_sub_fluxForm_mem_exactForms`). Hence for every closed two-form `σ` the
flux of `φ_t` is that of the translation loop along `v`
(`TauCeti.Diffeotopy.exists_flux_torusTranslationDiffeotopy_eq_flux`).

On the two-torus with the area form `A dt_0 ∧ dt_1` the two directions together compute the flux
group, the set of fluxes of the loops preserving the area form at every time:

`Γ = {A (m p_1 [dt_0] + n p_0 [dt_1]) | m, n ∈ ℤ}`

(`TauCeti.mem_fluxGroup_smul_torusVolumeForm_iff`). For unit periods this is
`A (ℤ [dx] + ℤ [dy])`, the area `A` times the integer combinations of the classes `[dx]` and `[dy]`
dual to the two coordinate circles. The computation uses only the loops themselves, not the
topology of the group of area-preserving diffeomorphisms.

## Main results

* `TauCeti.fluxForm_torusTranslationDiffeotopy_apply`: for a constant-coefficient two-form `β`,
  the flux form of the translation along `v` is `β (v, ·)`.
* `TauCeti.timeSlice_torusTranslationDiffeotopy_mem_diffeomorphStabilizer`,
  `TauCeti.final_torusTranslationDiffeotopy_mem_diffeomorphStabilizer`: translations preserve
  constant-coefficient two-forms.
* `TauCeti.fluxForm_torusTranslationDiffeotopy_smul_torusVolumeForm`,
  `TauCeti.flux_torusTranslationDiffeotopy_smul_torusVolumeForm`: the flux form and the flux of a
  translation of the two-torus for the area form `A dt_0 ∧ dt_1`.
* `TauCeti.flux_torusTranslationDiffeotopy_smul_torusVolumeForm_eq_zero_iff`: this flux vanishes
  exactly when `A = 0` or `v = 0`.
* `TauCeti.pathIntegral_fluxForm_torusTranslationDiffeotopy_smul_torusVolumeForm_update`: its
  periods along the coordinate circles.
* `TauCeti.exists_final_eq_refl_and_flux_smul_torusVolumeForm_eq`: every class
  `A (m p_1 [dt_0] + n p_0 [dt_1])` with `m n : ℤ` is the flux of a loop of area-preserving
  diffeomorphisms based at the identity.
* `TauCeti.Diffeotopy.exists_fluxForm_torusTranslationDiffeotopy_sub_mem_exactForms`,
  `TauCeti.Diffeotopy.exists_flux_torusTranslationDiffeotopy_eq_flux`: every loop of `Tⁿ` has,
  for every closed two-form, the flux of the translation loop along a lattice vector.
* `TauCeti.mem_fluxGroup_smul_torusVolumeForm_iff`: the flux group of `A dt_0 ∧ dt_1` consists of
  the classes `A (m p_1 [dt_0] + n p_0 [dt_1])` with `m n : ℤ`.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the flux homomorphism, and the flux of the translations of
  the torus).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)] (v : ι → ℝ)

section Constant

variable {σ : SmoothForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) ℝ 2}
  {β : (ι → ℝ) [⋀^Fin 2]→L[ℝ] ℝ}

/-- **The flux form of a translation.** For a two-form `σ` on the torus with constant coefficients
`β`, the flux form of the translation diffeotopy along `v` is the constant one-form `β (v, ·)`, the
contraction of `β` with `v`. -/
theorem fluxForm_torusTranslationDiffeotopy_apply
    (hσ : ∀ x, (σ.val x : (ι → ℝ) [⋀^Fin 2]→L[ℝ] ℝ) = β) (x : ∀ i, AddCircle (p i)) :
    ((torusTranslationDiffeotopy p v).fluxForm σ).val x = β.curryLeft v := by
  rw [Diffeotopy.fluxForm_apply]
  -- At every time the integrand is `β (v, ·)`: the velocity is `v`, the spatial derivative is the
  -- identity and `σ` has constant coefficients.
  simp only [mfderiv_cylinderMap_torusTranslationDiffeotopy_apply_one,
    mfderiv_cylinderMap_torusTranslationDiffeotopy_comp_inl, hσ]
  refine (intervalIntegral.integral_const (E := (ι → ℝ) [⋀^Fin 1]→L[ℝ] ℝ) (a := 0) (b := 1)
    ((β.curryLeft v).compContinuousLinearMap (ContinuousLinearMap.id ℝ (ι → ℝ)))).trans ?_
  rw [sub_zero, one_smul]
  -- Composing with the identity map changes nothing.
  ext w
  simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

/-- Every time slice of a translation diffeotopy, a translation of the torus, preserves every
two-form with constant coefficients. -/
theorem timeSlice_torusTranslationDiffeotopy_mem_diffeomorphStabilizer
    (hσ : ∀ x, (σ.val x : (ι → ℝ) [⋀^Fin 2]→L[ℝ] ℝ) = β) (t : unitInterval) :
    (torusTranslationDiffeotopy p v).timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ := by
  have hslice : ⇑((torusTranslationDiffeotopy (n := ∞) p v).timeSlice t) =
      (· + fun i ↦ (((t : ℝ) * v i : ℝ) : AddCircle (p i))) :=
    funext fun x ↦ (Diffeotopy.timeSlice_apply _ t x).trans (torusTranslationDiffeotopy_apply p v _)
  refine SmoothForm.mem_diffeomorphStabilizer_iff_forall.2 fun x ↦
    ContinuousAlternatingMap.ext fun w ↦ ?_
  rw [TauCeti.mpullback_apply, hslice, AddCircle.mfderiv_pi_add_right]
  -- Both sides evaluate the constant coefficient `β` on `w`.
  exact (DFunLike.congr_fun (hσ _) _).trans (DFunLike.congr_fun (hσ x) w).symm

/-- The final diffeomorphism of a translation diffeotopy, a translation of the torus, preserves
every two-form with constant coefficients. -/
theorem final_torusTranslationDiffeotopy_mem_diffeomorphStabilizer
    (hσ : ∀ x, (σ.val x : (ι → ℝ) [⋀^Fin 2]→L[ℝ] ℝ) = β) :
    (torusTranslationDiffeotopy p v).final ∈ SmoothForm.diffeomorphStabilizer σ := by
  rw [Diffeotopy.final_def]
  exact timeSlice_torusTranslationDiffeotopy_mem_diffeomorphStabilizer p v hσ 1

end Constant

section Loop

/-- The displacement `(t, x) ↦ φ_t x - x` of a loop of the torus lifts to smooth real coordinates
`D i` vanishing at time zero, whose values at time one form a lattice vector `v` independent of the
point. -/
private theorem Diffeotopy.exists_torus_displacement_lift
    (Φ : Diffeotopy (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞ (∀ i, AddCircle (p i)))
    (hΦ : Φ.final = 1) :
    ∃ (D : ι → unitInterval × (∀ i, AddCircle (p i)) → ℝ) (v : ι → ℝ),
      (∀ i, ContMDiff ((𝓡∂ 1).prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) 𝓘(ℝ) ∞ (D i)) ∧
      (∀ i q, Φ q i = q.2 i + D i q) ∧ (∀ i x, D i (0, x) = 0) ∧ (∀ i x, D i (1, x) = v i) ∧
      ∀ i, v i ∈ AddSubgroup.zmultiples (p i) := by
  have hg (i : ι) : ContMDiff ((𝓡∂ 1).prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) 𝓘(ℝ) ∞
      fun q : unitInterval × (∀ i, AddCircle (p i)) ↦ Φ q i - q.2 i :=
    (contMDiff_apply.comp Φ.contMDiff).sub (contMDiff_apply.comp contMDiff_snd)
  choose D hD hDg hD₀ using fun i ↦
    AddCircle.exists_contMDiff_lift_unitInterval_prod (f := fun _ ↦ (0 : ℝ)) (hg i)
      continuous_const fun x ↦ by simp [Φ.apply_zero x]
  have hfin (x : ∀ i, AddCircle (p i)) : Φ (1, x) = x := by
    rw [← Φ.final_apply, hΦ, Diffeomorph.one_apply]
  -- At time one the lift takes values in the discrete fibre over `0`, so it is constant.
  have hconst (i : ι) (x : ∀ i, AddCircle (p i)) : D i (1, x) = D i (1, 0) :=
    (AddCircle.isCoveringMap_coe (p i)).const_of_comp
      ((hD i).continuous.comp (Continuous.prodMk_right 1))
      (fun a a' ↦ by simp only [Function.comp_apply, ← hDg, hfin, sub_self]) x 0
  refine ⟨D, fun i ↦ D i (1, 0), hD, fun i q ↦ ?_, hD₀, hconst, fun i ↦ ?_⟩
  · rw [← hDg, add_sub_cancel]
  · rw [AddSubgroup.mem_zmultiples_iff, ← AddCircle.coe_eq_zero_iff, ← hDg, hfin, sub_self]

/-- **Loops of the torus have the flux form of a translation loop.** For every diffeotopy `φ_t` of
the torus `Tⁿ` with `φ_1 = id` there is a vector `v` of the period lattice such that, for every
closed two-form `σ`, the flux forms of `φ_t` and of the translation loop along `v` differ by an
exact form. The intermediate maps of `φ_t` need not preserve `σ`. -/
theorem Diffeotopy.exists_fluxForm_torusTranslationDiffeotopy_sub_mem_exactForms
    (Φ : Diffeotopy (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞ (∀ i, AddCircle (p i)))
    (hΦ : Φ.final = 1) :
    ∃ v : ι → ℝ, (∀ i, v i ∈ AddSubgroup.zmultiples (p i)) ∧
      ∀ σ : SmoothForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) ℝ 2,
        SmoothForm.IsClosed σ →
        (torusTranslationDiffeotopy p v).fluxForm σ - Φ.fluxForm σ ∈
          exactForms (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) 1 := by
  obtain ⟨D, v, hD, hΦD, hD₀, hD₁, hv⟩ := Φ.exists_torus_displacement_lift p hΦ
  refine ⟨v, hv, fun σ hσ ↦ ?_⟩
  have hs : ContMDiff (((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod (𝓡∂ 1)).prod (𝓡∂ 1)) 𝓘(ℝ) ∞
      fun q : ((∀ i, AddCircle (p i)) × unitInterval) × unitInterval ↦ (q.2 : ℝ) :=
    contMDiff_subtypeVal_Icc.comp contMDiff_snd
  have ht : ContMDiff (((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod (𝓡∂ 1)).prod (𝓡∂ 1)) 𝓘(ℝ) ∞
      fun q : ((∀ i, AddCircle (p i)) × unitInterval) × unitInterval ↦ (q.1.2 : ℝ) :=
    contMDiff_subtypeVal_Icc.comp (contMDiff_snd.comp contMDiff_fst)
  have hD' (i : ι) : ContMDiff (((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod (𝓡∂ 1)).prod (𝓡∂ 1))
      𝓘(ℝ) ∞ fun q : ((∀ i, AddCircle (p i)) × unitInterval) × unitInterval ↦
        D i (q.1.2, q.1.1) :=
    (hD i).comp ((contMDiff_snd.comp contMDiff_fst).prodMk (contMDiff_fst.comp contMDiff_fst))
  -- The straight-line homotopy `x + [(1 - s) D (t, x) + s t v]` from the motion of `Φ` to the
  -- translation motion fixes both time ends.
  refine Φ.fluxForm_sub_fluxForm_mem_exactForms hσ
    (G := fun q i ↦ q.1.1 i +
      (((1 - (q.2 : ℝ)) * D i (q.1.2, q.1.1) + q.2 * (q.1.2 * v i) : ℝ) : AddCircle (p i)))
    (contMDiff_pi_iff.2 fun i ↦ (contMDiff_apply.comp (contMDiff_fst.comp contMDiff_fst)).add
      ((AddCircle.contMDiff_coe (p i) ∞).comp
        (((contMDiff_const.sub hs).mul (hD' i)).add (hs.mul (ht.mul contMDiff_const)))))
    (fun q ↦ ?_) (fun q ↦ ?_) (fun x s ↦ ?_) (fun x s ↦ ?_) <;> funext i
  · simp [Diffeotopy.cylinderMap_apply, hΦD]
  · simp
  · simp [hD₀]
  · rw [Diffeotopy.final_apply, hΦD, hD₁]
    congr 2
    push_cast
    ring

/-- **Loops of the torus have the flux of a translation loop.** For every diffeotopy `φ_t` of the
torus `Tⁿ` with `φ_1 = id` there is a vector `v` of the period lattice such that, for every closed
two-form `σ`, the translation loop along `v` has the same flux as `φ_t`. -/
theorem Diffeotopy.exists_flux_torusTranslationDiffeotopy_eq_flux
    (Φ : Diffeotopy (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞ (∀ i, AddCircle (p i)))
    (hΦ : Φ.final = 1) :
    ∃ v : ι → ℝ, (∀ i, v i ∈ AddSubgroup.zmultiples (p i)) ∧
      ∀ (σ : closedForms (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) 2)
        (h : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
        (h' : (torusTranslationDiffeotopy p v).final ∈ SmoothForm.diffeomorphStabilizer σ.val),
        (torusTranslationDiffeotopy p v).flux σ h' = Φ.flux σ h := by
  obtain ⟨v, hv, hσ⟩ := Φ.exists_fluxForm_torusTranslationDiffeotopy_sub_mem_exactForms p hΦ
  refine ⟨v, hv, fun σ h h' ↦ ?_⟩
  rw [Diffeotopy.flux_def, Diffeotopy.flux_def, ← sub_eq_zero, ← map_sub,
    deRhamCohomology.mk_eq_zero_iff]
  exact hσ σ.val ((SmoothForm.isClosed_def _).mpr ((mem_closedForms _ σ.val).mp σ.property))

end Loop

section Area

variable (p : Fin 2 → ℝ) [∀ i, Fact (0 < p i)] (v : Fin 2 → ℝ) (A : ℝ)

/-- The area form `A dt_0 ∧ dt_1` of the two-torus has constant coefficients. -/
private theorem smul_torusVolumeForm_apply_eq (x : ∀ i, AddCircle (p i)) :
    ((A • torusVolumeForm p).val x : (Fin 2 → ℝ) [⋀^Fin 2]→L[ℝ] ℝ) =
      (A • torusVolumeForm p).val 0 :=
  congrArg (A • ·) (torusVolumeForm_apply_eq_apply_zero p x)

/-- **The flux form of a translation of the two-torus.** For the area form `A dt_0 ∧ dt_1`, the
translation diffeotopy along `v` has the constant flux form `A (v 0 dt_1 - v 1 dt_0)`. -/
theorem fluxForm_torusTranslationDiffeotopy_smul_torusVolumeForm :
    (torusTranslationDiffeotopy p v).fluxForm (A • torusVolumeForm p) =
      A • (v 0 • torusTimeForm p 1 - v 1 • torusTimeForm p 0) := by
  refine Subtype.ext (funext fun x ↦ ?_)
  rw [fluxForm_torusTranslationDiffeotopy_apply p v (smul_torusVolumeForm_apply_eq p A) x]
  ext w
  refine (ContinuousAlternatingMap.curryLeft_apply_apply _ v w).trans ?_
  -- Both sides are `A` times a `2 × 2` determinant, read through the formulas for the volume form
  -- and for the coordinate time forms. These are instantiated at `w` explicitly, since the forms
  -- take values in tangent-space fibres where `simp` cannot apply them.
  have hL := congrArg (A • ·) (torusVolumeForm_apply p 0 (Matrix.vecCons v w))
  have hR := congrArg (A • ·) (congrArg₂ (fun a b : ℝ ↦ v 0 • a - v 1 • b)
    (torusTimeForm_apply p 1 x w) (torusTimeForm_apply p 0 x w))
  refine hL.trans (Eq.trans ?_ hR.symm)
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val, smul_eq_mul]
  ring

/-- The flux form `A (v 0 dt_1 - v 1 dt_0)` as a constant-coefficient combination of the coordinate
time forms. -/
private theorem smul_sub_eq_sum_smul_torusTimeForm :
    A • (v 0 • torusTimeForm p 1 - v 1 • torusTimeForm p 0) =
      ∑ j, ![-(A * v 1), A * v 0] j • torusTimeForm p j := by
  rw [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]
  module

/-- **The periods of the flux form along the coordinate circles.** Along the `i`-th coordinate
circle through `x`, traversed from `[a]` to `[b]`, the flux form of the translation diffeotopy
along `v` for the area form `A dt_0 ∧ dt_1` integrates to `-A v 1 (b - a)` for `i = 0` and to
`A v 0 (b - a)` for `i = 1`. Over one circuit, `b - a = p i`. -/
theorem pathIntegral_fluxForm_torusTranslationDiffeotopy_smul_torusVolumeForm_update
    (x : ∀ i, AddCircle (p i)) (i : Fin 2) (a b : ℝ) :
    pathIntegral ((torusTranslationDiffeotopy p v).fluxForm (A • torusVolumeForm p)).val
        (fun t : ℝ ↦ Function.update x i (t : AddCircle (p i))) a b =
      ![-(A * v 1), A * v 0] i * (b - a) := by
  rw [fluxForm_torusTranslationDiffeotopy_smul_torusVolumeForm,
    smul_sub_eq_sum_smul_torusTimeForm, pathIntegral_sum_smul_torusTimeForm_update]

/-- **The flux of a translation of the two-torus.** For the area form `A dt_0 ∧ dt_1`, the
translation diffeotopy along `v` has flux `A (v 0 [dt_1] - v 1 [dt_0])` in `H¹_dR(T²)`. -/
theorem flux_torusTranslationDiffeotopy_smul_torusVolumeForm
    (h : (torusTranslationDiffeotopy p v).final ∈
      SmoothForm.diffeomorphStabilizer (A • torusVolumeForm p)) :
    (torusTranslationDiffeotopy p v).flux
        ⟨A • torusVolumeForm p, mem_closedForms_of_finrank_le _ (by simp) _⟩ h =
      A • (v 0 • deRhamCohomology.mk (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) 1
          (torusTimeClosedForm p 1) -
        v 1 • deRhamCohomology.mk (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) 1
          (torusTimeClosedForm p 0)) := by
  rw [Diffeotopy.flux_def, ← map_smul, ← map_smul, ← map_sub, ← map_smul]
  congr 1
  refine Subtype.ext ?_
  simp only [Submodule.coe_smul, Submodule.coe_sub, coe_torusTimeClosedForm]
  exact fluxForm_torusTranslationDiffeotopy_smul_torusVolumeForm p v A

/-- **Translations have nonzero flux.** For a nonzero area form `A dt_0 ∧ dt_1`, the translation
diffeotopy along `v` has zero flux only when `v = 0`: the classes `[dt_0]` and `[dt_1]` are
linearly independent. -/
theorem flux_torusTranslationDiffeotopy_smul_torusVolumeForm_eq_zero_iff
    (h : (torusTranslationDiffeotopy p v).final ∈
      SmoothForm.diffeomorphStabilizer (A • torusVolumeForm p)) :
    (torusTranslationDiffeotopy p v).flux
        ⟨A • torusVolumeForm p, mem_closedForms_of_finrank_le _ (by simp) _⟩ h = 0 ↔
      A = 0 ∨ v = 0 := by
  rw [Diffeotopy.flux_def, deRhamCohomology.mk_eq_zero_iff]
  simp only [fluxForm_torusTranslationDiffeotopy_smul_torusVolumeForm,
    smul_sub_eq_sum_smul_torusTimeForm, sum_smul_torusTimeForm_mem_exactForms_iff]
  constructor
  · intro h0
    have h₀ := congrFun h0 0
    have h₁ := congrFun h0 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, neg_eq_zero,
      mul_eq_zero] at h₀ h₁
    refine or_iff_not_imp_left.2 fun hA ↦ funext fun i ↦ ?_
    fin_cases i
    · exact h₁.resolve_left hA
    · exact h₀.resolve_left hA
  · rintro (rfl | rfl) <;> ext i <;> fin_cases i <;> simp

/-- **Integral translation loops realize the area lattice as fluxes.** On the two-torus with the
area form `A dt_0 ∧ dt_1`, for all integers `m` and `n` there is a loop of diffeomorphisms based at
the identity, all of whose maps preserve the area form, with flux `A (m p_1 [dt_0] + n p_0 [dt_1])`:
the translation diffeotopy along `(n p_0, -m p_1)`. These classes are the total area `A p_0 p_1`
times the integer combinations of the classes `[dt_i / p_i]` dual to the coordinate circles. -/
theorem exists_final_eq_refl_and_flux_smul_torusVolumeForm_eq (m n : ℤ) :
    ∃ (Φ : Diffeotopy (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) ∞ (∀ i, AddCircle (p i)))
      (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer (A • torusVolumeForm p)),
      (∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer (A • torusVolumeForm p)) ∧
      Φ.final = Diffeomorph.refl _ _ _ ∧
      Φ.flux ⟨A • torusVolumeForm p, mem_closedForms_of_finrank_le _ (by simp) _⟩ hΦ =
        A • ((m * p 1) • deRhamCohomology.mk (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) 1
            (torusTimeClosedForm p 0) +
          (n * p 0) • deRhamCohomology.mk (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) 1
            (torusTimeClosedForm p 1)) := by
  let v : Fin 2 → ℝ := ![n * p 0, -(m * p 1)]
  have hloop : ∀ i, v i ∈ AddSubgroup.zmultiples (p i) := by
    intro i
    fin_cases i
    · exact ⟨n, by simp [v]⟩
    · exact ⟨-m, by simp [v]⟩
  have hslice := timeSlice_torusTranslationDiffeotopy_mem_diffeomorphStabilizer p v
    (smul_torusVolumeForm_apply_eq p A)
  refine ⟨torusTranslationDiffeotopy p v, by rw [Diffeotopy.final_def]; exact hslice 1, hslice,
    (final_torusTranslationDiffeotopy_eq_refl_iff p v).2 hloop, ?_⟩
  rw [flux_torusTranslationDiffeotopy_smul_torusVolumeForm]
  simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul, sub_neg_eq_add]
  rw [add_comm]

/-- **The flux group of the two-torus.** For the area form `A dt_0 ∧ dt_1` on
`T² = AddCircle (p 0) × AddCircle (p 1)`, the fluxes of the loops preserving the area form at every
time are exactly the classes `A (m p_1 [dt_0] + n p_0 [dt_1])` with `m n : ℤ`. These are the total
area `A p_0 p_1` times the integer combinations of the classes `[dt_i / p_i]`, which integrate to
`1` around the `i`-th coordinate circle and to `0` around the other. -/
theorem mem_fluxGroup_smul_torusVolumeForm_iff
    {c : deRhamCohomology (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) 1} :
    c ∈ fluxGroup ⟨A • torusVolumeForm p, mem_closedForms_of_finrank_le _ (by simp) _⟩ ↔
      ∃ m n : ℤ, A • ((m * p 1) • deRhamCohomology.mk (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) 1
            (torusTimeClosedForm p 0) +
          (n * p 0) • deRhamCohomology.mk (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) 1
            (torusTimeClosedForm p 1)) = c := by
  rw [mem_fluxGroup]
  constructor
  · rintro ⟨Φ, -, hΦ₁, rfl⟩
    -- The loop has the flux of a translation loop along a lattice vector `(k₀ p_0, k₁ p_1)`.
    obtain ⟨v, hv, hflux⟩ := Φ.exists_flux_torusTranslationDiffeotopy_eq_flux p hΦ₁
    obtain ⟨k₀, hk₀⟩ := AddSubgroup.mem_zmultiples_iff.1 (hv 0)
    obtain ⟨k₁, hk₁⟩ := AddSubgroup.mem_zmultiples_iff.1 (hv 1)
    rw [zsmul_eq_mul] at hk₀ hk₁
    have hfin : (torusTranslationDiffeotopy p v).final ∈
        SmoothForm.diffeomorphStabilizer (A • torusVolumeForm p) := by
      rw [(final_torusTranslationDiffeotopy_eq_refl_iff p v).2 hv]
      exact Subgroup.one_mem _
    have e : ((-k₁ : ℤ) : ℝ) * p 1 = -v 1 := by rw [← hk₁]; push_cast; ring
    refine ⟨-k₁, k₀, ?_⟩
    rw [← hflux _ _ hfin, flux_torusTranslationDiffeotopy_smul_torusVolumeForm, e, hk₀]
    simp only [neg_smul, sub_eq_add_neg]
    rw [add_comm]
  · rintro ⟨m, n, rfl⟩
    obtain ⟨Φ, _, hslice, hfin, hflux⟩ :=
      exists_final_eq_refl_and_flux_smul_torusVolumeForm_eq p A m n
    exact ⟨Φ, hslice, hfin, hflux⟩

end Area

end TauCeti
