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
public import TauCeti.Geometry.Symplectic.Flux.Hamiltonian
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Topology.Covering.AddCircle
import TauCeti.Geometry.Manifold.Instances.AddCircle.Lift
import TauCeti.Geometry.Manifold.DeRham.AddCircle

/-!
# The flux of the translations and shears of a torus, and the flux group of the two-torus

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
when `v = 0`, since `[dt_0]` and `[dt_1]` are linearly independent. So for `A ≠ 0` and `v ≠ 0` it
is not homotopic relative to both time ends to any Hamiltonian diffeotopy
(`TauCeti.not_homotopic_torusTranslationDiffeotopy_of_isHamiltonian`), even when it is a loop at
the identity. Integrated around the two
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

**Shears.** Let `v` be a real vector with `v i = 0` and `g` a smooth function on the `i`-th circle,
and let `φ_t (x) = x + [t g(x i) v]` be the shear diffeotopy (`TauCeti.torusShearDiffeotopy`).
Its velocity is `g(x i) v` and its spatial derivative only adds multiples of `v`, so for a two-form
`σ` with constant coefficients `β` its flux form is `g(x i) β(v, ·)`
(`TauCeti.fluxForm_torusShearDiffeotopy_apply`). Suppose `β(v, ·) = c dt_i`. Then every `φ_t`
preserves `σ`, its flux form is `c g(x i) dt_i`, and since a one-form `g dt` on a circle is
cohomologous to `(⨍ g) dt` (`AddCircle.funSMulₗ_timeForm_sub_smul_timeForm_mem_exactForms`) the
flux is

`Flux(φ) = c (⨍ g) [dt_i]`,  `⨍ g = (p i)⁻¹ ∫₀^{p i} g`

(`TauCeti.flux_torusShearDiffeotopy`). When `c = 0` or `∫ g = 0`, the function `c G(x i)`, for a
primitive `G` of `g - ⨍ g` on the circle, is a Hamiltonian of the shear, read along the motion,
since the shear does not move the `i`-th coordinate. As `[dt_i] ≠ 0`, the shear is a Hamiltonian
isotopy exactly when `c = 0` or `∫ g = 0` (`TauCeti.isHamiltonian_torusShearDiffeotopy_iff`). On the
two-torus with the area form `A dt_0 ∧ dt_1`, `A ≠ 0`, the shear `(x, y) ↦ (x, y + [t g(x)])` has
`c = -A`, so it is Hamiltonian exactly when `∫ g = 0`
(`TauCeti.isHamiltonian_torusShearDiffeotopy_smul_torusVolumeForm_iff`).

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
* `TauCeti.not_homotopic_torusTranslationDiffeotopy_of_isHamiltonian`: for `A ≠ 0` and `v ≠ 0`
  the translation is not homotopic relative to both time ends to a Hamiltonian diffeotopy.
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
* `TauCeti.fluxForm_torusShearDiffeotopy_apply`,
  `TauCeti.timeSlice_torusShearDiffeotopy_mem_diffeomorphStabilizer`,
  `TauCeti.final_torusShearDiffeotopy_mem_diffeomorphStabilizer`: the flux form of a shear, and
  the shears preserving a constant-coefficient two-form.
* `TauCeti.flux_torusShearDiffeotopy`: the flux of a shear is `c (⨍ g) [dt_i]`.
* `TauCeti.isHamiltonian_torusShearDiffeotopy_iff`,
  `TauCeti.isHamiltonian_torusShearDiffeotopy_smul_torusVolumeForm_iff`: a shear is a Hamiltonian
  isotopy exactly when `c = 0` or `∫ g = 0`.

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

section Shear

/-! ### Shears -/

variable {v} {i : ι} (hv : v i = 0) (g : C^∞⟮𝓘(ℝ), AddCircle (p i); ℝ⟯)
  {β : (ι → ℝ) [⋀^Fin 2]→L[ℝ] ℝ}

/-- The integrand of the flux form of a shear: `σ` at the moving point, on the velocity
`g(x i) v` and the image `w + (t g'(x i) w i) v` of a spatial vector `w`, is `g(x i) β(v, w)`. -/
private theorem apply_mfderiv_cylinderMap_torusShearDiffeotopy
    {σ : SmoothForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ k, AddCircle (p k)) ℝ 2}
    (hσ : ∀ x, (σ.val x : (ι → ℝ) [⋀^Fin 2]→L[ℝ] ℝ) = β) (x : ∀ k, AddCircle (p k))
    (t : unitInterval) (w : ι → ℝ) :
    σ.val ((torusShearDiffeotopy p v hv g).cylinderMap (x, t))
        ![mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod (𝓡∂ 1))
            (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (torusShearDiffeotopy p v hv g).cylinderMap
            (x, t) ((0 : ι → ℝ), (1 : TangentSpace (𝓡∂ 1) t)),
          mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod (𝓡∂ 1))
            (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (torusShearDiffeotopy p v hv g).cylinderMap
            (x, t) (w, (0 : EuclideanSpace ℝ (Fin 1)))] =
      g (x i) * β ![v, w] := by
  rw [mfderiv_cylinderMap_torusShearDiffeotopy_apply_one,
    mfderiv_cylinderMap_torusShearDiffeotopy_space, hσ]
  -- The vectors are `0 + g(x i) v` and `w + b v`, read in the model space `ι → ℝ`, and `β`
  -- vanishes when its first vector is `0`.
  have h (a b : ℝ) : β ![a • v, w + b • v] = a * β ![v, w] := by
    simpa [β.map_coord_zero (m := ![0, _]) 0 rfl] using
      β.apply_vecCons_add_smul_add_smul v 0 w a b
  exact h _ _

/-- **The flux form of a shear.** For a two-form `σ` on the torus with constant coefficients `β`,
the shear diffeotopy `x ↦ x + [t g(x i) v]` has flux form `g(x i) β(v, ·)`. -/
theorem fluxForm_torusShearDiffeotopy_apply
    {σ : SmoothForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ k, AddCircle (p k)) ℝ 2}
    (hσ : ∀ x, (σ.val x : (ι → ℝ) [⋀^Fin 2]→L[ℝ] ℝ) = β) (x : ∀ k, AddCircle (p k)) :
    ((torusShearDiffeotopy p v hv g).fluxForm σ).val x = g (x i) • β.curryLeft v := by
  rw [Diffeotopy.fluxForm_apply]
  -- At every time the integrand is `g(x i) β(v, ·)`: the velocity is `g(x i) v` and the spatial
  -- derivative only adds multiples of `v`, on which `β(v, ·)` vanishes.
  refine (intervalIntegral.integral_congr (g := fun _ ↦ g (x i) • β.curryLeft v) fun t _ ↦
    ContinuousAlternatingMap.ext fun w ↦ ?_).trans ?_
  · obtain ⟨u, rfl⟩ : ∃ u : ι → ℝ, w = ![u] :=
      ⟨w 0, funext fun j ↦ by rw [Fin.fin_one_eq_zero j]; rfl⟩
    rw [Diffeotopy.curryLeft_mfderiv_cylinderMap_apply]
    -- The two vectors are the velocity and the image of `u`.
    refine (congrArg (σ.val _) (funext fun j ↦ by fin_cases j <;> rfl)).trans
      ((apply_mfderiv_cylinderMap_torusShearDiffeotopy p hv g hσ x _ u).trans ?_)
    simp
  · rw [intervalIntegral.integral_const, sub_zero, one_smul]

/-- **Shears preserve the two-forms they slide along.** Let `σ` be a two-form on the torus with
constant coefficients `β` such that `β(v, ·) = c dt_i` for a constant `c`. Then every map of the
shear diffeotopy `x ↦ x + [t g(x i) v]` preserves `σ`. -/
theorem timeSlice_torusShearDiffeotopy_mem_diffeomorphStabilizer
    {σ : SmoothForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ k, AddCircle (p k)) ℝ 2}
    (hσ : ∀ x, (σ.val x : (ι → ℝ) [⋀^Fin 2]→L[ℝ] ℝ) = β) {c : ℝ}
    (hβ : ∀ w, β ![v, w] = c * w i) (t : unitInterval) :
    (torusShearDiffeotopy p v hv g).timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ := by
  refine SmoothForm.mem_diffeomorphStabilizer_iff_forall.2 fun x ↦
    ContinuousAlternatingMap.ext fun W ↦ ?_
  -- The derivative of the time slice is the shear `w ↦ w + (t g'(x i) w i) • v`.
  set L := mvfderiv 𝓘(ℝ) g (x i)
  have hD (w : ι → ℝ) : mfderiv (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ((torusShearDiffeotopy p v hv g).timeSlice t) x w =
        w + ((t : ℝ) * L (w i)) • v :=
    ((torusShearDiffeotopy p v hv g).mfderiv_cylinderMap_inl (by simp) (x, t) w).symm.trans
      (mfderiv_cylinderMap_torusShearDiffeotopy_space p hv g x t w)
  -- A linear map of the real line satisfies `L a * b = L b * a`.
  have hL (a b : ℝ) : L a * b = L b * a := by
    have h₁ : L (b * a) = b * L a := L.map_smul b a
    have h₂ : L (a * b) = a * L b := L.map_smul a b
    rw [mul_comm b a] at h₁
    linarith
  rw [TauCeti.mpullback_apply, hσ, hσ]
  obtain ⟨u, u', rfl⟩ : ∃ u u' : ι → ℝ, W = ![u, u'] :=
    ⟨W 0, W 1, funext fun j ↦ by fin_cases j <;> rfl⟩
  -- Expand `β` on the two displaced vectors `u + (t L (u i)) v` and `u' + (t L (u' i)) v`.
  refine (congrArg β (funext fun j ↦ by fin_cases j <;> exact hD _)).trans
    ((β.apply_vecCons_add_smul_add_smul v u u' ((t : ℝ) * L (u i)) ((t : ℝ) * L (u' i))).trans ?_)
  have h₁ := β.apply_vecCons_swap u v
  have h₂ := hβ u
  have h₃ := hβ u'
  have h₄ := hL (u i) (u' i)
  linear_combination (t : ℝ) * L (u' i) * h₁ - (t : ℝ) * L (u' i) * h₂ +
    (t : ℝ) * L (u i) * h₃ + (t : ℝ) * c * h₄

/-- The final diffeomorphism `x ↦ x + [g(x i) v]` of a shear diffeotopy preserves every two-form
with constant coefficients `β` such that `β(v, ·) = c dt_i`. -/
theorem final_torusShearDiffeotopy_mem_diffeomorphStabilizer
    {σ : SmoothForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ k, AddCircle (p k)) ℝ 2}
    (hσ : ∀ x, (σ.val x : (ι → ℝ) [⋀^Fin 2]→L[ℝ] ℝ) = β) {c : ℝ}
    (hβ : ∀ w, β ![v, w] = c * w i) :
    (torusShearDiffeotopy p v hv g).final ∈ SmoothForm.diffeomorphStabilizer σ := by
  rw [Diffeotopy.final_def]
  exact timeSlice_torusShearDiffeotopy_mem_diffeomorphStabilizer p hv g hσ hβ 1

variable {σ : closedForms (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ k, AddCircle (p k)) 2}
  (hσ : ∀ x, (σ.val.val x : (ι → ℝ) [⋀^Fin 2]→L[ℝ] ℝ) = β) {c : ℝ}
  (hβ : ∀ w, β ![v, w] = c * w i)
include hσ hβ

/-- The flux form of a shear is `c g(x i) dt_i`, the pullback of `c g dt` along the `i`-th
coordinate projection. -/
private theorem fluxForm_torusShearDiffeotopy_eq_smul_mpullback :
    (torusShearDiffeotopy p v hv g).fluxForm σ.val =
      c • SmoothForm.mpullback (fun x : ∀ k, AddCircle (p k) ↦ x i) contMDiff_apply
        (SmoothForm.funSMulₗ g (AddCircle.timeForm (p i))) := by
  refine Subtype.ext (funext fun x ↦ ContinuousAlternatingMap.ext fun w ↦ ?_)
  have hw : w = ![w 0] := funext fun j ↦ by rw [Fin.fin_one_eq_zero j]; rfl
  rw [hw, fluxForm_torusShearDiffeotopy_apply p hv g hσ]
  simp only [Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
    SmoothForm.mpullback_apply, SmoothForm.coe_funSMulₗ, AddCircle.timeForm_apply,
    TauCeti.mfderiv_apply, Matrix.cons_val_zero, smul_eq_mul]
  -- Both sides are real numbers: the left side is `g(x i) β(v, w 0)` and the right side is
  -- `c (g(x i) (w 0) i)`, by the definitions of `curryLeft`, `proj` and scalar multiplication.
  exact (congrArg (g (x i) * ·) (hβ (w 0))).trans (mul_left_comm _ _ _)

/-- A shear has the Hamiltonian `(x, t) ↦ c G(x i)`, read along the motion, for a primitive `G` of
`(g - m) dt` on the `i`-th circle with `c m = 0`. -/
private theorem hasHamiltonian_torusShearDiffeotopy {G : AddCircle (p i) → ℝ}
    (hG : ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℝ) ∞ G) {m : ℝ}
    (hdG : mextDeriv (RoughForm.ofFunction 𝓘(ℝ) G) =
      (SmoothForm.funSMulₗ g (AddCircle.timeForm (p i)) - m • AddCircle.timeForm (p i)).val)
    (hcm : c * m = 0) :
    (torusShearDiffeotopy p v hv g).HasHamiltonian σ.val fun q ↦ c * G (q.1 i) := by
  refine Diffeotopy.hasHamiltonian_iff.2 ⟨contMDiff_const.mul
    (hG.comp (contMDiff_apply.comp contMDiff_fst)), fun q w ↦ ?_⟩
  obtain ⟨x, t⟩ := q
  -- The derivative of `G` at `x i` is multiplication by `g(x i) - m`.
  have hGd : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) G (x i) ((1 : ℝ →L[ℝ] ℝ).smulRight (g (x i) - m)) := by
    refine ((hG.mdifferentiableAt (by simp)).hasMFDerivAt).congr_mfderiv
      (ContinuousLinearMap.ext fun u ↦ ?_)
    have h := congrArg (fun φ : RoughForm 𝓘(ℝ) (AddCircle (p i)) ℝ 1 ↦ φ (x i) ![u]) hdG
    simp only [mextDeriv_ofFunction_apply] at h
    rw [h]
    simp only [Submodule.coe_sub, Submodule.coe_smul, SmoothForm.coe_funSMulₗ, Pi.sub_apply,
      Pi.smul_apply, ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
      AddCircle.timeForm_apply, Matrix.cons_val_zero]
    -- Tangent vectors of the circle are real numbers, on which both sides are `(g(x i) - m) u`.
    exact (show ∀ a b r : ℝ, a * r - b * r = r * (a - b) by intros; ring) (g (x i)) m u
  have happ := TauCeti.hasMFDerivAt_apply (I := fun _ : ι ↦ 𝓘(ℝ)) (M := fun k ↦ AddCircle (p k)) i x
  have hF : HasMFDerivAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod (𝓡∂ 1)) 𝓘(ℝ)
      (fun q : (∀ k, AddCircle (p k)) × unitInterval ↦ c * G (q.1 i)) (x, t)
      (c • (((1 : ℝ →L[ℝ] ℝ).smulRight (g (x i) - m)).comp (ContinuousLinearMap.proj i)).comp
        (ContinuousLinearMap.fst ℝ (ι → ℝ) (EuclideanSpace ℝ (Fin 1)))) :=
    ((hGd.comp x happ).comp (x, t) (hasMFDerivAt_fst (x, t))).const_smul c
  rw [TauCeti.mpullback_apply]
  -- The two vectors are the velocity and the image of `w`.
  refine (congrArg (σ.val.val _) (funext fun k ↦ by fin_cases k <;> rfl)).trans
    ((apply_mfderiv_cylinderMap_torusShearDiffeotopy p hv g hσ x t w).trans
      (Eq.trans ?_ (DFunLike.congr_fun hF.mfderiv (w, 0)).symm))
  rw [hβ]
  -- Both sides are real numbers: the right side is `c ((w i) (g(x i) - m))`.
  exact (show ∀ a b r : ℝ, c * b = 0 → a * (c * r) = c * (r * (a - b)) by
    intro a b r h; linear_combination r * h) (g (x i)) m (w i) hcm

/-- **The flux of a shear.** Let `σ` be a closed two-form on the torus with constant coefficients
`β` such that `β(v, ·) = c dt_i`. The shear diffeotopy `x ↦ x + [t g(x i) v]` has flux
`c (⨍ g) [dt_i]` in `H¹_dR(Tⁿ)`, where `⨍ g = (p i)⁻¹ ∫₀^{p i} g` is the mean of `g`. -/
theorem flux_torusShearDiffeotopy
    (h : (torusShearDiffeotopy p v hv g).final ∈ SmoothForm.diffeomorphStabilizer σ.val) :
    (torusShearDiffeotopy p v hv g).flux σ h =
      (c * ((p i)⁻¹ * ∫ s in (0)..(p i), g s)) •
        deRhamCohomology.mk (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) 1 (torusTimeClosedForm p i) := by
  set m := (p i)⁻¹ * ∫ s in (0)..(p i), g s
  -- The difference `c (g - ⨍ g) dt_i` is pulled back from the exact form `c (g - ⨍ g) dt` of the
  -- `i`-th circle.
  have hcl : SmoothForm.funSMulₗ g (AddCircle.timeForm (p i)) - m • AddCircle.timeForm (p i) ∈
      closedForms 𝓘(ℝ) (AddCircle (p i)) 1 :=
    mem_closedForms_of_finrank_le 𝓘(ℝ) (by simp) _
  have hex := closedForms.mpullback_mem_exactForms (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
    (I' := 𝓘(ℝ)) (fun x : ∀ k, AddCircle (p k) ↦ x i) contMDiff_apply 1
    (⟨_, hcl⟩ : closedForms 𝓘(ℝ) (AddCircle (p i)) 1)
    (AddCircle.funSMulₗ_timeForm_sub_smul_timeForm_mem_exactForms g)
  rw [Diffeotopy.flux_def, mul_smul, ← map_smul, ← map_smul, ← sub_eq_zero, ← map_sub,
    deRhamCohomology.mk_eq_zero_iff]
  convert Submodule.smul_mem _ c hex using 1
  simp only [Submodule.coe_sub, Submodule.coe_smul, coe_torusTimeClosedForm,
    closedForms.coe_mpullback, fluxForm_torusShearDiffeotopy_eq_smul_mpullback p hv g hσ hβ,
    map_sub, map_smul, torusTimeForm_def, smul_sub]

/-- **Hamiltonian shears.** Let `σ` be a closed two-form on the torus with constant coefficients
`β` such that `β(v, ·) = c dt_i`. The shear diffeotopy `x ↦ x + [t g(x i) v]` is a Hamiltonian
isotopy of `σ` exactly when `c = 0` or `g` has integral zero over a period. -/
theorem isHamiltonian_torusShearDiffeotopy_iff :
    (torusShearDiffeotopy p v hv g).IsHamiltonian σ.val ↔
      c = 0 ∨ ∫ s in (0)..(p i), g s = 0 := by
  have hslice := timeSlice_torusShearDiffeotopy_mem_diffeomorphStabilizer p hv g hσ hβ
  have hfin := final_torusShearDiffeotopy_mem_diffeomorphStabilizer p hv g hσ hβ
  have hpi : (p i)⁻¹ ≠ 0 := inv_ne_zero (Fact.out : 0 < p i).ne'
  constructor
  · -- A Hamiltonian isotopy has zero flux, and `[dt_i] ≠ 0`.
    intro hΦ
    have h0 := (flux_torusShearDiffeotopy p hv g hσ hβ hfin).symm.trans (hΦ.flux_eq_zero hfin)
    rw [smul_eq_zero, deRhamCohomology.mk_eq_zero_iff, coe_torusTimeClosedForm] at h0
    rcases mul_eq_zero.1 (h0.resolve_right (torusTimeForm_notMem_exactForms p i)) with h | h
    · exact .inl h
    · exact .inr ((mul_eq_zero.1 h).resolve_left hpi)
  · -- The Hamiltonian is `c G(x i)` for a primitive `G` of `g - ⨍ g` on the `i`-th circle.
    intro h
    obtain ⟨G, hG, hdG⟩ := exists_contMDiff_mextDeriv_eq_of_mem_exactForms 𝓘(ℝ)
      (AddCircle.funSMulₗ_timeForm_sub_smul_timeForm_mem_exactForms g)
    refine Diffeotopy.isHamiltonian_iff.2
      ⟨hslice, _, hasHamiltonian_torusShearDiffeotopy p hv g hσ hβ hG hdG ?_⟩
    rcases h with h | h <;> simp [h]

end Shear

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

/-- **Translations of the two-torus are not homotopic to Hamiltonian isotopies.** For a nonzero
area form `A dt_0 ∧ dt_1` and `v ≠ 0`, the translation diffeotopy along `v` is not homotopic,
relative to both time ends, to any Hamiltonian diffeotopy of the area form: its flux is nonzero,
while homotopic diffeotopies have the same flux and Hamiltonian ones have zero flux. This holds
also when `v` lies in the period lattice, where the translation diffeotopy is a loop at the
identity, itself a Hamiltonian diffeomorphism. -/
theorem not_homotopic_torusTranslationDiffeotopy_of_isHamiltonian (hA : A ≠ 0) (hv : v ≠ 0)
    {Ψ : Diffeotopy (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) ∞ (∀ i, AddCircle (p i))}
    (hΨ : Ψ.IsHamiltonian (A • torusVolumeForm p)) :
    ¬ (torusTranslationDiffeotopy p v).Homotopic Ψ := by
  intro h
  have hΨfin := SmoothForm.final_mem_diffeomorphStabilizer hΨ.timeSlice_mem_diffeomorphStabilizer
  have hfin : (torusTranslationDiffeotopy p v).final ∈
      SmoothForm.diffeomorphStabilizer (A • torusVolumeForm p) := h.final_eq ▸ hΨfin
  have h0 := (h.flux_eq ⟨A • torusVolumeForm p, mem_closedForms_of_finrank_le _ (by simp) _⟩ hfin
    hΨfin).trans (hΨ.flux_eq_zero hΨfin)
  exact ((flux_torusTranslationDiffeotopy_smul_torusVolumeForm_eq_zero_iff p v A hfin).1 h0).elim
    hA hv

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

/-- **Hamiltonian shears of the two-torus.** For a nonzero area form `A dt_0 ∧ dt_1` on the
two-torus, the shear diffeotopy `(x, y) ↦ (x, y + [t g(x)])` by a smooth function `g` on the first
circle is a Hamiltonian isotopy exactly when `g` has integral zero over a period. -/
theorem isHamiltonian_torusShearDiffeotopy_smul_torusVolumeForm_iff (hA : A ≠ 0)
    (g : C^∞⟮𝓘(ℝ), AddCircle (p 0); ℝ⟯) :
    (torusShearDiffeotopy p ![0, 1] rfl g).IsHamiltonian (A • torusVolumeForm p) ↔
      ∫ s in (0)..(p 0), g s = 0 := by
  -- The area form has constant coefficients `β` with `β((0, 1), w) = -A w 0`.
  have hβ (w : Fin 2 → ℝ) : (A • torusVolumeForm p).val 0 ![![0, 1], w] = -A * w 0 := by
    have h := congrArg (A • ·) (torusVolumeForm_apply p 0 ![![0, 1], w])
    refine h.trans ?_
    simp [Matrix.det_fin_two]
  rw [isHamiltonian_torusShearDiffeotopy_iff (σ := ⟨A • torusVolumeForm p,
    mem_closedForms_of_finrank_le _ (by simp) _⟩) p rfl g (smul_torusVolumeForm_apply_eq p A) hβ,
    neg_eq_zero, or_iff_right hA]

end Area

end TauCeti
