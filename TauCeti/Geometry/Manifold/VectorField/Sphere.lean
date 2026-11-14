/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.SmoothApprox
import TauCeti.Analysis.InnerProductSpace.Euclidean.Complex
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.Geometry.Manifold.VectorField.Immersion
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis

/-!
# Tangent vector fields on unit spheres

Let `E` be a real inner product space of dimension `n + 1`, with unit sphere
`Sⁿ = sphere (0 : E) 1` modelled on `ℝⁿ` via Mathlib's stereographic atlas. The differential of
the inclusion `ι : Sⁿ → E` identifies each tangent space `TangentSpace (𝓡 n) x` isometrically
with the hyperplane `x^⊥` (`TauCeti.sphereTangentEquiv`), and its orthogonal projection supplies
a continuous linear left inverse at every point (`TauCeti.hasLeftInverse_mfderiv_coe_sphere`).

Consequently, a section `V` of the tangent bundle of `Sⁿ` is `C^m` (or continuous, `m = 0`) if
and only if its ambient velocity `x ↦ dι_x (V x)` is `C^m` (or continuous) into `E`
(`TauCeti.contMDiffAt_section_sphere_iff`, `TauCeti.contMDiff_section_sphere_iff`,
`TauCeti.continuous_section_sphere_iff`). Conversely, any ambient map `v : Sⁿ → E` projects
orthogonally to an intrinsic section `TauCeti.sphereTangentSection n v` whose ambient velocity is
the tangential part `v x - ⟪x, v x⟫ x`, equal to `v x` itself when `v` is already tangent to the
sphere (`TauCeti.mvfderiv_coe_sphereTangentSection_of_inner_eq_zero`), and `C^m` whenever `v` is
(`TauCeti.contMDiff_sphereTangentSection`).

When a continuous tangent vector field on `Sⁿ` vanishes nowhere, approximating it within half its
pointwise norm by a smooth ambient map (`Continuous.exists_contMDiff_approx`), projecting onto the
tangent hyperplanes, and normalizing produces a `C^∞` unit tangent vector field on `Sⁿ`
(`TauCeti.exists_contMDiff_unit_tangent_sphere_of_ne_zero`,
`TauCeti.exists_contMDiff_unit_section_sphere_of_ne_zero`).

Finally, when `n` is odd, `dim E = n + 1` is even, so `E` carries an orthogonal almost complex
structure (`TauCeti.AlmostComplexStructure.exists_forall_norm_apply_eq`), giving a linear isometry
`L : E →ₗᵢ[ℝ] E` with `⟪L x, x⟫ = 0` everywhere
(`TauCeti.exists_linearIsometry_inner_self_eq_zero_of_odd`). Restricting `L` to `Sⁿ` yields an
analytic unit tangent vector field and tangent-bundle section
(`TauCeti.exists_contDiff_unit_tangent_of_odd`,
`TauCeti.exists_contMDiff_unit_section_sphere_of_odd`). On `ℝ^(2m)` in standard coordinates, the
explicit linear isometry `TauCeti.euclideanPairTurn` sends `(x₀, x₁, x₂, x₃, …)` to
`(-x₁, x₀, -x₃, x₂, …)`.

## Main definitions

* `TauCeti.sphereTangentSection`: the intrinsic tangent vector field on `Sⁿ` obtained by
  projecting `v : Sⁿ → E` orthogonally onto each tangent hyperplane `x^⊥`.
* `TauCeti.euclideanPairTurn`: the linear isometry `(x₀, x₁, x₂, x₃, …) ↦ (-x₁, x₀, -x₃, x₂, …)`
  on `EuclideanSpace ℝ (Fin (2 * m))`.
* `TauCeti.oddSphereStandardSection`: the nowhere-vanishing analytic unit tangent vector field on
  `sphere (0 : EuclideanSpace ℝ (Fin (2 * (m + 1)))) 1` induced by `euclideanPairTurn`.

## Main results

* `TauCeti.contMDiffAt_section_sphere_iff`, `TauCeti.contMDiff_section_sphere_iff`,
  `TauCeti.continuous_section_sphere_iff`: intrinsic regularity of a tangent-bundle section on
  `Sⁿ` is equivalent to regularity of its ambient velocity `x ↦ dι_x (V x)`.
* `TauCeti.mfderiv_coe_sphereTangentSection`, `TauCeti.mvfderiv_coe_sphereTangentSection`,
  `TauCeti.mvfderiv_coe_sphereTangentSection_of_inner_eq_zero`,
  `TauCeti.contMDiff_sphereTangentSection`, `TauCeti.continuous_sphereTangentSection`: ambient
  evaluation and regularity of `sphereTangentSection`.
* `TauCeti.exists_contMDiff_unit_tangent_sphere_of_ne_zero`,
  `TauCeti.exists_contMDiff_unit_section_sphere_of_ne_zero`: smoothing and normalizing a
  nowhere-vanishing continuous tangent vector field on `Sⁿ` to a `C^∞` unit field.
* `TauCeti.exists_linearIsometry_inner_self_eq_zero_of_odd`,
  `TauCeti.exists_contDiff_unit_tangent_of_odd`,
  `TauCeti.exists_contMDiff_unit_section_sphere_of_odd`: analytic unit tangent vector fields on
  odd-dimensional spheres.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 8 (tangent vector fields to submanifolds) and Problem 16-6.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
-/

public section

noncomputable section

open Bundle Metric Module TopologicalSpace
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

section GeneralSphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {m : ℕ∞ω}

/-- The differential of the unit-sphere inclusion has a continuous linear left inverse at every
point, given by orthogonal projection onto `x^⊥` followed by `(sphereTangentEquiv x).symm`. -/
theorem hasLeftInverse_mfderiv_coe_sphere (x : sphere (0 : E) 1) :
    (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x).HasLeftInverse := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  refine ⟨(sphereTangentEquiv x).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ℝ ∙ (x : E))ᗮ.orthogonalProjectionOnto.comp
      (NormedSpace.fromTangentSpace (x : E)).toContinuousLinearMap), fun v ↦ ?_⟩
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  -- `NormedSpace.fromTangentSpace` applied to `mfderiv` is `mvfderiv` by definition.
  have hval : NormedSpace.fromTangentSpace (x : E)
      (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x v) = (sphereTangentEquiv x v : E) :=
    mvfderiv_subtypeVal_sphere_eq_sphereTangentEquiv x v
  rw [hval]
  have hproj : (ℝ ∙ (x : E))ᗮ.orthogonalProjectionOnto (sphereTangentEquiv x v : E) =
      sphereTangentEquiv x v :=
    Subtype.ext (by
      rw [← Submodule.starProjection_apply]
      exact Submodule.starProjection_eq_self_iff.2 (sphereTangentEquiv x v).2)
  rw [hproj, LinearIsometryEquiv.symm_apply_apply]

/-- A section of the tangent bundle of the unit sphere is `C^m` at `x` if and only if its ambient
velocity `y ↦ dι_y (V y)` is `C^m` at `x`. -/
theorem contMDiffAt_section_sphere_iff
    {V : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x} {x : sphere (0 : E) 1} :
    ContMDiffAt (𝓡 n) (𝓡 n).tangent m
      (fun y ↦ (⟨y, V y⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) x ↔
      ContMDiffAt (𝓡 n) 𝓘(ℝ, E) m
        (fun y ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) y (V y)) x := by
  constructor
  · intro hV
    have hdf : ContMDiffAt (𝓡 n).tangent 𝓘(ℝ, E) m
        (fun q : TangentBundle (𝓡 n) (sphere (0 : E) 1) ↦
          mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) q.1 q.2) ⟨x, V x⟩ :=
      (contMDiff_coe_sphere (m := ω) x).contMDiffAt_mvfderiv_apply le_top
    exact hdf.comp x hV
  · intro hv
    have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
    refine (contMDiff_coe_sphere (m := ω) x).vectorField_of_mfderiv le_top
      (hasLeftInverse_mfderiv_coe_sphere x) ?_
    have hpair : ContMDiffAt (𝓡 n) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) m
        (fun y : sphere (0 : E) 1 ↦
          ((y : E), mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) y (V y))) x := by
      refine (contMDiff_coe_sphere x).prodMk ?_
      simpa only [mvfderiv_apply_eq_mfderiv_apply] using hv
    rw [chartedSpaceSelf_prod] at hpair
    exact (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ, E))).contMDiffAt.comp
      x hpair

/-- A section of the tangent bundle of the unit sphere is `C^m` if and only if its ambient
velocity `x ↦ dι_x (V x)` is `C^m`. -/
theorem contMDiff_section_sphere_iff
    {V : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x} :
    ContMDiff (𝓡 n) (𝓡 n).tangent m
      (fun x ↦ (⟨x, V x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) ↔
      ContMDiff (𝓡 n) 𝓘(ℝ, E) m
        (fun x ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (V x)) :=
  forall_congr' fun _ ↦ contMDiffAt_section_sphere_iff

/-- A section of the tangent bundle of the unit sphere is continuous if and only if its ambient
velocity `x ↦ dι_x (V x)` is continuous. -/
theorem continuous_section_sphere_iff
    {V : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x} :
    Continuous (fun x ↦ (⟨x, V x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) ↔
      Continuous (fun x ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (V x)) := by
  rw [← contMDiff_zero_iff (I := 𝓡 n) (I' := (𝓡 n).tangent),
    ← contMDiff_zero_iff (I := 𝓡 n) (I' := 𝓘(ℝ, E)),
    contMDiff_section_sphere_iff]

/-! ### Tangential projection of ambient vector fields -/

variable (n) in
/-- The intrinsic tangent vector field on the unit sphere obtained by projecting an ambient map
`v : sphere (0 : E) 1 → E` orthogonally onto each tangent hyperplane `x^⊥` and reading the result
in `TangentSpace (𝓡 n) x` through `TauCeti.sphereTangentEquiv`. When `v x` is already orthogonal
to `x`, its image under `dι_x` is `v x` itself
(`TauCeti.mvfderiv_coe_sphereTangentSection_of_inner_eq_zero`). -/
def sphereTangentSection (v : sphere (0 : E) 1 → E) (x : sphere (0 : E) 1) :
    TangentSpace (𝓡 n) x :=
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  (sphereTangentEquiv x).symm ((ℝ ∙ (x : E))ᗮ.orthogonalProjectionOnto (v x))

/-- Read in the ambient space `E` through `mfderiv`, `TauCeti.sphereTangentSection n v` is the
tangential component `v x - ⟪x, v x⟫ x` of `v x`. -/
@[simp]
theorem mfderiv_coe_sphereTangentSection (v : sphere (0 : E) 1 → E) (x : sphere (0 : E) 1) :
    mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x (sphereTangentSection n v x) =
      v x - ⟪(x : E), v x⟫ • (x : E) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  rw [sphereTangentSection, ← coe_sphereTangentEquiv_apply, LinearIsometryEquiv.apply_symm_apply,
    ← Submodule.starProjection_apply, Submodule.starProjection_orthogonal, sub_apply,
    ContinuousLinearMap.id_apply,
    Submodule.starProjection_unit_singleton ℝ (norm_eq_of_mem_sphere x)]

/-- Read in the ambient space `E` through `mvfderiv`, `TauCeti.sphereTangentSection n v` is the
tangential component `v x - ⟪x, v x⟫ x` of `v x`. -/
theorem mvfderiv_coe_sphereTangentSection (v : sphere (0 : E) 1 → E) (x : sphere (0 : E) 1) :
    mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (sphereTangentSection n v x) =
      v x - ⟪(x : E), v x⟫ • (x : E) := by
  rw [mvfderiv_apply_eq_mfderiv_apply, mfderiv_coe_sphereTangentSection]

/-- When `v x` is orthogonal to `x`, `TauCeti.sphereTangentSection n v x` lifts `v x` through the
differential of the sphere inclusion. -/
theorem mvfderiv_coe_sphereTangentSection_of_inner_eq_zero {v : sphere (0 : E) 1 → E}
    {x : sphere (0 : E) 1} (ht : ⟪v x, (x : E)⟫ = 0) :
    mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (sphereTangentSection n v x) = v x := by
  rw [mvfderiv_coe_sphereTangentSection, real_inner_comm, ht, zero_smul, sub_zero]

/-- The round norm of `TauCeti.sphereTangentSection n v x` is the norm of the tangential part of
`v x`. -/
theorem norm_sphereTangentSection (v : sphere (0 : E) 1 → E) (x : sphere (0 : E) 1) :
    ‖sphereTangentSection n v x‖ = ‖v x - ⟪(x : E), v x⟫ • (x : E)‖ := by
  rw [norm_tangentSpace_sphere, mvfderiv_coe_sphereTangentSection]

/-- When `v x` is orthogonal to `x`, `TauCeti.sphereTangentSection n v x` has the same norm as
`v x`. -/
theorem norm_sphereTangentSection_of_inner_eq_zero {v : sphere (0 : E) 1 → E}
    {x : sphere (0 : E) 1} (ht : ⟪v x, (x : E)⟫ = 0) :
    ‖sphereTangentSection n v x‖ = ‖v x‖ := by
  rw [norm_tangentSpace_sphere, mvfderiv_coe_sphereTangentSection_of_inner_eq_zero ht]

/-- When `v x` is orthogonal to `x`, `TauCeti.sphereTangentSection n v x` vanishes if and only if
`v x = 0`. -/
theorem sphereTangentSection_eq_zero_iff_of_inner_eq_zero {v : sphere (0 : E) 1 → E}
    {x : sphere (0 : E) 1} (ht : ⟪v x, (x : E)⟫ = 0) :
    sphereTangentSection n v x = 0 ↔ v x = 0 := by
  rw [← norm_eq_zero, norm_sphereTangentSection_of_inner_eq_zero ht, norm_eq_zero]

/-- Lifting the ambient velocity of an intrinsic section recovers the section. -/
theorem sphereTangentSection_mvfderiv_coe
    (V : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x) (x : sphere (0 : E) 1) :
    sphereTangentSection n (fun y ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) y (V y)) x =
      V x := by
  apply injective_mvfderiv_subtypeVal_sphere x
  rw [mvfderiv_coe_sphereTangentSection, inner_coe_mvfderiv_subtypeVal_sphere, zero_smul, sub_zero]

/-- If `v : sphere (0 : E) 1 → E` is `C^m` at `x`, then `TauCeti.sphereTangentSection n v` is `C^m`
at `x` as a section of the tangent bundle. -/
theorem contMDiffAt_sphereTangentSection {v : sphere (0 : E) 1 → E} {x : sphere (0 : E) 1}
    (hv : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) m v x) :
    ContMDiffAt (𝓡 n) (𝓡 n).tangent m
      (fun y ↦ (⟨y, sphereTangentSection n v y⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) x := by
  rw [contMDiffAt_section_sphere_iff]
  simp only [mvfderiv_coe_sphereTangentSection]
  have hinner : ContMDiffAt (𝓡 n) 𝓘(ℝ) m (fun y : sphere (0 : E) 1 ↦ ⟪(y : E), v y⟫) x :=
    (contDiffAt_inner (𝕜 := ℝ)).comp_contMDiffAt ((contMDiff_coe_sphere x).prodMk_space hv)
  exact hv.sub (hinner.smul (contMDiff_coe_sphere x))

/-- If `v : sphere (0 : E) 1 → E` is `C^m`, then `TauCeti.sphereTangentSection n v` is a `C^m`
section of the tangent bundle of the unit sphere. -/
theorem contMDiff_sphereTangentSection {v : sphere (0 : E) 1 → E}
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, E) m v) :
    ContMDiff (𝓡 n) (𝓡 n).tangent m
      (fun x ↦ (⟨x, sphereTangentSection n v x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) :=
  fun x ↦ contMDiffAt_sphereTangentSection (hv x)

/-- If `v : sphere (0 : E) 1 → E` is continuous, then `TauCeti.sphereTangentSection n v` is a
continuous section of the tangent bundle of the unit sphere. -/
theorem continuous_sphereTangentSection {v : sphere (0 : E) 1 → E} (hv : Continuous v) :
    Continuous
      (fun x ↦ (⟨x, sphereTangentSection n v x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) := by
  rw [← contMDiff_zero_iff (I := 𝓡 n) (I' := (𝓡 n).tangent)]
  exact contMDiff_sphereTangentSection (contMDiff_zero_iff.2 hv)

/-! ### Smoothing and normalizing nowhere-vanishing tangent fields -/

/-- **Smoothing and normalizing a nowhere-vanishing tangent field.** If `v : sphere (0 : E) 1 → E`
is continuous, tangent to the sphere (`⟪v x, x⟫ = 0`), and vanishes nowhere, then the unit sphere
carries a `C^∞` unit tangent vector field `w : sphere (0 : E) 1 → E`. -/
theorem exists_contMDiff_unit_tangent_sphere_of_ne_zero {v : sphere (0 : E) 1 → E}
    (hv : Continuous v) (ht : ∀ x, ⟪v x, (x : E)⟫ = 0) (hne : ∀ x, v x ≠ 0) :
    ∃ w : sphere (0 : E) 1 → E, ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ w ∧
      (∀ x, ⟪w x, (x : E)⟫ = 0) ∧ ∀ x, ‖w x‖ = 1 := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  -- Approximate `v` within half its pointwise norm by a smooth ambient map `g`.
  obtain ⟨g, hg, -⟩ := hv.exists_contMDiff_approx (𝓡 n) ⊤ (hv.norm.div_const 2)
    fun x ↦ half_pos (norm_pos_iff.2 (hne x))
  let p : sphere (0 : E) 1 → E := fun x ↦ g x - ⟪(x : E), g x⟫ • (x : E)
  have hp_smooth : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ p := by
    have hsec := contMDiff_sphereTangentSection (n := n) (m := ∞) g.contMDiff
    simpa only [mvfderiv_coe_sphereTangentSection] using contMDiff_section_sphere_iff.1 hsec
  -- Orthogonal projection onto `x^⊥` is `1`-Lipschitz and fixes `v x`, so `p x` stays nonzero.
  have hp_proj (x : sphere (0 : E) 1) : p x = (ℝ ∙ (x : E))ᗮ.starProjection (g x) := by
    rw [Submodule.starProjection_orthogonal, sub_apply, ContinuousLinearMap.id_apply,
      Submodule.starProjection_unit_singleton ℝ (norm_eq_of_mem_sphere x)]
  have hp_ne (x : sphere (0 : E) 1) : p x ≠ 0 := by
    intro h0
    have hv_mem : v x ∈ (ℝ ∙ (x : E))ᗮ := Submodule.mem_orthogonal_singleton_iff_inner_left.2 (ht x)
    have hdiff : p x - v x = (ℝ ∙ (x : E))ᗮ.starProjection (g x - v x) := by
      rw [map_sub, ← hp_proj, Submodule.starProjection_eq_self_iff.2 hv_mem]
    have hlt : ‖p x - v x‖ < ‖v x‖ / 2 := by
      calc ‖p x - v x‖ = ‖(ℝ ∙ (x : E))ᗮ.starProjection (g x - v x)‖ := by rw [hdiff]
        _ ≤ ‖g x - v x‖ := (ℝ ∙ (x : E))ᗮ.norm_starProjection_apply_le _
        _ < ‖v x‖ / 2 := by simpa only [dist_eq_norm] using hg x
    rw [h0, zero_sub, norm_neg] at hlt
    linarith [norm_pos_iff.2 (hne x)]
  -- Normalize `p` through the punctured ambient space `E \ {0}`.
  let p' : sphere (0 : E) 1 → (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens E) :=
    fun x ↦ ⟨p x, hp_ne x⟩
  have hp'_smooth : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ p' :=
    (ContMDiff.subtypeVal_comp_iff (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens E) p').1 hp_smooth
  refine ⟨fun x ↦ NormedSpace.normalize (p x),
    (contMDiff_normalize_compl_zero (E := E) (m := ∞)).comp hp'_smooth, fun x ↦ ?_, fun x ↦ ?_⟩
  · have hp_orth : ⟪p x, (x : E)⟫ = 0 := by
      rw [hp_proj]
      exact Submodule.inner_left_of_mem_orthogonal (Submodule.mem_span_singleton_self _)
        ((ℝ ∙ (x : E))ᗮ.starProjection_apply_mem _)
    simp only [NormedSpace.normalize, real_inner_smul_left, hp_orth, mul_zero]
  · exact NormedSpace.norm_normalize_eq_one_iff.2 (hp_ne x)

/-- If the unit sphere carries a nowhere-vanishing continuous section of its tangent bundle, then
it carries a `C^∞` unit section. -/
theorem exists_contMDiff_unit_section_sphere_of_ne_zero
    {V : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
    (hV : Continuous (fun x ↦ (⟨x, V x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))))
    (hne : ∀ x, V x ≠ 0) :
    ∃ W : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x,
      ContMDiff (𝓡 n) (𝓡 n).tangent ∞
        (fun x ↦ (⟨x, W x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) ∧
      ∀ x, ‖W x‖ = 1 := by
  have hv : Continuous (fun x ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (V x)) :=
    continuous_section_sphere_iff.1 hV
  have ht (x : sphere (0 : E) 1) :
      ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (V x), (x : E)⟫ = 0 := by
    rw [real_inner_comm]
    exact inner_coe_mvfderiv_subtypeVal_sphere x (V x)
  have hv_ne (x : sphere (0 : E) 1) :
      mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (V x) ≠ 0 := by
    rw [← norm_ne_zero_iff, ← norm_tangentSpace_sphere, norm_ne_zero_iff]
    exact hne x
  obtain ⟨w, hw, hwt, hwn⟩ := exists_contMDiff_unit_tangent_sphere_of_ne_zero (n := n) hv ht hv_ne
  refine ⟨sphereTangentSection n w, contMDiff_sphereTangentSection hw, fun x ↦ ?_⟩
  rw [norm_sphereTangentSection_of_inner_eq_zero (hwt x), hwn]

/-! ### Analytic unit tangent fields on odd-dimensional spheres -/

/-- When `n` is odd, the `(n + 1)`-dimensional ambient inner product space `E` admits a linear
isometry `L : E →ₗᵢ[ℝ] E` turning every vector by a right angle (`⟪L x, x⟫ = 0`) and satisfying
`L (L x) = -x`. -/
theorem exists_linearIsometry_inner_self_eq_zero_of_odd (hn : Odd n) :
    ∃ L : E →ₗᵢ[ℝ] E, (∀ x, ⟪L x, x⟫ = 0) ∧ ∀ x, L (L x) = -x := by
  have hE : finrank ℝ E = n + 1 := Fact.out
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  obtain ⟨J, hJ⟩ := AlmostComplexStructure.exists_forall_norm_apply_eq
    (V := E) (hE ▸ hn.add_one)
  let L : E →ₗᵢ[ℝ] E := { J.toLinearMap with norm_map' := hJ }
  exact ⟨L, AlmostComplexStructure.inner_apply_self (J := J) L.inner_map_map, J.apply_apply⟩

/-- On an odd-dimensional unit sphere `Sⁿ ⊆ E`, there exists a real-analytic (`C^ω`) map
`v : E → E` that is everywhere orthogonal to the position vector and has unit norm on `Sⁿ`. -/
theorem exists_contDiff_unit_tangent_of_odd (hn : Odd n) :
    ∃ v : E → E, ContDiff ℝ ω v ∧ (∀ x, ⟪v x, x⟫ = 0) ∧ ∀ x ∈ sphere (0 : E) 1, ‖v x‖ = 1 := by
  obtain ⟨L, hL, -⟩ := exists_linearIsometry_inner_self_eq_zero_of_odd (E := E) hn
  refine ⟨fun x ↦ L x, L.toContinuousLinearMap.contDiff, hL, fun x hx ↦ ?_⟩
  rw [L.norm_map, mem_sphere_zero_iff_norm.1 hx]

/-- Every odd-dimensional unit sphere carries a real-analytic (`C^ω`) unit section of its tangent
bundle. -/
theorem exists_contMDiff_unit_section_sphere_of_odd (hn : Odd n) :
    ∃ V : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x,
      ContMDiff (𝓡 n) (𝓡 n).tangent ω
        (fun x ↦ (⟨x, V x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) ∧
      ∀ x, ‖V x‖ = 1 := by
  obtain ⟨v, hv, ht, hn1⟩ := exists_contDiff_unit_tangent_of_odd (E := E) hn
  have hv_sphere : ContMDiff (𝓡 n) 𝓘(ℝ, E) ω (fun x : sphere (0 : E) 1 ↦ v (x : E)) :=
    hv.contMDiff.comp contMDiff_coe_sphere
  refine ⟨sphereTangentSection n fun x ↦ v (x : E), contMDiff_sphereTangentSection hv_sphere,
    fun x ↦ ?_⟩
  rw [norm_sphereTangentSection_of_inner_eq_zero (ht (x : E)), hn1 (x : E) x.2]

end GeneralSphere

/-! ### Explicit coordinate tangent field on `S^(2m+1) ⊆ ℝ^(2m+2)` -/

section EuclideanOddSphere

/-- Multiplication by `i` on `EuclideanSpace ℂ (Fin m)` as a real linear isometry equivalence. -/
private def smulIComplexEuclidean (m : ℕ) :
    EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin m) where
  toFun z := Complex.I • z
  map_add' _ _ := smul_add _ _ _
  map_smul' c z := smul_comm Complex.I c z
  invFun z := (-Complex.I) • z
  left_inv z := by simp [smul_smul]
  right_inv z := by simp [smul_smul]
  norm_map' z := by simp [norm_smul]

/-- The standard orthogonal complex structure `(x₀, x₁, x₂, x₃, …) ↦ (-x₁, x₀, -x₃, x₂, …)` on
`EuclideanSpace ℝ (Fin (2 * m))`, obtained by transporting multiplication by `i` along
`TauCeti.complexEuclideanRealLinearIsometryEquiv`. -/
def euclideanPairTurn (m : ℕ) :
    EuclideanSpace ℝ (Fin (2 * m)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * m)) :=
  (complexEuclideanRealLinearIsometryEquiv m).symm.trans
    ((smulIComplexEuclidean m).trans (complexEuclideanRealLinearIsometryEquiv m))

private theorem two_mul_eq_cast_finProdFinEquiv (m : ℕ) (j : Fin m) :
    (⟨2 * j.val, by omega⟩ : Fin (2 * m)) =
      Fin.cast (Nat.mul_comm m 2) (finProdFinEquiv (j, 0)) := by
  ext
  simp [finProdFinEquiv]

private theorem two_mul_add_one_eq_cast_finProdFinEquiv (m : ℕ) (j : Fin m) :
    (⟨2 * j.val + 1, by omega⟩ : Fin (2 * m)) =
      Fin.cast (Nat.mul_comm m 2) (finProdFinEquiv (j, 1)) := by
  ext
  simp [finProdFinEquiv]
  omega

/-- On even coordinates `2j`, `TauCeti.euclideanPairTurn` returns `-x_{2j+1}`. -/
@[simp]
theorem euclideanPairTurn_apply_two_mul (m : ℕ) (x : EuclideanSpace ℝ (Fin (2 * m))) (j : Fin m) :
    euclideanPairTurn m x ⟨2 * j.val, by omega⟩ = -x ⟨2 * j.val + 1, by omega⟩ := by
  rw [two_mul_eq_cast_finProdFinEquiv, two_mul_add_one_eq_cast_finProdFinEquiv, euclideanPairTurn,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply,
    complexEuclideanRealLinearIsometryEquiv_apply_re]
  simp [smulIComplexEuclidean]

/-- On odd coordinates `2j + 1`, `TauCeti.euclideanPairTurn` returns `x_{2j}`. -/
@[simp]
theorem euclideanPairTurn_apply_two_mul_add_one (m : ℕ) (x : EuclideanSpace ℝ (Fin (2 * m)))
    (j : Fin m) :
    euclideanPairTurn m x ⟨2 * j.val + 1, by omega⟩ = x ⟨2 * j.val, by omega⟩ := by
  rw [two_mul_eq_cast_finProdFinEquiv, two_mul_add_one_eq_cast_finProdFinEquiv, euclideanPairTurn,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply,
    complexEuclideanRealLinearIsometryEquiv_apply_im]
  simp [smulIComplexEuclidean]

/-- Applying `TauCeti.euclideanPairTurn` twice negates every vector. -/
@[simp]
theorem euclideanPairTurn_apply_apply (m : ℕ) (x : EuclideanSpace ℝ (Fin (2 * m))) :
    euclideanPairTurn m (euclideanPairTurn m x) = -x := by
  simp [euclideanPairTurn, smulIComplexEuclidean, smul_smul]

/-- `TauCeti.euclideanPairTurn` turns every vector of `ℝ^(2m)` by a right angle. -/
@[simp]
theorem inner_euclideanPairTurn_self (m : ℕ) (x : EuclideanSpace ℝ (Fin (2 * m))) :
    ⟪euclideanPairTurn m x, x⟫ = 0 := by
  have h := (euclideanPairTurn m).inner_map_map (euclideanPairTurn m x) x
  rw [euclideanPairTurn_apply_apply, inner_neg_left, real_inner_comm] at h
  linarith

/-- The dimension of `ℝ^(2(m+1))`, in the form `Fact (finrank ℝ E = (2 * m + 1) + 1)` expected by
the stereographic charts of the odd-dimensional unit sphere `S^(2m+1)`. -/
theorem finrank_euclideanSpace_two_mul_succ_fact (m : ℕ) :
    Fact (finrank ℝ (EuclideanSpace ℝ (Fin (2 * (m + 1)))) = (2 * m + 1) + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

attribute [local instance] finrank_euclideanSpace_two_mul_succ_fact in
/-- The standard analytic unit tangent vector field `x ↦ (-x₁, x₀, -x₃, x₂, …)` on the
odd-dimensional unit sphere `S^(2m+1) ⊆ ℝ^(2m+2)`. -/
def oddSphereStandardSection (m : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (2 * (m + 1)))) 1) :
    TangentSpace (𝓡 (2 * m + 1)) x :=
  sphereTangentSection (2 * m + 1) (fun y ↦ euclideanPairTurn (m + 1) (y : _)) x

attribute [local instance] finrank_euclideanSpace_two_mul_succ_fact in
/-- Read in `ℝ^(2m+2)` through `mfderiv`, `TauCeti.oddSphereStandardSection` acts as
`TauCeti.euclideanPairTurn`, sending `(x₀, x₁, x₂, x₃, …)` to `(-x₁, x₀, -x₃, x₂, …)`. -/
@[simp]
theorem mfderiv_coe_oddSphereStandardSection (m : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (2 * (m + 1)))) 1) :
    (mfderiv (𝓡 (2 * m + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * (m + 1))))
      ((↑) : sphere (0 : EuclideanSpace ℝ (Fin (2 * (m + 1)))) 1 →
        EuclideanSpace ℝ (Fin (2 * (m + 1)))) x (oddSphereStandardSection m x) :
        EuclideanSpace ℝ (Fin (2 * (m + 1)))) =
      euclideanPairTurn (m + 1) (x : _) := by
  rw [oddSphereStandardSection, mfderiv_coe_sphereTangentSection, real_inner_comm,
    inner_euclideanPairTurn_self, zero_smul, sub_zero]

attribute [local instance] finrank_euclideanSpace_two_mul_succ_fact in
/-- Read in `ℝ^(2m+2)` through `mvfderiv`, `TauCeti.oddSphereStandardSection` acts as
`TauCeti.euclideanPairTurn`, sending `(x₀, x₁, x₂, x₃, …)` to `(-x₁, x₀, -x₃, x₂, …)`. -/
theorem mvfderiv_coe_oddSphereStandardSection (m : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (2 * (m + 1)))) 1) :
    mvfderiv (𝓡 (2 * m + 1))
      ((↑) : sphere (0 : EuclideanSpace ℝ (Fin (2 * (m + 1)))) 1 →
        EuclideanSpace ℝ (Fin (2 * (m + 1)))) x (oddSphereStandardSection m x) =
      euclideanPairTurn (m + 1) (x : _) := by
  rw [mvfderiv_apply_eq_mfderiv_apply, mfderiv_coe_oddSphereStandardSection]

attribute [local instance] finrank_euclideanSpace_two_mul_succ_fact in
/-- `TauCeti.oddSphereStandardSection` is real-analytic (`C^ω`). -/
theorem contMDiff_oddSphereStandardSection (m : ℕ) :
    ContMDiff (𝓡 (2 * m + 1)) (𝓡 (2 * m + 1)).tangent ω
      (fun x ↦ (⟨x, oddSphereStandardSection m x⟩ :
        TangentBundle (𝓡 (2 * m + 1))
          (sphere (0 : EuclideanSpace ℝ (Fin (2 * (m + 1)))) 1))) := by
  let L := (euclideanPairTurn (m + 1)).toContinuousLinearEquiv.toContinuousLinearMap
  exact contMDiff_sphereTangentSection (L.contDiff.contMDiff.comp contMDiff_coe_sphere)

attribute [local instance] finrank_euclideanSpace_two_mul_succ_fact in
/-- `TauCeti.oddSphereStandardSection` has unit round norm at every point, so it vanishes
nowhere. -/
theorem norm_oddSphereStandardSection (m : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (2 * (m + 1)))) 1) :
    ‖oddSphereStandardSection m x‖ = 1 := by
  rw [norm_tangentSpace_sphere, mvfderiv_coe_oddSphereStandardSection,
    LinearIsometryEquiv.norm_map, norm_eq_of_mem_sphere]

end EuclideanOddSphere

end TauCeti
