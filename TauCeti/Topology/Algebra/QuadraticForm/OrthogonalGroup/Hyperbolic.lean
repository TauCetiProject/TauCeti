/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.SpecialOrthogonal.Hyperbolic
public import TauCeti.Topology.Algebra.Module.GeneralLinearGroup
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import TauCeti.LinearAlgebra.QuadraticForm.Transvection.Basic
import Mathlib.Analysis.Normed.Field.Basic

/-!
# The special orthogonal group of the hyperbolic plane as a topological group

Over a commutative ring `R` in which two is invertible, the diagonal torus
`TauCeti.hyperbolicTorus R` identifies the units `Rˣ` with the special orthogonal group of the
hyperbolic plane `x₀² - x₁²` (`TauCeti.hyperbolicTorusEquiv`). In the isotropic basis `![1, 1]`,
`![1, -1]`, which are the coordinates of the isometric `xy`-model, the torus is `diag(t, t⁻¹)`.

This file shows that, over a topological ring, the identification is an isomorphism of topological
groups, for the unit topology on `Rˣ` and the canonical forward-and-inverse topology on linear
automorphisms restricted to `SO(H)`. The torus is continuous because its matrix entries are
`⅟2 (t ± t⁻¹)`, and its inverse is continuous because the parameter of a proper isometry `g` is a
coordinate of `g ![1, 1]`, and that of `g⁻¹` is the inverse parameter.

So every topological statement about `SO(H)` is a statement about `Rˣ`. For instance, over `ℝ`
the special orthogonal group of `x² - y²` is not compact, because `ℝˣ` is not: the torus elements
`diag(t, t⁻¹)` leave every compact set as `t` grows. In dimension two the Eichler transvections
cannot witness this, since their parameter space `u^⊥ / ℝ u` is trivial; both facts are recorded
below as worked examples.

## Main definitions

* `TauCeti.hyperbolicTorusContinuousMulEquiv`: the topological group isomorphism
  `Rˣ ≃ₜ* SO(H)`.

## Main results

* `TauCeti.continuous_hyperbolicTorus`: the diagonal torus is continuous.
* `TauCeti.continuous_hyperbolicTorusEquiv_symm`: so is its inverse, which reads off the parameter
  of a proper isometry.
-/

public section

namespace TauCeti

open _root_.TauCeti.QuadraticMap

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Invertible (2 : R)]

/-- The diagonal torus `t ↦ diag(t, t⁻¹)` of the hyperbolic plane is continuous, for the unit
topology on `Rˣ` and the forward-and-inverse topology on linear automorphisms. -/
@[fun_prop]
theorem continuous_hyperbolicTorus : Continuous (hyperbolicTorus R) := by
  -- The forward endomorphism depends continuously on `t`, by the explicit matrix entries, and
  -- the inverse endomorphism at `t` is the forward one at `t⁻¹`.
  have hforward : Continuous fun t : Rˣ ↦
      ((hyperbolicTorus R t : (Fin 2 → R) ≃ₗ[R] (Fin 2 → R)) : Module.End R (Fin 2 → R)) := by
    refine ((Pi.basisFun R (Fin 2)).continuous_iff_apply _).mpr fun i ↦ ?_
    simp only [LinearEquiv.coe_coe, hyperbolicTorus_apply, Pi.basisFun_apply]
    refine continuous_pi fun j ↦ ?_
    fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] <;>
      fun_prop
  refine Continuous.subtype_mk (continuous_linearEquiv_iff.mpr ⟨hforward, ?_⟩) _
  refine (hforward.comp continuous_inv).congr fun t ↦ ?_
  simp [map_inv]

/-- The inverse of the diagonal torus of the hyperbolic plane, which sends a proper isometry to its
parameter, is continuous. -/
@[fun_prop]
theorem continuous_hyperbolicTorusEquiv_symm : Continuous (hyperbolicTorusEquiv R).symm := by
  -- The parameter is the first coordinate of the image of `![1, 1]`, a linear function of the
  -- forward endomorphism; the parameter of `g⁻¹` is the inverse parameter.
  let φ : Module.End R (Fin 2 → R) →ₗ[R] R :=
    (LinearMap.proj 0).comp (LinearMap.applyₗ ![1, 1])
  have hφ : Continuous φ := IsModuleTopology.continuous_of_linearMap φ
  have hcoe := continuous_linearEquiv_iff.mp
    (continuous_subtype_val (p := (· ∈ specialOrthogonalGroup (hyperbolicPlane R))))
  refine Units.continuous_iff.mpr ⟨(hφ.comp hcoe.1).congr fun g ↦ ?_,
    (hφ.comp hcoe.2).congr fun g ↦ ?_⟩
  · simp [φ, coe_hyperbolicTorusEquiv_symm_apply]
  · rw [← map_inv (hyperbolicTorusEquiv R).symm, coe_hyperbolicTorusEquiv_symm_apply]
    simp [φ]

variable (R) in
/-- The diagonal torus identifies the units with the special orthogonal group of the hyperbolic
plane as topological groups. -/
noncomputable def hyperbolicTorusContinuousMulEquiv :
    Rˣ ≃ₜ* specialOrthogonalGroup (hyperbolicPlane R) where
  toMulEquiv := hyperbolicTorusEquiv R
  continuous_toFun := continuous_hyperbolicTorus.congr fun t ↦ (hyperbolicTorusEquiv_apply t).symm
  continuous_invFun := continuous_hyperbolicTorusEquiv_symm

/-- The topological isomorphism `hyperbolicTorusContinuousMulEquiv R` is the diagonal torus. -/
@[simp]
theorem hyperbolicTorusContinuousMulEquiv_apply (t : Rˣ) :
    hyperbolicTorusContinuousMulEquiv R t = hyperbolicTorus R t :=
  hyperbolicTorusEquiv_apply t

/-- The underlying group isomorphism of `hyperbolicTorusContinuousMulEquiv R` is
`hyperbolicTorusEquiv R`. -/
@[simp]
theorem coe_hyperbolicTorusContinuousMulEquiv :
    (hyperbolicTorusContinuousMulEquiv R : Rˣ ≃* specialOrthogonalGroup (hyperbolicPlane R)) =
      hyperbolicTorusEquiv R :=
  (rfl)

/-- The inverse of `hyperbolicTorusContinuousMulEquiv R` is the inverse of
`hyperbolicTorusEquiv R`. -/
@[simp]
theorem hyperbolicTorusContinuousMulEquiv_symm_apply
    (g : specialOrthogonalGroup (hyperbolicPlane R)) :
    (hyperbolicTorusContinuousMulEquiv R).symm g = (hyperbolicTorusEquiv R).symm g :=
  (rfl)

/-! ### Worked examples over `ℝ` -/

-- The special orthogonal group of `x² - y²` is not compact, as witnessed by the diagonal torus:
-- a compact `SO(H)` would make `ℝˣ` compact, and then the nonzero reals would be bounded.
example : ¬IsCompact
    (specialOrthogonalGroup (hyperbolicPlane ℝ) : Set ((Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ))) := by
  intro hcpt
  have : CompactSpace (specialOrthogonalGroup (hyperbolicPlane ℝ)) :=
    isCompact_iff_compactSpace.mp hcpt
  have hunits : IsCompact (Set.univ : Set ℝˣ) := by
    simpa using isCompact_univ.image (hyperbolicTorusContinuousMulEquiv ℝ).symm.continuous
  obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.mp
    (hunits.image Units.continuous_val).isBounded
  have h := hr _ ⟨Units.mk0 (|r| + 1) (by positivity), Set.mem_univ _, rfl⟩
  simp only [Units.val_mk0, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < |r| + 1)] at h
  linarith [le_abs_self r]

-- In dimension two the Eichler transvections cannot witness noncompactness: for the isotropic
-- vector `![1, 1]` of `x² - y²`, the parameter space `u^⊥ / ℝ u` is trivial.
example : Subsingleton (LinearMap.ker ((hyperbolicPlane ℝ).polarBilin ![1, 1]) ⧸
    (ℝ ∙ (![1, 1] : Fin 2 → ℝ)).comap
      (LinearMap.ker ((hyperbolicPlane ℝ).polarBilin ![1, 1])).subtype) := by
  refine _root_.QuadraticMap.subsingleton_transvectionParameter_of_finrank_eq_two
    (by simp) (by simp [hyperbolicPlane_apply]) fun h ↦ ?_
  have := LinearMap.congr_fun h ![1, -1]
  norm_num [polar_hyperbolicPlane] at this

end TauCeti
