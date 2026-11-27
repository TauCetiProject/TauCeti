/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Topology.Algebra.Module.BilinearForm
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs

import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import TauCeti.Geometry.Symplectic.Duality

/-!
# The topology on linear complex structures

The complex structures of a finite-dimensional real normed space carry the topology induced by
the operator norm of their endomorphisms. Since all norms on a finite-dimensional space are
equivalent, it does not depend on the choice of the norm of `V`.

## Main declarations

* The instance `TopologicalSpace (TauCeti.AlmostComplexStructure V)`: the topology induced from
  the operator norm on `V →L[ℝ] V`.
* `TauCeti.AlmostComplexStructure.isEmbedding_toContinuousLinearMap`: sending a complex
  structure to its continuous endomorphism is a topological embedding.
* `TauCeti.AlmostComplexStructure.continuous_iff`: continuity of maps into the complex
  structures is continuity of their endomorphisms in the operator norm.
* `TauCeti.AlmostComplexStructure.toContinuousLinearMap_mul_self`: in the operator-norm algebra a
  complex structure squares to `-1`.
* `TauCeti.AlmostComplexStructure.toContinuousLinearMap_cayley`: in operator-norm coordinates the
  Cayley transform is the rational expression `-(1 + J₀ J₁)(1 - J₀ J₁)⁻¹`.
* `TauCeti.AlmostComplexStructure.mul_opNorm_le_of_eq_smul_sub_smul`: if `B = (a - b J) A` with
  `a² + b² = r² > 0`, then `r ‖A‖ ≤ (1 + ‖J‖) ‖B‖`, inverting `a - b J` through
  `(a + b J) (a - b J) = a² + b²`.
* `TauCeti.AlmostComplexStructure.mul_opNorm_le_opNorm_comp_smul_add_smul`: the same inversion on
  covectors, `r ‖θ‖ ≤ (1 + ‖J‖) ‖θ ∘ (a + b J)‖`.
* `TauCeti.AlmostComplexStructure.norm_smul_add_smul_le`: the bound from above,
  `‖a + b J‖ ≤ r (1 + ‖J‖)` for `|a|, |b| ≤ r`.
* `TauCeti.AlmostComplexStructure.isInvertible_smul_id_add_smul`: `a + b J` is invertible
  whenever `a² + b² ≠ 0`, with inverse `(a² + b²)⁻¹ (a - b J)`.
* `TauCeti.SymplecticForm.Tames.eventually_of_continuousAt`: tameness is an open condition along
  families that are continuous in the operator norm.
* `TauCeti.SymplecticForm.tames_of_mul_norm_sq_le`: a uniform lower bound `c ‖v‖² ≤ ω(v, J v)`
  with `c > 0` makes `J` tame.
* `TauCeti.SymplecticForm.exists_pos_forall_mul_norm_sq_le_associatedBilinForm`: along a family
  of tame structures continuous on a compact set, the forms `ω(·, J ·)` are uniformly equivalent
  to the square of the norm.
* `TauCeti.SymplecticForm.continuousOn_associatedBilinForm_apply_self`: the forms `ω(·, J ·)` of
  a continuous family of structures, evaluated along a continuous map, vary continuously.
* `ContDiffOn.associatedBilinForm`, `DifferentiableAt.associatedBilinForm`: the forms
  `ω(·, J ·)` of a family of structures are as smooth as their endomorphisms in the operator norm.
-/

public noncomputable section

open Filter Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

namespace AlmostComplexStructure

/-- The topology on the complex structures of a finite-dimensional real normed space induced by
the operator norm of their endomorphisms. Since all norms on a finite-dimensional space are
equivalent, it does not depend on the choice of the norm of `V`. -/
instance : TopologicalSpace (AlmostComplexStructure V) :=
  .induced (fun J ↦ LinearMap.toContinuousLinearMap J.toLinearMap) inferInstance

/-- Sending a complex structure to its endomorphism is a topological embedding into the
continuous endomorphisms. -/
theorem isEmbedding_toContinuousLinearMap :
    IsEmbedding fun J : AlmostComplexStructure V ↦ LinearMap.toContinuousLinearMap J.toLinearMap :=
  ⟨⟨rfl⟩, LinearMap.toContinuousLinearMap.injective.comp toLinearMap_injective⟩

/-- A map into the complex structures is continuous exactly when its endomorphisms are
continuous in the operator norm. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → AlmostComplexStructure V} :
    Continuous f ↔ Continuous fun x ↦ LinearMap.toContinuousLinearMap (f x).toLinearMap :=
  isEmbedding_toContinuousLinearMap.continuous_iff

/-- In the operator-norm algebra, an almost complex structure squares to `-1`. -/
@[simp]
theorem toContinuousLinearMap_mul_self (J : AlmostComplexStructure V) :
    LinearMap.toContinuousLinearMap J.toLinearMap * LinearMap.toContinuousLinearMap J.toLinearMap =
      -1 := by
  ext v
  simp

/-- In operator-norm coordinates, the Cayley transform is the rational expression
`-(1 + J₀ J₁)(1 - J₀ J₁)⁻¹` of the continuous endomorphisms `J₀` and `J₁`, with the junk
inverse `0` when `1 - J₀ J₁` is not invertible on either side. -/
theorem toContinuousLinearMap_cayley (J₀ J₁ : AlmostComplexStructure V) {A B : V →L[ℝ] V}
    (hA : A.toLinearMap = J₀.toLinearMap) (hB : B.toLinearMap = J₁.toLinearMap) :
    LinearMap.toContinuousLinearMap (J₀.cayley J₁) = cayleyFormula A B := by
  have hA' : LinearMap.toContinuousLinearMap J₀.toLinearMap = A :=
    ContinuousLinearMap.coe_injective (by rw [LinearMap.coe_toContinuousLinearMap, hA])
  have hB' : LinearMap.toContinuousLinearMap J₁.toLinearMap = B :=
    ContinuousLinearMap.coe_injective (by rw [LinearMap.coe_toContinuousLinearMap, hB])
  rw [← hA', ← hB', cayley_eq_cayleyFormula]
  exact map_cayleyFormula (Module.End.toContinuousLinearMap V) J₀.toLinearMap J₁.toLinearMap

/-- The norm estimate shared by the inversions of `a ± b J`: if `a² + b² = r²` with `r ≥ 0`, then
`‖a x‖ + ‖b J x‖ ≤ r (1 + ‖J‖) ‖x‖`, since `|a|, |b| ≤ r`. -/
private theorem norm_smul_add_norm_smul_apply_le (J : AlmostComplexStructure V) {a b r : ℝ}
    (hab : a ^ 2 + b ^ 2 = r ^ 2) (hr : 0 ≤ r) (x : V) :
    ‖a • x‖ + ‖b • J x‖ ≤ r * ((1 + ‖J.toLinearMap.toContinuousLinearMap‖) * ‖x‖) := by
  have ha : |a| ≤ r := abs_le_of_sq_le_sq (by nlinarith [sq_nonneg b]) hr
  have hb : |b| ≤ r := abs_le_of_sq_le_sq (by nlinarith [sq_nonneg a]) hr
  have hJx : ‖J x‖ ≤ ‖J.toLinearMap.toContinuousLinearMap‖ * ‖x‖ :=
    J.toLinearMap.toContinuousLinearMap.le_opNorm x
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |a| * ‖x‖ + |b| * ‖J x‖ ≤ r * ‖x‖ + r * (‖J.toLinearMap.toContinuousLinearMap‖ * ‖x‖) := by
        gcongr
    _ = r * ((1 + ‖J.toLinearMap.toContinuousLinearMap‖) * ‖x‖) := by ring

/-- The operator-norm step shared by the inversions of `a ± b J`: a pointwise bound
`r² ‖A v‖ ≤ r (C ‖v‖)` with `r > 0` and `C ≥ 0` gives `r ‖A‖ ≤ C`. -/
private theorem mul_opNorm_le_of_sq_mul_norm_apply_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (h : ∀ v, r ^ 2 * ‖A v‖ ≤ r * (C * ‖v‖)) : r * ‖A‖ ≤ C := by
  rw [← abs_of_pos hr, ← Real.norm_eq_abs, ← norm_smul]
  refine (r • A).opNorm_le_bound hC fun v ↦ ?_
  rw [smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  refine le_of_mul_le_mul_left ?_ hr
  rw [← mul_assoc, ← pow_two]
  exact h v

/-- Inverting `a - b J` for an almost complex structure `J`: if `B = (a - b J) A` and
`a² + b² = r²` with `r > 0`, then `r ‖A‖ ≤ (1 + ‖J‖) ‖B‖`, since `(a + b J) (a - b J) = a² + b²`. -/
theorem mul_opNorm_le_of_eq_smul_sub_smul (J : AlmostComplexStructure V)
    {A B : V →L[ℝ] V} {a b r : ℝ} (hAB : ∀ v, B v = a • A v - b • J (A v))
    (hab : a ^ 2 + b ^ 2 = r ^ 2) (hr : 0 < r) :
    r * ‖A‖ ≤ (1 + ‖J.toLinearMap.toContinuousLinearMap‖) * ‖B‖ := by
  set NJ := ‖J.toLinearMap.toContinuousLinearMap‖
  refine mul_opNorm_le_of_sq_mul_norm_apply_le A hr (by positivity) fun v ↦ ?_
  -- Taking norms in `(a² + b²) A v = a B v + b J B v`.
  calc r ^ 2 * ‖A v‖ = ‖(a ^ 2 + b ^ 2) • A v‖ := by
        rw [norm_smul, hab, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]
    _ = ‖a • B v + b • J (B v)‖ := by rw [hAB v, J.smul_add_smul_apply_smul_sub_smul]
    _ ≤ ‖a • B v‖ + ‖b • J (B v)‖ := norm_add_le _ _
    _ ≤ r * ((1 + NJ) * ‖B v‖) := J.norm_smul_add_norm_smul_apply_le hab hr.le _
    _ ≤ r * ((1 + NJ) * (‖B‖ * ‖v‖)) := by gcongr; exact B.le_opNorm v
    _ = r * ((1 + NJ) * ‖B‖ * ‖v‖) := by ring

/-- **Inverting `a + b J` on covectors.** For an almost complex structure `J` and `a² + b² = r²`
with `r > 0`, every continuous linear map `θ` out of `V`, such as a covector, satisfies
`r ‖θ‖ ≤ (1 + ‖J‖) ‖θ ∘ (a + b J)‖`, since `(a + b J) (a - b J) = a² + b²`. This is the covector
counterpart of `mul_opNorm_le_of_eq_smul_sub_smul`. -/
theorem mul_opNorm_le_opNorm_comp_smul_add_smul {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (J : AlmostComplexStructure V) (θ : V →L[ℝ] F) {a b r : ℝ}
    (hab : a ^ 2 + b ^ 2 = r ^ 2) (hr : 0 < r) :
    r * ‖θ‖ ≤ (1 + ‖J.toLinearMap.toContinuousLinearMap‖) *
      ‖θ.comp (a • (1 : V →L[ℝ] V) + b • J.toLinearMap.toContinuousLinearMap)‖ := by
  set NJ := ‖J.toLinearMap.toContinuousLinearMap‖
  set θ' := θ.comp (a • (1 : V →L[ℝ] V) + b • J.toLinearMap.toContinuousLinearMap)
  refine mul_opNorm_le_of_sq_mul_norm_apply_le θ hr (by positivity) fun v ↦ ?_
  -- `θ' (a v - b J v) = θ ((a² + b²) v) = r² θ v`.
  have hθ' : θ' (a • v - b • J v) = r ^ 2 • θ v := by
    have h := J.smul_add_smul_apply_smul_sub_smul a b v
    simp only [θ', ContinuousLinearMap.comp_apply, add_apply,
      smul_apply, one_apply_eq_self, LinearMap.coe_toContinuousLinearMap']
    rw [h, map_smul, hab]
  calc r ^ 2 * ‖θ v‖ = ‖θ' (a • v - b • J v)‖ := by
        rw [hθ', norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]
    _ ≤ ‖θ'‖ * ‖a • v - b • J v‖ := θ'.le_opNorm _
    _ ≤ ‖θ'‖ * (‖a • v‖ + ‖b • J v‖) := by gcongr; exact norm_sub_le _ _
    _ ≤ ‖θ'‖ * (r * ((1 + NJ) * ‖v‖)) := by
        gcongr; exact J.norm_smul_add_norm_smul_apply_le hab hr.le v
    _ = r * ((1 + NJ) * ‖θ'‖ * ‖v‖) := by ring

/-- **Bounding `a + b J` from above.** For an almost complex structure `J` and `|a|, |b| ≤ r`, the
operator norm of `a + b J` is at most `r (1 + ‖J‖)`. This is the upper-bound counterpart of
`mul_opNorm_le_opNorm_comp_smul_add_smul`. -/
theorem norm_smul_add_smul_le (J : AlmostComplexStructure V) {a b r : ℝ} (ha : |a| ≤ r)
    (hb : |b| ≤ r) :
    ‖a • (1 : V →L[ℝ] V) + b • J.toLinearMap.toContinuousLinearMap‖ ≤
      r * (1 + ‖J.toLinearMap.toContinuousLinearMap‖) := by
  have hr : 0 ≤ r := (abs_nonneg a).trans ha
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |a| * ‖(1 : V →L[ℝ] V)‖ + |b| * ‖J.toLinearMap.toContinuousLinearMap‖ ≤
        r * 1 + r * ‖J.toLinearMap.toContinuousLinearMap‖ := by
        gcongr
        exact ContinuousLinearMap.norm_id_le
    _ = _ := by ring

/-- For an almost complex structure `J`, `a + b J` is invertible whenever `a² + b² ≠ 0`, with
inverse `(a² + b²)⁻¹ (a - b J)`, since `(a + b J) (a - b J) = (a - b J) (a + b J) = a² + b²`. -/
theorem isInvertible_smul_id_add_smul (J : AlmostComplexStructure V) {a b : ℝ}
    (h : a ^ 2 + b ^ 2 ≠ 0) :
    (a • ContinuousLinearMap.id ℝ V + b • J.toLinearMap.toContinuousLinearMap).IsInvertible := by
  refine .of_inverse (g := (a ^ 2 + b ^ 2)⁻¹ •
      (a • ContinuousLinearMap.id ℝ V - b • J.toLinearMap.toContinuousLinearMap))
    (ContinuousLinearMap.ext fun v ↦ ?_) (ContinuousLinearMap.ext fun v ↦ ?_) <;>
    conv_rhs => rw [ContinuousLinearMap.id_apply, ← inv_smul_smul₀ h v]
  all_goals
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_apply, add_apply,
      sub_apply, LinearMap.coe_toContinuousLinearMap', map_add, map_sub, map_smul, J.apply_apply]
    module

end AlmostComplexStructure

namespace SymplecticForm

/-- Tameness is an open condition: if a family of complex structures is continuous at `x` in
the operator-norm topology and `ω`-tame there, it is `ω`-tame near `x`. -/
theorem Tames.eventually_of_continuousAt {X : Type*} [TopologicalSpace X] {ω : SymplecticForm V}
    {J : X → AlmostComplexStructure V} {x : X}
    (hJ : ContinuousAt (fun y => LinearMap.toContinuousLinearMap (J y).toLinearMap) x)
    (h : ω.Tames (J x)) : ∀ᶠ y in 𝓝 x, ω.Tames (J y) := by
  -- The endomorphisms tamed by the fixed form `ω` form an open set.
  filter_upwards [hJ.eventually ((isOpen_setOf_forall_endomorphism_pos
    ω.toBilinForm.toContinuousBilinearMap).mem_nhds fun v hv ↦ by simpa using h v hv)]
    with y hy v hv
  simpa using hy v hv

omit [FiniteDimensional ℝ V] in
/-- A uniform lower bound `c ‖v‖² ≤ ω(v, J v)` with `c > 0` makes `J` tame. Conversely, a family
of tame structures that is continuous on a compact set satisfies such a bound uniformly
(`TauCeti.SymplecticForm.exists_pos_forall_mul_norm_sq_le_associatedBilinForm`). -/
theorem tames_of_mul_norm_sq_le {ω : SymplecticForm V} {J : AlmostComplexStructure V} {c : ℝ}
    (hc : 0 < c) (h : ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J v)) : ω.Tames J :=
  fun v hv ↦ (mul_pos hc (pow_pos (norm_pos_iff.2 hv) 2)).trans_le (h v)

/-- **Uniform equivalence of tame metrics.** If a family of complex structures `J_x` is continuous
in the operator norm on a compact set `K` and `ω`-tame there, the forms `g_x = ω(·, J_x ·)` are
uniformly equivalent to the square of the norm over `K`: there are constants `a > 0` and `b ≥ 0`
with `a ‖v‖² ≤ g_x(v, v) ≤ b ‖v‖²` for every `x ∈ K` and every vector `v`. -/
theorem exists_pos_forall_mul_norm_sq_le_associatedBilinForm (ω : SymplecticForm V)
    {X : Type*} [TopologicalSpace X] {J : X → AlmostComplexStructure V} {K : Set X}
    (hK : IsCompact K)
    (hJ : ContinuousOn (fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) K)
    (hJt : ∀ x ∈ K, ω.Tames (J x)) :
    ∃ a > 0, ∃ b ≥ 0, ∀ x ∈ K, ∀ v,
      a * ‖v‖ ^ 2 ≤ ω.associatedBilinForm (J x) v v ∧
        ω.associatedBilinForm (J x) v v ≤ b * ‖v‖ ^ 2 := by
  set e : X → V →L[ℝ] V := fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap
  set ωc := ω.toBilinForm.toContinuousBilinearMap
  obtain ⟨a, ha, hlow⟩ := (hK.image_of_continuousOn hJ).exists_pos_forall_mul_norm_sq_le_compRight
    ωc (by
      rintro _ ⟨x, hx, rfl⟩ v hv
      simpa [e, ωc] using hJt x hx v hv)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hJ
  refine ⟨a, ha, ‖ωc‖ * max M 0, by positivity, fun x hx v ↦
    ⟨by simpa [e, ωc] using hlow _ ⟨x, hx, rfl⟩ v, ?_⟩⟩
  have h₁ : ω.associatedBilinForm (J x) v v = ωc v (e x v) := by simp [e, ωc]
  rw [h₁]
  calc ωc v (e x v) ≤ ‖ωc v (e x v)‖ := Real.le_norm_self _
    _ ≤ ‖ωc‖ * ‖v‖ * ‖e x v‖ := ωc.le_opNorm₂ _ _
    _ ≤ ‖ωc‖ * ‖v‖ * (max M 0 * ‖v‖) := by
        gcongr
        exact (e x).le_opNorm v |>.trans
          (mul_le_mul_of_nonneg_right ((hM x hx).trans (le_max_left _ _)) (norm_nonneg _))
    _ = ‖ωc‖ * max M 0 * ‖v‖ ^ 2 := by ring

/-- The map `x ↦ g_x(f x, f x)` for `g_x = ω(·, J(x) ·)` is continuous on a set when `J` and `f`
are. -/
theorem continuousOn_associatedBilinForm_apply_self {ω : SymplecticForm V} {X : Type*}
    [TopologicalSpace X] {J : X → AlmostComplexStructure V} {s : Set X}
    (hJc : ContinuousOn (fun x ↦ (J x).toLinearMap.toContinuousLinearMap) s) {f : X → V}
    (hf : ContinuousOn f s) :
    ContinuousOn (fun x ↦ ω.associatedBilinForm (J x) (f x) (f x)) s := by
  simpa using ω.continuousOn_apply_comp hf (hJc.clm_apply hf)

variable (ω : SymplecticForm V)

/-- The metric `ω(·, J ·)` is the image of the endomorphism `J` under a continuous linear map. -/
theorem toContinuousBilinearMap_associatedBilinForm (J : AlmostComplexStructure V) :
    (ω.associatedBilinForm J).toContinuousBilinearMap =
      (ContinuousLinearMap.compL ℝ V V ℝ).flip (LinearMap.toContinuousLinearMap J.toLinearMap) ∘L
        ω.toBilinForm.toContinuousBilinearMap := by
  ext u v
  simp [associatedBilinForm_apply]

/-- The metrics `ω(·, J x ·)` of a family of complex structures depend `C^n` on `x ∈ s` when the
endomorphisms `J x` do, in the operator norm. -/
theorem _root_.ContDiffOn.associatedBilinForm {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {s : Set P} {n : WithTop ℕ∞} {J : P → AlmostComplexStructure V}
    (hJ : ContDiffOn ℝ n (fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) s) :
    ContDiffOn ℝ n (fun x ↦ (ω.associatedBilinForm (J x)).toContinuousBilinearMap) s := by
  have h := ((ContinuousLinearMap.compL ℝ V V ℝ).flip.contDiff.comp_contDiffOn hJ).clm_comp
    (contDiffOn_const (c := ω.toBilinForm.toContinuousBilinearMap))
  exact h.congr fun x _ ↦ ω.toContinuousBilinearMap_associatedBilinForm (J x)

/-- The metrics `ω(·, J x ·)` of a family of complex structures are differentiable at every point
where the endomorphisms `J x` are, in the operator norm. -/
theorem _root_.DifferentiableAt.associatedBilinForm {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {x : P} {J : P → AlmostComplexStructure V}
    (hJ : DifferentiableAt ℝ (fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) x) :
    DifferentiableAt ℝ (fun x ↦ (ω.associatedBilinForm (J x)).toContinuousBilinearMap) x :=
  (((ContinuousLinearMap.compL ℝ V V ℝ).flip.differentiableAt.comp x hJ).clm_comp
    (differentiableAt_const ω.toBilinForm.toContinuousBilinearMap)).congr_of_eventuallyEq
      (.of_forall fun y ↦ ω.toContinuousBilinearMap_associatedBilinForm (J y))

end SymplecticForm

end TauCeti
