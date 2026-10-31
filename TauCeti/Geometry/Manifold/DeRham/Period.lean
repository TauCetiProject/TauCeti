/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.PathIntegral
public import TauCeti.Geometry.Manifold.DifferentialForm.LocalPrimitive
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Integrals of closed `1`-forms along continuous paths, and periods

A closed `C¹` `1`-form `φ` can be integrated along every continuous path, and the integral only
depends on the homotopy class of the path relative to its endpoints. The integral along a path
`γ` from `x` to `y` is `TauCeti.pathClassIntegral φ γ`. It is computed by lifting `γ` to the
covering space `TauCeti.PrimitiveSpace φ` of local primitives: a lift is a primitive of `φ` along
the path, and the integral is the change of its value (`TauCeti.pathClassIntegral_mk_eq_sub`).
Equivalently, the monodromy of the covering along `γ` translates values by the integral
(`TauCeti.PrimitiveSpace.value_monodromy`), which gives homotopy invariance for free.

The integral is additive under concatenation (`TauCeti.pathClassIntegral_trans`), linear in the
form (`TauCeti.pathClassIntegral_smul_add_smul`), equal to the endpoint difference of a primitive
for exact forms (`TauCeti.pathClassIntegral_mextDeriv_ofFunction`), and equal to the line integral
`TauCeti.pathIntegral` along `C¹` curves (`TauCeti.pathClassIntegral_mk_eq_pathIntegral`).

On loops at `x` it is the **period homomorphism** `TauCeti.periodHom φ x` from the fundamental
group to the coefficients. For smooth real closed forms it only depends on the de Rham class, and on
a connected manifold a closed form is exact exactly when all its periods vanish
(`TauCeti.mem_exactForms_one_iff_periodHom_eq_zero`). Hence the periods give an injective linear
map `TauCeti.deRhamCohomology.period` from `H¹_dR(M)` to the homomorphisms `π₁(M, x) → ℝ`.

## Main declarations

* `TauCeti.pathClassIntegral φ γ`: the integral of a closed `C¹` `1`-form along a homotopy class
  of paths.
* `TauCeti.periodHom φ x`: the period homomorphism of `φ` on the fundamental group at `x`.
* `TauCeti.mem_exactForms_one_iff_periodHom_eq_zero`: a closed smooth real `1`-form on a connected
  manifold is exact exactly when its periods vanish.
* `TauCeti.deRhamCohomology.period`: the periods of de Rham classes in degree one, an injective
  linear map on a connected manifold.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11, section *Conservative
  Covector Fields*, and Chapter 17.
* Allen Hatcher, *Algebraic Topology*, Section 1.3 (path lifting and monodromy).
* M. Farber, *Topology of Closed One-Forms*, Section 1.1 (the homomorphism of periods).
-/

public section

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] [CompleteSpace F]
  {φ ψ : RoughForm I M F 1} {x y z : M}

open Classical in
/-- The integral of a closed `C¹` `1`-form `φ` along a homotopy class `γ` of paths from `x` to `y`:
the value at the end of the lift of `γ` to the covering space of local primitives of `φ` which
starts at `x` with value `0`. It is `0` when `φ` is not a closed `C¹` form. -/
def pathClassIntegral (φ : RoughForm I M F 1) (γ : Path.Homotopic.Quotient x y) : F :=
  if h : IsSmoothForm I 1 φ ∧ mextDeriv φ = 0 then
    PrimitiveSpace.value φ ((PrimitiveSpace.isCoveringMap_proj (r := 1) le_rfl h.1 h.2).monodromy
      γ ⟨PrimitiveSpace.graph φ 0 x, PrimitiveSpace.proj_graph x⟩)
  else 0

/-- The integral of a form which is not a closed `C¹` form is `0` by convention. -/
theorem pathClassIntegral_undef (h : ¬(IsSmoothForm I 1 φ ∧ mextDeriv φ = 0))
    (γ : Path.Homotopic.Quotient x y) : pathClassIntegral φ γ = 0 :=
  dite_eq_right h

/-- **Integration along a lift.** If `Γ` is a continuous lift of the path `γ` to the covering space
of local primitives of a closed `C¹` form `φ`, then the integral of `φ` along `γ` is the change of
the value of `Γ`. -/
theorem pathClassIntegral_mk_eq_sub (hφ : IsSmoothForm I 1 φ) (hclosed : mextDeriv φ = 0)
    {γ : Path x y} {Γ : unitInterval → PrimitiveSpace φ} (hΓ : Continuous Γ)
    (hΓγ : ∀ t, PrimitiveSpace.proj φ (Γ t) = γ t) :
    pathClassIntegral φ (.mk γ) = PrimitiveSpace.value φ (Γ 1) - PrimitiveSpace.value φ (Γ 0) := by
  have hp := PrimitiveSpace.isCoveringMap_proj (r := 1) le_rfl hφ hclosed
  -- translate the lift so that it starts with value `0`
  let Γ' : C(unitInterval, PrimitiveSpace φ) :=
    ⟨fun t ↦ PrimitiveSpace.translate φ (-PrimitiveSpace.value φ (Γ 0)) (Γ t),
      (PrimitiveSpace.continuous_translate _).comp hΓ⟩
  have hΓ'0 : Γ' 0 = PrimitiveSpace.graph φ 0 x :=
    PrimitiveSpace.ext (by simp [Γ', hΓγ]) (by simp [Γ'])
  rw [pathClassIntegral, dite_eq_left (⟨hφ, hclosed⟩ : IsSmoothForm I 1 φ ∧ mextDeriv φ = 0),
    hp.monodromy_eq_apply_one (Γ := Γ') (funext fun t ↦ by simp [Γ', hΓγ]) hΓ'0]
  simp [Γ', sub_eq_add_neg]

/-- The monodromy of the covering space of local primitives along `γ` translates values by the
integral of `φ` along `γ`. -/
theorem PrimitiveSpace.value_monodromy (hφ : IsSmoothForm I 1 φ) (hclosed : mextDeriv φ = 0)
    (γ : Path.Homotopic.Quotient x y) (e : PrimitiveSpace.proj φ ⁻¹' {x}) :
    PrimitiveSpace.value φ
        ((PrimitiveSpace.isCoveringMap_proj (r := 1) le_rfl hφ hclosed).monodromy γ e) =
      PrimitiveSpace.value φ e + pathClassIntegral φ γ := by
  have hp := PrimitiveSpace.isCoveringMap_proj (r := 1) le_rfl hφ hclosed
  induction γ with | mk γ =>
  have he : γ 0 = PrimitiveSpace.proj φ e := γ.source.trans e.2.symm
  rw [pathClassIntegral_mk_eq_sub hφ hclosed (hp.liftPath γ e he).continuous
    (fun t ↦ congrFun (hp.liftPath_lifts γ e he) t), hp.liftPath_zero,
    ← hp.coe_monodromy_mk γ e]
  abel

/-- The integral along a constant path vanishes. -/
@[simp]
theorem pathClassIntegral_refl (x : M) :
    pathClassIntegral φ (.refl x) = 0 := by
  by_cases h : IsSmoothForm I 1 φ ∧ mextDeriv φ = 0
  · have e := PrimitiveSpace.value_monodromy h.1 h.2 (.refl x)
      ⟨PrimitiveSpace.graph φ 0 x, PrimitiveSpace.proj_graph x⟩
    rw [(PrimitiveSpace.isCoveringMap_proj (r := 1) le_rfl h.1 h.2).monodromy_refl, id,
      PrimitiveSpace.value_graph] at e
    simpa using e.symm
  · exact pathClassIntegral_undef h _

/-- The integral along a concatenation of paths is the sum of the integrals. -/
@[simp]
theorem pathClassIntegral_trans (γ : Path.Homotopic.Quotient x y)
    (γ' : Path.Homotopic.Quotient y z) :
    pathClassIntegral φ (γ.trans γ') = pathClassIntegral φ γ + pathClassIntegral φ γ' := by
  by_cases h : IsSmoothForm I 1 φ ∧ mextDeriv φ = 0
  · have hp := PrimitiveSpace.isCoveringMap_proj (r := 1) le_rfl h.1 h.2
    have e := PrimitiveSpace.value_monodromy h.1 h.2 (γ.trans γ')
      ⟨PrimitiveSpace.graph φ 0 x, PrimitiveSpace.proj_graph x⟩
    rw [hp.monodromy_trans_apply, PrimitiveSpace.value_monodromy h.1 h.2,
      PrimitiveSpace.value_monodromy h.1 h.2] at e
    simpa using e.symm
  · simp [pathClassIntegral_undef h]

/-- The integral along the reversed path is the negative of the integral. -/
@[simp]
theorem pathClassIntegral_symm (γ : Path.Homotopic.Quotient x y) :
    pathClassIntegral φ γ.symm = -pathClassIntegral φ γ := by
  rw [eq_neg_iff_add_eq_zero, ← pathClassIntegral_trans, Path.Homotopic.Quotient.symm_trans,
    pathClassIntegral_refl]

/-- **The fundamental theorem of calculus for path classes.** The integral of the differential of
a `C²` function along a path class is the difference of the values of the function at the
endpoints. -/
theorem pathClassIntegral_mextDeriv_ofFunction {g : M → F} (hg : ContMDiff I 𝓘(ℝ, F) 2 g)
    (γ : Path.Homotopic.Quotient x y) :
    pathClassIntegral (mextDeriv (RoughForm.ofFunction I g)) γ = g y - g x := by
  induction γ with | mk γ =>
  set φ := mextDeriv (RoughForm.ofFunction I g)
  have hφ : IsSmoothForm I 1 φ :=
    isSmoothForm_mextDeriv (isSmoothForm_ofFunction_iff.mpr hg) (by norm_num)
  have hgU : IsPrimitiveOn φ g univ :=
    ⟨isOpen_univ, (hg.mdifferentiable (by norm_num)).mdifferentiableOn, fun _ _ ↦ rfl⟩
  -- the graph of the global primitive `g` along `γ` is a lift of `γ`
  rw [pathClassIntegral_mk_eq_sub hφ (mextDeriv_mextDeriv_ofFunction hg)
    ((PrimitiveSpace.continuousOn_graph hgU).comp_continuous γ.continuous fun _ ↦ mem_univ _)
    (fun t ↦ PrimitiveSpace.proj_graph (γ t))]
  simp

/-- **The fundamental theorem of calculus for path classes**, for a `C²` form `ψ` of degree zero:
the integral of `dψ` along a path class is the difference of the values of `ψ` at the
endpoints. -/
theorem pathClassIntegral_mextDeriv {ψ : RoughForm I M F 0} (hψ : IsSmoothForm I 2 ψ)
    (γ : Path.Homotopic.Quotient x y) :
    pathClassIntegral (mextDeriv ψ) γ = ψ y 0 - ψ x 0 := by
  rw [RoughForm.eq_ofFunction ψ, isSmoothForm_ofFunction_iff] at hψ
  have h := pathClassIntegral_mextDeriv_ofFunction hψ γ
  rwa [← RoughForm.eq_ofFunction] at h

/-- **Path classes of smooth curves.** The integral of a closed `C¹` form along the class of a
path which follows a `C¹` curve `c` is the line integral along `c`. -/
theorem pathClassIntegral_mk_eq_pathIntegral (hφ : IsSmoothForm I 1 φ)
    (hclosed : mextDeriv φ = 0) {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) {γ : Path x y}
    (hγ : ∀ t : unitInterval, γ t = c t) : pathClassIntegral φ (.mk γ) = pathIntegral φ c 0 1 := by
  have hφ₀ : IsSmoothForm I 0 φ := hφ.of_le (by norm_num)
  have hint := hφ₀.intervalIntegrable_apply_curveVelocity hc
  -- the lift: follow `γ`, with value the line integral from `0`
  let Γ (t : unitInterval) : PrimitiveSpace φ :=
    PrimitiveSpace.graph φ (fun _ ↦ pathIntegral φ c 0 t) (γ t)
  have hΓ : Continuous Γ := continuous_iff_continuousAt.mpr fun t₀ ↦ by
    obtain ⟨g, hg, U, hxU, hgU⟩ := exists_contMDiff_isPrimitiveOn le_rfl hφ hclosed (c t₀)
    -- near `t₀`, the curve stays in `U`, where `φ = dg`
    obtain ⟨δ, hδ, hball⟩ :=
      Metric.isOpen_iff.mp (hgU.isOpen.preimage hc.continuous) (t₀ : ℝ) hxU
    refine PrimitiveSpace.continuousAt_of_eventually_value_eq
      (by simp only [Γ, PrimitiveSpace.proj_graph]; exact γ.continuous.continuousAt)
      (hgU.add_const (pathIntegral φ c 0 t₀ - g (c t₀)))
      (by simp only [Γ, PrimitiveSpace.proj_graph, hγ]; exact hxU) ?_
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds (t₀ : ℝ) hδ)] with s hs
    have hsub : uIcc (t₀ : ℝ) s ⊆ c ⁻¹' U := by
      refine (Set.OrdConnected.uIcc_subset ?_ (Metric.mem_ball_self (x := (t₀ : ℝ)) hδ) hs).trans
        hball
      rw [Real.ball_eq_Ioo]
      exact ordConnected_Ioo
    simp only [PrimitiveSpace.value_graph, PrimitiveSpace.proj_graph, Γ, hγ]
    rw [← pathIntegral_add_adjacent (hint 0 t₀) (hint t₀ s),
      pathIntegral_congr (ψ := mextDeriv (RoughForm.ofFunction I g))
        fun t ht ↦ (hgU.mextDeriv_eq _ (hsub ht)).symm,
      pathIntegral_mextDeriv_ofFunction hg hc]
    abel
  rw [pathClassIntegral_mk_eq_sub hφ hclosed hΓ fun t ↦ PrimitiveSpace.proj_graph (γ t)]
  simp [Γ]

/-! ### Linearity in the form -/

/-- Integration along path classes is linear in the closed `C¹` form. -/
theorem pathClassIntegral_smul_add_smul (hφ : IsSmoothForm I 1 φ) (hφc : mextDeriv φ = 0)
    (hψ : IsSmoothForm I 1 ψ) (hψc : mextDeriv ψ = 0) (a b : ℝ)
    (γ : Path.Homotopic.Quotient x y) :
    pathClassIntegral (a • φ + b • ψ) γ =
      a • pathClassIntegral φ γ + b • pathClassIntegral ψ γ := by
  induction γ with | mk γ =>
  have hpφ := PrimitiveSpace.isCoveringMap_proj (r := 1) le_rfl hφ hφc
  have hpψ := PrimitiveSpace.isCoveringMap_proj (r := 1) le_rfl hψ hψc
  -- lifts of `γ` for `φ` and for `ψ`
  obtain ⟨Γ, hΓγ, -⟩ := hpφ.exists_path_lifts γ.toContinuousMap (PrimitiveSpace.graph φ 0 x)
    (by simp)
  obtain ⟨Δ, hΔγ, -⟩ := hpψ.exists_path_lifts γ.toContinuousMap (PrimitiveSpace.graph ψ 0 x)
    (by simp)
  have hΓγ' (t : unitInterval) : PrimitiveSpace.proj φ (Γ t) = γ t := congrFun hΓγ t
  have hΔγ' (t : unitInterval) : PrimitiveSpace.proj ψ (Δ t) = γ t := congrFun hΔγ t
  have hsmooth : IsSmoothForm I 1 (a • φ + b • ψ) := (hφ.smul a).add (hψ.smul b)
  have hclosed : mextDeriv (a • φ + b • ψ) = 0 := by
    funext p
    rw [mextDeriv_add
      (((hφ.smul a).contDiffWithinAt_inChartAt_self p).differentiableWithinAt one_ne_zero)
      (((hψ.smul b).contDiffWithinAt_inChartAt_self p).differentiableWithinAt one_ne_zero),
      mextDeriv_smul, mextDeriv_smul, hφc, hψc]
    simp
  -- the same linear combination of the values is a lift of `γ` for `a • φ + b • ψ`
  let Λ (t : unitInterval) : PrimitiveSpace (a • φ + b • ψ) :=
    PrimitiveSpace.graph _ (fun _ ↦ a • PrimitiveSpace.value φ (Γ t) +
      b • PrimitiveSpace.value ψ (Δ t)) (γ t)
  have hΛ : Continuous Λ := continuous_iff_continuousAt.mpr fun t₀ ↦ by
    obtain ⟨g, -, U, hxU, hgU, c, hc⟩ :=
      PrimitiveSpace.exists_isPrimitiveOn_eventually_value_eq le_rfl hφ hφc
        Γ.continuous.continuousAt (t := t₀)
    obtain ⟨h, -, V, hxV, hhV, d, hd⟩ :=
      PrimitiveSpace.exists_isPrimitiveOn_eventually_value_eq le_rfl hψ hψc
        Δ.continuous.continuousAt (t := t₀)
    refine PrimitiveSpace.continuousAt_of_eventually_value_eq
      (by simp only [Λ, PrimitiveSpace.proj_graph]; exact γ.continuous.continuousAt)
      (((hgU.const_smul a).add (hhV.const_smul b)).add_const (a • c + b • d))
      (by simp only [Λ, PrimitiveSpace.proj_graph]; rw [hΓγ'] at hxU; rw [hΔγ'] at hxV
          exact ⟨hxU, hxV⟩) ?_
    filter_upwards [hc, hd] with s hcs hds
    simp only [PrimitiveSpace.value_graph, PrimitiveSpace.proj_graph, Λ, hcs.2, hds.2, hΓγ',
      hΔγ', Pi.add_apply, Pi.smul_apply, smul_add]
    abel
  rw [pathClassIntegral_mk_eq_sub hsmooth hclosed hΛ fun t ↦ PrimitiveSpace.proj_graph (γ t),
    pathClassIntegral_mk_eq_sub hφ hφc Γ.continuous hΓγ',
    pathClassIntegral_mk_eq_sub hψ hψc Δ.continuous hΔγ']
  simp only [PrimitiveSpace.value_graph, Λ, smul_sub]
  abel

/-- Integration along path classes is additive in the closed `C¹` form. -/
theorem pathClassIntegral_add (hφ : IsSmoothForm I 1 φ) (hφc : mextDeriv φ = 0)
    (hψ : IsSmoothForm I 1 ψ) (hψc : mextDeriv ψ = 0) (γ : Path.Homotopic.Quotient x y) :
    pathClassIntegral (φ + ψ) γ = pathClassIntegral φ γ + pathClassIntegral ψ γ := by
  simpa using pathClassIntegral_smul_add_smul hφ hφc hψ hψc 1 1 γ

/-- The integral of the zero form vanishes. -/
@[simp]
theorem pathClassIntegral_zero (γ : Path.Homotopic.Quotient x y) :
    pathClassIntegral (0 : RoughForm I M F 1) γ = 0 := by
  have h0 := IsSmoothForm.zero (I := I) (M := M) (F := F) (k := 1) 1
  simpa using pathClassIntegral_smul_add_smul h0 mextDeriv_zero h0 mextDeriv_zero 0 0 γ

/-- Integration along path classes commutes with real scalar multiplication of the form. -/
@[simp]
theorem pathClassIntegral_smul (a : ℝ) (γ : Path.Homotopic.Quotient x y) :
    pathClassIntegral (a • φ) γ = a • pathClassIntegral φ γ := by
  by_cases h : IsSmoothForm I 1 φ ∧ mextDeriv φ = 0
  · simpa using pathClassIntegral_smul_add_smul h.1 h.2 h.1 h.2 a 0 γ
  · rcases eq_or_ne a 0 with rfl | ha
    · simp
    · have h' : ¬(IsSmoothForm I 1 (a • φ) ∧ mextDeriv (a • φ) = 0) := fun h' ↦ h
        ⟨by simpa [ha] using h'.1.smul a⁻¹, by simpa [ha] using h'.2⟩
      rw [pathClassIntegral_undef h, pathClassIntegral_undef h', smul_zero]

/-! ### The period homomorphism -/

variable (φ) in
/-- The **period homomorphism** of a `1`-form `φ` at `x`: the integral of `φ` along loops at `x`,
as a homomorphism from the fundamental group to the coefficients. It is meaningful for closed
`C¹` forms, and `0` otherwise. -/
def periodHom (x : M) : Additive (FundamentalGroup M x) →+ F where
  toFun γ := pathClassIntegral φ (Additive.toMul γ).toPath
  map_zero' := pathClassIntegral_refl x
  map_add' γ γ' := by
    rw [toMul_add, FundamentalGroup.mul_def, add_comm]
    exact pathClassIntegral_trans _ _

@[simp]
theorem periodHom_apply (x : M) (γ : Additive (FundamentalGroup M x)) :
    periodHom φ x γ = pathClassIntegral φ (Additive.toMul γ).toPath :=
  (rfl)

/-- The periods of a sum of closed `C¹` forms are the sums of their periods. -/
theorem periodHom_add (hφ : IsSmoothForm I 1 φ) (hφc : mextDeriv φ = 0)
    (hψ : IsSmoothForm I 1 ψ) (hψc : mextDeriv ψ = 0) (x : M) :
    periodHom (φ + ψ) x = periodHom φ x + periodHom ψ x :=
  AddMonoidHom.ext fun _ ↦ pathClassIntegral_add hφ hφc hψ hψc _

/-- The periods of a real multiple of a form are the multiples of its periods. -/
@[simp]
theorem periodHom_smul (a : ℝ) (x : M) : periodHom (a • φ) x = a • periodHom φ x :=
  AddMonoidHom.ext fun _ ↦ pathClassIntegral_smul a _

/-- The periods of the zero form vanish. -/
@[simp]
theorem periodHom_zero (x : M) : periodHom (0 : RoughForm I M F 1) x = 0 :=
  AddMonoidHom.ext fun _ ↦ pathClassIntegral_zero _

/-- The period of a closed `C¹` form along the class of a `C¹` loop is its line integral. -/
theorem periodHom_ofMul_eq_pathIntegral (hφ : IsSmoothForm I 1 φ) (hclosed : mextDeriv φ = 0)
    {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) {γ : Path x x} (hγ : ∀ t : unitInterval, γ t = c t) :
    periodHom φ x (Additive.ofMul (.of (.mk γ))) = pathIntegral φ c 0 1 :=
  pathClassIntegral_mk_eq_pathIntegral hφ hclosed hc hγ

/-! ### Periods of smooth real forms and de Rham cohomology -/

/-- Exact smooth real `1`-forms have vanishing periods. -/
theorem periodHom_eq_zero_of_mem_exactForms {φ : SmoothForm I M ℝ 1}
    (hφ : φ ∈ exactForms I M 1) (x : M) : periodHom (φ : RoughForm I M ℝ 1) x = 0 := by
  rw [exactForms_succ, LinearMap.mem_range] at hφ
  obtain ⟨ψ, rfl⟩ := hφ
  refine AddMonoidHom.ext fun γ ↦ ?_
  rw [periodHom_apply, AddMonoidHom.zero_apply, mextDerivₗ_apply,
    pathClassIntegral_mextDeriv (ψ.isSmoothForm.of_le (by simp)), sub_self]

/-- **Periods detect exactness.** A closed smooth real `1`-form on a connected manifold is exact
exactly when all its periods at a base point `x₀` vanish. -/
theorem mem_exactForms_one_iff_periodHom_eq_zero [PreconnectedSpace M]
    {φ : SmoothForm I M ℝ 1} (hφ : φ ∈ closedForms I M 1) (x₀ : M) :
    φ ∈ exactForms I M 1 ↔ periodHom (φ : RoughForm I M ℝ 1) x₀ = 0 := by
  refine ⟨fun he ↦ periodHom_eq_zero_of_mem_exactForms he x₀, fun h ↦ ?_⟩
  rw [mem_exactForms_one_iff_forall_pathIntegral_eq_zero hφ x₀]
  intro c hc hc₀ hc₁
  -- a smooth loop at `x₀` defines an element of the fundamental group
  let γ : Path x₀ x₀ := ⟨⟨fun t ↦ c t, hc.continuous.comp continuous_subtype_val⟩, hc₀, hc₁⟩
  rw [← periodHom_ofMul_eq_pathIntegral (φ.isSmoothForm.of_le (by simp))
    ((mem_closedForms I φ).mp hφ) (hc.of_le (by simp)) (γ := γ) fun _ ↦ rfl, h,
    AddMonoidHom.zero_apply]

namespace deRhamCohomology

/-- The periods of closed smooth real `1`-forms, as a linear map. -/
private def periodClosedForms (x : M) :
    closedForms I M 1 →ₗ[ℝ] Additive (FundamentalGroup M x) →+ ℝ where
  toFun φ := periodHom (φ.1 : RoughForm I M ℝ 1) x
  map_add' φ ψ :=
    periodHom_add (φ.1.isSmoothForm.of_le (by simp)) ((mem_closedForms I _).mp φ.2)
      (ψ.1.isSmoothForm.of_le (by simp)) ((mem_closedForms I _).mp ψ.2) x
  map_smul' a φ := periodHom_smul a x

/-- Exact forms have vanishing periods. -/
private theorem ker_mk_le_ker_periodClosedForms (x : M) :
    LinearMap.ker (mk I (M := M) 1) ≤ LinearMap.ker (periodClosedForms (I := I) x) := by
  intro φ hφ
  rw [LinearMap.mem_ker, mk_eq_zero_iff] at hφ
  exact periodHom_eq_zero_of_mem_exactForms hφ x

/-- The **periods of a de Rham class** in degree one: the period homomorphism of any closed form
representing it, as a linear map from `H¹_dR(M)` to the homomorphisms from the fundamental group
at `x` to `ℝ`. -/
def period (x : M) : deRhamCohomology I M 1 →ₗ[ℝ] Additive (FundamentalGroup M x) →+ ℝ :=
  LinearMap.liftOfSurjective (R := ℝ) (M := closedForms I M 1)
    (M₂ := deRhamCohomology I M 1) (M₃ := Additive (FundamentalGroup M x) →+ ℝ)
    (f := mk I (M := M) 1) (mk_surjective I 1)
    ⟨periodClosedForms x, ker_mk_le_ker_periodClosedForms x⟩

/-- The periods of the class of a closed form are the periods of the form. -/
@[simp]
theorem period_mk (x : M) (φ : closedForms I M 1) :
    period x (mk I 1 φ) = periodHom (φ.1 : RoughForm I M ℝ 1) x :=
  LinearMap.equivOfSurjective_apply _ _

/-- **De Rham classes of degree one are determined by their periods** on a connected manifold. -/
theorem period_injective [PreconnectedSpace M] (x : M) :
    Function.Injective (period (I := I) (M := M) x) := by
  refine (injective_iff_map_eq_zero _).mpr fun c hc ↦ ?_
  obtain ⟨φ, rfl⟩ := mk_surjective I 1 c
  rw [period_mk] at hc
  rw [mk_eq_zero_iff, mem_exactForms_one_iff_periodHom_eq_zero φ.2 x]
  exact hc

end deRhamCohomology

end TauCeti
