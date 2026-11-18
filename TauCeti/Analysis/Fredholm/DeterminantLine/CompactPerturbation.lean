/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.CompactPerturbation
public import TauCeti.Analysis.Fredholm.DeterminantLine.Complex
public import TauCeti.Analysis.Fredholm.DeterminantLine.Homotopy

/-!
# Canonical orientations of compact perturbations of complex-linear Fredholm operators

The linearized operator of a pseudoholomorphic sphere, of a component of a nodal curve, or of the
normal directions at a node is a real Cauchy–Riemann operator: a complex-linear operator plus a
term of order zero, which is compact between the relevant Sobolev spaces. Its determinant line
`det (ker T) ⊗ (det (F ⧸ range T))^*` is oriented by deforming the operator to its complex-linear
part, whose determinant line carries the complex orientation
(`LinearMap.IsComplexPositiveDetLine`), and transporting that orientation back along the
deformation (`TauCeti.detLineOrientationTransport`). This file constructs this canonical
orientation and proves that it does not depend on the choices made.

* **Complex orientations are continuous.** Along a continuous family of complex-linear Fredholm
  operators over any parameter space, every family of complex positive elements of the determinant
  lines is coherent (`TauCeti.isDetLineCoherentOn_of_isComplexPositiveDetLine`), that is, a
  continuous orientation of the determinant line bundle. Hence orientation transport along a path
  of complex-linear Fredholm operators carries complex orientations to complex orientations
  (`TauCeti.detLineOrientationTransport_complexDetLineOrientation`). The proof reads the family in
  one complex kernel chart near each parameter, where complex positive elements are read as complex
  positive elements of a fixed line
  (`ContinuousLinearMap.isComplexPositiveTMulDual_detLineChartEquiv_iff`), and these differ by
  positive factors. Coherence may be checked in any kernel chart, not only in
  one stabilized by a subspace of the target
  (`TauCeti.isDetLineCoherentWithinAt_iff_eventually_sameRay`).
* **The canonical orientation.** For a complex-linear Fredholm operator `A` and a compact
  real-linear `K`, the operators `A + t K`, `0 ≤ t ≤ 1`, are Fredholm. The canonical orientation
  of the determinant line of `A + K`
  (`ContinuousLinearMap.IsFredholm.canonicalDetLineOrientation`) is the complex orientation of
  `A` (`ContinuousLinearMap.IsFredholm.complexDetLineOrientation`) transported along this path. For
  `K = 0` it is the complex orientation of `A`
  (`ContinuousLinearMap.IsFredholm.canonicalDetLineOrientation_zero`).
* **Families.** Along a path `x ↦ A x + K x` of such operators, with `A` and `K` continuous,
  orientation transport carries the canonical orientation at one end to the canonical orientation
  at the other (`TauCeti.detLineOrientationTransport_canonicalDetLineOrientation`). The proof
  transports around the rectangle `(x, t) ↦ A x + t K x`: its bottom edge is a path of
  complex-linear operators, along which complex orientations are transported to complex
  orientations, and transport around a rectangle commutes
  (`TauCeti.detLineOrientationTransport_comm`).
* **Independence of the splitting.** An operator may be written as a complex-linear Fredholm
  operator plus a compact operator in many ways. All of them give the same canonical orientation
  (`ContinuousLinearMap.IsFredholm.canonicalDetLineOrientation_congr`): two splittings
  `A + K = A' + K'` are joined by the path of splittings `A + s (A' - A)`, `K + s (K' - K)`, along
  which the operator itself is constant.

## Main definitions

* `ContinuousLinearMap.IsFredholm.complexDetLineOrientation`: the complex orientation of the
  determinant line of a complex-linear Fredholm operator.
* `ContinuousLinearMap.IsFredholm.canonicalDetLineOrientation`: the canonical orientation of the
  determinant line of a complex-linear Fredholm operator plus a compact operator.

## Main results

* `TauCeti.isDetLineCoherentWithinAt_iff_eventually_sameRay`: coherence in an arbitrary kernel
  chart.
* `TauCeti.isDetLineCoherentOn_of_isComplexPositiveDetLine`: complex orientations of a continuous
  family of complex-linear Fredholm operators are coherent.
* `TauCeti.detLineOrientationTransport_complexDetLineOrientation`: transport along complex-linear
  paths preserves complex orientations.
* `TauCeti.detLineOrientationTransport_canonicalDetLineOrientation`: transport along paths of
  compact perturbations preserves canonical orientations.
* `ContinuousLinearMap.IsFredholm.canonicalDetLineOrientation_congr`: the canonical orientation does
  not depend on the splitting into a complex-linear and a compact part.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 3.1 (the orientation of the moduli space of
  simple spheres through the complex-linear part of real Cauchy–Riemann operators) and
  Appendix A.2 (determinant line bundles).
-/

public section

noncomputable section

open Filter Set Topology ContinuousLinearMap Module

namespace TauCeti

section Real

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [TopologicalSpace X]
  {T : X → E →L[ℝ] F} {v : ∀ x, (T x : E →ₗ[ℝ] F).detLine} {s : Set X} {x₀ : X}

/-- **Coherence in an arbitrary kernel chart.** For a family continuous within `s` at `x₀` with
`T x₀` Fredholm, and any kernel chart `(D₂, q)` valid at `x₀`, a family of elements of the
determinant lines is coherent within `s` at `x₀` exactly when it is nonzero at `x₀` and the chart
reads it, for `x ∈ s` near `x₀`, as nonnegative multiples of its reading at `x₀`. The chart may be
stabilized by any finite-dimensional space, for instance by a complex subspace of the target
regarded as a real one. -/
theorem isDetLineCoherentWithinAt_iff_eventually_sameRay (hT : ContinuousWithinAt T s x₀)
    (hF : IsFredholm (T x₀)) {Λ G : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]
    [FiniteDimensional ℝ Λ] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {D₂ : Λ →L[ℝ] F} {q : E × Λ →L[ℝ] G} (h₀ : (((T x₀).coprod D₂).prod q).IsInvertible) :
    IsDetLineCoherentWithinAt T v s x₀ ↔ v x₀ ≠ 0 ∧
      ∀ᶠ x in 𝓝[s] x₀, ∃ h : (((T x).coprod D₂).prod q).IsInvertible,
        SameRay ℝ (detLineChartEquiv (T x) D₂ q h (v x))
          (detLineChartEquiv (T x₀) D₂ q h₀ (v x₀)) := by
  refine ⟨fun hv ↦ ⟨hv.ne_zero, hv.eventually_sameRay hT h₀⟩, fun ⟨hv0, hev⟩ ↦ ?_⟩
  obtain ⟨S, hS, G₁, hG₁, q₁, U, -, hxU, hinv⟩ := hF.exists_isOpen_kernelChart
  refine isDetLineCoherentWithinAt_iff.2 ⟨hv0, S, hS, G₁, hG₁, q₁, hinv _ hxU, ?_⟩
  filter_upwards [hev, hT.tendsto.eventually
      (eventually_detLineChartEquiv_symm_eq_smul (hinv _ hxU) h₀)] with x hx hcx
  obtain ⟨h, hsr⟩ := hx
  obtain ⟨h₁, _, c, hc, hcu⟩ := hcx
  refine ⟨h₁, ?_⟩
  -- Map the readings in the given chart to the kernel chart by the transition at `x₀`; at `x`
  -- the transition is `c` times that one.
  have := (hsr.map ((detLineChartEquiv (T x₀) D₂ q h₀).symm.trans
    (detLineChartEquiv (T x₀) S.subtypeL q₁ (hinv _ hxU))).toLinearMap).pos_smul_left hc
  simpa only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, ← hcu]
    using this

end Real

section Complex

section Chart

variable {E Λ F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup Λ]
  [NormedSpace ℂ Λ] [FiniteDimensional ℂ Λ] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G] {D₂ : Λ →L[ℂ] F}
  {q : E × Λ →L[ℂ] G} {T T' : E →L[ℂ] F}

/-- A complex kernel chart reads complex positive elements of the determinant lines of two
complex-linear operators as positive multiples of each other. -/
private theorem sameRay_detLineChartEquiv_of_isComplexPositiveDetLine
    (h : (((T.restrictScalars ℝ).coprod (D₂.restrictScalars ℝ)).prod
      (q.restrictScalars ℝ)).IsInvertible)
    (h' : (((T'.restrictScalars ℝ).coprod (D₂.restrictScalars ℝ)).prod
      (q.restrictScalars ℝ)).IsInvertible)
    {z : (T.restrictScalars ℝ : E →ₗ[ℝ] F).detLine}
    {z' : (T'.restrictScalars ℝ : E →ₗ[ℝ] F).detLine}
    (hz : (T : E →ₗ[ℂ] F).IsComplexPositiveDetLine z)
    (hz' : (T' : E →ₗ[ℂ] F).IsComplexPositiveDetLine z') :
    SameRay ℝ (detLineChartEquiv (T'.restrictScalars ℝ) _ _ h' z')
      (detLineChartEquiv (T.restrictScalars ℝ) _ _ h z) := by
  obtain ⟨c, hc, hcz⟩ :=
    ((isComplexPositiveTMulDual_detLineChartEquiv_iff h).2 hz).exists_pos_smul_eq
      ((isComplexPositiveTMulDual_detLineChartEquiv_iff h').2 hz')
  rw [hcz]
  exact SameRay.sameRay_pos_smul_left _ hc

end Chart

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [TopologicalSpace X]
  {T : X → E →L[ℂ] F} {s : Set X}

/-- **Complex orientations are coherent.** Along a family of complex-linear operators which is
continuous and Fredholm on `s`, a family of complex positive elements of the determinant lines of
the underlying real operators is coherent on `s`: the complex orientations form a continuous
orientation of the determinant line bundle over `s`. -/
theorem isDetLineCoherentOn_of_isComplexPositiveDetLine (hT : ContinuousOn T s)
    (hF : ∀ x ∈ s, IsFredholm (T x)) {v : ∀ x, ((T x).restrictScalars ℝ : E →ₗ[ℝ] F).detLine}
    (hv : ∀ x ∈ s, (T x : E →ₗ[ℂ] F).IsComplexPositiveDetLine (v x)) :
    IsDetLineCoherentOn (fun x ↦ (T x).restrictScalars ℝ) v s := by
  refine isDetLineCoherentOn_iff.2 fun x₀ hx₀ ↦ ?_
  obtain ⟨S, hS, G, hG, q, U, hU, hxU, hinv⟩ := (hF x₀ hx₀).exists_isOpen_kernelChart
  -- A complex kernel chart of `T x₀`, valid on `U`, is a kernel chart of the real operators.
  have hinvℝ (x : X) (hx : T x ∈ U) : ((((T x).restrictScalars ℝ).coprod
      (S.subtypeL.restrictScalars ℝ)).prod (q.restrictScalars ℝ)).IsInvertible :=
    (hinv _ hx).restrictScalars
  have hTℝ : ContinuousWithinAt (fun x ↦ (T x).restrictScalars ℝ) s x₀ :=
    (restrictScalarsIsometry ℂ E F ℝ ℝ).continuous.continuousAt.comp_continuousWithinAt
      (hT x₀ hx₀)
  have := (hF x₀ hx₀).finite_coker
  refine (isDetLineCoherentWithinAt_iff_eventually_sameRay hTℝ ((hF x₀ hx₀).restrictScalars ℝ)
    (hinvℝ x₀ hxU)).2 ⟨(hv x₀ hx₀).ne_zero, ?_⟩
  filter_upwards [(hT x₀ hx₀).tendsto.eventually (hU.mem_nhds hxU), self_mem_nhdsWithin]
    with x hxU' hx
  exact ⟨hinvℝ x hxU', sameRay_detLineChartEquiv_of_isComplexPositiveDetLine _ _ (hv x₀ hx₀)
    (hv x hx)⟩

end Complex

end TauCeti

namespace ContinuousLinearMap.IsFredholm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] {A : E →L[ℂ] F}

/-- The determinant line of a complex-linear Fredholm operator has a complex positive element. -/
theorem exists_isComplexPositiveDetLine (hA : IsFredholm A) :
    ∃ z : (A.restrictScalars ℝ : E →ₗ[ℝ] F).detLine,
      (A : E →ₗ[ℂ] F).IsComplexPositiveDetLine z ∧ z ≠ 0 := by
  have := hA.finite_ker
  have := hA.finite_coker
  obtain ⟨z, hz⟩ := (A : E →ₗ[ℂ] F).exists_isComplexPositiveDetLine
  exact ⟨z, hz, hz.ne_zero⟩

/-- The **complex orientation** of the determinant line of the real operator underlying a
complex-linear Fredholm operator `A`: the orientation given by its complex positive elements
(`LinearMap.IsComplexPositiveDetLine`), which orient the complex kernel and cokernel of `A` by
their complex structures. -/
def complexDetLineOrientation (hA : IsFredholm A) :
    Module.Ray ℝ (A.restrictScalars ℝ : E →ₗ[ℝ] F).detLine :=
  rayOfNeZero ℝ hA.exists_isComplexPositiveDetLine.choose
    hA.exists_isComplexPositiveDetLine.choose_spec.2

/-- The complex orientation is the orientation of any complex positive element of the
determinant line. -/
theorem complexDetLineOrientation_eq (hA : IsFredholm A)
    {z : (A.restrictScalars ℝ : E →ₗ[ℝ] F).detLine}
    (hz : (A : E →ₗ[ℂ] F).IsComplexPositiveDetLine z) (hz0 : z ≠ 0) :
    hA.complexDetLineOrientation = rayOfNeZero ℝ z hz0 := by
  have := hA.finite_coker
  obtain ⟨c, hc, rfl⟩ := hA.exists_isComplexPositiveDetLine.choose_spec.1.exists_pos_smul_eq hz
  exact (ray_pos_smul _ hc _).symm

end ContinuousLinearMap.IsFredholm

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Transport preserves complex orientations.** Along a path of complex-linear operators which
is continuous and Fredholm between `a` and `b`, orientation transport of the determinant lines of
the underlying real operators carries the complex orientation at `a` to the complex orientation
at `b`. -/
theorem detLineOrientationTransport_complexDetLineOrientation {T : ℝ → E →L[ℂ] F} {a b : ℝ}
    (hT : ContinuousOn T (uIcc a b)) (hF : ∀ t ∈ uIcc a b, IsFredholm (T t)) :
    detLineOrientationTransport (T := fun t ↦ (T t).restrictScalars ℝ) a b
        ((restrictScalarsIsometry ℂ E F ℝ ℝ).continuous.comp_continuousOn hT)
        (fun t ht ↦ (hF t ht).restrictScalars ℝ)
        (hF a left_mem_uIcc).complexDetLineOrientation =
      (hF b right_mem_uIcc).complexDetLineOrientation := by
  classical
  -- A family of complex positive elements along the path.
  let v : ∀ t, ((T t).restrictScalars ℝ : E →ₗ[ℝ] F).detLine := fun t ↦
    if h : IsFredholm (T t) then h.exists_isComplexPositiveDetLine.choose else 0
  have hv (t : ℝ) (ht : t ∈ uIcc a b) :
      (T t : E →ₗ[ℂ] F).IsComplexPositiveDetLine (v t) ∧ v t ≠ 0 := by
    simp only [v, dite_eq_left (hF t ht)]
    exact (hF t ht).exists_isComplexPositiveDetLine.choose_spec
  have hcoh := isDetLineCoherentOn_of_isComplexPositiveDetLine hT hF fun t ht ↦ (hv t ht).1
  rw [(hF a left_mem_uIcc).complexDetLineOrientation_eq (hv a left_mem_uIcc).1
      (hv a left_mem_uIcc).2,
    (hF b right_mem_uIcc).complexDetLineOrientation_eq (hv b right_mem_uIcc).1
      (hv b right_mem_uIcc).2]
  exact detLineOrientationTransport_rayOfNeZero _ _ hcoh

section Congr

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Transport along two pointwise equal paths agrees, once the determinant lines of the equal
operators at the endpoints are identified. -/
private theorem detLineOrientationTransport_map_detLineCongr {T₁ T₂ : ℝ → E →L[ℝ] F}
    (h : ∀ t, T₁ t = T₂ t) {a b : ℝ} (hT₁ : ContinuousOn T₁ (uIcc a b))
    (hF₁ : ∀ t ∈ uIcc a b, IsFredholm (T₁ t)) (hT₂ : ContinuousOn T₂ (uIcc a b))
    (hF₂ : ∀ t ∈ uIcc a b, IsFredholm (T₂ t)) (o : Module.Ray ℝ (T₁ a : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport a b hT₂ hF₂ (Module.Ray.map ((T₁ a : E →ₗ[ℝ] F).detLineCongr
        (LinearEquiv.refl ℝ E) (LinearEquiv.refl ℝ F) (by rw [h a]; rfl)) o) =
      Module.Ray.map ((T₁ b : E →ₗ[ℝ] F).detLineCongr (LinearEquiv.refl ℝ E)
        (LinearEquiv.refl ℝ F) (by rw [h b]; rfl)) (detLineOrientationTransport a b hT₁ hF₁ o) := by
  obtain rfl : T₁ = T₂ := funext h
  simp only [LinearMap.detLineCongr_refl, Module.Ray.map_refl, Equiv.refl_apply]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Identifying the determinant lines of equal operators twice is identifying them once. -/
private theorem map_detLineCongr_map_detLineCongr {S₁ S₂ S₃ : E →L[ℝ] F} (h₁₂ : S₁ = S₂)
    (h₂₃ : S₂ = S₃) (o : Module.Ray ℝ (S₁ : E →ₗ[ℝ] F).detLine) :
    Module.Ray.map ((S₂ : E →ₗ[ℝ] F).detLineCongr (LinearEquiv.refl ℝ E) (LinearEquiv.refl ℝ F)
        (by rw [h₂₃]; rfl))
      (Module.Ray.map ((S₁ : E →ₗ[ℝ] F).detLineCongr (LinearEquiv.refl ℝ E)
        (LinearEquiv.refl ℝ F) (by rw [h₁₂]; rfl)) o) =
      Module.Ray.map ((S₁ : E →ₗ[ℝ] F).detLineCongr (LinearEquiv.refl ℝ E)
        (LinearEquiv.refl ℝ F) (by rw [← h₂₃, ← h₁₂]; rfl)) o := by
  subst h₁₂ h₂₃
  simp only [LinearMap.detLineCongr_refl, Module.Ray.map_refl, Equiv.refl_apply]

end Congr

section Perturbation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The operators `A + t K` on the segment from a complex-linear Fredholm operator `A` to a
compact perturbation `A + K` are Fredholm. -/
private theorem isFredholm_restrictScalars_add_smul {A : E →L[ℂ] F} (hA : IsFredholm A)
    {K : E →L[ℝ] F} (hK : IsCompactOperator K) (t : ℝ) :
    IsFredholm (A.restrictScalars ℝ + t • K) :=
  (hA.restrictScalars ℝ).add_of_isCompactOperator (by simpa using hK.smul t)

end Perturbation

end TauCeti

namespace ContinuousLinearMap.IsFredholm

open TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {A : E →L[ℂ] F} {K : E →L[ℝ] F}

/-- The **canonical orientation** of the determinant line of `A + K`, for a complex-linear
Fredholm operator `A` and a compact real-linear operator `K`: the complex orientation of `A`
(`ContinuousLinearMap.IsFredholm.complexDetLineOrientation`) transported along the path of
Fredholm operators `A + t K`, `0 ≤ t ≤ 1` (`TauCeti.detLineOrientationTransport`). It depends only
on the operator `A + K`, not on its splitting
(`ContinuousLinearMap.IsFredholm.canonicalDetLineOrientation_congr`). -/
def canonicalDetLineOrientation (hA : IsFredholm A) (hK : IsCompactOperator K) :
    Module.Ray ℝ ((A.restrictScalars ℝ + K : E →L[ℝ] F) : E →ₗ[ℝ] F).detLine :=
  Module.Ray.map (((A.restrictScalars ℝ + (1 : ℝ) • K : E →L[ℝ] F) : E →ₗ[ℝ] F).detLineCongr
      (LinearEquiv.refl ℝ E) (LinearEquiv.refl ℝ F) (by rw [one_smul]; rfl))
    (detLineOrientationTransport (T := fun t : ℝ ↦ A.restrictScalars ℝ + t • K) 0 1
      (Continuous.continuousOn (by fun_prop))
      (fun t _ ↦ (hA.restrictScalars ℝ).add_of_isCompactOperator (by simpa using hK.smul t))
      (Module.Ray.map ((A.restrictScalars ℝ : E →ₗ[ℝ] F).detLineCongr (LinearEquiv.refl ℝ E)
        (LinearEquiv.refl ℝ F) (by rw [zero_smul, add_zero]; rfl)) hA.complexDetLineOrientation))

/-- The defining formula of `ContinuousLinearMap.IsFredholm.canonicalDetLineOrientation`: the
complex orientation of `A`, carried to the determinant line of `A + 0 K`, transported along
`t ↦ A + t K` from `0` to `1`, and carried from `A + 1 K` to `A + K`. -/
theorem canonicalDetLineOrientation_def (hA : IsFredholm A) (hK : IsCompactOperator K) :
    hA.canonicalDetLineOrientation hK =
      Module.Ray.map (((A.restrictScalars ℝ + (1 : ℝ) • K : E →L[ℝ] F) : E →ₗ[ℝ] F).detLineCongr
          (LinearEquiv.refl ℝ E) (LinearEquiv.refl ℝ F) (by rw [one_smul]; rfl))
        (detLineOrientationTransport (T := fun t : ℝ ↦ A.restrictScalars ℝ + t • K) 0 1
          (Continuous.continuousOn (by fun_prop))
          (fun t _ ↦ (hA.restrictScalars ℝ).add_of_isCompactOperator (by simpa using hK.smul t))
          (Module.Ray.map ((A.restrictScalars ℝ : E →ₗ[ℝ] F).detLineCongr (LinearEquiv.refl ℝ E)
            (LinearEquiv.refl ℝ F) (by rw [zero_smul, add_zero]; rfl))
            hA.complexDetLineOrientation)) := by
  rw [canonicalDetLineOrientation]

end ContinuousLinearMap.IsFredholm

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The canonical orientation of `A + K` is the complex orientation of `A` transported along any
path `P` which is pointwise equal to the segment `t ↦ A + t K`. -/
private theorem canonicalDetLineOrientation_eq_map {A : E →L[ℂ] F} {K : E →L[ℝ] F}
    (hA : IsFredholm A) (hK : IsCompactOperator K) {P : ℝ → E →L[ℝ] F}
    (hP : ∀ t, P t = A.restrictScalars ℝ + t • K) (hPc : ContinuousOn P (uIcc 0 1))
    (hPF : ∀ t ∈ uIcc (0 : ℝ) 1, IsFredholm (P t)) :
    hA.canonicalDetLineOrientation hK =
      Module.Ray.map ((P 1 : E →ₗ[ℝ] F).detLineCongr (LinearEquiv.refl ℝ E)
          (LinearEquiv.refl ℝ F) (by rw [hP, one_smul]; rfl))
        (detLineOrientationTransport 0 1 hPc hPF
          (Module.Ray.map ((A.restrictScalars ℝ : E →ₗ[ℝ] F).detLineCongr (LinearEquiv.refl ℝ E)
            (LinearEquiv.refl ℝ F) (by rw [hP, zero_smul, add_zero]; rfl))
            hA.complexDetLineOrientation)) := by
  have h0 : A.restrictScalars ℝ = A.restrictScalars ℝ + (0 : ℝ) • K := by rw [zero_smul, add_zero]
  have h0' : A.restrictScalars ℝ + (0 : ℝ) • K = P 0 := (hP 0).symm
  have h1 : A.restrictScalars ℝ + (1 : ℝ) • K = P 1 := (hP 1).symm
  have h1' : P 1 = A.restrictScalars ℝ + K := by rw [hP, one_smul]
  have hseg := detLineOrientationTransport_map_detLineCongr
    (T₁ := fun t : ℝ ↦ A.restrictScalars ℝ + t • K) (fun t ↦ (hP t).symm)
    (Continuous.continuousOn (by fun_prop)) (fun t _ ↦ isFredholm_restrictScalars_add_smul hA hK t)
    hPc hPF
  -- The proof is a chain of equalities rather than a rewrite, since rewriting would compare `P`
  -- with the operators of the segment at every subterm.
  exact (IsFredholm.canonicalDetLineOrientation_def _ _).trans
    ((map_detLineCongr_map_detLineCongr h1 h1' _).symm.trans (congrArg _
      ((hseg _).symm.trans (congrArg _ (map_detLineCongr_map_detLineCongr h0 h0' _)))))

/-- **Transport preserves canonical orientations.** Let `A` be a path of complex-linear Fredholm
operators and `K` a path of compact real-linear operators, both continuous between `a` and `b`.
Orientation transport along the path `A + K` carries the canonical orientation of `A a + K a` to
the canonical orientation of `A b + K b`. -/
theorem detLineOrientationTransport_canonicalDetLineOrientation {A : ℝ → E →L[ℂ] F}
    {K : ℝ → E →L[ℝ] F} {a b : ℝ} (hA : ContinuousOn A (uIcc a b))
    (hK : ContinuousOn K (uIcc a b)) (hAF : ∀ x ∈ uIcc a b, IsFredholm (A x))
    (hKc : ∀ x ∈ uIcc a b, IsCompactOperator (K x)) :
    detLineOrientationTransport (T := fun x ↦ (A x).restrictScalars ℝ + K x) a b
        (((restrictScalarsIsometry ℂ E F ℝ ℝ).continuous.comp_continuousOn hA).add hK)
        (fun x hx ↦ ((hAF x hx).restrictScalars ℝ).add_of_isCompactOperator (hKc x hx))
        ((hAF a left_mem_uIcc).canonicalDetLineOrientation (hKc a left_mem_uIcc)) =
      (hAF b right_mem_uIcc).canonicalDetLineOrientation (hKc b right_mem_uIcc) := by
  -- Transport around the rectangle `H (x, t) = A x + t K x`, `x ∈ [[a, b]]`, `t ∈ [0, 1]`. Its
  -- vertical edges define the canonical orientations, its bottom edge is complex-linear, and its
  -- top edge is the path `A + K`. `H` is kept opaque, and its edges are compared with these paths
  -- through pointwise equalities.
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ × ℝ → E →L[ℝ] F,
      H = fun p ↦ (A p.1).restrictScalars ℝ + p.2 • K p.1 := ⟨_, rfl⟩
  have hHapp (x t : ℝ) : H (x, t) = (A x).restrictScalars ℝ + t • K x := by rw [hHdef]
  have hAℝ := (restrictScalarsIsometry ℂ E F ℝ ℝ).continuous.comp_continuousOn hA
  have hfst : MapsTo Prod.fst (uIcc a b ×ˢ uIcc (0 : ℝ) 1) (uIcc a b) := fun _ hp ↦ hp.1
  have hH : ContinuousOn H (uIcc a b ×ˢ uIcc 0 1) := by
    rw [hHdef]
    exact (hAℝ.comp continuousOn_fst hfst).add
      (continuousOn_snd.smul (hK.comp continuousOn_fst hfst))
  have hHF (p : ℝ × ℝ) (hp : p ∈ uIcc a b ×ˢ uIcc 0 1) : IsFredholm (H p) := by
    rw [hHdef]
    exact isFredholm_restrictScalars_add_smul (hAF p.1 hp.1) (hKc p.1 hp.1) p.2
  have hvert (x : ℝ) (hx : x ∈ uIcc a b) :=
    canonicalDetLineOrientation_eq_map (hAF x hx) (hKc x hx) (P := fun t ↦ H (x, t)) (hHapp x)
      (hH.comp (Continuous.prodMk_right x).continuousOn fun _ ht ↦ ⟨hx, ht⟩)
      (fun t ht ↦ hHF _ ⟨hx, ht⟩)
  have hhor (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) : ContinuousOn (fun x ↦ H (x, t)) (uIcc a b) :=
    hH.comp (Continuous.prodMk_left t).continuousOn fun _ hx ↦ ⟨hx, ht⟩
  have hbot := detLineOrientationTransport_map_detLineCongr
    (T₁ := fun x ↦ (A x).restrictScalars ℝ) (T₂ := fun x ↦ H (x, 0))
    (fun x ↦ by rw [hHapp, zero_smul, add_zero]) hAℝ (fun x hx ↦ (hAF x hx).restrictScalars ℝ)
    (hhor 0 left_mem_uIcc) (fun x hx ↦ hHF _ ⟨hx, left_mem_uIcc⟩)
    (hAF a left_mem_uIcc).complexDetLineOrientation
  rw [detLineOrientationTransport_complexDetLineOrientation hA hAF] at hbot
  have htop := detLineOrientationTransport_map_detLineCongr
    (T₁ := fun x ↦ H (x, 1)) (T₂ := fun x ↦ (A x).restrictScalars ℝ + K x)
    (fun x ↦ by rw [hHapp, one_smul]) (hhor 1 right_mem_uIcc)
    (fun x hx ↦ hHF _ ⟨hx, right_mem_uIcc⟩) (hAℝ.add hK)
    (fun x hx ↦ ((hAF x hx).restrictScalars ℝ).add_of_isCompactOperator (hKc x hx))
  exact (congrArg _ (hvert a left_mem_uIcc)).trans ((htop _).trans
    ((congrArg _ (detLineOrientationTransport_comm hH hHF _)).trans
      ((congrArg _ (congrArg _ hbot)).trans (hvert b right_mem_uIcc).symm)))

/-- Equal splittings give the same canonical orientation, once the determinant lines of the equal
operators are identified. -/
private theorem map_detLineCongr_canonicalDetLineOrientation {A₁ A₂ : E →L[ℂ] F}
    {K₁ K₂ : E →L[ℝ] F} (hA₁ : IsFredholm A₁) (hK₁ : IsCompactOperator K₁) (hA₂ : IsFredholm A₂)
    (hK₂ : IsCompactOperator K₂) (hA : A₁ = A₂) (hK : K₁ = K₂) :
    Module.Ray.map (((A₁.restrictScalars ℝ + K₁ : E →L[ℝ] F) : E →ₗ[ℝ] F).detLineCongr
        (LinearEquiv.refl ℝ E) (LinearEquiv.refl ℝ F) (by rw [hA, hK]; rfl))
        (hA₁.canonicalDetLineOrientation hK₁) =
      hA₂.canonicalDetLineOrientation hK₂ := by
  subst hA hK
  simp only [LinearMap.detLineCongr_refl, Module.Ray.map_refl, Equiv.refl_apply]

end TauCeti

namespace ContinuousLinearMap.IsFredholm

open TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {A : E →L[ℂ] F}

/-- The canonical orientation of a complex-linear Fredholm operator, with no compact part, is its
complex orientation. -/
theorem canonicalDetLineOrientation_zero (hA : IsFredholm A)
    (h0 : IsCompactOperator (0 : E →L[ℝ] F)) :
    hA.canonicalDetLineOrientation h0 =
      Module.Ray.map ((A.restrictScalars ℝ : E →ₗ[ℝ] F).detLineCongr (LinearEquiv.refl ℝ E)
        (LinearEquiv.refl ℝ F) (by rw [add_zero]; rfl)) hA.complexDetLineOrientation := by
  have hP (t : ℝ) : A.restrictScalars ℝ = A.restrictScalars ℝ + t • (0 : E →L[ℝ] F) := by
    rw [smul_zero, add_zero]
  have hA₀ : A.restrictScalars ℝ = A.restrictScalars ℝ := rfl
  have hA₁ : A.restrictScalars ℝ = A.restrictScalars ℝ + 0 := (add_zero _).symm
  -- Along the constant path at `A`, transport is the identity.
  exact (canonicalDetLineOrientation_eq_map hA h0 (P := fun _ ↦ A.restrictScalars ℝ) hP
      continuousOn_const (fun _ _ ↦ hA.restrictScalars ℝ)).trans
    ((congrArg _ (congrFun (detLineOrientationTransport_const (hA.restrictScalars ℝ) 0 1) _)).trans
      (map_detLineCongr_map_detLineCongr hA₀ hA₁ _))

/-- **The canonical orientation does not depend on the splitting.** If `A + K = A' + K'` for
complex-linear Fredholm operators `A`, `A'` and compact real-linear operators `K`, `K'`, the
canonical orientations of the two splittings agree, once the determinant lines of the equal
operators are identified. -/
theorem canonicalDetLineOrientation_congr {A' : E →L[ℂ] F} {K K' : E →L[ℝ] F} (hA : IsFredholm A)
    (hK : IsCompactOperator K) (hA' : IsFredholm A') (hK' : IsCompactOperator K')
    (h : A.restrictScalars ℝ + K = A'.restrictScalars ℝ + K') :
    Module.Ray.map (((A.restrictScalars ℝ + K : E →L[ℝ] F) : E →ₗ[ℝ] F).detLineCongr
        (LinearEquiv.refl ℝ E) (LinearEquiv.refl ℝ F) (by rw [h]; rfl))
        (hA.canonicalDetLineOrientation hK) =
      hA'.canonicalDetLineOrientation hK' := by
  -- The splittings `A + s (A' - A)` and `K + s (K' - K)` join the two, and their sum is constant.
  -- The paths are kept opaque, and compared with their values through pointwise equalities.
  obtain ⟨B, hB⟩ : ∃ B : ℝ → E →L[ℂ] F, B = fun s ↦ A + s • (A' - A) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ → E →L[ℝ] F, L = fun s ↦ K + s • (K' - K) := ⟨_, rfl⟩
  have hdiff : IsCompactOperator (A' - A) := by
    have : ⇑(A' - A) = ⇑(K - K') := by
      ext v
      have hv := congrArg (fun T : E →L[ℝ] F ↦ T v) h
      simp only [add_apply, coe_restrictScalars', sub_apply] at hv ⊢
      linear_combination (norm := module) (-1 : ℝ) • hv
    rw [this]
    simpa using hK.sub hK'
  have hBF (s : ℝ) : IsFredholm (B s) := by
    rw [hB]
    exact hA.add_of_isCompactOperator (by simpa using hdiff.smul s)
  have hLc (s : ℝ) : IsCompactOperator (L s) := by
    rw [hL]
    simpa using hK.add ((hK'.sub hK).smul s)
  have hT (s : ℝ) : (B s).restrictScalars ℝ + L s = A.restrictScalars ℝ + K := by
    rw [hB, hL]
    ext v
    have hv := congrArg (fun T : E →L[ℝ] F ↦ T v) h
    simp only [add_apply, coe_restrictScalars', smul_apply, sub_apply] at hv ⊢
    linear_combination (norm := module) (-s) • hv
  have hBc : Continuous B := by rw [hB]; fun_prop
  have hLc' : Continuous L := by rw [hL]; fun_prop
  have hfam := detLineOrientationTransport_canonicalDetLineOrientation (a := 0) (b := 1)
    hBc.continuousOn hLc'.continuousOn (fun s _ ↦ hBF s) (fun s _ ↦ hLc s)
  -- Along the constant path `B + L`, transport is the identification of equal operators.
  have hconst := detLineOrientationTransport_eq_map_of_forall_eq
    (T := fun s ↦ (B s).restrictScalars ℝ + L s) (a := 0) (b := 1)
    (((restrictScalarsIsometry ℂ E F ℝ ℝ).continuous.comp_continuousOn hBc.continuousOn).add
      hLc'.continuousOn)
    (fun s _ ↦ ((hBF s).restrictScalars ℝ).add_of_isCompactOperator (hLc s))
    (fun s _ ↦ (hT s).trans (hT 0).symm)
  have h₀ : A.restrictScalars ℝ + K = (B 0).restrictScalars ℝ + L 0 := (hT 0).symm
  have h₀₁ : (B 0).restrictScalars ℝ + L 0 = (B 1).restrictScalars ℝ + L 1 :=
    (hT 0).trans (hT 1).symm
  have h₁ : (B 1).restrictScalars ℝ + L 1 = A'.restrictScalars ℝ + K' := (hT 1).trans h
  have hB₀ : A = B 0 := by simp [hB]
  have hL₀ : K = L 0 := by simp [hL]
  have hB₁ : B 1 = A' := by simp [hB]
  have hL₁ : L 1 = K' := by simp [hL]
  exact (map_detLineCongr_map_detLineCongr (h₀.trans h₀₁) h₁ _).symm.trans
    ((congrArg _ (map_detLineCongr_map_detLineCongr h₀ h₀₁ _).symm).trans
      ((congrArg _ (congrArg _ (map_detLineCongr_canonicalDetLineOrientation hA hK (hBF 0) (hLc 0)
        hB₀ hL₀))).trans ((congrArg _ ((hconst _).symm.trans hfam)).trans
          (map_detLineCongr_canonicalDetLineOrientation (hBF 1) (hLc 1) hA' hK' hB₁ hL₁))))

end ContinuousLinearMap.IsFredholm
