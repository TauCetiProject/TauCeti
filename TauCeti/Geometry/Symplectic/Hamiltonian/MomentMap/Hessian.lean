/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField.Linearization
public import TauCeti.Geometry.Symplectic.Hamiltonian.ConstantOrbit.Manifold
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Critical

/-!
# Hessians of moment map components

Let `μ : M → 𝔤*` be a moment map of an infinitesimal action `Z ↦ Z_M` for a closed two-form `σ`.
At a critical point `x` of a component `μ^X = ⟨μ, X⟩`, differentiating
`dμ^X(Y_M) = σ(X_M, Y_M)`, which differs from `μ^⁅X, Y⁆` by a locally constant function, gives the
Hessian of `μ^X` against a generator:

`Hess μ^X (x) (v, Y_M x) = σ_x(⁅X, Y⁆_M x, v)`

(`TauCeti.SmoothTwoForm.IsMomentMap.criticalHessian_apply_eq_eval₂_lie`). Where `μ` is moreover
infinitesimally equivariant, `σ(Z_M, Y_M) = μ ⁅Z, Y⁆`, this reads
`Hess μ^X (x) (Z_M x, Y_M x) = μ(x)(⁅⁅X, Y⁆, Z⁆)`
(`TauCeti.SmoothTwoForm.IsMomentMap.criticalHessian_apply_apply_eq_lie_lie`); on a coadjoint orbit,
where the generators span every tangent space, this determines the Hessian.

For the rest of the file, let a Lie group `G` act smoothly on a manifold `M` with a nondegenerate
two-form `σ`, with moment map `μ : M → 𝔤*`, so that the component `μ^ξ = ⟨μ, ξ⟩` has
Hamiltonian vector field the fundamental vector field `ξ_M`. The critical points of `μ^ξ` are the
zeros of `ξ_M`, the points fixed by the closure `T_ξ` of `{exp (t ξ) | t ∈ ℝ}`
(`TauCeti.SmoothTwoForm.IsMomentMap.criticalPoints_eq_fixedPoints`). This file computes the
Hessian of `μ^ξ` at such a point `p` from the isotropy representation of `T_ξ` on `T_p M`.

Every `exp (t ξ)` fixes `p`, so its differential `d(exp (t ξ))_p` is an operator on `T_p M`; let
`A_ξ` be the derivative of `t ↦ d(exp (t ξ))_p` at `t = 0`, the infinitesimal isotropy action
of `ξ` at `p`. At a zero of a Hamiltonian vector field the Hessian of the Hamiltonian is `σ_p`
applied to the linearization of the field, and the linearization of `ξ_M` at `p` is `A_ξ`
(`TauCeti.hasDerivAt_mfderiv_mulInvariantExp_smul_smul`). Hence

`Hess μ^ξ (p) (v, w) = σ_p(A_ξ v, w)`

(`TauCeti.SmoothTwoForm.IsMomentMap.criticalHessian_apply_eq_eval₂_deriv`). So the Hessian
quadratic form `v ↦ σ_p(A_ξ v, v)` is twice the quadratic Hamiltonian of the linear isotropy
action of `ξ` on `(T_p M, σ_p)`; in particular it depends only on the isotropy representation of
the one-parameter subgroup on `T_p M`.

Since `σ_p` is nondegenerate, the null space of the Hessian is the kernel of `A_ξ`, which consists
of the tangent vectors fixed by the differential at `p` of every element of `T_ξ`
(`TauCeti.SmoothTwoForm.IsMomentMap.criticalHessian_apply_eq_zero_iff`): the null space is the
fixed space `(T_p M)^{T_ξ}` of the isotropy representation. That this fixed space is the tangent
space at `p` of the critical set `M^{T_ξ}`, the Morse–Bott property, is not proved here. In
particular `p` is a nondegenerate critical point of `μ^ξ` exactly when no nonzero tangent vector
at `p` is fixed by `T_ξ`
(`TauCeti.SmoothTwoForm.IsMomentMap.isManifoldNondegenerateCriticalPoint_iff`).

When `T_ξ` is the whole group, for instance for a generic `ξ` in the Lie algebra of a torus, the
critical points of `μ^ξ` are the fixed points of `G`. So `μ^ξ` is a Morse function exactly when
at each fixed point the isotropy representation has no nonzero invariant vector
(`TauCeti.SmoothTwoForm.IsMomentMap.isMorse_iff_of_eq_top`). For a
compact connected abelian group acting with this property at every fixed point, the `ξ` for which
`μ^ξ` is a Morse function are therefore dense in the Lie algebra
(`TauCeti.SmoothTwoForm.IsMomentMap.dense_setOf_isMorse`).

For these fixed-point results neither closedness of `σ`, equivariance of `μ` nor compactness of
`M` is used.

## Main results

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsMomentMap`.

* `criticalHessian_apply_eq_eval₂_lie`: for a closed form, at a critical point of `μ^X`, the
  Hessian of `μ^X` against `Y_M x` is `σ_x(⁅X, Y⁆_M x, ·)`.
* `criticalHessian_apply_apply_eq_lie_lie`: where moreover the cocycle of `μ` vanishes, the
  Hessian on generators is `μ(x)(⁅⁅X, Y⁆, Z⁆)`.
* `criticalHessian_apply_eq_eval₂_deriv`: at a zero `p` of `ξ_M`, the Hessian of `μ^ξ` is
  `σ_p(A_ξ v, w)`.
* `criticalHessian_apply_eq_zero_iff`: its null space consists of the vectors fixed by the
  differential at `p` of every element of `T_ξ`.
* `isManifoldNondegenerateCriticalPoint_iff`: `p` is a nondegenerate critical point of `μ^ξ`
  exactly when `T_ξ` fixes no nonzero tangent vector at `p`.
* `isMorse_iff_of_eq_top`: if `T_ξ = G`, then `μ^ξ` is a Morse
  function exactly when at every fixed point of `G` no nonzero tangent vector is fixed by `G`.
* `dense_setOf_isMorse`: for a compact connected abelian group with this property at every fixed
  point, the `ξ` with `μ^ξ` Morse are dense.

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15,
  § 2 (the components of the moment map are Morse–Bott functions, with Hessian given by the
  isotropy weights).
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513, § 3.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, § 27.1 (Morse–Bott property of moment map components).
-/

public section

open Function Set
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsMomentMap

section Lie

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ : M → Module.Dual ℝ 𝔤} {X : 𝔤}
  {x : M}

/-- **The Hessian of a moment map component against a generator.** For a closed form, at a
critical point `x` of the component `μ^X`, the Hessian of `μ^X` pairs a tangent vector `v` with the
generator `Y_M x` to `σ_x(⁅X, Y⁆_M x, v)`, the derivative of `μ^⁅X, Y⁆` along `v`. Indeed
`dμ^X(Y_M) = σ(X_M, Y_M)`, which differs from `μ^⁅X, Y⁆` by a locally constant function. -/
theorem criticalHessian_apply_eq_eval₂_lie (h : σ.IsMomentMap a μ) (hσ : σ.IsClosed)
    (hx : x ∈ criticalPoints I fun y ↦ μ y X) (v : TangentSpace I x) (Y : 𝔤) :
    criticalHessian I (fun y ↦ μ y X) x v (a Y x) = SmoothBundleForm.eval₂ σ x (a ⁅X, Y⁆ x) v := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := by simp
  have : IsManifold I 2 M := IsManifold.of_le h2
  have hY : (fun y ↦ mvfderiv I (fun z ↦ μ z X) y (a Y y)) =
      fun y ↦ SmoothBundleForm.eval₂ σ y (a X y) (a Y y) :=
    funext fun y ↦ (h.eval₂_apply X y _).symm
  rw [criticalHessian_apply_eq_mvfderiv ((h.contMDiff X).of_le h2 x)
      (mem_criticalPoints.1 hx) ((a.contMDiff Y x).mdifferentiableAt (by simp)), hY,
    h.mvfderiv_eval₂ hσ, h.eval₂_apply]

/-- **The Hessian of a moment map component on generators.** For a closed form, at a critical
point `x` of the component `μ^X` at which the moment map is infinitesimally equivariant, the
Hessian of `μ^X` pairs the generators `Z_M x` and `Y_M x` to `μ(x)(⁅⁅X, Y⁆, Z⁆)`. -/
theorem criticalHessian_apply_apply_eq_lie_lie (h : σ.IsMomentMap a μ) (hσ : σ.IsClosed)
    (hx : x ∈ criticalPoints I fun y ↦ μ y X) (hc : σ.momentCocycle a μ x = 0) (Z Y : 𝔤) :
    criticalHessian I (fun y ↦ μ y X) x (a Z x) (a Y x) = μ x ⁅⁅X, Y⁆, Z⁆ := by
  rw [h.criticalHessian_apply_eq_eval₂_lie hσ hx, momentCocycle_eq_zero_iff.1 hc]

end Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {ξ : GroupLieAlgebra I G} {p : M}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

omit [T2Space G] [IsTopologicalGroup G] [I'.Boundaryless] [T2Space M] in
/-- A zero of the fundamental vector field `ξ_M` is a critical point of `μ^ξ`, at which the
Hamiltonian vector field of `μ^ξ` is `ξ_M`. -/
private theorem mvfderiv_eq_zero_and_hamiltonianVectorField_eq
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate)
    (hp : fundamentalVectorField I' ξ p = 0) :
    mvfderiv I' (fun y ↦ μ y ξ) p = 0 ∧
      σ.hamiltonianVectorField (fun y ↦ μ y ξ) = fundamentalVectorField I' ξ := by
  rw [h.hamiltonianVectorField_eq hσ, InfinitesimalAction.fundamental_apply,
    ← mem_criticalPoints, h.mem_criticalPoints_iff (hσ.nondegenerate_bilinFormAt p),
    InfinitesimalAction.fundamental_apply]
  exact ⟨hp, rfl⟩

omit [IsTopologicalGroup G] in
/-- **The Hessian of a moment map component at a fixed point.** Let `p` be a zero of the
fundamental vector field `ξ_M`, so that every `exp (t ξ)` fixes `p`. Then the Hessian of the
component `μ^ξ` at `p` is `σ_p(A_ξ v, w)`, where `A_ξ` is the derivative at `t = 0` of the
differentials `d(exp (t ξ))_p`, operators on `T_p M`. -/
theorem criticalHessian_apply_eq_eval₂_deriv
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate)
    (hp : fundamentalVectorField I' ξ p = 0) (v w : TangentSpace I' p) :
    criticalHessian I' (fun y ↦ μ y ξ) p v w = SmoothBundleForm.eval₂ σ p
      (deriv (F := E' →L[ℝ] E') (fun t : ℝ ↦
        mfderiv I' I' (fun y : M ↦ mulInvariantExp (t • ξ) • y) p) 0 v) w := by
  obtain ⟨hcrit, hX⟩ := h.mvfderiv_eq_zero_and_hamiltonianVectorField_eq hσ hp
  rw [hσ.criticalHessian_apply_eq_eval₂_fderiv ((h.contMDiff ξ).of_le (by simp)) hcrit, hX,
    (hasDerivAt_mfderiv_mulInvariantExp_smul_smul hp).deriv]

/-- **The null space of the Hessian of a moment map component.** At a zero `p` of the fundamental
vector field `ξ_M`, a tangent vector lies in the null space of the Hessian of `μ^ξ` exactly when it
is fixed by the differential at `p` of every element of the closure `T_ξ` of
`{exp (t ξ) | t ∈ ℝ}`. -/
theorem criticalHessian_apply_eq_zero_iff
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate)
    (hp : fundamentalVectorField I' ξ p = 0) (v : TangentSpace I' p) :
    criticalHessian I' (fun y ↦ μ y ξ) p v = 0 ↔
      ∀ g ∈ Lie.closedOneParameterSubgroup ξ, mfderiv I' I' (fun y : M ↦ g • y) p v = v := by
  obtain ⟨hcrit, hX⟩ := h.mvfderiv_eq_zero_and_hamiltonianVectorField_eq hσ hp
  rw [hσ.criticalHessian_apply_eq_zero_iff ((h.contMDiff ξ).of_le (by simp)) hcrit, hX,
    fderiv_mpullbackWithin_fundamentalVectorField_apply_eq_zero_iff hp,
    forall_mem_closedOneParameterSubgroup_mfderiv_smul_apply_eq_iff
      ((mulInvariantExp_smul_smul_eq_iff (I' := I')).2 hp)]

/-- **Nondegenerate critical points of a moment map component.** A zero `p` of the fundamental
vector field `ξ_M` is a nondegenerate critical point of `μ^ξ` exactly when no nonzero tangent
vector at `p` is fixed by the differential at `p` of every element of the closure `T_ξ` of
`{exp (t ξ) | t ∈ ℝ}`. -/
theorem isManifoldNondegenerateCriticalPoint_iff
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate)
    (hp : fundamentalVectorField I' ξ p = 0) :
    IsManifoldNondegenerateCriticalPoint I' (fun y ↦ μ y ξ) p ↔
      ∀ v : TangentSpace I' p,
        (∀ g ∈ Lie.closedOneParameterSubgroup ξ, mfderiv I' I' (fun y : M ↦ g • y) p v = v) →
          v = 0 := by
  have hF : ContMDiff I' 𝓘(ℝ) 2 fun y ↦ μ y ξ := (h.contMDiff ξ).of_le (by simp)
  have hcrit := (h.mvfderiv_eq_zero_and_hamiltonianVectorField_eq hσ hp).1
  rw [← hσ.injective_fderiv_mpullbackWithin_hamiltonianVectorField_iff hF hcrit,
    injective_iff_map_eq_zero]
  exact forall_congr' fun v ↦ imp_congr_left
    ((hσ.criticalHessian_apply_eq_zero_iff hF hcrit v).symm.trans
      (h.criticalHessian_apply_eq_zero_iff hσ hp v))

/-- **Morse components of a moment map.** If the closure `T_ξ` of `{exp (t ξ) | t ∈ ℝ}` is the
whole group, then the component `μ^ξ` is a Morse function exactly when, at every point fixed by
`G`, no nonzero tangent vector is fixed by the differential of every element of `G`. -/
theorem isMorse_iff_of_eq_top
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate)
    (hξ : Lie.closedOneParameterSubgroup ξ = ⊤) :
    IsMorse I' (fun y ↦ μ y ξ) ↔
      ∀ p ∈ MulAction.fixedPoints G M, ∀ v : TangentSpace I' p,
        (∀ g : G, mfderiv I' I' (fun y : M ↦ g • y) p v = v) → v = 0 := by
  rw [← isMorseOn_univ, isMorseOn_iff_criticalPoints,
    h.criticalPoints_eq_fixedPoints_of_eq_top hσ hξ]
  simp only [contMDiffOn_univ, h.contMDiff ξ, true_and, mem_univ, true_imp_iff]
  refine forall₂_congr fun p hp ↦ ?_
  rw [h.isManifoldNondegenerateCriticalPoint_iff hσ
    (fundamentalVectorField_eq_zero_of_forall_smul_eq hp ξ), hξ]
  simp only [Subgroup.mem_top, true_imp_iff]

variable (G) in
/-- **Generic components are Morse when fixed points are infinitesimally isolated.** Let a
compact connected abelian Lie group `G` act with a moment map `μ` such that at every fixed point
of `G` no nonzero tangent vector is fixed by the differential of every element of `G`. Then the
elements `ξ` of the Lie algebra for which `μ^ξ` is a Morse function form a dense subset. -/
theorem dense_setOf_isMorse [IsMulCommutative G] [CompactSpace G] [PreconnectedSpace G]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate)
    (hfix : ∀ p ∈ MulAction.fixedPoints G M, ∀ v : TangentSpace I' p,
      (∀ g : G, mfderiv I' I' (fun y : M ↦ g • y) p v = v) → v = 0) :
    Dense {ξ : GroupLieAlgebra I G | IsMorse I' fun y ↦ μ y ξ} :=
  (Lie.dense_setOf_closedOneParameterSubgroup_eq_top I G).mono fun _ hξ ↦
    (h.isMorse_iff_of_eq_top hσ hξ).2 hfix

end TauCeti.SmoothTwoForm.IsMomentMap
