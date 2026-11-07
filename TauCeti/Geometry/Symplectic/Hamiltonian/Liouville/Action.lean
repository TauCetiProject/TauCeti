/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Period
import Mathlib.Algebra.Group.Subgroup.Finsupp

/-!
# Action variables near a regular Liouville torus

Let `σ` be a symplectic form on a boundaryless manifold `M`, and let `F : M → (ι → ℝ)` be a smooth
family of pairwise Poisson-commuting functions with complete Hamiltonian vector fields, with the
conventions `ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`. Their flows generate an action
`v • y` of `ι → ℝ` on `M` (`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowAction`), whose
stabilizer `Λ_y` (`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowStabilizer`) is the group of
**periods** of `y`.

Let `s` be a local section of `F`, `F (s c) = c`, and let `λ` be a smooth family of periods along
it: `λ c ∈ Λ_{s c}`. This file proves that the **period one-form** `∑ⱼ λⱼ(c) dcⱼ` on the space of
values of `F` is closed, that is, the derivative of `λ` is symmetric with respect to the dot product
(`TauCeti.SmoothTwoForm.IsSymplectic.fderiv_dotProduct_comm_of_mem_hamiltonianFlowStabilizer`).
This comes from differentiating `λ(c) • s(c) = s(c)` and using that the derivative of the action of
a period `λ(c)` at the fixed point `s(c)` is a linear symplectic map
(`eval₂_mfderiv_hamiltonianFlowAction_of_mem_hamiltonianFlowStabilizer`, in the namespace
`TauCeti.SmoothTwoForm.IsSymplectic`).

By the Poincaré lemma for one-forms on convex sets
(`Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric`), a period family on a convex open set
therefore has an **action function** `A` with `dA = (2π)⁻¹ ∑ⱼ λⱼ dcⱼ`
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_forall_hasFDerivAt_of_mem_hamiltonianFlowStabilizer`).

Near a compact connected component of a level consisting of regular points of `F`, on a manifold of
dimension `2 |ι|`, the periods along a section form lattices with a smoothly varying basis
`λ⁽ⁱ⁾` (`exists_hamiltonianFlowStabilizer_section_eq_closure_of_isCompact`, in the namespace
`TauCeti.SmoothTwoForm.IsSymplectic`).
The corresponding action functions `Aᵢ`, with `dAᵢ = (2π)⁻¹ ∑ⱼ λ⁽ⁱ⁾ⱼ dcⱼ`, are the **action
variables** of the Liouville–Arnold theorem: the map `A = (A₁, …, Aₙ)` is a local diffeomorphism of
the space of values of `F`
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_isLocalDiffeomorphAt_action_of_isCompact`).
Equivalently, the periods of `s c` are exactly the vectors `v` whose one-form `v ⬝ᵥ dc` is
`2π ∑ᵢ nᵢ dAᵢ` for integers `nᵢ`: the period lattice is `2π (DA)ᵀ ℤⁿ`.

The angle coordinates and the symplectic form `∑ dθᵢ ∧ dAᵢ` in action-angle coordinates are not
treated here.

## Main results

All in the namespace `TauCeti.SmoothTwoForm.IsSymplectic`:

* `fderiv_dotProduct_comm_of_mem_hamiltonianFlowStabilizer`: the period one-forms are closed.
* `exists_forall_hasFDerivAt_of_mem_hamiltonianFlowStabilizer`: on a convex open set, a period
  family has an action function.
* `exists_isLocalDiffeomorphAt_action_of_isCompact`: action variables near a compact regular
  component of a level.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (action-angle variables).
* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706 (the period lattice and the action coordinates).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.4.
-/

public section

open Set Filter Module Topology Function Real
open ContinuousLinearMap (proj)
open scoped Manifold ContDiff Matrix

namespace TauCeti

namespace SmoothTwoForm

namespace IsSymplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
  {ι : Type*} [Fintype ι] {F : M → ι → ℝ} (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
  (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
  (hc : ∀ i, IsCompleteVectorField (σ.hamiltonianVectorField (F · i)))
  {s : (ι → ℝ) → M} {p : (ι → ℝ) → ι → ℝ} {c : ι → ℝ}

include hσ hF hcomm hc

/-- Differentiating `λ(c) • s(c) = s(c)`: the derivative `P` of the action of `λ(c)` at `s(c)`
satisfies `P (ds u) = ds u - ∑ᵢ (Dλ u)ᵢ X_{Fᵢ}(s c)`. -/
private theorem mfderiv_hamiltonianFlowAction_mfderiv_section
    (hs : MDifferentiableAt 𝓘(ℝ, ι → ℝ) I s c) (hp : DifferentiableAt ℝ p c)
    (hps : ∀ᶠ c' in 𝓝 c, p c' ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c'))
    (u : ι → ℝ) :
    mfderiv I I (hσ.hamiltonianFlowAction hF hcomm hc (p c)).toMul (s c)
        (mfderiv 𝓘(ℝ, ι → ℝ) I s c u) =
      mfderiv 𝓘(ℝ, ι → ℝ) I s c u -
        ∑ i, fderiv ℝ p c u i • σ.hamiltonianVectorField (F · i) (s c) := by
  set act : (ι → ℝ) → M → M := fun v ↦ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul
  set y := s c
  have hy : act (p c) y = y := (hσ.mem_hamiltonianFlowStabilizer hF hcomm hc).1 hps.self_of_nhds
  set ds : (ι → ℝ) →L[ℝ] TangentSpace I y := mfderiv 𝓘(ℝ, ι → ℝ) I s c
  set dp := fderiv ℝ p c
  have hGd : MDifferentiableAt (𝓘(ℝ, ι → ℝ).prod I) I
      (fun q : (ι → ℝ) × M ↦ act q.1 q.2) (p c, y) :=
    (hσ.contMDiff_hamiltonianFlowAction_uncurry hF hcomm hc).mdifferentiableAt (by simp)
  have hpair : HasMFDerivAt 𝓘(ℝ, ι → ℝ) (𝓘(ℝ, ι → ℝ).prod I) (fun c' ↦ (p c', s c')) c
      (dp.prod ds) :=
    (hasMFDerivAt_iff_hasFDerivAt.2 hp.hasFDerivAt).prodMk hs.hasMFDerivAt
  have hcomp : HasMFDerivAt 𝓘(ℝ, ι → ℝ) I (fun c' ↦ act (p c') (s c')) c _ :=
    hGd.hasMFDerivAt.comp c hpair
  -- `c' ↦ λ(c') • s(c')` agrees with `s` near `c`, so the two have the same derivative.
  have hΦ : (fun c' ↦ act (p c') (s c')) =ᶠ[𝓝 c] s :=
    hps.mono fun c' h ↦ (hσ.mem_hamiltonianFlowStabilizer hF hcomm hc).1 h
  have h := hΦ.mfderiv_eq (I := 𝓘(ℝ, ι → ℝ)) (I' := I)
  rw [hcomp.mfderiv] at h
  have h' : mfderiv (𝓘(ℝ, ι → ℝ).prod I) I (fun q : (ι → ℝ) × M ↦ act q.1 q.2) (p c, y)
      (dp u, ds u) = ds u :=
    congrArg (fun L ↦ L u) h
  -- Split the derivative of the joint action into its two partial derivatives. The tangent
  -- vector `ds u` is viewed in the model space `E` of the product tangent space.
  apply eq_sub_of_add_eq'
  refine Eq.trans ?_ ((mfderiv_prod_eq_add_apply (v := (dp u, @id E (ds u))) hGd).symm.trans h')
  congr 1
  have h1 := hσ.mfderiv_hamiltonianFlowAction_apply hF hcomm hc y (p c) (dp u)
  have hy' : (hσ.hamiltonianFlowAction hF hcomm hc (p c)).toMul y = y := hy
  rw [hy'] at h1
  exact h1.symm

/-- **The period one-forms are closed.** Let `s` be a local section of `F` near `c`, differentiable
at `c`, and let `λ`, differentiable at `c`, be a family of periods along it: `λ c'` is a period of
`s c'` for `c'` near `c`. Then the derivative of `λ` at `c` is symmetric for the dot product:
`Dλ(u) ⬝ᵥ w = Dλ(w) ⬝ᵥ u`. Equivalently, the one-form `∑ⱼ λⱼ dcⱼ` is closed at `c`. -/
theorem fderiv_dotProduct_comm_of_mem_hamiltonianFlowStabilizer
    (hs : MDifferentiableAt 𝓘(ℝ, ι → ℝ) I s c) (hFs : ∀ᶠ c' in 𝓝 c, F (s c') = c')
    (hp : DifferentiableAt ℝ p c)
    (hps : ∀ᶠ c' in 𝓝 c, p c' ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c'))
    (u w : ι → ℝ) :
    fderiv ℝ p c u ⬝ᵥ w = fderiv ℝ p c w ⬝ᵥ u := by
  set B : LinearMap.BilinForm ℝ (TangentSpace I (s c)) := SmoothForm.bilinFormAt σ (s c) with hB
  -- `dF ∘ ds = id`, since `F ∘ s = id` near `c`.
  have hFds (v : ι → ℝ) :
      mfderiv I 𝓘(ℝ, ι → ℝ) F (s c) (mfderiv 𝓘(ℝ, ι → ℝ) I s c v) = v := by
    have hFs' : (F ∘ s) =ᶠ[𝓝 c] id := hFs
    have h := hFs'.mfderiv_eq (I := 𝓘(ℝ, ι → ℝ)) (I' := 𝓘(ℝ, ι → ℝ))
    rw [mfderiv_comp c (hF.mdifferentiableAt (by simp)) hs, mfderiv_id] at h
    exact congrArg (fun L : (ι → ℝ) →L[ℝ] (ι → ℝ) ↦ L v) h
  -- `σ(X_{Fᵢ}, v) = dFᵢ(v)`, and `σ(X_{Fᵢ}, X_{Fₖ}) = {Fᵢ, Fₖ} = 0`.
  have hXv (i : ι) (v : TangentSpace I (s c)) :
      B (σ.hamiltonianVectorField (F · i) (s c)) v = mfderiv I 𝓘(ℝ, ι → ℝ) F (s c) v i := by
    rw [hB, SmoothForm.bilinFormAt_apply, hσ.isNondegenerate.eval₂_hamiltonianVectorField,
      mvfderiv_apply (hF.mdifferentiableAt (by simp)) i]
    simp only [ContinuousLinearMap.comp_apply, mvfderiv_apply_eq_mfderiv_apply]
    rfl
  have hvX (i : ι) (v : TangentSpace I (s c)) :
      B v (σ.hamiltonianVectorField (F · i) (s c)) = -mfderiv I 𝓘(ℝ, ι → ℝ) F (s c) v i := by
    rw [← hXv, hB, SmoothForm.bilinFormAt_apply, SmoothForm.bilinFormAt_apply,
      SmoothBundleForm.eval₂_swap]
  have hFX (i k : ι) :
      mfderiv I 𝓘(ℝ, ι → ℝ) F (s c) (σ.hamiltonianVectorField (F · k) (s c)) i = 0 := by
    rw [← hXv, hB, SmoothForm.bilinFormAt_apply, ← poissonBracket_def]
    exact hcomm i k (s c)
  -- Pair the identities `P (ds u) = ds u - ∑ᵢ (Dλ u)ᵢ X_{Fᵢ}` for `u` and `w` by `σ_y`, using that
  -- `P` is symplectic.
  have h := hσ.eval₂_mfderiv_hamiltonianFlowAction_of_mem_hamiltonianFlowStabilizer hF hcomm hc
    hps.self_of_nhds (mfderiv 𝓘(ℝ, ι → ℝ) I s c u) (mfderiv 𝓘(ℝ, ι → ℝ) I s c w)
  rw [hσ.mfderiv_hamiltonianFlowAction_mfderiv_section hF hcomm hc hs hp hps,
    hσ.mfderiv_hamiltonianFlowAction_mfderiv_section hF hcomm hc hs hp hps,
    ← SmoothForm.bilinFormAt_apply, ← SmoothForm.bilinFormAt_apply, ← hB] at h
  simp only [map_sub, LinearMap.sub_apply, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, hXv, hvX, hFX, hFds, smul_eq_mul, mul_zero, Finset.sum_const_zero,
    sub_zero, mul_neg, Finset.sum_neg_distrib] at h
  simp only [dotProduct]
  linarith

/-- **Action functions.** Let `s` be a differentiable section of `F` over a convex open set `D`,
and let `λ` be a differentiable family of periods along it: `λ c` is a period of `s c` for every
`c ∈ D`. Then the closed one-form `(2π)⁻¹ ∑ⱼ λⱼ dcⱼ` is exact on `D`: it is the differential of a
function `A`. -/
theorem exists_forall_hasFDerivAt_of_mem_hamiltonianFlowStabilizer {D : Set (ι → ℝ)}
    (hD : Convex ℝ D) (hDo : IsOpen D) (hs : MDifferentiableOn 𝓘(ℝ, ι → ℝ) I s D)
    (hFs : ∀ c ∈ D, F (s c) = c) (hp : DifferentiableOn ℝ p D)
    (hps : ∀ c ∈ D, p c ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c)) :
    ∃ A : (ι → ℝ) → ℝ, ∀ c ∈ D,
      HasFDerivAt A ((2 * π)⁻¹ • ∑ j, p c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c := by
  have hω (c : ι → ℝ) (hcD : c ∈ D) :
      HasFDerivAt (fun c ↦ (2 * π)⁻¹ • ∑ j, p c j • (proj j : (ι → ℝ) →L[ℝ] ℝ))
      ((2 * π)⁻¹ • ∑ j, ((proj j).comp (fderiv ℝ p c)).smulRight
        (proj j : (ι → ℝ) →L[ℝ] ℝ)) c := by
    have hpc := ((hp c hcD).differentiableAt (hDo.mem_nhds hcD)).hasFDerivAt
    have h1 (j : ι) : HasFDerivAt (fun c ↦ p c j • (proj j : (ι → ℝ) →L[ℝ] ℝ))
        (((proj j : (ι → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ p c)).smulRight
          (proj j : (ι → ℝ) →L[ℝ] ℝ)) c :=
      ((proj j : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp c hpc).smul_const
        (F := (ι → ℝ) →L[ℝ] ℝ) (proj j)
    exact (HasFDerivAt.fun_sum (F := (ι → ℝ) →L[ℝ] ℝ) (u := Finset.univ)
      fun j _ ↦ h1 j).fun_const_smul (F := (ι → ℝ) →L[ℝ] ℝ) _
  refine hD.exists_forall_hasFDerivAt_of_fderiv_symmetric hDo
    (fun c hcD ↦ (hω c hcD).differentiableAt.differentiableWithinAt) fun c hcD u w ↦ ?_
  have hsym := hσ.fderiv_dotProduct_comm_of_mem_hamiltonianFlowStabilizer hF hcomm hc
    ((hs c hcD).mdifferentiableAt (hDo.mem_nhds hcD))
    (eventually_of_mem (hDo.mem_nhds hcD) hFs)
    ((hp c hcD).differentiableAt (hDo.mem_nhds hcD))
    (eventually_of_mem (hDo.mem_nhds hcD) hps) u w
  rw [(hω c hcD).fderiv]
  simp only [dotProduct] at hsym
  simp [hsym]

/-- **Action variables near a compact Liouville torus.** On a manifold of dimension `2 · |ι|`, let
the connected component of `x` in its level `F⁻¹(F x)` be compact and consist of regular points of
`F`, and let `s` be a smooth local section of `F` through `x`, defined on an open set `t`. Then
there are functions `λ⁽ⁱ⁾` and a map `A : (ι → ℝ) → (ι → ℝ)`, a local diffeomorphism at `F x`,
such that for every `c` near `F x`:

* the vectors `λ⁽ⁱ⁾ c` are linearly independent and generate the period lattice of `s c`;
* the differential of `Aᵢ` at `c` is `(2π)⁻¹ ∑ⱼ λ⁽ⁱ⁾ⱼ(c) dcⱼ`;
* a vector `v` is a period of `s c` exactly when `v ⬝ᵥ dc = 2π ∑ᵢ nᵢ dAᵢ` for some integers `nᵢ`,
  so that the period lattice is `2π (DA)ᵀ ℤⁿ`.

The components `Aᵢ` are the action variables of the Liouville–Arnold theorem. -/
theorem exists_isLocalDiffeomorphAt_action_of_isCompact (hdim : 2 * Fintype.card ι = finrank ℝ E)
    {x : M} {t : Set (ι → ℝ)}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) (ht : IsOpen t) (hxt : F x ∈ t)
    (hsx : s (F x) = x) (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I ∞ s t) (hFs : ∀ c ∈ t, F (s c) = c) :
    ∃ (p : ι → (ι → ℝ) → ι → ℝ) (A : (ι → ℝ) → ι → ℝ),
      IsLocalDiffeomorphAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ A (F x) ∧ ∀ᶠ c in 𝓝 (F x),
        LinearIndependent ℝ (fun i ↦ p i c) ∧
        hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) =
          AddSubgroup.closure (range fun i ↦ p i c) ∧
        (∀ i, HasFDerivAt (fun c ↦ A c i)
          ((2 * π)⁻¹ • ∑ j, p i c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c) ∧
        ∀ v, v ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) ↔
          ∃ n : ι → ℤ, ∀ w, v ⬝ᵥ w = 2 * π * ∑ i, n i * fderiv ℝ (fun c ↦ A c i) c w := by
  classical
  obtain ⟨p, hp⟩ := hσ.exists_hamiltonianFlowStabilizer_section_eq_closure_of_isCompact hF hcomm
    hc hdim hreg hK ht hxt hsx hs hFs
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hp.and (ht.mem_nhds hxt))
  set D := Metric.ball (F x) ε
  have hpi (i : ι) : ContDiffOn ℝ ∞ (p i) D := fun c hc ↦ ((hball hc).1.1 i).contDiffWithinAt
  have hA (i : ι) := hσ.exists_forall_hasFDerivAt_of_mem_hamiltonianFlowStabilizer hF hcomm hc
    (p := p i) (convex_ball _ _) Metric.isOpen_ball
    ((hs.mono fun c hc ↦ (hball hc).2).mdifferentiableOn (by simp))
    (fun c hc ↦ hFs c (hball hc).2) ((hpi i).differentiableOn (by simp))
    (fun c hc ↦ (hball hc).1.2.2 ▸ AddSubgroup.subset_closure (mem_range_self i))
  choose A hA using hA
  set α : ι → (ι → ℝ) → (ι → ℝ) →L[ℝ] ℝ :=
    fun i c ↦ (2 * π)⁻¹ • ∑ j, p i c j • (proj j : (ι → ℝ) →L[ℝ] ℝ) with hα
  have hB (c : ι → ℝ) (hc : c ∈ D) :
      HasFDerivAt (fun c i ↦ A i c) (ContinuousLinearMap.pi fun i ↦ α i c) c :=
    hasFDerivAt_pi.2 fun i ↦ hA i c hc
  refine ⟨p, fun c i ↦ A i c, ?_, eventually_of_mem (Metric.ball_mem_nhds _ hε)
    fun c hc ↦ ⟨(hball hc).1.2.1, (hball hc).1.2.2, fun i ↦ hA i c hc, fun v ↦ ?_⟩⟩
  swap
  · -- The periods are the integral combinations of the `p i c`, and `dAᵢ = (2π)⁻¹ ⟨p i c, ·⟩`.
    have hd (i : ι) (w : ι → ℝ) :
        fderiv ℝ (fun c ↦ A i c) c w = (2 * π)⁻¹ * (p i c ⬝ᵥ w) := by
      rw [(hA i c hc).fderiv]
      simp [dotProduct, Finset.mul_sum]
    simp_rw [hd, (hball hc).1.2.2, AddSubgroup.mem_closure_range_iff_of_fintype]
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨n, fun w ↦ ?_⟩
      rw [sum_dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← Int.cast_smul_eq_zsmul ℝ, smul_dotProduct, smul_eq_mul]
      field_simp
    · rintro ⟨n, hn⟩
      refine ⟨n, funext fun k ↦ ?_⟩
      have h := hn (Pi.single k 1)
      simp only [dotProduct_single, mul_one] at h
      rw [h, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Pi.smul_apply, zsmul_eq_mul]
      field_simp
  -- The action map is smooth on `D`, since its derivative is.
  have hαs (i : ι) : ContDiffOn ℝ ∞ (α i) D := by
    have h1 (j : ι) : ContDiffOn ℝ ∞ (fun c ↦ p i c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) D :=
      (contDiffOn_pi.1 (hpi i) j).smul_const (F := (ι → ℝ) →L[ℝ] ℝ) (proj j)
    exact (ContDiffOn.sum fun j _ ↦ h1 j).const_smul _
  have hBs : ContDiffOn ℝ ∞ (fun c i ↦ A i c) D := by
    refine contDiffOn_pi.2 fun i ↦ (contDiffOn_infty_iff_fderiv_of_isOpen Metric.isOpen_ball).2
      ⟨fun c hc ↦ (hA i c hc).differentiableAt.differentiableWithinAt, ?_⟩
    exact (hαs i).congr fun c hc ↦ (hA i c hc).fderiv
  -- Its derivative at `F x` is `(2π)⁻¹` times the matrix with rows the periods `p i (F x)`, which
  -- is invertible since these rows are linearly independent.
  have hx := hball (Metric.mem_ball_self hε)
  set L := ContinuousLinearMap.pi fun i ↦ α i (F x) with hL
  have hL' (w : ι → ℝ) : L w = (2 * π)⁻¹ • (Matrix.of fun i j ↦ p i (F x) j) *ᵥ w := by
    ext i
    simp [hL, hα, Matrix.mulVec, dotProduct, Finset.mul_sum]
  have hinj : Injective L := by
    have hM := Matrix.mulVec_injective_iff_isUnit.2
      (Matrix.linearIndependent_row_iff_isUnit.1 hx.1.2.1)
    intro w w' h
    rw [hL', hL'] at h
    exact hM (smul_right_injective _ (by positivity) h)
  set e := (LinearEquiv.ofInjectiveEndo (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) hinj).toContinuousLinearEquiv
  refine isLocalDiffeomorphAt_of_mfderiv_eq (contMDiffOn_iff_contDiffOn.2 hBs) Metric.isOpen_ball
    (Metric.mem_ball_self hε) BoundarylessManifold.isInteriorPoint (by simp) ⟨e, ?_⟩
  rw [mfderiv_eq_fderiv, (hB _ (Metric.mem_ball_self hε)).fderiv]
  rfl

end IsSymplectic

end SmoothTwoForm

end TauCeti
