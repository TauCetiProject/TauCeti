/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Christoffel symbols of a nondegenerate metric in linear coordinates

Let `g : E → E →L[ℝ] E →L[ℝ] ℝ` be a field of symmetric nondegenerate bilinear forms on an open
subset of a finite-dimensional real normed space `E`, as a metric reads in a chart. No positivity
is assumed, so pseudo-Riemannian metrics are included. Writing `Dg(u)` for the derivative of the
metric coefficients in the direction `u`, the *Christoffel symbols of the first kind* are the
covectors

`Γ₁(u, v)(w) = (Dg(u)(v, w) + Dg(v)(u, w) - Dg(w)(u, v)) / 2`,

and the *Christoffel symbols of the second kind* `Γ(u, v)` are the vectors obtained by raising
the index with the metric: `g(Γ(u, v), w) = Γ₁(u, v)(w)` for all `w`. Raising the index is
the inverse of the musical map `v ↦ g(v, ·)`, which is invertible by nondegeneracy. The map `Γ`
is bundled as a continuous bilinear map, so that its smoothness in the base point is a statement
about a single function.

These are the coefficients of the Levi-Civita connection in a chart, and this file proves the
characteristic local facts behind the Koszul construction of that connection:

* `Γ` is symmetric, which is torsion-freeness in coordinates;
* `Dg(u)(v, w) = g(Γ(u, v), w) + g(v, Γ(u, w))`, which is metric compatibility in coordinates;
* `Γ` is the only symmetric bilinear map with this compatibility property, using only
  nondegeneracy;
* if `g` is `C^(n+1)` on an open set then `Γ` is `C^n` there, since inversion of the musical map
  is smooth;
* in a basis, `Γ^k_ij = (1/2) Σ_l g^(kl) (∂_i g_jl + ∂_j g_il - ∂_l g_ij)` with `g^(kl)` the
  inverse of the Gram matrix of the metric.

## Main definitions and results

* `TauCeti.Manifold.christoffelFirstKind`: the Christoffel symbols of the first kind.
* `TauCeti.Manifold.christoffelSecondKind`: the Christoffel symbols of the second kind.
* `TauCeti.Manifold.christoffelSecondKindOfJet`: the Christoffel formula on metric first jets.
* `TauCeti.Manifold.contDiffAt_christoffelSecondKindOfJet`: smoothness at invertible metric values.
* `TauCeti.Manifold.apply_christoffelSecondKind`: lowering the index of `Γ` gives `Γ₁`.
* `TauCeti.Manifold.christoffelSecondKind_comm`: `Γ` is symmetric.
* `TauCeti.Manifold.fderiv_apply_eq_christoffelSecondKind_add`: metric compatibility of `Γ`.
* `TauCeti.Manifold.eq_christoffelSecondKind_iff`: `Γ` is the unique symmetric compatible
  bilinear map.
* `TauCeti.Manifold.contDiffOn_christoffelSecondKind`: smoothness of `Γ`.
* `TauCeti.Manifold.repr_christoffelSecondKind`: the classical index formula.

## References

* B. O'Neill, *Semi-Riemannian Geometry with Applications to Relativity*, Academic Press (1983),
  Chapter 3: the Levi-Civita connection of a nondegenerate metric and its Christoffel symbols.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 5: the Christoffel symbols of a metric in coordinates.
-/

public section

noncomputable section

open Filter ContinuousLinearMap
open scoped Matrix Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {g : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}

/-! ### The Christoffel symbols of the first kind -/

/-- The **Christoffel symbols of the first kind** of a field of bilinear forms `g` at `x`: the
covector `Γ₁(u, v) = w ↦ (Dg(u)(v, w) + Dg(v)(u, w) - Dg(w)(u, v)) / 2`, where `Dg` is the
derivative of `g` at `x`. -/
def christoffelFirstKind (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x u v : E) : E →L[ℝ] ℝ :=
  (2⁻¹ : ℝ) • (fderiv ℝ g x u v + fderiv ℝ g x v u - ((fderiv ℝ g x).flip u).flip v)

/-- Evaluation of the Christoffel symbols of the first kind. -/
@[simp]
theorem christoffelFirstKind_apply (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x u v w : E) :
    christoffelFirstKind g x u v w =
      (fderiv ℝ g x u v w + fderiv ℝ g x v u w - fderiv ℝ g x w u v) / 2 := by
  simp [christoffelFirstKind, div_eq_inv_mul]

/-- At a point where `g` is differentiable, the Christoffel symbols of the first kind of `g`, with
the last term written as the derivative of the scalar function `y ↦ g y u v`. -/
theorem christoffelFirstKind_eq_of_differentiableAt (hg : DifferentiableAt ℝ g x) (u v : E) :
    christoffelFirstKind g x u v =
      (2⁻¹ : ℝ) • (fderiv ℝ g x u v + fderiv ℝ g x v u - fderiv ℝ (fun y ↦ g y u v) x) := by
  ext w
  rw [christoffelFirstKind_apply, smul_apply, sub_apply, add_apply,
    fderiv_clm_apply_const_apply (hg.clm_apply (differentiableAt_const u)),
    fderiv_clm_apply_const_apply hg, smul_eq_mul]
  ring

/-- The Christoffel symbols of the first kind of a metric are symmetric in their first two
arguments. -/
theorem christoffelFirstKind_comm (hsymm : ∀ᶠ y in 𝓝 x, (g y).toBilinForm.IsSymm) (u v : E) :
    christoffelFirstKind g x u v = christoffelFirstKind g x v u := by
  have hc : ∀ᶠ y in 𝓝 x, ∀ a b, g y a b = g y b a :=
    hsymm.mono fun _ ↦ isSymm_toBilinForm_iff.1
  ext w
  simp only [christoffelFirstKind_apply, fderiv_apply_apply_comm hc w u v]
  ring

/-- The Christoffel symbols of the first kind of a metric, summed over the two orders of their
last two arguments, give the derivative of the metric. -/
theorem christoffelFirstKind_add_christoffelFirstKind
    (hsymm : ∀ᶠ y in 𝓝 x, (g y).toBilinForm.IsSymm) (u v w : E) :
    christoffelFirstKind g x u v w + christoffelFirstKind g x u w v = fderiv ℝ g x u v w := by
  have hc : ∀ᶠ y in 𝓝 x, ∀ a b, g y a b = g y b a :=
    hsymm.mono fun _ ↦ isSymm_toBilinForm_iff.1
  simp only [christoffelFirstKind_apply, fderiv_apply_apply_comm hc u w v,
    fderiv_apply_apply_comm hc v u w, fderiv_apply_apply_comm hc w u v]
  ring

/-! ### The Christoffel symbols of the second kind -/

/-- The Christoffel symbols determined by a metric value and its first derivative. The first
component of the jet is the musical map, and the second is the derivative of the metric. -/
def christoffelSecondKindOfJet
    (j : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) :
    E →L[ℝ] E →L[ℝ] E :=
  -- Compose each Koszul term with the inverse separately to avoid operations on trilinear forms.
  (2⁻¹ : ℝ) • (compL ℝ E (E →L[ℝ] ℝ) E j.1.inverse ∘L j.2 +
    compL ℝ E (E →L[ℝ] ℝ) E j.1.inverse ∘L j.2.flip -
    (compL ℝ E (E →L[ℝ] ℝ) E j.1.inverse ∘L
      (flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap) ∘L j.2.flip)

/-- Evaluation of the Christoffel formula on a metric first jet. -/
@[simp]
theorem christoffelSecondKindOfJet_apply
    (j : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) (u v : E) :
    christoffelSecondKindOfJet j u v =
      j.1.inverse ((2⁻¹ : ℝ) • (j.2 u v + j.2 v u - (j.2.flip u).flip v)) := by
  simp [christoffelSecondKindOfJet]

/-- **The Christoffel symbols of the second kind** of a field of bilinear forms `g` at `x`: the
bilinear map `Γ` with `g(Γ(u, v), w) = Γ₁(u, v)(w)`, obtained from the Christoffel symbols of the
first kind `Γ₁` by inverting the musical map `g x : E →L[ℝ] E →L[ℝ] ℝ`. When `g x` is not
invertible this inverse, and hence `Γ`, is zero. -/
def christoffelSecondKind (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) : E →L[ℝ] E →L[ℝ] E :=
  christoffelSecondKindOfJet (g x, fderiv ℝ g x)

/-- The Christoffel symbols at a point depend only on the metric value and its derivative. -/
theorem christoffelSecondKind_eq_christoffelSecondKindOfJet
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) :
    christoffelSecondKind g x = christoffelSecondKindOfJet (g x, fderiv ℝ g x) := by
  rfl

section JetRegularity

-- Cache the canonical bilinear-space instances locally: synthesizing the next operator-space
-- layer directly fails, whereas synthesis succeeds once its target's instances are fixed.
/-- The canonical normed additive group on metric bilinear forms, cached for jet regularity. -/
local instance christoffelBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The canonical real normed space on metric bilinear forms, cached for jet regularity. -/
local instance christoffelBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The Christoffel formula depends smoothly on the metric value and its first derivative
wherever the musical map is invertible. -/
theorem contDiffAt_christoffelSecondKindOfJet [CompleteSpace E] {n : WithTop ℕ∞}
    {j : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)}
    (hj : j.1.IsInvertible) : ContDiffAt ℝ n (christoffelSecondKindOfJet (E := E)) j := by
  -- These canonical instances resolve the intermediate space of composition operators.
  let : NormedAddCommGroup ((E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
      (E := E →L[ℝ] E →L[ℝ] ℝ) (F := E →L[ℝ] E) (σ₁₂ := RingHom.id ℝ)
  let : NormedSpace ℝ ((E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ)
      (E := E →L[ℝ] E →L[ℝ] ℝ) (F := E →L[ℝ] E) (σ₁₂ := RingHom.id ℝ)
  have hinv := (hj.contDiffAt_map_inverse (n := n)).comp j contDiffAt_fst
  have hcomp := (compL ℝ E (E →L[ℝ] ℝ) E).contDiff.contDiffAt.comp j hinv
  have hflip := (flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearEquiv.toContinuousLinearMap
    |>.contDiff.contDiffAt.comp j (contDiffAt_snd (n := n))
  have hperm := ((compL ℝ (E →L[ℝ] E →L[ℝ] ℝ) (E →L[ℝ] E →L[ℝ] ℝ)
    (E →L[ℝ] E)).flip
      (flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap).contDiff.contDiffAt.comp
        j hcomp
  have hfirst := hcomp.clm_comp (𝕜 := ℝ) (E := E)
    (F := E →L[ℝ] E →L[ℝ] ℝ) (G := E →L[ℝ] E) contDiffAt_snd
  have hsecond := hcomp.clm_comp (𝕜 := ℝ) (E := E)
    (F := E →L[ℝ] E →L[ℝ] ℝ) (G := E →L[ℝ] E) hflip
  have hlast := hperm.clm_comp (𝕜 := ℝ) (E := E)
    (F := E →L[ℝ] E →L[ℝ] ℝ) (G := E →L[ℝ] E) hflip
  exact ((hfirst.add hsecond).sub hlast).const_smul (2⁻¹ : ℝ)

end JetRegularity

/-- The Christoffel symbols of the second kind are the Christoffel symbols of the first kind
with the index raised by the inverse musical map. -/
theorem christoffelSecondKind_apply (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x u v : E) :
    christoffelSecondKind g x u v = (g x).inverse (christoffelFirstKind g x u v) := by
  simp [christoffelSecondKind, christoffelFirstKind]

/-- The Christoffel symbols of the second kind of a metric are symmetric. In coordinates this
is torsion-freeness of the Levi-Civita connection. -/
theorem christoffelSecondKind_comm (hsymm : ∀ᶠ y in 𝓝 x, (g y).toBilinForm.IsSymm) (u v : E) :
    christoffelSecondKind g x u v = christoffelSecondKind g x v u := by
  rw [christoffelSecondKind_apply, christoffelSecondKind_apply, christoffelFirstKind_comm hsymm]

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- Lowering the index of the Christoffel symbols of the second kind of a nondegenerate metric
gives the Christoffel symbols of the first kind: `g(Γ(u, v), w) = Γ₁(u, v)(w)`. -/
@[simp]
theorem apply_christoffelSecondKind (hnd : (g x).toBilinForm.Nondegenerate) (u v w : E) :
    g x (christoffelSecondKind g x u v) w = christoffelFirstKind g x u v w := by
  rw [christoffelSecondKind_apply, (isInvertible_of_separatingLeft hnd.1).self_apply_inverse]

/-- **Metric compatibility in coordinates.** The derivative of a symmetric nondegenerate metric
is `Dg(u)(v, w) = g(Γ(u, v), w) + g(v, Γ(u, w))`. -/
theorem fderiv_apply_eq_christoffelSecondKind_add
    (hsymm : ∀ᶠ y in 𝓝 x, (g y).toBilinForm.IsSymm) (hnd : (g x).toBilinForm.Nondegenerate)
    (u v w : E) :
    fderiv ℝ g x u v w =
      g x (christoffelSecondKind g x u v) w + g x v (christoffelSecondKind g x u w) := by
  have hv : g x v (christoffelSecondKind g x u w) = g x (christoffelSecondKind g x u w) v :=
    isSymm_toBilinForm_iff.1 hsymm.self_of_nhds _ _
  rw [hv, apply_christoffelSecondKind hnd, apply_christoffelSecondKind hnd,
    christoffelFirstKind_add_christoffelFirstKind hsymm]

/-- **Uniqueness of the Christoffel symbols.** At a point where the metric is symmetric and
nondegenerate, a symmetric bilinear map `A` with `Dg(u)(v, w) = g(A(u, v), w) + g(v, A(u, w))`
is the map of Christoffel symbols of the second kind. -/
theorem eq_christoffelSecondKind_of_fderiv_apply_eq (hsymm : (g x).toBilinForm.IsSymm)
    (hnd : (g x).toBilinForm.Nondegenerate) {A : E →L[ℝ] E →L[ℝ] E}
    (hA : ∀ u v, A u v = A v u)
    (hcomp : ∀ u v w, fderiv ℝ g x u v w = g x (A u v) w + g x v (A u w)) :
    A = christoffelSecondKind g x := by
  have hg := isSymm_toBilinForm_iff.1 hsymm
  ext u v : 2
  refine (isInvertible_of_separatingLeft hnd.1).injective (ContinuousLinearMap.ext fun w ↦ ?_)
  -- The Koszul combination of three compatibility identities isolates `2 g(A(u, v), w)`.
  have h₁ := hcomp u v w
  have h₂ := hcomp v u w
  have h₃ := hcomp w u v
  rw [hg v (A u w)] at h₁
  rw [hg u (A v w), hA v u] at h₂
  rw [hg u (A w v), hA w u, hA w v] at h₃
  rw [apply_christoffelSecondKind hnd, christoffelFirstKind_apply]
  linarith

/-- **Characterization of the Christoffel symbols.** Near a point where the metric is symmetric,
and at which it is nondegenerate, the Christoffel symbols of the second kind are the unique
symmetric bilinear map `A` with `Dg(u)(v, w) = g(A(u, v), w) + g(v, A(u, w))`. -/
theorem eq_christoffelSecondKind_iff (hsymm : ∀ᶠ y in 𝓝 x, (g y).toBilinForm.IsSymm)
    (hnd : (g x).toBilinForm.Nondegenerate) {A : E →L[ℝ] E →L[ℝ] E} :
    A = christoffelSecondKind g x ↔
      (∀ u v, A u v = A v u) ∧
        ∀ u v w, fderiv ℝ g x u v w = g x (A u v) w + g x v (A u w) := by
  refine ⟨?_, fun h ↦ eq_christoffelSecondKind_of_fderiv_apply_eq hsymm.self_of_nhds hnd h.1 h.2⟩
  rintro rfl
  exact ⟨christoffelSecondKind_comm hsymm, fderiv_apply_eq_christoffelSecondKind_add hsymm hnd⟩

/-! ### Smoothness -/

/-- The Christoffel symbols of the first kind of a `C^m` field of bilinear forms are `C^n` on
an open set, for `n + 1 ≤ m`. -/
theorem contDiffOn_christoffelFirstKind {m n : WithTop ℕ∞} {U : Set E} (hU : IsOpen U)
    (hg : ContDiffOn ℝ m g U) (hnm : n + 1 ≤ m) (u v : E) :
    ContDiffOn ℝ n (fun y ↦ christoffelFirstKind g y u v) U := by
  -- Each coefficient `y ↦ Dg_y(a)(b, c)` is the derivative of the `C^m` function `y ↦ g y b c`.
  have hcoeff (a b c : E) : ContDiffOn ℝ n (fun y ↦ fderiv ℝ g y a b c) U := by
    have h : ContDiffOn ℝ m (fun y ↦ g y b c) U :=
      (hg.clm_apply contDiffOn_const).clm_apply contDiffOn_const
    refine ((h.fderiv_of_isOpen hU hnm).clm_apply (contDiffOn_const (c := a))).congr
      fun y hy ↦ ?_
    have hd : DifferentiableAt ℝ g y :=
      (hg.contDiffAt (hU.mem_nhds hy)).differentiableAt (fun h0 ↦ by simp [h0] at hnm)
    rw [fderiv_clm_apply_const_apply (hd.clm_apply (differentiableAt_const b)),
      fderiv_clm_apply_const_apply hd]
  refine contDiffOn_clm_apply.2 fun w ↦ ?_
  simp only [christoffelFirstKind_apply]
  exact (((hcoeff u v w).add (hcoeff v u w)).sub (hcoeff w u v)).div_const 2

/-- **Smoothness of the Christoffel symbols.** If a field of nondegenerate bilinear forms is
`C^m` on an open set, then its Christoffel symbols of the second kind are `C^n` there, for
`n + 1 ≤ m`. -/
theorem contDiffOn_christoffelSecondKind {m n : WithTop ℕ∞} {U : Set E} (hU : IsOpen U)
    (hg : ContDiffOn ℝ m g U) (hnm : n + 1 ≤ m)
    (hnd : ∀ y ∈ U, (g y).toBilinForm.Nondegenerate) :
    ContDiffOn ℝ n (christoffelSecondKind g) U := by
  have hD := hg.fderiv_of_isOpen hU hnm
  intro y hy
  rw [funext (christoffelSecondKind_eq_christoffelSecondKindOfJet g)]
  simpa only [Function.comp_def] using
    ((contDiffAt_christoffelSecondKindOfJet (j := (g y, fderiv ℝ g y))
      (isInvertible_of_separatingLeft (hnd y hy).1)).comp y
      (((hg.of_le (le_self_add.trans hnm)).contDiffAt (hU.mem_nhds hy)).prodMk
        (hD.contDiffAt (hU.mem_nhds hy)))).contDiffWithinAt

/-! ### The index formula -/

/-- **The index formula for the Christoffel symbols.** For a basis `b` of `E`, the `k`-th
coordinate of `Γ(b i, b j)` is `(1/2) Σ_l g^(kl) (∂_i g_jl + ∂_j g_il - ∂_l g_ij)`, where `g^(kl)`
is the inverse of the Gram matrix `g_ij = g(b i, b j)` of the symmetric nondegenerate metric at
`x`, and `∂_i g_jl = Dg(b i)(b j, b l)`. -/
theorem repr_christoffelSecondKind {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hsymm : (g x).toBilinForm.IsSymm) (hnd : (g x).toBilinForm.Nondegenerate)
    (b : Module.Basis ι ℝ E) (i j k : ι) :
    b.repr (christoffelSecondKind g x (b i) (b j)) k =
      2⁻¹ * ∑ l, (LinearMap.toMatrix₂ b b (g x).toBilinForm)⁻¹ k l *
        (fderiv ℝ g x (b i) (b j) (b l) + fderiv ℝ g x (b j) (b i) (b l) -
          fderiv ℝ g x (b l) (b i) (b j)) := by
  set G := LinearMap.toMatrix₂ b b (g x).toBilinForm
  -- The coordinate vector `c` of `Γ(b i, b j)` satisfies `G c = r`, with `r` the lowered symbols.
  set c : ι → ℝ := fun k ↦ b.repr (christoffelSecondKind g x (b i) (b j)) k
  set r : ι → ℝ := fun l ↦ christoffelFirstKind g x (b i) (b j) (b l)
  have hG : IsUnit G.det :=
    isUnit_iff_ne_zero.2 ((LinearMap.nondegenerate_iff_det_ne_zero b).1 hnd)
  have hGc : G *ᵥ c = r := by
    ext l
    have h := apply_christoffelSecondKind hnd (b i) (b j) (b l)
    conv_lhs at h => rw [← b.sum_repr (christoffelSecondKind g x (b i) (b j))]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul] at h
    simp only [Matrix.mulVec, dotProduct, G, LinearMap.toMatrix₂_apply, toBilinForm_apply, r,
      ← h, c]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [mul_comm]
    congr 1
    exact isSymm_toBilinForm_iff.1 hsymm (b l) (b p)
  have hc : c = G⁻¹ *ᵥ r := by
    rw [← hGc, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG, Matrix.one_mulVec]
  have := congrFun hc k
  simp only [c, r, Matrix.mulVec, dotProduct, christoffelFirstKind_apply] at this
  rw [this, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  ring

end FiniteDimensional

end TauCeti.Manifold
