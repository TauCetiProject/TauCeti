/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.NormalOperator
public import TauCeti.Analysis.Calculus.ContDiff.Twisted
public import TauCeti.Analysis.InnerProductSpace.SymplecticCokernel
public import TauCeti.LinearAlgebra.Determinant.Line
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# Kernel, adjoint kernel and determinant line of the orbit-torus operator

Let `D u = ∂s u + (J₀ ∂t u + S(t) u)` be the model normal operator of an orbit torus
(`TauCeti.orbitTorusOperator`), with `J₀` an orthogonal complex structure on the fibre `V` and
`S` a `d`-periodic path of symmetric operators. Its formal adjoint is

`D† u = -∂s u + (J₀ ∂t u + S(t) u)`

(`TauCeti.orbitTorusAdjoint`): for `C¹` maps twisted by the same signs `ε₁`, `ε₂` along the
two periods, `∫ ⟪D u, v⟫ = ∫ ⟪u, D† v⟫` over the fundamental rectangle
(`TauCeti.setIntegral_inner_orbitTorusOperator_eq_setIntegral_inner_orbitTorusAdjoint`).
The reflection `(s, t) ↦ (-s, t)` intertwines `D` and `D†`
(`TauCeti.orbitTorusOperator_comp_neg_fst`), so the analysis of the kernel of `D` in
`TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.NormalOperator` applies to `D†` as well.

This file turns that analysis into linear algebra. On a finite cover of the torus with deck group
spanned by `(k ℓ, 0)` and `(a ℓ, n d)`, consider the `C²` maps twisted by the signs `ε₁` and `ε₂`
along these generators (`TauCeti.doublyTwistedContDiff`), on which `D` and `D†` act as linear maps
(`TauCeti.orbitTorusOperatorₗ`, `TauCeti.orbitTorusAdjointₗ`). Write `Ψ` for the propagator of the
loop equation `w' = J₀ S(t) w` and `Q = Ψ(d) ^ n` for the return map of the `n`-th iterate.

* If `ε₁ = -1`, both kernels vanish (`TauCeti.ker_orbitTorusOperatorₗ_eq_bot`,
  `TauCeti.ker_orbitTorusAdjointₗ_eq_bot`). This uses only that `J₀` is skew-adjoint and `S`
  symmetric, not that `J₀ ^ 2 = -1` or that `S` is periodic.
* If `ε₁ = 1`, evaluation at the origin is a linear equivalence from each kernel onto the
  `ε₂`-eigenspace `ker (ε₂ - Q)` of the return map, with inverse `v ↦ ((s, t) ↦ Ψ(t) v)`
  (`TauCeti.kerOrbitTorusOperatorEquiv`, `TauCeti.kerOrbitTorusAdjointEquiv`).
* In finite dimension, `v ↦ J₀ v` induces a linear equivalence from `ker (ε₂ - Q)` onto the
  cokernel `V ⧸ range (ε₂ - Q)` (`LinearMap.kerEquivQuotientRangeOfInnerPreserving`). The return
  map preserves the symplectic form `⟪J₀ ·, ·⟫`
  (`TauCeti.inner_apply_dysonSeriesLeft_apply_dysonSeriesLeft_apply`), so `J₀` carries the
  `ε₂`-eigenspace into the orthogonal complement of the range; it meets the range only in `0`, and
  dimensions agree.
  Hence the kernel of `D†` is identified with the cokernel of `ε₂ - Q`
  (`TauCeti.kerOrbitTorusAdjointEquivQuotientRange`).
* Consequently the determinant line `det (ker D) ⊗ (det (ker D†))^*` of the twisted operator is
  isomorphic to the determinant line `det (ker (ε₂ - Q)) ⊗ (det (coker (ε₂ - Q)))^*` of the finite
  map `ε₂ - Q` (`TauCeti.orbitTorusDetLineEquiv`), and the two kernels have the same dimension as
  `ker (ε₂ - Q)` (`TauCeti.finrank_ker_orbitTorusOperatorₗ`,
  `TauCeti.finrank_ker_orbitTorusAdjointₗ`).

For the four real sign characters of an orbit torus, the twists untwisted along the circle factor
are thus compared with `det (1 - Ψ(d))` and `det (-1 - Ψ(d))`, at the level of kernels, adjoint
kernels and determinant lines. Here the kernel of the formal adjoint on `C²` twisted maps plays the
role of the cokernel. Its identification with the cokernel of a Sobolev realization of `D`, and the
determinant signs obtained by transport to a complex-linear reference operator, are separate.

## Main definitions

* `TauCeti.orbitTorusAdjoint`: the formal adjoint `D† u = -∂s u + (J₀ ∂t u + S(t) u)`.
* `TauCeti.orbitTorusOperatorₗ`, `TauCeti.orbitTorusAdjointₗ`: `D` and `D†` on these maps.
* `TauCeti.kerOrbitTorusOperatorEquiv`, `TauCeti.kerOrbitTorusAdjointEquiv`: the kernels of `D`
  and `D†` are `ker (ε₂ - Ψ(d) ^ n)`.
* `TauCeti.kerOrbitTorusAdjointEquivQuotientRange`: the kernel of `D†` is
  `V ⧸ range (ε₂ - Ψ(d) ^ n)`.
* `TauCeti.orbitTorusDetLineEquiv`: the comparison of determinant lines.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant lines).
-/

public section

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace TensorProduct

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {J₀ : V →L[ℝ] V} {S : ℝ → V →L[ℝ] V} {u v : ℝ × ℝ → V} {ε₁ ε₂ ℓ d : ℝ}

section Adjoint

/-- The formal adjoint `D† u = -∂s u + (J₀ ∂t u + S(t) u)` of the orbit-torus operator
`TauCeti.orbitTorusOperator`, for `J₀` skew-adjoint and `S` symmetric
(`TauCeti.setIntegral_inner_orbitTorusOperator_eq_setIntegral_inner_orbitTorusAdjoint`). -/
def orbitTorusAdjoint (J₀ : V →L[ℝ] V) (S : ℝ → V →L[ℝ] V) (u : ℝ × ℝ → V) (z : ℝ × ℝ) : V :=
  -fderiv ℝ u z stdComplexLineReal + (J₀ (fderiv ℝ u z stdComplexLineImag) + S z.2 (u z))

/-- Unfolding `orbitTorusAdjoint` at a point. -/
theorem orbitTorusAdjoint_apply (z : ℝ × ℝ) :
    orbitTorusAdjoint J₀ S u z =
      -fderiv ℝ u z stdComplexLineReal + (J₀ (fderiv ℝ u z stdComplexLineImag) + S z.2 (u z)) :=
  (rfl)

/-- **`D†` is the formal adjoint of `D`.** For `C¹` maps `u` and `v`, both twisted by the signs
`ε₁` along `(ℓ, 0)` and `ε₂` along `(0, d)` with `ε₁ ^ 2 = ε₂ ^ 2 = 1`, and for `J₀`
skew-adjoint and `S` symmetric, `∫ ⟪D u, v⟫ = ∫ ⟪u, D† v⟫` over the fundamental rectangle
`[0, ℓ] × [0, d]`. The difference of the integrands is `∂s ⟪u, v⟫ - ∂t ⟪u, J₀ v⟫`, whose two
potentials are periodic because the twists square to one. -/
theorem setIntegral_inner_orbitTorusOperator_eq_setIntegral_inner_orbitTorusAdjoint
    (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫) (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫)
    (hScont : Continuous S) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (hε₁ : ε₁ ^ 2 = 1)
    (hε₂ : ε₂ ^ 2 = 1) (hus : ∀ s t, u (s + ℓ, t) = ε₁ • u (s, t))
    (hut : ∀ s t, u (s, t + d) = ε₂ • u (s, t)) (hvs : ∀ s t, v (s + ℓ, t) = ε₁ • v (s, t))
    (hvt : ∀ s t, v (s, t + d) = ε₂ • v (s, t)) :
    ∫ z in Icc (0 : ℝ) ℓ ×ˢ Icc 0 d, ⟪orbitTorusOperator J₀ S u z, v z⟫ =
      ∫ z in Icc (0 : ℝ) ℓ ×ˢ Icc 0 d, ⟪u z, orbitTorusAdjoint J₀ S v z⟫ := by
  set e₁ := stdComplexLineReal
  set e₂ := stdComplexLineImag
  have hR : IsCompact (Icc (0 : ℝ) ℓ ×ˢ Icc 0 d) := isCompact_Icc.prod isCompact_Icc
  have hu1 : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hv1 : Differentiable ℝ v := hv.differentiable one_ne_zero
  have hdu : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hdv : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
  have hu0 := hu.continuous
  have hv0 := hv.continuous
  -- The two potentials and their partial derivatives.
  set φ₁ : ℝ × ℝ → ℝ := fun z => ⟪u z, fderiv ℝ v z e₁⟫ + ⟪fderiv ℝ u z e₁, v z⟫
  set φ₂ : ℝ × ℝ → ℝ := fun z => ⟪u z, J₀ (fderiv ℝ v z e₂)⟫ + ⟪fderiv ℝ u z e₂, J₀ (v z)⟫
  have hφ₁ : Continuous φ₁ := by fun_prop
  have hφ₂ : Continuous φ₂ := by fun_prop
  have hfst {w : ℝ × ℝ → V} (hw : Differentiable ℝ w) (s t : ℝ) :
      HasDerivAt (fun s => w (s, t)) (fderiv ℝ w (s, t) e₁) s :=
    (hw _).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_prodMk_left s t)
  have hsnd {w : ℝ × ℝ → V} (hw : Differentiable ℝ w) (s t : ℝ) :
      HasDerivAt (fun t => w (s, t)) (fderiv ℝ w (s, t) e₂) t :=
    (hw _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_prodMk_right s t)
  have hI₁ : ∫ z in Icc (0 : ℝ) ℓ ×ˢ Icc 0 d, φ₁ z = 0 := by
    refine setIntegral_rect_eq_zero_of_hasDerivAt_fst hφ₁ (Φ := fun z => ⟪u z, v z⟫)
      (fun s t => HasDerivAt.inner ℝ (hfst hu1 s t) (hfst hv1 s t)) fun t => ?_
    have hu' : u (ℓ, t) = ε₁ • u (0, t) := by simpa using hus 0 t
    have hv' : v (ℓ, t) = ε₁ • v (0, t) := by simpa using hvs 0 t
    simp only [hu', hv', real_inner_smul_left, real_inner_smul_right]
    linear_combination ⟪u (0, t), v (0, t)⟫ * hε₁
  have hI₂ : ∫ z in Icc (0 : ℝ) ℓ ×ˢ Icc 0 d, φ₂ z = 0 := by
    refine setIntegral_rect_eq_zero_of_hasDerivAt_snd hφ₂ (Φ := fun z => ⟪u z, J₀ (v z)⟫)
      (fun s t => HasDerivAt.inner ℝ (hsnd hu1 s t)
        (J₀.hasFDerivAt.comp_hasDerivAt t (hsnd hv1 s t)))
      fun s => ?_
    have hu' : u (s, d) = ε₂ • u (s, 0) := by simpa using hut s 0
    have hv' : v (s, d) = ε₂ • v (s, 0) := by simpa using hvt s 0
    simp only [hu', hv', map_smul, real_inner_smul_left, real_inner_smul_right]
    linear_combination ⟪u (s, 0), J₀ (v (s, 0))⟫ * hε₂
  -- Pointwise, the difference of the two integrands is `φ₁ - φ₂`.
  have hpt : (fun z => ⟪orbitTorusOperator J₀ S u z, v z⟫ - ⟪u z, orbitTorusAdjoint J₀ S v z⟫) =
      fun z => φ₁ z - φ₂ z := by
    funext z
    simp only [orbitTorusOperator_apply, orbitTorusAdjoint_apply, φ₁, φ₂, e₁, e₂, inner_add_left,
      inner_add_right, inner_neg_right, hJ₀ (fderiv ℝ u z stdComplexLineImag), hS z.2 (u z)]
    ring
  have hc₁ : Continuous fun z => ⟪orbitTorusOperator J₀ S u z, v z⟫ := by
    simp only [orbitTorusOperator_apply]
    fun_prop
  have hc₂ : Continuous fun z => ⟪u z, orbitTorusAdjoint J₀ S v z⟫ := by
    simp only [orbitTorusAdjoint_apply]
    fun_prop
  have h := congrArg (fun f : ℝ × ℝ → ℝ => ∫ z in Icc (0 : ℝ) ℓ ×ˢ Icc 0 d, f z) hpt
  rw [integral_sub (hc₁.continuousOn.integrableOn_compact hR)
      (hc₂.continuousOn.integrableOn_compact hR),
    integral_sub (hφ₁.continuousOn.integrableOn_compact hR)
      (hφ₂.continuousOn.integrableOn_compact hR), hI₁, hI₂, sub_self, sub_eq_zero] at h
  exact h

/-- **Reflection intertwines `D` and `D†`.** For a differentiable `u`, the operator `D` applied to
the reflection `(s, t) ↦ u (-s, t)` is the reflection of `D† u`. -/
theorem orbitTorusOperator_comp_neg_fst (hu : Differentiable ℝ u) (z : ℝ × ℝ) :
    orbitTorusOperator J₀ S (fun w => u (-w.1, w.2)) z = orbitTorusAdjoint J₀ S u (-z.1, z.2) := by
  set L : ℝ × ℝ →L[ℝ] ℝ × ℝ := (-ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hL (w : ℝ × ℝ) : L w = (-w.1, w.2) := rfl
  have hf : HasFDerivAt (fun w => u (-w.1, w.2)) ((fderiv ℝ u (-z.1, z.2)).comp L) z :=
    (hu _).hasFDerivAt.comp z L.hasFDerivAt
  have h₁ : L stdComplexLineReal = -stdComplexLineReal := by
    simp [hL, stdComplexLineReal_eq]
  have h₂ : L stdComplexLineImag = stdComplexLineImag := by
    simp [hL, stdComplexLineImag_eq]
  rw [orbitTorusOperator_apply, orbitTorusAdjoint_apply, hf.fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h₁, h₂, map_neg]

/-- The orbit-torus adjoint is additive on maps differentiable at the point. -/
theorem orbitTorusAdjoint_add {z : ℝ × ℝ} (hu : DifferentiableAt ℝ u z)
    (hv : DifferentiableAt ℝ v z) :
    orbitTorusAdjoint J₀ S (u + v) z = orbitTorusAdjoint J₀ S u z + orbitTorusAdjoint J₀ S v z := by
  simp only [orbitTorusAdjoint_apply, fderiv_add hu hv, add_apply, map_add, Pi.add_apply]
  abel

/-- The orbit-torus adjoint commutes with multiplication by a real scalar. -/
@[simp]
theorem orbitTorusAdjoint_smul (c : ℝ) :
    orbitTorusAdjoint J₀ S (c • u) = c • orbitTorusAdjoint J₀ S u := by
  funext z
  simp only [orbitTorusAdjoint_apply, fderiv_const_smul_field, Pi.smul_apply,
    smul_apply, map_smul, smul_add, smul_neg]

/-- Where the `s`-derivative of `u` vanishes, `D† u = D u`. -/
theorem orbitTorusAdjoint_eq_orbitTorusOperator {z : ℝ × ℝ}
    (h : fderiv ℝ u z stdComplexLineReal = 0) :
    orbitTorusAdjoint J₀ S u z = orbitTorusOperator J₀ S u z := by
  rw [orbitTorusAdjoint_apply, orbitTorusOperator_apply, h, neg_zero]

end Adjoint

section Kernel

variable (J₀ S) in
/-- The orbit-torus operator `D` as a linear map on doubly twisted `C²` maps. -/
def orbitTorusOperatorₗ (p q : ℝ × ℝ) (ε₁ ε₂ : ℝ) :
    doublyTwistedContDiff ℝ V 2 p q ε₁ ε₂ →ₗ[ℝ] ℝ × ℝ → V where
  toFun u := orbitTorusOperator J₀ S u
  map_add' u v := funext fun z => orbitTorusOperator_add
    ((mem_doublyTwistedContDiff.1 u.2).1.differentiable two_ne_zero z)
    ((mem_doublyTwistedContDiff.1 v.2).1.differentiable two_ne_zero z)
  map_smul' c _ := orbitTorusOperator_smul c

variable (J₀ S) in
/-- The formal adjoint `D†` as a linear map on doubly twisted `C²` maps. -/
def orbitTorusAdjointₗ (p q : ℝ × ℝ) (ε₁ ε₂ : ℝ) :
    doublyTwistedContDiff ℝ V 2 p q ε₁ ε₂ →ₗ[ℝ] ℝ × ℝ → V where
  toFun u := orbitTorusAdjoint J₀ S u
  map_add' u v := funext fun z => orbitTorusAdjoint_add
    ((mem_doublyTwistedContDiff.1 u.2).1.differentiable two_ne_zero z)
    ((mem_doublyTwistedContDiff.1 v.2).1.differentiable two_ne_zero z)
  map_smul' c _ := orbitTorusAdjoint_smul c

@[simp]
theorem orbitTorusOperatorₗ_apply {p q : ℝ × ℝ} (u : doublyTwistedContDiff ℝ V 2 p q ε₁ ε₂) :
    orbitTorusOperatorₗ J₀ S p q ε₁ ε₂ u = orbitTorusOperator J₀ S u :=
  (rfl)

@[simp]
theorem orbitTorusAdjointₗ_apply {p q : ℝ × ℝ} (u : doublyTwistedContDiff ℝ V 2 p q ε₁ ε₂) :
    orbitTorusAdjointₗ J₀ S p q ε₁ ε₂ u = orbitTorusAdjoint J₀ S u :=
  (rfl)

theorem mem_ker_orbitTorusOperatorₗ {p q : ℝ × ℝ} {u : doublyTwistedContDiff ℝ V 2 p q ε₁ ε₂} :
    u ∈ LinearMap.ker (orbitTorusOperatorₗ J₀ S p q ε₁ ε₂) ↔
      ∀ z, orbitTorusOperator J₀ S u z = 0 := by
  rw [LinearMap.mem_ker, orbitTorusOperatorₗ_apply, funext_iff]
  rfl

theorem mem_ker_orbitTorusAdjointₗ {p q : ℝ × ℝ} {u : doublyTwistedContDiff ℝ V 2 p q ε₁ ε₂} :
    u ∈ LinearMap.ker (orbitTorusAdjointₗ J₀ S p q ε₁ ε₂) ↔
      ∀ z, orbitTorusAdjoint J₀ S u z = 0 := by
  rw [LinearMap.mem_ker, orbitTorusAdjointₗ_apply, funext_iff]
  rfl

/-- The twists along the generators `(k ℓ, 0)` and `(a ℓ, n d)` of the deck group of a finite
cover, in the coordinate form of the kernel theorems for `TauCeti.orbitTorusOperator`. -/
private theorem twists_of_mem {k n : ℕ} {a : ℤ}
    (hu : u ∈ doublyTwistedContDiff ℝ V 2 ((k : ℝ) * ℓ, 0) ((a : ℝ) * ℓ, (n : ℝ) * d) ε₁ ε₂) :
    (∀ s t, u (s + k * ℓ, t) = ε₁ • u (s, t)) ∧
      ∀ s t, u (s + a * ℓ, t + n * d) = ε₂ • u (s, t) := by
  rw [mem_doublyTwistedContDiff] at hu
  exact ⟨fun s t => by simpa using hu.2.1 (s, t), fun s t => by simpa using hu.2.2 (s, t)⟩

/-- The reflection `(s, t) ↦ u (-s, t)` of a map twisted by `ε₁` along `(k ℓ, 0)` and by `ε₂`
along `(a ℓ, n d)` is twisted by `ε₁` along `(k ℓ, 0)` and by `ε₂` along `(-a ℓ, n d)`. -/
private theorem reflect_mem {k n : ℕ} {a : ℤ} (hε₁ : ε₁ ^ 2 = 1)
    (hu : u ∈ doublyTwistedContDiff ℝ V 2 ((k : ℝ) * ℓ, 0) ((a : ℝ) * ℓ, (n : ℝ) * d) ε₁ ε₂) :
    (fun w : ℝ × ℝ => u (-w.1, w.2)) ∈
      doublyTwistedContDiff ℝ V 2 ((k : ℝ) * ℓ, 0) (((-a : ℤ) : ℝ) * ℓ, (n : ℝ) * d) ε₁ ε₂ := by
  obtain ⟨hs, ht⟩ := twists_of_mem hu
  rw [mem_doublyTwistedContDiff] at hu ⊢
  refine ⟨hu.1.comp (contDiff_fst.neg.prodMk contDiff_snd), fun ⟨s, t⟩ => ?_,
    fun ⟨s, t⟩ => ?_⟩
  · have h := hs (-s - k * ℓ) t
    rw [sub_add_cancel] at h
    simp only [Prod.mk_add_mk, add_zero, neg_add_rev]
    rw [show -((k : ℝ) * ℓ) + -s = -s - k * ℓ by ring, h, smul_smul, ← sq, hε₁, one_smul]
  · have h := ht (-s) t
    simp only [Prod.mk_add_mk, Int.cast_neg]
    rw [show -(s + -(a : ℝ) * ℓ) = -s + a * ℓ by ring, h]

/-- **Twisting along the circle factor kills the kernel of `D`.** On maps antiperiodic along
`(k ℓ, 0)` and twisted by `ε₂` along `(a ℓ, n d)`, the operator `D` is injective. -/
theorem ker_orbitTorusOperatorₗ_eq_bot (hℓ : 0 < ℓ) (hd : 0 < d)
    (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫) (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫)
    (hScont : Continuous S) (hε₂ : ε₂ ^ 2 = 1) {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (a : ℤ) :
    LinearMap.ker (orbitTorusOperatorₗ J₀ S ((k : ℝ) * ℓ, 0) ((a : ℝ) * ℓ, (n : ℝ) * d) (-1) ε₂) =
      ⊥ := by
  refine eq_bot_iff.2 fun u hu => ?_
  obtain ⟨hs, ht⟩ := twists_of_mem u.2
  have h := eq_one_or_eq_zero_of_orbitTorusOperator_eq_zero hℓ hd hJ₀ hS hScont
    (mem_doublyTwistedContDiff.1 u.2).1 (by norm_num) hε₂ hk hn hs ht
    (mem_ker_orbitTorusOperatorₗ.1 hu)
  rw [Submodule.mem_bot]
  exact Subtype.ext (h.resolve_left (by norm_num))

/-- **Twisting along the circle factor kills the kernel of `D†`.** On maps antiperiodic along
`(k ℓ, 0)` and twisted by `ε₂` along `(a ℓ, n d)`, the formal adjoint `D†` is injective. The
reflection `(s, t) ↦ (-s, t)` carries its kernel into the kernel of `D` on maps twisted along
`(k ℓ, 0)` and `(-a ℓ, n d)`. -/
theorem ker_orbitTorusAdjointₗ_eq_bot (hℓ : 0 < ℓ) (hd : 0 < d)
    (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫) (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫)
    (hScont : Continuous S) (hε₂ : ε₂ ^ 2 = 1) {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (a : ℤ) :
    LinearMap.ker (orbitTorusAdjointₗ J₀ S ((k : ℝ) * ℓ, 0) ((a : ℝ) * ℓ, (n : ℝ) * d) (-1) ε₂) =
      ⊥ := by
  refine eq_bot_iff.2 fun u hu => ?_
  have hw := reflect_mem (by norm_num) u.2
  obtain ⟨hs, ht⟩ := twists_of_mem hw
  have hDw (z : ℝ × ℝ) :
      orbitTorusOperator J₀ S (fun w : ℝ × ℝ => (u : ℝ × ℝ → V) (-w.1, w.2)) z = 0 := by
    rw [orbitTorusOperator_comp_neg_fst
      ((mem_doublyTwistedContDiff.1 u.2).1.differentiable two_ne_zero),
      mem_ker_orbitTorusAdjointₗ.1 hu]
  have h := (eq_one_or_eq_zero_of_orbitTorusOperator_eq_zero hℓ hd hJ₀ hS hScont
    (mem_doublyTwistedContDiff.1 hw).1 (by norm_num) hε₂ hk hn hs ht hDw).resolve_left (by norm_num)
  rw [Submodule.mem_bot]
  ext1; funext ⟨s, t⟩
  simpa using congrFun h (-s, t)

variable [CompleteSpace V]

/-- The propagator `Ψ` of the loop equation `w' = J₀ S(t) w` applied to `v`, extended constantly
in `s`. -/
private def propagatorField (J₀ : V →L[ℝ] V) (S : ℝ → V →L[ℝ] V) (v : V) (z : ℝ × ℝ) : V :=
  dysonSeriesLeft (fun t => J₀ ∘L S t) z.2 v

private theorem fderiv_propagatorField_apply_stdComplexLineReal (hScont : Continuous S) (v : V)
    (z : ℝ × ℝ) : fderiv ℝ (propagatorField J₀ S v) z stdComplexLineReal = 0 := by
  have hg := hasDerivAt_dysonSeriesLeft_apply
    ((continuous_const (y := J₀)).clm_comp hScont) v z.2
  have hf : HasFDerivAt (propagatorField J₀ S v) _ z :=
    (hasDerivAt_iff_hasFDerivAt.1 hg).comp z hasFDerivAt_snd
  rw [hf.fderiv]
  simp [stdComplexLineReal_eq]

/-- The propagator field of `v` is independent of `s`, so it also lies in the kernel of `D†`. -/
private theorem orbitTorusAdjoint_propagatorField (hJ₀sq : ∀ x, J₀ (J₀ x) = -x)
    (hScont : Continuous S) (v : V) (z : ℝ × ℝ) :
    orbitTorusAdjoint J₀ S (propagatorField J₀ S v) z = 0 := by
  rw [orbitTorusAdjoint_eq_orbitTorusOperator
    (fderiv_propagatorField_apply_stdComplexLineReal hScont v z)]
  exact orbitTorusOperator_dysonSeriesLeft_apply_eq_zero hJ₀sq hScont v z

/-- For `v` in the `ε₂`-eigenspace of `Ψ(d) ^ n`, the propagator field of `v` is a `C²` map
periodic along `(k ℓ, 0)` and twisted by `ε₂` along `(a ℓ, n d)`. -/
private theorem propagatorField_mem (hS1 : ContDiff ℝ 1 S) (hper : Function.Periodic S d)
    (k : ℕ) {n : ℕ} (a : ℤ) {v : V}
    (hv : v ∈ LinearMap.ker
      (ε₂ • 1 - ((dysonSeriesLeft (fun t => J₀ ∘L S t) d ^ n : V →L[ℝ] V) : V →ₗ[ℝ] V))) :
    propagatorField J₀ S v ∈
      doublyTwistedContDiff ℝ V 2 ((k : ℝ) * ℓ, 0) ((a : ℝ) * ℓ, (n : ℝ) * d) 1 ε₂ := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self,
    ContinuousLinearMap.coe_coe, sub_eq_zero] at hv
  set Ψ := dysonSeriesLeft (fun t => J₀ ∘L S t) with hΨdef
  have hM : Continuous fun t => J₀ ∘L S t := (continuous_const (y := J₀)).clm_comp hS1.continuous
  have hMper : Function.Periodic (fun t => J₀ ∘L S t) d := fun t => by simp only [hper t]
  have hΨ : ContDiff ℝ 2 Ψ := (contDiff_dysonSeriesLeft (n := 1)
    ((contDiff_const (c := J₀)).clm_comp (by simpa using hS1))).of_le (by norm_num)
  rw [mem_doublyTwistedContDiff]
  refine ⟨(hΨ.clm_apply contDiff_const).comp contDiff_snd, fun z => ?_, fun ⟨s, t⟩ => ?_⟩
  · simp [propagatorField]
  · have hadd : Ψ (t + n * d) = Ψ t * Ψ d ^ n :=
      (dysonSeriesLeft_add_of_periodic hM (hMper.nat_mul n) t).trans
        (congrArg (Ψ t * ·) (dysonSeriesLeft_natCast_mul_of_periodic hM hMper n))
    simp only [propagatorField, Prod.mk_add_mk, ← hΨdef]
    rw [hadd, mul_apply_eq_comp, ← hv, map_smul]

/-- A kernel element of `D` on maps twisted by `ε₁` along `(k ℓ, 0)` and by `ε₂` along `(a ℓ, n d)`
is the propagator field of its value at the origin, and that value lies in the `ε₂`-eigenspace
`ker (ε₂ - Ψ(d) ^ n)`. -/
private theorem of_mem_ker (hℓ : 0 < ℓ) (hd : 0 < d) (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫)
    (hJ₀sq : ∀ x, J₀ (J₀ x) = -x) (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫) (hScont : Continuous S)
    (hper : Function.Periodic S d) (hε₁ : ε₁ ^ 2 = 1) (hε₂ : ε₂ ^ 2 = 1) {k n : ℕ} (hk : 0 < k)
    (hn : 0 < n) {a : ℤ}
    (hu : u ∈ doublyTwistedContDiff ℝ V 2 ((k : ℝ) * ℓ, 0) ((a : ℝ) * ℓ, (n : ℝ) * d) ε₁ ε₂)
    (hD : ∀ z, orbitTorusOperator J₀ S u z = 0) :
    u = propagatorField J₀ S (u 0) ∧ u 0 ∈ LinearMap.ker
      (ε₂ • 1 - ((dysonSeriesLeft (fun t => J₀ ∘L S t) d ^ n : V →L[ℝ] V) : V →ₗ[ℝ] V)) := by
  obtain ⟨hs, ht⟩ := twists_of_mem hu
  have hu := (mem_doublyTwistedContDiff.1 hu).1
  refine ⟨funext
    (eq_one_or_eq_zero_and_apply_eq_dysonSeriesLeft_apply_of_orbitTorusOperator_eq_zero hℓ hd hJ₀
      hJ₀sq hS hScont hu hε₁ hε₂ hk hn hs ht hD).2, ?_⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self,
    ContinuousLinearMap.coe_coe, dysonSeriesLeft_pow_apply_eq_smul_of_orbitTorusOperator_eq_zero hℓ
      hd hJ₀ hJ₀sq hS hScont hper hu hε₁ hε₂ hk hn hs ht hD, sub_self]

/-- The adjoint version of `of_mem_ker`, obtained by reflection in `s`. -/
private theorem of_mem_ker_adjoint (hℓ : 0 < ℓ) (hd : 0 < d)
    (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫) (hJ₀sq : ∀ x, J₀ (J₀ x) = -x)
    (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫) (hScont : Continuous S)
    (hper : Function.Periodic S d) (hε₁ : ε₁ ^ 2 = 1) (hε₂ : ε₂ ^ 2 = 1) {k n : ℕ} (hk : 0 < k)
    (hn : 0 < n) {a : ℤ}
    (hu : u ∈ doublyTwistedContDiff ℝ V 2 ((k : ℝ) * ℓ, 0) ((a : ℝ) * ℓ, (n : ℝ) * d) ε₁ ε₂)
    (hD : ∀ z, orbitTorusAdjoint J₀ S u z = 0) :
    u = propagatorField J₀ S (u 0) ∧ u 0 ∈ LinearMap.ker
      (ε₂ • 1 - ((dysonSeriesLeft (fun t => J₀ ∘L S t) d ^ n : V →L[ℝ] V) : V →ₗ[ℝ] V)) := by
  have hw := reflect_mem hε₁ hu
  have hDw (z : ℝ × ℝ) : orbitTorusOperator J₀ S (fun w : ℝ × ℝ => u (-w.1, w.2)) z = 0 := by
    rw [orbitTorusOperator_comp_neg_fst
      ((mem_doublyTwistedContDiff.1 hu).1.differentiable two_ne_zero), hD]
  obtain ⟨h₂, h₃⟩ := of_mem_ker hℓ hd hJ₀ hJ₀sq hS hScont hper hε₁ hε₂ hk hn hw hDw
  have h0 : u (-(0 : ℝ × ℝ).1, (0 : ℝ × ℝ).2) = u 0 := congrArg u (by ext <;> simp)
  rw [h0] at h₂ h₃
  refine ⟨funext fun ⟨s, t⟩ => ?_, h₃⟩
  simpa [propagatorField] using congrFun h₂ (-s, t)

/-- **The kernel of `D` is the eigenspace of the return map.** On maps periodic along `(k ℓ, 0)`
and twisted by `ε₂` along `(a ℓ, n d)`, evaluation at the origin is a linear equivalence from the
kernel of `D` onto the `ε₂`-eigenspace `ker (ε₂ - Ψ(d) ^ n)` of the return map of the `n`-th
iterate of the loop. Its inverse sends `v` to `(s, t) ↦ Ψ(t) v`
(`TauCeti.kerOrbitTorusOperatorEquiv_symm_apply`). -/
def kerOrbitTorusOperatorEquiv (hℓ : 0 < ℓ) (hd : 0 < d) (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫)
    (hJ₀sq : ∀ x, J₀ (J₀ x) = -x) (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫)
    (hS1 : ContDiff ℝ 1 S) (hper : Function.Periodic S d) (hε₂ : ε₂ ^ 2 = 1) {k n : ℕ}
    (hk : 0 < k) (hn : 0 < n) (a : ℤ) :
    LinearMap.ker
        (orbitTorusOperatorₗ J₀ S ((k : ℝ) * ℓ, 0) ((a : ℝ) * ℓ, (n : ℝ) * d) 1 ε₂) ≃ₗ[ℝ]
      LinearMap.ker
        (ε₂ • 1 - ((dysonSeriesLeft (fun t => J₀ ∘L S t) d ^ n : V →L[ℝ] V) : V →ₗ[ℝ] V)) where
  toFun u := ⟨u.1.1 0, (of_mem_ker hℓ hd hJ₀ hJ₀sq hS hS1.continuous hper (one_pow 2) hε₂ hk hn
    u.1.2 (mem_ker_orbitTorusOperatorₗ.1 u.2)).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v :=
    ⟨⟨propagatorField J₀ S v, propagatorField_mem hS1 hper k a v.2⟩,
      mem_ker_orbitTorusOperatorₗ.2
        (orbitTorusOperator_dysonSeriesLeft_apply_eq_zero hJ₀sq hS1.continuous v)⟩
  left_inv u := by
    ext1; ext1
    exact (of_mem_ker hℓ hd hJ₀ hJ₀sq hS hS1.continuous hper (one_pow 2) hε₂ hk hn u.1.2
      (mem_ker_orbitTorusOperatorₗ.1 u.2)).1.symm
  right_inv v := by ext; simp [propagatorField, dysonSeriesLeft_zero]

/-- **The kernel of `D†` is the eigenspace of the return map.** On maps periodic along `(k ℓ, 0)`
and twisted by `ε₂` along `(a ℓ, n d)`, evaluation at the origin is a linear equivalence from the
kernel of the formal adjoint `D†` onto `ker (ε₂ - Ψ(d) ^ n)`, with inverse `v ↦ ((s, t) ↦ Ψ(t) v)`
(`TauCeti.kerOrbitTorusAdjointEquiv_symm_apply`). -/
def kerOrbitTorusAdjointEquiv (hℓ : 0 < ℓ) (hd : 0 < d) (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫)
    (hJ₀sq : ∀ x, J₀ (J₀ x) = -x) (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫)
    (hS1 : ContDiff ℝ 1 S) (hper : Function.Periodic S d) (hε₂ : ε₂ ^ 2 = 1) {k n : ℕ}
    (hk : 0 < k) (hn : 0 < n) (a : ℤ) :
    LinearMap.ker
        (orbitTorusAdjointₗ J₀ S ((k : ℝ) * ℓ, 0) ((a : ℝ) * ℓ, (n : ℝ) * d) 1 ε₂) ≃ₗ[ℝ]
      LinearMap.ker
        (ε₂ • 1 - ((dysonSeriesLeft (fun t => J₀ ∘L S t) d ^ n : V →L[ℝ] V) : V →ₗ[ℝ] V)) where
  toFun u := ⟨u.1.1 0, (of_mem_ker_adjoint hℓ hd hJ₀ hJ₀sq hS hS1.continuous hper (one_pow 2) hε₂
    hk hn u.1.2 (mem_ker_orbitTorusAdjointₗ.1 u.2)).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v :=
    ⟨⟨propagatorField J₀ S v, propagatorField_mem hS1 hper k a v.2⟩,
      mem_ker_orbitTorusAdjointₗ.2 (orbitTorusAdjoint_propagatorField hJ₀sq hS1.continuous v)⟩
  left_inv u := by
    ext1; ext1
    exact (of_mem_ker_adjoint hℓ hd hJ₀ hJ₀sq hS hS1.continuous hper (one_pow 2) hε₂ hk hn u.1.2
      (mem_ker_orbitTorusAdjointₗ.1 u.2)).1.symm
  right_inv v := by ext; simp [propagatorField, dysonSeriesLeft_zero]

section Apply

variable (hℓ : 0 < ℓ) (hd : 0 < d) (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫)
  (hJ₀sq : ∀ x, J₀ (J₀ x) = -x) (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫)
  (hS1 : ContDiff ℝ 1 S) (hper : Function.Periodic S d) (hε₂ : ε₂ ^ 2 = 1) {k n : ℕ}
  (hk : 0 < k) (hn : 0 < n) (a : ℤ)

@[simp]
theorem kerOrbitTorusOperatorEquiv_apply
    (u : LinearMap.ker
      (orbitTorusOperatorₗ J₀ S ((k : ℝ) * ℓ, 0) ((a : ℝ) * ℓ, (n : ℝ) * d) 1 ε₂)) :
    (kerOrbitTorusOperatorEquiv hℓ hd hJ₀ hJ₀sq hS hS1 hper hε₂ hk hn a u : V) =
      (u : ℝ × ℝ → V) 0 :=
  (rfl)

@[simp]
theorem kerOrbitTorusOperatorEquiv_symm_apply
    (v : LinearMap.ker
      (ε₂ • 1 - ((dysonSeriesLeft (fun t => J₀ ∘L S t) d ^ n : V →L[ℝ] V) : V →ₗ[ℝ] V)))
    (z : ℝ × ℝ) :
    ((kerOrbitTorusOperatorEquiv hℓ hd hJ₀ hJ₀sq hS hS1 hper hε₂ hk hn a).symm v :
      ℝ × ℝ → V) z = dysonSeriesLeft (fun t => J₀ ∘L S t) z.2 v :=
  (rfl)

@[simp]
theorem kerOrbitTorusAdjointEquiv_apply
    (u : LinearMap.ker
      (orbitTorusAdjointₗ J₀ S ((k : ℝ) * ℓ, 0) ((a : ℝ) * ℓ, (n : ℝ) * d) 1 ε₂)) :
    (kerOrbitTorusAdjointEquiv hℓ hd hJ₀ hJ₀sq hS hS1 hper hε₂ hk hn a u : V) =
      (u : ℝ × ℝ → V) 0 :=
  (rfl)

@[simp]
theorem kerOrbitTorusAdjointEquiv_symm_apply
    (v : LinearMap.ker
      (ε₂ • 1 - ((dysonSeriesLeft (fun t => J₀ ∘L S t) d ^ n : V →L[ℝ] V) : V →ₗ[ℝ] V)))
    (z : ℝ × ℝ) :
    ((kerOrbitTorusAdjointEquiv hℓ hd hJ₀ hJ₀sq hS hS1 hper hε₂ hk hn a).symm v :
      ℝ × ℝ → V) z = dysonSeriesLeft (fun t => J₀ ∘L S t) z.2 v :=
  (rfl)

/-- The kernel of `D`, on maps periodic along `(k ℓ, 0)` and twisted by `ε₂` along `(a ℓ, n d)`,
has the dimension of the `ε₂`-eigenspace of `Ψ(d) ^ n`. -/
theorem finrank_ker_orbitTorusOperatorₗ (hℓ : 0 < ℓ) (hd : 0 < d)
    (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫)
    (hJ₀sq : ∀ x, J₀ (J₀ x) = -x) (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫)
    (hS1 : ContDiff ℝ 1 S) (hper : Function.Periodic S d) (hε₂ : ε₂ ^ 2 = 1) {k n : ℕ}
    (hk : 0 < k) (hn : 0 < n) (a : ℤ) :
    Module.finrank ℝ (LinearMap.ker
        (orbitTorusOperatorₗ J₀ S ((k : ℝ) * ℓ, 0) ((a : ℝ) * ℓ, (n : ℝ) * d) 1 ε₂)) =
      Module.finrank ℝ (LinearMap.ker
        (ε₂ • 1 - ((dysonSeriesLeft (fun t => J₀ ∘L S t) d ^ n : V →L[ℝ] V) : V →ₗ[ℝ] V))) :=
  (kerOrbitTorusOperatorEquiv hℓ hd hJ₀ hJ₀sq hS hS1 hper hε₂ hk hn a).finrank_eq

/-- The kernel of `D†`, on maps periodic along `(k ℓ, 0)` and twisted by `ε₂` along `(a ℓ, n d)`,
has the dimension of the `ε₂`-eigenspace of `Ψ(d) ^ n`. -/
theorem finrank_ker_orbitTorusAdjointₗ (hℓ : 0 < ℓ) (hd : 0 < d)
    (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫)
    (hJ₀sq : ∀ x, J₀ (J₀ x) = -x) (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫)
    (hS1 : ContDiff ℝ 1 S) (hper : Function.Periodic S d) (hε₂ : ε₂ ^ 2 = 1) {k n : ℕ}
    (hk : 0 < k) (hn : 0 < n) (a : ℤ) :
    Module.finrank ℝ (LinearMap.ker
        (orbitTorusAdjointₗ J₀ S ((k : ℝ) * ℓ, 0) ((a : ℝ) * ℓ, (n : ℝ) * d) 1 ε₂)) =
      Module.finrank ℝ (LinearMap.ker
        (ε₂ • 1 - ((dysonSeriesLeft (fun t => J₀ ∘L S t) d ^ n : V →L[ℝ] V) : V →ₗ[ℝ] V))) :=
  (kerOrbitTorusAdjointEquiv hℓ hd hJ₀ hJ₀sq hS hS1 hper hε₂ hk hn a).finrank_eq

end Apply

variable [FiniteDimensional ℝ V]

/-- **The kernel of `D†` is the cokernel of `ε₂ - Ψ(d) ^ n`.** On maps periodic along `(k ℓ, 0)`
and twisted by `ε₂` along `(a ℓ, n d)`, the map `u ↦ [J₀ (u 0)]` is a linear equivalence from the
kernel of the formal adjoint `D†` onto `V ⧸ range (ε₂ - Ψ(d) ^ n)`. It is the composite of
`TauCeti.kerOrbitTorusAdjointEquiv` with `LinearMap.kerEquivQuotientRangeOfInnerPreserving`, for
the return map `Ψ(d) ^ n`, which preserves the symplectic form `⟪J₀ ·, ·⟫`. -/
def kerOrbitTorusAdjointEquivQuotientRange (hℓ : 0 < ℓ) (hd : 0 < d)
    (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫) (hJ₀sq : ∀ x, J₀ (J₀ x) = -x)
    (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫) (hS1 : ContDiff ℝ 1 S)
    (hper : Function.Periodic S d) (hε₂ : ε₂ ^ 2 = 1) {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (a : ℤ) :
    LinearMap.ker
        (orbitTorusAdjointₗ J₀ S ((k : ℝ) * ℓ, 0) ((a : ℝ) * ℓ, (n : ℝ) * d) 1 ε₂) ≃ₗ[ℝ]
      V ⧸ LinearMap.range
        (ε₂ • 1 - ((dysonSeriesLeft (fun t => J₀ ∘L S t) d ^ n : V →L[ℝ] V) : V →ₗ[ℝ] V)) :=
  (kerOrbitTorusAdjointEquiv hℓ hd hJ₀ hJ₀sq hS hS1 hper hε₂ hk hn a).trans
    (LinearMap.kerEquivQuotientRangeOfInnerPreserving (J := (J₀ : V →ₗ[ℝ] V))
      (Q := ((dysonSeriesLeft (fun t => J₀ ∘L S t) d ^ n : V →L[ℝ] V) : V →ₗ[ℝ] V))
      (Function.LeftInverse.injective (g := fun x => -J₀ x) fun x => by simp [hJ₀sq])
      (fun x y => by
        have hM : Continuous fun t => J₀ ∘L S t :=
          (continuous_const (y := J₀)).clm_comp hS1.continuous
        have hMper : Function.Periodic (fun t => J₀ ∘L S t) d := fun t => by simp only [hper t]
        simpa [← dysonSeriesLeft_natCast_mul_of_periodic hM hMper n] using
          inner_apply_dysonSeriesLeft_apply_dysonSeriesLeft_apply hJ₀ hJ₀sq hS hS1.continuous
            (n * d) x y)
      hε₂ (fun x => by simp))

@[simp]
theorem kerOrbitTorusAdjointEquivQuotientRange_apply (hℓ : 0 < ℓ) (hd : 0 < d)
    (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫) (hJ₀sq : ∀ x, J₀ (J₀ x) = -x)
    (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫) (hS1 : ContDiff ℝ 1 S)
    (hper : Function.Periodic S d) (hε₂ : ε₂ ^ 2 = 1) {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (a : ℤ)
    (u : LinearMap.ker
      (orbitTorusAdjointₗ J₀ S ((k : ℝ) * ℓ, 0) ((a : ℝ) * ℓ, (n : ℝ) * d) 1 ε₂)) :
    kerOrbitTorusAdjointEquivQuotientRange hℓ hd hJ₀ hJ₀sq hS hS1 hper hε₂ hk hn a u =
      Submodule.Quotient.mk (J₀ ((u : ℝ × ℝ → V) 0)) := by
  rw [kerOrbitTorusAdjointEquivQuotientRange, LinearEquiv.trans_apply,
    LinearMap.kerEquivQuotientRangeOfInnerPreserving_apply, kerOrbitTorusAdjointEquiv_apply,
    ContinuousLinearMap.coe_coe]

/-- **The determinant line of the twisted orbit-torus operator.** On maps periodic along
`(k ℓ, 0)` and twisted by `ε₂` along `(a ℓ, n d)`, the line `det (ker D) ⊗ (det (ker D†))^*`,
with the kernel of the formal adjoint in the place of the cokernel, is isomorphic to the
determinant line `det (ker (ε₂ - Q)) ⊗ (det (coker (ε₂ - Q)))^*` of the finite map `ε₂ - Q`, where
`Q = Ψ(d) ^ n` is the return map of the `n`-th iterate of the loop. The isomorphism is induced by
`TauCeti.kerOrbitTorusOperatorEquiv` on the kernel and by
`TauCeti.kerOrbitTorusAdjointEquivQuotientRange` on the cokernel. -/
def orbitTorusDetLineEquiv (hℓ : 0 < ℓ) (hd : 0 < d) (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫)
    (hJ₀sq : ∀ x, J₀ (J₀ x) = -x) (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫)
    (hS1 : ContDiff ℝ 1 S) (hper : Function.Periodic S d) (hε₂ : ε₂ ^ 2 = 1) {k n : ℕ}
    (hk : 0 < k) (hn : 0 < n) (a : ℤ) :
    detLine ℝ (LinearMap.ker
        (orbitTorusOperatorₗ J₀ S ((k : ℝ) * ℓ, 0) ((a : ℝ) * ℓ, (n : ℝ) * d) 1 ε₂)) ⊗[ℝ]
      Module.Dual ℝ (detLine ℝ (LinearMap.ker
        (orbitTorusAdjointₗ J₀ S ((k : ℝ) * ℓ, 0) ((a : ℝ) * ℓ, (n : ℝ) * d) 1 ε₂))) ≃ₗ[ℝ]
      LinearMap.detLine
        (ε₂ • 1 - ((dysonSeriesLeft (fun t => J₀ ∘L S t) d ^ n : V →L[ℝ] V) : V →ₗ[ℝ] V)) :=
  TensorProduct.congr
    (LinearEquiv.detLineCongr (kerOrbitTorusOperatorEquiv hℓ hd hJ₀ hJ₀sq hS hS1 hper hε₂ hk hn a))
    (LinearEquiv.detLineCongr
      (kerOrbitTorusAdjointEquivQuotientRange hℓ hd hJ₀ hJ₀sq hS hS1 hper hε₂ hk hn a)).symm.dualMap

/-- `TauCeti.orbitTorusDetLineEquiv` on a pure tensor `x ⊗ φ`: the kernel factor `x` is transported
along `TauCeti.kerOrbitTorusOperatorEquiv`, and the dual factor `φ` is transported contravariantly,
by precomposition with the determinant-line transport along the inverse of
`TauCeti.kerOrbitTorusAdjointEquivQuotientRange`. -/
@[simp]
theorem orbitTorusDetLineEquiv_tmul (hℓ : 0 < ℓ) (hd : 0 < d)
    (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫) (hJ₀sq : ∀ x, J₀ (J₀ x) = -x)
    (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫) (hS1 : ContDiff ℝ 1 S)
    (hper : Function.Periodic S d) (hε₂ : ε₂ ^ 2 = 1) {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (a : ℤ)
    (x : detLine ℝ (LinearMap.ker
      (orbitTorusOperatorₗ J₀ S ((k : ℝ) * ℓ, 0) ((a : ℝ) * ℓ, (n : ℝ) * d) 1 ε₂)))
    (φ : Module.Dual ℝ (detLine ℝ (LinearMap.ker
      (orbitTorusAdjointₗ J₀ S ((k : ℝ) * ℓ, 0) ((a : ℝ) * ℓ, (n : ℝ) * d) 1 ε₂)))) :
    orbitTorusDetLineEquiv hℓ hd hJ₀ hJ₀sq hS hS1 hper hε₂ hk hn a (x ⊗ₜ φ) =
      LinearEquiv.detLineCongr (kerOrbitTorusOperatorEquiv hℓ hd hJ₀ hJ₀sq hS hS1 hper hε₂ hk hn a)
          x ⊗ₜ
        (LinearEquiv.detLineCongr
          (kerOrbitTorusAdjointEquivQuotientRange hℓ hd hJ₀ hJ₀sq hS hS1 hper hε₂ hk hn
            a).symm).dualMap φ := by
  simp [orbitTorusDetLineEquiv]

end Kernel

end TauCeti
