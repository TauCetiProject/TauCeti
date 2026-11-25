/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Holomorphic
public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.TangentLattice
public import TauCeti.Geometry.Manifold.Algebra.Quotient
import TauCeti.Geometry.Lie.Exponential.Derivative.Basic
import TauCeti.Geometry.Manifold.Complex.InverseFunction
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible

/-!
# A compact connected commutative complex Lie group is a complex torus

Let `G` be a compact connected commutative complex Lie group modelled on a finite-dimensional
complex space `E`. Its exponential `exp : E → G` (the tangent-space exponential of the underlying
real Lie group) is a holomorphic surjective homomorphism, and its kernel `Λ` is a discrete full
`ℤ`-lattice in `E` (`TauCeti.isZLattice_ker_mulInvariantExpAddMonoidHom`). This file shows that
`exp` is a local biholomorphism, so that for connected `G` it induces a biholomorphism `E ⧸ Λ ≃ G`
(`TauCeti.mulInvariantExpQuotientKerDiffeomorph`): `G` is the complex torus of the lattice `Λ`.

The derivative of `exp` at `v` is invertible: near `v`, `exp` followed by translation by
`(exp v)⁻¹` is `w ↦ exp (w - v)`, whose derivative at `v`, read in the chart at the identity, is the
identity (`TauCeti.hasFDerivAt_extChartAt_mulInvariantExp_zero_complex`). The holomorphic inverse
function theorem then applies to the map `E ⧸ Λ → G` through the covering projection
`E → E ⧸ Λ`.

## Main results

* `TauCeti.isInvertible_mfderiv_mulInvariantExp_complex`: the derivative of the exponential of a
  commutative complex Lie group is invertible everywhere.
* `TauCeti.mulInvariantExpQuotientKerDiffeomorph`: for connected `G`, the biholomorphism
  `E ⧸ ker exp ≃ G`, of class `C^n` for every `n`; for compact `G` this exhibits `G` as a complex
  torus.

## References

* C. Birkenhake and H. Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Springer
  (2004), §1.1, for compact connected complex Lie groups as complex tori.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [T2Space G] [LieGroup 𝓘(ℂ, E) ∞ G] [IsMulCommutative G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The underlying real Lie group; a local instance for this file. -/
local instance : LieGroup 𝓘(ℝ, E) ∞ G := LieGroup.restrictScalars_self ℝ (𝕜 := ℂ)

/-- The space `E` is finite-dimensional over `ℂ`; a local instance for this file. -/
local instance : FiniteDimensional ℂ E := .of_restrictScalars_finite ℝ ℂ E

/-- The exponential of the commutative complex Lie group `G`, as a function `E → G`. -/
local notation "expG" => fun v : E ↦
  mulInvariantExp (I := 𝓘(ℝ, E)) (G := G) (v : GroupLieAlgebra 𝓘(ℝ, E) G)

/-- **The derivative of the exponential of a commutative complex Lie group is invertible** at
every point: translated back to the identity, it is the identity of `E` in the chart at `1`. -/
theorem isInvertible_mfderiv_mulInvariantExp_complex (v : E) :
    (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) expG v).IsInvertible := by
  refine (isInvertible_mfderiv_iff_injective rfl).2 ?_
  set g := expG v
  -- The chart at `1` after translation by `g⁻¹` is differentiable at `g`.
  have hA : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E)
      (fun x : G ↦ extChartAt 𝓘(ℂ, E) (1 : G) (g⁻¹ * x)) g := by
    refine MDifferentiableAt.comp g ?_
      (((contMDiff_mul_left (I := 𝓘(ℂ, E)) (n := 1)).mdifferentiableAt one_ne_zero))
    rw [inv_mul_cancel]
    exact mdifferentiableAt_extChartAt (mem_chart_source E 1)
  have hB : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E) expG v :=
    mdifferentiable_mulInvariantExp_complex v
  -- The composite is `w ↦ chart (exp (w - v))`, with derivative the identity at `v`.
  have hfun : (fun x : G ↦ extChartAt 𝓘(ℂ, E) (1 : G) (g⁻¹ * x)) ∘ expG =
      fun w : E ↦ extChartAt 𝓘(ℂ, E) (1 : G)
        (mulInvariantExp (I := 𝓘(ℝ, E)) (G := G) ((w - v : E) : GroupLieAlgebra 𝓘(ℝ, E) G)) := by
    funext w
    simp only [Function.comp_apply, g]
    congr 1
    rw [inv_mul_eq_iff_eq_mul]
    refine Eq.trans ?_ (GroupLieAlgebra.mulInvariantExp_add (I := 𝓘(ℝ, E)) (G := G)
      (v : GroupLieAlgebra 𝓘(ℝ, E) G) ((w - v : E) : GroupLieAlgebra 𝓘(ℝ, E) G))
    congr 1
    exact (add_sub_cancel v w).symm
  have hd : HasFDerivAt ((fun x : G ↦ extChartAt 𝓘(ℂ, E) (1 : G) (g⁻¹ * x)) ∘ expG)
      (ContinuousLinearMap.id ℂ E) v := by
    rw [hfun]
    have h0 := hasFDerivAt_extChartAt_mulInvariantExp_zero_complex (E := E) (G := G)
    rw [← sub_self v] at h0
    exact (h0.comp (f := fun x : E ↦ x - v) v ((hasFDerivAt_id v).sub_const v)).congr_fderiv
      (by ext; simp)
  have hc := hd.hasMFDerivAt.mfderiv
  rw [mfderiv_comp v hA hB] at hc
  have key (z : E) : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E)
      (fun x : G ↦ extChartAt 𝓘(ℂ, E) (1 : G) (g⁻¹ * x)) g
        (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) expG v z) = z :=
    DFunLike.congr_fun hc z
  intro x y h
  rw [← key x, ← key y, h]

variable [IsTopologicalGroup G] [PreconnectedSpace G]

/-- The topological group isomorphism `E ⧸ ker exp ≃ G`, written multiplicatively on `G`. -/
local notation "ψ" => fun q : E ⧸ (mulInvariantExpAddMonoidHom 𝓘(ℝ, E) G).ker ↦
  Additive.toMul (mulInvariantExpQuotientKerContinuousAddEquiv (I := 𝓘(ℝ, E)) (G := G) q)

private theorem psi_comp_mk :
    (ψ) ∘ (QuotientAddGroup.mk (s := (mulInvariantExpAddMonoidHom 𝓘(ℝ, E) G).ker)) = expG := by
  funext v
  simp

/-- The map `E ⧸ ker exp → G` is holomorphic. -/
theorem contMDiff_mulInvariantExpQuotientKerContinuousAddEquiv (n : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) n (ψ) := by
  rw [(mulInvariantExpAddMonoidHom 𝓘(ℝ, E) G).ker.contMDiff_quotient_iff (n := ω) le_top]
  rw [psi_comp_mk]
  exact contMDiff_mulInvariantExp_complex n

/-- **A connected commutative complex Lie group is the quotient of its tangent space by the kernel
of the exponential**: the exponential induces a biholomorphism `E ⧸ ker exp ≃ G`, of class `C^n`
for every `n`, including `n = ω`. When `G` is compact, `ker exp` is a full lattice
(`TauCeti.isZLattice_ker_mulInvariantExpAddMonoidHom`), so `G` is a complex torus. -/
def mulInvariantExpQuotientKerDiffeomorph (n : ℕ∞ω) :
    (E ⧸ (mulInvariantExpAddMonoidHom 𝓘(ℝ, E) G).ker) ≃ₘ^n⟮𝓘(ℂ, E), 𝓘(ℂ, E)⟯ G :=
  IsLocalDiffeomorph.diffeomorphOfBijective (f := ψ)
    ((contMDiff_mulInvariantExpQuotientKerContinuousAddEquiv 1).mdifferentiable
        one_ne_zero |>.isLocalDiffeomorph_of_bijective_mfderiv fun q ↦ by
      obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective q
      have hπ := (mulInvariantExpAddMonoidHom 𝓘(ℝ, E) G).ker.isLocalDiffeomorph_quotientMk
        (I := 𝓘(ℂ, E)) (n := 1) v
      have h := isInvertible_mfderiv_mulInvariantExp_complex (G := G) v
      rw [← psi_comp_mk] at h
      exact ((hπ.isInvertible_mfderiv_comp_iff one_ne_zero).mp h).bijective)
    (Additive.toMul.bijective.comp
      (mulInvariantExpQuotientKerContinuousAddEquiv (I := 𝓘(ℝ, E)) (G := G)).bijective)

/-- The biholomorphism `E ⧸ ker exp ≃ G` sends the class of `v` to `exp v`. -/
@[simp]
theorem mulInvariantExpQuotientKerDiffeomorph_mk (n : ℕ∞ω) (v : E) :
    mulInvariantExpQuotientKerDiffeomorph (G := G) n (QuotientAddGroup.mk v) =
      mulInvariantExp (I := 𝓘(ℝ, E)) (G := G) (v : GroupLieAlgebra 𝓘(ℝ, E) G) :=
  by
    rw [mulInvariantExpQuotientKerDiffeomorph, IsLocalDiffeomorph.coe_diffeomorphOfBijective]
    exact congrFun psi_comp_mk v

end TauCeti
