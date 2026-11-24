/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Torus
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction
public import TauCeti.Geometry.Toric.Delzant.Quotient.Symplectic

/-!
# The Delzant quotient is a Hamiltonian torus manifold

Let `i : N →+ V` be an integral lattice and `(u, c)` the facet presentation of a Delzant polytope
`Δ`, with Delzant quotient `M_Δ = Z / N_Δ` (`TauCeti.Toric.DelzantQuotient i u c`), its smooth
structure, its symplectic form `ω_Δ` (`TauCeti.Toric.IsDelzant.delzantQuotientSymplecticForm`) and
its reduced moment map `μ_Δ : M_Δ → V*` (`TauCeti.Toric.DelzantQuotient.reducedMomentMap`). The
torus `T = (ℝ / 2πℤ)^ι` acts on `M_Δ` through the residual torus `T / N_Δ`. This file shows that
this action is a Hamiltonian torus action with moment map `β_ℝ^* μ_Δ`, where
`β_ℝ : ℝ^ι → V`, `t ↦ Σ_j t_j i(u_j)`, is the derivative of `T → V / 2π i(N)`
(`TauCeti.Toric.IsDelzant.hamiltonianTorusData_delzantQuotientSymplecticForm`):

* **Smoothness.** The torus acts smoothly on the level `Z`, by restricting the rotations
  `z_j ↦ exp(-i θ_j) z_j` of `ℂ^ι` (`TauCeti.Toric.IsDelzant.contMDiffVAdd_delzantLevel`), and
  hence on `M_Δ` (`TauCeti.Toric.IsDelzant.contMDiffVAdd_delzantQuotient`), since the projection
  `π : Z → M_Δ` is a surjective submersion intertwining the two actions.
* **Symplectomorphisms.** Every `θ ∈ T` preserves `ω_Δ`
  (`TauCeti.Toric.IsDelzant.mpullback_vadd_delzantQuotientSymplecticForm`). The rotation by `θ`
  preserves the standard form `ω` of `ℂ^ι`, hence its restriction `i^* ω` to `Z`
  (`TauCeti.Toric.IsDelzant.mpullback_vadd_mpullback_coe_delzantLevel`), and `ω_Δ` is the unique
  form pulling back to `i^* ω` along `π`.
* **The moment map.** Write `ξ_M` for the fundamental vector field of `ξ ∈ ℝ^ι`, the Lie algebra
  of `T`. It is the image under `dπ` of the generator of the rotations on `Z`, which `ℂ^ι` sees as
  the Hamiltonian vector field of `⟨μ, ξ⟩`, for the moment map
  `⟨μ(z), ξ⟩ = Σ_j ξ_j (½ |z_j|² + c_j)` of the torus on `ℂ^ι`
  (`TauCeti.Toric.hamiltonianVectorField_delzantMomentMap`). Since `π^* ω_Δ = i^* ω` and
  `μ(z) = β_ℝ^* μ_Δ [z]` on `Z`
  (`TauCeti.Toric.DelzantQuotient.delzantMomentMap_eq_comp_reducedMomentMap`), this gives
  `ω_Δ(ξ_M, dπ w) = d⟨μ_Δ, β_ℝ ξ⟩(dπ w)` for every tangent vector `w` of `Z`
  (`TauCeti.SmoothTwoForm.eval₂_mfderiv_eq_mvfderiv_of_mpullback_eq`), and these `dπ w`
  exhaust the tangent spaces of `M_Δ`
  (`TauCeti.Toric.IsDelzant.isMomentMap_delzantQuotientSymplecticForm`).
* **Invariance.** `μ_Δ` is invariant under the torus, which acts through the residual torus
  (`TauCeti.Toric.DelzantQuotient.reducedMomentMap_vadd'`).

The torus `T` is taken in its multiplicative copy, the convention of Lie group actions. Its action
on `M_Δ` factors through the residual torus `T / N_Δ`, which for a Delzant polytope is the torus
`V / 2π i(N)` and acts effectively (`TauCeti.Toric.IsDelzant.faithfulVAdd_delzantQuotient`); the
image of `μ_Δ` is `Δ` (`TauCeti.Toric.DelzantQuotient.range_reducedMomentMap`).

## Main results

* `TauCeti.Toric.IsDelzant.mpullback_vadd_delzantQuotientSymplecticForm`: the torus preserves
  `ω_Δ`.
* `TauCeti.Toric.IsDelzant.isMomentMap_delzantQuotientSymplecticForm`: `β_ℝ^* μ_Δ` is a moment
  map of its fundamental vector fields.
* `TauCeti.Toric.IsDelzant.hamiltonianTorusData_delzantQuotientSymplecticForm`: the action of `T`
  on `(M_Δ, ω_Δ)` is a Hamiltonian torus action with moment map `β_ℝ^* μ_Δ`.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 23 and 29.
-/

public section

noncomputable section

open Module Set Real
open scoped Manifold ContDiff

namespace TauCeti.Toric

local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {ι N V : Type*} [Fintype ι] [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {i : N →+ V} {u : ι → N} {c : ι → ℝ}

namespace IsDelzant

variable (hΔ : IsDelzant i u c) (hi : IsIntegralLattice i)
include hΔ hi

/-! ### The torus acts by symplectomorphisms -/

/-- **The torus acts on the Delzant quotient by symplectomorphisms**: every element of the torus
preserves the symplectic form `ω_Δ` of the Delzant quotient. Since `ω_Δ` is the unique form
pulling back along the projection `π : Z → M_Δ` to the restriction `i^* ω` of the standard form,
this follows from the invariance of `i^* ω`, as `π` intertwines the actions. -/
theorem mpullback_vadd_delzantQuotientSymplecticForm (θ : ι → AddCircle (2 * π)) :
    letI := hΔ.delzantQuotientChartedSpace hi
    haveI := hΔ.isManifold_delzantQuotient hi
    haveI := hΔ.contMDiffVAdd_delzantQuotient hi
    SmoothForm.mpullback (fun q : DelzantQuotient i u c ↦ θ +ᵥ q)
        (ContMDiffVAdd.contMDiff_const_vadd (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) θ)
        (hΔ.delzantQuotientSymplecticForm hi) =
      hΔ.delzantQuotientSymplecticForm hi := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantLevel hi ∞
  have := hΔ.isManifold_delzantQuotient hi
  have := hΔ.contMDiffVAdd_delzantLevel hi
  have := hΔ.contMDiffVAdd_delzantQuotient hi
  refine (hΔ.eq_delzantQuotientSymplecticForm_iff hi).2 ?_
  rw [SmoothForm.mpullback_mpullback_of_comp_eq _ _
    (ContMDiffVAdd.contMDiff_const_vadd (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) θ)
    (hΔ.isSubmersion_delzantQuotientMk hi).contMDiff
    (funext fun z ↦ DelzantQuotient.vadd_mk θ z),
    hΔ.mpullback_delzantQuotientMk_delzantQuotientSymplecticForm hi,
    hΔ.mpullback_vadd_mpullback_coe_delzantLevel hi θ]

/-! ### The moment map

The Lie algebra of the torus is its tangent space `ℝ^ι` at the identity, so its elements are read
as angle velocities `ξ : ι → ℝ`. -/

/-- **The fundamental vector fields on the level are rotation generators.** For the torus acting on
the level, the inclusion into `ℂ^ι` sends the fundamental vector field `ξ_Z(z)` of `ξ ∈ ℝ^ι` to the
generator `weightGenerator (-ξ) z` of the rotations, which is the Hamiltonian vector field of
`⟨μ, ξ⟩` (`TauCeti.Toric.hamiltonianVectorField_delzantMomentMap`). -/
theorem mvfderiv_coe_fundamentalVectorField_delzantLevel (z : delzantLevel i u c) (ξ : ι → ℝ) :
    letI := hΔ.delzantLevelChartedSpace hi
    haveI := hΔ.contMDiffVAdd_delzantLevel hi
    mvfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
        ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) z
        (fundamentalVectorField 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
          (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (G := Multiplicative (ι → AddCircle (2 * π))) ξ z) =
      weightGenerator (-ξ) z := by
  let _ := hΔ.delzantLevelChartedSpace hi
  have := hΔ.contMDiffVAdd_delzantLevel hi
  have hcoe := (hΔ.contMDiff_coe_delzantLevel hi (m := ∞)).mdifferentiableAt (x := z) (by simp)
  have horbit : MDifferentiableAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
      (fun g : Multiplicative (ι → AddCircle (2 * π)) ↦ g • z) 1 :=
    ((contMDiff_id.smul contMDiff_const : ContMDiff _ _ ∞ _) 1).mdifferentiableAt (by simp)
  have hrot : MDifferentiableAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
      (fun θ : ι → AddCircle (2 * π) ↦ torusRotation θ z) 0 :=
    ((contMDiff_torusRotation.comp (contMDiff_id.prodMk contMDiff_const) : ContMDiff _ _ ∞ _)
      0).mdifferentiableAt (by simp)
  have htoAdd : MDifferentiableAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (Multiplicative.toAdd : Multiplicative (ι → AddCircle (2 * π)) → ι → AddCircle (2 * π)) 1 :=
    ((Multiplicative.contMDiff_toAdd : ContMDiff _ _ ∞ _) 1).mdifferentiableAt (by simp)
  -- The multiplicative copy of the torus carries the charts of the torus, so forgetting the type
  -- tag, which is the identity on the underlying torus, has the identity as derivative.
  have hdtoAdd : mfderiv (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (Multiplicative.toAdd : Multiplicative (ι → AddCircle (2 * π)) → ι → AddCircle (2 * π)) 1
        ξ = ξ :=
    congrArg (· ξ) (mfderiv_id (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (M := Multiplicative (ι → AddCircle (2 * π))) (x := 1))
  -- The composite of the orbit map with the inclusion is the rotation orbit map after `toAdd`.
  have hcomp : ((↑) ∘ fun g : Multiplicative (ι → AddCircle (2 * π)) ↦ g • z) =
      (fun θ ↦ torusRotation θ z) ∘ Multiplicative.toAdd :=
    funext fun g ↦ by
      rw [Function.comp_apply, Function.comp_apply, ← toAdd_vadd, coe_vadd_delzantLevel]
  rw [mvfderiv_apply_eq_mfderiv_apply, fundamentalVectorField_apply
      (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (G := Multiplicative (ι → AddCircle (2 * π))) ξ z,
    ← mfderiv_comp_apply_of_eq 1 hcoe horbit (one_smul _ z) ξ, hcomp,
    mfderiv_comp_apply_of_eq 1 hrot htoAdd toAdd_one ξ, hdtoAdd, mfderiv_torusRotation_zero]

/-- **The fundamental vector fields on the Delzant quotient** are the images under the projection
`π : Z → M_Δ` of those on the level: `ξ_M([z]) = dπ (ξ_Z(z))`, since `π` is equivariant. -/
theorem fundamentalVectorField_delzantQuotientMk (z : delzantLevel i u c) (ξ : ι → ℝ) :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ.delzantQuotientChartedSpace hi
    haveI := hΔ.contMDiffVAdd_delzantLevel hi
    fundamentalVectorField 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (G := Multiplicative (ι → AddCircle (2 * π))) ξ (DelzantQuotient.mk z) =
      mfderiv 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
        𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
          (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
        DelzantQuotient.mk z (fundamentalVectorField
          𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (G := Multiplicative (ι → AddCircle (2 * π))) ξ z) := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.contMDiffVAdd_delzantLevel hi
  refine (mfderiv_fundamentalVectorField_of_map_smul
    ((hΔ.isSubmersion_delzantQuotientMk hi).contMDiff.mdifferentiableAt (by simp))
    (((contMDiff_id.smul contMDiff_const : ContMDiff _ _ ∞ _) 1).mdifferentiableAt (by simp))
    (fun g ↦ ?_) ξ).symm
  rw [← toAdd_vadd, ← toAdd_vadd, DelzantQuotient.vadd_mk]

/-- The moment map equation `ω_Δ(ξ_M, ·) = d⟨μ_Δ, β_ℝ ξ⟩` on the Delzant quotient. -/
private theorem eval₂_delzantQuotientSymplecticForm_fundamentalVectorField
    (hβ : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j))) (ξ : ι → ℝ)
    (q : DelzantQuotient i u c) :
    letI := hΔ.delzantQuotientChartedSpace hi
    haveI := hΔ.isManifold_delzantQuotient hi
    haveI := hΔ.contMDiffVAdd_delzantQuotient hi
    ∀ v, SmoothBundleForm.eval₂ (hΔ.delzantQuotientSymplecticForm hi) q
        (fundamentalVectorField 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
          (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
          (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (G := Multiplicative (ι → AddCircle (2 * π))) ξ q) v =
      mvfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
          (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
        (fun q ↦ DelzantQuotient.reducedMomentMap hβ q
          (Fintype.linearCombination ℝ (fun j ↦ i (u j)) ξ)) q v := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ.delzantQuotientChartedSpace hi
  intro v
  obtain ⟨z, rfl⟩ := DelzantQuotient.mk_surjective q
  obtain ⟨w, rfl⟩ := (hΔ.isSubmersion_delzantQuotientMk hi).surjective_mfderiv (x := z) (by simp) v
  have := hΔ.isManifold_delzantLevel hi ∞
  have := hΔ.isManifold_delzantQuotient hi
  -- In `ℂ^ι`, the generator of `ξ` is the Hamiltonian vector field of `⟨μ, ξ⟩`.
  have hX : stdSymplecticForm.constSmooth.IsHamiltonianVectorField
      (fun y ↦ delzantMomentMap c y ξ) (weightGenerator (-ξ)) := by
    have h := (SymplecticForm.isNondegenerate_constSmooth stdSymplecticForm
      ).isHamiltonianVectorField_hamiltonianVectorField fun y ↦ delzantMomentMap c y ξ
    rwa [SymplecticForm.hamiltonianVectorField_constSmooth,
      funext (hamiltonianVectorField_delzantMomentMap (c := c) ξ)] at h
  -- On representatives, `⟨μ_Δ, β_ℝ ξ⟩` is `⟨μ, ξ⟩`, since `μ(z) = β_ℝ^* μ_Δ [z]`.
  have hfF : (fun y ↦ delzantMomentMap c y ξ) ∘
      ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) =
      (fun q ↦ DelzantQuotient.reducedMomentMap hβ q
        (Fintype.linearCombination ℝ (fun j ↦ i (u j)) ξ)) ∘ DelzantQuotient.mk :=
    funext fun x ↦ by
      rw [Function.comp_apply, Function.comp_apply,
        DelzantQuotient.delzantMomentMap_eq_comp_reducedMomentMap hβ x,
        ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap']
  rw [hΔ.fundamentalVectorField_delzantQuotientMk hi z ξ]
  exact SmoothTwoForm.eval₂_mfderiv_eq_mvfderiv_of_mpullback_eq (hΔ.contMDiff_coe_delzantLevel hi)
    (hΔ.isSubmersion_delzantQuotientMk hi).contMDiff
    (hΔ.mpullback_delzantQuotientMk_delzantQuotientSymplecticForm hi) hX hfF
    (((contDiff_delzantMomentMap c (n := ∞)).clm_apply contDiff_const).contMDiff.mdifferentiableAt
      (by simp))
    (((hΔ.contMDiff_reducedMomentMap hi hβ).clm_apply contMDiff_const).mdifferentiableAt (by simp))
    ((mvfderiv_apply_eq_mfderiv_apply (F := EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) _ _
      _).symm.trans (hΔ.mvfderiv_coe_fundamentalVectorField_delzantLevel hi z ξ)) w

/-- **The moment map of the torus action on the Delzant quotient.** For the action of the torus
`(ℝ / 2πℤ)^ι` on `(M_Δ, ω_Δ)`, the reduced moment map composed with `β_ℝ : ℝ^ι → V`,
`ξ ↦ ⟨μ_Δ, β_ℝ ξ⟩`, is a moment map of the fundamental vector fields:
`ω_Δ(ξ_M, ·) = d⟨μ_Δ, β_ℝ ξ⟩`. -/
theorem isMomentMap_delzantQuotientSymplecticForm
    (hβ : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j))) :
    letI := hΔ.delzantQuotientChartedSpace hi
    haveI := hΔ.isManifold_delzantQuotient hi
    haveI := hΔ.contMDiffVAdd_delzantQuotient hi
    (hΔ.delzantQuotientSymplecticForm hi).IsMomentMap
      (InfinitesimalAction.fundamental (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (Multiplicative (ι → AddCircle (2 * π)))
        𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
          (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) (DelzantQuotient i u c))
      fun q ↦ (DelzantQuotient.reducedMomentMap hβ q).toLinearMap ∘ₗ
        Fintype.linearCombination ℝ fun j ↦ i (u j) := by
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantQuotient hi
  have := hΔ.contMDiffVAdd_delzantQuotient hi
  refine ⟨fun ξ ↦ (hΔ.contMDiff_reducedMomentMap hi hβ).clm_apply contMDiff_const,
    fun ξ ↦ SmoothTwoForm.isHamiltonianVectorField_iff.2 fun q v ↦ ?_⟩
  rw [InfinitesimalAction.fundamental_apply]
  exact hΔ.eval₂_delzantQuotientSymplecticForm_fundamentalVectorField hi hβ ξ q v

/-- **The Delzant quotient is a Hamiltonian torus manifold.** The torus `(ℝ / 2πℤ)^ι` acts smoothly
on the Delzant quotient `(M_Δ, ω_Δ)` by symplectomorphisms, and `ξ ↦ ⟨μ_Δ, β_ℝ ξ⟩` is an invariant
moment map of the action. The action factors through the residual torus. -/
theorem hamiltonianTorusData_delzantQuotientSymplecticForm
    (hβ : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j))) :
    letI := hΔ.delzantQuotientChartedSpace hi
    haveI := hΔ.isManifold_delzantQuotient hi
    haveI := hΔ.contMDiffVAdd_delzantQuotient hi
    (hΔ.delzantQuotientSymplecticForm hi).HamiltonianTorusData
      (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (G := Multiplicative (ι → AddCircle (2 * π)))
      fun q ↦ (DelzantQuotient.reducedMomentMap hβ q).toLinearMap ∘ₗ
        Fintype.linearCombination ℝ fun j ↦ i (u j) := by
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantQuotient hi
  have := hΔ.contMDiffVAdd_delzantQuotient hi
  refine SmoothTwoForm.hamiltonianTorusData_iff.2
    ⟨fun g ↦ ?_, hΔ.isMomentMap_delzantQuotientSymplecticForm hi hβ, fun g q ↦ ?_⟩
  · simp only [← toAdd_vadd]
    exact hΔ.mpullback_vadd_delzantQuotientSymplecticForm hi g.toAdd
  · rw [← toAdd_vadd, DelzantQuotient.reducedMomentMap_vadd']

end IsDelzant

end TauCeti.Toric
