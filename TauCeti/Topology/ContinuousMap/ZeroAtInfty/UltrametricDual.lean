/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Matrix

/-!
# Duality between `C₀(I, R)` and bounded families

Let `R` be a complete ultrametric normed commutative ring admitting a multiplicative
pseudo-uniformiser (`TauCeti.NormedRing.IsTate R`) and `I` a discrete index type. By the universal
property of the model space (`ZeroAtInftyContinuousMap.linearCombinationEquiv R R`), the continuous
dual of `C₀(I, R)` is isometrically the space `ℓ∞(I, R) = lp (fun _ : I ↦ R) ∞` of bounded
families, for the operator norm of the scope `TauCeti.RingOpNorm`. A bounded family `b` acts by
the convergent pairing

`⟨b, a⟩ = linearCombination R b a = ∑' i, b i * a i`,

which is bounded by `‖b‖ * ‖a‖`. Unlike the archimedean duality `C₀(I, 𝕜)* = ℓ¹` of
`TauCeti/Topology/ContinuousMap/ZeroAtInfty/Dual.lean`, no summability of `b` is needed: the
ultrametric inequality makes the pairing converge for every bounded `b`.

This file develops the two sides of this pairing.

* Pairing with a fixed `a ∈ C₀(I, R)` is a continuous linear functional on `ℓ∞(I, R)`, and
  `ZeroAtInftyContinuousMap.toLpInftyDual R : C₀(I, R) →ₗᵢ[R] (ℓ∞(I, R) →L[R] R)` is a linear
  isometry. Under the identification of `ℓ∞(I, R)` with the dual of `C₀(I, R)` it is the
  evaluation map `a ↦ (u ↦ u a)` into the bidual
  (`ZeroAtInftyContinuousMap.toLpInftyDual_linearCombinationEquiv_symm`), so the canonical
  embedding of `C₀(I, R)` into its bidual is isometric.
* A continuous linear map `u : C₀(J, R) →L[R] C₀(I, R)` has a transpose
  `u.transposeLpInfty : ℓ∞(I, R) →L[R] ℓ∞(J, R)`, characterised by
  `⟨u.transposeLpInfty b, a⟩ = ⟨b, u a⟩`. In coordinates it is the action of the transposed
  matrix on bounded families, `(u.transposeLpInfty b) j = ∑' i, b i * u.matrixCoeff i j`, it
  reverses composition, and it has the same operator norm as `u`. Transposes act on bounded
  families, not on `C₀`: the coefficient families they produce need not tend to zero.

## Main definitions

* `ZeroAtInftyContinuousMap.toLpInftyDual R`: pairing with an element of `C₀(I, R)`, as a linear
  isometry into the dual of `ℓ∞(I, R)`.
* `ContinuousLinearMap.transposeLpInfty`: the transpose of a continuous linear map between model
  spaces, acting on bounded families.

## Main results

* `ZeroAtInftyContinuousMap.toLpInftyDual_linearCombinationEquiv_symm`: the isometry
  `toLpInftyDual` is the canonical embedding of `C₀(I, R)` into its bidual.
* `ContinuousLinearMap.linearCombination_transposeLpInfty`: the defining property of the
  transpose.
* `ContinuousLinearMap.hasSum_transposeLpInfty_apply`: the transposed matrix action.
* `ContinuousLinearMap.transposeLpInfty_comp`: `(u ∘ v)ᵗ = vᵗ ∘ uᵗ`.
* `ContinuousLinearMap.ringOpNorm_transposeLpInfty`: `‖uᵗ‖ = ‖u‖`.

## References

* P. Schneider, *Nonarchimedean Functional Analysis*, Springer, 2002, §§9–10.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS 12 (1962), 69–85.
-/

public section

open Filter Topology
open scoped ENNReal ZeroAtInfty TauCeti.RingOpNorm

variable {I J K R : Type*} [TopologicalSpace I] [DiscreteTopology I]
  [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]

namespace ZeroAtInftyContinuousMap

section Bidual

variable [NormedCommRing R] [TauCeti.NormedRing.IsTate R] [IsUltrametricDist R] [CompleteSpace R]

/-- A functional on `ℓ∞(I, R)` given by pairing with `a` has operator norm at least `‖a‖`: its
value at the coordinate family at `i` is `a i`. -/
private theorem norm_le_ringOpNorm_of_eq_linearCombination (a : C₀(I, R))
    (f : lp (fun _ : I ↦ R) ∞ →L[R] R) (hf : ∀ b, f b = linearCombination R b a) : ‖a‖ ≤ ‖f‖ := by
  classical
  refine (norm_le (ContinuousLinearMap.ringOpNorm_nonneg f)).2 fun i ↦ ?_
  simpa [hf, lp.norm_single] using
    ContinuousLinearMap.le_ringOpNorm f (lp.single (E := fun _ : I ↦ R) ∞ i 1)

variable (R) in
/-- **The embedding of `C₀(I, R)` into its bidual.** Pairing with `a ∈ C₀(I, R)` is the continuous
linear functional `b ↦ ∑' i, b i * a i` on the dual `ℓ∞(I, R)` of `C₀(I, R)`, and `a` is
recovered isometrically from it. -/
noncomputable def toLpInftyDual : C₀(I, R) →ₗᵢ[R] (lp (fun _ : I ↦ R) ∞ →L[R] R) where
  toFun a := LinearMap.mkContinuous
    { toFun b := linearCombination R b a
      map_add' b c := by rw [linearCombination_add, _root_.add_apply]
      map_smul' c b := by simp [linearCombination_smul] }
    ‖a‖ fun b ↦ (norm_linearCombination_apply_le b a).trans_eq (mul_comm _ _)
  map_add' a a' := ContinuousLinearMap.ext fun b ↦ map_add (linearCombination R b) a a'
  map_smul' c a := ContinuousLinearMap.ext fun b ↦ map_smul (linearCombination R b) c a
  norm_map' a := le_antisymm
    (ContinuousLinearMap.ringOpNorm_le_bound _ (norm_nonneg a) fun b ↦
      (norm_linearCombination_apply_le b a).trans_eq (mul_comm _ _))
    (norm_le_ringOpNorm_of_eq_linearCombination a _ fun _ ↦ rfl)

/-- The bidual embedding pairs `a` with a bounded family `b`. -/
@[simp]
theorem toLpInftyDual_apply (a : C₀(I, R)) (b : lp (fun _ : I ↦ R) ∞) :
    toLpInftyDual R a b = linearCombination R b a :=
  (rfl)

/-- Under the identification `linearCombinationEquiv R R` of `ℓ∞(I, R)` with the dual of
`C₀(I, R)`, the isometry `toLpInftyDual R` is the canonical evaluation map `a ↦ (u ↦ u a)` into the
bidual. -/
theorem toLpInftyDual_linearCombinationEquiv_symm [DecidableEq I] (a : C₀(I, R))
    (u : C₀(I, R) →L[R] R) :
    toLpInftyDual R a ((linearCombinationEquiv R R).symm u) = u a := by
  rw [toLpInftyDual_apply, ← linearCombinationEquiv_apply, LinearIsometryEquiv.apply_symm_apply]

end Bidual

end ZeroAtInftyContinuousMap

namespace ContinuousLinearMap

open ZeroAtInftyContinuousMap

variable [NormedCommRing R] [TauCeti.NormedRing.IsTate R] [IsUltrametricDist R] [CompleteSpace R]

/-- **The transpose** of a continuous linear map `u : C₀(J, R) →L[R] C₀(I, R)` between model
spaces, acting on the bounded families that represent continuous linear functionals: the family
`b` is sent to the family representing the functional `a ↦ ⟨b, u a⟩`, whose `j`-th entry is
`∑' i, b i * u.matrixCoeff i j`. -/
noncomputable def transposeLpInfty (u : C₀(J, R) →L[R] C₀(I, R)) :
    lp (fun _ : I ↦ R) ∞ →L[R] lp (fun _ : J ↦ R) ∞ :=
  LinearMap.mkContinuous
    { toFun b := (linearCombinationEquiv R R).symm ((linearCombination R b).comp u)
      map_add' b c := by rw [linearCombination_add, add_comp, map_add]
      map_smul' c b := by simp [linearCombination_smul, smul_comp] }
    ‖u‖ fun b ↦ by
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [LinearIsometryEquiv.norm_map, mul_comm]
      exact (ringOpNorm_comp_le _ _).trans_eq (by rw [ringOpNorm_linearCombination])

/-- **The defining property of the transpose**: `⟨u.transposeLpInfty b, a⟩ = ⟨b, u a⟩`. -/
@[simp]
theorem linearCombination_transposeLpInfty (u : C₀(J, R) →L[R] C₀(I, R))
    (b : lp (fun _ : I ↦ R) ∞) :
    linearCombination R (u.transposeLpInfty b) = (linearCombination R b).comp u := by
  rw [← linearCombinationEquiv_apply]
  exact (linearCombinationEquiv R R).apply_symm_apply _

/-- The entries of the transposed family are the pairings of `b` with the columns of `u`. -/
theorem transposeLpInfty_apply (u : C₀(J, R) →L[R] C₀(I, R)) (b : lp (fun _ : I ↦ R) ∞) (j : J) :
    u.transposeLpInfty b j = linearCombination R b (u (ZeroAtInftyContinuousMap.single j 1)) := by
  rw [← one_smul R (u.transposeLpInfty b j), ← linearCombination_single,
    linearCombination_transposeLpInfty, comp_apply]

/-- **The transposed matrix action**: the `j`-th entry of `u.transposeLpInfty b` is the
unconditional sum of the `b i * u.matrixCoeff i j`. -/
theorem hasSum_transposeLpInfty_apply (u : C₀(J, R) →L[R] C₀(I, R)) (b : lp (fun _ : I ↦ R) ∞)
    (j : J) : HasSum (fun i ↦ b i * u.matrixCoeff i j) (u.transposeLpInfty b j) := by
  simpa only [transposeLpInfty_apply, matrixCoeff_apply, smul_eq_mul, mul_comm] using
    hasSum_linearCombination b (u (ZeroAtInftyContinuousMap.single j 1))

/-- The transpose sends the coordinate family at `i` to the `i`-th row of the matrix of `u`. -/
@[simp]
theorem transposeLpInfty_lpSingle [DecidableEq I] (u : C₀(J, R) →L[R] C₀(I, R)) (i : I) (j : J) :
    u.transposeLpInfty (lp.single ∞ i 1) j = u.matrixCoeff i j := by
  simp [transposeLpInfty_apply, matrixCoeff_apply]

/-- A continuous linear map between model spaces is determined by its transpose. -/
theorem transposeLpInfty_injective :
    Function.Injective (transposeLpInfty : (C₀(J, R) →L[R] C₀(I, R)) → _) := by
  classical
  intro u v h
  refine matrixCoeff_injective (Matrix.ext fun i j ↦ ?_)
  rw [← transposeLpInfty_lpSingle, h, transposeLpInfty_lpSingle]

/-- The transpose of the identity is the identity. -/
@[simp]
theorem transposeLpInfty_id [DecidableEq I] :
    (ContinuousLinearMap.id R C₀(I, R)).transposeLpInfty = ContinuousLinearMap.id R _ :=
  ext fun b ↦ linearCombination_injective (R := R) <| by simp

/-- The transpose of the zero map is zero. -/
@[simp]
theorem transposeLpInfty_zero :
    (0 : C₀(J, R) →L[R] C₀(I, R)).transposeLpInfty = 0 :=
  ext fun b ↦ linearCombination_injective (R := R) <| by simp

/-- Transposition is additive. -/
@[simp]
theorem transposeLpInfty_add (u v : C₀(J, R) →L[R] C₀(I, R)) :
    (u + v).transposeLpInfty = u.transposeLpInfty + v.transposeLpInfty :=
  ext fun b ↦ linearCombination_injective (R := R) <| by simp [linearCombination_add]

/-- Transposition commutes with scalar multiplication. -/
@[simp]
theorem transposeLpInfty_smul (c : R) (u : C₀(J, R) →L[R] C₀(I, R)) :
    (c • u).transposeLpInfty = c • u.transposeLpInfty :=
  ext fun b ↦ linearCombination_injective (R := R) <| by simp [linearCombination_smul]

/-- **Transposition reverses composition**: `(u ∘ v)ᵗ = vᵗ ∘ uᵗ`. -/
@[simp]
theorem transposeLpInfty_comp [TopologicalSpace K] [DiscreteTopology K] [DecidableEq K]
    (u : C₀(J, R) →L[R] C₀(I, R)) (v : C₀(K, R) →L[R] C₀(J, R)) :
    (u.comp v).transposeLpInfty = v.transposeLpInfty.comp u.transposeLpInfty :=
  ext fun b ↦ linearCombination_injective (R := R) <| by simp [comp_assoc]

/-- **The norm of the transpose**: `u.transposeLpInfty` has the same operator norm as `u`. -/
@[simp]
theorem ringOpNorm_transposeLpInfty (u : C₀(J, R) →L[R] C₀(I, R)) :
    ‖u.transposeLpInfty‖ = ‖u‖ := by
  classical
  refine le_antisymm (ringOpNorm_le_bound _ (ringOpNorm_nonneg u) fun b ↦ ?_) ?_
  · rw [← ringOpNorm_linearCombination (R := R), linearCombination_transposeLpInfty,
      ← ringOpNorm_linearCombination (R := R) b, mul_comm]
    exact ringOpNorm_comp_le _ _
  -- Each entry of the matrix of `u` is an entry of the transpose of a coordinate family.
  refine (ringOpNorm_le_iff_forall_norm_matrixCoeff_le (ringOpNorm_nonneg _)).2 fun i j ↦ ?_
  rw [← transposeLpInfty_lpSingle]
  refine (lp.norm_apply_le_norm ENNReal.top_ne_zero _ j).trans ?_
  simpa [lp.norm_single] using
    le_ringOpNorm u.transposeLpInfty (lp.single (E := fun _ : I ↦ R) ∞ i 1)

/-- **Transposes leave `C₀`**: over an infinite index type `J`, the transpose of the summation map
`C₀(J, R) → C₀(Unit, R)`, whose matrix has all entries one, sends the coordinate family to the
constant family one, which does not tend to zero. So transposes act on bounded families and not
on the model spaces themselves. -/
theorem exists_not_tendsto_transposeLpInfty [Infinite J] :
    ∃ (u : C₀(J, R) →L[R] C₀(Unit, R)) (b : lp (fun _ : Unit ↦ R) ∞),
      ¬ Tendsto (fun j ↦ u.transposeLpInfty b j) cofinite (𝓝 0) := by
  have : Nontrivial R := NormOneClass.nontrivial
  refine ⟨Matrix.toZeroAtInftyCLM (Matrix.of fun _ _ ↦ (1 : R))
    (fun _ ↦ by simp) ⟨1, by simp⟩, lp.single ∞ () 1, ?_⟩
  simp [tendsto_const_nhds_iff]

end ContinuousLinearMap
