/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Complex.Clutching

/-!
# Clutching numbers of complex vector bundles with a conjugation

Let `E` be a complex vector bundle over `X` with finite-dimensional model fibre `F`. A
**conjugation** of `E` is a family of conjugate-linear automorphisms `c x : E x ≃ E x`, continuous
on the total space. This file shows that a complex vector bundle with a conjugation has vanishing
clutching numbers on `π₂(X, x)` (`TauCeti.clutchingNumber_eq_zero_of_conjugateLinear`): its first
Chern number vanishes on every sphere.

A conjugation identifies `E` with its complex conjugate bundle, whose first Chern class is
`-c₁(E)`, so `c₁(E) = -c₁(E)`. In the clutching description no conjugate bundle is needed. Let
`φ` be a frame of `E` along a sphere `p`, and let `κ` be the conjugation of `F` in a basis. Then
`ψ y = c ∘ φ y ∘ κ` is again a complex-linear frame of `E` along `p`. In the fibre over the base
point, read in a trivialization `e`, the transition `e ∘ ψ y` is the conjugate `κ ∘ (e ∘ φ y) ∘ κ`
of the transition of `φ`, followed by the fixed automorphism `κ ∘ e⁻¹ ∘ c ∘ e`. Conjugating an
automorphism by `κ` conjugates its determinant, and complex conjugation inverts points of the
circle (`Module.Basis.normalizedDet_coordConjL_trans_trans_coordConjL`). So on the boundary of the
square the clutching function of `ψ` is the inverse of that of `φ`, up to a constant factor, and its
degree is the negative of that of `φ`. Both degrees are the clutching number of `p`, which is
therefore `0`.

The motivating instance is a real vector bundle `V` with a continuous complex structure `J` and a
continuous automorphism `c` anticommuting with `J`, `c ∘ J = -J ∘ c`: then `c` is a conjugation of
the complex vector bundle `J.Fiber`, whose clutching numbers therefore vanish
(`TauCeti.Bundle.ContinuousComplexStructure.clutchingNumberHom_eq_zero_of_anticommute`). For the
tangent bundle of a symplectic manifold with a tame almost complex structure `J` and a Lagrangian
distribution `L`, such as the vertical distribution of a cotangent bundle, the reflection of
`TM = L ⊕ J L` in `L` is such an automorphism. This is how the first Chern number of a cotangent
bundle vanishes on spheres: along the zero section its tangent bundle is the complexification of the
tangent bundle of the base.

## Main definitions

* `Module.Basis.coordConjL`: the conjugation of the coordinates in a basis.

## Main results

* `Module.Basis.normalizedDet_coordConjL_trans_trans_coordConjL`: conjugating an automorphism by
  the conjugation of the coordinates inverts its normalized determinant.
* `TauCeti.clutchingNumber_eq_zero_of_conjugateLinear`,
  `TauCeti.clutchingNumberHom_eq_zero_of_conjugateLinear`: a complex vector bundle with a
  conjugation has vanishing clutching numbers.
* `TauCeti.Bundle.ContinuousComplexStructure.clutchingNumberHom_eq_zero_of_anticommute`: a complex
  structure on a real vector bundle with an anticommuting continuous automorphism has vanishing
  clutching numbers.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (the Chern classes of the conjugate bundle) and §15 (the complexification
  of a real vector bundle is isomorphic to its conjugate).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.2 (the canonical grading of the Floer
  homology of a cotangent bundle).
-/

public section

noncomputable section

open Bundle Set Module
open scoped unitInterval Topology.Homotopy ComplexConjugate

/-! ### The conjugation of a space in a basis -/

namespace Module.Basis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {ι : Type*} [Fintype ι] (b : Basis ι ℂ F)

/-- The **conjugation of the coordinates** in a basis `b` of a finite-dimensional complex normed
space, a conjugate-linear isomorphism. -/
def coordConjL : F ≃SL[starRingEnd ℂ] F :=
  b.equivFunL.trans ((starL ℂ : (ι → ℂ) ≃L⋆[ℂ] (ι → ℂ)).trans b.equivFunL.symm)

theorem coordConjL_apply (v : F) : b.coordConjL v = b.equivFun.symm (star (b.equivFun v)) :=
  (rfl)

@[simp]
theorem repr_coordConjL (v : F) (i : ι) : b.repr (b.coordConjL v) i = conj (b.repr v i) := by
  rw [← b.equivFun_apply, coordConjL_apply, LinearEquiv.apply_symm_apply, Pi.star_apply,
    b.equivFun_apply]
  rfl

/-- The conjugation of the coordinates fixes the basis vectors. -/
@[simp]
theorem coordConjL_self (i : ι) : b.coordConjL (b i) = b i := by
  classical
  refine b.ext_elem fun k ↦ ?_
  rw [repr_coordConjL, repr_self, Finsupp.single_apply]
  split_ifs <;> simp

/-- The conjugation of the coordinates is an involution. -/
@[simp]
theorem coordConjL_coordConjL (v : F) : b.coordConjL (b.coordConjL v) = v :=
  b.ext_elem fun i ↦ by simp

/-- **Conjugating an automorphism by the conjugation of the coordinates conjugates its
determinant**: the matrix of `κ ∘ A ∘ κ` in the basis is the complex conjugate of the matrix of
`A`. -/
theorem det_coordConjL_trans_trans_coordConjL (A : F ≃L[ℂ] F) :
    LinearMap.det ((b.coordConjL.trans (A.trans b.coordConjL) : F ≃L[ℂ] F).toLinearEquiv :
        F →ₗ[ℂ] F) =
      conj (LinearMap.det (A.toLinearEquiv : F →ₗ[ℂ] F)) := by
  classical
  have hM : LinearMap.toMatrix b b
      ((b.coordConjL.trans (A.trans b.coordConjL) : F ≃L[ℂ] F).toLinearEquiv : F →ₗ[ℂ] F) =
        (starRingEnd ℂ).mapMatrix (LinearMap.toMatrix b b (A.toLinearEquiv : F →ₗ[ℂ] F)) := by
    ext i j
    simp [LinearMap.toMatrix_apply]
  rw [← LinearMap.det_toMatrix b, hM, ← RingHom.map_det, LinearMap.det_toMatrix]

/-- **Conjugating an automorphism by the conjugation of the coordinates inverts its normalized
determinant**, since complex conjugation inverts points of the circle. -/
theorem normalizedDet_coordConjL_trans_trans_coordConjL (A : F ≃L[ℂ] F) :
    (b.coordConjL.trans (A.trans b.coordConjL) : F ≃L[ℂ] F).normalizedDet =
      A.normalizedDet⁻¹ := by
  ext1
  rw [Circle.coe_inv_eq_conj, ContinuousLinearEquiv.coe_normalizedDet,
    ContinuousLinearEquiv.coe_normalizedDet, det_coordConjL_trans_trans_coordConjL,
    Complex.norm_conj, map_div₀, Complex.conj_ofReal]

end Module.Basis

namespace TauCeti

/-! ### Vanishing of clutching numbers -/

section Clutching

variable {X : Type*} [TopologicalSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)] {x : X}

/-- The finite-dimensional model fibre is complete, as `TauCeti.exists_continuous_frame` needs. -/
private local instance : CompleteSpace F := FiniteDimensional.completeSpace ℂ F

/-- The automorphism `κ ∘ e⁻¹ ∘ c ∘ e` of the model fibre, read at a point `b` of the base set of a
trivialization `e`, and the identity elsewhere. -/
private def conjCoordinate (c : ∀ x, E x ≃SL[starRingEnd ℂ] E x) (κ : F ≃SL[starRingEnd ℂ] F)
    (e : Trivialization F (π F E)) [e.IsLinear ℂ] (b : X) : F ≃L[ℂ] F :=
  open Classical in
  if hb : b ∈ e.baseSet then
    κ.trans ((e.continuousLinearEquivAt ℂ b hb).symm.trans
      ((c b).trans (e.continuousLinearEquivAt ℂ b hb)))
  else ContinuousLinearEquiv.refl ℂ F

/-- **A complex vector bundle with a conjugation has vanishing clutching numbers.** If `E` carries
a family of conjugate-linear automorphisms `c x : E x ≃ E x`, continuous on the total space, then
the clutching number of every sphere `p` based at `x` is `0`. -/
theorem clutchingNumber_eq_zero_of_conjugateLinear (c : ∀ x, E x ≃SL[starRingEnd ℂ] E x)
    (hc : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F v.proj (c v.proj v.snd))
    (p : Ω^ (Fin 2) X x) : clutchingNumber F E p = 0 := by
  obtain ⟨φ, hφ⟩ := exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous p)
  let κ := (Module.finBasis ℂ F).coordConjL
  -- The conjugate frame `ψ y = c ∘ φ y ∘ κ`, again complex-linear and continuous.
  let ψ : ∀ y, F ≃L[ℂ] E (p y) := fun y ↦ κ.trans ((φ y).trans (c (p y)))
  have hψ : Continuous fun q : (Fin 2 → I) × F ↦ TotalSpace.mk' F (p q.1) (ψ q.1 q.2) :=
    hc.comp (hφ.comp (continuous_fst.prodMk (κ.continuous.comp continuous_snd)))
  set e := trivializationAt F E x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F E x
  have hcφ := continuousOn_clutchingFunction_boundary p hφ e hx
  -- On the boundary, the clutching function of `ψ` is the inverse of that of `φ`, times the
  -- constant `κ ∘ e⁻¹ ∘ c ∘ e` at the base point.
  have heq : EqOn (clutchingFunction p ψ e)
      ((clutchingFunction p φ e)⁻¹ * fun _ ↦ (conjCoordinate c κ e x).normalizedDet⁻¹)
      (Cube.boundary (Fin 2)) := by
    intro y hy
    have hy' : p y ∈ e.baseSet := mem_of_eq_of_mem (GenLoop.boundary p y hy) hx
    have hsplit : (ψ y).trans (e.continuousLinearEquivAt ℂ (p y) hy') =
        (κ.trans (((φ y).trans (e.continuousLinearEquivAt ℂ (p y) hy')).trans κ) :
          F ≃L[ℂ] F).trans (conjCoordinate c κ e (p y)) := by
      ext v
      simp [ψ, conjCoordinate, hy', κ]
    rw [clutchingFunction_of_mem hy', hsplit, ContinuousLinearEquiv.normalizedDet_trans,
      Module.Basis.normalizedDet_coordConjL_trans_trans_coordConjL, Pi.mul_apply, Pi.inv_apply,
      clutchingFunction_of_mem hy',
      show conjCoordinate c κ e (p y) = conjCoordinate c κ e x by rw [GenLoop.boundary p y hy],
      mul_inv, inv_inv]
  have h := clutchingNumber_eq_squareBoundaryDegree p e hx hψ
  rw [squareBoundaryDegree_congr heq, squareBoundaryDegree_mul hcφ.inv continuousOn_const,
    squareBoundaryDegree_inv, squareBoundaryDegree_const, add_zero,
    ← clutchingNumber_eq_squareBoundaryDegree p e hx hφ] at h
  omega

variable (F E) in
/-- **A complex vector bundle with a conjugation has vanishing clutching numbers**: the clutching
number homomorphism `π₂(X, x) → ℤ` is zero. -/
theorem clutchingNumberHom_eq_zero_of_conjugateLinear (c : ∀ x, E x ≃SL[starRingEnd ℂ] E x)
    (hc : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F v.proj (c v.proj v.snd)) (x : X) :
    clutchingNumberHom F E x = 0 := by
  ext a
  induction a using Additive.rec with
  | ofMul a =>
    induction a using Quotient.inductionOn with
    | h p =>
      exact (clutchingNumberHom_apply_mk (F := F) (E := E) p).trans
        (clutchingNumber_eq_zero_of_conjugateLinear c hc p)

end Clutching

/-! ### Complex structures with an anticommuting automorphism -/

section ComplexStructure

variable {X : Type*} [TopologicalSpace X]
  {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [FiniteDimensional ℝ F₀]
  {V : X → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F₀ V)] [FiberBundle F₀ V] [VectorBundle ℝ F₀ V]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [Fact (finrank ℝ F₀ = 2 * finrank ℂ F)]

namespace Bundle.ContinuousComplexStructure

variable (J : Bundle.ContinuousComplexStructure F₀ V)

/-- An automorphism `c` of `V b` anticommuting with `J b` is conjugate-linear on `J.Fiber b`. -/
private def conjOfAnticommute (c : ∀ x, V x ≃L[ℝ] V x)
    (hc : ∀ x v, c x (J x v) = -J x (c x v)) (b : X) : J.Fiber b ≃SL[starRingEnd ℂ] J.Fiber b where
  toFun v := (J.fiberEquiv b).symm (c b (J.fiberEquiv b v))
  invFun v := (J.fiberEquiv b).symm ((c b).symm (J.fiberEquiv b v))
  map_add' v w := by simp only [map_add]
  map_smul' z v := by
    -- `z • v = re z • v + im z • J v`, and `c` commutes with `re z` and anticommutes with `J`.
    apply (J.fiberEquiv b).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, fiberEquiv_smul, fiberEquiv_smul,
      ContinuousLinearEquiv.apply_symm_apply, map_add, map_smul, map_smul, hc, Complex.conj_re,
      Complex.conj_im, neg_smul, smul_neg]
  left_inv v := by simp
  right_inv v := by simp
  continuous_toFun := (J.fiberEquiv b).symm.continuous.comp
    ((c b).continuous.comp (J.fiberEquiv b).continuous)
  continuous_invFun := (J.fiberEquiv b).symm.continuous.comp
    ((c b).symm.continuous.comp (J.fiberEquiv b).continuous)

/-- **A complex structure with an anticommuting automorphism has vanishing clutching numbers.**
If a continuous family of automorphisms `c x` of the real vector bundle `V`, continuous on the
total space, anticommutes with the complex structure `J`, `c ∘ J = -J ∘ c`, then the complex vector
bundle `J.Fiber` has vanishing clutching numbers: `c` is a conjugation of it. -/
theorem clutchingNumberHom_eq_zero_of_anticommute (c : ∀ x, V x ≃L[ℝ] V x)
    (hc : ∀ x v, c x (J x v) = -J x (c x v))
    (hcont : Continuous fun v : TotalSpace F₀ V ↦ TotalSpace.mk' F₀ v.proj (c v.proj v.snd))
    (x : X) : clutchingNumberHom F J.Fiber x = 0 := by
  refine clutchingNumberHom_eq_zero_of_conjugateLinear F J.Fiber (J.conjOfAnticommute c hc)
    ((((J.totalSpaceHomeomorph F).symm.continuous.comp hcont).comp
      (J.totalSpaceHomeomorph F).continuous).congr fun v ↦ ?_) x
  simp [conjOfAnticommute]

end Bundle.ContinuousComplexStructure

end ComplexStructure

end TauCeti
