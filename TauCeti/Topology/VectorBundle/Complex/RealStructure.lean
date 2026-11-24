/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Complex.Clutching
public import TauCeti.Topology.VectorBundle.Complexification

/-!
# Clutching numbers of complex vector bundles with a real structure

A complex vector bundle `E` over `X` has a **real structure** if it carries a continuous map of
total spaces covering the identity of `X` that is a conjugate-linear automorphism `κ x` of each
fibre, for instance the conjugation `z ⊗ v ↦ conj z ⊗ v` of the complexification `ℂ ⊗[ℝ] V` of a
real vector bundle `V`. Such a bundle is isomorphic to its own conjugate, whose first Chern number
is the negative of that of `E`, so its first Chern number vanishes on every sphere. This file proves
this for the clutching number of `TauCeti.Topology.VectorBundle.Complex.Clutching`
(`TauCeti.clutchingNumber_eq_zero_of_conjugateLinear`,
`TauCeti.clutchingNumberHom_eq_zero_of_conjugateLinear`), and in particular for the
complexification of a real vector bundle (`TauCeti.clutchingNumber_complexification_eq_zero`,
`TauCeti.clutchingNumberHom_complexification_eq_zero`).

The proof compares two frames along a sphere `p : I² → X` based at `x`. If `φ` is a frame of `E`
along `p` and `e` a trivialization near `x`, read `κ x` in `e` as a conjugate-linear automorphism
`K` of the model fibre and put `ψ y = κ ∘ φ y ∘ K⁻¹`, again a continuous complex-linear frame. On
the boundary of the square `p` is the base point, so the transition `e ∘ ψ y` of the new frame is
the conjugate `K ∘ (e ∘ φ y) ∘ K⁻¹` of the old one by `K`. Conjugation by a conjugate-linear
automorphism conjugates determinants (`LinearMap.det_conjₛₗ`), so the clutching function of `ψ` is
the inverse of that of `φ` on the boundary, and its degree is the negative one
(`TauCeti.squareBoundaryDegree_inv`). Both frames compute the clutching number, which is therefore
equal to its negative.

For example, along the zero section the tangent bundle of a cotangent bundle `T*Q` is the
complexification `TQ ⊗ ℂ` of `TQ`, so its first Chern number vanishes on spheres there; this is the
Chern half of the symplectic asphericity of cotangent bundles used in Floer theory.

## Main results

* `TauCeti.clutchingNumber_eq_zero_of_conjugateLinear`: a complex vector bundle with a real
  structure has clutching number `0` on every sphere.
* `TauCeti.clutchingNumberHom_eq_zero_of_conjugateLinear`: its clutching number homomorphism
  `π₂(X, x) → ℤ` vanishes.
* `TauCeti.clutchingNumber_complexification_eq_zero`,
  `TauCeti.clutchingNumberHom_complexification_eq_zero`: the same for the complexification of a
  finite-rank real vector bundle.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14, Lemma 14.9 (the first Chern class of the conjugate bundle is the negative
  one), and §15 (a complexified real bundle is isomorphic to its own conjugate, so its odd Chern
  classes, in particular `c₁`, are of order at most two).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.2 (the canonical grading of the Floer
  homology of `T*Q`).
-/

public section

noncomputable section

open Bundle Set Topology
open scoped unitInterval Topology.Homotopy TensorProduct

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)] {x : X}

/-- **A complex vector bundle with a real structure has clutching number zero.** If `κ x` is a
conjugate-linear automorphism of each fibre `E x`, continuous as a map of total spaces, then the
clutching number of `E` vanishes on every sphere. -/
theorem clutchingNumber_eq_zero_of_conjugateLinear (κ : ∀ x, E x ≃L⋆[ℂ] E x)
    (hκ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F v.proj (κ v.proj v.snd))
    (p : Ω^ (Fin 2) X x) : clutchingNumber F E p = 0 := by
  have : CompleteSpace F := FiniteDimensional.completeSpace ℂ F
  obtain ⟨φ, hφ⟩ := exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous p)
  set e := trivializationAt F E x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F E x
  -- The conjugate-linear automorphism of `F` that `κ` induces at `x` through `e`.
  let K : F ≃L⋆[ℂ] F :=
    ((e.continuousLinearEquivAt ℂ x hx).symm.trans (κ x)).trans (e.continuousLinearEquivAt ℂ x hx)
  have hK (z : X) (hz : z ∈ e.baseSet) (hzx : z = x) (v : E z) :
      e.continuousLinearEquivAt ℂ z hz (κ z v) = K (e.continuousLinearEquivAt ℂ z hz v) := by
    subst hzx
    simp [K, e.symm_apply_apply_mk hz]
  -- The conjugate frame `κ ∘ φ ∘ K⁻¹`.
  let ψ (y : Fin 2 → I) : F ≃L[ℂ] E (p y) := (K.symm.trans (φ y)).trans (κ (p y))
  have hψ : Continuous fun q : (Fin 2 → I) × F ↦ TotalSpace.mk' F (p q.1) (ψ q.1 q.2) :=
    hκ.comp (hφ.comp (continuous_fst.prodMk (K.symm.continuous.comp continuous_snd)))
  -- On the boundary, the clutching function of the conjugate frame is the inverse of that of `φ`.
  have heq :
      EqOn (clutchingFunction p ψ e) (clutchingFunction p φ e)⁻¹ (Cube.boundary (Fin 2)) := by
    intro y hy
    have hy' : p y ∈ e.baseSet := mem_of_eq_of_mem (GenLoop.boundary p y hy) hx
    have h : (ψ y).trans (e.continuousLinearEquivAt ℂ (p y) hy') =
        (K.symm.trans ((φ y).trans (e.continuousLinearEquivAt ℂ (p y) hy'))).trans K := by
      ext v
      simp [ψ, hK (p y) hy' (GenLoop.boundary p y hy)]
    rw [Pi.inv_apply, clutchingFunction_of_mem hy', clutchingFunction_of_mem hy', h,
      ContinuousLinearEquiv.normalizedDet_conjₛₗ]
  have h₁ := clutchingNumber_eq_squareBoundaryDegree p e hx hφ
  have h₂ := clutchingNumber_eq_squareBoundaryDegree p e hx hψ
  rw [squareBoundaryDegree_congr heq, squareBoundaryDegree_inv, ← h₁] at h₂
  omega

/-- The clutching number homomorphism `π₂(X, x) → ℤ` of a complex vector bundle with a real
structure is zero. -/
theorem clutchingNumberHom_eq_zero_of_conjugateLinear (κ : ∀ x, E x ≃L⋆[ℂ] E x)
    (hκ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F v.proj (κ v.proj v.snd)) (x : X) :
    clutchingNumberHom F E x = 0 := by
  refine AddMonoidHom.ext fun a ↦ ?_
  obtain ⟨p, hp⟩ := Quotient.exists_rep a.toMul
  rw [← ofMul_toMul a, ← hp, clutchingNumberHom_apply_mk,
    clutchingNumber_eq_zero_of_conjugateLinear κ hκ, AddMonoidHom.zero_apply]

section Complexification

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {V : X → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace G V)] [FiberBundle G V] [VectorBundle ℝ G V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] V x)] [∀ x, IsComplexificationTopology (V x)]

/-- **The complexification of a real vector bundle has clutching number zero.** The fibrewise
conjugation `z ⊗ v ↦ conj z ⊗ v` is a real structure on `ℂ ⊗[ℝ] V`. -/
@[simp]
theorem clutchingNumber_complexification_eq_zero (p : Ω^ (Fin 2) X x) :
    clutchingNumber (Complexification G) (fun x ↦ ℂ ⊗[ℝ] V x) p = 0 :=
  clutchingNumber_eq_zero_of_conjugateLinear (fun x ↦ tmulConjCLE (V x))
    ((tmulConjHomeomorph G V).continuous.congr fun v ↦ by simp) p

/-- The clutching number homomorphism `π₂(X, x) → ℤ` of the complexification of a real vector bundle
is zero. -/
@[simp]
theorem clutchingNumberHom_complexification_eq_zero (x : X) :
    clutchingNumberHom (Complexification G) (fun x ↦ ℂ ⊗[ℝ] V x) x = 0 :=
  clutchingNumberHom_eq_zero_of_conjugateLinear (fun x ↦ tmulConjCLE (V x))
    ((tmulConjHomeomorph G V).continuous.congr fun v ↦ by simp) x

end Complexification

end TauCeti
