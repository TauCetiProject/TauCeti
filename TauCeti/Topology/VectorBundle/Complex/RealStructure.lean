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

Both follow from the behaviour of clutching numbers under conjugate-linear bundle maps. Let
`Φ x : E x ≃ E' (f x)` be conjugate-linear isomorphisms covering a continuous map `f : X → Y`,
continuous on total spaces. Then `E'` on `f ∘ p` has the negative of the clutching number of `E` on
`p` (`TauCeti.clutchingNumber_map_of_conjugateLinear`); a real structure is the case `f = id`,
`E' = E`, in which the clutching number is its own negative. The proof compares two frames. If `φ`
is a frame of `E` along a sphere `p : I² → X` based at `x`, and `e`, `e'` are trivializations near
`x` and `f x`, read `Φ x` in `e` and `e'` as a conjugate-linear isomorphism `K` of the model fibres
and put `ψ y = Φ ∘ φ y ∘ K⁻¹`, a continuous complex-linear frame of `E'` along `f ∘ p`. On the
boundary of the square `p` is the base point, so the transition `e' ∘ ψ y` of the new frame is the
conjugate `K ∘ (e ∘ φ y) ∘ K⁻¹` of the old one by `K`. Conjugation by a conjugate-linear
isomorphism conjugates determinants (`LinearMap.det_conjₛₗ`), so the clutching function of `ψ` is
the inverse of that of `φ` on the boundary, and its degree is the negative one
(`TauCeti.squareBoundaryDegree_inv`).

For example, along the zero section the tangent bundle of a cotangent bundle `T*Q` is the
complexification `TQ ⊗ ℂ` of `TQ`, so its first Chern number vanishes on spheres there; this is the
Chern half of the symplectic asphericity of cotangent bundles used in Floer theory. The vanishing on
all of `T*Q` is proved instead with the anti-symplectic fibre negation, a conjugate-linear map of
tangent bundles covering a map homotopic to the identity
(`TauCeti.CotangentBundle.firstChernHom_symplecticForm_eq_zero`).

## Main results

* `TauCeti.clutchingNumber_map_of_conjugateLinear`,
  `TauCeti.clutchingNumberHom_map_of_conjugateLinear`: a conjugate-linear bundle map covering a map
  of the bases reverses clutching numbers.
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

/-- The finite-dimensional model fibre is complete, as `TauCeti.exists_continuous_frame` needs. -/
private local instance : CompleteSpace F := FiniteDimensional.completeSpace ℂ F

section Map

variable {Y : Type*} [TopologicalSpace Y] {y : Y}
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F'] [FiniteDimensional ℂ F']
  {E' : Y → Type*} [∀ y, AddCommGroup (E' y)] [∀ y, Module ℂ (E' y)]
  [∀ y, TopologicalSpace (E' y)] [TopologicalSpace (TotalSpace F' E')] [FiberBundle F' E']
  [VectorBundle ℂ F' E'] [∀ y, IsTopologicalAddGroup (E' y)] [∀ y, ContinuousSMul ℂ (E' y)]

/-- **Conjugate-linear bundle maps reverse clutching numbers.** Let `f : X → Y` be continuous and
let `Φ x : E x ≃ E' (f x)` be a family of conjugate-linear isomorphisms, continuous as a map of
total spaces covering `f`. Then the clutching number of `E'` on the image `f ∘ p` of a sphere `p` is
the negative of the clutching number of `E` on `p`. The model fibres `F` and `F'` may differ. -/
theorem clutchingNumber_map_of_conjugateLinear (f : C(X, Y)) (Φ : ∀ x, E x ≃L⋆[ℂ] E' (f x))
    (hΦ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F' (f v.proj) (Φ v.proj v.snd))
    (hfx : f x = y) (p : Ω^ (Fin 2) X x) :
    clutchingNumber F' E' (GenLoop.map f hfx p) = -clutchingNumber F E p := by
  subst hfx
  obtain ⟨φ, hφ⟩ := exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous p)
  set e := trivializationAt F E x
  set e' := trivializationAt F' E' (f x)
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F E x
  have hx' : f x ∈ e'.baseSet := mem_baseSet_trivializationAt F' E' (f x)
  -- The conjugate-linear isomorphism `F ≃ F'` that `Φ` induces at `x` through `e` and `e'`.
  let K : F ≃L⋆[ℂ] F' :=
    ((e.continuousLinearEquivAt ℂ x hx).symm.trans (Φ x)).trans
      (e'.continuousLinearEquivAt ℂ (f x) hx')
  have hK (z : X) (hz : z ∈ e.baseSet) (hz' : f z ∈ e'.baseSet) (hzx : z = x) (v : E z) :
      e'.continuousLinearEquivAt ℂ (f z) hz' (Φ z v) = K (e.continuousLinearEquivAt ℂ z hz v) := by
    subst hzx
    simp [K, e.symm_apply_apply_mk hz]
  -- The frame `Φ ∘ φ ∘ K⁻¹` of `E'` along `f ∘ p`.
  let ψ (z : Fin 2 → I) : F' ≃L[ℂ] E' (f (p z)) := (K.symm.trans (φ z)).trans (Φ (p z))
  have hψ : Continuous fun q : (Fin 2 → I) × F' ↦ TotalSpace.mk' F' (f (p q.1)) (ψ q.1 q.2) :=
    hΦ.comp (hφ.comp (continuous_fst.prodMk (K.symm.continuous.comp continuous_snd)))
  -- On the boundary, the clutching function of `ψ` is the inverse of that of `φ`.
  have heq :
      EqOn (clutchingFunction (fun z ↦ f (p z)) ψ e') (clutchingFunction p φ e)⁻¹
        (Cube.boundary (Fin 2)) := by
    intro z hz
    have hpz : p z = x := GenLoop.boundary p z hz
    have h : p z ∈ e.baseSet := mem_of_eq_of_mem hpz hx
    have h' : f (p z) ∈ e'.baseSet := mem_of_eq_of_mem (congrArg f hpz) hx'
    have hc : (ψ z).trans (e'.continuousLinearEquivAt ℂ (f (p z)) h') =
        (K.symm.trans ((φ z).trans (e.continuousLinearEquivAt ℂ (p z) h))).trans K := by
      ext v
      simp [ψ, hK (p z) h h' hpz]
    rw [Pi.inv_apply, clutchingFunction_of_mem (f := fun z ↦ f (p z)) h',
      clutchingFunction_of_mem h, hc, ContinuousLinearEquiv.normalizedDet_conjₛₗ]
  have h₁ := clutchingNumber_eq_squareBoundaryDegree p e hx hφ
  have h₂ := clutchingNumber_map_eq_squareBoundaryDegree f rfl p e' hx' hψ
  rw [squareBoundaryDegree_congr heq, squareBoundaryDegree_inv, ← h₁] at h₂
  exact h₂

/-- **Conjugate-linear bundle maps reverse clutching number homomorphisms.** For a family of
conjugate-linear isomorphisms `Φ x : E x ≃ E' (f x)` continuous on total spaces and covering a
continuous map `f : X → Y`, the clutching number of `E'` on the image `f_* a ∈ π₂(Y, f x)` of a
class `a ∈ π₂(X, x)` is the negative of the clutching number of `E` on `a`. -/
theorem clutchingNumberHom_map_of_conjugateLinear (f : C(X, Y)) (Φ : ∀ x, E x ≃L⋆[ℂ] E' (f x))
    (hΦ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F' (f v.proj) (Φ v.proj v.snd))
    (hfx : f x = y) (a : π_ 2 X x) :
    clutchingNumberHom F' E' y (.ofMul (HomotopyGroup.map f hfx a)) =
      -clutchingNumberHom F E x (.ofMul a) := by
  induction a using Quotient.inductionOn with
  | h p =>
    rw [HomotopyGroup.map_mk, clutchingNumberHom_apply_mk, clutchingNumberHom_apply_mk,
      clutchingNumber_map_of_conjugateLinear f Φ hΦ hfx p]

end Map

/-- **A complex vector bundle with a real structure has clutching number zero.** If `κ x` is a
conjugate-linear automorphism of each fibre `E x`, continuous as a map of total spaces, then the
clutching number of `E` vanishes on every sphere. -/
theorem clutchingNumber_eq_zero_of_conjugateLinear (κ : ∀ x, E x ≃L⋆[ℂ] E x)
    (hκ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F v.proj (κ v.proj v.snd))
    (p : Ω^ (Fin 2) X x) : clutchingNumber F E p = 0 := by
  have h : clutchingNumber F E p = -clutchingNumber F E p := by
    have h := clutchingNumber_map_of_conjugateLinear (ContinuousMap.id X) κ hκ rfl p
    rwa [GenLoop.map_id] at h
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
