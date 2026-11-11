/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.DeterminantLoop
public import TauCeti.Topology.VectorBundle.HomotopyInvariance
public import TauCeti.Topology.Circle.Degree
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Topology.Path.Map

/-!
# The clutching first Chern number of a based sphere

Let `E` be a complex vector bundle over a space `X`, with finite-dimensional model fibre `F`, and
let `γ : Ω^ (Fin 2) X x` be a based sphere: a map of the square `I²` sending its boundary to `x`,
so a map of the sphere `I² / ∂I²`. This file defines the first Chern number of the pullback of `E`
along `γ` by clutching, and shows that it is a homomorphism on `π₂(X, x)`.

The pullback of `E` to the contractible square is trivial. Concretely, `γ` contracts to the
constant map at `x` by shrinking the square to its corner, and homotopy invariance of vector
bundles (`ContinuousMap.Homotopic.exists_continuousLinearEquiv_pullback`) gives isomorphisms
`Φ y : E (γ y) ≃L[ℂ] E x`, continuous on total spaces with their inverses
(`TauCeti.IsPullbackTrivialization`, `TauCeti.exists_isPullbackTrivialization_genLoop`). They give
a frame of the pullback over the square, the disc of the sphere. Its complement is the collapsed
boundary, where the bundle has the constant frame of `E x`. Along the boundary, where `γ y = x`,
the transition `g y = e ∘ Φ y ∘ e⁻¹` expresses the complement frame in the disc frame
(`TauCeti.clutchingFunction`, read in the trivialization `e` of `E` at `x`). The **clutching Chern
number** `TauCeti.clutchingChernNumber F E γ` is the winding number of `det g` along the boundary
of the square, traversed counterclockwise for the orientation in which coordinate `0` comes first
(`TauCeti.squareBoundaryLoop`): the degree of the loop of phases `det g / ‖det g‖` in the circle
(`ContinuousLinearMap.detPhase`).

* It does not depend on the choice of `Φ` (`TauCeti.clutchingChernNumber_eq_degree`). Two
  choices differ by a continuous family of automorphisms of `E x` over the whole square, and the
  loop of their determinants along the boundary contracts through the square.
* It is invariant under homotopies of based spheres relative to the boundary
  (`TauCeti.clutchingChernNumber_eq_of_homotopic`). A homotopy contracts as a family, so a single
  family of frames gives a homotopy of the loops of determinants.
* It is additive under concatenation of spheres (`TauCeti.clutchingChernNumber_transAt`). Restrict
  a frame of the concatenation to the two halves of the square. The boundary loops of the halves
  run along the seam in opposite directions, so the angles swept by the determinant along the
  seam cancel. Their remaining pieces make up the boundary loop of the whole square.

Hence it descends to a homomorphism `π₂(X, x) →+ ℤ`
(`TauCeti.homotopyGroupClutchingChernNumber`). For the tangent bundle of a symplectic manifold
with a compatible almost complex structure this gives the first Chern numbers of spheres, which,
together with their symplectic areas, determine the classes of spheres used as exponents in the
Novikov ring of Hamiltonian Floer theory. This file does not compare the clutching number with the
first Chern class in cohomology, nor treat surfaces other than spheres.

## Main definitions

* `TauCeti.squareBoundaryLoop`: the counterclockwise boundary loop of the square.
* `TauCeti.clutchingFunction`: the clutching function over the square of an identification
  `TauCeti.IsPullbackTrivialization` of the pulled-back bundle with the trivial bundle with fibre
  `E x`.
* `TauCeti.clutchingChernNumber`: the clutching first Chern number of a based sphere.
* `TauCeti.homotopyGroupClutchingChernNumber`: the clutching first Chern number on `π₂(X, x)`.

## Main results

* `TauCeti.clutchingChernNumber_eq_degree`: the clutching number may be computed from any
  identification of the pulled-back bundle with the trivial bundle.
* `TauCeti.clutchingChernNumber_eq_of_homotopic`: homotopy invariance.
* `TauCeti.clutchingChernNumber_transAt`: additivity under concatenation.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.2 (clutching functions of vector bundles over
  spheres).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford Graduate
  Texts in Mathematics 27, Oxford University Press, 2017, Section 2.7 (the first Chern number of a
  symplectic vector bundle over a surface from the Maslov index of the transition loop).
-/

public section

noncomputable section

open Bundle Set Function Topology
open scoped unitInterval Topology.Homotopy

namespace TauCeti

/-! ### The boundary loop of the square -/

/-- The bottom edge `y 1 = 0` of the square, from `0` to `![1, 0]`. -/
private def squareEdge₀ : Path (0 : I^Fin 2) ![1, 0] where
  toFun t := ![t, 0]
  source' := by ext i; fin_cases i <;> rfl
  target' := rfl

/-- The right edge `y 0 = 1` of the square, from `![1, 0]` to `![1, 1]`. -/
private def squareEdge₁ : Path (![1, 0] : I^Fin 2) ![1, 1] where
  toFun t := ![1, t]
  source' := rfl
  target' := rfl

/-- The top edge `y 1 = 1` of the square, from `![1, 1]` to `![0, 1]`. -/
private def squareEdge₂ : Path (![1, 1] : I^Fin 2) ![0, 1] where
  toFun t := ![σ t, 1]
  source' := by simp
  target' := by simp

/-- The left edge `y 0 = 0` of the square, from `![0, 1]` to `0`. -/
private def squareEdge₃ : Path (![0, 1] : I^Fin 2) 0 where
  toFun t := ![0, σ t]
  source' := by simp
  target' := by ext i; fin_cases i <;> simp

/-- The loop running once around the boundary of the square `I^(Fin 2)`, counterclockwise for
the orientation in which coordinate `0` comes first: from the corner `0` along the edge
`y 1 = 0`, then up the edge `y 0 = 1`, back along the edge `y 1 = 1` and down the edge `y 0 = 0`. -/
def squareBoundaryLoop : Path (0 : I^Fin 2) 0 :=
  squareEdge₀.trans <| squareEdge₁.trans <| squareEdge₂.trans squareEdge₃

/-- The boundary loop of the square runs along the boundary. -/
theorem squareBoundaryLoop_mem_boundary (t : I) :
    squareBoundaryLoop t ∈ Cube.boundary (Fin 2) := by
  have h := mem_range_self (f := squareBoundaryLoop) t
  rw [squareBoundaryLoop, Path.trans_range, Path.trans_range, Path.trans_range] at h
  rcases h with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨r, hr⟩ <;> rw [squareBoundaryLoop, ← hr]
  · exact ⟨1, Or.inl rfl⟩
  · exact ⟨0, Or.inr rfl⟩
  · exact ⟨1, Or.inr rfl⟩
  · exact ⟨0, Or.inl rfl⟩

/-- The map of the square onto its left half `y 0 ≤ 1 / 2`, halving the coordinate `0`. -/
private def leftHalf (y : I^Fin 2) : I^Fin 2 :=
  ![Set.projIcc 0 1 zero_le_one ((y 0 : ℝ) / 2), y 1]

/-- The map of the square onto its right half `1 / 2 ≤ y 0`. -/
private def rightHalf (y : I^Fin 2) : I^Fin 2 :=
  ![Set.projIcc 0 1 zero_le_one (((y 0 : ℝ) + 1) / 2), y 1]

private theorem continuous_leftHalf : Continuous leftHalf := by
  unfold leftHalf
  fun_prop

private theorem continuous_rightHalf : Continuous rightHalf := by
  unfold rightHalf
  fun_prop

/-- The concatenation `transAt 0 q p` of based spheres along the coordinate `0` restricts to `q` on
the left half of the square. -/
private theorem transAt_leftHalf {X : Type*} [TopologicalSpace X] {x : X} (q p : Ω^ (Fin 2) X x)
    (y : I^Fin 2) : GenLoop.transAt 0 q p (leftHalf y) = q y := by
  have hy : ((y 0 : ℝ) / 2) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [(y 0).2.1], by linarith [(y 0).2.2]⟩
  simp only [GenLoop.transAt, GenLoop.coe_copy]
  split_ifs with h
  · congr 1
    ext j
    fin_cases j <;> simp [leftHalf, Set.projIcc_of_mem _ hy,
      show 2 * ((y 0 : ℝ) / 2) = y 0 by ring, Set.projIcc_of_mem _ (y 0).2]
  · simp [leftHalf, Set.projIcc_of_mem _ hy] at h
    linarith [(y 0).2.2]

/-- The concatenation `transAt 0 q p` of based spheres along the coordinate `0` restricts to `p` on
the right half of the square. -/
private theorem transAt_rightHalf {X : Type*} [TopologicalSpace X] {x : X} (q p : Ω^ (Fin 2) X x)
    (y : I^Fin 2) : GenLoop.transAt 0 q p (rightHalf y) = p y := by
  have hy : (((y 0 : ℝ) + 1) / 2) ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [(y 0).2.1], by linarith [(y 0).2.2]⟩
  simp only [GenLoop.transAt, GenLoop.coe_copy]
  split_ifs with h
  · -- On the seam `y 0 = 0` both sides take the base point value.
    simp only [rightHalf, Matrix.cons_val_zero, Set.projIcc_of_mem _ hy] at h
    have h0 : (y 0 : ℝ) = 0 := le_antisymm (by linarith) (y 0).2.1
    rw [GenLoop.boundary p y ⟨0, Or.inl (Subtype.ext h0)⟩]
    refine GenLoop.boundary q _ ⟨0, Or.inr ?_⟩
    simp [rightHalf, h0, Set.projIcc_of_mem _ (show (2⁻¹ : ℝ) ∈ Icc 0 1 by norm_num)]
  · congr 1
    ext j
    fin_cases j <;> simp [rightHalf, Set.projIcc_of_mem _ hy,
      show 2 * (((y 0 : ℝ) + 1) / 2) - 1 = y 0 by ring, Set.projIcc_of_mem _ (y 0).2]

/-! ### The clutching number -/

section Clutching

variable {X : Type*} [TopologicalSpace X] {x : X}
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle ℂ F E]

/-- The clutching function of a family `Φ y : E (f y) ≃L[ℂ] E x`, read in the trivialization `e`
of `E` at `x`: the operator `e ∘ Φ y ∘ e⁻¹` of the model fibre. Over the boundary of the square,
where a based sphere `f` takes the value `x`, it expresses the constant frame of `E x` in the frame
of `f *ᵖ E` given by `Φ`. -/
def clutchingFunction (f : (I^Fin 2) → X) (Φ : ∀ y, E (f y) ≃L[ℂ] E x) (y : I^Fin 2) :
    F →L[ℂ] F :=
  (trivializationAt F E x).continuousLinearMapAt ℂ x ∘L (Φ y : E (f y) →L[ℂ] E x) ∘L
    (trivializationAt F E x).symmL ℂ (f y)

variable {F}

/-- The clutching function sends `v` to `e (Φ y (e⁻¹ v))`, where `e` is the trivialization of `E`
at `x`, inverted over `f y` and applied over `x`. -/
theorem clutchingFunction_apply (f : (I^Fin 2) → X) (Φ : ∀ y, E (f y) ≃L[ℂ] E x) (y : I^Fin 2)
    (v : F) : clutchingFunction F f Φ y v = (trivializationAt F E x).continuousLinearMapAt ℂ x
      (Φ y ((trivializationAt F E x).symmL ℂ (f y) v)) := by
  simp only [clutchingFunction, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]

/-- The clutching function is invertible wherever `f y` lies in the base set of the trivialization
at `x`, in particular on the boundary of the square for a based sphere. -/
theorem det_clutchingFunction_ne_zero {f : (I^Fin 2) → X} (Φ : ∀ y, E (f y) ≃L[ℂ] E x)
    {y : I^Fin 2} (hy : f y ∈ (trivializationAt F E x).baseSet) :
    (clutchingFunction F f Φ y).det ≠ 0 := by
  have hx : x ∈ (trivializationAt F E x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have h : clutchingFunction F f Φ y =
      ((((trivializationAt F E x).continuousLinearEquivAt ℂ (f y) hy).symm.trans
        ((Φ y).trans ((trivializationAt F E x).continuousLinearEquivAt ℂ x hx))) : F →L[ℂ] F) := by
    ext v
    rw [clutchingFunction_apply, (trivializationAt F E x).symmL_apply hy,
      (trivializationAt F E x).continuousLinearMapAt_apply_of_mem ℂ hx]
    rfl
  rw [h]
  exact (LinearEquiv.isUnit_det' _).ne_zero

/-- On the boundary loop of the square, the clutching function of a based sphere is invertible. -/
theorem det_clutchingFunction_squareBoundaryLoop_ne_zero (γ : Ω^ (Fin 2) X x)
    (Φ : ∀ y, E (γ y) ≃L[ℂ] E x) (t : I) :
    (clutchingFunction F γ Φ (squareBoundaryLoop t)).det ≠ 0 :=
  det_clutchingFunction_ne_zero Φ <| by
    rw [GenLoop.boundary γ _ (squareBoundaryLoop_mem_boundary t)]
    exact FiberBundle.mem_baseSet_trivializationAt' x

/-- A loop of phases of determinants of invertible operators which extend continuously over the
square has degree zero: it contracts through the square to its corner. -/
private theorem degree_eq_zero_of_continuous {A : (I^Fin 2) → F →L[ℂ] F} (hA : Continuous A)
    (hdet : ∀ y, (A y).det ≠ 0) {c : Circle} (δ : Path c c)
    (hδ : ∀ t, δ t = (A (squareBoundaryLoop t)).detPhase) : Circle.degree δ = 0 := by
  let G : C(I × I, Circle) :=
    ⟨fun p ↦ (A fun i ↦ σ p.1 * squareBoundaryLoop p.2 i).detPhase,
      ContinuousLinearMap.continuous_detPhase (hA.comp (by fun_prop)) fun _ ↦ hdet _⟩
  refine (Circle.degree_eq_of_homotopy δ (Path.refl (A 0).detPhase) G
    (fun t ↦ ?_) (fun t ↦ ?_) (fun s ↦ ?_)).trans (Circle.degree_refl _)
  · simp only [G, ContinuousMap.coe_mk, unitInterval.symm_zero, one_mul, hδ]
  · simp only [G, ContinuousMap.coe_mk, unitInterval.symm_one, zero_mul, Path.refl_apply]
    rfl
  · simp only [G, ContinuousMap.coe_mk, Path.source, Path.target]

variable [FiniteDimensional ℂ F]

/-- The loop of phases of the determinant of the clutching function along the boundary of the
square. -/
private def clutchingLoop (γ : Ω^ (Fin 2) X x) {Φ : ∀ y, E (γ y) ≃L[ℂ] E x}
    (hΦ : IsPullbackTrivialization F γ x Φ) :
    Path (clutchingFunction F γ Φ (squareBoundaryLoop 0)).detPhase
      (clutchingFunction F γ Φ (squareBoundaryLoop 0)).detPhase where
  toFun t := (clutchingFunction F γ Φ (squareBoundaryLoop t)).detPhase
  continuous_toFun := by
    refine ContinuousLinearMap.continuous_detPhase ?_
      (det_clutchingFunction_squareBoundaryLoop_ne_zero γ Φ)
    refine (hΦ.continuousOn_coord γ.1.continuous).comp_continuous squareBoundaryLoop.continuous
      fun t ↦ ?_
    rw [mem_preimage, GenLoop.boundary γ _ (squareBoundaryLoop_mem_boundary t)]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  source' := rfl
  target' := by simp only [Path.target, Path.source]

private theorem clutchingLoop_apply (γ : Ω^ (Fin 2) X x) {Φ : ∀ y, E (γ y) ≃L[ℂ] E x}
    (hΦ : IsPullbackTrivialization F γ x Φ) (t : I) :
    clutchingLoop γ hΦ t = (clutchingFunction F γ Φ (squareBoundaryLoop t)).detPhase :=
  rfl

/-- The degree of the clutching loop does not depend on the pullback trivialization: two
trivializations differ by a continuous family of automorphisms of `E x` over the whole square,
whose loop of determinants along the boundary contracts. -/
private theorem degree_clutchingLoop_eq (γ : Ω^ (Fin 2) X x) {Φ Ψ : ∀ y, E (γ y) ≃L[ℂ] E x}
    (hΦ : IsPullbackTrivialization F γ x Φ) (hΨ : IsPullbackTrivialization F γ x Ψ) :
    Circle.degree (clutchingLoop γ hΨ) = Circle.degree (clutchingLoop γ hΦ) := by
  have hx : x ∈ (trivializationAt F E x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  -- The transition from `Φ` to `Ψ`, read in the trivialization at `x`.
  let A : (I^Fin 2) → F →L[ℂ] F := fun y ↦
    (trivializationAt F E x).continuousLinearMapAt ℂ x ∘L (Ψ y : E (γ y) →L[ℂ] E x) ∘L
      ((Φ y).symm : E x →L[ℂ] E (γ y)) ∘L (trivializationAt F E x).symmL ℂ x
  have hA : Continuous A := hΦ.continuous_coord_trans hΨ
  have hAe (y : I^Fin 2) : A y =
      ((((trivializationAt F E x).continuousLinearEquivAt ℂ x hx).symm.trans
        (((Φ y).symm.trans (Ψ y)).trans
          ((trivializationAt F E x).continuousLinearEquivAt ℂ x hx))) : F →L[ℂ] F) := by
    ext v
    simp only [A, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      (trivializationAt F E x).symmL_apply hx,
      (trivializationAt F E x).continuousLinearMapAt_apply_of_mem ℂ hx]
    rfl
  have hdet (y : I^Fin 2) : (A y).det ≠ 0 := by
    rw [hAe]
    exact (LinearEquiv.isUnit_det' _).ne_zero
  have hcomp (y : I^Fin 2) :
      clutchingFunction F γ Ψ y = A y ∘L clutchingFunction F γ Φ y := by
    ext v
    simp only [clutchingFunction_apply, A, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe]
    rw [(trivializationAt F E x).symmL_continuousLinearMapAt hx,
      ContinuousLinearEquiv.symm_apply_apply]
  let δ : Path (A (squareBoundaryLoop 0)).detPhase (A (squareBoundaryLoop 0)).detPhase :=
    { toFun := fun t ↦ (A (squareBoundaryLoop t)).detPhase
      continuous_toFun := ContinuousLinearMap.continuous_detPhase
        (hA.comp squareBoundaryLoop.continuous) fun _ ↦ hdet _
      source' := rfl
      target' := by simp only [Path.source, Path.target] }
  have hδ : Circle.degree δ = 0 := degree_eq_zero_of_continuous hA hdet δ fun _ ↦ rfl
  rw [← zero_add (Circle.degree (clutchingLoop γ hΦ)), ← hδ, ← Circle.degree_mul]
  refine Circle.degree_congr _ _ fun t ↦ ?_
  rw [Path.mul_apply, clutchingLoop_apply, clutchingLoop_apply, hcomp]
  exact ContinuousLinearMap.detPhase_comp (hdet _)
    (det_clutchingFunction_squareBoundaryLoop_ne_zero γ Φ t)

variable [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)]

/-- `exists_isPullbackTrivialization_genLoop` for the finite-dimensional, hence complete, model
fibre `F`. -/
private theorem exists_isPullbackTrivialization (γ : Ω^ (Fin 2) X x) :
    ∃ Φ : ∀ y, E (γ y) ≃L[ℂ] E x, IsPullbackTrivialization F γ x Φ :=
  have := FiniteDimensional.complete ℂ F
  exists_isPullbackTrivialization_genLoop γ

variable (F E) in
/-- The **clutching first Chern number** of a based sphere `γ` in `X` for the complex vector
bundle `E`. Choose an identification `Φ y : E (γ y) ≃L[ℂ] E x` of the pulled-back bundle over the
square with the trivial bundle with fibre `E x`. Over the boundary of the square, where `γ` takes
the value `x`, the clutching function `clutchingFunction F γ Φ` expresses the constant frame of
`E x` in the frame given by `Φ`, and the clutching number is the degree of the loop of phases
`det g / ‖det g‖` of its determinant along the counterclockwise boundary loop
`squareBoundaryLoop`. It does not depend on `Φ` (`clutchingChernNumber_eq_degree`). -/
def clutchingChernNumber (γ : Ω^ (Fin 2) X x) : ℤ :=
  Circle.degree (clutchingLoop γ (exists_isPullbackTrivialization (F := F) (E := E) γ).choose_spec)

/-- **Independence of the trivialization.** The clutching Chern number of a based sphere `γ` is
the degree of the loop of phases `det g / ‖det g‖` of the clutching function `g` of any pullback
trivialization `Φ`, along the boundary of the square. -/
theorem clutchingChernNumber_eq_degree (γ : Ω^ (Fin 2) X x) {Φ : ∀ y, E (γ y) ≃L[ℂ] E x}
    (hΦ : IsPullbackTrivialization F γ x Φ) {c : Circle} (δ : Path c c)
    (hδ : ∀ t, (δ t : ℂ) = (clutchingFunction F γ Φ (squareBoundaryLoop t)).det /
      ‖(clutchingFunction F γ Φ (squareBoundaryLoop t)).det‖) :
    clutchingChernNumber F E γ = Circle.degree δ := by
  rw [clutchingChernNumber, degree_clutchingLoop_eq γ hΦ]
  refine Circle.degree_congr _ _ fun t ↦ Circle.ext ?_
  rw [hδ, clutchingLoop_apply,
    ContinuousLinearMap.coe_detPhase (det_clutchingFunction_squareBoundaryLoop_ne_zero γ Φ t)]

/-- **Homotopy invariance.** Based spheres which are homotopic relative to the boundary of the
square have the same clutching Chern number. -/
theorem clutchingChernNumber_eq_of_homotopic {γ₀ γ₁ : Ω^ (Fin 2) X x}
    (h : GenLoop.Homotopic γ₀ γ₁) : clutchingChernNumber F E γ₀ = clutchingChernNumber F E γ₁ := by
  obtain ⟨H⟩ := h
  have := FiniteDimensional.complete ℂ F
  set f : C(I × I^Fin 2, X) := H.toContinuousMap
  have hf (s : I) : ∀ y ∈ Cube.boundary (Fin 2), f (s, y) = x := fun y hy ↦
    (H.eq_fst s hy).trans (GenLoop.boundary γ₀ y hy)
  obtain ⟨Ψ, hΨ⟩ := exists_isPullbackTrivialization_of_boundary (𝕜 := ℂ) (F := F) (E := E) f hf
  -- The based spheres `y ↦ f (s, y)`, with the restrictions of `Ψ` as trivializations.
  let γ : I → Ω^ (Fin 2) X x := fun s ↦ ⟨⟨fun y ↦ f (s, y), by fun_prop⟩, hf s⟩
  have hγ (s : I) : IsPullbackTrivialization F (γ s) x fun y ↦ Ψ (s, y) :=
    hΨ.comp (g := fun y : I^Fin 2 ↦ (s, y)) (by fun_prop)
  have hmem (p : I × I) : f (p.1, squareBoundaryLoop p.2) ∈ (trivializationAt F E x).baseSet := by
    rw [hf p.1 _ (squareBoundaryLoop_mem_boundary p.2)]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  have hdet (p : I × I) :
      (clutchingFunction F (γ p.1) (fun y ↦ Ψ (p.1, y)) (squareBoundaryLoop p.2)).det ≠ 0 :=
    det_clutchingFunction_squareBoundaryLoop_ne_zero (γ p.1) _ p.2
  have hcont : Continuous fun p : I × I ↦
      clutchingFunction F (γ p.1) (fun y ↦ Ψ (p.1, y)) (squareBoundaryLoop p.2) :=
    (hΨ.continuousOn_coord f.continuous).comp_continuous
      (continuous_fst.prodMk (squareBoundaryLoop.continuous.comp continuous_snd)) hmem
  -- The clutching loops of the spheres `γ s` form a homotopy of loops.
  let G : C(I × I, Circle) := ⟨fun p ↦ (clutchingFunction F (γ p.1) (fun y ↦ Ψ (p.1, y))
    (squareBoundaryLoop p.2)).detPhase, ContinuousLinearMap.continuous_detPhase hcont hdet⟩
  have h₀ : γ 0 = γ₀ := GenLoop.ext _ _ H.apply_zero
  have h₁ : γ 1 = γ₁ := GenLoop.ext _ _ H.apply_one
  rw [← h₀, ← h₁, clutchingChernNumber, clutchingChernNumber, degree_clutchingLoop_eq _ (hγ 0),
    degree_clutchingLoop_eq _ (hγ 1)]
  exact Circle.degree_eq_of_homotopy _ _ G (fun _ ↦ rfl) (fun _ ↦ rfl) fun s ↦ by
    simp only [G, ContinuousMap.coe_mk, Path.source, Path.target]

/-- **Additivity.** The clutching Chern number of the concatenation `transAt 0 q p` of two based
spheres along the coordinate `0` is the sum of their clutching Chern numbers. The boundary loops
of the two halves of the square traverse the seam `y 0 = 1 / 2` in opposite directions, so the
angles swept along the seam cancel. -/
theorem clutchingChernNumber_transAt (q p : Ω^ (Fin 2) X x) :
    clutchingChernNumber F E (GenLoop.transAt 0 q p) =
      clutchingChernNumber F E q + clutchingChernNumber F E p := by
  -- Read all three clutching numbers from one trivialization `Φ` of the concatenation `γ`: on
  -- the halves of the square, `γ` restricts to `q` and `p`. Each boundary loop splits into four
  -- pieces, along the edges of the square and the seam, and the angle swept along each piece is
  -- read off from a lift of the phase along that edge or the seam.
  set γ := GenLoop.transAt 0 q p
  obtain ⟨Φ, hΦ⟩ := exists_isPullbackTrivialization (F := F) (E := E) γ
  have hx : x ∈ (trivializationAt F E x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  set U := γ ⁻¹' (trivializationAt F E x).baseSet
  have memU {y : I^Fin 2} (h : γ y = x) : y ∈ U := by
    simp only [U, mem_preimage, h]
    exact hx
  -- The phase of the determinant of the clutching function of `γ`, continuous on `U`, and its
  -- paths of values along paths in `U`.
  set H : (I^Fin 2) → Circle := fun y ↦ (clutchingFunction F γ Φ y).detPhase
  have hH : ContinuousOn H U := ContinuousLinearMap.continuousOn_detPhase
    (hΦ.continuousOn_coord γ.1.continuous) fun y hy ↦ det_clutchingFunction_ne_zero Φ hy
  have hm {a b : I^Fin 2} {c : Path a b} (hc : ∀ t, c t ∈ U) : ContinuousOn H (range c) :=
    hH.mono (range_subset_iff.2 hc)
  have hHc {a b : I^Fin 2} {c : Path a b} (hc : ∀ t, c t ∈ U) (t : I) :
      ((c.map' (hm hc) t : Circle) : ℂ) = (clutchingFunction F γ Φ (c t)).det /
        ‖(clutchingFunction F γ Φ (c t)).det‖ := by
    rw [Path.map'_coe, comp_apply, ContinuousLinearMap.coe_detPhase
      (det_clutchingFunction_ne_zero Φ (hc t))]
  have hb {y : I^Fin 2} (hy : y ∈ Cube.boundary (Fin 2)) : y ∈ U := memU (GenLoop.boundary γ y hy)
  have hl {y : I^Fin 2} (hy : y ∈ Cube.boundary (Fin 2)) : leftHalf y ∈ U :=
    memU ((transAt_leftHalf q p y).trans (GenLoop.boundary q y hy))
  have hr {y : I^Fin 2} (hy : y ∈ Cube.boundary (Fin 2)) : rightHalf y ∈ U :=
    memU ((transAt_rightHalf q p y).trans (GenLoop.boundary p y hy))
  have hβ (t : I) := squareBoundaryLoop_mem_boundary t
  have hβL (t : I) : squareBoundaryLoop.map continuous_leftHalf t ∈ U := by
    rw [Path.map_coe, comp_apply]
    exact hl (hβ t)
  have hβR (t : I) : squareBoundaryLoop.map continuous_rightHalf t ∈ U := by
    rw [Path.map_coe, comp_apply]
    exact hr (hβ t)
  -- The three clutching numbers as degrees of loops of phases.
  have hγ : clutchingChernNumber F E γ =
      Circle.degree (squareBoundaryLoop.map' (hm fun t ↦ hb (hβ t))) :=
    clutchingChernNumber_eq_degree γ hΦ _ (hHc fun t ↦ hb (hβ t))
  have hq : clutchingChernNumber F E q =
      Circle.degree ((squareBoundaryLoop.map continuous_leftHalf).map' (hm hβL)) := by
    have h := clutchingChernNumber_eq_degree (F := F) (E := E)
      (GenLoop.copy q (γ ∘ leftHalf) (funext (transAt_leftHalf q p)))
      (Φ := fun y ↦ Φ (leftHalf y)) (hΦ.comp continuous_leftHalf)
      ((squareBoundaryLoop.map continuous_leftHalf).map' (hm hβL)) fun t ↦ by
        rw [hHc hβL, Path.map_coe, comp_apply]
        rfl
    rwa [GenLoop.copy_eq] at h
  have hp : clutchingChernNumber F E p =
      Circle.degree ((squareBoundaryLoop.map continuous_rightHalf).map' (hm hβR)) := by
    have h := clutchingChernNumber_eq_degree (F := F) (E := E)
      (GenLoop.copy p (γ ∘ rightHalf) (funext (transAt_rightHalf q p)))
      (Φ := fun y ↦ Φ (rightHalf y)) (hΦ.comp continuous_rightHalf)
      ((squareBoundaryLoop.map continuous_rightHalf).map' (hm hβR)) fun t ↦ by
        rw [hHc hβR, Path.map_coe, comp_apply]
        rfl
    rwa [GenLoop.copy_eq] at h
  -- The edges of the square and the seam, with continuous lifts of the phase along them.
  have he₀ (t : I) : squareEdge₀ t ∈ Cube.boundary (Fin 2) := ⟨1, Or.inl rfl⟩
  have he₁ (t : I) : squareEdge₁ t ∈ Cube.boundary (Fin 2) := ⟨0, Or.inr rfl⟩
  have he₂ (t : I) : squareEdge₂ t ∈ Cube.boundary (Fin 2) := ⟨1, Or.inr rfl⟩
  have he₃ (t : I) : squareEdge₃ t ∈ Cube.boundary (Fin 2) := ⟨0, Or.inl rfl⟩
  obtain ⟨θB, hθB⟩ := Circle.exists_lift (squareEdge₀.map' (hm fun t ↦ hb (he₀ t)))
  obtain ⟨θR, hθR⟩ := Circle.exists_lift (squareEdge₁.map' (hm fun t ↦ hb (he₁ t)))
  obtain ⟨θT, hθT⟩ := Circle.exists_lift (squareEdge₂.map' (hm fun t ↦ hb (he₂ t)))
  obtain ⟨θL, hθL⟩ := Circle.exists_lift (squareEdge₃.map' (hm fun t ↦ hb (he₃ t)))
  obtain ⟨θS, hθS⟩ := Circle.exists_lift
    ((squareEdge₁.map continuous_leftHalf).map' (hm fun t ↦ hl (he₁ t)))
  -- The angle swept along each piece, read off from the lifts along the edges and the seam.
  have hpt {a b c d : I^Fin 2} {u : Path a b} {v : Path c d} (hu : ∀ t, u t ∈ U)
      (hv : ∀ t, v t ∈ U) {r : I → I} (h : ∀ t, u t = v (r t)) (t : I) :
      u.map' (hm hu) t = v.map' (hm hv) (r t) := by
    simp only [Path.map'_coe, comp_apply, h]
  have F₀ := Circle.angleChange_eq_sub _ θB.continuous hθB
  have F₁ := Circle.angleChange_eq_sub _ θR.continuous hθR
  have F₂ := Circle.angleChange_eq_sub _ θT.continuous hθT
  have F₃ := Circle.angleChange_eq_sub _ θL.continuous hθL
  have L₁ := Circle.angleChange_eq_sub _ θS.continuous hθS
  have L₀ := Circle.angleChange_eq_sub_of_reparam
    ((squareEdge₀.map continuous_leftHalf).map' (hm fun t ↦ hl (he₀ t))) _ θB.continuous hθB
    (r := fun t ↦ Set.projIcc 0 1 zero_le_one ((t : ℝ) / 2)) (by fun_prop)
    (hpt (fun t ↦ hl (he₀ t)) (fun t ↦ hb (he₀ t)) fun t ↦ by
      rw [Path.map_coe, comp_apply]
      ext j; fin_cases j <;> simp [leftHalf, squareEdge₀])
  have R₀ := Circle.angleChange_eq_sub_of_reparam
    ((squareEdge₀.map continuous_rightHalf).map' (hm fun t ↦ hr (he₀ t))) _ θB.continuous hθB
    (r := fun t ↦ Set.projIcc 0 1 zero_le_one (((t : ℝ) + 1) / 2)) (by fun_prop)
    (hpt (fun t ↦ hr (he₀ t)) (fun t ↦ hb (he₀ t)) fun t ↦ by
      rw [Path.map_coe, comp_apply]
      ext j; fin_cases j <;> simp [rightHalf, squareEdge₀])
  have L₂ := Circle.angleChange_eq_sub_of_reparam
    ((squareEdge₂.map continuous_leftHalf).map' (hm fun t ↦ hl (he₂ t))) _ θT.continuous hθT
    (r := fun t ↦ σ (Set.projIcc 0 1 zero_le_one ((σ t : ℝ) / 2))) (by fun_prop)
    (hpt (fun t ↦ hl (he₂ t)) (fun t ↦ hb (he₂ t)) fun t ↦ by
      rw [Path.map_coe, comp_apply]
      ext j; fin_cases j <;> simp [leftHalf, squareEdge₂])
  have R₂ := Circle.angleChange_eq_sub_of_reparam
    ((squareEdge₂.map continuous_rightHalf).map' (hm fun t ↦ hr (he₂ t))) _ θT.continuous hθT
    (r := fun t ↦ σ (Set.projIcc 0 1 zero_le_one (((σ t : ℝ) + 1) / 2))) (by fun_prop)
    (hpt (fun t ↦ hr (he₂ t)) (fun t ↦ hb (he₂ t)) fun t ↦ by
      rw [Path.map_coe, comp_apply]
      ext j; fin_cases j <;> simp [rightHalf, squareEdge₂])
  have L₃ := Circle.angleChange_eq_sub_of_reparam
    ((squareEdge₃.map continuous_leftHalf).map' (hm fun t ↦ hl (he₃ t))) _ θL.continuous hθL
    (r := id) continuous_id (hpt (fun t ↦ hl (he₃ t)) (fun t ↦ hb (he₃ t)) fun t ↦ by
      rw [Path.map_coe, comp_apply]
      ext j; fin_cases j <;> simp [leftHalf, squareEdge₃])
  have R₁ := Circle.angleChange_eq_sub_of_reparam
    ((squareEdge₁.map continuous_rightHalf).map' (hm fun t ↦ hr (he₁ t))) _ θR.continuous hθR
    (r := id) continuous_id (hpt (fun t ↦ hr (he₁ t)) (fun t ↦ hb (he₁ t)) fun t ↦ by
      rw [Path.map_coe, comp_apply]
      ext j; fin_cases j <;> simp [rightHalf, squareEdge₁])
  have R₃ := Circle.angleChange_eq_sub_of_reparam
    ((squareEdge₃.map continuous_rightHalf).map' (hm fun t ↦ hr (he₃ t))) _ θS.continuous hθS
    (r := σ) unitInterval.continuous_symm
    (hpt (fun t ↦ hr (he₃ t)) (fun t ↦ hl (he₁ t)) fun t ↦ by
      rw [Path.map_coe, Path.map_coe, comp_apply, comp_apply]
      ext j; fin_cases j <;> simp [leftHalf, rightHalf, squareEdge₁, squareEdge₃])
  -- Each boundary loop is a concatenation of four pieces. The angles along the seam cancel, and
  -- the halves of the bottom and top edges add up.
  have key : Circle.angleChange (squareBoundaryLoop.map' (hm fun t ↦ hb (hβ t))) =
      Circle.angleChange ((squareBoundaryLoop.map continuous_leftHalf).map' (hm hβL)) +
        Circle.angleChange ((squareBoundaryLoop.map continuous_rightHalf).map' (hm hβR)) := by
    simp only [squareBoundaryLoop, Path.map_trans, Path.map'_trans, Circle.angleChange_trans]
    rw [F₀, F₁, F₂, F₃, L₀, L₁, L₂, L₃, R₀, R₁, R₂, R₃]
    norm_num [unitInterval.symm_zero, unitInterval.symm_one]
    ring
  rw [Circle.angleChange_eq_degree_mul, Circle.angleChange_eq_degree_mul,
    Circle.angleChange_eq_degree_mul, ← add_mul] at key
  rw [hγ, hq, hp]
  exact_mod_cast mul_right_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) key

private theorem lift_clutchingChernNumber_mul (a b : HomotopyGroup (Fin 2) X x) :
    Quotient.lift (clutchingChernNumber F E) (fun _ _ ↦ clutchingChernNumber_eq_of_homotopic)
        (a * b) =
      Quotient.lift (clutchingChernNumber F E) (fun _ _ ↦ clutchingChernNumber_eq_of_homotopic) a +
        Quotient.lift (clutchingChernNumber F E)
          (fun _ _ ↦ clutchingChernNumber_eq_of_homotopic) b := by
  induction a using Quotient.inductionOn with | h p => ?_
  induction b using Quotient.inductionOn with | h q => ?_
  refine (congrArg (Quotient.lift (clutchingChernNumber F E)
    (fun _ _ ↦ clutchingChernNumber_eq_of_homotopic)) (HomotopyGroup.mul_spec (i := 0))).trans ?_
  simp only [Quotient.lift_mk, clutchingChernNumber_transAt, add_comm]

variable (F E) in
/-- The **clutching first Chern number** on the second homotopy group, `π₂(X, x) →+ ℤ`: the
clutching Chern number `clutchingChernNumber F E γ` of a representative `γ`, which depends only on
its homotopy class (`clutchingChernNumber_eq_of_homotopic`) and is additive for the group law of
`π₂(X, x)` (`clutchingChernNumber_transAt`). -/
def homotopyGroupClutchingChernNumber : Additive (HomotopyGroup (Fin 2) X x) →+ ℤ :=
  AddMonoidHom.mk' (fun a ↦ Quotient.lift (clutchingChernNumber F E)
      (fun _ _ ↦ clutchingChernNumber_eq_of_homotopic) a.toMul) fun a b ↦
    lift_clutchingChernNumber_mul a.toMul b.toMul

/-- The clutching Chern number of the homotopy class of a based sphere is the clutching Chern number
of the sphere. -/
@[simp]
theorem homotopyGroupClutchingChernNumber_ofMul_mk (γ : Ω^ (Fin 2) X x) :
    homotopyGroupClutchingChernNumber F E (.ofMul ⟦γ⟧) = clutchingChernNumber F E γ :=
  Quotient.lift_mk (s := GenLoop.Homotopic.setoid (Fin 2) x) (clutchingChernNumber F E)
    (fun _ _ ↦ clutchingChernNumber_eq_of_homotopic) γ

/-- The constant sphere has clutching Chern number zero. -/
@[simp]
theorem clutchingChernNumber_const :
    clutchingChernNumber F E (GenLoop.const : Ω^ (Fin 2) X x) = 0 := by
  rw [← homotopyGroupClutchingChernNumber_ofMul_mk, ← HomotopyGroup.one_def, ofMul_one, map_zero]

end Clutching

end TauCeti
