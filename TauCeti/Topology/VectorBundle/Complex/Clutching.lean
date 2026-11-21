/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import TauCeti.Analysis.Complex.NormalizedDeterminant
public import TauCeti.Topology.Circle.Degree.Square
public import TauCeti.Topology.Homotopy.HomotopyGroup.FundamentalGroupAction
public import TauCeti.Topology.Homotopy.HomotopyGroup.TransAt
public import TauCeti.Topology.VectorBundle.Complex.Structure
public import TauCeti.Topology.VectorBundle.Contractible
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Subpath

/-!
# The clutching number of a complex vector bundle over the second homotopy group

Let `E` be a complex vector bundle over a space `X`, with finite-dimensional model fibre `F`, and
let `x ∈ X`. A class of `π₂(X, x)` is represented by a sphere `p : Ω^ (Fin 2) X x`, a map
`I² → X` sending the boundary of the square to `x`, that is, a map from `S² = I² / ∂I²`. This file
attaches to `p` an integer, the **clutching number** `TauCeti.clutchingNumber F E p`, and shows
that it is an additive homomorphism `π₂(X, x) → ℤ` (`TauCeti.clutchingNumberHom`). This is the
clutching description of the first Chern number of `E` on the sphere `p` (Milnor–Stasheff, §14);
no comparison with a cohomological first Chern class is made here.

The sphere is the union of the square, a disc, and a small disc around the collapsed boundary,
where `p` is constant at `x`. The pullback of `E` to each piece is trivial:

* over the square, by a **frame of `E` along `p`**, a family of complex-linear isomorphisms
  `φ y : F ≃ E (p y)` for which `(y, v) ↦ φ y v` is continuous into the total space of `E`; it
  exists because the square is contractible (`TauCeti.exists_continuous_frame`);
* near the collapsed boundary, by a trivialization `e` of `E` near `x`.

Along the boundary of the square the transition `g y = (e ∘ φ y)⁻¹ : F ≃ F` expresses the frame
`e⁻¹` in the frame `φ y`, and the clutching number is the winding number of `det g` once
counterclockwise around the boundary of the square: the degree around the boundary
(`TauCeti.squareBoundaryDegree`) of the **clutching function**
`TauCeti.clutchingFunction p φ e y = det g y / ‖det g y‖`.

The clutching function depends on the choices, but its degree does not:

* **frames:** two frames along the same map differ by a continuous map from the domain to
  `GL(F)`, so their clutching functions differ by a factor continuous on the whole square
  (`TauCeti.clutchingFunction_eq_mul_normalizedDet_inv`,
  `TauCeti.continuous_normalizedDet_trans_symm`), which has degree `0`;
* **trivializations:** two trivializations near `x` change the clutching function on the boundary
  by the constant factor of their coordinate change at `x`
  (`TauCeti.clutchingFunction_eq_mul_coordChangeL`).

So `TauCeti.clutchingNumber_eq_squareBoundaryDegree` computes the clutching number from any frame
and any trivialization near `x`. It is additive under the concatenation `GenLoop.transAt 0` that
defines the product of `π₂(X, x)`, because a frame along the concatenation restricts to frames
along both halves (`TauCeti.clutchingNumber_transAt`).

The clutching number is invariant under homotopies of spheres whose base points trace a path `γ`
(`TauCeti.GenLoop.HomotopyAlong`). Restrict one frame along the whole homotopy to each time. Near
a given time, read the slices in one trivialization around the corresponding point of `γ`; the
change of trivialization at the moving base point is a constant factor on the boundary, so the
clutching number of the slices is locally constant in time, hence constant
(`TauCeti.clutchingNumber_eq_of_homotopyAlong`). For a constant path this is invariance under
homotopies relative to the boundary (`TauCeti.clutchingNumber_eq_of_homotopic`). The clutching
number does not depend on the base point: since the transport of a sphere along a path is joined
to it by such a homotopy, transport does not change clutching numbers
(`TauCeti.clutchingNumberHom_homotopyGroupTransport`), and the clutching number homomorphism is
invariant under the action of the fundamental group on `π₂(X, x)`
(`TauCeti.clutchingNumberHom_fundamentalGroup_smul`).

A family of complex-linear isomorphisms `E x ≃ E' x`, continuous on total spaces, carries frames
of `E` to frames of `E'` and changes the clutching function only by conjugation, so isomorphic
bundles have the same clutching numbers (`TauCeti.clutchingNumber_eq_of_continuousLinearEquiv`).

The bundle may be the tangent bundle `(TX, J)` of a manifold with an almost complex structure `J`,
made a complex vector bundle by
`TauCeti.ContMDiffAlmostComplexStructure.toContinuousComplexStructure`; this gives the clutching
number of the almost complex tangent bundle on spheres. More generally, a continuous complex
structure `J` on a real vector bundle `V` makes it a complex vector bundle `J.Fiber`. Two such
structures `J₀` and `J₁` that are nowhere opposite, `J₁ v ≠ -J₀ v` for `v ≠ 0`, give isomorphic
complex vector bundles, hence the same clutching numbers
(`TauCeti.Bundle.ContinuousComplexStructure.clutchingNumberHom_eq_of_injective_add`); this is the
case for any two almost complex structures tamed by a common symplectic form.

## Main definitions

* `TauCeti.clutchingFunction p φ e`: the normalized determinant of the transition between a frame
  `φ` along `p` and a trivialization `e`.
* `TauCeti.clutchingNumber F E p`: the clutching number of `E` on a based sphere `p`.
* `TauCeti.clutchingNumberHom F E x`: the clutching number as a homomorphism `π₂(X, x) → ℤ`.

## Main results

* `TauCeti.clutchingNumber_eq_squareBoundaryDegree`: the clutching number may be computed from any
  frame and any trivialization near `x`.
* `TauCeti.clutchingNumber_eq_of_homotopic`: homotopy invariance.
* `TauCeti.clutchingNumber_transAt`: additivity under concatenation.
* `TauCeti.clutchingNumber_eq_of_homotopyAlong`: invariance under homotopies through spheres
  whose base points move along a path.
* `TauCeti.clutchingNumberHom_homotopyGroupTransport`,
  `TauCeti.clutchingNumberHom_fundamentalGroup_smul`: independence of the base point.
* `TauCeti.clutchingNumber_eq_of_continuousLinearEquiv`,
  `TauCeti.clutchingNumberHom_eq_of_continuousLinearEquiv`: invariance under isomorphisms of
  complex vector bundles.
* `TauCeti.Bundle.ContinuousComplexStructure.clutchingNumberHom_eq_of_injective_add`: nowhere
  opposite complex structures on a real vector bundle have the same clutching numbers.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (Chern classes of complex vector bundles).
* A. Hatcher, *Vector Bundles and K-Theory*, Section 1.2 (clutching functions).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Appendix C.1 (the first Chern number of a bundle over a surface by clutching).
-/

public section

noncomputable section

open Bundle Set Topology Filter
open scoped unitInterval Topology.Homotopy

namespace TauCeti

variable {B X : Type*} [TopologicalSpace B] [TopologicalSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]

/-! ### The clutching function of a frame -/

section ClutchingFunction

variable {f : B → X} {φ ψ : ∀ y, F ≃L[ℂ] E (f y)}
  {e e' : Trivialization F (π F E)} [e.IsLinear ℂ] [e'.IsLinear ℂ]

open Classical in
/-- The **clutching function** of a family `φ y : F ≃ E (f y)` of frames of `E` along a map `f`,
read in a trivialization `e` of `E`: at a point `y` with `f y` in the base set of `e`, the
normalized determinant of the transition `(e ∘ φ y)⁻¹ : F ≃ F`, which expresses the frame of `E`
given by `e` in the frame `φ y`. It is `1` at the other points. -/
def clutchingFunction (f : B → X) (φ : ∀ y, F ≃L[ℂ] E (f y)) (e : Trivialization F (π F E))
    [e.IsLinear ℂ] (y : B) : Circle :=
  if hy : f y ∈ e.baseSet then
    ((φ y).trans (e.continuousLinearEquivAt ℂ (f y) hy)).normalizedDet⁻¹
  else 1

omit [TopologicalSpace B] in
theorem clutchingFunction_of_mem {y : B} (hy : f y ∈ e.baseSet) :
    clutchingFunction f φ e y =
      ((φ y).trans (e.continuousLinearEquivAt ℂ (f y) hy)).normalizedDet⁻¹ :=
  dite_eq_left hy

omit [TopologicalSpace B] in
theorem clutchingFunction_of_notMem {y : B} (hy : f y ∉ e.baseSet) :
    clutchingFunction f φ e y = 1 :=
  dite_eq_right hy

omit [TopologicalSpace B] in
/-- The clutching function of a frame restricted along a map `k` is the restriction of the
clutching function. -/
@[simp]
theorem clutchingFunction_comp {B' : Type*} (f : B → X) (k : B' → B) (φ : ∀ y, F ≃L[ℂ] E (f y))
    (e : Trivialization F (π F E)) [e.IsLinear ℂ] (y : B') :
    clutchingFunction (f ∘ k) (fun y ↦ φ (k y)) e y = clutchingFunction f φ e (k y) :=
  (rfl)

omit [TopologicalSpace B] in
/-- **Change of frame.** If `φ` and `ψ` are frames along the same map, their clutching functions
in a trivialization differ by the inverse normalized determinant of the automorphism
`(φ y)⁻¹ ∘ ψ y` of `F`. -/
theorem clutchingFunction_eq_mul_normalizedDet_inv {y : B} (hy : f y ∈ e.baseSet) :
    clutchingFunction f ψ e y =
      clutchingFunction f φ e y * ((ψ y).trans (φ y).symm).normalizedDet⁻¹ := by
  have h : (ψ y).trans (e.continuousLinearEquivAt ℂ (f y) hy) =
      ((ψ y).trans (φ y).symm).trans ((φ y).trans (e.continuousLinearEquivAt ℂ (f y) hy)) := by
    ext v
    simp
  rw [clutchingFunction_of_mem hy, clutchingFunction_of_mem hy, h,
    ContinuousLinearEquiv.normalizedDet_trans, mul_inv, mul_comm]

omit [TopologicalSpace B] in
/-- **Change of trivialization.** At a point where two trivializations `e` and `e'` are both
defined, the clutching functions of a frame in `e'` and in `e` differ by the inverse normalized
determinant of the coordinate change from `e` to `e'`. -/
theorem clutchingFunction_eq_mul_coordChangeL {y : B} (hy : f y ∈ e.baseSet)
    (hy' : f y ∈ e'.baseSet) :
    clutchingFunction f φ e' y =
      clutchingFunction f φ e y * (e.coordChangeL ℂ e' (f y)).normalizedDet⁻¹ := by
  have h : (φ y).trans (e'.continuousLinearEquivAt ℂ (f y) hy') =
      ((φ y).trans (e.continuousLinearEquivAt ℂ (f y) hy)).trans (e.coordChangeL ℂ e' (f y)) := by
    ext v
    simp [e.coordChangeL_apply e' ⟨hy, hy'⟩, e.symm_apply_apply_mk hy]
  rw [clutchingFunction_of_mem hy, clutchingFunction_of_mem hy', h,
    ContinuousLinearEquiv.normalizedDet_trans, mul_inv]

variable [FiniteDimensional ℂ F]

/-- The clutching function of a continuous frame is continuous wherever the trivialization is
defined. -/
theorem continuousOn_clutchingFunction
    (hφ : Continuous fun q : B × F ↦ TotalSpace.mk' F (f q.1) (φ q.1 q.2))
    (e : Trivialization F (π F E)) [e.IsLinear ℂ] :
    ContinuousOn (clutchingFunction f φ e) (f ⁻¹' e.baseSet) := by
  classical
  -- A total family of automorphisms of `F` agreeing with `e ∘ φ` over the base set.
  let A : B → F ≃L[ℂ] F := fun y ↦ if hy : f y ∈ e.baseSet then
    (φ y).trans (e.continuousLinearEquivAt ℂ (f y) hy) else ContinuousLinearEquiv.refl ℂ F
  have hA : ContinuousOn (fun y ↦ (A y : F →L[ℂ] F)) (f ⁻¹' e.baseSet) :=
    (continuousOn_continuousLinearMapAt_comp hφ e).congr fun y (hy : f y ∈ e.baseSet) ↦
      ContinuousLinearMap.ext fun v ↦ by simp [A, hy, e.coe_linearMapAt_of_mem hy]
  refine hA.normalizedDet.inv.congr fun y (hy : f y ∈ e.baseSet) ↦ ?_
  simp [A, clutchingFunction_of_mem hy, hy]

/-- Two continuous frames along the same map differ by a continuous family of automorphisms of
`F`, so the normalized determinant of `(φ y)⁻¹ ∘ ψ y` is continuous on the whole domain. -/
theorem continuous_normalizedDet_trans_symm [VectorBundle ℂ F E]
    (hφ : Continuous fun q : B × F ↦ TotalSpace.mk' F (f q.1) (φ q.1 q.2))
    (hψ : Continuous fun q : B × F ↦ TotalSpace.mk' F (f q.1) (ψ q.1 q.2)) :
    Continuous fun y ↦ ((ψ y).trans (φ y).symm).normalizedDet := by
  refine continuous_iff_continuousAt.2 fun y₀ ↦ ?_
  -- Near `y₀`, read both frames in a trivialization around `f y₀`.
  let e₀ := trivializationAt F E (f y₀)
  have hU : f ⁻¹' e₀.baseSet ∈ 𝓝 y₀ :=
    (continuous_of_continuous_frame hφ).continuousAt.preimage_mem_nhds
      (e₀.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E (f y₀)))
  refine (((continuousOn_clutchingFunction hψ e₀).inv.mul
    (continuousOn_clutchingFunction hφ e₀)).continuousAt hU).congr
      (eventually_of_mem hU fun y (hy : f y ∈ e₀.baseSet) ↦ ?_)
  simp [clutchingFunction_eq_mul_normalizedDet_inv (φ := φ) (ψ := ψ) hy]

end ClutchingFunction

/-! ### The clutching number -/

section ClutchingNumber

variable [VectorBundle ℂ F E] [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)]
  [FiniteDimensional ℂ F] {x y : X}

/-- The finite-dimensional model fibre is complete, as `TauCeti.exists_continuous_frame` needs. -/
private local instance : CompleteSpace F := FiniteDimensional.completeSpace ℂ F

omit [VectorBundle ℂ F E] [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)] in
/-- The clutching function of a continuous frame along a sphere based at `x`, read in a
trivialization defined at `x`, is continuous on the boundary of the square. -/
theorem continuousOn_clutchingFunction_boundary (p : Ω^ (Fin 2) X x)
    {φ : ∀ y, F ≃L[ℂ] E (p y)}
    (hφ : Continuous fun q : (Fin 2 → I) × F ↦ TotalSpace.mk' F (p q.1) (φ q.1 q.2))
    (e : Trivialization F (π F E)) [e.IsLinear ℂ] (hx : x ∈ e.baseSet) :
    ContinuousOn (clutchingFunction p φ e) (Cube.boundary (Fin 2)) :=
  (continuousOn_clutchingFunction hφ e).mono fun y hy ↦ by simp [GenLoop.boundary p y hy, hx]

variable (F E) in
/-- The **clutching number** of a complex vector bundle `E` on a sphere `p : I² → X` based at `x`
(sending the boundary of the square to `x`): the degree around the boundary of the square of the
clutching function of a frame of `E` along `p`, read in the trivialization
`trivializationAt F E x`. It does not depend on these choices
(`TauCeti.clutchingNumber_eq_squareBoundaryDegree`). -/
def clutchingNumber (p : Ω^ (Fin 2) X x) : ℤ :=
  squareBoundaryDegree
    (clutchingFunction p
      (exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous p)).choose
      (trivializationAt F E x))

/-- **The clutching number from any frame and any trivialization.** The clutching number of a
sphere `p` based at `x` is the degree around the boundary of the square of the clutching function
of any continuous frame along `p`, read in any trivialization of `E` around `x`. -/
theorem clutchingNumber_eq_squareBoundaryDegree (p : Ω^ (Fin 2) X x)
    (e : Trivialization F (π F E)) [e.IsLinear ℂ] (hx : x ∈ e.baseSet)
    {φ : ∀ y, F ≃L[ℂ] E (p y)}
    (hφ : Continuous fun q : (Fin 2 → I) × F ↦ TotalSpace.mk' F (p q.1) (φ q.1 q.2)) :
    clutchingNumber F E p = squareBoundaryDegree (clutchingFunction p φ e) := by
  obtain hφ₀ := (exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous p)).choose_spec
  set φ₀ := (exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous p)).choose
  set e₀ := trivializationAt F E x
  have hx₀ : x ∈ e₀.baseSet := mem_baseSet_trivializationAt F E x
  have hc₀ := continuousOn_clutchingFunction_boundary p hφ₀ e₀ hx₀
  have hK : Continuous fun y ↦ ((φ y).trans (φ₀ y).symm).normalizedDet⁻¹ :=
    (continuous_normalizedDet_trans_symm hφ₀ hφ).inv
  -- On the boundary, the clutching function of `φ` in `e` is that of `φ₀` in `e₀`, times a factor
  -- continuous on the whole square (change of frame) and a constant (change of trivialization).
  have heq : EqOn (clutchingFunction p φ e)
      ((clutchingFunction p φ₀ e₀ * fun y ↦ ((φ y).trans (φ₀ y).symm).normalizedDet⁻¹) *
        fun _ ↦ (e₀.coordChangeL ℂ e x).normalizedDet⁻¹) (Cube.boundary (Fin 2)) := by
    intro y hy
    have hy₀ : p y ∈ e₀.baseSet := mem_of_eq_of_mem (GenLoop.boundary p y hy) hx₀
    have hy' : p y ∈ e.baseSet := mem_of_eq_of_mem (GenLoop.boundary p y hy) hx
    rw [clutchingFunction_eq_mul_coordChangeL hy₀ hy',
      clutchingFunction_eq_mul_normalizedDet_inv (φ := φ₀) hy₀,
      show e₀.coordChangeL ℂ e (p y) = e₀.coordChangeL ℂ e x by rw [GenLoop.boundary p y hy],
      Pi.mul_apply, Pi.mul_apply]
  rw [squareBoundaryDegree_congr heq, squareBoundaryDegree_mul (hc₀.mul hK.continuousOn)
    continuousOn_const, squareBoundaryDegree_mul hc₀ hK.continuousOn,
    squareBoundaryDegree_eq_zero_of_continuous hK, squareBoundaryDegree_const, add_zero, add_zero,
    clutchingNumber]

/-- **Restricting a frame.** If a sphere is `f ∘ k` for a continuous map `k` from the square into
the domain of `f`, its clutching number is the degree around the boundary of the square of the
clutching function of any continuous frame along `f`, restricted along `k`. -/
theorem clutchingNumber_eq_squareBoundaryDegree_comp {f : C(B, X)} {Ψ : ∀ y, F ≃L[ℂ] E (f y)}
    (hΨ : Continuous fun q : B × F ↦ TotalSpace.mk' F (f q.1) (Ψ q.1 q.2))
    (k : C(Fin 2 → I, B)) (hk : ∀ y ∈ Cube.boundary (Fin 2), f (k y) = x)
    (e : Trivialization F (π F E)) [e.IsLinear ℂ] (hx : x ∈ e.baseSet) :
    clutchingNumber F E ⟨f.comp k, hk⟩ = squareBoundaryDegree (clutchingFunction f Ψ e ∘ k) := by
  rw [clutchingNumber_eq_squareBoundaryDegree ⟨f.comp k, hk⟩ e hx (φ := fun y ↦ Ψ (k y))
    (hΨ.comp ((k.continuous.comp continuous_fst).prodMk continuous_snd))]
  exact congrArg squareBoundaryDegree (funext fun y ↦ clutchingFunction_comp f k Ψ e y)

omit [VectorBundle ℂ F E] [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)] in
/-- Along a homotopy `H` of spheres whose base points trace a path `γ`, the clutching function of a
frame along `H`, read in a trivialization `e` containing `γ` on the interval between two times `a`
and `b`, has the same degree around the boundary of the square at the times `a` and `b`. -/
private theorem squareBoundaryDegree_clutchingFunction_eq_of_uIcc {H : I × (Fin 2 → I) → X}
    {γ : Path x y} (hHγ : ∀ t, ∀ z ∈ Cube.boundary (Fin 2), H (t, z) = γ t)
    {Θ : ∀ w, F ≃L[ℂ] E (H w)}
    (hΘ : Continuous fun q : (I × (Fin 2 → I)) × F ↦ TotalSpace.mk' F (H q.1) (Θ q.1 q.2))
    (e : Trivialization F (π F E)) [e.IsLinear ℂ] {a b : I}
    (hab : ∀ t ∈ uIcc a b, γ t ∈ e.baseSet) :
    squareBoundaryDegree (fun z ↦ clutchingFunction H Θ e (a, z)) =
      squareBoundaryDegree (fun z ↦ clutchingFunction H Θ e (b, z)) := by
  -- Run through the interval from `a` to `b` by the convex combinations of `a` and `b`.
  have hc : ContinuousOn
      (fun w : I × (Fin 2 → I) ↦ clutchingFunction H Θ e (Set.Icc.convexComb a b w.1, w.2))
      (univ ×ˢ Cube.boundary (Fin 2)) := by
    refine (continuousOn_clutchingFunction hΘ e).comp (by fun_prop) fun w hw ↦ ?_
    rw [mem_preimage, hHγ _ _ hw.2]
    exact hab _ (Path.range_subpathAux a b ▸ mem_range_self _)
  simpa using squareBoundaryDegree_eq_of_homotopy hc

/-- **Invariance under free homotopy.** Spheres `p` at `x` and `q` at `y` joined by a homotopy
through spheres whose base points trace a path `γ` from `x` to `y` have the same clutching
number. -/
theorem clutchingNumber_eq_of_homotopyAlong {γ : Path x y} {p : Ω^ (Fin 2) X x}
    {q : Ω^ (Fin 2) X y} (h : GenLoop.HomotopyAlong γ p q) :
    clutchingNumber F E q = clutchingNumber F E p := by
  have : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  obtain ⟨Θ, hΘ⟩ := exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous h)
  have hHγ (t : I) (z : Fin 2 → I) (hz : z ∈ Cube.boundary (Fin 2)) : h (t, z) = γ t :=
    h.map_boundary t z hz
  -- The slice of the homotopy at time `τ`, a sphere based at `γ τ`, with the restricted frame.
  let ι (τ : I) : C(Fin 2 → I, I × (Fin 2 → I)) := ⟨fun z ↦ (τ, z), by fun_prop⟩
  let slice (τ : I) : Ω^ (Fin 2) X (γ τ) := ⟨(h : C(I × (Fin 2 → I), X)).comp (ι τ), hHγ τ⟩
  have hslice (τ : I) (e : Trivialization F (π F E)) [e.IsLinear ℂ] (he : γ τ ∈ e.baseSet) :
      clutchingNumber F E (slice τ) =
        squareBoundaryDegree (fun z ↦ clutchingFunction h Θ e (τ, z)) :=
    clutchingNumber_eq_squareBoundaryDegree_comp (f := h) hΘ (ι τ) (hHγ τ) e he
  -- The clutching number of the slice is locally constant in time: near `τ₀`, compute it in one
  -- trivialization around `γ τ₀` and move along intervals on which `γ` stays in its base set.
  have hloc : IsLocallyConstant fun τ ↦ clutchingNumber F E (slice τ) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun τ₀ ↦ ?_
    set e₀ := trivializationAt F E (γ τ₀)
    have hW : γ ⁻¹' e₀.baseSet ∈ 𝓝 τ₀ := γ.continuous.continuousAt.preimage_mem_nhds
      (e₀.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E (γ τ₀)))
    filter_upwards [tendsto_smallSets_iff.1 (tendsto_const_nhds.uIcc tendsto_id) _ hW]
      with τ hτ
    rw [hslice τ e₀ (hτ right_mem_uIcc), hslice τ₀ e₀ (hτ left_mem_uIcc)]
    exact (squareBoundaryDegree_clutchingFunction_eq_of_uIcc hHγ hΘ e₀ hτ).symm
  -- The slices at times `0` and `1` are `p` and `q`, read at the base points `x` and `y`.
  have hend (τ : I) {z : X} (hz : γ τ = z) (r : Ω^ (Fin 2) X z) (hr : ∀ w, h (τ, w) = r w) :
      clutchingNumber F E r = clutchingNumber F E (slice τ) := by
    set e := trivializationAt F E z
    have hze : z ∈ e.baseSet := mem_baseSet_trivializationAt F E z
    have hr' : r = ⟨(h : C(I × (Fin 2 → I), X)).comp (ι τ), fun w hw ↦
        (hHγ τ w hw).trans hz⟩ := GenLoop.ext _ _ fun w ↦ (hr w).symm
    rw [hr', clutchingNumber_eq_squareBoundaryDegree_comp (f := h) hΘ (ι τ) _ e hze,
      hslice τ e (by rwa [hz])]
    simp only [Function.comp_def, ι, ContinuousMap.coe_mk]
  rw [hend 0 γ.source p h.apply_zero, hend 1 γ.target q h.apply_one]
  exact hloc.apply_eq_of_preconnectedSpace 1 0

/-- **Homotopy invariance.** Spheres based at `x` that are homotopic relative to the boundary of
the square have the same clutching number. -/
theorem clutchingNumber_eq_of_homotopic {p q : Ω^ (Fin 2) X x} (h : GenLoop.Homotopic p q) :
    clutchingNumber F E p = clutchingNumber F E q := by
  obtain ⟨H⟩ := h
  exact (clutchingNumber_eq_of_homotopyAlong (GenLoop.HomotopyAlong.ofHomotopyRel H)).symm

/-- **Additivity.** The clutching number of the concatenation `GenLoop.transAt 0 q p` of two
spheres is the sum of their clutching numbers. -/
theorem clutchingNumber_transAt (p q : Ω^ (Fin 2) X x) :
    clutchingNumber F E (GenLoop.transAt 0 q p) =
      clutchingNumber F E q + clutchingNumber F E p := by
  set f := GenLoop.transAt 0 q p
  obtain ⟨Ψ, hΨ⟩ := exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous f)
  set e₀ := trivializationAt F E x
  have hx₀ : x ∈ e₀.baseSet := mem_baseSet_trivializationAt F E x
  -- The concatenation is the base point on the boundary and on the seam `s = 1/2`, so its
  -- clutching function splits along the seam.
  have hcont : ContinuousOn (clutchingFunction f Ψ e₀)
      (Cube.boundary (Fin 2) ∪ {y : Fin 2 → I | (y 0 : ℝ) = 1 / 2}) := by
    refine (continuousOn_clutchingFunction hΨ e₀).mono fun y hy ↦ ?_
    rcases hy with hy | hy
    · exact mem_preimage.2 (mem_of_eq_of_mem (GenLoop.boundary f y hy) hx₀)
    · exact mem_preimage.2 (mem_of_eq_of_mem (GenLoop.transAt_apply_of_coe_eq_half 0 q p hy) hx₀)
  -- The two halves of the concatenation are `q` and `p`, with the halves of the frame `Ψ`.
  let qL : Ω^ (Fin 2) X x := ⟨f.val.comp (cubeLeftHalf 0), fun y hy ↦
    (GenLoop.transAt_apply_cubeLeftHalf 0 q p y).trans (GenLoop.boundary q y hy)⟩
  let pR : Ω^ (Fin 2) X x := ⟨f.val.comp (cubeRightHalf 0), fun y hy ↦
    (GenLoop.transAt_apply_cubeRightHalf 0 q p y).trans (GenLoop.boundary p y hy)⟩
  have hqL : qL = q := GenLoop.ext _ _ (GenLoop.transAt_apply_cubeLeftHalf 0 q p)
  have hpR : pR = p := GenLoop.ext _ _ (GenLoop.transAt_apply_cubeRightHalf 0 q p)
  rw [clutchingNumber_eq_squareBoundaryDegree f e₀ hx₀ hΨ, squareBoundaryDegree_eq_add hcont,
    ← hqL, ← hpR,
    clutchingNumber_eq_squareBoundaryDegree_comp (f := f.val) hΨ (cubeLeftHalf 0) _ e₀ hx₀,
    clutchingNumber_eq_squareBoundaryDegree_comp (f := f.val) hΨ (cubeRightHalf 0) _ e₀ hx₀]
  -- The coercions `⇑f` and `⇑f.1` agree by definition (`GenLoop.coe_coe`).
  rfl

variable (F E x) in
/-- The **clutching number homomorphism** `π₂(X, x) → ℤ` of a finite-rank complex vector bundle
`E` over `X`: the clutching number of any sphere representing the class. -/
def clutchingNumberHom : Additive (π_ 2 X x) →+ ℤ :=
  AddMonoidHom.mk' (fun a ↦ Quotient.lift (fun p : Ω^ (Fin 2) X x ↦ clutchingNumber F E p)
    (fun _ _ ↦ clutchingNumber_eq_of_homotopic) a.toMul)
    fun a b ↦ by
      obtain ⟨p, hp⟩ := Quotient.exists_rep a.toMul
      obtain ⟨q, hq⟩ := Quotient.exists_rep b.toMul
      have hmul := HomotopyGroup.mul_spec (i := (0 : Fin 2)) (p := p) (q := q)
      beta_reduce at hmul
      rw [toMul_add, ← hp, ← hq, hmul]
      exact (clutchingNumber_transAt p q).trans (add_comm _ _)

/-- The clutching number homomorphism evaluated on the class of a sphere. -/
@[simp]
theorem clutchingNumberHom_apply_mk (p : Ω^ (Fin 2) X x) :
    clutchingNumberHom F E x (Additive.ofMul (Quotient.mk _ p)) = clutchingNumber F E p :=
  (rfl)

/-! ### Base-point change -/

/-- **Base-point change.** Transporting a sphere along a path does not change its clutching
number. -/
@[simp]
theorem clutchingNumber_transport (γ : Path x y) (p : Ω^ (Fin 2) X x) :
    clutchingNumber F E (GenLoop.transport γ p) = clutchingNumber F E p :=
  clutchingNumber_eq_of_homotopyAlong (GenLoop.collarHomotopyAlong γ p)

/-- **Base-point change.** The clutching number homomorphism at `y`, on the transport of a class of
`π₂(X, x)` along a path from `x` to `y`, is the clutching number homomorphism at `x` on that
class. -/
@[simp]
theorem clutchingNumberHom_homotopyGroupTransport (γ : Path x y) (a : π_ 2 X x) :
    clutchingNumberHom F E y (Additive.ofMul (homotopyGroupTransport γ a)) =
      clutchingNumberHom F E x (Additive.ofMul a) := by
  induction a using Quotient.inductionOn with
  | h p => rw [homotopyGroupTransport_mk, clutchingNumberHom_apply_mk,
      clutchingNumberHom_apply_mk, clutchingNumber_transport]

/-- The clutching number homomorphism is invariant under the action of the fundamental group on
`π₂(X, x)`. -/
@[simp]
theorem clutchingNumberHom_fundamentalGroup_smul (g : FundamentalGroup X x) (a : π_ 2 X x) :
    clutchingNumberHom F E x (Additive.ofMul (g • a)) =
      clutchingNumberHom F E x (Additive.ofMul a) := by
  obtain ⟨p, hp⟩ := Path.Homotopic.Quotient.mk_surjective g.toPath
  rw [fundamentalGroup_smul_eq_transport hp.symm, clutchingNumberHom_homotopyGroupTransport]

end ClutchingNumber

/-! ### Isomorphic bundles -/

section Equiv

variable [VectorBundle ℂ F E] [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)]
  [FiniteDimensional ℂ F] {x : X}
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F'] [FiniteDimensional ℂ F']
  {E' : X → Type*} [∀ x, AddCommGroup (E' x)] [∀ x, Module ℂ (E' x)]
  [∀ x, TopologicalSpace (E' x)] [TopologicalSpace (TotalSpace F' E')] [FiberBundle F' E']
  [VectorBundle ℂ F' E'] [∀ x, IsTopologicalAddGroup (E' x)] [∀ x, ContinuousSMul ℂ (E' x)]

/-- The finite-dimensional model fibre is complete, as `TauCeti.exists_continuous_frame` needs. -/
private local instance : CompleteSpace F := FiniteDimensional.completeSpace ℂ F

/-- **Isomorphic bundles have the same clutching numbers.** If `Φ x : E x ≃ E' x` is a family of
complex-linear isomorphisms that is continuous on total spaces, then `E` and `E'` have the same
clutching number on every sphere. The model fibres `F` and `F'` may differ. -/
theorem clutchingNumber_eq_of_continuousLinearEquiv (Φ : ∀ x, E x ≃L[ℂ] E' x)
    (hΦ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F' v.proj (Φ v.proj v.snd))
    (p : Ω^ (Fin 2) X x) : clutchingNumber F' E' p = clutchingNumber F E p := by
  obtain ⟨φ, hφ⟩ := exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous p)
  set e := trivializationAt F E x
  set e' := trivializationAt F' E' x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F E x
  have hx' : x ∈ e'.baseSet := mem_baseSet_trivializationAt F' E' x
  -- The model fibres are identified through the fibres over the base point, and `Φ` carries the
  -- frame `φ` of `E` to a frame `ψ` of `E'`.
  let L : F' ≃L[ℂ] F := (e'.continuousLinearEquivAt ℂ x hx').symm.trans
    ((Φ x).symm.trans (e.continuousLinearEquivAt ℂ x hx))
  let ψ : ∀ y, F' ≃L[ℂ] E' (p y) := fun y ↦ L.trans ((φ y).trans (Φ (p y)))
  have hψ : Continuous fun q : (Fin 2 → I) × F' ↦ TotalSpace.mk' F' (p q.1) (ψ q.1 q.2) :=
    hΦ.comp (hφ.comp (continuous_fst.prodMk (L.continuous.comp continuous_snd)))
  -- Over the base point, `Φ` read in the two trivializations is `L⁻¹` read in `e`.
  have hΦx : ∀ z, z = x → ∀ (h : z ∈ e.baseSet) (h' : z ∈ e'.baseSet),
      (Φ z).trans (e'.continuousLinearEquivAt ℂ z h') =
        (e.continuousLinearEquivAt ℂ z h).trans L.symm := by
    rintro z rfl h h'
    ext v
    simp [L, e.symm_apply_apply_mk h]
  rw [clutchingNumber_eq_squareBoundaryDegree p e' hx' hψ,
    clutchingNumber_eq_squareBoundaryDegree p e hx hφ]
  refine squareBoundaryDegree_congr fun y hy ↦ ?_
  have hpy : p y = x := GenLoop.boundary p y hy
  have h : p y ∈ e.baseSet := mem_of_eq_of_mem hpy hx
  have h' : p y ∈ e'.baseSet := mem_of_eq_of_mem hpy hx'
  -- On the boundary, the transition of `ψ` in `e'` is that of `φ` in `e`, conjugated by `L`.
  have hconj : (ψ y).trans (e'.continuousLinearEquivAt ℂ (p y) h') =
      L.trans (((φ y).trans (e.continuousLinearEquivAt ℂ (p y) h)).trans L.symm) := by
    ext v
    simpa [ψ] using congrArg (fun T : E (p y) ≃L[ℂ] F' ↦ T (φ y (L v))) (hΦx (p y) hpy h h')
  rw [clutchingFunction_of_mem h', clutchingFunction_of_mem h, hconj,
    ContinuousLinearEquiv.normalizedDet_trans_trans_symm]

/-- **Isomorphic bundles have the same clutching number homomorphisms**: the clutching number
homomorphisms of `E` and `E'` agree, for any family of complex-linear isomorphisms
`Φ x : E x ≃ E' x` that is continuous on total spaces. -/
theorem clutchingNumberHom_eq_of_continuousLinearEquiv (Φ : ∀ x, E x ≃L[ℂ] E' x)
    (hΦ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F' v.proj (Φ v.proj v.snd)) (x : X) :
    clutchingNumberHom F' E' x = clutchingNumberHom F E x := by
  ext a
  induction a using Additive.rec with
  | ofMul a =>
    induction a using Quotient.inductionOn with
    | h p => exact clutchingNumber_eq_of_continuousLinearEquiv Φ hΦ p

end Equiv

/-! ### Changing the complex structure -/

section ComplexStructure

variable {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [FiniteDimensional ℝ F₀]
  {V : X → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F₀ V)] [FiberBundle F₀ V] [VectorBundle ℝ F₀ V]
  [FiniteDimensional ℂ F] [Fact (Module.finrank ℝ F₀ = 2 * Module.finrank ℂ F)]

variable (F) in
/-- **Nowhere opposite complex structures have the same clutching numbers.** If two continuous
complex structures `J₀` and `J₁` on a real vector bundle `V` satisfy `J₁ b v ≠ -J₀ b v` for every
nonzero `v`, the complex vector bundles they define have the same clutching number homomorphism,
since `J₀ + J₁` is an isomorphism between them
(`TauCeti.Bundle.ContinuousComplexStructure.fiberCongr`). This applies to any two almost complex
structures tamed by a common symplectic form. -/
theorem Bundle.ContinuousComplexStructure.clutchingNumberHom_eq_of_injective_add
    (J₀ J₁ : Bundle.ContinuousComplexStructure F₀ V) (h : ∀ b, Function.Injective (J₀ b + J₁ b))
    (x : X) :
    clutchingNumberHom F J₁.Fiber x = clutchingNumberHom F J₀.Fiber x :=
  clutchingNumberHom_eq_of_continuousLinearEquiv (J₀.fiberCongr J₁ h)
    (J₀.continuous_fiberCongr F J₁ h) x

end ComplexStructure

end TauCeti
