/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.GeneralLinearGroup.Connected
public import TauCeti.Topology.VectorBundle.Complex.RelativeClutching

/-!
# The clutching number of a complex vector bundle over a torus

Let `E` be a complex vector bundle over a space `X`, with finite-dimensional model fibre `F`. A map
of the torus to `X` is read, as for the area condition `TauCeti.VanishesOnTori`, as a map
`u : I² → X` of the square that agrees on opposite edges, `u (1, t) = u (0, t)` and
`u (s, 1) = u (s, 0)`. This file defines the first Chern number `c₁(u^* E)[T²]` of the pulled-back
bundle by clutching (`TauCeti.torusClutchingNumber`), the torus counterpart of the clutching
number `TauCeti.clutchingNumber` of a sphere.

The pulled-back bundle over the torus is trivial over the square, which is the torus cut open along
two circles, and over the union `S¹ ∨ S¹` of these circles. A **torus frame** along `u`
(`TauCeti.IsTorusFrame`) is a frame of `E` along `u` continuous on the boundary `∂I²` that takes the
same values on opposite edges, so that it is a frame over `S¹ ∨ S¹`. The clutching number of the
torus is the relative clutching number of the square relative to a torus frame,
`TauCeti.relativeClutchingNumber u τ`: the winding number around `∂I²` of the determinant of the
transition from a frame over the square to `τ`. It is the clutching description of `c₁` on a closed
surface: a frame over a disc and a frame over the complement of the disc, compared along the
boundary circle.

* **Independence of the torus frame.** Two torus frames `τ` and `τ'` give the same relative
  clutching number (`TauCeti.IsTorusFrame.relativeClutchingNumber_eq`): the transition from `τ` to
  `τ'` also agrees on opposite edges, and a circle-valued map on `∂I²` agreeing on opposite edges
  has degree `0` (`TauCeti.squareBoundaryDegree_eq_zero_of_periodic`), since the boundary of the
  square runs along each circle of the torus once in each direction.
* **Existence of torus frames.** Every map of the torus has a torus frame
  (`TauCeti.exists_isTorusFrame`), and so does every homotopy through maps of the torus, as a family
  continuous in the time of the homotopy (`TauCeti.exists_isTorusFrame_homotopy`). Starting from a
  frame `Φ` over the whole square, the frame `Φ (1, t)` differs from `Φ (0, t)` by an automorphism
  `A t` of `F`, and `Φ (s, 1)` from `Φ (s, 0)` by `B s`. Composing `Φ` on the left and bottom edges
  with paths of automorphisms from `1` to `B 0` and to `A 0`, which exist because the group of
  automorphisms of `F` is path connected
  (`ContinuousLinearEquiv.exists_continuous_path_refl_family`), and on the right and top edges with
  the same paths followed by `A t` and `B s`, gives a torus frame. At the corner `(1, 1)` the two
  prescriptions agree because `A` and `B` both compare frames at the four corners.
* **Homotopy invariance.** Homotopic maps of the torus, through maps of the torus, have the same
  clutching number (`TauCeti.torusClutchingNumber_eq_of_homotopy`).
* **Spheres.** A sphere `p`, a map of the square sending its boundary to a point, is a map of the
  torus, and its torus clutching number is its clutching number
  (`TauCeti.torusClutchingNumber_eq_clutchingNumber`). This is the value of `c₁` on the torus
  mapped to the sphere by collapsing `S¹ ∨ S¹`, a map of degree one.
* **Bundle maps.** Semilinear bundle maps carry torus frames to torus frames
  (`TauCeti.IsTorusFrame.map`). Complex-linear bundle maps preserve torus clutching numbers
  (`TauCeti.torusClutchingNumber_map_of_continuousLinearEquiv`) and conjugate-linear ones reverse
  them (`TauCeti.torusClutchingNumber_map_of_conjugateLinear`). In particular a complex vector
  bundle with a real structure, a conjugate-linear automorphism of the bundle covering the identity,
  has torus clutching number `0` on every map of the torus
  (`TauCeti.torusClutchingNumber_eq_zero_of_conjugateLinear`).

For a symplectic manifold, the vanishing of the first Chern number on all maps of the torus is the
Chern half of symplectic atoroidality, under which Hamiltonian Floer theory is graded on all free
homotopy classes of loops.

## Main definitions

* `TauCeti.IsTorusFrame u τ`: `τ` is a frame of `E` along `u`, continuous on `∂I²` and agreeing on
  opposite edges.
* `TauCeti.torusClutchingNumber F E u`: the first Chern number of `E` on the torus `u`.

## Main results

* `TauCeti.IsTorusFrame.apply_right_eq_left`, `TauCeti.IsTorusFrame.apply_top_eq_bottom`: a map
  of the square with a torus frame agrees on opposite edges.
* `TauCeti.IsTorusFrame.relativeClutchingNumber_eq`: independence of the torus frame.
* `TauCeti.exists_isTorusFrame_homotopy`, `TauCeti.exists_isTorusFrame`: torus frames exist along
  homotopies of maps of the torus and along maps of the torus.
* `TauCeti.IsTorusFrame.torusClutchingNumber_eq`: the torus clutching number is the relative
  clutching number relative to any torus frame.
* `TauCeti.torusClutchingNumber_eq_zero_of_not_periodic`: the value `0` off maps of the torus.
* `TauCeti.torusClutchingNumber_eq_of_homotopy`: homotopy invariance.
* `TauCeti.torusClutchingNumber_eq_clutchingNumber`: comparison with spheres.
* `TauCeti.IsTorusFrame.map`: bundle maps carry torus frames to torus frames.
* `TauCeti.torusClutchingNumber_map_of_continuousLinearEquiv`,
  `TauCeti.torusClutchingNumber_map_of_conjugateLinear`,
  `TauCeti.torusClutchingNumber_eq_zero_of_conjugateLinear`: bundle maps and real structures.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Appendix C.1 (the first Chern number of a bundle over a closed surface by clutching).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.2 (symplectic atoroidality,
  `f^*[ω] = f^*(2c₁) = 0` on tori) and §4.2 (the cotangent bundle).
-/

public section

noncomputable section

open Bundle Set
open scoped unitInterval Topology.Homotopy

namespace TauCeti

variable {X : Type*} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]

variable [TopologicalSpace X] [FiniteDimensional ℂ F]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)]

/-- The finite-dimensional model fibre is complete, as `TauCeti.exists_continuous_frame` needs. -/
private local instance : CompleteSpace F := FiniteDimensional.completeSpace ℂ F

/-! ### Torus frames -/

/-- A **torus frame** of `E` along a map `u : I² → X` of the square: a family of complex-linear
isomorphisms `τ y : F ≃ E (u y)`, continuous along the boundary `∂I²` of the square, that takes the
same values on opposite edges, read as points of the total space. When `u` agrees on opposite
edges, so that it is a map of the torus, such a `τ` is a frame of the pulled-back bundle over the
two circles `S¹ ∨ S¹` of the torus along which the square is glued. -/
structure IsTorusFrame (u : C(Fin 2 → I, X)) (τ : ∀ y, F ≃L[ℂ] E (u y)) : Prop where
  /-- The frame is continuous along the boundary of the square. -/
  continuousOn :
    ContinuousOn (fun q : (Fin 2 → I) × F ↦ TotalSpace.mk' F (u q.1) (τ q.1 q.2))
      (Cube.boundary (Fin 2) ×ˢ univ)
  /-- The frame agrees on the right and left edges. -/
  right_eq_left (t : I) (v : F) :
    TotalSpace.mk' F (u ![1, t]) (τ ![1, t] v) = TotalSpace.mk' F (u ![0, t]) (τ ![0, t] v)
  /-- The frame agrees on the top and bottom edges. -/
  top_eq_bottom (s : I) (v : F) :
    TotalSpace.mk' F (u ![s, 1]) (τ ![s, 1] v) = TotalSpace.mk' F (u ![s, 0]) (τ ![s, 0] v)

omit [FiniteDimensional ℂ F] [FiberBundle F E] [VectorBundle ℂ F E]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)] in
/-- A map of the square with a torus frame agrees on the right and left edges. -/
theorem IsTorusFrame.apply_right_eq_left {u : C(Fin 2 → I, X)} {τ : ∀ y, F ≃L[ℂ] E (u y)}
    (hτ : IsTorusFrame u τ) (t : I) : u ![1, t] = u ![0, t] :=
  congrArg TotalSpace.proj (hτ.right_eq_left t 0)

omit [FiniteDimensional ℂ F] [FiberBundle F E] [VectorBundle ℂ F E]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)] in
/-- A map of the square with a torus frame agrees on the top and bottom edges. -/
theorem IsTorusFrame.apply_top_eq_bottom {u : C(Fin 2 → I, X)} {τ : ∀ y, F ≃L[ℂ] E (u y)}
    (hτ : IsTorusFrame u τ) (s : I) : u ![s, 1] = u ![s, 0] :=
  congrArg TotalSpace.proj (hτ.top_eq_bottom s 0)

/-- **Independence of the torus frame.** Two torus frames along `u` have the same relative
clutching number. -/
theorem IsTorusFrame.relativeClutchingNumber_eq {u : C(Fin 2 → I, X)}
    {τ τ' : ∀ y, F ≃L[ℂ] E (u y)} (hτ : IsTorusFrame u τ) (hτ' : IsTorusFrame u τ') :
    relativeClutchingNumber u τ = relativeClutchingNumber u τ' := by
  obtain ⟨φ, hφ⟩ := exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous u)
  -- The transition from `τ` to `τ'` agrees on opposite edges, so its degree vanishes.
  have hper : squareBoundaryDegree (fun y ↦ ((τ' y).trans (τ y).symm).normalizedDet) = 0 :=
    squareBoundaryDegree_eq_zero_of_periodic
      (continuousOn_normalizedDet_trans_symm hτ.continuousOn hτ'.continuousOn)
      (fun t ↦ by
        rw [frame_trans_symm_eq_of_totalSpaceMk'_eq (hτ'.right_eq_left t) (hτ.right_eq_left t)])
      fun s ↦ by
        rw [frame_trans_symm_eq_of_totalSpaceMk'_eq (hτ'.top_eq_bottom s) (hτ.top_eq_bottom s)]
  have h : (fun y ↦ ((τ' y).trans (φ y).symm).normalizedDet) =
      (fun y ↦ ((τ' y).trans (τ y).symm).normalizedDet) *
        fun y ↦ ((τ y).trans (φ y).symm).normalizedDet :=
    funext fun y ↦
      (ContinuousLinearEquiv.normalizedDet_trans_symm_mul_trans (τ' y) (τ y) (φ y).symm).symm
  rw [relativeClutchingNumber_eq_squareBoundaryDegree u τ hφ,
    relativeClutchingNumber_eq_squareBoundaryDegree u τ' hφ, h,
    squareBoundaryDegree_mul
      (continuousOn_normalizedDet_trans_symm hτ.continuousOn hτ'.continuousOn)
      (continuousOn_normalizedDet_trans_symm hφ.continuousOn hτ.continuousOn), hper, zero_add]

/-! ### Existence of torus frames -/

/-- **Automorphisms along the boundary of the square twisted by `A` and `B`.** Given automorphisms
`A (r, t)` and `B (r, s)` of `F`, continuous in both variables, such that the two ways of going
around the corner `(1, 1)` agree, there are automorphisms `ψ (r, y)` along the boundary of the
square, continuous on `I × ∂I²`, with `ψ (r, (1, t)) = A (r, t) ∘ ψ (r, (0, t))` and
`ψ (r, (s, 1)) = B (r, s) ∘ ψ (r, (s, 0))`. They are paths from the identity to `A (r, 0)` along the
bottom edge and to `B (r, 0)` along the left edge, followed by `A` and `B` on the opposite edges. -/
private theorem exists_twisted_boundary {A B : I × I → F ≃L[ℂ] F}
    (hA : Continuous fun q ↦ (A q : F →L[ℂ] F)) (hB : Continuous fun q ↦ (B q : F →L[ℂ] F))
    (hAB : ∀ r, (B (r, 0)).trans (A (r, 1)) = (A (r, 0)).trans (B (r, 1))) :
    ∃ ψ : I × (Fin 2 → I) → F ≃L[ℂ] F,
      ContinuousOn (fun q ↦ (ψ q : F →L[ℂ] F)) (univ ×ˢ Cube.boundary (Fin 2)) ∧
      (∀ r t, ψ (r, ![1, t]) = (ψ (r, ![0, t])).trans (A (r, t))) ∧
      ∀ r s, ψ (r, ![s, 1]) = (ψ (r, ![s, 0])).trans (B (r, s)) := by
  obtain ⟨L, hLc, hL0, hL1⟩ := ContinuousLinearEquiv.exists_continuous_path_refl_family
    (K := fun r ↦ B (r, 0)) (hB.comp (by fun_prop))
  obtain ⟨D, hDc, hD0, hD1⟩ := ContinuousLinearEquiv.exists_continuous_path_refl_family
    (K := fun r ↦ A (r, 0)) (hA.comp (by fun_prop))
  classical
  -- `D` on the bottom edge, `L` on the left edge, `L` followed by `A` on the right edge and `D`
  -- followed by `B` on the top edge.
  let ψ (q : I × (Fin 2 → I)) : F ≃L[ℂ] F :=
    if q.2 1 = 0 then D q.1 (q.2 0)
    else if q.2 0 = 0 then L q.1 (q.2 1)
    else if q.2 0 = 1 then (L q.1 (q.2 1)).trans (A (q.1, q.2 1))
    else (D q.1 (q.2 0)).trans (B (q.1, q.2 0))
  have hψB : EqOn ψ (fun q ↦ D q.1 (q.2 0)) {q | q.2 1 = 0} := fun q (hq : q.2 1 = 0) ↦ by
    simp [ψ, hq]
  have hψL : EqOn ψ (fun q ↦ L q.1 (q.2 1)) {q | q.2 0 = 0} := fun q (hq : q.2 0 = 0) ↦ by
    by_cases h1 : q.2 1 = 0 <;> simp [ψ, h1, hq, hD0, hL0]
  have hψR : EqOn ψ (fun q ↦ (L q.1 (q.2 1)).trans (A (q.1, q.2 1))) {q | q.2 0 = 1} :=
    fun q (hq : q.2 0 = 1) ↦ by
      by_cases h1 : q.2 1 = 0
      · ext v
        simp [ψ, h1, hq, hD1, hL0]
      · simp [ψ, h1, hq]
  have hψT : EqOn ψ (fun q ↦ (D q.1 (q.2 0)).trans (B (q.1, q.2 0))) {q | q.2 1 = 1} :=
    fun q (hq : q.2 1 = 1) ↦ by
      by_cases h0 : q.2 0 = 0
      · ext v
        simp [ψ, hq, h0, hL1, hD0]
      · by_cases h1 : q.2 0 = 1
        · simp [ψ, hq, h1, hL1, hD1, hAB]
        · simp [ψ, hq, h0, h1]
  have h0 : Continuous fun q : I × (Fin 2 → I) ↦ (q.1, q.2 0) := by fun_prop
  have h1 : Continuous fun q : I × (Fin 2 → I) ↦ (q.1, q.2 1) := by fun_prop
  refine ⟨ψ, continuousOn_boundary_of_edges ?_ ?_ ?_ ?_, fun r t ↦ ?_, fun r s ↦ ?_⟩
  · exact (hDc.comp h0).continuousOn.congr fun q hq ↦ by simp [hψB hq]
  · exact (hLc.comp h1).continuousOn.congr fun q hq ↦ by simp [hψL hq]
  · exact ((hA.comp h1).clm_comp (hLc.comp h1)).continuousOn.congr
      fun q hq ↦ by simp [hψR hq]
  · exact ((hB.comp h0).clm_comp (hDc.comp h0)).continuousOn.congr
      fun q hq ↦ by simp [hψT hq]
  · simp [hψR (by simp : (r, ![1, t]).2 0 = 1), hψL (by simp : (r, ![0, t]).2 0 = 0)]
  · simp [hψT (by simp : (r, ![s, 1]).2 1 = 1), hψB (by simp : (r, ![s, 0]).2 1 = 0)]

/-- **Torus frames along homotopies.** Let `H : I × I² → X` be a homotopy through maps of the
torus: each `H (r, ·)` agrees on opposite edges of the square. Then there is a family `T` of frames
along `H`, continuous over `I × ∂I²`, such that each `T (r, ·)` is a torus frame along
`H (r, ·)`. -/
theorem exists_isTorusFrame_homotopy (H : C(I × (Fin 2 → I), X))
    (hR : ∀ r t, H (r, ![1, t]) = H (r, ![0, t])) (hT : ∀ r s, H (r, ![s, 1]) = H (r, ![s, 0])) :
    ∃ T : ∀ q, F ≃L[ℂ] E (H q),
      ContinuousOn (fun q : (I × (Fin 2 → I)) × F ↦ TotalSpace.mk' F (H q.1) (T q.1 q.2))
        ((univ ×ˢ Cube.boundary (Fin 2)) ×ˢ univ) ∧
      ∀ r, IsTorusFrame (H.curry r) fun y ↦ T (r, y) := by
  have : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  obtain ⟨Φ, hΦ⟩ := exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous H)
  have hedge (k : I → Fin 2 → I) (hk : Continuous k) :
      Continuous fun p : (I × I) × F ↦
        TotalSpace.mk' F (H (p.1.1, k p.1.2)) (Φ (p.1.1, k p.1.2) p.2) :=
    hΦ.comp ((continuous_fst.fst.prodMk (hk.comp continuous_fst.snd)).prodMk continuous_snd)
  -- The seam transitions: `Φ (r, (1, t)) ∘ A (r, t)` is `Φ (r, (0, t))`, and
  -- `Φ (r, (s, 1)) ∘ B (r, s)` is `Φ (r, (s, 0))`.
  obtain ⟨A, hAc, hA⟩ := exists_continuous_transition_of_continuous_frame
    (f := fun q : I × I ↦ H (q.1, ![0, q.2]))
    (g := fun q ↦ H (q.1, ![1, q.2])) (fun q ↦ (hR q.1 q.2).symm)
    (φ := fun q ↦ Φ (q.1, ![0, q.2])) (ψ := fun q ↦ Φ (q.1, ![1, q.2]))
    (hedge (fun t ↦ ![0, t]) (by fun_prop)) (hedge (fun t ↦ ![1, t]) (by fun_prop))
  obtain ⟨B, hBc, hB⟩ := exists_continuous_transition_of_continuous_frame
    (f := fun q : I × I ↦ H (q.1, ![q.2, 0]))
    (g := fun q ↦ H (q.1, ![q.2, 1])) (fun q ↦ (hT q.1 q.2).symm)
    (φ := fun q ↦ Φ (q.1, ![q.2, 0])) (ψ := fun q ↦ Φ (q.1, ![q.2, 1]))
    (hedge (fun s ↦ ![s, 0]) (by fun_prop)) (hedge (fun s ↦ ![s, 1]) (by fun_prop))
  -- At the corner `(1, 1)` both ways around the seams compare `Φ` there with `Φ` at `(0, 0)`.
  have hAB (r : I) : (B (r, 0)).trans (A (r, 1)) = (A (r, 0)).trans (B (r, 1)) :=
    eq_of_frame_comp_totalSpaceMk'_eq (φ := Φ (r, ![1, 1])) (φ' := Φ (r, ![0, 0]))
      (fun v ↦ (hA (r, 1) (B (r, 0) v)).trans (hB (r, 0) v))
      fun v ↦ (hB (r, 1) (A (r, 0) v)).trans (hA (r, 0) v)
  obtain ⟨ψ, hψc, hψR, hψT⟩ := exists_twisted_boundary hAc hBc hAB
  have hT : ContinuousOn (fun q : (I × (Fin 2 → I)) × F ↦
      TotalSpace.mk' F (H q.1) ((ψ q.1).trans (Φ q.1) q.2))
        ((univ ×ˢ Cube.boundary (Fin 2)) ×ˢ univ) :=
    hΦ.comp_continuousOn (continuousOn_fst.prodMk
      ((hψc.comp continuousOn_fst
        fun q (hq : q ∈ (univ ×ˢ Cube.boundary (Fin 2)) ×ˢ univ) ↦ hq.1).clm_apply
          continuousOn_snd))
  refine ⟨fun q ↦ (ψ q).trans (Φ q), hT, fun r ↦ ⟨?_, fun t v ↦ ?_, fun s v ↦ ?_⟩⟩
  · exact hT.comp ((Continuous.prodMk_right r).prodMap continuous_id).continuousOn
      fun q (hq : q ∈ Cube.boundary (Fin 2) ×ˢ univ) ↦ ⟨⟨mem_univ _, hq.1⟩, mem_univ _⟩
  · -- On the right edge the frame is `Φ ∘ A ∘ ψ (r, (0, t))`, which is `Φ ∘ ψ` on the left edge.
    exact (congrArg (fun g : F ≃L[ℂ] F ↦
      TotalSpace.mk' F (H (r, ![1, t])) (Φ (r, ![1, t]) (g v))) (hψR r t)).trans (hA (r, t) _)
  · exact (congrArg (fun g : F ≃L[ℂ] F ↦
      TotalSpace.mk' F (H (r, ![s, 1])) (Φ (r, ![s, 1]) (g v))) (hψT r s)).trans (hB (r, s) _)

/-- **Torus frames exist.** A map of the square that agrees on opposite edges has a torus frame. -/
theorem exists_isTorusFrame (u : C(Fin 2 → I, X)) (hR : ∀ t, u ![1, t] = u ![0, t])
    (hT : ∀ s, u ![s, 1] = u ![s, 0]) : ∃ τ : ∀ y, F ≃L[ℂ] E (u y), IsTorusFrame u τ := by
  obtain ⟨T, -, hT'⟩ := exists_isTorusFrame_homotopy (F := F) (E := E)
    (u.comp ContinuousMap.snd) (fun _ t ↦ hR t) fun _ s ↦ hT s
  exact ⟨_, hT' 0⟩

/-! ### The clutching number of a torus -/

variable (F E) in
open Classical in
/-- The **clutching number of a torus**: the first Chern number of `E` on a map `u : I² → X` of the
square agreeing on opposite edges, read as a map of the torus. It is the relative clutching number
of `E` along `u` relative to any torus frame
(`TauCeti.IsTorusFrame.torusClutchingNumber_eq`), and torus frames exist exactly when `u` agrees
on opposite edges (`TauCeti.exists_isTorusFrame`, `TauCeti.IsTorusFrame.apply_right_eq_left`,
`TauCeti.IsTorusFrame.apply_top_eq_bottom`). Otherwise it is `0`
(`TauCeti.torusClutchingNumber_eq_zero_of_not_periodic`). -/
def torusClutchingNumber (u : C(Fin 2 → I, X)) : ℤ :=
  if h : ∃ τ : ∀ y, F ≃L[ℂ] E (u y), IsTorusFrame u τ then relativeClutchingNumber u h.choose
  else 0

/-- The torus clutching number is the relative clutching number relative to any torus frame. -/
theorem IsTorusFrame.torusClutchingNumber_eq {u : C(Fin 2 → I, X)} {τ : ∀ y, F ≃L[ℂ] E (u y)}
    (hτ : IsTorusFrame u τ) : torusClutchingNumber F E u = relativeClutchingNumber u τ := by
  have h : ∃ τ : ∀ y, F ≃L[ℂ] E (u y), IsTorusFrame u τ := ⟨τ, hτ⟩
  rw [torusClutchingNumber, dite_eq_left h]
  exact h.choose_spec.relativeClutchingNumber_eq hτ

/-- The torus clutching number of a map of the square that does not agree on opposite edges, and
so is not a map of the torus, is `0`. -/
theorem torusClutchingNumber_eq_zero_of_not_periodic {u : C(Fin 2 → I, X)}
    (h : ¬((∀ t, u ![1, t] = u ![0, t]) ∧ ∀ s, u ![s, 1] = u ![s, 0])) :
    torusClutchingNumber F E u = 0 :=
  dite_eq_right fun ⟨_, hτ⟩ ↦ h ⟨hτ.apply_right_eq_left, hτ.apply_top_eq_bottom⟩

/-- **Homotopy invariance.** If `H : I × I² → X` is a homotopy through maps of the torus, the two
ends `H (0, ·)` and `H (1, ·)` have the same torus clutching number. -/
theorem torusClutchingNumber_eq_of_homotopy (H : C(I × (Fin 2 → I), X))
    (hR : ∀ r t, H (r, ![1, t]) = H (r, ![0, t])) (hT : ∀ r s, H (r, ![s, 1]) = H (r, ![s, 0])) :
    torusClutchingNumber F E (H.curry 0) = torusClutchingNumber F E (H.curry 1) := by
  obtain ⟨T, hTc, hT'⟩ := exists_isTorusFrame_homotopy (F := F) (E := E) H hR hT
  rw [(hT' 0).torusClutchingNumber_eq, (hT' 1).torusClutchingNumber_eq]
  exact relativeClutchingNumber_eq_of_homotopy H hTc

/-- **Comparison with spheres.** A sphere `p` based at `x`, which sends the boundary of the square
to `x`, is a map of the torus, and its torus clutching number is its clutching number: the frame of
a trivialization of `E` near `x` is a torus frame along `p`. -/
theorem torusClutchingNumber_eq_clutchingNumber {x : X} (p : Ω^ (Fin 2) X x) :
    torusClutchingNumber F E p.val = clutchingNumber F E p := by
  classical
  set e := trivializationAt F E x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F E x
  obtain ⟨φ, -⟩ := exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous p)
  -- The frame of `e`, where it is defined.
  let τ (y : Fin 2 → I) : F ≃L[ℂ] E (p y) :=
    if hy : p y ∈ e.baseSet then (e.continuousLinearEquivAt ℂ (p y) hy).symm else φ y
  have hτ (y : Fin 2 → I) (hy : y ∈ Cube.boundary (Fin 2)) (v : F) :
      TotalSpace.mk' F (p y) (τ y v) = e.toOpenPartialHomeomorph.symm (x, v) := by
    have hpy : p y = x := GenLoop.boundary p y hy
    have hy' : p y ∈ e.baseSet := mem_of_eq_of_mem hpy hx
    simp only [τ, dite_eq_left hy', Trivialization.symm_continuousLinearEquivAt_eq,
      Trivialization.symmL_apply e hy']
    refine (e.mk_symm hy' v).trans ?_
    rw [hpy]
  have hR (t : I) : ![(1 : I), t] ∈ Cube.boundary (Fin 2) := ⟨0, Or.inr rfl⟩
  have hL (t : I) : ![(0 : I), t] ∈ Cube.boundary (Fin 2) := ⟨0, Or.inl rfl⟩
  have hTop (s : I) : ![s, (1 : I)] ∈ Cube.boundary (Fin 2) := ⟨1, Or.inr rfl⟩
  have hBot (s : I) : ![s, (0 : I)] ∈ Cube.boundary (Fin 2) := ⟨1, Or.inl rfl⟩
  have hframe : IsTorusFrame p.val τ :=
    { continuousOn := by
        refine (e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
          (continuous_const.prodMk continuous_snd)
            fun q ↦ e.mem_target.2 hx).continuousOn.congr fun q hq ↦ ?_
        exact hτ q.1 hq.1 q.2
      right_eq_left := fun t v ↦ (hτ _ (hR t) v).trans (hτ _ (hL t) v).symm
      top_eq_bottom := fun s v ↦ (hτ _ (hTop s) v).trans (hτ _ (hBot s) v).symm }
  rw [hframe.torusClutchingNumber_eq]
  refine (clutchingNumber_eq_relativeClutchingNumber p e hx fun y hy v ↦ ?_).symm
  rw [hτ y hy v]
  exact congrArg Prod.snd (e.apply_symm_apply' hx)

/-! ### Bundle maps -/

section Map

variable {Y : Type*} [TopologicalSpace Y]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F'] [FiniteDimensional ℂ F']
  {E' : Y → Type*} [∀ y, AddCommGroup (E' y)] [∀ y, Module ℂ (E' y)]
  [∀ y, TopologicalSpace (E' y)] [TopologicalSpace (TotalSpace F' E')] [FiberBundle F' E']
  [VectorBundle ℂ F' E'] [∀ y, IsTopologicalAddGroup (E' y)] [∀ y, ContinuousSMul ℂ (E' y)]

omit [FiniteDimensional ℂ F] [FiberBundle F E] [VectorBundle ℂ F E]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)] [FiniteDimensional ℂ F']
  [FiberBundle F' E'] [VectorBundle ℂ F' E'] [∀ y, IsTopologicalAddGroup (E' y)]
  [∀ y, ContinuousSMul ℂ (E' y)] in
/-- **Bundle maps carry torus frames to torus frames.** Let `Φ x : E x ≃ E' (f x)` be
`σ₁₂`-semilinear isomorphisms covering a continuous map `f : X → Y`, continuous as a map of total
spaces, for instance complex-linear or conjugate-linear ones, and let `K : F ≃ F'` be a
`σ₁₂`-semilinear isomorphism of the model fibres. If `τ` is a torus
frame along `u`, then `Φ ∘ τ ∘ K⁻¹` is a torus frame along `f ∘ u`. -/
theorem IsTorusFrame.map {σ₁₂ σ₂₁ : ℂ →+* ℂ} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    {f : C(X, Y)} {Φ : ∀ x, E x ≃SL[σ₁₂] E' (f x)}
    (hΦ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F' (f v.proj) (Φ v.proj v.snd))
    (K : F ≃SL[σ₁₂] F') {u : C(Fin 2 → I, X)} {τ : ∀ y, F ≃L[ℂ] E (u y)}
    (hτ : IsTorusFrame u τ) :
    IsTorusFrame (f.comp u) fun y ↦ (K.symm.trans (τ y)).trans (Φ (u y)) where
  continuousOn := hΦ.comp_continuousOn (hτ.continuousOn.comp
    (continuousOn_fst.prodMk (K.symm.continuous.comp continuous_snd).continuousOn)
      fun q (hq : q ∈ Cube.boundary (Fin 2) ×ˢ univ) ↦ ⟨hq.1, mem_univ _⟩)
  right_eq_left t v := congrArg
    (fun w : TotalSpace F E ↦ TotalSpace.mk' F' (f w.proj) (Φ w.proj w.snd))
      (hτ.right_eq_left t (K.symm v))
  top_eq_bottom s v := congrArg
    (fun w : TotalSpace F E ↦ TotalSpace.mk' F' (f w.proj) (Φ w.proj w.snd))
      (hτ.top_eq_bottom s (K.symm v))

/-- **Complex-linear bundle maps preserve torus clutching numbers.** Let `Φ x : E x ≃ E' (f x)` be
complex-linear isomorphisms covering a continuous map `f : X → Y`, continuous as a map of total
spaces. For a map `u` of the torus, the torus clutching number of `E'` on `f ∘ u` is that of `E` on
`u`. The model fibres `F` and `F'` may differ. -/
theorem torusClutchingNumber_map_of_continuousLinearEquiv (f : C(X, Y))
    (Φ : ∀ x, E x ≃L[ℂ] E' (f x))
    (hΦ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F' (f v.proj) (Φ v.proj v.snd))
    (u : C(Fin 2 → I, X)) (hR : ∀ t, u ![1, t] = u ![0, t]) (hT : ∀ s, u ![s, 1] = u ![s, 0]) :
    torusClutchingNumber F' E' (f.comp u) = torusClutchingNumber F E u := by
  obtain ⟨τ, hτ⟩ := exists_isTorusFrame (F := F) (E := E) u hR hT
  -- The model fibres are identified through `τ` and `Φ` at a point and a trivialization of `E'`.
  let L : F ≃L[ℂ] F' := ((τ 0).trans (Φ (u 0))).trans
    ((trivializationAt F' E' (f (u 0))).continuousLinearEquivAt ℂ (f (u 0))
      (mem_baseSet_trivializationAt F' E' (f (u 0))))
  rw [(hτ.map hΦ L).torusClutchingNumber_eq, hτ.torusClutchingNumber_eq]
  exact relativeClutchingNumber_map_of_continuousLinearEquiv f Φ hΦ L u τ

/-- **Conjugate-linear bundle maps reverse torus clutching numbers.** Let `Φ x : E x ≃ E' (f x)` be
conjugate-linear isomorphisms covering a continuous map `f : X → Y`, continuous as a map of total
spaces. For a map `u` of the torus, the torus clutching number of `E'` on `f ∘ u` is the negative
of that of `E` on `u`. The model fibres `F` and `F'` may differ. -/
theorem torusClutchingNumber_map_of_conjugateLinear (f : C(X, Y))
    (Φ : ∀ x, E x ≃L⋆[ℂ] E' (f x))
    (hΦ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F' (f v.proj) (Φ v.proj v.snd))
    (u : C(Fin 2 → I, X)) (hR : ∀ t, u ![1, t] = u ![0, t]) (hT : ∀ s, u ![s, 1] = u ![s, 0]) :
    torusClutchingNumber F' E' (f.comp u) = -torusClutchingNumber F E u := by
  obtain ⟨τ, hτ⟩ := exists_isTorusFrame (F := F) (E := E) u hR hT
  -- The conjugate-linear isomorphism of the model fibres induced by `τ` and `Φ` at a point.
  let K : F ≃L⋆[ℂ] F' := ((τ 0).trans (Φ (u 0))).trans
    ((trivializationAt F' E' (f (u 0))).continuousLinearEquivAt ℂ (f (u 0))
      (mem_baseSet_trivializationAt F' E' (f (u 0))))
  rw [(hτ.map hΦ K).torusClutchingNumber_eq, hτ.torusClutchingNumber_eq]
  exact relativeClutchingNumber_map_of_conjugateLinear f Φ hΦ K u τ

end Map

/-- **A real structure kills torus clutching numbers.** If `E` has a real structure, a family of
conjugate-linear automorphisms `κ x` of the fibres that is continuous on the total space, then its
torus clutching number vanishes on every map of the torus. -/
theorem torusClutchingNumber_eq_zero_of_conjugateLinear (κ : ∀ x, E x ≃L⋆[ℂ] E x)
    (hκ : Continuous fun v : TotalSpace F E ↦ TotalSpace.mk' F v.proj (κ v.proj v.snd))
    (u : C(Fin 2 → I, X)) (hR : ∀ t, u ![1, t] = u ![0, t]) (hT : ∀ s, u ![s, 1] = u ![s, 0]) :
    torusClutchingNumber F E u = 0 := by
  have h := torusClutchingNumber_map_of_conjugateLinear (ContinuousMap.id X) κ hκ u hR hT
  rw [ContinuousMap.id_comp] at h
  omega

end TauCeti
