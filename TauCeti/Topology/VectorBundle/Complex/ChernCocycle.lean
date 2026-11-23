/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Kronecker
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Square
public import TauCeti.Topology.VectorBundle.Complex.Clutching
import TauCeti.Geometry.Convex.ConvexSpace.ContractibleSpaceStdSimplex
import TauCeti.Geometry.Convex.ConvexSpace.LocallyPathConnectedSpaceStdSimplex
import TauCeti.Topology.Circle.Degree.StdSimplex

/-!
# Clutching numbers factor through the Hurewicz map

Let `E` be a complex vector bundle over a space `X`, with finite-dimensional model fibre `F`. Its
clutching numbers `TauCeti.clutchingNumberHom F E x : π₂(X, x) → ℤ`, the first Chern numbers of `E`
on spheres, are defined sphere by sphere. This file shows that they come from one additive map on
integral singular homology: there is `P : H₂(X; ℤ) → ℤ` with

`P (hurewicz a) = clutchingNumberHom F E x a`

for every base point `x` and every `a ∈ π₂(X, x)`
(`TauCeti.exists_addMonoidHom_hurewiczIntHom_eq_clutchingNumberHom`). In particular the clutching
number of a sphere only depends on its Hurewicz class, and two families of spheres with the same
total homology class have the same total clutching number.

The map `P` is a multiple of the evaluation of an integral singular `2`-cocycle, the obstruction
cocycle of obstruction theory (Milnor–Stasheff, §12) for a frame of the determinant of `E`, built
from frames as follows:

* every point `v` gets the frame `F ≃ E v` of the trivialization at `v`, every singular simplex
  `σ` a continuous frame of `E` along `σ`, which exists because simplices are contractible
  (`TauCeti.exists_continuous_frame`);
* along an edge `s` of a singular `2`-simplex `σ`, the determinant of the frame of `σ` against the
  frame of `s` sweeps an angle, corrected at the ends by the arguments of the frames of the
  endpoints; around the boundary of `σ` these angles add up to `2π m(σ)` for an integer `m(σ)`,
  since the corrections make the ends match;
* the frame of `σ` may be replaced by any other continuous frame: their determinants differ by a
  map from the simplex to the circle, which lifts to `ℝ` because the simplex is simply connected,
  so it sweeps no total angle around the boundary;
* on the boundary of a singular `3`-simplex `τ`, compute all four integers with the frame of `τ`:
  each edge of `τ` then appears twice with opposite signs, so `m` vanishes on boundaries, and
  `m` descends to `P₀ : H₂(X; ℤ) → ℤ`.

On the triangulated cycle `GenLoop.squareChain p` of a sphere `p` (two triangles of the square
and twice the constant simplex at the base point), the frame of a whole square restricts to both
triangles, the diagonal cancels, and the remaining edges run once around the boundary of the
square, where the angle is the clutching function of `p`. So `P₀` takes the value
`clutchingNumber F E p` on the class `GenLoop.squareClass p`, which is a universal multiple `k` of
the Hurewicz class of `p` (`GenLoop.exists_forall_squareClass_eq_zsmul_hurewicz`), and `P = k • P₀`.

Only the values of `P` on Hurewicz classes are determined here: its values on other classes are
computed from the chosen frames, and no comparison with a cohomological first Chern class is
made.

## Main results

* `TauCeti.exists_addMonoidHom_hurewiczIntHom_eq_clutchingNumberHom`: the clutching numbers of a
  complex vector bundle factor through the integral Hurewicz map, uniformly in the base point.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (obstruction classes) and §14 (Chern classes).
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton (1951), Part III (obstruction theory).
-/

public section

noncomputable section

open AlgebraicTopology Bundle CategoryTheory Convexity Real Set Topology
open Convexity.StdSimplex (faceInclusion)
open Circle (sweptAngle sweptAngle_eq_sub exp_sweptAngle exists_sweptAngle_eq_sub sweptAngle_mul
  sweptAngle_comp_symm)
open scoped unitInterval Topology.Homotopy

namespace TauCeti

namespace ChernCocycle

/-! ### Frames at points and along simplices -/

variable {X : Type} [TopologicalSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)]

/-- The finite-dimensional model fibre is complete, as `TauCeti.exists_continuous_frame` needs. -/
private local instance : CompleteSpace F := FiniteDimensional.completeSpace ℂ F

variable (F) in
/-- The frame of `E` at a point `v`: the inverse of the trivialization at `v`. -/
private def pointFrame (v : X) : F ≃L[ℂ] E v :=
  ((trivializationAt F E v).continuousLinearEquivAt ℂ v
    (FiberBundle.mem_baseSet_trivializationAt' v)).symm

variable (F E) in
/-- A continuous frame of `E` along a singular simplex. -/
private def simplexFrame {n : ℕ} (s : C(StdSimplex ℝ (Fin (n + 1)), X)) :
    ∀ y, F ≃L[ℂ] E (s y) :=
  (exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) s.continuous).choose

variable (F E) in
private theorem continuous_simplexFrame {n : ℕ} (s : C(StdSimplex ℝ (Fin (n + 1)), X)) :
    Continuous fun q : StdSimplex ℝ (Fin (n + 1)) × F ↦
      TotalSpace.mk' F (s q.1) (simplexFrame F E s q.1 q.2) :=
  (exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) s.continuous).choose_spec

/-- The value at a point `y` of a frame `Φ` along `s`, compared with the frame of `E` at the point
`s y`: the normalized determinant of `(Φ y)⁻¹ ∘ pointFrame (s y)`. -/
private def vertexValue {B : Type*} (s : B → X) (Φ : ∀ y, F ≃L[ℂ] E (s y)) (y : B) : Circle :=
  ((pointFrame F (s y)).trans (Φ y).symm).normalizedDet

/-! ### The angle of an edge -/

/-- The **angle of an edge**: along a singular `1`-simplex `s` with a frame `Φ`, the angle swept by
the determinant of `Φ` against the chosen frame of `s`, corrected at both ends by the arguments of
the chosen frame against the frames of the endpoints. Its exponential is the quotient of the
values of `Φ` at the two ends (`exp_edgeAngle`). -/
private def edgeAngle (s : C(StdSimplex ℝ (Fin 2), X)) (Φ : ∀ z, F ≃L[ℂ] E (s z)) : ℝ :=
  sweptAngle (fun t ↦ ((simplexFrame F E s (StdSimplex.homeomorphI.symm t)).trans
      (Φ (StdSimplex.homeomorphI.symm t)).symm).normalizedDet) +
    Complex.arg (vertexValue s (simplexFrame F E s) (StdSimplex.single 1)) -
    Complex.arg (vertexValue s (simplexFrame F E s) (StdSimplex.single 0))

omit [FiniteDimensional ℂ F] [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)] in
/-- Comparing a frame with the frame of a point through an intermediate frame `Ψ`. -/
private theorem vertexValue_eq_mul {B : Type*} (s : B → X) (Φ Ψ : ∀ y, F ≃L[ℂ] E (s y)) (y : B) :
    vertexValue s Φ y =
      vertexValue s Ψ y * ((Ψ y).trans (Φ y).symm).normalizedDet :=
  (ContinuousLinearEquiv.normalizedDet_trans_symm_mul_trans (pointFrame F (s y)) (Ψ y)
    (Φ y).symm).symm

private theorem exp_edgeAngle (s : C(StdSimplex ℝ (Fin 2), X)) {Φ : ∀ z, F ≃L[ℂ] E (s z)}
    (hΦ : Continuous fun q : StdSimplex ℝ (Fin 2) × F ↦ TotalSpace.mk' F (s q.1) (Φ q.1 q.2)) :
    Circle.exp (edgeAngle s Φ) =
      vertexValue s Φ (StdSimplex.single 1) / vertexValue s Φ (StdSimplex.single 0) := by
  have hw : Continuous fun t ↦ ((simplexFrame F E s (StdSimplex.homeomorphI.symm t)).trans
      (Φ (StdSimplex.homeomorphI.symm t)).symm).normalizedDet :=
    (continuous_normalizedDet_trans_symm hΦ (continuous_simplexFrame F E s)).comp
      StdSimplex.homeomorphI.symm.continuous
  rw [edgeAngle, Circle.exp_sub, Circle.exp_add, exp_sweptAngle hw, Circle.exp_arg,
    Circle.exp_arg, vertexValue_eq_mul s Φ (simplexFrame F E s),
    vertexValue_eq_mul s Φ (simplexFrame F E s)]
  rw [StdSimplex.homeomorphI_symm_one, StdSimplex.homeomorphI_symm_zero]
  simp only [div_eq_mul_inv, mul_inv]
  ac_rfl

/-- **Change of frame along an edge.** Replacing the frame `Φ` by `Φ'` changes the angle of an
edge by the angle swept by the determinant of `Φ'` against `Φ`. -/
private theorem edgeAngle_eq_add (s : C(StdSimplex ℝ (Fin 2), X)) {Φ Φ' : ∀ z, F ≃L[ℂ] E (s z)}
    (hΦ : Continuous fun q : StdSimplex ℝ (Fin 2) × F ↦ TotalSpace.mk' F (s q.1) (Φ q.1 q.2))
    (hΦ' : Continuous fun q : StdSimplex ℝ (Fin 2) × F ↦ TotalSpace.mk' F (s q.1) (Φ' q.1 q.2)) :
    edgeAngle s Φ' = edgeAngle s Φ + sweptAngle (fun t ↦
      ((Φ (StdSimplex.homeomorphI.symm t)).trans
        (Φ' (StdSimplex.homeomorphI.symm t)).symm).normalizedDet) := by
  have hw : Continuous fun t ↦ ((simplexFrame F E s (StdSimplex.homeomorphI.symm t)).trans
      (Φ (StdSimplex.homeomorphI.symm t)).symm).normalizedDet :=
    (continuous_normalizedDet_trans_symm hΦ (continuous_simplexFrame F E s)).comp
      StdSimplex.homeomorphI.symm.continuous
  have hg : Continuous fun t ↦ ((Φ (StdSimplex.homeomorphI.symm t)).trans
      (Φ' (StdSimplex.homeomorphI.symm t)).symm).normalizedDet :=
    (continuous_normalizedDet_trans_symm hΦ' hΦ).comp StdSimplex.homeomorphI.symm.continuous
  have hmul : (fun t ↦ ((simplexFrame F E s (StdSimplex.homeomorphI.symm t)).trans
      (Φ' (StdSimplex.homeomorphI.symm t)).symm).normalizedDet) =
      (fun t ↦ ((simplexFrame F E s (StdSimplex.homeomorphI.symm t)).trans
        (Φ (StdSimplex.homeomorphI.symm t)).symm).normalizedDet) *
      fun t ↦ ((Φ (StdSimplex.homeomorphI.symm t)).trans
        (Φ' (StdSimplex.homeomorphI.symm t)).symm).normalizedDet := by
    funext t
    rw [Pi.mul_apply]
    exact (ContinuousLinearEquiv.normalizedDet_trans_symm_mul_trans _ _ _).symm
  rw [edgeAngle, edgeAngle, hmul, sweptAngle_mul hw hg]
  ring

omit [TopologicalSpace X] [FiniteDimensional ℂ F] [FiberBundle F E] [VectorBundle ℂ F E]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)] in
/-- A continuous frame along `s` restricts to a continuous frame along `s ∘ k`. -/
private theorem continuous_frame_comp {B B' : Type*} [TopologicalSpace B] [TopologicalSpace B']
    {s : B → X} {Φ : ∀ y, F ≃L[ℂ] E (s y)}
    (hΦ : Continuous fun q : B × F ↦ TotalSpace.mk' F (s q.1) (Φ q.1 q.2)) {k : B' → B}
    (hk : Continuous k) :
    Continuous fun q : B' × F ↦ TotalSpace.mk' F (s (k q.1)) (Φ (k q.1) q.2) :=
  hΦ.comp (hk.prodMap continuous_id)

/-! ### The angle around a triangle -/

/-- The **angle around a singular `2`-simplex** `s` with a frame `Φ`: the alternating sum of the
angles of its three edges, with the restrictions of `Φ`. It is an integer multiple of `2π`
(`exp_triangleAngle`) and does not depend on `Φ` (`triangleAngle_eq`). -/
private def triangleAngle (s : C(StdSimplex ℝ (Fin 3), X)) (Φ : ∀ y, F ≃L[ℂ] E (s y)) : ℝ :=
  ∑ i : Fin 3, (-1 : ℝ) ^ (i : ℕ) *
    edgeAngle (s.comp (faceInclusion i)) fun z ↦ Φ (faceInclusion i z)

private theorem exp_triangleAngle (s : C(StdSimplex ℝ (Fin 3), X)) {Φ : ∀ y, F ≃L[ℂ] E (s y)}
    (hΦ : Continuous fun q : StdSimplex ℝ (Fin 3) × F ↦ TotalSpace.mk' F (s q.1) (Φ q.1 q.2)) :
    Circle.exp (triangleAngle s Φ) = 1 := by
  have he (i : Fin 3) := exp_edgeAngle (s.comp (faceInclusion i))
    (Φ := fun z ↦ Φ (faceInclusion i z)) (continuous_frame_comp hΦ (faceInclusion i).continuous)
  -- The ends of the edges are the vertices of `s`.
  have hv (i : Fin 3) (k : Fin 2) :
      vertexValue (s.comp (faceInclusion i)) (fun z ↦ Φ (faceInclusion i z)) (StdSimplex.single k) =
        vertexValue s Φ (StdSimplex.single (i.succAbove k)) := by
    rw [← StdSimplex.faceInclusion_single]
    -- `s.comp (faceInclusion i)` evaluates to `s ∘ faceInclusion i` by definition of
    -- `ContinuousMap.comp`.
    rfl
  simp only [hv] at he
  simp only [triangleAngle, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero,
    pow_one, one_mul, neg_one_mul, neg_one_sq, Circle.exp_add, Circle.exp_neg, he]
  simp [Fin.succAbove, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- **The angle around a triangle does not depend on the frame.** Two continuous frames along a
singular `2`-simplex give the same angle around it. -/
private theorem triangleAngle_eq (s : C(StdSimplex ℝ (Fin 3), X)) {Φ Φ' : ∀ y, F ≃L[ℂ] E (s y)}
    (hΦ : Continuous fun q : StdSimplex ℝ (Fin 3) × F ↦ TotalSpace.mk' F (s q.1) (Φ q.1 q.2))
    (hΦ' : Continuous fun q : StdSimplex ℝ (Fin 3) × F ↦ TotalSpace.mk' F (s q.1) (Φ' q.1 q.2)) :
    triangleAngle s Φ' = triangleAngle s Φ := by
  have h0 := Circle.sum_sweptAngle_faceInclusion_eq_zero
    ⟨fun y ↦ ((Φ y).trans (Φ' y).symm).normalizedDet, continuous_normalizedDet_trans_symm hΦ' hΦ⟩
  simp only [ContinuousMap.coe_mk] at h0
  have he (i : Fin 3) := edgeAngle_eq_add (s.comp (faceInclusion i))
    (Φ := fun z ↦ Φ (faceInclusion i z)) (Φ' := fun z ↦ Φ' (faceInclusion i z))
    (continuous_frame_comp hΦ (faceInclusion i).continuous)
    (continuous_frame_comp hΦ' (faceInclusion i).continuous)
  simp only [triangleAngle, he, mul_add, Finset.sum_add_distrib]
  rw [h0, add_zero]

/-- **The angles around the faces of a `3`-simplex cancel.** For a singular `3`-simplex `τ`, the
alternating sum of the angles around its four faces, each with its own chosen frame, vanishes:
computed with the frame of `τ`, every edge of `τ` occurs in two faces with opposite signs. -/
private theorem sum_triangleAngle_faces (τ : C(StdSimplex ℝ (Fin 4), X)) :
    ∑ j : Fin 4, (-1 : ℝ) ^ (j : ℕ) *
      triangleAngle (τ.comp (faceInclusion j)) (simplexFrame F E (τ.comp (faceInclusion j))) =
        0 := by
  have hΦ := continuous_simplexFrame F E τ
  have hface (j : Fin 4) : triangleAngle (τ.comp (faceInclusion j))
      (simplexFrame F E (τ.comp (faceInclusion j))) =
      triangleAngle (τ.comp (faceInclusion j)) fun z ↦ simplexFrame F E τ (faceInclusion j z) :=
    triangleAngle_eq _ (continuous_frame_comp hΦ (faceInclusion j).continuous)
      (continuous_simplexFrame F E _)
  -- With the frame of `τ`, the angle of an edge only depends on its inclusion into `Δ³`.
  let T : C(StdSimplex ℝ (Fin 2), StdSimplex ℝ (Fin 4)) → ℝ := fun e ↦
    edgeAngle (τ.comp e) fun z ↦ simplexFrame F E τ (e z)
  have hT (j : Fin 4) (i : Fin 3) : edgeAngle ((τ.comp (faceInclusion j)).comp (faceInclusion i))
      (fun z ↦ simplexFrame F E τ (faceInclusion j (faceInclusion i z))) =
      T ((faceInclusion j).comp (faceInclusion i)) :=
    -- Composition of continuous maps is associative by definition of `ContinuousMap.comp`.
    rfl
  simp only [hface]
  simp only [triangleAngle, hT, Fin.sum_univ_four, Fin.sum_univ_three]
  rw [StdSimplex.faceInclusion_comp_faceInclusion (i := 0) (j := 1) (i' := 0) (j' := 0) (by decide),
    StdSimplex.faceInclusion_comp_faceInclusion (i := 0) (j := 2) (i' := 0) (j' := 1) (by decide),
    StdSimplex.faceInclusion_comp_faceInclusion (i := 1) (j := 2) (i' := 1) (j' := 1) (by decide),
    StdSimplex.faceInclusion_comp_faceInclusion (i := 0) (j := 3) (i' := 0) (j' := 2) (by decide),
    StdSimplex.faceInclusion_comp_faceInclusion (i := 1) (j := 3) (i' := 1) (j' := 2) (by decide),
    StdSimplex.faceInclusion_comp_faceInclusion (i := 2) (j := 3) (i' := 2) (j' := 2) (by decide)]
  norm_num
  ring

/-! ### The integral cochain and its class on homology -/

private theorem exists_triangleAngle_eq (s : C(StdSimplex ℝ (Fin 3), X)) :
    ∃ m : ℤ, triangleAngle s (simplexFrame F E s) = m * (2 * π) :=
  Circle.exp_eq_one.1 (exp_triangleAngle s (continuous_simplexFrame F E s))

variable (F E) in
/-- The **integer of a singular `2`-simplex**: the angle around it, in full turns. -/
private def triangleNumber (s : C(StdSimplex ℝ (Fin 3), X)) : ℤ :=
  (exists_triangleAngle_eq (F := F) (E := E) s).choose

private theorem triangleNumber_mul (s : C(StdSimplex ℝ (Fin 3), X)) :
    (triangleNumber F E s : ℝ) * (2 * π) = triangleAngle s (simplexFrame F E s) :=
  (exists_triangleAngle_eq s).choose_spec.symm

variable (F E) in
/-- The **clutching cochain**: the integral singular `2`-cochain with value `triangleNumber F E s`
on each singular `2`-simplex `s`. -/
private def clutchingCochain : ((singularChains ℤ).obj (TopCat.of X)).X 2 →ₗ[ℤ] ℤ :=
  chainsDesc fun s ↦ triangleNumber F E ((TopCat.of X).toSSetObjEquiv _ s)

private theorem clutchingCochain_simplexMapChain (s : C(StdSimplex ℝ (Fin 3), X)) :
    clutchingCochain F E (simplexMapChain ℤ s) = triangleNumber F E s := by
  rw [clutchingCochain, chainsDesc_simplexChain_one, Equiv.apply_symm_apply]

/-- **The clutching cochain is a cocycle**: it vanishes on boundaries. -/
private theorem clutchingCochain_d (c : ((singularChains ℤ).obj (TopCat.of X)).X 3) :
    clutchingCochain F E (((singularChains ℤ).obj (TopCat.of X)).d 3 2 c) = 0 := by
  refine LinearMap.congr_fun (singularChains_linearMap_ext
    (L := clutchingCochain F E ∘ₗ (((singularChains ℤ).obj (TopCat.of X)).d 3 2).hom) (L' := 0)
    fun τ ↦ ?_) c
  set τ' := (TopCat.of X).toSSetObjEquiv _ τ
  -- The faces of a singular simplex are its restrictions to the facets.
  have hδ (j : Fin 4) : (TopCat.of X).toSSetObjEquiv _ ((TopCat.toSSet.obj (TopCat.of X)).δ j τ) =
      τ'.comp (faceInclusion j) :=
    ContinuousMap.ext fun z ↦ (TopCat.toSSetObjEquiv_δ_apply τ j z).trans
      (congrArg τ' (StdSimplex.faceInclusion_apply j z).symm)
  rw [LinearMap.comp_apply, singularChains_d_simplexChain (n := 2), map_sum, LinearMap.zero_apply]
  simp only [map_zsmul, clutchingCochain, chainsDesc_simplexChain_one, hδ, smul_eq_mul]
  have h : ((∑ j : Fin 4, (-1 : ℤ) ^ (j : ℕ) * triangleNumber F E (τ'.comp (faceInclusion j)) :
      ℤ) : ℝ) * (2 * π) = 0 := by
    push_cast
    rw [Finset.sum_mul]
    simp only [mul_assoc, triangleNumber_mul]
    exact sum_triangleAngle_faces τ'
  exact_mod_cast (mul_eq_zero.1 h).resolve_right (by positivity)

variable (F E) in
private theorem d_next_comp_clutchingCochain :
    ((singularChains ℤ).obj (TopCat.of X)).d ((ComplexShape.up ℕ).next 2) 2 ≫
      ModuleCat.ofHom (clutchingCochain F E) = 0 := by
  rw [CochainComplex.next ℕ 2]
  ext c
  exact clutchingCochain_d c

variable (F E) in
/-- The evaluation of the class of the clutching cochain on integral singular homology. -/
private def clutchingHomologyHom : ((singularChains ℤ).obj (TopCat.of X)).homology 2 →+ ℤ :=
  (ChainComplex.kronecker ℤ ((singularChains ℤ).obj (TopCat.of X)) (ModuleCat.of ℤ ℤ) 2
    (ChainComplex.homologyClassOfComp ℤ (ModuleCat.of ℤ ℤ) (ModuleCat.ofHom (clutchingCochain F E))
      (d_next_comp_clutchingCochain F E) (𝟙 _))).hom.toAddMonoidHom

private theorem clutchingHomologyHom_homologyπ
    (z : ((singularChains ℤ).obj (TopCat.of X)).cycles 2) :
    clutchingHomologyHom F E ((((singularChains ℤ).obj (TopCat.of X)).homologyπ 2).hom z) =
      clutchingCochain F E ((((singularChains ℤ).obj (TopCat.of X)).iCycles 2).hom z) :=
  ConcreteCategory.congr_hom (ChainComplex.homologyπ_kronecker_homologyClassOfComp _ _ (𝟙 _)) z

/-! ### Edges along which the map is constant -/

omit [FiniteDimensional ℂ F] [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)] in
variable (F E) in
/-- The constant frame of the fibre at `x` is continuous. -/
private theorem continuous_pointFrame_const {B : Type*} [TopologicalSpace B] (x : X) :
    Continuous fun q : B × F ↦ TotalSpace.mk' F x (pointFrame F (E := E) x q.2) :=
  (FiberBundle.continuous_totalSpaceMk F E x).comp ((pointFrame F x).continuous.comp continuous_snd)

/-- **Edges at a point.** If the edge `s` is constant at `x`, its angle with a frame `Φ` is the
angle of the constant edge at `x` with the frame of `x`, plus the angle swept by the values of `Φ`
against the frame of `x`. -/
private theorem edgeAngle_eq_of_forall_eq {x : X} (s : C(StdSimplex ℝ (Fin 2), X))
    (hs : ∀ z, s z = x) {Φ : ∀ z, F ≃L[ℂ] E (s z)}
    (hΦ : Continuous fun q : StdSimplex ℝ (Fin 2) × F ↦ TotalSpace.mk' F (s q.1) (Φ q.1 q.2)) :
    edgeAngle s Φ = edgeAngle (ContinuousMap.const _ x) (fun _ ↦ pointFrame F (E := E) x) +
      sweptAngle (fun t ↦ vertexValue s Φ (StdSimplex.homeomorphI.symm t)) := by
  obtain rfl : s = ContinuousMap.const _ x := ContinuousMap.ext hs
  exact edgeAngle_eq_add _ (continuous_pointFrame_const F E x) hΦ

omit [FiniteDimensional ℂ F] [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)] in
/-- At a point over `x`, the value of a frame against the frame of `x` is the clutching function
of the frame in the trivialization at `x`. -/
private theorem vertexValue_eq_clutchingFunction {B : Type*} {s : B → X} (Φ : ∀ y, F ≃L[ℂ] E (s y))
    {x : X} {y : B} (hy : s y = x) :
    vertexValue s Φ y = clutchingFunction s Φ (trivializationAt F E x) y := by
  have hmem : s y ∈ (trivializationAt F E x).baseSet := by
    rw [hy]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  rw [clutchingFunction_of_mem hmem, vertexValue]
  -- Over the point `s y = x`, the frame of the point is the inverse of the trivialization at `x`.
  suffices ∀ (z : X) (_ : z = x) (A : F ≃L[ℂ] E z) (hm : z ∈ (trivializationAt F E x).baseSet),
      ((pointFrame F z).trans A.symm).normalizedDet =
        (A.trans ((trivializationAt F E x).continuousLinearEquivAt ℂ z hm)).normalizedDet⁻¹ from
    this _ hy _ _
  rintro z rfl A hm
  rw [← ContinuousLinearEquiv.normalizedDet_symm]
  rfl

/-! ### The value on the triangulated cycle of a sphere -/

/-- **The clutching number from the edges of the square.** For a continuous frame `φ` along a
sphere `p`, `2π` times the clutching number of `p` is the sum of the angles swept by the clutching
function of `φ` along the bottom, right, reversed top and reversed left edges of the square. -/
private theorem clutchingNumber_mul_two_pi_eq {x : X} (p : Ω^ (Fin 2) X x)
    {φ : ∀ y, F ≃L[ℂ] E (p y)}
    (hφ : Continuous fun q : (Fin 2 → I) × F ↦ TotalSpace.mk' F (p q.1) (φ q.1 q.2)) :
    (clutchingNumber F E p : ℝ) * (2 * π) =
      sweptAngle (fun t ↦ clutchingFunction p φ (trivializationAt F E x) ![t, 0]) +
        sweptAngle (fun t ↦ clutchingFunction p φ (trivializationAt F E x) ![1, t]) +
        sweptAngle (fun t ↦ clutchingFunction p φ (trivializationAt F E x) ![σ t, 1]) -
        sweptAngle (fun t ↦ clutchingFunction p φ (trivializationAt F E x) ![0, t]) := by
  have hx : x ∈ (trivializationAt F E x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  set Γ := clutchingFunction p φ (trivializationAt F E x)
  have hΓ : ContinuousOn Γ (Cube.boundary (Fin 2)) :=
    continuousOn_clutchingFunction_boundary p hφ _ hx
  obtain ⟨θB, hθB, hB, hsB⟩ := exists_sweptAngle_eq_sub (w := fun t ↦ Γ ![t, 0])
    (hΓ.comp_continuous (by fun_prop) fun t ↦ ⟨1, Or.inl rfl⟩)
  obtain ⟨θR, hθR, hR, hsR⟩ := exists_sweptAngle_eq_sub (w := fun t ↦ Γ ![1, t])
    (hΓ.comp_continuous (by fun_prop) fun t ↦ ⟨0, Or.inr rfl⟩)
  have hcT : Continuous fun t ↦ Γ ![t, 1] :=
    hΓ.comp_continuous (by fun_prop) fun t ↦ ⟨1, Or.inr rfl⟩
  obtain ⟨θT, hθT, hT, hsT⟩ := exists_sweptAngle_eq_sub hcT
  obtain ⟨θL, hθL, hL, hsL⟩ := exists_sweptAngle_eq_sub (w := fun t ↦ Γ ![0, t])
    (hΓ.comp_continuous (by fun_prop) fun t ↦ ⟨0, Or.inl rfl⟩)
  rw [clutchingNumber_eq_squareBoundaryDegree p _ hx hφ,
    squareBoundaryDegree_mul_two_pi_eq hΓ hθB hθR hθT hθL hB hR hT hL,
    sweptAngle_comp_symm (w := fun t ↦ Γ ![t, 1]) hcT, hsB, hsR, hsT, hsL]
  ring

/-- **Boundary edges of the square.** Let `c` be an edge of the square lying in its boundary,
parametrized by `g`. The angle of the edge `p ∘ c` of a sphere `p`, with the restriction of a frame
`φ` along `p`, is the angle of the constant edge at the base point plus the angle swept by the
clutching function of `φ` along `g`. -/
private theorem edgeAngle_comp_of_mem_boundary {x : X} (p : Ω^ (Fin 2) X x)
    {φ : ∀ y, F ≃L[ℂ] E (p y)}
    (hφ : Continuous fun q : (Fin 2 → I) × F ↦ TotalSpace.mk' F (p q.1) (φ q.1 q.2))
    (c : C(StdSimplex ℝ (Fin 2), I^(Fin 2))) {g : I → I^(Fin 2)}
    (hcg : ∀ t, c (StdSimplex.homeomorphI.symm t) = g t)
    (hg : ∀ t, g t ∈ Cube.boundary (Fin 2)) :
    edgeAngle ((p : C(I^(Fin 2), X)).comp c) (fun z ↦ φ (c z)) =
      edgeAngle (ContinuousMap.const _ x) (fun _ ↦ pointFrame F (E := E) x) +
        sweptAngle (fun t ↦ clutchingFunction p φ (trivializationAt F E x) (g t)) := by
  have hc (z : StdSimplex ℝ (Fin 2)) : c z ∈ Cube.boundary (Fin 2) := by
    have h := hg (StdSimplex.homeomorphI z)
    rwa [← hcg, Homeomorph.symm_apply_apply] at h
  rw [edgeAngle_eq_of_forall_eq _ (fun z ↦ GenLoop.boundary p _ (hc z))
    (continuous_frame_comp hφ c.continuous)]
  congr 2
  funext t
  rw [← hcg]
  exact vertexValue_eq_clutchingFunction φ (GenLoop.boundary p _ (hc _))

/-- The angle around a singular `2`-simplex `P ∘ S` that factors through a map `P` with a
continuous frame `φ` is the alternating sum of the angles of the edges `P ∘ S ∘ δᵢ`, with the
restrictions of `φ`. -/
private theorem triangleAngle_comp {Y : Type*} [TopologicalSpace Y] (P : C(Y, X))
    {φ : ∀ y, F ≃L[ℂ] E (P y)}
    (hφ : Continuous fun q : Y × F ↦ TotalSpace.mk' F (P q.1) (φ q.1 q.2))
    (S : C(StdSimplex ℝ (Fin 3), Y)) :
    triangleAngle (P.comp S) (simplexFrame F E _) =
      edgeAngle (P.comp (S.comp (faceInclusion 0))) (fun z ↦ φ (S.comp (faceInclusion 0) z)) -
        edgeAngle (P.comp (S.comp (faceInclusion 1))) (fun z ↦ φ (S.comp (faceInclusion 1) z)) +
        edgeAngle (P.comp (S.comp (faceInclusion 2))) (fun z ↦ φ (S.comp (faceInclusion 2) z)) := by
  rw [triangleAngle_eq _ (Φ := fun y ↦ φ (S y)) (continuous_frame_comp hφ S.continuous)
    (continuous_simplexFrame F E _)]
  simp only [triangleAngle, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero,
    pow_one, one_mul, neg_one_mul, neg_one_sq, ← sub_eq_add_neg]
  -- Composition of continuous maps is associative by definition of `ContinuousMap.comp`.
  rfl

/-- The angle around the constant `2`-simplex at `x` is the angle of the constant edge at `x`. -/
private theorem triangleAngle_const (x : X) :
    triangleAngle (ContinuousMap.const (StdSimplex ℝ (Fin 3)) x) (simplexFrame F E _) =
      edgeAngle (ContinuousMap.const _ x) (fun _ ↦ pointFrame F (E := E) x) := by
  rw [triangleAngle_eq _ (Φ := fun _ ↦ pointFrame F (E := E) x) (continuous_pointFrame_const F E x)
    (continuous_simplexFrame F E _)]
  have h (i : Fin 3) :
      edgeAngle ((ContinuousMap.const (StdSimplex ℝ (Fin 3)) x).comp (faceInclusion i))
        (fun _ ↦ pointFrame F (E := E) x) =
      edgeAngle (ContinuousMap.const _ x) (fun _ ↦ pointFrame F (E := E) x) := by
    rw [edgeAngle_eq_of_forall_eq
      ((ContinuousMap.const (StdSimplex ℝ (Fin 3)) x).comp (faceInclusion i)) (fun _ ↦ rfl)
      (Φ := fun _ ↦ pointFrame F (E := E) x) (continuous_pointFrame_const F E x),
      add_eq_left]
    -- The frame of `x` against itself has determinant `1`, which sweeps no angle.
    have h1 (t : I) :
        vertexValue ((ContinuousMap.const (StdSimplex ℝ (Fin 3)) x).comp (faceInclusion i))
          (fun _ ↦ pointFrame F (E := E) x) (StdSimplex.homeomorphI.symm t) = 1 :=
      -- The constant map takes the value `x`, so `vertexValue` is the determinant of
      -- `(pointFrame F x)⁻¹ ∘ pointFrame F x`.
      (congrArg ContinuousLinearEquiv.normalizedDet
        (ContinuousLinearEquiv.self_trans_symm (pointFrame F (E := E) x))).trans
        ContinuousLinearEquiv.normalizedDet_refl
    simp only [h1]
    rw [sweptAngle_eq_sub continuous_const (θ := fun _ ↦ 0) continuous_const
      fun _ ↦ Circle.exp_zero, sub_self]
  simp only [triangleAngle, h, Fin.sum_univ_three]
  norm_num

/-- **The clutching cochain on the triangulated cycle of a sphere** is the clutching number of the
sphere. -/
private theorem clutchingCochain_squareChain {x : X} (p : Ω^ (Fin 2) X x) :
    clutchingCochain F E (GenLoop.squareChain p) = clutchingNumber F E p := by
  obtain ⟨φ, hφ⟩ := exists_continuous_frame (𝕜 := ℂ) (F := F) (E := E) (map_continuous p)
  -- The three simplices of the cycle, computed with the frame `φ` and the frame of `x`: the
  -- diagonal edge cancels, the constant edges cancel against the constant simplex, and the four
  -- boundary edges remain.
  have hm₁ := triangleNumber_mul (F := F) (E := E) ((p : C(I^(Fin 2), X)).comp squareLowerTriangle)
  have hm₂ := triangleNumber_mul (F := F) (E := E) ((p : C(I^(Fin 2), X)).comp squareUpperTriangle)
  have hm₀ := triangleNumber_mul (F := F) (E := E) (ContinuousMap.const (StdSimplex ℝ (Fin 3)) x)
  rw [triangleAngle_comp _ hφ] at hm₁ hm₂
  rw [triangleAngle_const] at hm₀
  -- The diagonal faces of the two triangles of the square agree.
  have hdiag : squareLowerTriangle.comp (faceInclusion 1) =
      squareUpperTriangle.comp (faceInclusion 2) :=
    ContinuousMap.ext fun z ↦ by
      simpa only [ContinuousMap.comp_apply, StdSimplex.faceInclusion_apply] using
        squareLowerTriangle_map_succAbove_one z
  rw [← hdiag,
    edgeAngle_comp_of_mem_boundary p hφ (squareUpperTriangle.comp (faceInclusion 0))
      (g := fun t ↦ ![σ t, 1]) squareUpperTriangle_faceInclusion_zero fun t ↦ ⟨1, Or.inr rfl⟩,
    edgeAngle_comp_of_mem_boundary p hφ (squareUpperTriangle.comp (faceInclusion 1))
      (g := fun t ↦ ![0, t]) squareUpperTriangle_faceInclusion_one fun t ↦ ⟨0, Or.inl rfl⟩] at hm₂
  rw [edgeAngle_comp_of_mem_boundary p hφ (squareLowerTriangle.comp (faceInclusion 0))
      (g := fun t ↦ ![1, t]) squareLowerTriangle_faceInclusion_zero fun t ↦ ⟨0, Or.inr rfl⟩,
    edgeAngle_comp_of_mem_boundary p hφ (squareLowerTriangle.comp (faceInclusion 2))
      (g := fun t ↦ ![t, 0]) squareLowerTriangle_faceInclusion_two fun t ↦ ⟨1, Or.inl rfl⟩] at hm₁
  have hdeg := clutchingNumber_mul_two_pi_eq p hφ
  rw [GenLoop.squareChain_def, map_sub, map_add, map_nsmul, clutchingCochain_simplexMapChain,
    clutchingCochain_simplexMapChain, clutchingCochain_simplexMapChain]
  have key : ((triangleNumber F E ((p : C(I^(Fin 2), X)).comp squareLowerTriangle) +
      triangleNumber F E ((p : C(I^(Fin 2), X)).comp squareUpperTriangle) -
      2 • triangleNumber F E (ContinuousMap.const (StdSimplex ℝ (Fin 3)) x) : ℤ) : ℝ) * (2 * π) =
      (clutchingNumber F E p : ℝ) * (2 * π) := by
    push_cast [nsmul_eq_mul]
    linarith
  exact_mod_cast mul_right_cancel₀ (by positivity) key

end ChernCocycle

open ChernCocycle

variable {X : Type} [TopologicalSpace X]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℂ (E x)]

/-- **Clutching numbers factor through the Hurewicz map.** For a complex vector bundle `E` with
finite-dimensional model fibre `F` over a space `X`, there is an additive map
`P : H₂(X; ℤ) → ℤ` whose value on the Hurewicz class of every `a ∈ π₂(X, x)`, at every base point
`x`, is the clutching number of `E` on `a`. -/
theorem exists_addMonoidHom_hurewiczIntHom_eq_clutchingNumberHom :
    ∃ P : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of X) →+ ℤ,
      ∀ (x : X) (a : Additive (π_ 2 X x)),
        P (HomotopyGroup.hurewiczIntHom X x 1 a) = clutchingNumberHom F E x a := by
  obtain ⟨k, hk⟩ := GenLoop.exists_forall_squareClass_eq_zsmul_hurewicz
  refine ⟨k • clutchingHomologyHom F E, fun x a ↦ ?_⟩
  obtain ⟨a, rfl⟩ := Additive.ofMul.surjective a
  obtain ⟨p, rfl⟩ := Quotient.exists_rep a
  -- The clutching cochain takes the value `clutchingNumber F E p` on the square class of `p`,
  -- which is `k` times its Hurewicz class.
  have h₁ : clutchingHomologyHom F E (GenLoop.squareClass p) = clutchingNumber F E p := by
    rw [GenLoop.squareClass_def, clutchingHomologyHom_homologyπ,
      HomologicalComplex.iCycles_moduleCatCyclesMk, clutchingCochain_squareChain]
  have h₂ : clutchingHomologyHom F E (GenLoop.squareClass p) =
      k • clutchingHomologyHom F E ((GenLoop.hurewicz (ModuleCat.of ℤ ℤ) p).hom 1) :=
    (congrArg (clutchingHomologyHom F E) (hk X x p)).trans (map_zsmul _ _ _)
  rw [HomotopyGroup.hurewiczIntHom_mk, clutchingNumberHom_apply_mk, ← h₁, h₂]
  -- The domain of `P`, the value of `singularHomologyFunctor`, is by definition the homology of
  -- the singular chains on which `clutchingHomologyHom` is defined.
  exact AddMonoidHom.zsmul_apply _ _ _

end TauCeti
