/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.Family.Nijenhuis
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import TauCeti.LinearAlgebra.Complex.LinearPart

/-!
# Block almost complex structures in a product trivialization

In a smooth product trivialization `B × V` over a base `B` carrying a constant complex structure
`i`, a smooth almost complex structure `J` makes the projection `Prod.fst : B × V → B`
pseudoholomorphic precisely when `J` has the lower-triangular block form

`J(p)(a, v) = (i a, α(p) a + j(p) v)`

(`TauCeti.ComplexStructureFamily.blockEndomorphism i α j p`), where at each point `p : B × V`
the fibre block `j(p)` is an almost complex structure on `V` and the connection block `α(p)` is
`(i, j(p))`-complex-antilinear, `α(p)(i a) + j(p)(α(p) a) = 0`.

This file builds both directions of that correspondence on arbitrary real normed spaces `B` and `V`
(without finite-dimensionality assumptions):

* `blockEndomorphism_comp_self_eq_neg_id_iff` characterizes when `blockEndomorphism i α j p`
  squares to `-1` in terms of `i² = -1`, `j(p)² = -1`, and `α(p)(i a) + j(p)(α(p) a) = 0`
  (equivalently `IsComplexAntilinear`, `isComplexAntilinear_iff_apply_add_apply_eq_zero`);
* `blockAlmostComplexStructure` bundles smooth `α` and `j` satisfying these identities into a
  `SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V)` whose projection `Prod.fst` is
  pseudoholomorphic (`isPseudoholomorphic_fst_blockAlmostComplexStructure`);
* conversely, `connectionBlock` and `fiberBlock` extract smooth blocks from any
  `J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V)`, and
  `isPseudoholomorphicAt_fst_iff_toEndomorphism_eq_blockEndomorphism` proves that `Prod.fst` is
  pseudoholomorphic at `p` if and only if `J` equals `blockEndomorphism i (connectionBlock J)
  (fiberBlock J)` at `p`.

For the manifold-level diagonal (`α = 0`) product family on `P × M`, see
`TauCeti.SmoothAlmostComplexStructure.prodFamily`.

## Main declarations

* `TauCeti.ComplexStructureFamily.blockEndomorphism_comp_self_eq_neg_id_iff`: block square `-1`
  criterion.
* `TauCeti.ComplexStructureFamily.blockAlmostComplexStructure`: smooth almost complex structure
  associated to `(i, α, j)`.
* `TauCeti.ComplexStructureFamily.connectionBlock`,
  `TauCeti.ComplexStructureFamily.fiberBlock`: the off-diagonal and vertical blocks of an almost
  complex structure on `B × V`.
* `TauCeti.ComplexStructureFamily.isPseudoholomorphicAt_fst_iff_toEndomorphism_eq_blockEndomorphism`
  and `ComplexStructureFamily.isPseudoholomorphic_fst_iff_toEndomorphism_eq_blockEndomorphism`:
  characterization of block structures via pseudoholomorphy of `Prod.fst`.

## References

* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*, J. Eur. Math.
  Soc. 8 (2006), 611–699, Section 8.9.
* J. W. Robbin and D. A. Salamon, *Corrigendum to A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. 9 (2007), 901–905.
-/

public noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

namespace TauCeti.ComplexStructureFamily

variable {B V : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Algebraic structure and regularity of `blockEndomorphism` -/

/-- Applying `blockEndomorphism i α j p` twice yields
`(i (i w.1), α p (i w.1) + j p (α p w.1) + j p (j p w.2))`. -/
theorem blockEndomorphism_comp_self_apply (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V)
    (j : B × V → V →L[ℝ] V) (p w : B × V) :
    blockEndomorphism i α j p (blockEndomorphism i α j p w) =
      (i (i w.1), (α p (i w.1) + j p (α p w.1)) + j p (j p w.2)) := by
  simp only [blockEndomorphism_apply, map_add, add_assoc]

/-- The block endomorphism `[[i, 0], [α, j]]` at `p` squares to `-1` if and only if `i² = -1`,
`j(p)² = -1`, and `α(p)(i a) + j(p)(α(p) a) = 0` for all `a`. -/
theorem blockEndomorphism_comp_self_eq_neg_id_iff (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V)
    (j : B × V → V →L[ℝ] V) (p : B × V) :
    (blockEndomorphism i α j p).comp (blockEndomorphism i α j p) =
        -ContinuousLinearMap.id ℝ (B × V) ↔
      (∀ a, i (i a) = -a) ∧ (∀ v, j p (j p v) = -v) ∧
        (∀ a, α p (i a) + j p (α p a) = 0) := by
  constructor
  · intro h
    have happ (w : B × V) :
        blockEndomorphism i α j p (blockEndomorphism i α j p w) = -w :=
      congrArg (fun L : (B × V) →L[ℝ] B × V ↦ L w) h
    refine ⟨fun a ↦ ?_, fun v ↦ ?_, fun a ↦ ?_⟩
    · simpa [blockEndomorphism_comp_self_apply] using congrArg Prod.fst (happ (a, 0))
    · simpa [blockEndomorphism_comp_self_apply] using congrArg Prod.snd (happ (0, v))
    · simpa [blockEndomorphism_comp_self_apply] using congrArg Prod.snd (happ (a, 0))
  · rintro ⟨hi, hj, hαj⟩
    ext w <;> simp [hi, hj, hαj]

/-- Anticommutation `α(i a) + j(α a) = 0` is equivalent to `(i, j)`-complex antilinearity of `α`. -/
theorem isComplexAntilinear_iff_apply_add_apply_eq_zero (i : B →L[ℝ] B) (α : B →L[ℝ] V)
    (j : V →L[ℝ] V) :
    IsComplexAntilinear i.toLinearMap j.toLinearMap α.toLinearMap ↔
      ∀ a, α (i a) + j (α a) = 0 := by
  constructor
  · intro h a
    have ha := h.apply a
    simp only [ContinuousLinearMap.coe_coe] at ha
    rw [ha, neg_add_cancel]
  · intro h
    refine isComplexAntilinear_of_apply fun a ↦ ?_
    simp only [ContinuousLinearMap.coe_coe]
    exact eq_neg_of_add_eq_zero_left (h a)

/-- Expressing `blockEndomorphism` via `inl` and `inr` exposes its smoothness in `(α, j)`. -/
theorem blockEndomorphism_eq_inl_add_inr (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V)
    (j : B × V → V →L[ℝ] V) (p : B × V) :
    blockEndomorphism i α j p =
      (ContinuousLinearMap.inl ℝ B V).comp (i.comp (ContinuousLinearMap.fst ℝ B V)) +
        (ContinuousLinearMap.inr ℝ B V).comp
          ((α p).comp (ContinuousLinearMap.fst ℝ B V) +
            (j p).comp (ContinuousLinearMap.snd ℝ B V)) := by
  ext w <;> simp [blockEndomorphism_apply]

theorem contDiffWithinAt_blockEndomorphism {n : ℕ∞ω} {s : Set (B × V)} {p : B × V}
    (i : B →L[ℝ] B) {α : B × V → B →L[ℝ] V} {j : B × V → V →L[ℝ] V}
    (hα : ContDiffWithinAt ℝ n α s p) (hj : ContDiffWithinAt ℝ n j s p) :
    ContDiffWithinAt ℝ n (blockEndomorphism i α j) s p := by
  rw [funext (blockEndomorphism_eq_inl_add_inr i α j)]
  exact contDiffWithinAt_const.add (contDiffWithinAt_const.clm_comp
    ((hα.clm_comp contDiffWithinAt_const).add (hj.clm_comp contDiffWithinAt_const)))

theorem contDiffAt_blockEndomorphism {n : ℕ∞ω} {p : B × V}
    (i : B →L[ℝ] B) {α : B × V → B →L[ℝ] V} {j : B × V → V →L[ℝ] V}
    (hα : ContDiffAt ℝ n α p) (hj : ContDiffAt ℝ n j p) :
    ContDiffAt ℝ n (blockEndomorphism i α j) p := by
  simpa only [← contDiffWithinAt_univ] using
    contDiffWithinAt_blockEndomorphism i hα.contDiffWithinAt hj.contDiffWithinAt

theorem contDiff_blockEndomorphism {n : ℕ∞ω}
    (i : B →L[ℝ] B) {α : B × V → B →L[ℝ] V} {j : B × V → V →L[ℝ] V}
    (hα : ContDiff ℝ n α) (hj : ContDiff ℝ n j) :
    ContDiff ℝ n (blockEndomorphism i α j) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ contDiffAt_blockEndomorphism i hα.contDiffAt hj.contDiffAt

theorem differentiableAt_blockEndomorphism {p : B × V}
    (i : B →L[ℝ] B) {α : B × V → B →L[ℝ] V} {j : B × V → V →L[ℝ] V}
    (hα : DifferentiableAt ℝ α p) (hj : DifferentiableAt ℝ j p) :
    DifferentiableAt ℝ (blockEndomorphism i α j) p := by
  rw [funext (blockEndomorphism_eq_inl_add_inr i α j)]
  exact (differentiableAt_const _).add ((differentiableAt_const _).clm_comp
    ((hα.clm_comp (differentiableAt_const _)).add (hj.clm_comp (differentiableAt_const _))))

/-- Fréchet derivative of `blockEndomorphism i α j`: the constant base block differentiates to `0`,
while the vertical block differentiates to `fderiv ℝ α q h w.1 + fderiv ℝ j q h w.2`. -/
theorem fderiv_blockEndomorphism_apply (i : B →L[ℝ] B) {α : B × V → B →L[ℝ] V}
    {j : B × V → V →L[ℝ] V} {q : B × V}
    (hα : DifferentiableAt ℝ α q) (hj : DifferentiableAt ℝ j q) (h w : B × V) :
    fderiv ℝ (blockEndomorphism i α j) q h w = (0, fderiv ℝ α q h w.1 + fderiv ℝ j q h w.2) := by
  have h1 := (differentiableAt_blockEndomorphism i hα hj).hasFDerivAt.clm_apply
    (hasFDerivAt_const w q)
  have hd := ((hasFDerivAt_const (i w.1) q).prodMk
    ((hα.hasFDerivAt.clm_apply (hasFDerivAt_const w.1 q)).add
      (hj.hasFDerivAt.clm_apply (hasFDerivAt_const w.2 q)))).congr_of_eventuallyEq
    (Filter.EventuallyEq.of_eq (funext fun r ↦ blockEndomorphism_apply i α j r w))
  simpa using congrArg (fun D : (B × V) →L[ℝ] B × V ↦ D h) (h1.unique hd)

/-! ### Smooth block almost complex structures and projection characterization -/

/-- Construct a `SmoothAlmostComplexStructure` on `B × V` from a constant base complex structure
`i`, a smooth connection block `α`, and a smooth fibre almost complex structure family `j`
satisfying `α(p)(i a) + j(p)(α(p) a) = 0`. -/
def blockAlmostComplexStructure (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V)
    (j : B × V → V →L[ℝ] V) (hα : ContDiff ℝ ∞ α) (hj : ContDiff ℝ ∞ j)
    (hi : ∀ a, i (i a) = -a) (hj_sq : ∀ p v, j p (j p v) = -v)
    (hαj : ∀ p a, α p (i a) + j p (α p a) = 0) :
    SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V) where
  toEndomorphism :=
    ⟨blockEndomorphism i α j, fun p ↦ (contMDiffAt_hom_bundle _).2 ⟨contMDiffAt_id, by
      simpa [inCoordinates_tangent_bundle_core_model_space] using
        (contDiff_blockEndomorphism i hα hj).contDiffAt.contMDiffAt⟩⟩
  square_neg p := by
    change (blockEndomorphism i α j p).comp (blockEndomorphism i α j p) =
      -ContinuousLinearMap.id ℝ (B × V)
    exact (blockEndomorphism_comp_self_eq_neg_id_iff i α j p).2 ⟨hi, hj_sq p, hαj p⟩

@[simp]
theorem blockAlmostComplexStructure_toEndomorphism (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V)
    (j : B × V → V →L[ℝ] V) (hα : ContDiff ℝ ∞ α) (hj : ContDiff ℝ ∞ j)
    (hi : ∀ a, i (i a) = -a) (hj_sq : ∀ p v, j p (j p v) = -v)
    (hαj : ∀ p a, α p (i a) + j p (α p a) = 0) (p : B × V) :
    (blockAlmostComplexStructure i α j hα hj hi hj_sq hαj).toEndomorphism p =
      blockEndomorphism i α j p := (rfl)

theorem blockAlmostComplexStructure_apply (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V)
    (j : B × V → V →L[ℝ] V) (hα : ContDiff ℝ ∞ α) (hj : ContDiff ℝ ∞ j)
    (hi : ∀ a, i (i a) = -a) (hj_sq : ∀ p v, j p (j p v) = -v)
    (hαj : ∀ p a, α p (i a) + j p (α p a) = 0) (p w : B × V) :
    blockAlmostComplexStructure i α j hα hj hi hj_sq hαj p w = (i w.1, α p w.1 + j p w.2) :=
  blockEndomorphism_apply i α j p w

/-- For a smooth block almost complex structure, the base projection `Prod.fst : B × V → B` is
pseudoholomorphic. -/
theorem isPseudoholomorphic_fst_blockAlmostComplexStructure (i : B →L[ℝ] B)
    (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V)
    (hα : ContDiff ℝ ∞ α) (hj : ContDiff ℝ ∞ j)
    (hi : ∀ a, i (i a) = -a) (hj_sq : ∀ p v, j p (j p v) = -v)
    (hαj : ∀ p a, α p (i a) + j p (α p a) = 0) :
    IsPseudoholomorphic (blockAlmostComplexStructure i α j hα hj hi hj_sq hαj)
      (SmoothAlmostComplexStructure.const i hi) Prod.fst := by
  refine isPseudoholomorphic_iff.2 fun p ↦ isPseudoholomorphicAt_of_hasMFDerivAt
    (ContinuousLinearMap.fst ℝ B V).hasFDerivAt.hasMFDerivAt fun w ↦ ?_
  let w' : B × V := w
  exact (congrArg Prod.fst (blockEndomorphism_apply i α j p w')).trans
    (congrArg (· w'.1) (SmoothAlmostComplexStructure.const_toEndomorphism_apply i hi p.1)).symm

/-- The off-diagonal connection block `a ↦ (J(p)(a, 0)).2` of a smooth almost complex structure on
`B × V`. -/
def connectionBlock (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V)) (p : B × V) :
    B →L[ℝ] V :=
  (ContinuousLinearMap.snd ℝ B V).comp
    ((J.toEndomorphism p : (B × V) →L[ℝ] B × V).comp (ContinuousLinearMap.inl ℝ B V))

/-- The vertical fibre block `v ↦ (J(p)(0, v)).2` of a smooth almost complex structure on
`B × V`. -/
def fiberBlock (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V)) (p : B × V) :
    V →L[ℝ] V :=
  (ContinuousLinearMap.snd ℝ B V).comp
    ((J.toEndomorphism p : (B × V) →L[ℝ] B × V).comp (ContinuousLinearMap.inr ℝ B V))

@[simp]
theorem connectionBlock_apply (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V))
    (p : B × V) (a : B) : connectionBlock J p a = (J p (a, 0)).2 := (rfl)

@[simp]
theorem fiberBlock_apply (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V))
    (p : B × V) (v : V) : fiberBlock J p v = (J p (0, v)).2 := (rfl)

@[simp]
theorem connectionBlock_blockAlmostComplexStructure (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V)
    (j : B × V → V →L[ℝ] V) (hα : ContDiff ℝ ∞ α) (hj : ContDiff ℝ ∞ j)
    (hi : ∀ a, i (i a) = -a) (hj_sq : ∀ p v, j p (j p v) = -v)
    (hαj : ∀ p a, α p (i a) + j p (α p a) = 0) :
    connectionBlock (blockAlmostComplexStructure i α j hα hj hi hj_sq hαj) = α := by
  ext p a; change (blockEndomorphism i α j p (a, 0)).2 = α p a; simp [blockEndomorphism_apply]

@[simp]
theorem fiberBlock_blockAlmostComplexStructure (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V)
    (j : B × V → V →L[ℝ] V) (hα : ContDiff ℝ ∞ α) (hj : ContDiff ℝ ∞ j)
    (hi : ∀ a, i (i a) = -a) (hj_sq : ∀ p v, j p (j p v) = -v)
    (hαj : ∀ p a, α p (i a) + j p (α p a) = 0) :
    fiberBlock (blockAlmostComplexStructure i α j hα hj hi hj_sq hαj) = j := by
  ext p v; change (blockEndomorphism i α j p (0, v)).2 = j p v; simp [blockEndomorphism_apply]

/-- On a self-modelled normed space, the endomorphism field of a `SmoothAlmostComplexStructure` is
smooth in the normed-space sense. -/
theorem contDiff_toEndomorphism {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : SmoothAlmostComplexStructure 𝓘(ℝ, E) E) :
    ContDiff ℝ (E := E) (F := E →L[ℝ] E) ∞ (fun x ↦ J.toEndomorphism x) := by
  refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
  have h2 : ContDiffAt ℝ ∞ (fun x₁ ↦ ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E))
      E (TangentSpace 𝓘(ℝ, E)) x x₁ x x₁ (J.toEndomorphism x₁)) x :=
    contMDiffAt_iff_contDiffAt.1 ((contMDiffAt_hom_bundle _).1 (J.toEndomorphism.contMDiff x)).2
  exact (funext fun x₁ ↦ inCoordinates_tangent_bundle_core_model_space (I := 𝓘(ℝ, E))
    (I' := 𝓘(ℝ, E)) x x₁ x x₁ (J.toEndomorphism x₁)) ▸ h2

theorem contDiff_connectionBlock (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V)) :
    ContDiff ℝ ∞ (connectionBlock J) :=
  contDiff_const.clm_comp ((contDiff_toEndomorphism J).clm_comp contDiff_const)

theorem contDiff_fiberBlock (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V)) :
    ContDiff ℝ ∞ (fiberBlock J) :=
  contDiff_const.clm_comp ((contDiff_toEndomorphism J).clm_comp contDiff_const)

/-- The projection `Prod.fst : B × V → B` is pseudoholomorphic at `p` from `J` to the constant
structure `i` if and only if `(J p w).1 = i w.1` for every `w`. -/
theorem isPseudoholomorphicAt_fst_iff (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V))
    (i : B →L[ℝ] B) (hi : ∀ a, i (i a) = -a) (p : B × V) :
    IsPseudoholomorphicAt J (SmoothAlmostComplexStructure.const i hi) Prod.fst p ↔
      ∀ w : B × V, (J p w).1 = i w.1 := by
  have hfst : HasMFDerivAt 𝓘(ℝ, B × V) 𝓘(ℝ, B) Prod.fst p (ContinuousLinearMap.fst ℝ B V) :=
    (ContinuousLinearMap.fst ℝ B V).hasFDerivAt.hasMFDerivAt
  constructor
  · intro h w
    have hcomm := h.mfderiv_apply_commute w
    rw [hfst.mfderiv] at hcomm
    change (J p w).1 = (SmoothAlmostComplexStructure.const i hi).toEndomorphism p.1 w.1 at hcomm
    rwa [SmoothAlmostComplexStructure.const_toEndomorphism_apply] at hcomm
  · intro h
    refine isPseudoholomorphicAt_of_hasMFDerivAt hfst fun w ↦ ?_
    change (J p w).1 = (SmoothAlmostComplexStructure.const i hi).toEndomorphism p.1 w.1
    rw [SmoothAlmostComplexStructure.const_toEndomorphism_apply]; exact h w

/-- A smooth almost complex structure `J` on `B × V` agrees at `p` with
`blockEndomorphism i (connectionBlock J) (fiberBlock J) p` if and only if `Prod.fst` is
pseudoholomorphic at `p`. -/
theorem isPseudoholomorphicAt_fst_iff_toEndomorphism_eq_blockEndomorphism
    (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V))
    (i : B →L[ℝ] B) (hi : ∀ a, i (i a) = -a) (p : B × V) :
    IsPseudoholomorphicAt J (SmoothAlmostComplexStructure.const i hi) Prod.fst p ↔
      (J.toEndomorphism p : (B × V) →L[ℝ] B × V) =
        blockEndomorphism i (connectionBlock J) (fiberBlock J) p := by
  rw [isPseudoholomorphicAt_fst_iff]
  let K : (B × V) →L[ℝ] B × V := J.toEndomorphism p
  change (∀ w : B × V, (K w).1 = i w.1) ↔
    K = blockEndomorphism i (connectionBlock J) (fiberBlock J) p
  refine ⟨fun h ↦ ContinuousLinearMap.ext fun w ↦ Prod.ext (by simp [h w]) ?_,
    fun h w ↦ by
      simpa [blockEndomorphism_apply] using congrArg (fun L : (B × V) →L[ℝ] B × V ↦ (L w).1) h⟩
  simp only [blockEndomorphism_apply]
  exact congrArg Prod.snd
    (show K w = K (w.1, 0) + K (0, w.2) by rw [← map_add]; congr 1; ext <;> simp)

/-- When `Prod.fst` is pseudoholomorphic at `p`, the extracted blocks satisfy `j(p)² = -1` and
`α(p)(i a) + j(p)(α(p) a) = 0`. -/
theorem fiberBlock_apply_apply_and_connectionBlock_anticommute
    (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V))
    (i : B →L[ℝ] B) (hi : ∀ a, i (i a) = -a) {p : B × V}
    (hp : IsPseudoholomorphicAt J (SmoothAlmostComplexStructure.const i hi) Prod.fst p) :
    (∀ v, fiberBlock J p (fiberBlock J p v) = -v) ∧
      (∀ a, connectionBlock J p (i a) + fiberBlock J p (connectionBlock J p a) = 0) := by
  have hblk := (isPseudoholomorphicAt_fst_iff_toEndomorphism_eq_blockEndomorphism J i hi p).1 hp
  exact ((blockEndomorphism_comp_self_eq_neg_id_iff i (connectionBlock J) (fiberBlock J) p).1
    (hblk ▸ J.square_neg p)).2

/-- Global characterization: `Prod.fst : B × V → B` is pseudoholomorphic if and only if `J` is the
block almost complex structure built from `i`, `connectionBlock J`, and `fiberBlock J`. -/
theorem isPseudoholomorphic_fst_iff_toEndomorphism_eq_blockEndomorphism
    (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V))
    (i : B →L[ℝ] B) (hi : ∀ a, i (i a) = -a) :
    IsPseudoholomorphic J (SmoothAlmostComplexStructure.const i hi) Prod.fst ↔
      ∀ p, (J.toEndomorphism p : (B × V) →L[ℝ] B × V) =
        blockEndomorphism i (connectionBlock J) (fiberBlock J) p := by
  rw [isPseudoholomorphic_iff]
  exact forall_congr' fun p ↦
    isPseudoholomorphicAt_fst_iff_toEndomorphism_eq_blockEndomorphism J i hi p

/-- Reconstructing `J` as `blockAlmostComplexStructure` when `Prod.fst` is pseudoholomorphic. -/
theorem eq_blockAlmostComplexStructure_of_isPseudoholomorphic_fst
    (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V))
    (i : B →L[ℝ] B) (hi : ∀ a, i (i a) = -a)
    (hJ : IsPseudoholomorphic J (SmoothAlmostComplexStructure.const i hi) Prod.fst) :
    J = blockAlmostComplexStructure i (connectionBlock J) (fiberBlock J)
      (contDiff_connectionBlock J) (contDiff_fiberBlock J) hi
      (fun p ↦ (fiberBlock_apply_apply_and_connectionBlock_anticommute J i hi
        (hJ.isPseudoholomorphicAt p)).1)
      (fun p ↦ (fiberBlock_apply_apply_and_connectionBlock_anticommute J i hi
        (hJ.isPseudoholomorphicAt p)).2) := by
  have hblk := (isPseudoholomorphic_fst_iff_toEndomorphism_eq_blockEndomorphism J i hi).1 hJ
  ext p w
  exact congrArg (fun L : (B × V) →L[ℝ] B × V ↦ L w) (hblk p)

end TauCeti.ComplexStructureFamily
