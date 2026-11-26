/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.Family.Nijenhuis
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic

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
  (equivalently `IsComplexAntilinear`, `TauCeti.isComplexAntilinear_iff_apply_add_apply_eq_zero`);
* `blockAlmostComplexStructure` bundles smooth `α` and `j` satisfying these identities into a
  `SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V)` whose projection `Prod.fst` is
  pseudoholomorphic (`isPseudoholomorphic_fst_blockAlmostComplexStructure`);
* conversely, `connectionBlock` and `fiberBlock` extract smooth blocks from any
  `J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V)`, and
  `isPseudoholomorphicAt_fst_iff_toEndomorphism_eq_blockEndomorphism` proves that `Prod.fst` is
  pseudoholomorphic at `p` if and only if `J` equals `blockEndomorphism i (connectionBlock J)
  (fiberBlock J)` at `p`.

The fibres `{b} × V` of a block structure are `J`-complex: `J` sends a vertical vector `(0, w)` at
`(b, v)` to `(0, j(b, v) w)` (`apply_zero_prodMk`). So `v ↦ j(b, v)` is a smooth almost complex
structure on `V`, the fibre structure over `b` (`fiberAlmostComplexStructure`), and a map
`y ↦ (b, g y)` into the fibre over `b` is pseudoholomorphic exactly when `g` is pseudoholomorphic
for the fibre structure (`isPseudoholomorphicAt_prodMk_right_iff`). In particular the fibre
component of a pseudoholomorphic map lying in one fibre is pseudoholomorphic for the fibre
structure (`TauCeti.IsPseudoholomorphicAt.snd_of_forall_fst_eq`).

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
* `TauCeti.ComplexStructureFamily.fiberAlmostComplexStructure`: the almost complex structure of
  the fibre over a point of the base.
* `TauCeti.ComplexStructureFamily.isPseudoholomorphicAt_prodMk_right_iff`: maps into one fibre are
  pseudoholomorphic exactly when they are for the fibre structure.

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
    ext w
    exact congrArg (fun L : (B × V) →L[ℝ] B × V ↦ L w)
      ((blockEndomorphism_comp_self_eq_neg_id_iff i α j p).2 ⟨hi, hj_sq p, hαj p⟩)

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
  exact (congrArg Prod.fst (blockAlmostComplexStructure_apply i α j hα hj hi hj_sq hαj p w')).trans
    (SmoothAlmostComplexStructure.const_apply i hi p.1 w'.1).symm

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
  ext p a
  rw [connectionBlock_apply, blockAlmostComplexStructure_apply]
  simp

@[simp]
theorem fiberBlock_blockAlmostComplexStructure (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V)
    (j : B × V → V →L[ℝ] V) (hα : ContDiff ℝ ∞ α) (hj : ContDiff ℝ ∞ j)
    (hi : ∀ a, i (i a) = -a) (hj_sq : ∀ p v, j p (j p v) = -v)
    (hαj : ∀ p a, α p (i a) + j p (α p a) = 0) :
    fiberBlock (blockAlmostComplexStructure i α j hα hj hi hj_sq hαj) = j := by
  ext p v
  rw [fiberBlock_apply, blockAlmostComplexStructure_apply]
  simp

theorem contDiff_connectionBlock (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V)) :
    ContDiff ℝ ∞ (connectionBlock J) :=
  contDiff_const.clm_comp (J.contDiff_toEndomorphism.clm_comp contDiff_const)

theorem contDiff_fiberBlock (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V)) :
    ContDiff ℝ ∞ (fiberBlock J) :=
  contDiff_const.clm_comp (J.contDiff_toEndomorphism.clm_comp contDiff_const)

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
    have hc : (J p w).1 = SmoothAlmostComplexStructure.const i hi p.1 w.1 := by
      -- `hfst.mfderiv` identifies `mfderiv ... Prod.fst p` on `TangentSpace` with
      -- `ContinuousLinearMap.fst ℝ B V`, which acts as `Prod.fst` on the model space `B × V`.
      have hcomm := h.mfderiv_apply_commute w
      rw [hfst.mfderiv] at hcomm
      exact hcomm
    exact hc.trans (SmoothAlmostComplexStructure.const_apply i hi p.1 w.1)
  · intro h
    refine isPseudoholomorphicAt_of_hasMFDerivAt hfst fun w ↦ ?_
    let w' : B × V := w
    -- As above, on self-modelled spaces `ContinuousLinearMap.fst` on `TangentSpace` is `Prod.fst`.
    exact (h w').trans (SmoothAlmostComplexStructure.const_apply i hi p.1 w'.1).symm

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
  -- Read `J p` on the self-modelled tangent space `TangentSpace 𝓘(ℝ, B × V) p` as the model-space
  -- endomorphism `K : (B × V) →L[ℝ] B × V` so `ContinuousLinearMap.ext` uses `B × V` instances.
  let K : (B × V) →L[ℝ] B × V := J.toEndomorphism p
  change (∀ w : B × V, (K w).1 = i w.1) ↔
    K = blockEndomorphism i (connectionBlock J) (fiberBlock J) p
  refine ⟨fun h ↦ ContinuousLinearMap.ext fun w ↦ Prod.ext (by simp [h w]) ?_,
    fun h w ↦ by
      simpa [blockEndomorphism_apply] using congrArg (fun L : (B × V) →L[ℝ] B × V ↦ (L w).1) h⟩
  have hKw : K w = K (w.1, 0) + K (0, w.2) := by rw [← map_add]; congr 1; ext <;> simp
  simp only [blockEndomorphism_apply]
  exact congrArg Prod.snd hKw

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

/-! ### The fibres of a block structure -/

section Fiber

variable (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V)) {i : B →L[ℝ] B}
  {hi : ∀ a, i (i a) = -a}
  (hJ : IsPseudoholomorphic J (SmoothAlmostComplexStructure.const i hi) Prod.fst)

include hJ in
/-- The **fibre structure** over `b` of a block almost complex structure `J` on `B × V`: the smooth
almost complex structure `v ↦ j(b, v)` on `V` given by the fibre block of `J` along the fibre
`{b} × V`. The fibres `{b} × V` are `J`-complex submanifolds, and this is the structure `J`
induces on them (`TauCeti.ComplexStructureFamily.isPseudoholomorphicAt_prodMk_right_iff`). -/
def fiberAlmostComplexStructure (b : B) : SmoothAlmostComplexStructure 𝓘(ℝ, V) V where
  toEndomorphism := Manifold.tangentEndomorphismOfModel (fun v ↦ fiberBlock J (b, v))
    ((contDiff_fiberBlock J).comp (contDiff_const.prodMk contDiff_id))
  square_neg v := by
    ext w
    rw [Manifold.tangentEndomorphismOfModel_apply]
    exact (fiberBlock_apply_apply_and_connectionBlock_anticommute J i hi
      (hJ.isPseudoholomorphicAt (b, v))).1 w

@[simp]
theorem fiberAlmostComplexStructure_toEndomorphism (b : B) (v : V) :
    (fiberAlmostComplexStructure J hJ b).toEndomorphism v = fiberBlock J (b, v) :=
  Manifold.tangentEndomorphismOfModel_apply _ _ v

/-- The fibre structure over `b` acts on a vertical vector `w` at `v` as `J` does on `(0, w)` at
`(b, v)`. -/
theorem fiberAlmostComplexStructure_apply (b : B) (v w : V) :
    fiberAlmostComplexStructure J hJ b v w = (J (b, v) (0, w)).2 :=
  (congrArg (fun A : V →L[ℝ] V ↦ A w)
    (fiberAlmostComplexStructure_toEndomorphism J hJ b v)).trans (fiberBlock_apply J (b, v) w)

/-- A block structure sends a vertical vector `(0, w)` at `(b, v)` to the vertical vector
`(0, j w)`, with `j` the fibre structure over `b`: the vertical subspaces are `J`-complex. -/
theorem apply_zero_prodMk (b : B) (v w : V) :
    J (b, v) (0, w) = ((0 : B), fiberAlmostComplexStructure J hJ b v w) := by
  refine Prod.ext ?_ (fiberAlmostComplexStructure_apply J hJ b v w).symm
  have h := (isPseudoholomorphicAt_fst_iff J i hi (b, v)).1 (hJ.isPseudoholomorphicAt (b, v))
    ((0 : B), w)
  rw [h, map_zero]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {j : SmoothAlmostComplexStructure I M}

variable {J}

/-- **Vertical maps.** A map `y ↦ (b, g y)` into the fibre over `b` is pseudoholomorphic at `x`
for a block structure `J` exactly when `g` is pseudoholomorphic at `x` for the fibre structure
over `b`. -/
theorem isPseudoholomorphicAt_prodMk_right_iff {b : B} {g : M → V} {x : M} :
    IsPseudoholomorphicAt j J (fun y ↦ (b, g y)) x ↔
      IsPseudoholomorphicAt j (fiberAlmostComplexStructure J hJ b) g x := by
  -- the inclusion `v ↦ (b, v)` of the fibre has derivative `inr` at every point
  have hinr (v : V) : HasMFDerivAt 𝓘(ℝ, V) 𝓘(ℝ, B × V) (fun v : V ↦ (b, v)) v
      (ContinuousLinearMap.inr ℝ B V) := (hasFDerivAt_prodMk_right b v).hasMFDerivAt
  have hsnd (p : B × V) : HasMFDerivAt 𝓘(ℝ, B × V) 𝓘(ℝ, V) Prod.snd p
      (ContinuousLinearMap.snd ℝ B V) := (ContinuousLinearMap.snd ℝ B V).hasFDerivAt.hasMFDerivAt
  have hfst (p : B × V) : HasMFDerivAt 𝓘(ℝ, B × V) 𝓘(ℝ, B) Prod.fst p
      (ContinuousLinearMap.fst ℝ B V) := (ContinuousLinearMap.fst ℝ B V).hasFDerivAt.hasMFDerivAt
  constructor
  · intro hu
    set u' := mfderiv I 𝓘(ℝ, B × V) (fun y ↦ (b, g y)) x
    have hu' : HasMFDerivAt I 𝓘(ℝ, B × V) (fun y ↦ (b, g y)) x u' :=
      hu.mdifferentiableAt.hasMFDerivAt
    have hlin := hu.mfderiv_apply_commute
    -- the base component of `u'` vanishes, since the base component of the map is constant
    have h₀ : (ContinuousLinearMap.fst ℝ B V).comp u' = 0 :=
      ((hfst _).comp x hu').mfderiv.symm.trans (hasMFDerivAt_const b x).mfderiv
    have hu'w (w : TangentSpace I x) : u' w = ((0 : B), (u' w).2) :=
      Prod.ext (congrArg (fun L : TangentSpace I x →L[ℝ] B ↦ L w) h₀) rfl
    refine isPseudoholomorphicAt_of_hasMFDerivAt ((hsnd _).comp x hu') fun w ↦ ?_
    have h := congrArg Prod.snd (hlin w)
    -- `J (b, g x)` acts on the vertical vector `u' w` through the fibre structure
    rw [hu'w w, apply_zero_prodMk J hJ] at h
    exact h
  · intro hg
    refine isPseudoholomorphicAt_of_hasMFDerivAt
      ((hinr (g x)).comp x hg.mdifferentiableAt.hasMFDerivAt) fun w ↦ ?_
    -- `inr` carries the equation for `g` to the equation for `(b, g)` along the vertical vectors
    exact (congrArg (fun v : V ↦ ((0 : B), v)) (hg.mfderiv_apply_commute w)).trans
      (apply_zero_prodMk J hJ b (g x) _).symm

/-- **Vertical curves.** If a map `u` into `B × V` is pseudoholomorphic at `x` for a block
structure `J` and lies in the fibre over `b`, then its fibre component is pseudoholomorphic at `x`
for the fibre structure over `b`. -/
theorem _root_.TauCeti.IsPseudoholomorphicAt.snd_of_forall_fst_eq {b : B} {u : M → B × V} {x : M}
    (hu : IsPseudoholomorphicAt j J u x) (hb : ∀ y, (u y).1 = b) :
    IsPseudoholomorphicAt j (fiberAlmostComplexStructure J hJ b) (fun y ↦ (u y).2) x := by
  have hu' : u = fun y ↦ (b, (u y).2) := funext fun y ↦ Prod.ext (hb y) rfl
  rw [hu'] at hu
  exact (isPseudoholomorphicAt_prodMk_right_iff hJ).1 hu

end Fiber

end TauCeti.ComplexStructureFamily
