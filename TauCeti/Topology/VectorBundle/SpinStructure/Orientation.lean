/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Euclidean.Space
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Euclidean
public import TauCeti.Topology.VectorBundle.Orientation.OrientedFrame
public import TauCeti.Topology.VectorBundle.SpinStructure.Basic

import TauCeti.Topology.Covering.BundleMap

/-!
# The orientation and double-cover geometry of a Spin structure

Let `E → X` be a real vector bundle with model fibre `F` and fibre inner products, equipped with a
Spin structure `s : TauCeti.SpinStructure F E n` of positive rank `n`. Its frame map
`s.toFrame : P → Fr(E)` intertwines the right `Spin(n)`-action on `P` with the right action of
`TauCeti.specialOrthogonalGroup (EuclideanSpace ℝ (Fin n))` on orthonormal frames via the double
cover `TauCeti.CliffordAlgebra.realCliffordSpinToEuclideanSpecialOrthogonal n`
(`TauCeti.SpinStructure.toFrame_op_smul`).

From this equivariance three structural consequences follow:

1. **Central sheet involution and automorphisms.** Right multiplication on every fibre by the
   central element `-1` of `Spin(n)` defines an involutive self-equivalence
   `TauCeti.OrthonormalFrameLift.Equiv.negOne s : s.Equiv s` commuting with all equivalences and
   pullbacks. The fibres of `s.toFrame` are the two-point orbits `{p, p • (-1)}`
   (`TauCeti.SpinStructure.toFrame_eq_toFrame_iff`), so every automorphism `φ : s.Equiv s` acts on
   each fibre as the identity or as `-1`; over a preconnected base `Equiv.refl s` and
   `Equiv.negOne s` are the only automorphisms
   (`TauCeti.OrthonormalFrameLift.Equiv.eq_refl_or_eq_negOne`), and any two equivalences
   `s.Equiv t` are equal or differ by `Equiv.negOne s`.

2. **Induced fibre and bundle orientations.** Because `SO(n)` acts by transformations of determinant
   `1`, all points of a fibre `s.P x` transport a model orientation `o` of `ℝⁿ` to the same
   orientation `s.fiberOrientation o x` of `E x`, compatible with negation, equivalences,
   pullbacks (`TauCeti.SpinStructure.fiberOrientation_pullback`) and transport along fibrewise
   isometries (`TauCeti.SpinStructure.fiberOrientation_map`). When `E` is a vector bundle, the
   quotient property of `π : P → X` descends `OrthonormalFrameBundle.toOrientationCover o ∘
   s.toFrame` to a bundle orientation `s.orientation o : TauCeti.VectorBundleOrientation F E
   (Fin n)`. In particular, any vector bundle admitting a Spin structure is orientable
   (`TauCeti.SpinStructure.nonempty_vectorBundleOrientation`).

3. **Two-sheeted covering of positively oriented frames.** The image of `s.toFrame` is precisely the
   bundle `OrthonormalFrameBundle.orientedFrames (s.orientation o) o` of positively oriented
   orthonormal frames (`TauCeti.SpinStructure.range_toFrame_eq_orientedFrames`), so `s.toFrame`
   restricts to a continuous equivariant surjection `s.toOrientedFrames o`. When `E` is a
   continuous Riemannian bundle, comparing equivariant local trivializations of `s.P` and of
   `orientedFrames` conjugates `s.toOrientedFrames o` locally to a product of the identity on the
   base with the Spin double cover `Spin(n) → SO(n)`
   (`IsCoveringMap.of_equivariant_trivialization`), proving that `s.toOrientedFrames o` is a
   covering map (`TauCeti.SpinStructure.isCoveringMap_toOrientedFrames`) and a quotient covering map
   by the two-element kernel of `Spin(n) → SO(n)`
   (`TauCeti.SpinStructure.isQuotientCoveringMap_toOrientedFrames`).

## Main definitions

* `TauCeti.OrthonormalFrameLift.Equiv.negOne`: the sheet-exchange automorphism of a Spin structure,
  acting by `-1 ∈ Spin(n)`.
* `TauCeti.OrthonormalFrameLift.fiberOrientation`: the fibre orientation induced by a lift of the
  orthonormal frame bundle, such as a Spin or `Spinᶜ` structure, and an orientation of
  `EuclideanSpace ℝ (Fin n)`. When the structure group acts by transformations of positive
  determinant, all frames over a point carry the model orientation to it
  (`TauCeti.OrthonormalFrameLift.fiberOrientation_eq_map_frameAt`).
* `TauCeti.SpinStructure.orientation`: the bundle orientation induced by a Spin structure on a
  vector bundle.
* `TauCeti.SpinStructure.toOrientedFrames`: the lifted frame map into positively oriented frames.

## Main results

* `TauCeti.SpinStructure.toFrame_op_smul`, `TauCeti.SpinStructure.toFrame_eq_toFrame_iff`:
  `SO(n)`-equivariance and `{1, -1}`-fibres of `s.toFrame`.
* `TauCeti.OrthonormalFrameLift.Equiv.eq_refl_or_eq_negOne`,
  `TauCeti.OrthonormalFrameLift.Equiv.eq_or_eq_negOne_trans`: classification of equivalences over a
  preconnected base.
* `TauCeti.SpinStructure.fiberOrientation_pullback`, `TauCeti.SpinStructure.fiberOrientation_map`,
  `TauCeti.SpinStructure.nonempty_vectorBundleOrientation`,
  `TauCeti.OrthonormalFrameLift.Equiv.orientation_eq`: orientability and functoriality of the
  induced orientation.
* `TauCeti.SpinStructure.range_toFrame_eq_orientedFrames`,
  `TauCeti.SpinStructure.isCoveringMap_toOrientedFrames`,
  `TauCeti.SpinStructure.isQuotientCoveringMap_toOrientedFrames`: the Spin structure as a
  two-sheeted principal covering of positively oriented orthonormal frames.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Chapter II,
  §1.
* R. C. Kirby, *The topology of 4-manifolds*, Lecture Notes in Mathematics 1374, Springer, 1989,
  Chapter IV, §1.
-/

public section

noncomputable section

open Bundle MulOpposite CliffordAlgebra Set Topology
open TauCeti.CliffordAlgebra

universe w

namespace TauCeti.SpinStructure

open OrthonormalFrameLift

section EquivarianceAndFibers

variable {X : Type*} [TopologicalSpace X] {F : Type*} {E : X → Type w}
  [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)] {n : ℕ}

/-- The frame map of a Spin structure is equivariant for the right `Spin(n)`-action on `P` and the
right `SO(n)`-action on orthonormal frames via
`TauCeti.CliffordAlgebra.realCliffordSpinToEuclideanSpecialOrthogonal`. -/
theorem toFrame_op_smul (s : SpinStructure F E n) (g : realCliffordSpinGroupZero n)
    (p : TotalSpace (realCliffordSpinGroupZero n) s.P) :
    s.toFrame (op g • p) =
      op ((realCliffordSpinToEuclideanSpecialOrthogonal n g :
          specialOrthogonalGroup (EuclideanSpace ℝ (Fin n))) :
        unitary (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) • s.toFrame p := by
  obtain ⟨x, p⟩ := p
  refine OrthonormalFrameBundle.ext_totalSpaceMk fun v ↦ ?_
  rw [TotalSpace.smul_mk, s.toFrame_smul_spinVectorAction, OrthonormalFrameBundle.frame_smul_apply,
    unop_op, realCliffordSpinToEuclideanSpecialOrthogonal_apply_apply, WithLp.ofLp_toLp]
  -- The two sides differ only in the base point, and acting on a frame keeps its base point.
  rfl

section NegOne

variable [NeZero n]

/-- Acting on the right by the central element `-1` of `Spin(n)` preserves the induced frame. -/
@[simp]
theorem toFrame_negOne_smul (s : SpinStructure F E n)
    (p : TotalSpace (realCliffordSpinGroupZero n) s.P) :
    s.toFrame (op (spinGroup.negOne (realCliffordForm n 0)
      (nondegenerate_realCliffordForm n 0).ne_zero) • p) = s.toFrame p := by
  rw [s.toFrame_op_smul, realCliffordSpinToEuclideanSpecialOrthogonal_negOne, OneMemClass.coe_one,
    op_one, one_smul]

/-- Acting on a point of `P` by `g : Spin(n)` fixes its image frame if and only if `g = 1` or
`g = -1`. -/
theorem toFrame_op_smul_eq_self_iff (s : SpinStructure F E n)
    {g : realCliffordSpinGroupZero n} {p : TotalSpace (realCliffordSpinGroupZero n) s.P} :
    s.toFrame (op g • p) = s.toFrame p ↔
      g = 1 ∨
        g = spinGroup.negOne (realCliffordForm n 0)
          (nondegenerate_realCliffordForm n 0).ne_zero := by
  rw [s.toFrame_op_smul, OrthonormalFrameBundle.smul_eq_self_iff, OneMemClass.coe_eq_one,
    realCliffordSpinToEuclideanSpecialOrthogonal_eq_one_iff]

/-- Two points of `P` map to the same orthonormal frame if and only if they are equal or differ by
the central element `-1` of `Spin(n)`. -/
theorem toFrame_eq_toFrame_iff (s : SpinStructure F E n)
    {p q : TotalSpace (realCliffordSpinGroupZero n) s.P} :
    s.toFrame p = s.toFrame q ↔
      p = q ∨
        p = op (spinGroup.negOne (realCliffordForm n 0)
          (nondegenerate_realCliffordForm n 0).ne_zero) • q := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨x, p⟩ := p
    obtain ⟨y, q⟩ := q
    have hxy : x = y := by
      simpa only [proj_toFrame] using congrArg OrthonormalFrameBundle.proj h
    subst hxy
    rw [← PrincipalBundle.smul_division_mk q p] at h ⊢
    rcases (s.toFrame_op_smul_eq_self_iff.1 h) with hg | hg <;> rw [hg]
    · exact .inl (one_smul _ _)
    · exact .inr rfl
  · rintro (rfl | rfl)
    · rfl
    · exact s.toFrame_negOne_smul q

/-- Right multiplication by `-1 ∈ Spin(n)` has no fixed points on the total space of `P`. -/
theorem op_negOne_smul_ne_self (s : SpinStructure F E n)
    (p : TotalSpace (realCliffordSpinGroupZero n) s.P) :
    op (spinGroup.negOne (realCliffordForm n 0)
      (nondegenerate_realCliffordForm n 0).ne_zero) • p ≠ p := by
  intro h
  have hfib : op (spinGroup.negOne (realCliffordForm n 0)
      (nondegenerate_realCliffordForm n 0).ne_zero) • p.snd = p.snd :=
    TotalSpace.mk_inj.1 h
  exact spinGroup.negOne_ne_one (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0).ne_zero
    (PrincipalBundle.smul_eq_self_iff.1 hfib)

/-- Every fibre of `s.toFrame` over its image has cardinality `2`. -/
@[simp]
theorem ncard_preimage_toFrame_singleton (s : SpinStructure F E n)
    (p : TotalSpace (realCliffordSpinGroupZero n) s.P) :
    (s.toFrame ⁻¹' {s.toFrame p}).ncard = 2 := by
  have hset : s.toFrame ⁻¹' {s.toFrame p} =
      {p, op (spinGroup.negOne (realCliffordForm n 0)
        (nondegenerate_realCliffordForm n 0).ne_zero) • p} := by
    ext q
    simpa only [mem_preimage, mem_singleton_iff, mem_insert_iff] using
      s.toFrame_eq_toFrame_iff (p := q) (q := p)
  rw [hset, ncard_pair (s.op_negOne_smul_ne_self p).symm]

end NegOne

/-- Acting on `P` by `Spin(n)` preserves the induced point in the orientation double cover. -/
theorem toOrientationCover_toFrame_op_smul (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (g : realCliffordSpinGroupZero n)
    (p : TotalSpace (realCliffordSpinGroupZero n) s.P) :
    OrthonormalFrameBundle.toOrientationCover o (s.toFrame (op g • p)) =
      OrthonormalFrameBundle.toOrientationCover o (s.toFrame p) := by
  rw [s.toFrame_op_smul]
  exact OrthonormalFrameBundle.toOrientationCover_smul_of_det_pos Fact.out o
    (mem_specialOrthogonalGroup_iff_det_pos.1
      (realCliffordSpinToEuclideanSpecialOrthogonal n g).property) (s.toFrame p)

/-- Points in the same fibre of `P` induce the same point of the orientation double cover. -/
theorem toOrientationCover_toFrame_eq_of_proj_eq (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))
    {p q : TotalSpace (realCliffordSpinGroupZero n) s.P} (h : p.proj = q.proj) :
    OrthonormalFrameBundle.toOrientationCover o (s.toFrame p) =
      OrthonormalFrameBundle.toOrientationCover o (s.toFrame q) := by
  obtain ⟨x, p⟩ := p
  obtain ⟨y, q⟩ := q
  obtain rfl : x = y := h
  rw [← PrincipalBundle.smul_division_mk q p, s.toOrientationCover_toFrame_op_smul]

end EquivarianceAndFibers

end TauCeti.SpinStructure

/-! ### Central sheet involution and automorphisms

A Spin structure `s` is an `OrthonormalFrameLift`, and its equivalences are
`TauCeti.OrthonormalFrameLift.Equiv`, so the automorphisms below live in that namespace. -/

namespace TauCeti.OrthonormalFrameLift.Equiv

open SpinStructure

variable {X : Type*} [TopologicalSpace X] {F : Type*} {E : X → Type w}
  [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)] {n : ℕ} [NeZero n]

/-- The **sheet-exchange automorphism** of a Spin structure, acting on every fibre by the central
element `-1` of `Spin(n)`. -/
def negOne (s : SpinStructure F E n) : s.Equiv s where
  toEquiv x :=
    { toFun p :=
        op (spinGroup.negOne (realCliffordForm n 0)
          (nondegenerate_realCliffordForm n 0).ne_zero) • p
      invFun p :=
        op (spinGroup.negOne (realCliffordForm n 0)
          (nondegenerate_realCliffordForm n 0).ne_zero) • p
      left_inv p := by simp [smul_smul, ← op_mul]
      right_inv p := by simp [smul_smul, ← op_mul] }
  continuous_toFun :=
    continuous_const_smul
      (op (spinGroup.negOne (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0).ne_zero))
  continuous_invFun :=
    continuous_const_smul
      (op (spinGroup.negOne (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0).ne_zero))
  map_smul x p g := by
    simp only [_root_.Equiv.coe_fn_mk, smul_smul, ← op_mul, spinGroup.negOne_mul_comm]
  toFrame_map x p := s.toFrame_negOne_smul ⟨x, p⟩

@[simp]
theorem negOne_toEquiv_apply (s : SpinStructure F E n) (x : X) (p : s.P x) :
    (negOne s).toEquiv x p =
      op (spinGroup.negOne (realCliffordForm n 0)
        (nondegenerate_realCliffordForm n 0).ne_zero) • p :=
  (rfl)

@[simp]
theorem negOne_toEquiv_symm_apply (s : SpinStructure F E n) (x : X) (p : s.P x) :
    ((negOne s).toEquiv x).symm p =
      op (spinGroup.negOne (realCliffordForm n 0)
        (nondegenerate_realCliffordForm n 0).ne_zero) • p := by
  rw [_root_.Equiv.symm_apply_eq, negOne_toEquiv_apply, smul_smul, ← op_mul]
  simp

theorem negOne_toHomeomorph_apply (s : SpinStructure F E n)
    (p : TotalSpace (realCliffordSpinGroupZero n) s.P) :
    (negOne s).toHomeomorph p =
      op (spinGroup.negOne (realCliffordForm n 0)
        (nondegenerate_realCliffordForm n 0).ne_zero) • p := by
  cases p
  rw [toHomeomorph_apply, negOne_toEquiv_apply, TotalSpace.smul_mk]

@[simp]
theorem negOne_symm (s : SpinStructure F E n) : (negOne s).symm = negOne s :=
  ext fun _ _ ↦ by simp

@[simp]
theorem negOne_trans_self (s : SpinStructure F E n) :
    (negOne s).trans (negOne s) = refl s :=
  ext fun _ p ↦ by simp [smul_smul, ← op_mul]

/-- The sheet-exchange automorphism commutes with every equivalence of Spin structures. -/
theorem negOne_trans_comm {s t : SpinStructure F E n} (φ : s.Equiv t) :
    (negOne s).trans φ = φ.trans (negOne t) :=
  ext fun x p ↦ by simp

/-- Over a nonempty base, the sheet-exchange automorphism is distinct from the identity. -/
theorem negOne_ne_refl [Nonempty X] (s : SpinStructure F E n) :
    negOne s ≠ refl s := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨p⟩ := s.nonempty_P x
  have hp : (negOne s).toHomeomorph ⟨x, p⟩ = (refl s).toHomeomorph ⟨x, p⟩ :=
    congrArg (fun ψ : s.Equiv s ↦ ψ.toHomeomorph ⟨x, p⟩) h
  rw [negOne_toHomeomorph_apply, refl_toHomeomorph, Homeomorph.refl_apply] at hp
  exact s.op_negOne_smul_ne_self ⟨x, p⟩ hp

/-- Pulling back the sheet-exchange automorphism gives the sheet-exchange automorphism of the
pullback. -/
@[simp]
theorem pullback_negOne {Y : Type*} [TopologicalSpace Y] {K : Type*} [FunLike K Y X]
    [ContinuousMapClass K Y X] (s : SpinStructure F E n) (f : K) :
    (negOne s).pullback f = negOne (s.pullback f) :=
  ext fun y p ↦ by
    rw [pullback_toEquiv]
    exact (negOne_toEquiv_apply s (f y) p).trans (negOne_toEquiv_apply (s.pullback f) y p).symm

/-- Transporting the sheet-exchange automorphism along fibrewise isometries gives the
sheet-exchange automorphism of the transport. -/
@[simp]
theorem map_negOne {F' : Type*} {E' : X → Type w} [TopologicalSpace (TotalSpace F' E')]
    [∀ x, NormedAddCommGroup (E' x)] [∀ x, InnerProductSpace ℝ (E' x)]
    (s : SpinStructure F E n) {Φ : ∀ x, E x ≃ₗᵢ[ℝ] E' x}
    (hΦ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, Φ v.proj v.snd⟩ : TotalSpace F' E')) :
    (negOne s).map Φ hΦ = negOne (s.map Φ hΦ) :=
  ext fun x p ↦ by
    rw [map_toEquiv]
    exact (negOne_toEquiv_apply s x p).trans (negOne_toEquiv_apply (s.map Φ hΦ) x p).symm

/-- An automorphism of a Spin structure acts on each point of a fibre either as the identity or by
the central element `-1` of `Spin(n)`. -/
theorem toEquiv_apply_eq_self_or_negOne_smul {s : SpinStructure F E n} (φ : s.Equiv s) (x : X)
    (p : s.P x) :
    φ.toEquiv x p = p ∨
      φ.toEquiv x p =
        op (spinGroup.negOne (realCliffordForm n 0)
          (nondegenerate_realCliffordForm n 0).ne_zero) • p := by
  rcases s.toFrame_eq_toFrame_iff.1 (φ.toFrame_map x p) with h | h
  · exact .inl (TotalSpace.mk_inj.1 h)
  · exact .inr (TotalSpace.mk_inj.1 h)

/-- At every point `p` of a fibre `s.P x`, the division element carrying `p` to `φ.toEquiv x p` is
`1` or `-1`. -/
theorem division_toEquiv_eq_one_or_negOne {s : SpinStructure F E n} (φ : s.Equiv s) (x : X)
    (p : s.P x) :
    PrincipalBundle.division (realCliffordSpinGroupZero n) p (φ.toEquiv x p) = 1 ∨
      PrincipalBundle.division (realCliffordSpinGroupZero n) p (φ.toEquiv x p) =
        spinGroup.negOne (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0).ne_zero := by
  rcases toEquiv_apply_eq_self_or_negOne_smul φ x p with h | h <;> rw [h]
  · exact .inl (PrincipalBundle.division_self p)
  · refine .inr (PrincipalBundle.division_eq_iff.2 rfl)

/-- For an automorphism `φ : s.Equiv s`, the division element `division _ p (φ.toEquiv x p)` is
independent of the choice of point `p` in the fibre `s.P x`. -/
theorem division_toEquiv_eq {s : SpinStructure F E n} (φ : s.Equiv s) (x : X) (p q : s.P x) :
    PrincipalBundle.division (realCliffordSpinGroupZero n) p (φ.toEquiv x p) =
      PrincipalBundle.division (realCliffordSpinGroupZero n) q (φ.toEquiv x q) := by
  rw [← PrincipalBundle.smul_division (G := realCliffordSpinGroupZero n) q p, φ.map_smul,
    PrincipalBundle.division_smul_left, PrincipalBundle.division_smul_right]
  rcases division_toEquiv_eq_one_or_negOne φ x q with hd | hd <;> rw [hd]
  · simp
  · rw [spinGroup.negOne_mul_comm, inv_mul_cancel_left]

omit [NeZero n] in
/-- For an automorphism `φ : s.Equiv s`, the division map
`p ↦ division _ p.2 (φ.toEquiv p.proj p.2)` is continuous on the total space of `s.P`. -/
theorem continuous_division_toEquiv {s : SpinStructure F E n} (φ : s.Equiv s) :
    Continuous fun p : TotalSpace (realCliffordSpinGroupZero n) s.P ↦
      PrincipalBundle.division (realCliffordSpinGroupZero n) p.snd (φ.toEquiv p.proj p.snd) :=
  Continuous.division (f := TotalSpace.proj)
    (p := fun p : TotalSpace (realCliffordSpinGroupZero n) s.P ↦ p.snd)
    (q := fun p : TotalSpace (realCliffordSpinGroupZero n) s.P ↦ φ.toEquiv p.proj p.snd)
    continuous_id φ.continuous_toFun

/-- Over a preconnected base, every automorphism of a Spin structure is either the identity or the
sheet-exchange automorphism `Equiv.negOne`. -/
theorem eq_refl_or_eq_negOne [PreconnectedSpace X] {s : SpinStructure F E n} (φ : s.Equiv s) :
    φ = refl s ∨ φ = negOne s := by
  -- Because `-1` is central, `p ↦ division _ p (φ.toEquiv x p)` is constant on each fibre and
  -- descends along the quotient projection `P → X` to a `{1, -1}`-valued continuous map on `X`.
  let d : X → realCliffordSpinGroupZero n := fun x ↦
    PrincipalBundle.division (realCliffordSpinGroupZero n) (Classical.arbitrary (s.P x))
      (φ.toEquiv x (Classical.arbitrary (s.P x)))
  have hd_eq (p : TotalSpace (realCliffordSpinGroupZero n) s.P) :
      d p.proj = PrincipalBundle.division (realCliffordSpinGroupZero n) p.snd
        (φ.toEquiv p.proj p.snd) :=
    division_toEquiv_eq φ p.proj _ p.snd
  have hd_cont : Continuous d := by
    rw [(FiberBundle.isQuotientMap_proj
      (F := realCliffordSpinGroupZero n) (E := s.P)).continuous_iff]
    exact (continuous_division_toEquiv φ).congr fun p ↦ (hd_eq p).symm
  let T : Set (realCliffordSpinGroupZero n) :=
    {1, spinGroup.negOne (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0).ne_zero}
  obtain ⟨g, hgT, hdg⟩ := isPreconnected_univ.eqOn_const_of_mapsTo (T := T)
    (toFinite T).isDiscrete hd_cont.continuousOn
    (fun x _ ↦ division_toEquiv_eq_one_or_negOne φ x _) ⟨1, by simp [T]⟩
  have hdiv (x : X) (p : s.P x) :
      PrincipalBundle.division (realCliffordSpinGroupZero n) p (φ.toEquiv x p) = g :=
    (hd_eq ⟨x, p⟩).symm.trans (hdg (mem_univ x))
  rcases hgT with rfl | rfl
  · exact .inl <| ext fun x p ↦ by
      simpa only [refl_toEquiv, _root_.Equiv.refl_apply, op_one, one_smul] using
        (PrincipalBundle.division_eq_iff.1 (hdiv x p)).symm
  · exact .inr <| ext fun x p ↦ by
      rw [negOne_toEquiv_apply]
      exact (PrincipalBundle.division_eq_iff.1 (hdiv x p)).symm

/-- Over a preconnected base, any two equivalences between the same pair of Spin structures are
equal or differ by the sheet-exchange automorphism `Equiv.negOne`. -/
theorem eq_or_eq_negOne_trans [PreconnectedSpace X] {s t : SpinStructure F E n}
    (φ ψ : s.Equiv t) :
    φ = ψ ∨ φ = (negOne s).trans ψ := by
  rcases eq_refl_or_eq_negOne (φ.trans ψ.symm) with h | h
  · left
    calc
      φ = (φ.trans ψ.symm).trans ψ := by simp [trans_assoc]
      _ = ψ := by rw [h, refl_trans]
  · right
    calc
      φ = (φ.trans ψ.symm).trans ψ := by simp [trans_assoc]
      _ = (negOne s).trans ψ := by rw [h]

end TauCeti.OrthonormalFrameLift.Equiv

/-! ### Induced fibre orientations -/

namespace TauCeti.OrthonormalFrameLift

variable {X : Type*} [TopologicalSpace X] {F : Type*} {E : X → Type w}
  [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)] {n : ℕ}
  {G : Type*} [Group G] [TopologicalSpace G] {ρ : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)}

/-- The **orientation of the fibre `E x` induced by a lift** `s` of the orthonormal frame bundle and
a model orientation `o` of `EuclideanSpace ℝ (Fin n)`: the orientation to which the frame of a
chosen point of `s.P x` transports `o`. When `G` acts by transformations of positive determinant,
every frame `s.frameAt p` over `x` transports `o` to it
(`TauCeti.OrthonormalFrameLift.fiberOrientation_eq_map_frameAt`). -/
def fiberOrientation (s : OrthonormalFrameLift F E n G ρ)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (x : X) :
    Orientation ℝ (E x) (Fin n) :=
  Orientation.map (Fin n) (s.frameAt (Classical.arbitrary (s.P x))).toLinearEquiv o

/-- If `ρ g` has positive determinant, the frames `p` and `p • g` transport a model orientation to
the same orientation of `E x`. -/
private theorem map_frameAt_op_smul (s : OrthonormalFrameLift F E n G ρ)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) {x : X} (p : s.P x) {g : G}
    (hg : 0 < (LinearEquiv.det (ρ g) : ℝ)) :
    Orientation.map (Fin n) (s.frameAt (op g • p)).toLinearEquiv o =
      Orientation.map (Fin n) (s.frameAt p).toLinearEquiv o := by
  -- In coordinates, the frame of `p • g` is the frame of `p` after the transformation `R` of `g`.
  let e := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  let R : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := (e.symm.trans (ρ g)).trans e
  have hR : (s.frameAt (op g • p)).toLinearEquiv = R.trans (s.frameAt p).toLinearEquiv := by
    ext v
    simpa [R, e] using s.frameAt_smul p g v.ofLp
  rw [hR, Orientation.map_trans, (o.map_eq_iff_det_pos R (by simp)).2]
  rwa [← LinearEquiv.coe_det, LinearEquiv.det_conj]

/-- If `G` acts by transformations of positive determinant, every frame `s.frameAt p` over `x`
transports `o` to `s.fiberOrientation o x`. -/
theorem fiberOrientation_eq_map_frameAt (s : OrthonormalFrameLift F E n G ρ)
    (hρ : ∀ g, 0 < (LinearEquiv.det (ρ g) : ℝ))
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) {x : X} (p : s.P x) :
    s.fiberOrientation o x = Orientation.map (Fin n) (s.frameAt p).toLinearEquiv o := by
  rw [fiberOrientation]
  -- Compare the chosen frame `p₀` with `p = p₀ • g`.
  generalize Classical.arbitrary (s.P x) = p₀
  obtain ⟨g, hg⟩ : ∃ g, PrincipalBundle.division G p₀ p = g := ⟨_, rfl⟩
  obtain rfl : op g • p₀ = p := hg ▸ PrincipalBundle.smul_division p₀ p
  rw [map_frameAt_op_smul s o p₀ (hρ g)]

/-- Reversing the model orientation reverses the induced orientation of every fibre. -/
@[simp]
theorem fiberOrientation_neg (s : OrthonormalFrameLift F E n G ρ)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (x : X) :
    s.fiberOrientation (-o) x = -s.fiberOrientation o x := by
  simp [fiberOrientation, Orientation.map_neg]

end TauCeti.OrthonormalFrameLift

namespace TauCeti.SpinStructure

open OrthonormalFrameLift

section EquivarianceAndFibers

variable {X : Type*} [TopologicalSpace X] {F : Type*} {E : X → Type w}
  [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)] {n : ℕ}

/-! ### Induced fibre orientations of a Spin structure -/

omit [TopologicalSpace X] [TopologicalSpace (TotalSpace F E)] in
private theorem mk_cast_orientation_eq_toOrientationCover
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))
    (q : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin n))) {x : X} (hq : q.proj = x) :
    (⟨x, hq ▸ Orientation.map (Fin n) q.frame.toLinearEquiv o⟩ :
      VectorBundleOrientationCover F E (Fin n)) =
      OrthonormalFrameBundle.toOrientationCover o q := by
  cases hq
  exact (OrthonormalFrameBundle.toOrientationCover_eq_mk o q).symm

/-- Every point of `P` sends `o` in the orientation double cover to `s.fiberOrientation o` over its
base point. -/
@[simp]
theorem toOrientationCover_toFrame (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))
    (p : TotalSpace (realCliffordSpinGroupZero n) s.P) :
    OrthonormalFrameBundle.toOrientationCover o (s.toFrame p) =
      ⟨p.proj, s.fiberOrientation o p.proj⟩ := by
  obtain ⟨x, p⟩ := p
  -- `Spin(n)` acts on frames through `SO(n)`, by transformations of determinant `1`.
  rw [s.toFrame_mk, OrthonormalFrameBundle.toOrientationCover_eq_mk,
    s.fiberOrientation_eq_map_frameAt
      (fun g ↦ by simp [QuadraticMap.det_coe_specialOrthogonalGroup]) o p]

/-- The orientation of `E x` transported from `o` along the frame of `(x, p)` is
`s.fiberOrientation o x`. -/
theorem map_frame_toFrame (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))
    (p : TotalSpace (realCliffordSpinGroupZero n) s.P) :
    (s.proj_toFrame p) ▸ Orientation.map (Fin n) (s.toFrame p).frame.toLinearEquiv o =
      s.fiberOrientation o p.proj := by
  have h := s.toOrientationCover_toFrame o p
  rw [← mk_cast_orientation_eq_toOrientationCover o (s.toFrame p) (s.proj_toFrame p),
    VectorBundleOrientationCover.mk_eq_mk_iff] at h
  exact h

/-- Equivalent Spin structures induce the same orientation on every fibre. -/
theorem _root_.TauCeti.OrthonormalFrameLift.Equiv.fiberOrientation_eq
    {s t : SpinStructure F E n} (φ : s.Equiv t)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (x : X) :
    t.fiberOrientation o x = s.fiberOrientation o x := by
  obtain ⟨p⟩ := s.nonempty_P x
  have ht := t.toOrientationCover_toFrame o (φ.toHomeomorph ⟨x, p⟩)
  rw [φ.toFrame_toHomeomorph, s.toOrientationCover_toFrame, φ.proj_toHomeomorph,
    VectorBundleOrientationCover.mk_eq_mk_iff] at ht
  exact ht.symm

/-- Pulling back a Spin structure along a continuous map pulls back its induced fibre
orientations. -/
@[simp]
theorem fiberOrientation_pullback {Y : Type*} [TopologicalSpace Y] {K : Type*} [FunLike K Y X]
    [ContinuousMapClass K Y X] (s : SpinStructure F E n) (f : K)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (y : Y) :
    fiberOrientation (s.pullback f) o y = s.fiberOrientation o (f y) := by
  obtain ⟨p⟩ := s.nonempty_P (f y)
  obtain ⟨φ₁, hfr⟩ := s.exists_toFrame_eq_mk ⟨f y, p⟩
  have h₁ := toOrientationCover_toFrame (s.pullback f) o ⟨y, p⟩
  rw [s.toFrame_pullback_mk f y p hfr, OrthonormalFrameBundle.toOrientationCover_eq_mk,
    VectorBundleOrientationCover.mk_eq_mk_iff] at h₁
  have h₂ := s.toOrientationCover_toFrame o ⟨f y, p⟩
  rw [hfr, OrthonormalFrameBundle.toOrientationCover_eq_mk,
    VectorBundleOrientationCover.mk_eq_mk_iff] at h₂
  exact h₁.symm.trans h₂

/-- Transporting a Spin structure along fibrewise isometries `Φ x : E x ≃ₗᵢ[ℝ] E' x` transports
its induced fibre orientations along `Φ`. -/
@[simp]
theorem fiberOrientation_map {F' : Type*} {E' : X → Type w}
    [TopologicalSpace (TotalSpace F' E')] [∀ x, NormedAddCommGroup (E' x)]
    [∀ x, InnerProductSpace ℝ (E' x)] (s : SpinStructure F E n) {Φ : ∀ x, E x ≃ₗᵢ[ℝ] E' x}
    (hΦ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, Φ v.proj v.snd⟩ : TotalSpace F' E'))
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (x : X) :
    fiberOrientation (s.map Φ hΦ) o x =
      Orientation.map (Fin n) (Φ x).toLinearEquiv (s.fiberOrientation o x) := by
  obtain ⟨p⟩ := s.nonempty_P x
  obtain ⟨φ, hfr⟩ := s.exists_toFrame_eq_mk ⟨x, p⟩
  have hmap : (s.map Φ hΦ).toFrame ⟨x, p⟩ = OrthonormalFrameBundle.map Φ ⟨x, φ⟩ :=
    (s.toFrame_map ⟨x, p⟩).trans (congrArg _ hfr)
  have h₁ := toOrientationCover_toFrame (s.map Φ hΦ) o ⟨x, p⟩
  rw [hmap, OrthonormalFrameBundle.map_mk,
    OrthonormalFrameBundle.toOrientationCover_eq_mk,
    VectorBundleOrientationCover.mk_eq_mk_iff] at h₁
  have h₂ := s.toOrientationCover_toFrame o ⟨x, p⟩
  rw [hfr, OrthonormalFrameBundle.toOrientationCover_eq_mk,
    VectorBundleOrientationCover.mk_eq_mk_iff] at h₂
  rw [← h₁, ← h₂, LinearIsometryEquiv.toLinearEquiv_trans, Orientation.map_trans]

end EquivarianceAndFibers

/-! ### Induced bundle orientation -/

section Orientation

variable {X : Type*} [TopologicalSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : X → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {n : ℕ}

/-- The **orientation of a vector bundle induced by a Spin structure** `s` and a model orientation
`o` of `EuclideanSpace ℝ (Fin n)`: at each base point `x`, every point of `s.P x` transports `o`
along its orthonormal frame to the orientation `s.fiberOrientation o x` of `E x`. -/
def orientation (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) :
    VectorBundleOrientation F E (Fin n) :=
  VectorBundleOrientation.ofContinuous (s.fiberOrientation o) <| by
    rw [(FiberBundle.isQuotientMap_proj
      (F := realCliffordSpinGroupZero n) (E := s.P)).continuous_iff]
    exact ((OrthonormalFrameBundle.continuous_toOrientationCover Fact.out o).comp
      s.continuous_toFrame).congr fun p ↦ s.toOrientationCover_toFrame o p

@[simp]
theorem orientation_apply (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (x : X) :
    s.orientation o x = s.fiberOrientation o x := by
  rw [orientation, VectorBundleOrientation.coe_ofContinuous]

/-- Every frame in the image of `s.toFrame` is positively oriented for `s.orientation o`. -/
theorem toFrame_mem_orientedFrames (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))
    (p : TotalSpace (realCliffordSpinGroupZero n) s.P) :
    s.toFrame p ∈ OrthonormalFrameBundle.orientedFrames (s.orientation o) o := by
  rw [OrthonormalFrameBundle.mem_orientedFrames_iff_toOrientationCover,
    s.toOrientationCover_toFrame, s.proj_toFrame, s.orientation_apply]

/-- The orientation `s.orientation o` is the unique bundle orientation for which every frame in the
image of `s.toFrame` is positively oriented. -/
theorem orientation_eq_of_toFrame_mem_orientedFrames (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))
    {oE : VectorBundleOrientation F E (Fin n)}
    (h : ∀ p, s.toFrame p ∈ OrthonormalFrameBundle.orientedFrames oE o) :
    oE = s.orientation o := by
  ext x
  obtain ⟨p⟩ := s.nonempty_P x
  have hp := OrthonormalFrameBundle.mem_orientedFrames_iff_toOrientationCover.1 (h ⟨x, p⟩)
  rw [s.toOrientationCover_toFrame, s.proj_toFrame, VectorBundleOrientationCover.mk_eq_mk_iff] at hp
  rw [s.orientation_apply]
  exact hp.symm

/-- Reversing the model orientation of `ℝⁿ` reverses the bundle orientation induced by a Spin
structure. -/
@[simp]
theorem orientation_neg (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) :
    s.orientation (-o) = -s.orientation o := by
  ext x
  simp

/-- Equivalent Spin structures induce the same orientation of the underlying vector bundle. -/
theorem _root_.TauCeti.OrthonormalFrameLift.Equiv.orientation_eq {s t : SpinStructure F E n}
    (φ : s.Equiv t)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) :
    t.orientation o = s.orientation o := by
  ext x
  simp [φ.fiberOrientation_eq]

/-- Pulling back the bundle orientation `s.orientation o` along `f : C(Y, X)` agrees fibrewise with
the fibre orientation of the pulled-back Spin structure `s.pullback f`. -/
theorem pullback_orientation_apply {Y : Type*} [TopologicalSpace Y] (s : SpinStructure F E n)
    (f : C(Y, X)) (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (y : Y) :
    (s.orientation o).pullback f y = fiberOrientation (s.pullback f) o y := by
  rw [VectorBundleOrientation.pullback_apply, s.orientation_apply, s.fiberOrientation_pullback]

/-- Transporting a Spin structure along fibrewise isometries of vector bundles transports its
induced bundle orientation along them. -/
theorem orientation_map_apply {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {E' : X → Type w} [TopologicalSpace (TotalSpace F' E')] [∀ x, NormedAddCommGroup (E' x)]
    [∀ x, InnerProductSpace ℝ (E' x)] [FiberBundle F' E'] [VectorBundle ℝ F' E']
    (s : SpinStructure F E n) {Φ : ∀ x, E x ≃ₗᵢ[ℝ] E' x}
    (hΦ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, Φ v.proj v.snd⟩ : TotalSpace F' E'))
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (x : X) :
    orientation (s.map Φ hΦ) o x =
      Orientation.map (Fin n) (Φ x).toLinearEquiv (s.orientation o x) := by
  rw [orientation_apply, orientation_apply, fiberOrientation_map]

/-- **Every real vector bundle carrying a Spin structure is orientable.** -/
theorem nonempty_vectorBundleOrientation (s : SpinStructure F E n) :
    Nonempty (VectorBundleOrientation F E (Fin n)) :=
  ⟨s.orientation (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation⟩

/-! ### The map onto positively oriented orthonormal frames -/

/-- The image of the frame map of a Spin structure is the set of positively oriented orthonormal
frames for its induced orientation. -/
theorem range_toFrame_eq_orientedFrames (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) :
    Set.range s.toFrame = OrthonormalFrameBundle.orientedFrames (s.orientation o) o := by
  refine Subset.antisymm (range_subset_iff.2 (s.toFrame_mem_orientedFrames o)) fun q hq ↦ ?_
  obtain ⟨p₀⟩ := s.nonempty_P q.proj
  obtain ⟨u, hu, huq⟩ := OrthonormalFrameBundle.SMulMemIff.exists_mem_smul_eq
    (H := specialOrthogonalGroup _) (s.toFrame_mem_orientedFrames o ⟨q.proj, p₀⟩) hq
    (s.proj_toFrame ⟨q.proj, p₀⟩)
  obtain ⟨g, hg⟩ := realCliffordSpinToEuclideanSpecialOrthogonal_surjective n ⟨u, hu⟩
  refine ⟨op g • ⟨q.proj, p₀⟩, ?_⟩
  rw [s.toFrame_op_smul, hg, huq]

/-- The frame map of a Spin structure, codomain-restricted to the positively oriented orthonormal
frames for the induced bundle orientation. -/
def toOrientedFrames (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))
    (p : TotalSpace (realCliffordSpinGroupZero n) s.P) :
    OrthonormalFrameBundle.orientedFrames (s.orientation o) o :=
  ⟨s.toFrame p, s.toFrame_mem_orientedFrames o p⟩

@[simp]
theorem coe_toOrientedFrames (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))
    (p : TotalSpace (realCliffordSpinGroupZero n) s.P) :
    (s.toOrientedFrames o p : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin n))) =
      s.toFrame p :=
  (rfl)

theorem proj_coe_toOrientedFrames (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))
    (p : TotalSpace (realCliffordSpinGroupZero n) s.P) :
    (s.toOrientedFrames o p : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin n))).proj =
      p.proj :=
  s.proj_toFrame p

/-- The lifted frame map into positively oriented frames is continuous. -/
theorem continuous_toOrientedFrames (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) :
    Continuous (s.toOrientedFrames o) :=
  s.continuous_toFrame.subtype_mk _

/-- The lifted frame map into positively oriented frames is equivariant along the Spin double cover
`realCliffordSpinToEuclideanSpecialOrthogonal n`. -/
theorem toOrientedFrames_op_smul (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))
    (g : realCliffordSpinGroupZero n) (p : TotalSpace (realCliffordSpinGroupZero n) s.P) :
    s.toOrientedFrames o (op g • p) =
      op (realCliffordSpinToEuclideanSpecialOrthogonal n g) • s.toOrientedFrames o p :=
  Subtype.ext <| by
    rw [OrthonormalFrameBundle.SMulMemIff.coe_smul]
    exact s.toFrame_op_smul g p

@[simp]
theorem toOrientedFrames_negOne_smul [NeZero n] (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))
    (p : TotalSpace (realCliffordSpinGroupZero n) s.P) :
    s.toOrientedFrames o (op (spinGroup.negOne (realCliffordForm n 0)
      (nondegenerate_realCliffordForm n 0).ne_zero) • p) = s.toOrientedFrames o p :=
  Subtype.ext (s.toFrame_negOne_smul p)

/-- Two points of `P` map to the same positively oriented frame if and only if they are equal or
differ by `-1 ∈ Spin(n)`. -/
theorem toOrientedFrames_eq_iff [NeZero n] (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))
    {p q : TotalSpace (realCliffordSpinGroupZero n) s.P} :
    s.toOrientedFrames o p = s.toOrientedFrames o q ↔
      p = q ∨
        p = op (spinGroup.negOne (realCliffordForm n 0)
          (nondegenerate_realCliffordForm n 0).ne_zero) • q :=
  Subtype.ext_iff.trans s.toFrame_eq_toFrame_iff

/-- Every automorphism of `s` is a deck transformation of `s.toOrientedFrames o`. -/
theorem _root_.TauCeti.OrthonormalFrameLift.Equiv.toOrientedFrames_toHomeomorph_self
    {s : SpinStructure F E n} (φ : s.Equiv s)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))
    (p : TotalSpace (realCliffordSpinGroupZero n) s.P) :
    s.toOrientedFrames o (φ.toHomeomorph p) = s.toOrientedFrames o p :=
  Subtype.ext (φ.toFrame_toHomeomorph p)

/-- The lifted frame map onto positively oriented orthonormal frames is surjective. -/
theorem toOrientedFrames_surjective (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) :
    Function.Surjective (s.toOrientedFrames o) := by
  rintro ⟨q, hq⟩
  rw [← s.range_toFrame_eq_orientedFrames o] at hq
  obtain ⟨p, rfl⟩ := hq
  exact ⟨p, rfl⟩

/-! ### Covering map structure over positively oriented frames -/

section ContinuousRiemannian

variable [IsContinuousRiemannianBundle F E] [NeZero n]

/-- **The lifted frame map of a Spin structure is a covering map** onto the positively oriented
orthonormal frames of a continuous Riemannian vector bundle (with two-point fibres by
`ncard_preimage_toFrame_singleton` and quotient covering structure in
`isQuotientCoveringMap_toOrientedFrames`). -/
theorem isCoveringMap_toOrientedFrames (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) :
    IsCoveringMap (s.toOrientedFrames o) := by
  refine IsCoveringMap.of_equivariant_trivialization
    (projP := TotalSpace.proj)
    (projQ := fun q : OrthonormalFrameBundle.orientedFrames (s.orientation o) o ↦
      (q : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin n))).proj)
    (isCoveringMap_realCliffordSpinToEuclideanSpecialOrthogonal n)
    (s.continuous_toOrientedFrames o) (s.proj_coe_toOrientedFrames o)
    (fun g p ↦ TotalSpace.proj_smul (op g) p) (s.toOrientedFrames_op_smul o) fun q₀ ↦ ?_
  let x := (q₀ : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin n))).proj
  have : Nonempty X := ⟨x⟩
  have : FiniteDimensional ℝ F := s.finiteDimensional_model
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 (NeZero.pos n)
  have hF : Fintype.card (Fin n) = Module.finrank ℝ F :=
    (Fintype.card_fin n).trans s.finrank_model.symm
  obtain ⟨t, hxt, ht⟩ :=
    OrthonormalFrameBundle.exists_trivialization_orientedFrames (s.orientation o) o hF x
  let e := trivializationAt (realCliffordSpinGroupZero n) s.P x
  exact ⟨e, t, mem_baseSet_trivializationAt _ s.P x, hxt,
    fun g ⟨_, p⟩ hp ↦ e.snd_apply_smul hp p g,
    fun h q hq ↦ congrArg Prod.snd (ht h q hq)⟩

/-- The lifted frame map of a Spin structure onto positively oriented frames is an open map. -/
theorem isOpenMap_toOrientedFrames (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) :
    IsOpenMap (s.toOrientedFrames o) :=
  (s.isCoveringMap_toOrientedFrames o).isOpenMap

/-- The lifted frame map of a Spin structure onto positively oriented frames is a quotient map. -/
theorem isQuotientMap_toOrientedFrames (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) :
    IsQuotientMap (s.toOrientedFrames o) :=
  (s.isCoveringMap_toOrientedFrames o).isQuotientMap (s.toOrientedFrames_surjective o)

/-- The lifted frame map of a Spin structure onto positively oriented frames is an open quotient
map. -/
theorem isOpenQuotientMap_toOrientedFrames (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) :
    IsOpenQuotientMap (s.toOrientedFrames o) where
  surjective := s.toOrientedFrames_surjective o
  continuous := s.continuous_toOrientedFrames o
  isOpenMap := s.isOpenMap_toOrientedFrames o

/-- **The lifted frame map of a Spin structure is a quotient covering map** by the two-element
kernel of `Spin(n) → SO(n)` acting on the right on `P`. -/
theorem isQuotientCoveringMap_toOrientedFrames (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) :
    IsQuotientCoveringMap (s.toOrientedFrames o)
      (MonoidHom.ker (realCliffordSpinToEuclideanSpecialOrthogonal n :
        realCliffordSpinGroupZero n →*
          specialOrthogonalGroup (EuclideanSpace ℝ (Fin n)))).op := by
  let K := (MonoidHom.ker (realCliffordSpinToEuclideanSpecialOrthogonal n :
    realCliffordSpinGroupZero n →* specialOrthogonalGroup (EuclideanSpace ℝ (Fin n)))).op
  have hc : ContinuousConstSMul K (TotalSpace (realCliffordSpinGroupZero n) s.P) :=
    ⟨fun k ↦ continuous_const_smul (k : (realCliffordSpinGroupZero n)ᵐᵒᵖ)⟩
  have hfree : IsCancelSMul K (TotalSpace (realCliffordSpinGroupZero n) s.P) :=
    { right_cancel' k₁ k₂ p h := by
        have hfib : (k₁ : (realCliffordSpinGroupZero n)ᵐᵒᵖ) • p.snd =
            (k₂ : (realCliffordSpinGroupZero n)ᵐᵒᵖ) • p.snd :=
          TotalSpace.mk_inj.1 h
        exact Subtype.ext (MulOpposite.unop_injective (PrincipalBundle.smul_eq_smul_iff.1 hfib)) }
  refine (isQuotientCoveringMap_iff_isCoveringMap_and (s.toOrientedFrames o) K).2
    ⟨s.isCoveringMap_toOrientedFrames o, s.toOrientedFrames_surjective o, hc, hfree, ?_⟩
  intro p q
  rw [s.toOrientedFrames_eq_iff, MulAction.mem_orbit_iff]
  refine ⟨?_, ?_⟩
  · rintro (rfl | rfl)
    · exact ⟨1, one_smul _ _⟩
    · refine ⟨⟨op (spinGroup.negOne (realCliffordForm n 0)
        (nondegenerate_realCliffordForm n 0).ne_zero), ?_⟩, rfl⟩
      exact (mem_ker_realCliffordSpinToEuclideanSpecialOrthogonal_iff n).2 (.inr rfl)
  · rintro ⟨k, rfl⟩
    have hk : k.val.unop ∈ MonoidHom.ker (realCliffordSpinToEuclideanSpecialOrthogonal n :
        realCliffordSpinGroupZero n →* specialOrthogonalGroup (EuclideanSpace ℝ (Fin n)))
            := k.property
    rcases (mem_ker_realCliffordSpinToEuclideanSpecialOrthogonal_iff n).1 hk with h1 | hneg
    · left
      have hk1 : k = 1 := Subtype.ext (MulOpposite.unop_injective h1)
      rw [hk1, one_smul]
    · right
      have hkneg : (k : (realCliffordSpinGroupZero n)ᵐᵒᵖ) =
          op (spinGroup.negOne (realCliffordForm n 0)
            (nondegenerate_realCliffordForm n 0).ne_zero) :=
        MulOpposite.unop_injective hneg
      exact congrArg (· • q) hkneg

end ContinuousRiemannian

end Orientation

end TauCeti.SpinStructure
