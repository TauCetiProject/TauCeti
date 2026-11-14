/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Euclidean
public import TauCeti.Topology.VectorBundle.Orientation.OrientedFrame
public import TauCeti.Topology.VectorBundle.SpinStructure.Basic

import TauCeti.Topology.Covering.Pullback

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
   `TauCeti.SpinStructure.Equiv.negOne s : s.Equiv s` commuting with all equivalences and pullbacks.
   The fibres of `s.toFrame` are the two-point orbits `{p, p • (-1)}`
   (`TauCeti.SpinStructure.toFrame_eq_toFrame_iff`), so every automorphism `φ : s.Equiv s` acts on
   each fibre as the identity or as `-1`; over a preconnected base `Equiv.refl s` and
   `Equiv.negOne s` are the only automorphisms (`TauCeti.SpinStructure.Equiv.eq_refl_or_eq_negOne`),
   and any two equivalences `s.Equiv t` are equal or differ by `Equiv.negOne s`.

2. **Induced fibre and bundle orientations.** Because `SO(n)` acts by transformations of determinant
   `1`, all points of a fibre `s.P x` transport a model orientation `o` of `ℝⁿ` to the same
   orientation `s.fiberOrientation o x` of `E x`, compatible with negation, equivalences, and
   pullbacks (`TauCeti.SpinStructure.fiberOrientation_pullback`). When `E` is a vector bundle, the
   quotient property of `π : P → X` descends `OrthonormalFrameBundle.toOrientationCover o ∘
   s.toFrame` to a bundle orientation `s.orientation o : TauCeti.VectorBundleOrientation F E
   (Fin n)`. In particular, any vector bundle admitting a Spin structure is orientable
   (`TauCeti.SpinStructure.nonempty_vectorBundleOrientation`).

3. **Two-sheeted covering of positively oriented frames.** The image of `s.toFrame` is precisely the
   bundle `OrthonormalFrameBundle.orientedFrames (s.orientation o) o` of positively oriented
   orthonormal frames (`TauCeti.SpinStructure.range_toFrame_eq_orientedFrames`), so `s.toFrame`
   restricts to a continuous equivariant surjection `s.toOrientedFrames o`. When `E` is a
   continuous Riemannian bundle, comparing equivariant local trivializations of `s.P` and of
   `orientedFrames` identifies `s.toOrientedFrames o` locally with a pullback of the Spin double
   cover `Spin(n) → SO(n)`, proving that `s.toOrientedFrames o` is a covering map
   (`TauCeti.SpinStructure.isCoveringMap_toOrientedFrames`) and a quotient covering map by the
   two-element kernel of `Spin(n) → SO(n)`
   (`TauCeti.SpinStructure.isQuotientCoveringMap_toOrientedFrames`).

## Main definitions

* `TauCeti.SpinStructure.Equiv.negOne`: the sheet-exchange automorphism acting by `-1 ∈ Spin(n)`.
* `TauCeti.SpinStructure.fiberOrientation`: the fibre orientation induced by a Spin structure and an
  orientation of `EuclideanSpace ℝ (Fin n)`.
* `TauCeti.SpinStructure.orientation`: the bundle orientation induced by a Spin structure on a
  vector bundle.
* `TauCeti.SpinStructure.toOrientedFrames`: the lifted frame map into positively oriented frames.

## Main results

* `TauCeti.SpinStructure.toFrame_op_smul`, `TauCeti.SpinStructure.toFrame_eq_toFrame_iff`:
  `SO(n)`-equivariance and `{1, -1}`-fibres of `s.toFrame`.
* `TauCeti.SpinStructure.Equiv.eq_refl_or_eq_negOne`,
  `TauCeti.SpinStructure.Equiv.eq_or_eq_negOne_trans`: classification of equivalences over a
  preconnected base.
* `TauCeti.SpinStructure.fiberOrientation_pullback`,
  `TauCeti.SpinStructure.nonempty_vectorBundleOrientation`,
  `TauCeti.SpinStructure.Equiv.orientation_eq`: orientability and functoriality of the induced
  orientation.
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

section EquivarianceAndFibers

variable {X : Type*} [TopologicalSpace X] {F : Type*} {E : X → Type w}
  [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)] {n : ℕ} [NeZero n]

private theorem negOne_mul_comm (g : realCliffordSpinGroupZero n) :
    spinGroup.negOne (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0).ne_zero * g =
      g * spinGroup.negOne (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0).ne_zero :=
  Subtype.ext (by simp)

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
  rcases hq₀ : s.toFrame ⟨x, p⟩ with ⟨x₀, φ₀⟩
  rcases hq₁ : s.toFrame ⟨x, op g • p⟩ with ⟨x₁, φ₁⟩
  obtain rfl : x = x₀ := by
    symm
    simpa [hq₀] using s.proj_toFrame ⟨x, p⟩
  obtain rfl : x = x₁ := by
    symm
    simpa [hq₁] using s.proj_toFrame ⟨x, op g • p⟩
  refine OrthonormalFrameBundle.mk_eq_mk_iff.2 (LinearIsometryEquiv.ext fun w ↦ ?_)
  have hw := s.toFrame_smul x p g w.ofLp
  rw [WithLp.toLp_ofLp, hq₀, hq₁] at hw
  rw [TotalSpace.mk_inj.1 hw, LinearIsometryEquiv.trans_apply, unop_op]
  have hu := DFunLike.congr_fun (Unitary.coe_linearIsometryEquiv_apply
    ((realCliffordSpinToEuclideanSpecialOrthogonal n g :
      specialOrthogonalGroup (EuclideanSpace ℝ (Fin n))) :
      unitary (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))) w
  exact congrArg φ₀
    ((congrFun (LinearIsometryEquiv.coe_coe'' (Unitary.linearIsometryEquiv _)) w).symm.trans
      (hu.trans (realCliffordSpinToEuclideanSpecialOrthogonal_apply_apply n g w))).symm

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
    set g := PrincipalBundle.division (realCliffordSpinGroupZero n) q p
    have hpq : (⟨x, p⟩ : TotalSpace (realCliffordSpinGroupZero n) s.P) = op g • ⟨x, q⟩ :=
      congrArg (TotalSpace.mk' _ x) (PrincipalBundle.smul_division q p).symm
    rw [hpq] at h ⊢
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
      (nondegenerate_realCliffordForm n 0).ne_zero) • p.2 = p.2 :=
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

/-- Every fibre `E x` of a bundle carrying a Spin structure of rank `n` is finite-dimensional. -/
theorem finiteDimensional_fiber (s : SpinStructure F E n) (x : X) :
    FiniteDimensional ℝ (E x) := by
  obtain ⟨p⟩ := s.nonempty_P x
  have hproj : (s.toFrame ⟨x, p⟩).proj = x := s.proj_toFrame ⟨x, p⟩
  exact hproj ▸ (s.toFrame ⟨x, p⟩).frame.toLinearEquiv.finiteDimensional

/-- Every fibre `E x` of a bundle carrying a Spin structure of rank `n` has dimension `n`. -/
theorem finrank_fiber (s : SpinStructure F E n) (x : X) :
    Module.finrank ℝ (E x) = n := by
  obtain ⟨p⟩ := s.nonempty_P x
  have hproj : (s.toFrame ⟨x, p⟩).proj = x := s.proj_toFrame ⟨x, p⟩
  have h := (s.toFrame ⟨x, p⟩).frame.toLinearEquiv.finrank_eq
  rw [hproj, finrank_euclideanSpace_fin] at h
  exact h.symm

/-- Acting on `P` by `Spin(n)` preserves the induced point in the orientation double cover. -/
theorem toOrientationCover_toFrame_op_smul (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (g : realCliffordSpinGroupZero n)
    (p : TotalSpace (realCliffordSpinGroupZero n) s.P) :
    OrthonormalFrameBundle.toOrientationCover o (s.toFrame (op g • p)) =
      OrthonormalFrameBundle.toOrientationCover o (s.toFrame p) := by
  rw [s.toFrame_op_smul]
  exact OrthonormalFrameBundle.toOrientationCover_smul_of_det_pos Fact.out o
    (mem_specialOrthogonalGroup_iff_det_pos.1
      (realCliffordSpinToEuclideanSpecialOrthogonal n g).2) (s.toFrame p)

/-- Points in the same fibre of `P` induce the same point of the orientation double cover. -/
theorem toOrientationCover_toFrame_eq_of_proj_eq (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))
    {p q : TotalSpace (realCliffordSpinGroupZero n) s.P} (h : p.proj = q.proj) :
    OrthonormalFrameBundle.toOrientationCover o (s.toFrame p) =
      OrthonormalFrameBundle.toOrientationCover o (s.toFrame q) := by
  obtain ⟨x, p⟩ := p
  obtain ⟨y, q⟩ := q
  obtain rfl : x = y := h
  have hpq : (⟨x, p⟩ : TotalSpace (realCliffordSpinGroupZero n) s.P) =
      op (PrincipalBundle.division (realCliffordSpinGroupZero n) q p) • ⟨x, q⟩ :=
    congrArg (TotalSpace.mk' _ x) (PrincipalBundle.smul_division q p).symm
  rw [hpq, s.toOrientationCover_toFrame_op_smul]

/-! ### Central sheet involution and automorphisms -/

namespace Equiv

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
    simp only [_root_.Equiv.coe_fn_mk, smul_smul, ← op_mul, negOne_mul_comm]
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
  rw [toHomeomorph_apply, negOne_toEquiv_apply]
  rfl

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
  rcases φ.toEquiv_apply_eq_self_or_negOne_smul x p with h | h <;> rw [h]
  · exact .inl (PrincipalBundle.division_self p)
  · refine .inr (PrincipalBundle.division_eq_iff.2 rfl)

/-- For an automorphism `φ : s.Equiv s`, the division element `division _ p (φ.toEquiv x p)` is
independent of the choice of point `p` in the fibre `s.P x`. -/
theorem division_toEquiv_eq {s : SpinStructure F E n} (φ : s.Equiv s) (x : X) (p q : s.P x) :
    PrincipalBundle.division (realCliffordSpinGroupZero n) p (φ.toEquiv x p) =
      PrincipalBundle.division (realCliffordSpinGroupZero n) q (φ.toEquiv x q) := by
  set g := PrincipalBundle.division (realCliffordSpinGroupZero n) q p
  have hp : p = op g • q := (PrincipalBundle.smul_division q p).symm
  rw [hp, φ.map_smul, PrincipalBundle.division_smul_left, PrincipalBundle.division_smul_right]
  rcases φ.division_toEquiv_eq_one_or_negOne x q with hd | hd <;> rw [hd]
  · simp
  · rw [negOne_mul_comm g, inv_mul_cancel_left]

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
      d p.proj = PrincipalBundle.division (realCliffordSpinGroupZero n) p.2
        (φ.toEquiv p.proj p.2) :=
    φ.division_toEquiv_eq p.proj _ p.2
  have hd_cont : Continuous d := by
    rw [(FiberBundle.isQuotientMap_proj
      (F := realCliffordSpinGroupZero n) (E := s.P)).continuous_iff]
    exact (Continuous.division (f := TotalSpace.proj)
      (p := fun p : TotalSpace (realCliffordSpinGroupZero n) s.P ↦ p.2)
      (q := fun p : TotalSpace (realCliffordSpinGroupZero n) s.P ↦ φ.toEquiv p.proj p.2)
      continuous_id φ.continuous_toFun).congr fun p ↦ (hd_eq p).symm
  have hd_or (x : X) :
      d x = 1 ∨
        d x = spinGroup.negOne (realCliffordForm n 0)
          (nondegenerate_realCliffordForm n 0).ne_zero :=
    φ.division_toEquiv_eq_one_or_negOne x _
  have hcompl :
      {x : X | d x = 1}ᶜ =
        {x : X | d x = spinGroup.negOne (realCliffordForm n 0)
          (nondegenerate_realCliffordForm n 0).ne_zero} := by
    ext x
    simp only [mem_compl_iff, mem_ofPred_eq]
    refine ⟨(hd_or x).resolve_left, fun h h1 ↦ ?_⟩
    exact spinGroup.negOne_ne_one (realCliffordForm n 0)
      (nondegenerate_realCliffordForm n 0).ne_zero (h.symm.trans h1)
  have hc_neg :
      IsClosed {x : X | d x = spinGroup.negOne (realCliffordForm n 0)
        (nondegenerate_realCliffordForm n 0).ne_zero} :=
    isClosed_singleton.preimage hd_cont
  rw [← hcompl] at hc_neg
  have hclopen : IsClopen {x : X | d x = 1} :=
    ⟨isClosed_singleton.preimage hd_cont, isClosed_compl_iff.1 hc_neg⟩
  rcases isClopen_iff.1 hclopen with hempty | huniv
  · right
    refine ext fun x p ↦ ?_
    have hx : d x = spinGroup.negOne (realCliffordForm n 0)
        (nondegenerate_realCliffordForm n 0).ne_zero :=
      (hd_or x).resolve_left fun h1 ↦ hempty.subset h1
    have hdiv : PrincipalBundle.division (realCliffordSpinGroupZero n) p (φ.toEquiv x p) =
        spinGroup.negOne (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0).ne_zero :=
      (hd_eq ⟨x, p⟩).symm.trans hx
    rw [negOne_toEquiv_apply]
    exact (PrincipalBundle.division_eq_iff.1 hdiv).symm
  · left
    refine ext fun x p ↦ ?_
    have hx : d x = 1 := huniv.symm.subset (mem_univ x)
    have hdiv : PrincipalBundle.division (realCliffordSpinGroupZero n) p (φ.toEquiv x p) = 1 :=
      (hd_eq ⟨x, p⟩).symm.trans hx
    rw [refl_toEquiv, _root_.Equiv.refl_apply]
    simpa only [op_one, one_smul] using (PrincipalBundle.division_eq_iff.1 hdiv).symm

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

end Equiv

/-! ### Induced fibre orientations -/

omit [TopologicalSpace X] [TopologicalSpace (TotalSpace F E)] [NeZero n] in
private theorem mk_cast_orientation_eq_toOrientationCover
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))
    (q : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin n))) {x : X} (hq : q.proj = x) :
    (⟨x, hq ▸ Orientation.map (Fin n) q.frame.toLinearEquiv o⟩ :
      VectorBundleOrientationCover F E (Fin n)) =
      OrthonormalFrameBundle.toOrientationCover o q := by
  cases hq
  exact (OrthonormalFrameBundle.toOrientationCover_eq_mk o q).symm

/-- The **orientation of the fibre `E x` induced by a Spin structure** `s` and a model orientation
`o` of `EuclideanSpace ℝ (Fin n)`: every point of `s.P x` transports `o` along its orthonormal frame
to this same orientation of `E x`. -/
def fiberOrientation (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (x : X) :
    Orientation ℝ (E x) (Fin n) :=
  have hproj : (s.toFrame ⟨x, Classical.arbitrary (s.P x)⟩).proj = x :=
    s.proj_toFrame ⟨x, Classical.arbitrary (s.P x)⟩
  hproj ▸
    Orientation.map (Fin n)
      (s.toFrame ⟨x, Classical.arbitrary (s.P x)⟩).frame.toLinearEquiv o

/-- Every point of `P` sends `o` in the orientation double cover to `s.fiberOrientation o` over its
base point. -/
@[simp]
theorem toOrientationCover_toFrame (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))
    (p : TotalSpace (realCliffordSpinGroupZero n) s.P) :
    OrthonormalFrameBundle.toOrientationCover o (s.toFrame p) =
      ⟨p.proj, s.fiberOrientation o p.proj⟩ := by
  symm
  rw [fiberOrientation, mk_cast_orientation_eq_toOrientationCover]
  exact s.toOrientationCover_toFrame_eq_of_proj_eq o rfl

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

/-- Reversing the model orientation of `ℝⁿ` reverses the induced orientation on every fibre. -/
@[simp]
theorem fiberOrientation_neg (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (x : X) :
    s.fiberOrientation (-o) x = -s.fiberOrientation o x := by
  have hcast {a b : X} (hab : a = b) (v : Orientation ℝ (E a) (Fin n)) :
      (hab ▸ -v : Orientation ℝ (E b) (Fin n)) = -(hab ▸ v) := by
    cases hab
    rfl
  obtain ⟨p⟩ := s.nonempty_P x
  have hpos := s.map_frame_toFrame o ⟨x, p⟩
  have hneg := s.map_frame_toFrame (-o) ⟨x, p⟩
  dsimp only at hpos hneg
  rw [← hneg, ← hpos, Orientation.map_neg]
  exact hcast (s.proj_toFrame ⟨x, p⟩) _

/-- Equivalent Spin structures induce the same orientation on every fibre. -/
theorem Equiv.fiberOrientation_eq {s t : SpinStructure F E n} (φ : s.Equiv t)
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
    (s.pullback f).fiberOrientation o y = s.fiberOrientation o (f y) := by
  obtain ⟨p⟩ := s.nonempty_P (f y)
  rcases hfr : s.toFrame ⟨f y, p⟩ with ⟨x₁, φ₁⟩
  obtain rfl : f y = x₁ := by
    symm
    simpa [hfr] using s.proj_toFrame ⟨f y, p⟩
  let q : TotalSpace (realCliffordSpinGroupZero n) (s.pullback f).P := ⟨y, p⟩
  let φ₁' : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] ((f : Y → X) *ᵖ E) y := φ₁
  have hlift : OrthonormalFrameBundle.pullbackLift f ((s.pullback f).toFrame q) = ⟨f y, φ₁⟩ :=
    (s.pullbackLift_toFrame_pullback f q).trans hfr
  have hpull : (s.pullback f).toFrame q =
      (⟨y, φ₁'⟩ : OrthonormalFrameBundle ℝ F ((f : Y → X) *ᵖ E) (EuclideanSpace ℝ (Fin n))) :=
    (OrthonormalFrameBundle.pullbackHomeomorph (f : Y → X)).injective <|
      Subtype.ext <|
        (congrArg Subtype.val
          (OrthonormalFrameBundle.pullbackHomeomorph_apply (f : Y → X)
            ((s.pullback f).toFrame q))).trans <|
        (Prod.ext ((s.pullback f).proj_toFrame q)
          (hlift.trans
            (OrthonormalFrameBundle.pullbackLift_mk (F := F) (f : Y → X) y φ₁).symm)).trans
        (congrArg Subtype.val
          (OrthonormalFrameBundle.pullbackHomeomorph_apply (f : Y → X) ⟨y, φ₁'⟩)).symm
  have h₁ := (s.pullback f).toOrientationCover_toFrame o q
  rw [hpull, OrthonormalFrameBundle.toOrientationCover_eq_mk,
    VectorBundleOrientationCover.mk_eq_mk_iff] at h₁
  have h₂ := s.toOrientationCover_toFrame o ⟨f y, p⟩
  rw [hfr, OrthonormalFrameBundle.toOrientationCover_eq_mk,
    VectorBundleOrientationCover.mk_eq_mk_iff] at h₂
  exact h₁.symm.trans h₂

end EquivarianceAndFibers

/-! ### Induced bundle orientation -/

section Orientation

variable {X : Type*} [TopologicalSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : X → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {n : ℕ} [NeZero n]

/-- Over a nonempty base, the model fibre `F` of a vector bundle carrying a Spin structure of rank
`n` is finite-dimensional. -/
theorem finiteDimensional_model [Nonempty X] (s : SpinStructure F E n) :
    FiniteDimensional ℝ F := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have := s.finiteDimensional_fiber x
  exact ((trivializationAt F E x).linearEquivAt ℝ x
    (FiberBundle.mem_baseSet_trivializationAt' x)).finiteDimensional

/-- Over a nonempty base, the model fibre `F` of a vector bundle carrying a Spin structure of rank
`n` has dimension `n`. -/
theorem finrank_model [Nonempty X] (s : SpinStructure F E n) :
    Module.finrank ℝ F = n := by
  obtain ⟨x⟩ := ‹Nonempty X›
  rw [← ((trivializationAt F E x).linearEquivAt ℝ x
    (FiberBundle.mem_baseSet_trivializationAt' x)).finrank_eq, s.finrank_fiber x]

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
theorem Equiv.orientation_eq {s t : SpinStructure F E n} (φ : s.Equiv t)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) :
    t.orientation o = s.orientation o := by
  ext x
  simp [φ.fiberOrientation_eq]

/-- Pulling back the bundle orientation `s.orientation o` along `f : C(Y, X)` agrees fibrewise with
the fibre orientation of the pulled-back Spin structure `s.pullback f`. -/
theorem pullback_orientation_apply {Y : Type*} [TopologicalSpace Y] (s : SpinStructure F E n)
    (f : C(Y, X)) (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (y : Y) :
    (s.orientation o).pullback f y = (s.pullback f).fiberOrientation o y := by
  rw [VectorBundleOrientation.pullback_apply, s.orientation_apply, s.fiberOrientation_pullback]

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
  obtain ⟨u, hu, huq⟩ := OrthonormalFrameBundle.exists_mem_specialOrthogonalGroup_smul_eq
    (Fact.out : Fintype.card (Fin n) = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (s.toFrame_mem_orientedFrames o ⟨q.proj, p₀⟩) hq (s.proj_toFrame ⟨q.proj, p₀⟩)
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
  Subtype.ext (s.toFrame_op_smul g p)

@[simp]
theorem toOrientedFrames_negOne_smul (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))
    (p : TotalSpace (realCliffordSpinGroupZero n) s.P) :
    s.toOrientedFrames o (op (spinGroup.negOne (realCliffordForm n 0)
      (nondegenerate_realCliffordForm n 0).ne_zero) • p) = s.toOrientedFrames o p :=
  Subtype.ext (s.toFrame_negOne_smul p)

/-- Two points of `P` map to the same positively oriented frame if and only if they are equal or
differ by `-1 ∈ Spin(n)`. -/
theorem toOrientedFrames_eq_iff (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n))
    {p q : TotalSpace (realCliffordSpinGroupZero n) s.P} :
    s.toOrientedFrames o p = s.toOrientedFrames o q ↔
      p = q ∨
        p = op (spinGroup.negOne (realCliffordForm n 0)
          (nondegenerate_realCliffordForm n 0).ne_zero) • q :=
  Subtype.ext_iff.trans s.toFrame_eq_toFrame_iff

/-- Every automorphism of `s` is a deck transformation of `s.toOrientedFrames o`. -/
theorem Equiv.toOrientedFrames_toHomeomorph_self {s : SpinStructure F E n} (φ : s.Equiv s)
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

variable [IsContinuousRiemannianBundle F E]

/-- **The lifted frame map of a Spin structure is a two-sheeted covering map** onto the positively
oriented orthonormal frames of a continuous Riemannian vector bundle. -/
theorem isCoveringMap_toOrientedFrames (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) :
    IsCoveringMap (s.toOrientedFrames o) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · have : IsEmpty (TotalSpace (realCliffordSpinGroupZero n) s.P) := ⟨fun p ↦ isEmptyElim p.proj⟩
    exact .of_isEmpty _
  have : FiniteDimensional ℝ F := s.finiteDimensional_model
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 (NeZero.pos n)
  have hF : Fintype.card (Fin n) = Module.finrank ℝ F :=
    (Fintype.card_fin n).trans s.finrank_model.symm
  intro q₀
  let x := (q₀ : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin n))).proj
  let e := trivializationAt (realCliffordSpinGroupZero n) s.P x
  have hxe : x ∈ e.baseSet := mem_baseSet_trivializationAt _ s.P x
  obtain ⟨t, hxt, ht⟩ :=
    OrthonormalFrameBundle.exists_trivialization_orientedFrames (s.orientation o) o hF x
  let W : Set X := e.baseSet ∩ t.baseSet
  have hW : IsOpen W := e.open_baseSet.inter t.open_baseSet
  have hxW : x ∈ W := ⟨hxe, hxt⟩
  let pr : OrthonormalFrameBundle.orientedFrames (s.orientation o) o → X :=
    fun q ↦ (q : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin n))).proj
  let V : Set (OrthonormalFrameBundle.orientedFrames (s.orientation o) o) := pr ⁻¹' W
  have hV : IsOpen V :=
    hW.preimage (OrthonormalFrameBundle.continuous_proj.comp continuous_subtype_val)
  have hpreV_eq : s.toOrientedFrames o ⁻¹' V = π (realCliffordSpinGroupZero n) s.P ⁻¹' W := by
    ext p
    simp [V, pr]
  have hpreV : IsOpen (s.toOrientedFrames o ⁻¹' V) :=
    hpreV_eq ▸ hW.preimage (FiberBundle.continuous_proj (realCliffordSpinGroupZero n) s.P)
  refine IsCoveringMapOn.of_isCoveringMap_restrictPreimage _ hV hpreV ?_ q₀ hxW
  have hWe : W ⊆ e.baseSet := fun _ hy ↦ hy.1
  have hWt : W ⊆ t.baseSet := fun _ hy ↦ hy.2
  -- Identify `s.toOrientedFrames o ⁻¹' V` and `V` with `W × Spin(n)` and `W × SO(n)` via `e`
  -- and `t`; `hSet` is written directly so its underlying coercion is definitional under `module`.
  let hSet : (s.toOrientedFrames o ⁻¹' V) ≃ₜ (π (realCliffordSpinGroupZero n) s.P ⁻¹' W) :=
    { toFun q := ⟨q.1, hpreV_eq ▸ q.2⟩
      invFun q := ⟨q.1, hpreV_eq.symm ▸ q.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := continuous_subtype_val.subtype_mk _
      continuous_invFun := continuous_subtype_val.subtype_mk _ }
  let hDom : (s.toOrientedFrames o ⁻¹' V) ≃ₜ W × realCliffordSpinGroupZero n :=
    hSet.trans (e.preimageHomeomorph hWe)
  let hCod : V ≃ₜ W × specialOrthogonalGroup (EuclideanSpace ℝ (Fin n)) :=
    t.preimageHomeomorph hWt
  -- Read the local unit section `σ` of `s.P` in `t` to obtain the transition map `c : W → SO(n)`
  -- such that `(y, g)` maps to `(y, c y * ρ g)`, realizing the local map as `Pullback.fst`.
  let σ : W → TotalSpace (realCliffordSpinGroupZero n) s.P :=
    fun y ↦ e.toOpenPartialHomeomorph.symm (y.1, 1)
  have hσ_cont : Continuous σ :=
    e.continuousOn_invFun.comp_continuous (continuous_subtype_val.prodMk continuous_const)
      fun y ↦ e.mem_target.2 y.2.1
  have hσ_proj (y : W) : (σ y).proj = y.1 := e.proj_symm_apply' y.2.1
  let c : W → specialOrthogonalGroup (EuclideanSpace ℝ (Fin n)) :=
    fun y ↦ (t (s.toOrientedFrames o (σ y))).2
  have hc_cont : Continuous c :=
    continuous_snd.comp <| t.continuousOn_toFun.comp_continuous
      ((s.continuous_toOrientedFrames o).comp hσ_cont) fun y ↦ by
        rw [t.mem_source, s.proj_coe_toOrientedFrames, hσ_proj]
        exact y.2.2
  let ρ := realCliffordSpinToEuclideanSpecialOrthogonal n
  let f : W × specialOrthogonalGroup (EuclideanSpace ℝ (Fin n)) →
      specialOrthogonalGroup (EuclideanSpace ℝ (Fin n)) :=
    fun yh ↦ (c yh.1)⁻¹ * yh.2
  have hf_cont : Continuous f := (hc_cont.comp continuous_fst).inv.mul continuous_snd
  let hPull : W × realCliffordSpinGroupZero n ≃ₜ _root_.Function.Pullback f ρ :=
    { toFun yg := ⟨((yg.1, c yg.1 * ρ yg.2), yg.2), inv_mul_cancel_left (c yg.1) (ρ yg.2)⟩
      invFun z := (z.1.1.1, z.1.2)
      left_inv _ := rfl
      right_inv z := by
        rcases z with ⟨⟨⟨y, h⟩, g⟩, hzg⟩
        dsimp only [f] at hzg
        exact Subtype.ext (Prod.ext (Prod.ext rfl (inv_mul_eq_iff_eq_mul.1 hzg).symm) rfl)
      continuous_toFun :=
        ((continuous_fst.prodMk ((hc_cont.comp continuous_fst).mul
          ((map_continuous ρ).comp continuous_snd))).prodMk continuous_snd).subtype_mk _
      continuous_invFun :=
        (continuous_fst.comp _root_.Function.Pullback.continuous_fst).prodMk
          _root_.Function.Pullback.continuous_snd }
  have hlocal :
      V.restrictPreimage (s.toOrientedFrames o) =
        hCod.symm ∘ _root_.Function.Pullback.fst ∘ hPull ∘ hDom := by
    funext p
    apply hCod.injective
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, Homeomorph.apply_symm_apply]
    have hpW : p.1.proj ∈ W := by simpa only [hpreV_eq, mem_preimage] using p.2
    let y : W := ⟨p.1.proj, hpW⟩
    let g : realCliffordSpinGroupZero n := (e p.1).2
    have hDom_p : hDom p = (y, g) :=
      (Homeomorph.trans_apply hSet (e.preimageHomeomorph hWe) p).trans
        (e.preimageHomeomorph_apply hWe (hSet p))
    have hPull_fst : _root_.Function.Pullback.fst (hPull (y, g)) = (y, c y * ρ g) := rfl
    rw [hDom_p, hPull_fst]
    have hp_eq : p.1 = op g • σ y := by
      have he1 : (e p.1).1 = y.1 := e.coe_fst' hpW.1
      calc
        p.1 = e.toOpenPartialHomeomorph.symm (e p.1) :=
          (e.symm_apply_apply (e.mem_source.2 hpW.1)).symm
        _ = e.toOpenPartialHomeomorph.symm (y.1, g) := by rw [← he1]
        _ = op g • σ y := e.symm_apply_eq_smul hpW.1 g
    have hq_mem : (s.toOrientedFrames o (σ y) :
        OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin n))).proj ∈ t.baseSet := by
      rw [s.proj_coe_toOrientedFrames, hσ_proj]
      exact hpW.2
    have hCod_p :
        hCod (V.restrictPreimage (s.toOrientedFrames o) p) =
          (⟨pr (s.toOrientedFrames o p.1), p.2⟩, (t (s.toOrientedFrames o p.1)).2) :=
      t.preimageHomeomorph_apply hWt (V.restrictPreimage (s.toOrientedFrames o) p)
    rw [hCod_p]
    refine Prod.ext (Subtype.ext ?_) ?_
    · exact s.proj_coe_toOrientedFrames o p.1
    · dsimp only
      rw [hp_eq, s.toOrientedFrames_op_smul, ht _ _ hq_mem]
  rw [hlocal]
  exact ((((isCoveringMap_realCliffordSpinToEuclideanSpecialOrthogonal n).pullback_fst
    hf_cont).comp_homeomorph hPull).homeomorph_comp hCod.symm).comp_homeomorph hDom

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
        have hfib : (k₁ : (realCliffordSpinGroupZero n)ᵐᵒᵖ) • p.2 =
            (k₂ : (realCliffordSpinGroupZero n)ᵐᵒᵖ) • p.2 :=
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
    have hk : k.1.unop ∈ MonoidHom.ker (realCliffordSpinToEuclideanSpecialOrthogonal n :
        realCliffordSpinGroupZero n →* specialOrthogonalGroup (EuclideanSpace ℝ (Fin n))) := k.2
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
