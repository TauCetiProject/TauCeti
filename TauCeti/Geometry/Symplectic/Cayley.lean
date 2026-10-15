/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import TauCeti.Geometry.Symplectic.TameMetric

/-!
# The Cayley transform of tame complex structures

Let `ω` be a symplectic form on a finite-dimensional real vector space `V` and let `J₀` be an
`ω`-compatible complex structure, with metric `g₀ = ω(·, J₀ ·)`. Every complex structure `J`
can be written `J = J₀ A` with `A = -J₀ J`, and then `ω(v, J v) = g₀(v, A v)`. So `ω` tames `J`
exactly when `A` is positive for `g₀`, and the Cayley transform

`C = (A - 1)(A + 1)⁻¹ = -(1 + J₀ J)(1 - J₀ J)⁻¹`

is then a strict contraction for `g₀`. The identity `J² = -1` becomes the linear condition
`C J₀ = -J₀ C`. Conversely every `J₀`-antilinear strict contraction `C` comes from the tame
structure `J = J₀ (1 + C)(1 - C)⁻¹`.

Thus the Cayley transform `TauCeti.AlmostComplexStructure.cayley` identifies the `ω`-tame
complex structures with the *Cayley ball* `TauCeti.SymplecticForm.cayleyBall ω J₀`: the
`J₀`-antilinear endomorphisms that strictly contract `v ↦ ω(v, J₀ v)`. This ball is convex and
contains `0`, the transform of `J₀`. So the Cayley transform is a global coordinate system on the
tame structures with values in the linear space of `J₀`-antilinear endomorphisms. Straight lines
in the ball give explicit families of tame structures: two tame structures are joined by the
inverse transforms of the points of the segment between their Cayley transforms. This is the
linear algebra behind the contractibility of the space of tame almost complex structures.

## Main definitions

* `TauCeti.SymplecticForm.cayleyBall`: the `J₀`-antilinear strict contractions for
  `v ↦ ω(v, J₀ v)`.
* `TauCeti.SymplecticForm.Compatible.cayleyEquiv`: for `ω`-compatible `J₀`, the Cayley transform
  as a bijection from the `ω`-tame complex structures onto the Cayley ball.

## Main results

* `TauCeti.SymplecticForm.Tames.convex_cayleyBall`: the Cayley ball is convex.
* `TauCeti.SymplecticForm.Tames.isUnit_one_sub_mul` and
  `TauCeti.SymplecticForm.isUnit_one_sub_of_mem_cayleyBall`: the denominators `1 - J₀ J` of the
  transform and `1 - C` of its inverse are invertible.
* `TauCeti.SymplecticForm.Tames.cayley_mul_one_sub_mul`: the Cayley transform `C` of `J` is
  characterized by `C (1 - J₀ J) = -(1 + J₀ J)`.
* `TauCeti.SymplecticForm.Compatible.cayley_mem_cayleyBall`: the Cayley transform of a tame
  structure lies in the Cayley ball.
* `TauCeti.SymplecticForm.Compatible.cayleyEquiv_symm_apply_toLinearMap`: the inverse transform
  is `C ↦ J₀ (1 + C)(1 - C)⁻¹`.
* `TauCeti.SymplecticForm.Compatible.cayleyEquiv_self`: the transform sends `J₀` to `0`.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 2.5 (linear complex structures, and the contractibility of the spaces of
  compatible and of tame ones).
* M. Audin and J. Lafontaine (eds.), *Holomorphic Curves in Symplectic Geometry*, Progress in
  Mathematics **117**, Birkhäuser, 1994, Chapter II (Sévennec's Cayley-transform argument for
  tame structures).
-/

public section

noncomputable section

namespace TauCeti

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

namespace SymplecticForm

variable {ω : SymplecticForm V} {J₀ J : AlmostComplexStructure V}

variable (ω J₀) in
/-- The **Cayley ball** of `ω` at `J₀`: the endomorphisms `C` that anticommute with `J₀` and are
strict contractions for the quadratic form `v ↦ ω(v, J₀ v)`. For `ω`-compatible `J₀` it is the
image of the `ω`-tame complex structures under the Cayley transform. -/
def cayleyBall : Set (Module.End ℝ V) :=
  {C | C * J₀.toLinearMap = -(J₀.toLinearMap * C) ∧
    ∀ v, v ≠ 0 → ω (C v) (J₀ (C v)) < ω v (J₀ v)}

/-- Membership in the Cayley ball: anticommutation with `J₀` and strict contraction of
`v ↦ ω(v, J₀ v)`. -/
@[simp]
lemma mem_cayleyBall {C : Module.End ℝ V} :
    C ∈ ω.cayleyBall J₀ ↔ C * J₀.toLinearMap = -(J₀.toLinearMap * C) ∧
      ∀ v, v ≠ 0 → ω (C v) (J₀ (C v)) < ω v (J₀ v) := Iff.rfl

/-- The Cayley transform of `J₀` itself, `0`, lies in the Cayley ball when `ω` tames `J₀`. -/
lemma Tames.zero_mem_cayleyBall (h₀ : ω.Tames J₀) : 0 ∈ ω.cayleyBall J₀ :=
  ⟨by simp, fun v hv => by simpa using h₀ v hv⟩

/-- The quadratic form `q(v) = ω(v, J₀ v)` satisfies the convexity identity
`q(a x + b y) = a q(x) + b q(y) - a b q(x - y)` when `a + b = 1`. -/
private lemma apply_add_apply_eq {a b : ℝ} (hab : a + b = 1) (x y : V) :
    ω (a • x + b • y) (J₀ (a • x + b • y)) =
      a * ω x (J₀ x) + b * ω y (J₀ y) - a * b * ω (x - y) (J₀ (x - y)) := by
  simp only [map_add, map_smul, map_sub, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, smul_eq_mul]
  obtain rfl : b = 1 - a := by linarith
  ring

/-- The Cayley ball of `J₀` is convex when `ω` tames `J₀`. -/
theorem Tames.convex_cayleyBall (h₀ : ω.Tames J₀) : Convex ℝ (ω.cayleyBall J₀) := by
  intro C hC D hD a b ha hb hab
  refine ⟨?_, fun v hv => ?_⟩
  · simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hC.1, hD.1, smul_neg, neg_add]
  · have hCv := hC.2 v hv
    have hDv := hD.2 v hv
    have hnonneg := h₀.symplecticForm_apply_apply_self_nonneg (C v - D v)
    have hab' := apply_add_apply_eq (ω := ω) (J₀ := J₀) hab (C v) (D v)
    simp only [LinearMap.add_apply, LinearMap.smul_apply]
    beta_reduce at hCv hDv hnonneg hab' ⊢
    set m := max (ω (C v) (J₀ (C v))) (ω (D v) (J₀ (D v)))
    have hm : m < ω v (J₀ v) := max_lt hCv hDv
    have hCm := mul_le_mul_of_nonneg_left (le_max_left _ _ : ω (C v) (J₀ (C v)) ≤ m) ha
    have hDm := mul_le_mul_of_nonneg_left (le_max_right _ _ : ω (D v) (J₀ (D v)) ≤ m) hb
    have habm : a * m + b * m = m := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_nonneg (mul_nonneg ha hb) hnonneg]

/-- For two structures tamed by `ω`, the endomorphism `1 - J₀ J` is invertible, since
`ω(v, J₀ (v - J₀ J v)) = ω(v, J₀ v) + ω(v, J v)` is positive for `v ≠ 0`. -/
lemma Tames.isUnit_one_sub_mul [FiniteDimensional ℝ V] (h₀ : ω.Tames J₀)
    (h : ω.Tames J) : IsUnit (1 - J₀.toLinearMap * J.toLinearMap) := by
  refine (LinearMap.isUnit_iff_ker_eq_bot _).mpr (LinearMap.ker_eq_bot'.mpr fun v hv => ?_)
  by_contra hne
  have hpos : 0 < ω v (J₀ (v - J₀ (J v))) := by
    simpa [map_sub] using add_pos (h₀ v hne) (h v hne)
  have hzero : v - J₀ (J v) = 0 := by simpa using hv
  simp [hzero] at hpos

/-- The defining relation of the Cayley transform without `Ring.inverse`: for two structures tamed
by `ω`, `C = J₀.cayley J` satisfies `C (1 - J₀ J) = -(1 + J₀ J)`. -/
lemma Tames.cayley_mul_one_sub_mul [FiniteDimensional ℝ V] (h₀ : ω.Tames J₀) (h : ω.Tames J) :
    J₀.cayley J * (1 - J₀.toLinearMap * J.toLinearMap) =
      -(1 + J₀.toLinearMap * J.toLinearMap) := by
  rw [AlmostComplexStructure.cayley_def, neg_mul,
    Ring.inverse_mul_cancel_right _ _ (h₀.isUnit_one_sub_mul h)]

/-- The endomorphisms `P = 1 - J₀ J` and `N = 1 + J₀ J` satisfy `P J₀ N = -(N J₀ P)`, a
consequence of `J₀² = J² = -1`. -/
private lemma one_sub_mul_mul_one_add_mul (J₀ J : AlmostComplexStructure V) :
    (1 - J₀.toLinearMap * J.toLinearMap) * J₀.toLinearMap *
        (1 + J₀.toLinearMap * J.toLinearMap) =
      -((1 + J₀.toLinearMap * J.toLinearMap) * J₀.toLinearMap *
        (1 - J₀.toLinearMap * J.toLinearMap)) := by
  ext v
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply,
    Module.End.one_apply, map_add, map_sub, AlmostComplexStructure.apply_apply, map_neg]
  abel

/-- The Cayley transform of a structure tamed by `ω` lies in the Cayley ball of an
`ω`-compatible `J₀`. -/
theorem Compatible.cayley_mem_cayleyBall [FiniteDimensional ℝ V] (h₀ : ω.Compatible J₀)
    (h : ω.Tames J) : J₀.cayley J ∈ ω.cayleyBall J₀ := by
  set j := J₀.toLinearMap
  set P := 1 - j * J.toLinearMap
  set N := 1 + j * J.toLinearMap
  have hP : IsUnit P := h₀.tames.isUnit_one_sub_mul h
  have hNP : N * P = P * N := by simp only [N, P]; noncomm_ring
  have hC : J₀.cayley J = -(N * Ring.inverse P) := J₀.cayley_def J
  refine ⟨?_, fun w hw => ?_⟩
  · -- Conjugating `P J₀ N = -(N J₀ P)` by `P⁻¹` shows that `N P⁻¹` anticommutes with `J₀`.
    have hPinvN : Ring.inverse P * N = N * Ring.inverse P := by
      rw [Ring.inverse_mul_eq_iff_eq_mul _ _ _ hP, ← mul_assoc, ← hNP, mul_assoc,
        Ring.mul_inverse_cancel _ hP, mul_one]
    have key : P * (N * Ring.inverse P * j + j * (N * Ring.inverse P)) * P = 0 := by
      have hrel := one_sub_mul_mul_one_add_mul J₀ J
      calc P * (N * Ring.inverse P * j + j * (N * Ring.inverse P)) * P
          = P * (Ring.inverse P * N) * j * P + P * j * N * (Ring.inverse P * P) := by
            rw [hPinvN]; noncomm_ring
        _ = N * j * P + P * j * N := by
            rw [Ring.mul_inverse_cancel_left _ _ hP, Ring.inverse_mul_cancel _ hP, mul_one]
        _ = 0 := by rw [hrel]; abel
    have hsum : N * Ring.inverse P * j + j * (N * Ring.inverse P) = 0 :=
      hP.mul_right_eq_zero.mp (hP.mul_left_eq_zero.mp key)
    rw [hC, neg_mul, mul_neg, neg_neg, neg_eq_iff_eq_neg]
    exact eq_neg_of_add_eq_zero_left hsum
  · -- With `u = P⁻¹ w`, the defect `q(w) - q(C w)` is `4 ω(u, J u)`.
    set u := Ring.inverse P w
    have hw' : P u = w := by
      simp only [u, ← Module.End.mul_apply, Ring.mul_inverse_cancel _ hP, Module.End.one_apply]
    have hu : u ≠ 0 := by
      rintro hu
      exact hw (by rw [← hw', hu, map_zero])
    have hCw : J₀.cayley J w = -(N u) := by
      rw [← hw', ← Module.End.mul_apply, h₀.tames.cayley_mul_one_sub_mul h, LinearMap.neg_apply]
    have hswap := h₀.associatedBilinForm_apply_swap u (J₀ (J u))
    have hpos := h u hu
    rw [hCw, ← hw']
    simp only [P, N, j, LinearMap.sub_apply, LinearMap.add_apply, Module.End.one_apply,
      Module.End.mul_apply, map_neg, map_sub, map_add, LinearMap.neg_apply,
      AlmostComplexStructure.apply_apply] at hswap ⊢
    beta_reduce at hpos
    linarith

/-- An element `C` of the Cayley ball has `1 - C` invertible: `C v = v` is impossible for a strict
contraction unless `v = 0`. -/
lemma isUnit_one_sub_of_mem_cayleyBall [FiniteDimensional ℝ V] {C : Module.End ℝ V}
    (hC : C ∈ ω.cayleyBall J₀) : IsUnit (1 - C) := by
  refine (LinearMap.isUnit_iff_ker_eq_bot _).mpr (LinearMap.ker_eq_bot'.mpr fun v hv => ?_)
  by_contra hne
  have hCv : C v = v := (sub_eq_zero.mp (by simpa using hv)).symm
  have := hC.2 v hne
  rw [hCv] at this
  exact this.false

/-- The inverse Cayley transform `J₀ (1 + C)(1 - C)⁻¹` of an element of the Cayley ball squares
to `-1`. -/
private lemma inverseCayley_mul_self [FiniteDimensional ℝ V] {C : Module.End ℝ V}
    (hC : C ∈ ω.cayleyBall J₀) :
    J₀.toLinearMap * (1 + C) * Ring.inverse (1 - C) *
        (J₀.toLinearMap * (1 + C) * Ring.inverse (1 - C)) = -1 := by
  set j := J₀.toLinearMap
  have hQ := isUnit_one_sub_of_mem_cayleyBall hC
  -- Anticommutation gives `(1 - C) J₀ = J₀ (1 + C)` and `(1 + C) J₀ = J₀ (1 - C)`.
  have hQj : (1 - C) * j = j * (1 + C) := by
    rw [sub_mul, mul_add, hC.1, one_mul, mul_one, sub_neg_eq_add]
  have hRj : (1 + C) * j = j * (1 - C) := by
    rw [add_mul, mul_sub, hC.1, one_mul, mul_one, sub_eq_add_neg]
  have h₁ : Ring.inverse (1 - C) * j * (1 + C) = j := by
    rw [mul_assoc, ← hQj, ← mul_assoc, Ring.inverse_mul_cancel _ hQ, one_mul]
  calc j * (1 + C) * Ring.inverse (1 - C) * (j * (1 + C) * Ring.inverse (1 - C))
      = j * (1 + C) * (Ring.inverse (1 - C) * j * (1 + C)) * Ring.inverse (1 - C) := by
        simp only [mul_assoc]
    _ = j * j * ((1 - C) * Ring.inverse (1 - C)) := by
        rw [h₁, mul_assoc j (1 + C) j, hRj]
        simp only [mul_assoc]
    _ = -1 := by rw [Ring.mul_inverse_cancel _ hQ]; simp [j]

/-- The inverse Cayley transform of an element `C` of the Cayley ball, the complex structure
`J₀ (1 + C)(1 - C)⁻¹`. -/
private def inverseCayley [FiniteDimensional ℝ V] {C : Module.End ℝ V}
    (hC : C ∈ ω.cayleyBall J₀) : AlmostComplexStructure V where
  toLinearMap := J₀.toLinearMap * (1 + C) * Ring.inverse (1 - C)
  square_neg := by
    rw [← Module.End.mul_eq_comp, inverseCayley_mul_self hC, Module.End.one_eq_id]

private lemma inverseCayley_toLinearMap [FiniteDimensional ℝ V] {C : Module.End ℝ V}
    (hC : C ∈ ω.cayleyBall J₀) :
    (inverseCayley hC).toLinearMap = J₀.toLinearMap * (1 + C) * Ring.inverse (1 - C) := rfl

/-- The inverse Cayley transform of an element of the Cayley ball of a compatible pair is tamed
by `ω`: with `w = (1 - C)⁻¹ v`, the value `ω(v, J v)` is `ω(w, J₀ w) - ω(C w, J₀ (C w))`. -/
private lemma Compatible.tames_inverseCayley [FiniteDimensional ℝ V] (h₀ : ω.Compatible J₀)
    {C : Module.End ℝ V} (hC : C ∈ ω.cayleyBall J₀) : ω.Tames (inverseCayley hC) := by
  intro v hv
  have hQ := isUnit_one_sub_of_mem_cayleyBall hC
  set w := Ring.inverse (1 - C) v
  have hv' : (1 - C) w = v := by
    simp only [w, ← Module.End.mul_apply, Ring.mul_inverse_cancel _ hQ, Module.End.one_apply]
  have hw : w ≠ 0 := by
    rintro hw
    exact hv (by rw [← hv', hw, map_zero])
  have hJv : inverseCayley hC v = J₀ ((1 + C) w) := by
    simp [w, inverseCayley_toLinearMap, Module.End.mul_apply]
  have hswap := h₀.associatedBilinForm_apply_swap w (C w)
  have hcontr := hC.2 w hw
  rw [hJv, ← hv']
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.one_apply, map_sub,
    map_add] at hswap ⊢
  beta_reduce at hswap hcontr ⊢
  linarith

/-- The Cayley transform of the inverse Cayley transform of `C` is `C`. -/
private lemma Compatible.cayley_inverseCayley [FiniteDimensional ℝ V] (h₀ : ω.Compatible J₀)
    {C : Module.End ℝ V} (hC : C ∈ ω.cayleyBall J₀) : J₀.cayley (inverseCayley hC) = C := by
  set j := J₀.toLinearMap
  set K := (inverseCayley hC).toLinearMap
  have hQ := isUnit_one_sub_of_mem_cayleyBall hC
  have hP : IsUnit (1 - j * K) := h₀.tames.isUnit_one_sub_mul (h₀.tames_inverseCayley hC)
  -- Since `J₀ K = -(1 + C)(1 - C)⁻¹`, right multiplication by `1 - C` clears the inverse.
  have hjKQ : j * K * (1 - C) = -(1 + C) := by
    have hK : K = j * (1 + C) * Ring.inverse (1 - C) := inverseCayley_toLinearMap hC
    calc j * K * (1 - C) = j * j * (1 + C) * (Ring.inverse (1 - C) * (1 - C)) := by
          rw [hK]; simp only [mul_assoc]
      _ = -(1 + C) := by rw [Ring.inverse_mul_cancel _ hQ]; simp [j]
  rw [AlmostComplexStructure.cayley_def, neg_eq_iff_eq_neg, eq_comm,
    Ring.eq_mul_inverse_iff_mul_eq _ _ _ hP]
  refine (hQ.mul_left_inj).mp ?_
  calc -C * (1 - j * K) * (1 - C) = -C * ((1 - C) - j * K * (1 - C)) := by noncomm_ring
    _ = (1 - C) + -(1 + C) := by rw [hjKQ]; noncomm_ring
    _ = (1 + j * K) * (1 - C) := by rw [add_mul, one_mul, hjKQ]

/-- The inverse Cayley transform of the Cayley transform of a tame structure `J` is `J`. -/
private lemma Compatible.inverseCayley_cayley [FiniteDimensional ℝ V] (h₀ : ω.Compatible J₀)
    (h : ω.Tames J) :
    (inverseCayley (h₀.cayley_mem_cayleyBall h)).toLinearMap = J.toLinearMap := by
  set j := J₀.toLinearMap
  set k := J.toLinearMap
  set P := 1 - j * k
  set N := 1 + j * k
  have hQ := isUnit_one_sub_of_mem_cayleyBall (h₀.cayley_mem_cayleyBall h)
  have hP : IsUnit P := h₀.tames.isUnit_one_sub_mul h
  have hCP : J₀.cayley J * P = -N := h₀.tames.cayley_mul_one_sub_mul h
  -- `P + N = 2` and `P - N = -2 J₀ J`, so `J (P + N) = J₀ (P - N)`.
  have hkj : k * (P + N) = j * (P - N) := by
    ext v
    simp only [P, N, j, k, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_add, map_sub, AlmostComplexStructure.apply_apply]
    abel
  rw [inverseCayley_toLinearMap, eq_comm, Ring.eq_mul_inverse_iff_mul_eq _ _ _ hQ]
  -- Right multiplication by `P = 1 - J₀ J` turns `C` into `C P = -N`.
  refine (hP.mul_left_inj).mp ?_
  calc k * (1 - J₀.cayley J) * P = k * (P - J₀.cayley J * P) := by noncomm_ring
    _ = j * (P + J₀.cayley J * P) := by rw [hCP, sub_neg_eq_add, hkj, sub_eq_add_neg]
    _ = j * (1 + J₀.cayley J) * P := by noncomm_ring

variable [FiniteDimensional ℝ V]

/-- For an `ω`-compatible `J₀`, the Cayley transform `J ↦ -(1 + J₀ J)(1 - J₀ J)⁻¹` is a bijection
from the `ω`-tame complex structures onto the Cayley ball of `J₀`. Its inverse is
`C ↦ J₀ (1 + C)(1 - C)⁻¹`. -/
def Compatible.cayleyEquiv (h₀ : ω.Compatible J₀) :
    {J : AlmostComplexStructure V // ω.Tames J} ≃ ω.cayleyBall J₀ where
  toFun J := ⟨J₀.cayley J, h₀.cayley_mem_cayleyBall J.2⟩
  invFun C := ⟨inverseCayley C.2, h₀.tames_inverseCayley C.2⟩
  left_inv J := Subtype.ext <| AlmostComplexStructure.toLinearMap_injective <|
    h₀.inverseCayley_cayley J.2
  right_inv C := Subtype.ext <| h₀.cayley_inverseCayley C.2

/-- The Cayley equivalence is the Cayley transform. -/
@[simp]
lemma Compatible.cayleyEquiv_apply_coe (h₀ : ω.Compatible J₀)
    (J : {J : AlmostComplexStructure V // ω.Tames J}) :
    (h₀.cayleyEquiv J : Module.End ℝ V) = J₀.cayley J := (rfl)

/-- The inverse Cayley transform is `C ↦ J₀ (1 + C)(1 - C)⁻¹`. -/
@[simp]
lemma Compatible.cayleyEquiv_symm_apply_toLinearMap (h₀ : ω.Compatible J₀)
    (C : ω.cayleyBall J₀) :
    (h₀.cayleyEquiv.symm C : AlmostComplexStructure V).toLinearMap =
      J₀.toLinearMap * (1 + (C : Module.End ℝ V)) * Ring.inverse (1 - (C : Module.End ℝ V)) :=
    (rfl)

/-- The Cayley equivalence sends `J₀` to `0`. -/
@[simp]
lemma Compatible.cayleyEquiv_self (h₀ : ω.Compatible J₀) :
    h₀.cayleyEquiv ⟨J₀, h₀.tames⟩ = ⟨0, h₀.tames.zero_mem_cayleyBall⟩ :=
  Subtype.ext (by simp)

end SymplecticForm

end TauCeti
