/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Normalized
public import Mathlib.Topology.Homotopy.Basic

/-!
# Cubical prisms

A homotopy sweeps an `n`-cube out into an `(n + 1)`-cube, with time as the first coordinate.
This construction preserves Massey's degeneracies, so it induces a degree-one operator on
normalized cubical chains. With the boundary convention `∑ i, (-1)^i (face i 0 - face i 1)`,
we take the negative of the swept cube. The resulting identity is
`∂ prism + prism ∂ = map g - map f` for a homotopy from `f` to `g`.

Sweeping with time as the **last** coordinate instead gives `prismLast`. With the sign
`(-1) ^ (n + 1)` on `n`-chains it satisfies the same identity. The two operators suit different
actions of a monoid on the space: placing time first keeps the coordinates of a chain acting on
the right after those of the swept cube, and placing time last keeps the coordinates of a chain
acting on the left before them; the module operators built from them are in
`TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Prism`.

In particular, a contraction supplies explicit fillings of cycles. These fillings give the
acyclicity of the standard cubes needed by the acyclic-models comparison of cubical and
simplicial chains.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II.
-/

public section

noncomputable section

open unitInterval Finsupp

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {f g : C(X, Y)}

namespace SingularCube

/-- The cube swept out by a homotopy, with time as the first coordinate. -/
def prism (H : ContinuousMap.Homotopy f g) {n : ℕ} (c : SingularCube X n) :
    SingularCube Y (n + 1) where
  toFun x := H (x 0, c (Fin.tail x))
  continuous_toFun := by fun_prop

@[simp]
theorem prism_apply (H : ContinuousMap.Homotopy f g) {n : ℕ} (c : SingularCube X n)
    (x : Fin (n + 1) → I) : prism H c x = H (x 0, c (Fin.tail x)) :=
  (rfl)

/-- The time faces of a prism are the two endpoint maps. -/
@[simp]
theorem face_zero_prism (H : ContinuousMap.Homotopy f g) {n : ℕ} (c : SingularCube X n) :
    face 0 0 (prism H c) = f.comp c := by
  ext x
  simp [Fin.insertNth_zero']

@[simp]
theorem face_one_prism (H : ContinuousMap.Homotopy f g) {n : ℕ} (c : SingularCube X n) :
    face 0 1 (prism H c) = g.comp c := by
  ext x
  simp [Fin.insertNth_zero']

/-- Taking a spatial face commutes with sweeping out the cube. -/
@[simp]
theorem face_succ_prism (H : ContinuousMap.Homotopy f g) {n : ℕ}
    (c : SingularCube X (n + 1)) (i : Fin (n + 1)) (t : I) :
    face i.succ t (prism H c) = prism H (face i t c) := by
  ext x
  rw [face_apply, prism_apply, prism_apply, face_apply]
  rw [← Fin.cons_self_tail x, Fin.insertNth_succ_cons]
  simp

/-- A prism is degenerate in the shifted coordinate whenever its input is degenerate. -/
theorem IsDegenerateAt.prism {n : ℕ} {c : SingularCube X n} {i : Fin n}
    (hc : IsDegenerateAt c i) (H : ContinuousMap.Homotopy f g) :
    IsDegenerateAt (prism H c) i.succ := by
  rw [isDegenerateAt_iff]
  intro x t
  simp [Fin.tail_update_succ, hc.apply_update, Function.update_of_ne (Fin.succ_ne_zero i).symm]

/-- Sweeping out a degenerate cube gives a degenerate cube. -/
theorem IsDegenerate.prism {n : ℕ} {c : SingularCube X n} (hc : IsDegenerate c)
    (H : ContinuousMap.Homotopy f g) : IsDegenerate (prism H c) := by
  obtain ⟨i, hi⟩ := isDegenerate_iff.1 hc
  exact isDegenerate_iff.2 ⟨i.succ, hi.prism H⟩

end SingularCube

namespace CubicalChain

variable (R : Type*) [Ring R]

/-- The negative swept-cube operator, extended linearly to unnormalized chains. -/
def prism (H : ContinuousMap.Homotopy f g) (n : ℕ) :
    CubicalChain X R n →ₗ[R] CubicalChain Y R (n + 1) :=
  -lmapDomain R R (SingularCube.prism H)

@[simp]
theorem prism_single (H : ContinuousMap.Homotopy f g) {n : ℕ}
    (c : SingularCube X n) (a : R) :
    prism R H n (single c a) = -single (SingularCube.prism H c) a := by
  simp [prism, lmapDomain_apply]

/-- The prism operator preserves the submodules of degenerate chains. -/
theorem prism_mem_degenerate (H : ContinuousMap.Homotopy f g) {n : ℕ}
    {c : CubicalChain X R n} (hc : c ∈ degenerate X R n) :
    prism R H n c ∈ degenerate Y R (n + 1) := by
  refine degenerate_induction (R := R)
    (P := fun c ↦ prism R H n c ∈ degenerate Y R (n + 1)) (by simp) (fun c hc ↦ ?_)
    (fun a b ha hb ↦ by simpa using Submodule.add_mem _ ha hb)
    (fun a c hc ↦ by simpa using Submodule.smul_mem _ a hc) hc
  rw [prism_single]
  exact Submodule.neg_mem _ (single_mem_degenerate R (hc.prism H) 1)

/-- The prism identity in positive degrees. -/
theorem boundary_prism_add_prism_boundary (H : ContinuousMap.Homotopy f g) (n : ℕ) :
    boundary Y R (n + 1) ∘ₗ prism R H (n + 1) +
        prism R H n ∘ₗ boundary X R n = map R g (n + 1) - map R f (n + 1) := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, lsingle_apply,
    prism_single, map_neg, boundary_single, map_sum, map_smul, map_sub, map_single]
  rw [Fin.sum_univ_succ]
  simp only [SingularCube.face_zero_prism, SingularCube.face_one_prism, Fin.val_zero,
    pow_zero, one_smul, SingularCube.face_succ_prism, Fin.val_succ, pow_succ,
    mul_neg_one, neg_smul, smul_neg, smul_sub]
  abel

/-- In degree zero the prism has just its two endpoint faces. -/
theorem boundary_prism_zero (H : ContinuousMap.Homotopy f g) :
    boundary Y R 0 ∘ₗ prism R H 0 = map R g 0 - map R f 0 := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp [boundary_single]

end CubicalChain

namespace NormalizedCubicalChain

variable (R : Type*) [Ring R]

/-- The prism operator on normalized cubical chains. -/
def prism (H : ContinuousMap.Homotopy f g) (n : ℕ) :
    NormalizedCubicalChain X R n →ₗ[R] NormalizedCubicalChain Y R (n + 1) :=
  Submodule.mapQ _ _ (CubicalChain.prism R H n)
    (fun _ hc ↦ CubicalChain.prism_mem_degenerate R H hc)

@[simp]
theorem prism_mk (H : ContinuousMap.Homotopy f g) {n : ℕ} (c : CubicalChain X R n) :
    prism R H n (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (CubicalChain.prism R H n c) :=
  Submodule.mapQ_apply _ _ _ c

@[simp]
theorem prism_ofCube (H : ContinuousMap.Homotopy f g) {n : ℕ} (c : SingularCube X n) :
    prism R H n (ofCube X R c) = -ofCube Y R (SingularCube.prism H c) := by
  rw [ofCube_def, prism_mk, CubicalChain.prism_single, ofCube_def]
  exact map_neg (Submodule.mkQ _) _

/-- The normalized prism identity in positive degrees. -/
theorem boundary_prism_add_prism_boundary (H : ContinuousMap.Homotopy f g) (n : ℕ)
    (c : NormalizedCubicalChain X R (n + 1)) :
    boundary Y R (n + 1) (prism R H (n + 1) c) +
        prism R H n (boundary X R n c) = map R g (n + 1) c - map R f (n + 1) c := by
  induction c using Submodule.Quotient.induction_on with
  | H c =>
    rw [prism_mk, boundary_mk, boundary_mk, prism_mk, map_mk, map_mk]
    have h := LinearMap.congr_fun (CubicalChain.boundary_prism_add_prism_boundary R H n) c
    simpa only [← Submodule.mkQ_apply, map_add, map_sub, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.sub_apply] using
      congrArg (Submodule.mkQ (CubicalChain.degenerate Y R (n + 1))) h

/-- The normalized prism identity in degree zero. -/
theorem boundary_prism_zero (H : ContinuousMap.Homotopy f g)
    (c : NormalizedCubicalChain X R 0) :
    boundary Y R 0 (prism R H 0 c) = map R g 0 c - map R f 0 c := by
  induction c using Submodule.Quotient.induction_on with
  | H c =>
    rw [prism_mk, boundary_mk, map_mk, map_mk]
    have h := LinearMap.congr_fun (CubicalChain.boundary_prism_zero R H) c
    simpa only [← Submodule.mkQ_apply, map_sub, LinearMap.comp_apply,
      LinearMap.sub_apply] using
      congrArg (Submodule.mkQ (CubicalChain.degenerate Y R 0)) h

end NormalizedCubicalChain

/-! ### Prisms with time last -/

namespace SingularCube

/-- The cube swept out by a homotopy, with time as the last coordinate. -/
def prismLast (H : ContinuousMap.Homotopy f g) {n : ℕ} (c : SingularCube X n) :
    SingularCube Y (n + 1) where
  toFun x := H (x (Fin.last n), c (Fin.init x))
  continuous_toFun := by unfold Fin.init; fun_prop

@[simp]
theorem prismLast_apply (H : ContinuousMap.Homotopy f g) {n : ℕ} (c : SingularCube X n)
    (x : Fin (n + 1) → I) : prismLast H c x = H (x (Fin.last n), c (Fin.init x)) :=
  (rfl)

/-- The time faces of a prism with time last are the two endpoint maps. -/
@[simp]
theorem face_last_zero_prismLast (H : ContinuousMap.Homotopy f g) {n : ℕ}
    (c : SingularCube X n) : face (Fin.last n) 0 (prismLast H c) = f.comp c := by
  ext x
  simp

@[simp]
theorem face_last_one_prismLast (H : ContinuousMap.Homotopy f g) {n : ℕ}
    (c : SingularCube X n) : face (Fin.last n) 1 (prismLast H c) = g.comp c := by
  ext x
  simp

/-- Taking a spatial face commutes with sweeping out the cube with time last. -/
@[simp]
theorem face_castSucc_prismLast (H : ContinuousMap.Homotopy f g) {n : ℕ}
    (c : SingularCube X (n + 1)) (i : Fin (n + 1)) (t : I) :
    face i.castSucc t (prismLast H c) = prismLast H (face i t c) := by
  ext x
  rw [face_apply, prismLast_apply, prismLast_apply, face_apply]
  -- The last coordinate is untouched, and the other ones form the face of the initial part.
  have hlast :
      (i.castSucc.insertNth (α := fun _ ↦ I) t x) (Fin.last (n + 1)) = x (Fin.last n) := by
    have : (Fin.last (n + 1) : Fin (n + 2)) = i.castSucc.succAbove (Fin.last n) :=
      (Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.2 (Fin.le_last i))).symm
    rw [this, Fin.insertNth_apply_succAbove]
  have hinit : Fin.init (i.castSucc.insertNth (α := fun _ ↦ I) t x) =
      i.insertNth (α := fun _ ↦ I) t (Fin.init x) := by
    funext j
    induction j using Fin.succAboveCases i with
    | x => simp [Fin.init]
    | p k => simp [Fin.init, ← Fin.castSucc_succAbove_castSucc]
  rw [hlast, hinit]

/-- A prism with time last is degenerate in the same coordinate as its input. -/
theorem IsDegenerateAt.prismLast {n : ℕ} {c : SingularCube X n} {i : Fin n}
    (hc : IsDegenerateAt c i) (H : ContinuousMap.Homotopy f g) :
    IsDegenerateAt (prismLast H c) i.castSucc := by
  rw [isDegenerateAt_iff]
  intro x t
  simp [Fin.init_update_castSucc, hc.apply_update,
    Function.update_of_ne (Fin.castSucc_lt_last i).ne']

/-- Sweeping out a degenerate cube with time last gives a degenerate cube. -/
theorem IsDegenerate.prismLast {n : ℕ} {c : SingularCube X n} (hc : IsDegenerate c)
    (H : ContinuousMap.Homotopy f g) : IsDegenerate (prismLast H c) := by
  obtain ⟨i, hi⟩ := isDegenerate_iff.1 hc
  exact isDegenerate_iff.2 ⟨i.castSucc, hi.prismLast H⟩

end SingularCube

namespace CubicalChain

variable (R : Type*) [Ring R]

/-- The swept-cube operator with time last, extended linearly to unnormalized chains, with the
sign `(-1) ^ (n + 1)` on `n`-chains. -/
def prismLast (H : ContinuousMap.Homotopy f g) (n : ℕ) :
    CubicalChain X R n →ₗ[R] CubicalChain Y R (n + 1) :=
  ((-1 : ℤ) ^ (n + 1)) • lmapDomain R R (SingularCube.prismLast H (n := n))

/-- The operator with time last on a single cube. -/
@[simp]
theorem prismLast_single (H : ContinuousMap.Homotopy f g) {n : ℕ}
    (c : SingularCube X n) (a : R) :
    prismLast R H n (single c a) =
      ((-1 : ℤ) ^ (n + 1)) • single (SingularCube.prismLast H c) a := by
  simp [prismLast]

/-- The operator with time last preserves the submodules of degenerate chains. -/
theorem prismLast_mem_degenerate (H : ContinuousMap.Homotopy f g) {n : ℕ}
    {c : CubicalChain X R n} (hc : c ∈ degenerate X R n) :
    prismLast R H n c ∈ degenerate Y R (n + 1) := by
  refine degenerate_induction (R := R)
    (P := fun c ↦ prismLast R H n c ∈ degenerate Y R (n + 1)) (by simp) (fun c hc ↦ ?_)
    (fun a b ha hb ↦ by simpa using Submodule.add_mem _ ha hb)
    (fun a c hc ↦ by simpa using Submodule.smul_mem _ a hc) hc
  rw [prismLast_single]
  exact Submodule.smul_of_tower_mem _ _ (single_mem_degenerate R (hc.prismLast H) 1)

/-- The prism identity with time last, in positive degrees. -/
theorem boundary_prismLast_add_prismLast_boundary (H : ContinuousMap.Homotopy f g) (n : ℕ) :
    boundary Y R (n + 1) ∘ₗ prismLast R H (n + 1) +
        prismLast R H n ∘ₗ boundary X R n = map R g (n + 1) - map R f (n + 1) := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, lsingle_apply,
    prismLast_single, map_zsmul, boundary_single, map_sum, map_sub, map_smul, map_single]
  rw [Fin.sum_univ_castSucc]
  simp only [SingularCube.face_last_zero_prismLast, SingularCube.face_last_one_prismLast,
    SingularCube.face_castSucc_prismLast, Fin.val_last, Fin.val_castSucc, smul_sub,
    Finset.smul_sum, smul_add]
  -- Convert the signs of the boundary into integer signs, which commute with everything.
  have hz : ∀ (k : ℕ) (z : CubicalChain Y R (n + 1)), (-1 : R) ^ k • z = ((-1 : ℤ) ^ k) • z :=
    fun k z ↦ by rw [← Int.cast_smul_eq_zsmul R]; simp
  simp only [hz, pow_succ (-1 : ℤ) (n + 1), mul_neg_one, smul_smul]
  -- The swept faces cancel in pairs, and the time faces carry the sign `-((-1) ^ (n + 1)) ^ 2`.
  have hs : ((-1 : ℤ) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  rw [add_right_comm, ← Finset.sum_add_distrib, Finset.sum_eq_zero fun x _ ↦ ?_, zero_add,
    neg_mul, hs]
  · rw [neg_smul, neg_smul, one_smul, one_smul]
    abel
  · rw [pow_add, mul_comm ((-1 : ℤ) ^ (x : ℕ)), neg_mul, neg_smul, neg_smul]
    abel

/-- In degree zero the prism with time last has just its two endpoint faces. -/
theorem boundary_prismLast_zero (H : ContinuousMap.Homotopy f g) :
    boundary Y R 0 ∘ₗ prismLast R H 0 = map R g 0 - map R f 0 := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  have h₀ := SingularCube.face_last_zero_prismLast H c
  have h₁ := SingularCube.face_last_one_prismLast H c
  simp only [Fin.last_zero] at h₀ h₁
  simp [boundary_single, h₀, h₁]

end CubicalChain

namespace NormalizedCubicalChain

variable (R : Type*) [Ring R]

/-- The prism operator with time last on normalized cubical chains. -/
def prismLast (H : ContinuousMap.Homotopy f g) (n : ℕ) :
    NormalizedCubicalChain X R n →ₗ[R] NormalizedCubicalChain Y R (n + 1) :=
  Submodule.mapQ _ _ (CubicalChain.prismLast R H n)
    (fun _ hc ↦ CubicalChain.prismLast_mem_degenerate R H hc)

@[simp]
theorem prismLast_mk (H : ContinuousMap.Homotopy f g) {n : ℕ} (c : CubicalChain X R n) :
    prismLast R H n (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (CubicalChain.prismLast R H n c) :=
  Submodule.mapQ_apply _ _ _ c

@[simp]
theorem prismLast_ofCube (H : ContinuousMap.Homotopy f g) {n : ℕ} (c : SingularCube X n) :
    prismLast R H n (ofCube X R c) =
      ((-1 : ℤ) ^ (n + 1)) • ofCube Y R (SingularCube.prismLast H c) := by
  rw [ofCube_def, prismLast_mk, CubicalChain.prismLast_single, ofCube_def]
  exact map_zsmul (Submodule.mkQ _) _ _

/-- The normalized prism identity with time last, in positive degrees. -/
theorem boundary_prismLast_add_prismLast_boundary (H : ContinuousMap.Homotopy f g) (n : ℕ)
    (c : NormalizedCubicalChain X R (n + 1)) :
    boundary Y R (n + 1) (prismLast R H (n + 1) c) +
        prismLast R H n (boundary X R n c) = map R g (n + 1) c - map R f (n + 1) c := by
  induction c using Submodule.Quotient.induction_on with
  | H c =>
    rw [prismLast_mk, boundary_mk, boundary_mk, prismLast_mk, map_mk, map_mk]
    have h := LinearMap.congr_fun (CubicalChain.boundary_prismLast_add_prismLast_boundary R H n) c
    simpa only [← Submodule.mkQ_apply, map_add, map_sub, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.sub_apply] using
      congrArg (Submodule.mkQ (CubicalChain.degenerate Y R (n + 1))) h

/-- The normalized prism identity with time last, in degree zero. -/
theorem boundary_prismLast_zero (H : ContinuousMap.Homotopy f g)
    (c : NormalizedCubicalChain X R 0) :
    boundary Y R 0 (prismLast R H 0 c) = map R g 0 c - map R f 0 c := by
  induction c using Submodule.Quotient.induction_on with
  | H c =>
    rw [prismLast_mk, boundary_mk, map_mk, map_mk]
    have h := LinearMap.congr_fun (CubicalChain.boundary_prismLast_zero R H) c
    simpa only [← Submodule.mkQ_apply, map_sub, LinearMap.comp_apply,
      LinearMap.sub_apply] using
      congrArg (Submodule.mkQ (CubicalChain.degenerate Y R 0)) h

end NormalizedCubicalChain

end TauCeti
