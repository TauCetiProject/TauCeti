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

end TauCeti
