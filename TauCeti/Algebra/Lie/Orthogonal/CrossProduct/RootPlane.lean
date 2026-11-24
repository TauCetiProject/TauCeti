/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Coadjoint.Height
public import TauCeti.Algebra.Lie.Orthogonal.CrossProduct
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# The root plane of `so(3)`

The Lie algebra `so(3) ≅ (R³, ⨯₃)` with the dot product (`TauCeti.soThreeForm`) has the root
plane `E = ẑ^⊥` of `t = R ẑ` (`TauCeti.IsRootPlane`), where `ẑ` is the hat matrix of the third
standard basis vector, with rotation `J = ad ẑ` and root `α(c ẑ) = c`
(`TauCeti.isRootPlane_soThree`). For `p = r ẑ` and `X = a ẑ` the root-plane formulas of
`TauCeti.Algebra.Lie.Coadjoint.RootPlane` give the Hessian `-a B / r` of the height on the tangent
plane of the coadjoint sphere of radius `r` (`TauCeti.soThreeForm_lie_lie_smul_soThreeZ`); here
`t` is a line, hence abelian, and the dot product is symmetric and invariant.

The line and its orthogonal plane form a root-plane decomposition of `so(3)`
(`TauCeti.isRootPlaneDecomposition_soThree`), so the index formulas of
`TauCeti.Algebra.Lie.Coadjoint.Height` apply: writing `Z = soThreeZ` for the generator, the Morse
index of the height `B(·, a Z)` at `r Z` is two when `r a > 0` and zero otherwise
(`TauCeti.sigNeg_toQuadraticMap_heightHessian_soThree`).

## Main definitions

* `TauCeti.soThreeZ`: the generator `ẑ` of the rotations about the third axis.
* `TauCeti.soThreeRotation`: the rotation `ad ẑ` of the plane `ẑ^⊥`.

## Main results

* `TauCeti.isRootPlane_soThree`: the root plane of `so(3)`.
* `TauCeti.soThreeForm_lie_lie_smul_soThreeZ`: its height Hessian.
* `TauCeti.isRootPlaneDecomposition_soThree`: the root-plane decomposition of `so(3)`.
* `TauCeti.sigNeg_toQuadraticMap_heightHessian_soThree`: the Morse index of the height.

## References

* M. Audin, *Torus Actions on Symplectic Manifolds*, 2nd ed., Progress in Mathematics 93,
  Birkhäuser, 2004, Chapter II (coadjoint orbits and their height functions).
-/

public section

namespace TauCeti

open Matrix LieAlgebra.Orthogonal

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type*} [CommRing R] [NoZeroDivisors R] [NeZero (2 : R)]

variable (R) in
/-- The generator `ẑ ∈ so(3)` of the rotations about the third axis. -/
abbrev soThreeZ : so (Fin 3) R := soThreeEquiv R ![0, 0, 1]

/-- The rotation `ad ẑ` preserves the plane `ẑ^⊥`. -/
private theorem lie_soThreeZ_mem_ker {x : so (Fin 3) R}
    (hx : x ∈ LinearMap.ker (soThreeForm R (soThreeZ R))) :
    ⁅soThreeZ R, x⁆ ∈ LinearMap.ker (soThreeForm R (soThreeZ R)) := by
  obtain ⟨u, rfl⟩ := (soThreeEquiv R).surjective x
  simp only [LinearMap.mem_ker, lie_soThreeEquiv, soThreeForm_apply_soThreeEquiv] at hx ⊢
  exact dot_self_cross _ _

variable (R) in
/-- The rotation `J = ad ẑ` of the plane `ẑ^⊥` of `so(3)`. -/
def soThreeRotation : Module.End R (LinearMap.ker (soThreeForm R (soThreeZ R))) :=
  (LieAlgebra.ad R (so (Fin 3) R) (soThreeZ R)).restrict fun _ ↦ lie_soThreeZ_mem_ker

@[simp]
theorem coe_soThreeRotation_apply (v : LinearMap.ker (soThreeForm R (soThreeZ R))) :
    (soThreeRotation R v : so (Fin 3) R) = ⁅soThreeZ R, (v : so (Fin 3) R)⁆ :=
  (rfl)

/-- **The root plane of `so(3)`.** For the dot product, the plane `ẑ^⊥` is a root plane of the
line `t = R ẑ`, with rotation `ad ẑ` and root `α(c ẑ) = c`, the restriction of `B ẑ` to `t`. -/
theorem isRootPlane_soThree :
    IsRootPlane (soThreeForm R) (R ∙ soThreeZ R) ((soThreeForm R (soThreeZ R)).domRestrict _)
      (LinearMap.ker (soThreeForm R (soThreeZ R))) (soThreeRotation R) where
  apply_apply v := by
    obtain ⟨x, hx⟩ := v
    obtain ⟨u, rfl⟩ := (soThreeEquiv R).surjective x
    have hu : u 2 = 0 := by simpa [dotProduct, Fin.sum_univ_three] using hx
    refine Subtype.ext ?_
    simp only [coe_soThreeRotation_apply, lie_soThreeEquiv, Submodule.coe_neg, ← map_neg]
    congr 1
    ext i
    fin_cases i <;> simp [cross_apply, hu]
  apply_left v w := by
    obtain ⟨x, -⟩ := v
    obtain ⟨y, -⟩ := w
    obtain ⟨u, rfl⟩ := (soThreeEquiv R).surjective x
    obtain ⟨w, rfl⟩ := (soThreeEquiv R).surjective y
    simp only [coe_soThreeRotation_apply, lie_soThreeEquiv, soThreeForm_apply_soThreeEquiv,
      cross_apply, dotProduct, Fin.sum_univ_three]
    simp
  lie_apply H v := by
    obtain ⟨H, hH⟩ := H
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hH
    simp [dotProduct, Fin.sum_univ_three]

/-- **The height Hessian of the coadjoint sphere of `so(3)`.** For `p = r ẑ`, `X = a ẑ` and
`u, w ⊥ e₃`, `B(q_p û, q_X ŵ) = r a (u ⬝ᵥ w)`. Since `p` and `X` commute and the dot product is
symmetric and invariant (`TauCeti.isSymm_soThreeForm`, `TauCeti.lieInvariant_soThreeForm`), the
Hessian at `p` of the height `B(·, X)` on the orbit of `p` is `-r a B` in the coordinates `û, ŵ`
of `ẑ^⊥`, and `-a B / r` in the tangent vectors `q_p û, q_p ŵ`
(`TauCeti.IsRootPlane.mul_apply_lie_lie`). -/
theorem soThreeForm_lie_lie_smul_soThreeZ (r a : R) {u w : Fin 3 → R} (hu : u 2 = 0)
    (hw : w 2 = 0) :
    soThreeForm R ⁅soThreeEquiv R u, r • soThreeZ R⁆ ⁅soThreeEquiv R w, a • soThreeZ R⁆ =
      r * a * (u ⬝ᵥ w) := by
  have hmem (c : R) : c • soThreeZ R ∈ R ∙ soThreeZ R := Submodule.smul_mem _ c
    (Submodule.mem_span_singleton_self _)
  have hker {v : Fin 3 → R} (hv : v 2 = 0) :
      soThreeEquiv R v ∈ LinearMap.ker (soThreeForm R (soThreeZ R)) := by
    simp [dotProduct, Fin.sum_univ_three, hv]
  have h := isRootPlane_soThree.apply_lie_lie ⟨r • soThreeZ R, hmem r⟩ ⟨a • soThreeZ R, hmem a⟩
    ⟨soThreeEquiv R u, hker hu⟩ ⟨soThreeEquiv R w, hker hw⟩
  simpa [dotProduct, Fin.sum_univ_three] using h

/-! ### The root-plane decomposition and the Morse index of the height -/

/-- `B(Z, Z) = 1` for the generator `Z = soThreeZ`. -/
theorem soThreeForm_soThreeZ_soThreeZ : soThreeForm R (soThreeZ R) (soThreeZ R) = 1 := by
  simp [dotProduct, Fin.sum_univ_three]

/-- The plane `Z^⊥` of `so(3)` has dimension two. -/
theorem finrank_ker_soThreeForm_soThreeZ {K : Type*} [Field K] [NeZero (2 : K)] :
    Module.finrank K (LinearMap.ker (soThreeForm K (soThreeZ K))) = 2 := by
  have hne : soThreeForm K (soThreeZ K) ≠ 0 := fun h ↦ by
    simpa [h] using (soThreeForm_soThreeZ_soThreeZ (R := K))
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hne
  rw [finrank_so_three] at h
  omega

section Ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **The root-plane decomposition of `so(3)`.** For the dot product, the line `t = K Z` and its
orthogonal plane `Z^⊥`, with rotation `ad Z` and root `α(c Z) = c`, form a root-plane
decomposition of `so(3)`. -/
theorem isRootPlaneDecomposition_soThree :
    IsRootPlaneDecomposition (soThreeForm K) (K ∙ soThreeZ K)
      (fun _ : Unit ↦ (soThreeForm K (soThreeZ K)).domRestrict _)
      (fun _ ↦ LinearMap.ker (soThreeForm K (soThreeZ K))) (fun _ ↦ soThreeRotation K) where
  isRootPlane _ := isRootPlane_soThree
  le_orthogonal hij := (hij (Subsingleton.elim _ _)).elim
  pos _ v _ hv0 := by
    obtain ⟨u, rfl⟩ := (soThreeEquiv K).surjective v
    have hu : u ≠ 0 := fun h ↦ hv0 (by rw [h, map_zero])
    rw [soThreeForm_apply_soThreeEquiv]
    exact (Matrix.dotProduct_self_nonneg u).lt_of_ne' (dotProduct_self_eq_zero.not.mpr hu)
  lie_eq_zero hH hH' := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hH
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hH'
    rw [smul_lie, lie_smul, lie_self, smul_zero, smul_zero]
  sup_eq_top := by
    -- `x = B(Z, x) Z + (x - B(Z, x) Z)`, and the second summand is orthogonal to `Z`.
    refine eq_top_iff.mpr fun x _ ↦ Submodule.mem_sup.mpr
      ⟨soThreeForm K (soThreeZ K) x • soThreeZ K,
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
        x - soThreeForm K (soThreeZ K) x • soThreeZ K, ?_, add_sub_cancel _ _⟩
    rw [iSup_const, LinearMap.mem_ker, map_sub, map_smul, soThreeForm_soThreeZ_soThreeZ,
      smul_eq_mul, mul_one, sub_self]

/-- **The Morse index of the height on a coadjoint sphere of `so(3)`.** For `p = r Z` and
`X = a Z`, the Hessian at `p` of the height `B(·, X)` on the orbit of `p` has negative index two
when `r a > 0`, where `p` is the maximum of the height on its sphere, and zero otherwise. -/
theorem sigNeg_toQuadraticMap_heightHessian_soThree (r a : K) :
    sigNeg ((soThreeForm K).heightHessian (r • soThreeZ K) (a • soThreeZ K)).toQuadraticMap =
      if 0 < r * a then 2 else 0 := by
  have hmem (c : K) : c • soThreeZ K ∈ K ∙ soThreeZ K :=
    Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  have h := isRootPlaneDecomposition_soThree.sigNeg_toQuadraticMap_heightHessian_eq_two_mul_card
    (fun _ ↦ finrank_ker_soThreeForm_soThreeZ) ⟨r • soThreeZ K, hmem r⟩ ⟨a • soThreeZ K, hmem a⟩
  simp only [LinearMap.domRestrict_apply, map_smul, soThreeForm_soThreeZ_soThreeZ, smul_eq_mul,
    mul_one] at h
  rw [h]
  split_ifs with hra <;> simp [hra]

end Ordered

end TauCeti
