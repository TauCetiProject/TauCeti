/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Coadjoint.RootPlane.Decomposition
public import TauCeti.Algebra.Lie.Orthogonal.CrossProduct

/-!
# The root plane of `so(3)`

The Lie algebra `so(3) ≅ (R³, ⨯₃)` with the dot product (`TauCeti.soThreeForm`) has the root
plane `E = ẑ^⊥` of `t = R ẑ` (`TauCeti.IsRootPlane`), where `ẑ` is the hat matrix of the third
standard basis vector, with rotation `J = ad ẑ` and root `α(c ẑ) = c`
(`TauCeti.isRootPlane_soThree`). For `p = r ẑ` and `X = a ẑ` the root-plane formulas of
`TauCeti.Algebra.Lie.Coadjoint.RootPlane` give the Hessian `-a B / r` of the height on the tangent
plane of the coadjoint sphere of radius `r` (`TauCeti.soThreeForm_lie_lie_smul_soThreeZ`); here
`t` is a line, hence abelian, and the dot product is symmetric and invariant.

The line `t` and the plane `ẑ^⊥` form a root-plane decomposition of `so(3)`
(`TauCeti.isRootPlaneDecomposition_soThree`), so the index count of
`TauCeti.Algebra.Lie.Coadjoint.RootPlane.Decomposition` applies: over an ordered field the height
Hessian `A ↦ -B(⁅A, r ẑ⁆, ⁅A, a ẑ⁆)` has negative index `2` when `r a > 0` and `0` otherwise
(`TauCeti.sigNeg_heightHessian_soThree`), the indices `2` and `0` of the maximum and the minimum of
the height on the coadjoint sphere.

## Main definitions

* `TauCeti.soThreeZ`: the generator `ẑ` of the rotations about the third axis.
* `TauCeti.soThreeRotation`: the rotation `ad ẑ` of the plane `ẑ^⊥`.

## Main results

* `TauCeti.isRootPlane_soThree`: the root plane of `so(3)`.
* `TauCeti.soThreeForm_lie_lie_smul_soThreeZ`: its height Hessian.
* `TauCeti.isRootPlaneDecomposition_soThree`: the root-plane decomposition of `so(3)`.
* `TauCeti.sigNeg_heightHessian_soThree`: the Morse index of the height Hessian.

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

/-- The generator `ẑ` has unit length for the dot product. -/
private theorem soThreeForm_soThreeZ_soThreeZ : soThreeForm R (soThreeZ R) (soThreeZ R) = 1 := by
  simp [dotProduct, Fin.sum_univ_three]

/-- **The root-plane decomposition of `so(3)`.** For the dot product, `so(3)` is the direct sum of
the line `t = R ẑ` and its root plane `ẑ^⊥` (`TauCeti.isRootPlane_soThree`), indexed by `Unit`. -/
theorem isRootPlaneDecomposition_soThree :
    IsRootPlaneDecomposition (soThreeForm R) (R ∙ soThreeZ R)
      (fun _ : Unit ↦ (soThreeForm R (soThreeZ R)).domRestrict _)
      (fun _ ↦ LinearMap.ker (soThreeForm R (soThreeZ R))) (fun _ ↦ soThreeRotation R) where
  isRootPlane _ := isRootPlane_soThree
  lie_eq_zero hH hH' := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hH
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hH'
    rw [smul_lie, lie_smul, lie_self, smul_zero, smul_zero]
  le_orthogonal i j hij := absurd (Subsingleton.elim i j) hij
  iSupIndep := iSupIndep_subsingleton _
  disjoint := by
    rw [iSup_const, Submodule.disjoint_def]
    intro v hv hker
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [LinearMap.mem_ker, map_smul, soThreeForm_soThreeZ_soThreeZ, smul_eq_mul, mul_one] at hker
    rw [hker, zero_smul]
  sup_eq_top := by
    refine eq_top_iff.mpr fun v _ ↦ ?_
    rw [iSup_const, ← add_sub_cancel (soThreeForm R (soThreeZ R) v • soThreeZ R) v]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) ?_
    simp

section LinearOrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **The Morse index of a height on the coadjoint sphere of `so(3)`.** For `p = r ẑ` and
`X = a ẑ`, the height Hessian `A ↦ -B(⁅A, p⁆, ⁅A, X⁆)` has negative index `2` when `r a > 0`, at
the maximum of the height on the orbit sphere, and `0` otherwise. -/
theorem sigNeg_heightHessian_soThree (r a : K) :
    sigNeg ((soThreeForm K).heightHessian (r • soThreeZ K) (a • soThreeZ K)) =
      if 0 < r * a then 2 else 0 := by
  have : FiniteDimensional K (so (Fin 3) K) := Module.Finite.equiv (soThreeEquiv K)
  have hmem (c : K) : c • soThreeZ K ∈ K ∙ soThreeZ K :=
    Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  have hpos : ∀ _ : Unit, ∀ v ∈ LinearMap.ker (soThreeForm K (soThreeZ K)), v ≠ 0 →
      0 < soThreeForm K v v := fun _ v _ hv ↦ by
    obtain ⟨u, rfl⟩ := (soThreeEquiv K).surjective v
    rw [soThreeForm_apply_soThreeEquiv]
    exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (u i))
      (Ne.symm (dotProduct_self_eq_zero.not.mpr (by simpa using hv)))
  -- The functional `B ẑ` is onto, so its kernel `ẑ^⊥` is a plane.
  have hrange : LinearMap.range (soThreeForm K (soThreeZ K)) = ⊤ :=
    LinearMap.range_eq_top.mpr fun c ↦
      ⟨c • soThreeZ K, by rw [map_smul, soThreeForm_soThreeZ_soThreeZ, smul_eq_mul, mul_one]⟩
  have hker := LinearMap.finrank_range_add_finrank_ker (soThreeForm K (soThreeZ K))
  rw [hrange, finrank_top, Module.finrank_self, finrank_so_three] at hker
  rw [isRootPlaneDecomposition_soThree.sigNeg_heightHessian hpos ⟨r • soThreeZ K, hmem r⟩
    ⟨a • soThreeZ K, hmem a⟩, Finset.sum_filter, Fintype.sum_unique]
  simp only [LinearMap.domRestrict_apply, map_smul, soThreeForm_soThreeZ_soThreeZ, smul_eq_mul,
    mul_one]
  split_ifs <;> omega

end LinearOrderedField

end TauCeti
