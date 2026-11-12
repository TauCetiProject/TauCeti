/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Rational.Basic
public import TauCeti.Analysis.Convex.Sweep.Basic
public import TauCeti.Analysis.Convex.Polyhedron.Projection

/-!
# Rational-normal polyhedral sweeps

Fourier–Motzkin elimination gives an actual rational-normal presentation of the
negative-ray sweep. The parameter coefficient of each inequality is its normal
evaluated at the lattice sweeping vector, hence is rational. Every resultant
normal is therefore a rational combination of the original normals.

No transversality assumption is needed. Arbitrary real offsets remain allowed;
when the original offsets are rational, the resulting offsets are rational too.

Adapted from `Mei/Geometry/Convex/Polyhedron/Rational/Sweep.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7`, released under Apache 2.0.
Original copyright (c) 2026 Mei contributors; original author: Codex.
-/

public section

namespace TauCeti

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Rational parameter coefficients preserve rational normals in every
Fourier–Motzkin resultant row. -/
theorem rational_linear_nonnegElimFamily (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, TauCeti.Toric.IsRationalFunctional h (g j).toAffineMap.linear)
    (a : ι → ℝ) (ha : ∀ j, ∃ q : ℚ, a j = (q : ℝ)) (k : NonnegElimIndex a) :
    TauCeti.Toric.IsRationalFunctional h (nonnegElimFamily g a k).toAffineMap.linear := by
  rcases k with j | ⟨j, k⟩
  · rw [nonnegElimFamily_single_linear]
    exact hg j.val
  · rw [nonnegElimFamily_pair_linear]
    obtain ⟨qj, hqj⟩ := ha j.val
    obtain ⟨qk, hqk⟩ := ha k.val
    rw [hqj, hqk]
    exact ((hg j.val).rat_smul qk).sub ((hg k.val).rat_smul qj)

/-- Rational coefficients and rational offsets give rational offsets for each
resultant row. -/
theorem rational_offset_nonnegElimFamily (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, ∃ q : ℚ, g j 0 = (q : ℝ)) (a : ι → ℝ)
    (ha : ∀ j, ∃ q : ℚ, a j = (q : ℝ)) (k : NonnegElimIndex a) :
    ∃ q : ℚ, nonnegElimFamily g a k 0 = (q : ℝ) := by
  rcases k with j | ⟨j, k⟩
  · rw [nonnegElimFamily_single_apply]
    exact hg j.val
  · obtain ⟨aj, haj⟩ := ha j.val
    obtain ⟨ak, hak⟩ := ha k.val
    obtain ⟨bj, hbj⟩ := hg j.val
    obtain ⟨bk, hbk⟩ := hg k.val
    refine ⟨ak * bj - aj * bk, ?_⟩
    rw [nonnegElimFamily_pair_apply, haj, hak, hbj, hbk]
    simp only [Rat.cast_sub, Rat.cast_mul]

end TauCeti

namespace TauCeti.RationalAffinePolyhedron

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- The negative-ray sweep of a rational-normal affine presentation along a
lattice vector, with the explicit finite Fourier–Motzkin resultant inequalities. -/
noncomputable def sweep (P : RationalAffinePolyhedron h) (n : N) :
    RationalAffinePolyhedron h :=
  ofFinite
    (TauCeti.nonnegElimFamily P.inequality (fun j => (P.inequality j).linear (i n)))
    (TauCeti.rational_linear_nonnegElimFamily P.inequality P.rational_linear
      (fun j => (P.inequality j).linear (i n))
      (fun j => (P.rational_linear j).exists_rat_apply n))

/-- The resultant presentation has exactly the original negative-ray sweep as
its carrier, including for tangent sweeping vectors. -/
@[simp]
theorem carrier_sweep (P : RationalAffinePolyhedron h) (n : N) :
    (P.sweep n).carrier = Set.sweep ℝ P.carrier (i n) := by
  ext y
  unfold sweep
  rw [mem_carrier_ofFinite, Set.mem_sweep_iff]
  symm
  simp only [mem_carrier]
  have he := TauCeti.setOf_exists_nonneg_add_smul_forall_le_eq P.inequality (i n)
  exact Set.ext_iff.mp he y

/-- Sweeping preserves rational offsets because its resultant coefficients are
rational evaluations of the original normals on a lattice vector. -/
theorem HasRationalOffsets.sweep {P : RationalAffinePolyhedron h}
    (hP : P.HasRationalOffsets) (n : N) : (P.sweep n).HasRationalOffsets := by
  rw [TauCeti.RationalAffinePolyhedron.sweep]
  rw [hasRationalOffsets_iff] at hP
  apply (hasRationalOffsets_ofFinite_iff _).mpr
  exact TauCeti.rational_offset_nonnegElimFamily P.inequality hP
    (fun j => (P.inequality j).linear (i n))
    (fun j => (P.rational_linear j).exists_rat_apply n)

end TauCeti.RationalAffinePolyhedron

namespace TauCeti

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {P : Set V}

/-- The negative-ray sweep along a lattice vector has rational normals. -/
theorem IsRationalNormalPolyhedron.sweep (hP : IsRationalNormalPolyhedron h P) (n : N) :
    IsRationalNormalPolyhedron h (Set.sweep ℝ P (i n)) := by
  obtain ⟨Q, rfl⟩ := isRationalNormalPolyhedron_iff.mp hP
  exact isRationalNormalPolyhedron_iff.mpr ⟨Q.sweep n, Q.carrier_sweep n⟩

/-- Negative-ray sweeping preserves rational normals and rational offsets. -/
theorem IsRationalPolyhedron.sweep (hP : IsRationalPolyhedron h P) (n : N) :
    IsRationalPolyhedron h (Set.sweep ℝ P (i n)) := by
  obtain ⟨Q, rfl, hQ⟩ := isRationalPolyhedron_iff.mp hP
  exact isRationalPolyhedron_iff.mpr ⟨Q.sweep n, Q.carrier_sweep n, hQ.sweep n⟩

end TauCeti
