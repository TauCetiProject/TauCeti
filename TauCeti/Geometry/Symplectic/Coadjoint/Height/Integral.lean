/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Geometry.Symplectic.Coadjoint.Height.Perfect
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod
import TauCeti.Geometry.Manifold.Morse.EulerCharacteristic
import TauCeti.AlgebraicTopology.Singular.Coefficients.PrimeField
import TauCeti.Geometry.Manifold.Morse.CWModel

/-!
# Integral homology of coadjoint orbits of compact Lie groups

Let `G` be a compact Lie group, `ν ∈ 𝔤*` and `O = G ⧸ G_ν` its coadjoint orbit. Every Morse height
`f_X = ⟨μ, X⟩` on `O` has even Morse indices and is a perfect Morse function over every division
ring (`Module.Dual.isPerfectMorse_orbitMap_coadjointRepresentation_apply`), so the odd Betti numbers
of `O` vanish over every field, in particular over every prime field `𝔽_p`. This file deduces the
integral statement:

* the integral homology `Hⱼ(O; ℤ)` vanishes in odd degrees
  (`Module.Dual.isZero_singularHomology_int_quotient_stabilizer_coadjointRepresentation_of_odd`);
* it is a free abelian group of finite rank in every degree
  (`Module.Dual.free_singularHomology_int_quotient_stabilizer_coadjointRepresentation`,
  `Module.Dual.finite_singularHomology_int_quotient_stabilizer_coadjointRepresentation`).

So coadjoint orbits of compact Lie groups have no torsion in their integral homology, and their
integral homology is concentrated in even degrees. For instance this holds for the complex
projective spaces, the Grassmannians and the flag manifolds `G ⧸ T`. Since no Morse index is odd,
the Euler characteristic `χ(O)` is the number of critical points of any Morse height
(`Module.Dual.eulerChar_quotient_stabilizer_coadjointRepresentation_eq_ncard`); for the height of a
regular element of a maximal torus, these are counted by the Weyl group in
`TauCeti.Geometry.Symplectic.Coadjoint.Height.Weyl`.

The argument uses no cell structure. The coadjoint orbit is a compact manifold carrying a Morse
height, hence of finite CW type (`TauCeti.IsMorse.finiteCWType`), so its integral homology is
finitely generated (`TauCeti.finite_singularHomology_int_of_finiteCWType`). In the coefficient
long exact sequence of `0 ⟶ ℤ ⟶ ℤ ⟶ ℤ/p ⟶ 0`, vanishing of `Hⱼ₊₁(O; 𝔽_p)` for odd `j + 1` makes
multiplication by `p` injective on `Hⱼ(O; ℤ)`, and vanishing of `Hⱼ(O; 𝔽_p)` for odd `j` makes it
onto. A finitely generated abelian group on which every prime acts injectively is free, and one on
which every prime acts surjectively is zero
(`TopCat.isTorsionFree_singularHomology_of_forall_isZero_zmod`,
`TopCat.isZero_singularHomology_of_forall_isZero_zmod`).

## Main results

* `Module.Dual.isZero_singularHomology_int_quotient_stabilizer_coadjointRepresentation_of_odd`:
  the odd-degree integral homology of a coadjoint orbit of a compact Lie group vanishes.
* `Module.Dual.free_singularHomology_int_quotient_stabilizer_coadjointRepresentation`: its integral
  homology is free in every degree.
* `Module.Dual.finite_singularHomology_int_quotient_stabilizer_coadjointRepresentation`: and
  finitely generated.
* `Module.Dual.eulerChar_quotient_stabilizer_coadjointRepresentation_eq_ncard`: the Euler
  characteristic of a coadjoint orbit is the number of critical points of any Morse height.

## References

* R. Bott, *An application of the Morse theory to the topology of Lie-groups*, Bull. Soc. Math.
  France 84 (1956), 251–281, Theorem III (coadjoint orbits have no torsion and no odd-dimensional
  homology).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.A (the universal coefficient theorem and change of coefficients).
-/

public section

open CategoryTheory Limits AlgebraicTopology Module Manifold TauCeti TauCeti.Lie
open scoped Manifold ContDiff

universe u

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
  isClosed_stabilizer_coadjointRepresentation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type u} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [CompactSpace G]

namespace Module.Dual

variable (ν : Module.Dual ℝ (GroupLieAlgebra I G))

/-- The homology of a coadjoint orbit of a compact Lie group with coefficients in the integer module
`ℤ/p`, for a prime `p`, vanishes in odd degrees. -/
private theorem isZero_singularHomology_zmod_quotient_stabilizer_of_odd {p : ℕ} (hp : p.Prime)
    {j : ℕ} (hj : Odd j) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) j).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod p)))).obj
        (TopCat.of (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν))) := by
  have : Fact p.Prime := ⟨hp⟩
  -- the homology over the field `𝔽_p` is finite-dimensional of dimension the odd Betti number `0`
  obtain ⟨X, hX⟩ := ν.exists_isMorse_orbitMap_coadjointRepresentation_apply
  have := (ν.isPerfectMorse_orbitMap_coadjointRepresentation_apply (ULift.{u} (ZMod p)) hX
    (X := X)).finite_singularHomology j
  have h := ν.bettiNumber_quotient_stabilizer_coadjointRepresentation_eq_zero_of_odd
    (ULift.{u} (ZMod p)) hj
  rw [bettiNumber_def, finrank_zero_iff] at h
  exact ((TopCat.of _).isZero_singularHomology_zmod_iff_of_ringEquiv p ULift.ringEquiv j).2
    (ModuleCat.isZero_of_subsingleton _)

/-- **The integral homology of a coadjoint orbit is finitely generated.** For a coadjoint orbit `O`
of a compact Lie group, `Hⱼ(O; ℤ)` is a finitely generated abelian group in every degree. -/
theorem finite_singularHomology_int_quotient_stabilizer_coadjointRepresentation (j : ℕ) :
    Module.Finite ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) j).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj
        (TopCat.of (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν))) := by
  obtain ⟨X, hX⟩ := ν.exists_isMorse_orbitMap_coadjointRepresentation_apply
  have := hX.finiteCWType
  exact finite_singularHomology_int_of_finiteCWType _ j

/-- **Odd integral homology of coadjoint orbits vanishes.** For a coadjoint orbit `O` of a compact
Lie group, `Hⱼ(O; ℤ) = 0` for every odd `j`. -/
theorem isZero_singularHomology_int_quotient_stabilizer_coadjointRepresentation_of_odd {j : ℕ}
    (hj : Odd j) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) j).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj
        (TopCat.of (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν))) := by
  have := ν.finite_singularHomology_int_quotient_stabilizer_coadjointRepresentation j
  exact (TopCat.of _).isZero_singularHomology_of_forall_isZero_zmod j fun p hp ↦
    ν.isZero_singularHomology_zmod_quotient_stabilizer_of_odd hp hj

/-- **The integral homology of a coadjoint orbit is free.** For a coadjoint orbit `O` of a compact
Lie group, `Hⱼ(O; ℤ)` is a free abelian group in every degree: it is zero in odd degrees, and in
even degrees it is finitely generated and torsion-free. -/
theorem free_singularHomology_int_quotient_stabilizer_coadjointRepresentation (j : ℕ) :
    Module.Free ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) j).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj
        (TopCat.of (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν))) := by
  have := ν.finite_singularHomology_int_quotient_stabilizer_coadjointRepresentation j
  rcases Nat.even_or_odd j with hj | hj
  · -- in even degree `j`, the prime field homology vanishes in the odd degree `j + 1`
    have := (TopCat.of _).isTorsionFree_singularHomology_of_forall_isZero_zmod j fun p hp ↦
      ν.isZero_singularHomology_zmod_quotient_stabilizer_of_odd hp hj.add_one
    infer_instance
  · have := ModuleCat.isZero_iff_subsingleton.1
      (ν.isZero_singularHomology_int_quotient_stabilizer_coadjointRepresentation_of_odd hj)
    infer_instance

/-- **The Euler characteristic of a coadjoint orbit counts critical points.** For a Morse height
`f_X` on a coadjoint orbit `O` of a compact Lie group, `χ(O)` is the number of critical points of
`f_X`: all its Morse indices are even, so no critical point is counted negatively. -/
theorem eulerChar_quotient_stabilizer_coadjointRepresentation_eq_ncard {X : GroupLieAlgebra I G}
    [FiniteCWType (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν)]
    (hX : IsMorse 𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
      fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X) :
    eulerChar (G ⧸ (coadjointRepresentation ℝ I G).stabilizer ν) =
      (criticalPoints
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((coadjointRepresentation ℝ I G).stabilizer ν))
        (fun y ↦ (coadjointRepresentation ℝ I G).orbitMap ν y X)).ncard := by
  -- compare the signed critical count with the Betti numbers over `ℚ`, which vanish in odd degrees
  have hP := ν.isPerfectMorse_orbitMap_coadjointRepresentation_apply (ULift.{u} ℚ) hX
  rw [← hX.sum_range_neg_one_pow_mul_toNat_criticalCount_eq_eulerChar,
    ← ν.sum_bettiNumber_quotient_stabilizer_coadjointRepresentation_eq_ncard (ULift.{u} ℚ) hX,
    Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hP.criticalCount_eq i, ← bettiNumber_def, ENat.toNat_natCast]
  rcases Nat.even_or_odd i with hi | hi
  · simp [hi.neg_one_pow]
  · simp [ν.bettiNumber_quotient_stabilizer_coadjointRepresentation_eq_zero_of_odd _ hi]

end Module.Dual
