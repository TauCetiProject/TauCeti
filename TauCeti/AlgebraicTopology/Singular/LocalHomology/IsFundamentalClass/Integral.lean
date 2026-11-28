/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass.Manifold

/-!
# Integral and rational fundamental classes and `IsFundamentalClass`

This module compares `TauCeti.IsFundamentalClass` (from
`TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass.Basic` and
`TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass.Manifold`) with integral and
rational fundamental classes of oriented manifolds (`TauCeti.HomologicalOrientation`).

## Main results

* `TauCeti.isFundamentalClass_iff_forall_isLocalOrientation`: with integral coefficients, `μ` is a
  fundamental class exactly when its image at each point is a local orientation.
* `TauCeti.HomologicalOrientation.isFundamentalClass_fundamentalClass`: the integral fundamental
  class of a compact oriented manifold is a fundamental class.
* `TauCeti.HomologicalOrientation.isFundamentalClass_zsmul_fundamentalClass_iff`: on a nonempty
  compact oriented manifold, `c • [M]` is a fundamental class exactly when `c = ±1`. In
  particular `2 • [M]` is not (`not_isFundamentalClass_two_zsmul_fundamentalClass`).
* `TauCeti.HomologicalOrientation.isFundamentalClass_iff_eq_or_eq_neg`: on a compact connected
  oriented manifold, the integral fundamental classes are exactly `[M]` and `-[M]`.
* `TauCeti.HomologicalOrientation.exists_eq_smul_mapFundamentalClass_of_isFundamentalClass`: the
  integral fundamental classes of a space homeomorphic to such a manifold through `e` are
  `±e_*[M]`.
* `TauCeti.HomologicalOrientation.isFundamentalClass_rationalFundamentalClass`: the rational
  fundamental class of a compact connected oriented manifold is a fundamental class.
* `TauCeti.HomologicalOrientation.ofIsFundamentalClass`: the orientation given by the local images
  of an integral fundamental class, and
  `TauCeti.HomologicalOrientation.fundamentalClass_ofIsFundamentalClass`: on a compact manifold,
  its fundamental class is the class itself. Conversely, the orientation of the fundamental class
  of `o` is `o` (`TauCeti.HomologicalOrientation.ofIsFundamentalClass_fundamentalClass`). So the
  integral fundamental classes of a compact manifold correspond exactly to its orientations.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, p.236 and Theorem 3.26.
-/

public section

noncomputable section

open CategoryTheory Module Set

universe w

namespace TauCeti

section Integral

variable {M : Type w} [TopologicalSpace M] {n : ℕ}

/-- **Integral fundamental classes.** With integral coefficients, a class is fundamental exactly
when its image in the local homology at every point is a local orientation. -/
theorem isFundamentalClass_iff_forall_isLocalOrientation
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{w} ℤ)) n :
      ModuleCat.{w} ℤ)) :
    IsFundamentalClass μ ↔ ∀ x : M, IsLocalOrientation x n
      (singularHomologyToLocalHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) x n μ) := by
  rw [isFundamentalClass_iff]
  exact forall_congr' fun _ ↦ (isLocalOrientation_iff_span_eq_top _ _ _).symm

end Integral

section OfIsFundamentalClass

variable {M E : Type w} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ}
  {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{w} ℤ)) n :
    ModuleCat.{w} ℤ)}

namespace HomologicalOrientation

/-- **The orientation of an integral fundamental class.** The images `μ_x` of an integral
fundamental class `μ ∈ Hₙ(M; ℤ)` in the local homology groups are local orientations, and they are
carried to one another by transport along paths. Delegated to
`TauCeti.IsFundamentalClass.toModuleOrientation` through
`TauCeti.ModuleOrientation.equivHomologicalOrientation`; its fundamental class is `μ` when `M` is
compact (`TauCeti.HomologicalOrientation.fundamentalClass_ofIsFundamentalClass`). -/
def ofIsFundamentalClass (hμ : IsFundamentalClass μ) : HomologicalOrientation M E n :=
  ModuleOrientation.equivHomologicalOrientation hμ.toModuleOrientation

/-- The local orientation of `TauCeti.HomologicalOrientation.ofIsFundamentalClass` at `x` is the
image of the fundamental class in the local homology at `x`. -/
@[simp]
theorem coe_ofIsFundamentalClass_apply (hμ : IsFundamentalClass μ) (x : M) :
    (ofIsFundamentalClass (E := E) hμ x).val =
      singularHomologyToLocalHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) x n μ := by
  rw [ofIsFundamentalClass, ModuleOrientation.coe_equivHomologicalOrientation_apply,
    hμ.coe_toModuleOrientation_apply]

end HomologicalOrientation

end OfIsFundamentalClass

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n) [CompactSpace M]

/-- **The integral fundamental class is a fundamental class**: its image at every point is the
local orientation there, which generates the local homology. -/
theorem isFundamentalClass_fundamentalClass : IsFundamentalClass (o.fundamentalClass hn) :=
  (isFundamentalClass_iff_forall_isLocalOrientation _).2 fun x ↦ by
    rw [o.singularHomologyToLocalHomology_fundamentalClass hn x]
    exact (o x).property

/-- **Multiples of the fundamental class.** On a nonempty compact oriented manifold, `c • [M]` is
a fundamental class exactly when `c` is a unit, that is `c = ±1`. -/
theorem isFundamentalClass_zsmul_fundamentalClass_iff [Nonempty M] (c : ℤ) :
    IsFundamentalClass (c • o.fundamentalClass hn) ↔ IsUnit c := by
  rw [← int_smul_eq_zsmul]
  exact (o.isFundamentalClass_fundamentalClass hn).isFundamentalClass_smul_iff hn c

/-- **Twice the fundamental class is not a fundamental class** on a nonempty compact oriented
manifold, for instance the circle: its image at each point is twice a generator of `ℤ`. -/
theorem not_isFundamentalClass_two_zsmul_fundamentalClass [Nonempty M] :
    ¬ IsFundamentalClass ((2 : ℤ) • o.fundamentalClass hn) := by
  rw [o.isFundamentalClass_zsmul_fundamentalClass_iff hn, Int.isUnit_iff]
  omega

/-- **The fundamental classes of a connected manifold.** On a compact connected oriented manifold,
the integral fundamental classes are exactly `[M]` and `-[M]`. -/
theorem isFundamentalClass_iff_eq_or_eq_neg [ConnectedSpace M]
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
      ModuleCat.{0} ℤ)) :
    IsFundamentalClass μ ↔ μ = o.fundamentalClass hn ∨ μ = -o.fundamentalClass hn := by
  have : Nonempty M := ConnectedSpace.toNonempty
  obtain ⟨c, rfl⟩ := o.exists_eq_zsmul_fundamentalClass hn μ
  rw [o.isFundamentalClass_zsmul_fundamentalClass_iff hn, Int.isUnit_iff]
  refine ⟨?_, ?_⟩
  · rintro (rfl | rfl) <;> simp
  · rintro (h | h)
    · exact Or.inl (((o.fundamentalClassEquiv hn).injective (by simpa using h)))
    · exact Or.inr (((o.fundamentalClassEquiv hn).injective (by simpa using h)))

open AlgebraicTopology CategoryTheory in
/-- **Fundamental classes of a homeomorphic copy.** If `e : M ≃ₜ X` is a homeomorphism from a
compact connected oriented manifold, every integral fundamental class of `X` is `±` the image
`e_*[M]` of the fundamental class of `M`. -/
theorem exists_eq_smul_mapFundamentalClass_of_isFundamentalClass [ConnectedSpace M] {X : Type}
    [TopologicalSpace X] (e : M ≃ₜ X)
    {μ : ((TopCat.toSSet.obj (TopCat.of X)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
      ModuleCat.{0} ℤ)} (hμ : IsFundamentalClass μ) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ μ = s • o.mapFundamentalClass hn (e : C(M, X)) := by
  -- Pull `μ` back to `M`, where it is `±[M]`, and push it forward again along `e`.
  have hμe : (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom (e : C(M, X)))).hom
      ((((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom (e.symm : C(X, M)))).hom μ) = μ :=
    congrArg (fun φ ↦ φ.hom μ) (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).mapIso (TopCat.isoOfHomeo (X := TopCat.of M) e)).inv_hom_id
  rcases (o.isFundamentalClass_iff_eq_or_eq_neg hn _).1 (hμ.map_homeomorph e.symm) with h | h
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [one_smul, mapFundamentalClass_def, ← h]
    exact hμe.symm
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [neg_one_zsmul, ← mapFundamentalClass_neg, mapFundamentalClass_def, fundamentalClass_neg,
      ← h]
    exact hμe.symm

/-- **The rational fundamental class is a fundamental class** on a compact connected oriented
manifold: it is nonzero, and over the field `ℚ` every nonzero top-dimensional class is
fundamental. -/
theorem isFundamentalClass_rationalFundamentalClass [ConnectedSpace M] :
    IsFundamentalClass (N := ModuleCat.of ℚ ℚ) (n := n) (o.rationalFundamentalClass hn) := by
  refine (isFundamentalClass_iff_ne_zero hn _).2 ?_
  rw [rationalFundamentalClass_def]
  exact (o.rationalFundamentalClassEquiv hn).map_ne_zero_iff.2 one_ne_zero

/-- **An integral fundamental class is the fundamental class of its orientation.** On a compact
manifold, the fundamental class of the orientation
`TauCeti.HomologicalOrientation.ofIsFundamentalClass` determined by an integral fundamental class
`μ` is `μ` itself. -/
@[simp]
theorem fundamentalClass_ofIsFundamentalClass
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
      ModuleCat.{0} ℤ)} (hμ : IsFundamentalClass μ) :
    (ofIsFundamentalClass (E := E) hμ).fundamentalClass hn = μ :=
  ((ofIsFundamentalClass hμ).eq_fundamentalClass hn fun x ↦
    (coe_ofIsFundamentalClass_apply hμ x).symm).symm

/-- **The orientation of the fundamental class.** On a compact manifold, the orientation
`TauCeti.HomologicalOrientation.ofIsFundamentalClass` determined by the fundamental class of an
orientation `o` is `o` itself. -/
@[simp]
theorem ofIsFundamentalClass_fundamentalClass :
    ofIsFundamentalClass (o.isFundamentalClass_fundamentalClass hn) = o :=
  HomologicalOrientation.ext fun x ↦ Subtype.ext <| by
    rw [coe_ofIsFundamentalClass_apply, singularHomologyToLocalHomology_fundamentalClass]

end HomologicalOrientation

end TauCeti
